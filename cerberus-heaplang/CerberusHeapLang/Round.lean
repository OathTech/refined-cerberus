/-
CerberusHeapLang.Round — THE SHIPPED ENGINE ROUND, NAMED.

`CerberusRound M c c'` is ONE ITERATION OF THE SHIPPED DRIVER'S THREAD
LOOP at a machine context, stated in the driver's own vocabulary and
nothing else: at every driver state that embeds the context and the
live configuration `c` (`MachineCtx.Embeds` — the single thread
`M.tid` holding `M.thread c.1 c.2.1 c.2.2.1`, the memory `c.2.2.2`, the file,
extern map and run state of `M`), the engine's step list read by the
loop body (`step_ctx`, Core_reduction.lean:484 — exactly the `nd_read`
of `drive_nonmemory_steps_aux2`, Driver.lean:346) is a singleton `s`,
`s` is advanceable (`can_advance`, Driver.lean:310 — the loop's
`find_can_advance` selects it), and the shipped `advance_step`
(Driver.lean:336) on it is ONE ACTIVE, WAKEUP-FREE transition to the
driver state that embeds `c'` (the run state's aid supply possibly
ticked — `labeled` untouched — the trace extended, the step counter
moved). `CerberusRound.loop_step` is the loop-level reading of the same
fact: `runOne (drive_nonmemory_steps_aux2_lemFuel (fl+1) …) dst =
runOne (drive_nonmemory_steps_aux2_lemFuel fl …) dst'` — the shape
`loop_step_frag` (DriverCollapse.lean) ships at the production profile —
proved there INDEPENDENTLY, by its own per-redex case analysis, not
derived from this round (see "WHAT CONSUMES WHAT" below).

NO FUEL DEPENDENCY. The round is stated at the loop BODY: the step
list, `find_can_advance` and `advance_step` are not fuelled (`nd_bind`
spends one layer of its own fresh budget per bind —
`runOne_bind_active`, DriverCollapse.lean — never accumulating). The
loop-level corollary holds for EVERY `fl`: the continuation at `fl` is
the same shipped function on both sides, and no fuel-zero arm is ever
evaluated by the statement.

THE REFERENT DISCIPLINE ([USER 2026-09-02], CLAUDE.md "The referent
of every export is the genuine semantics"). Before this slice the round
was `outcomesU … = [.next …]`, i.e. the graph of the hand-written
`dischargeStep` (Soundness.lean) — a package definition in an export's
referent. Now every constant in the statement of `CerberusRound`, of
the classification and of the refusal classes is either the engine's
(`step_ctx`, `can_advance`, `advance_step`, `perform_memop_request2`,
`update_thread_state`, `failwithI`, the `ndM`/`nd_action` types) or
context/embedding plumbing (`MachineCtx`, `MachineCtx.thread`,
`MachineCtx.Embeds`, `Config`). The one package name that is neither
is `runOne` (DriverCollapse.lean): `match m with | ND f => f s`, the
`ND` constructor's eliminator — the very operation `nd_bind` performs
on its left argument (Nondeterminism.lean:188). It carries no driver,
discharge or scheduler content; it is to `ndM` what `Prod.fst` is to
pairs. `dischargeStep`/`outcomesU` (Soundness.lean) remain as PROOF
DEVICES of this module's classification (the discharge-device readings
below) — and appear in no export's statement here (since the fuel-lane
restatement of 2026-09-03 no adequacy lane consumes them: both lanes run
on `loop_step_frag`; the `outcomesU` step-match `outcomesU_of_step` was
deleted 2026-09-04, consumerless — KNOWN-OPEN-ITEMS C3).

WHAT IS PROVED — the classification (`cerberusRound_classify`): for
every well-sized `Frag` configuration at a sequentially well-formed
context with a cons-shaped environment stack, EXACTLY ONE of

- `value_done`   — a bare value; the engine's step list is PROGRAM-DONE
                   (`[Step_done2 v]`, not advanceable: the loop records
                   it — `loop_step_done` — and `driver2` routes it to
                   `prepare_exit` — `driver2_done`, DriverCollapse.lean);
- `value_annot`  — an annotated value; the engine's round is the
                   REMOVE-ANNOT tau (a `CerberusRound` to the bare
                   value, env and memory verbatim) — NOT a mirror step,
                   by the mirror's value protocol (`toVal`);
- `step`         — the mirror steps, and then for EVERY c':
                   `Step M c c' ↔ CerberusRound M c c'` (two-sided GIVEN
                   the mirror step: the shipped round is exactly the
                   mirror's step, and conversely; mirror determinism
                   falls out);
- `refused`      — the mirror is STUCK at a non-value configuration AND
                   the shipped round is a classified refusal
                   (`ShippedRefusal`);
- `open_`        — the mirror is STUCK at a non-value configuration of
                   the RESIDUAL (`OpenRound`, two arms; below).

MIRROR COMPLETENESS (`frag_round_complete`, the second half of this
module): at every non-value `Frag` configuration the mirror steps, or
the shipped round is a `ShippedRefusal`, or the configuration is in the
residual `OpenRound` — one lemma per redex root (`complete_store` …
`complete_memop_vals`), dispatched by `Frag.decomp`, the redex's step
lifted through the context by `Decomp.lift_step`. The refusal
vocabulary (`ShippedRefusal`) is stated in the same discipline as the
round: ILLTYPED (`[Step_error2 msg]`), ILLTYPED AT DISTANCE ONE (a
successful round `CerberusRound M c c'` whose successor's step list is
`[Step_error2 msg]` — the load/store ACTION_EVAL at a non-pointer
value, `error_next`), KILL (the shipped `advance_step` returns
`NDkilled r` for an engine `kill_reason` — memory kills through
`liftMem`, pure-evaluator kills `Other (DErr_core_run err)` through
`liftCore_run`), FORK (the shipped exhaustive runner `CerbND.runND`
returns ≥ 2 executions — determinism is NOT baked in), PANIC (the
redex's own monad, under step_ctx's bind wrapper, IS the engine's
`failwithI msg` — LemLib's rendering of OCaml `failwith`, opaque by
design), PANIC-env (the successor's environment head IS the engine's
binding-mismatch `failwithI`), PANIC-memop (the driver's INVALID-memop
`failwithI` under its install bind), PANIC-noproc (the Erun step's label
lookup keyed by the engine's "outside of a proc" `failwithI`).

THE FRAGMENT IS EXACTLY WHAT THE MIRROR COVERS ([USER 2026-09-02], the
fragment-closure ruling: "fail-closed if we've achieved complete
coverage"; record `docs/2026-09-02_fragment-closure-notes.md`). Of the
four gaps the 2026-09-02 mirror-completeness slice registered, (a) the
LETS-ANNOT beta at the plain-symbol binder is UNREACHABLE — the binder's
head is restricted to the bare-value producers `BareHead`
(Soundness.lean); (b) the ACTION_EVAL to a non-pointer value is ILLTYPED
AT DISTANCE ONE; (d) the jump without a current procedure is
PANIC-noproc; (c) operand evaluation outside the mirror evaluator is
closed to the KILL classification for every operand the CLASSIFIER
rejects (`evalClass … = .kill err`, EvalClass.lean — the failure twin of
the success bridge) and leaves THE RESIDUAL `OpenRound`: `eval_uncovered`
(an operand in the covered grammar CONTAINING A LEAF the mirror evaluator
does not evaluate and the engine's evaluator accepts: a symbol unbound in
the environment but naming a `Proc` of the file, a mirrored binop at two
floats, `OpEq` at two ctypes — environment/file-dependent, carrying the
offending operand as witness). `evalClass` answers `.uncovered` at the
FIRST such leaf and carries NO engine claim about the whole operand, so
the engine's outcome on that operand is NOT characterized here — it may
succeed, KILL on a later type error (`f + 1` with `f` a `Proc`-named
unbound symbol is `PePure`, classified `.uncovered`, and the engine kills
it as `Illformed_program … ill-typed PEop`; 2026-09-03 audit, by
execution), or PANIC (a float guard under `Eif`). Precisely: every
operand the classifier REJECTS is a proved engine KILL; operands the
classifier leaves UNCOVERED are not characterized (the residual is a
SUPERSET of the engine-accepted shapes). The mover is `evalClass`
computing the engine's value at the three leaf shapes, which reserves
`.uncovered` for the leaf itself and puts the downstream rejections under
the KILL bridge. The other arm is `run_surplus` (a jump with more arguments than the label's
parameters whose zipped arguments evaluate and whose surplus does not —
label-map-dependent). Both arms record that the mirror is stuck and the
engine step's shape; neither is a refusal, and neither is removable by
a syntactic narrowing of `Frag`. `cerberusRound_refused_store`/`_load`/
`_create`/`_case` are the root-redex refusal instances kept from
commit 1 of the mirror-completeness slice (DECISIONS.md, "MIRROR
COMPLETENESS — GO"); `cerberusRound_refused_kill` (kill/free arc K2)
is the same instance at the kill redex, its three engine reasons
enumerated by `killM_killed_inv`.

THE MIRROR'S ONLY REFERENCE is this round: no other relational
semantics is referenced or bridged, and none is needed for the root of
trust, which is the engine (`step_ctx` and the shipped driver).

WHAT CONSUMES WHAT (2026-09-03 audit, N-1). `CerberusRound`,
`engine_step_matchU`, `step_iff_cerberusRound`, `cerberusRound_classify`
and `frag_round_complete` are the reference relation and the
certification/completeness statements OVER it; they are consumed by NO
adequacy export. Both adequacy lanes — the partial fuel induction
(`drive_safe_aux`, Adequacy.lean) and the total budget inductions
(`wpt_driver_aux`/`wpt_driver_cps`, ProdLoop.lean, consumed by the
production collapse `prod_run_eqJ`/`prod_run_eqJ_procs`) — consume the
shipped round `loop_step_frag`/`loop_step_frag'` (DriverCollapse.lean),
proved independently of this module. Deriving
`loop_step_frag` from `CerberusRound.loop_step` via a context-transport
lemma would retire that duplication; today they stand side by side.
-/
import CerberusHeapLang.Heap
import CerberusHeapLang.DriverCollapse
import CerberusHeapLang.EnvLaws
import CerberusHeapLang.EvalClass

set_option autoImplicit false

namespace CerberusHeapLang

open Lem_Basic_classes Lem_Maybe Lem_List

/-- The driver states that EMBED a machine context and a live
    configuration: the single thread `M.tid` (parent `M.parent`) holds
    `M.thread c.1 c.2.1 c.2.2.1` (the live control's fields are the
    thread's control fields), the memory is `c.2.2.2`, and the file, extern
    map and run state are the context's. Every other driver-state field
    (trace, step counter, concurrency and file-system state, …) is
    free: the fragment's rounds read none of them. -/
structure MachineCtx.Embeds (M : MachineCtx) (dst : driver_state) (c : Config) : Prop where
  thread : dst.core_state0.thread_states = [(M.tid, (M.parent, M.thread c.1 c.2.1 c.2.2.1))]
  layout : dst.layout_state = c.2.2.2
  file : dst.core_file = M.file
  extern : dst.core_extern = M.extern
  /-- E1: the run state is tied at the fields the fragment READS — the
      label registry (the context's) and the two symbol supplies (the
      live control's `Ctl.sup`; the E5 shape — no E1 rule writes them,
      and every round preserves them). -/
  labeled : dst.core_run_state0.labeled = M.runState.labeled
  sym : dst.core_run_state0.sym_supply = c.2.2.1.sup.sym
  excl : dst.core_run_state0.excluded_supply = c.2.2.1.sup.excl

/-- Every context and configuration is embedded by some driver state. -/
theorem MachineCtx.embeds_exists (M : MachineCtx) (c : Config) : ∃ dst, M.Embeds dst c :=
  ⟨{ (default : driver_state) with
      core_state0 := { (default : core_state) with
        thread_states := [(M.tid, (M.parent, M.thread c.1 c.2.1 c.2.2.1))] },
      layout_state := c.2.2.2, core_file := M.file, core_extern := M.extern,
      core_run_state0 := { M.runState with
        sym_supply := c.2.2.1.sup.sym, excluded_supply := c.2.2.1.sup.excl } },
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- THE SHIPPED ROUND (module header): at every embedding driver state,
    the engine's step list is a singleton `s`, `s` is advanceable, and
    the shipped `advance_step` on it is one active wakeup-free
    transition to the state embedding `c'` — with the run state
    replaced by some `rs'` whose `labeled` fiber is untouched (the
    action rounds tick `aid_supply`, nothing else), the trace and the
    step counter arbitrary. -/
def CerberusRound (M : MachineCtx) (c c' : Config) : Prop :=
  ∀ dst : driver_state, M.Embeds dst c →
    ∃ s : core_step2,
      step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
        (M.parent, M.thread c.1 c.2.1 c.2.2.1) = [s] ∧
      can_advance s = true ∧
      ∃ (rs' : core_run_state) (tr : List trace_event) (ctr : Nat),
        rs'.labeled = dst.core_run_state0.labeled ∧
        rs'.sym_supply = c'.2.2.1.sup.sym ∧ rs'.excluded_supply = c'.2.2.1.sup.excl ∧
        runOne (advance_step M.tagDefs M.tid s) dst =
          (NDactive NOWAKEUP,
           { dst with
              core_state0 := update_thread_state M.tid (M.thread c'.1 c'.2.1 c'.2.2.1) dst.core_state0,
              layout_state := c'.2.2.2,
              core_run_state0 := rs', trace := tr, dr_step_counter := ctr })

/-- THE REFUSAL VOCABULARY, in the shipped driver's own terms (module
    header). Each arm is a fact about every embedding driver state;
    the payload (`msg`, `r`) is fixed by the configuration, not by the
    embedding. -/
inductive ShippedRefusal (M : MachineCtx) (c : Config) : Prop where
  /-- ILLTYPED: the engine's step list is the singleton `Step_error2
      msg` (one_step0's `ILLTYPED`/step_action's `ACTION_ILLTYPED`,
      Core_reduction.lean:353/424). The shipped driver's response to
      this step is the panic `failwithI ("can_advance: Step_error2 ==>
      " ++ msg)` (Driver.lean:310) — recorded, not modelled. -/
  | error (msg : String) :
      (∀ dst, M.Embeds dst c →
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread c.1 c.2.1 c.2.2.1) = [Step_error2 msg]) →
      ShippedRefusal M c
  /-- KILL: the step is advanceable and the shipped `advance_step`
      returns `NDkilled r` — `r` in the engine's own `kill_reason`
      vocabulary (`Undef0 loc ubs` for undefined behaviour, `Error0`,
      `Other err` for the driver's non-UB kills; memory kills arrive
      through `liftMem`'s `DErr_memory`, Driver.lean:218). -/
  | killed (r : kill_reason driver_error) :
      (∀ dst, M.Embeds dst c → ∃ (s : core_step2) (dst' : driver_state),
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread c.1 c.2.1 c.2.2.1) = [s] ∧
        can_advance s = true ∧
        runOne (advance_step M.tagDefs M.tid s) dst = (NDkilled r, dst')) →
      ShippedRefusal M c
  /-- FORK: the step is advanceable and the shipped exhaustive runner
      delivers at least two outcomes for the advance (a nondeterministic
      node — `msum`, Nondeterminism.lean:245 — inside the memory
      operation). Determinism is not baked in: a later mirror may cover
      this class with a nondeterministic step. -/
  | fork :
      (∀ dst, M.Embeds dst c → ∃ s : core_step2,
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread c.1 c.2.1 c.2.2.1) = [s] ∧
        can_advance s = true ∧
        2 ≤ (CerbND.runND (advance_step M.tagDefs M.tid s) dst).length) →
      ShippedRefusal M c
  /-- PANIC (with-runstate): the step is `Step_with_runstate2 rsk m`,
      `m` is the engine's state-except bind of the redex's own monad
      `step_m` with the step's continuation `k` (step_ctx's
      TAU_WITH_RUNSTATE/EVAL wrappers, Core_reduction.lean:484 — for a
      monad without a wrapper, `k` is the return, by the right unit
      law `stExceptUndef_bind_return_right`), and `step_m` at the
      driver's run state IS the panic `failwithI msg` (LemLib's opaque
      rendering of OCaml `failwith`: the interpreter aborts; neither a
      kill nor a value). -/
  | panic :
      (∀ dst, M.Embeds dst c →
        ∃ (rsk : runstate_step_kind) (m : core_runM thread_state) (d : Type)
          (inst : Inhabited (core_run_state → exceptM (t0 d × core_run_state) core_run_cause))
          (step_m : core_run_state → exceptM (t0 d × core_run_state) core_run_cause)
          (k : d → core_run_state → exceptM (t0 thread_state × core_run_state) core_run_cause)
          (msg : String),
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread c.1 c.2.1 c.2.2.1) = [Step_with_runstate2 rsk m] ∧
        m = stExceptUndef_bind step_m k ∧
        step_m dst.core_run_state0 = @failwithI _ inst msg dst.core_run_state0) →
      ShippedRefusal M c
  /-- PANIC (binding): the step is a TAU whose successor thread's
      environment head IS the panic `failwithI msg` — the engine's
      `update_env_aux` pattern-mismatch arm (Core_aux.lean:861, the
      `CaseCtor ctor pats, _` catch-all): a `Cspecified` binder meeting a
      non-`Specified` value, or — E2 — a flat TUPLE binder meeting a
      non-tuple head value (`update_env_aux_tuple_mismatch`,
      `complete_beta_tuple`/`complete_wbeta_tuple`). In OCaml the
      strict `update_env` raises during the round; Lean's opaque
      `failwithI` defers the same abort to the first read. -/
  | panic_env (msg : String) :
      (∀ dst, M.Embeds dst c →
        ∃ (s : String) (th' : thread_state) (evs : List (Fmap sym value)),
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread c.1 c.2.1 c.2.2.1) = [Step_tau2 s TSK_Misc th'] ∧
        th'.env = (failwithI msg : Fmap sym value) :: evs) →
      ShippedRefusal M c
  /-- PANIC (memop): the step is a memop request and the shipped
      `perform_memop_request2` (Driver.lean:288) on it is a bind whose
      head is the panic `failwithI msg` (its `INVALID memop request`
      arm). -/
  | panic_memop (msg : String) :
      (∀ dst, M.Embeds dst c →
        ∃ (loc : CerbLocation.Loc) (mop : memop) (cvals : List value) (uw : Bool)
          (k : value → thread_state)
          (g : thread_state → ndM Unit step_kind driver_error
            (mem_constraint CerbMem.IntegerValue) driver_state),
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread c.1 c.2.1 c.2.2.1) = [Step_memop_request2 loc mop cvals M.tid uw k] ∧
        perform_memop_request2 M.tagDefs loc mop cvals M.tid k =
          nd_bind (failwithI msg) g) →
      ShippedRefusal M c
  /-- ILLTYPED AT DISTANCE ONE (fragment closure, gap (b)): the shipped
      round SUCCEEDS — `CerberusRound M c c'` — into a configuration `c'`
      at which the engine's NEXT step list is the ILLTYPED report
      `[Step_error2 msg]`. The instance: a load/store ACTION_EVAL whose
      pointer operand evaluates to a non-pointer value — the evaluation
      round rebuilds the action with the value (step_action's `_, _`
      ACTION_EVAL arm, Core_reduction.lean:424), and the rebuilt action's
      operand test falls to `some _, some _ => ACTION_ILLTYPED "Load"`
      (`"Store"`). An ill-typed program: classified, not narrowed. -/
  | error_next (c' : Config) (msg : String) :
      CerberusRound M c c' →
      (∀ dst, M.Embeds dst c' →
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread c'.1 c'.2.1 c'.2.2.1) = [Step_error2 msg]) →
      ShippedRefusal M c
  /-- PANIC (jump without a current procedure; fragment closure, gap
      (d)): at a configuration whose control has `proc = none` the engine's Erun step
      (step_ctx's Erun arm, Core_reduction.lean:484) reads
      `current_proc := failwithI "Core_reduction ==> Erun outside of a
      proc"` and consults the run state's label table AT THAT KEY — the
      step's monad is exhibited: the state-read of `labeled` keyed by the
      extern-resolved panic term, bound to the arm's continuation `k`.
      In OCaml the strict `failwith` aborts the round; Lean's opaque
      `failwithI` defers the same abort into the lookup key. The
      mirror's label map at such a context is empty (`MachineCtx.labelsAt`,
      fail-closed). Every shipped thread inside a procedure body has a
      current procedure. -/
  | panic_noproc (msg : String) :
      c.2.2.1.proc = none →
      (∀ dst, M.Embeds dst c →
        ∃ (s : String) (l : sym) (inst : Inhabited sym)
          (k : Option (List (sym × core_base_type) × CoreExpr) → core_run_state →
            exceptM (t0 thread_state × core_run_state) core_run_cause),
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread c.1 c.2.1 c.2.2.1) =
          [Step_with_runstate2 (RSK_eval s)
            (stExceptUndef_bind
              (runSE (state_except_read (fun rs : core_run_state =>
                Lem_Maybe.bind0
                  (fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
                      Lem_Basic_classes.ordCompare s1 s2)
                    (resolveExtern dst.core_extern (@failwithI sym inst msg)) rs.labeled)
                  (fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
                    Lem_Basic_classes.ordCompare s1 s2) l))))
              k)]) →
      ShippedRefusal M c

/-- THE RESIDUAL — the configuration classes the mirror does not step at
    and this package does not classify as a refusal (fragment closure,
    2026-09-02; gaps (a), (b), (d) are closed — `Frag.sseq_sym`'s
    `BareHead` premise, `ShippedRefusal.error_next`,
    `ShippedRefusal.panic_noproc` — and gap (c) is closed up to what
    follows). Both arms record that the mirror IS stuck, name the engine
    step's shape, and carry a mirror-side witness that names the class;
    every instance is environment-, file- or label-map-dependent, so no
    syntactic narrowing of `Frag` removes it. Neither arm carries an
    engine claim beyond the step's shape: the whole-operand outcome in
    `eval_uncovered` and the successor in `run_surplus` are NOT
    characterized here (2026-09-03 audit, M-1). -/
inductive OpenRound (M : MachineCtx) (c : Config) : Prop where
  /-- An operand of the configuration's redex, in the covered grammar,
      that the mirror evaluator does not evaluate and that the CLASSIFIER
      leaves uncovered: `evalClass … = .uncovered` (EvalClass.lean). The
      classifier answers `.uncovered` at the FIRST uncovered LEAF — a
      symbol unbound in the environment but naming a `Proc` of the file
      (the engine evaluates that leaf to the null function pointer), one
      of the eight mirrored binops at two floating-point operands, or
      `OpEq` at two ctypes — and carries NO engine claim about the whole
      operand. So this arm contains operands whose whole-operand outcome
      is NOT characterized, INCLUDING ones the engine KILLS (`f + 1` with
      `f` a `Proc`-named unbound symbol is `PePure`, classified
      `.uncovered`, and the engine kills it as `Illformed_program …
      ill-typed PEop` — 2026-09-03 audit, by execution) or PANICS (a float
      guard under `Eif`). The engine's round is the
      operand-evaluation with-runstate step; its successor is not
      characterized here. Every operand the classifier REJECTS
      (`evalClass … = .kill err`) is a proved engine KILL (`ShippedRefusal.
      killed (Other (DErr_core_run err))`, the `complete_*` lemmas);
      operands the classifier leaves UNCOVERED are not characterized — the
      residual is a SUPERSET of the engine-accepted shapes. The mover:
      `evalClass` computing the engine's value at the three leaf shapes. -/
  | eval_uncovered (pe : generic_pexpr Unit sym) :
      (∀ c'', ¬ Step M c c'') →
      pe ∈ operandsOf c.1 → PePure pe →
      evalClass M.tagDefs c.2.2.1.curLoc M.extern M.file c.2.1 pe = .uncovered →
      (∀ dst, M.Embeds dst c → ∃ (rsk : runstate_step_kind) (m : core_runM thread_state),
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread c.1 c.2.1 c.2.2.1) = [Step_with_runstate2 rsk m]) →
      OpenRound M c
  /-- A jump whose argument list is LONGER than the registered label's
      parameter list, every zipped argument evaluating and some surplus
      argument not: the engine's Erun arm folds over `zip sym_bTys pes`
      (truncating) and SUCCEEDS; the mirror's `Step.run` evaluates every
      argument and is stuck. An arity-mismatched program; its successor
      is not characterized here. -/
  | run_surplus (l : sym) (pes : List (generic_pexpr Unit sym)) (p : sym)
      (params : List (sym × core_base_type)) (cont : CoreExpr) :
      (∀ c'', ¬ Step M c c'') →
      jumpRedex? c.1 = some (l, pes) → c.2.2.1.proc = some p →
      lookupLabel (M.labelsAt c.2.2.1.proc) l = some (params, cont) →
      (∃ vs, evalPexprs M.tagDefs M.extern c.2.1 (zipArgs params pes) = some vs) →
      evalPexprs M.tagDefs M.extern c.2.1 pes = none →
      (∀ dst, M.Embeds dst c → ∃ (rsk : runstate_step_kind) (m : core_runM thread_state),
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread c.1 c.2.1 c.2.2.1) = [Step_with_runstate2 rsk m]) →
      OpenRound M c

/-- The completeness disjunction at a configuration: the mirror steps,
    or the shipped round is a classified refusal, or the configuration
    is one of the registered gaps. -/
abbrev RoundComplete (M : MachineCtx) (c : Config) : Prop :=
  (∃ c', Step M c c') ∨ ShippedRefusal M c ∨ OpenRound M c

/-! ## Driver plumbing at a general thread id (the `0` instances live
in DriverCollapse.lean) -/

/-- The driver's thread-id equality test (the `instBEqOfEq0 → Eq0 →
    SetType-of-Ord → defaultCompare` chain, `lemNatBeq_iff`,
    EnvLaws.lean) is reflexive. -/
theorem lemNatBeq_self (n : Nat) :
    (@BEq.beq Nat (@instBEqOfEq0 Nat Lem_Num.instEq0Nat_1) n n) = true :=
  (lemNatBeq_iff n n).mpr rfl

/-- `lookupBy` (LemLib List.lean:256) at the singleton thread
    association list. -/
theorem lookupBy_single {β : Type} (k : Nat) (v : β) :
    lookupBy (fun (x y : Nat) => x == y) k [(k, v)] = some v := by
  simp only [lookupBy, find, lemNatBeq_self, if_true, Option.map]

/-- `update_thread_state` (Core_run.lean:99, via assoc_adjust
    Utils.lean:186) at the singleton thread list, any thread id. -/
theorem update_thread_state_single' (tid : Nat) (parent : Option Nat)
    (th th' : thread_state) (cs : core_state)
    (hth : cs.thread_states = [(tid, (parent, th))]) :
    update_thread_state tid th' cs =
      { cs with thread_states := [(tid, (parent, th'))] } := by
  unfold update_thread_state
  rw [hth]
  simp only [assoc_adjust, lemNatBeq_self, if_true]

/-! ## The shipped loop body, decomposed (Driver.lean:346-351):
{`nd_read` of the step list → `find_can_advance` → `advance_step`} -/

/-- ONE LOOP ITERATION from its three parts: a singleton advanceable
    step list whose shipped advance is active and wakeup-free continues
    the loop on the same thread list at the successor state. -/
theorem loop_step_of_advance {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {tid : Nat} {parent : Option Nat} {th : thread_state} {s : core_step2}
    {dst dst' : driver_state} (fl : Nat) (acc : Fmap thread_id (List core_step2))
    (hth : dst.core_state0.thread_states = [(tid, (parent, th))])
    (hsteps : step_ctx tds dst.layout_state dst.core_file dst.core_extern tid
      (parent, th) = [s])
    (hca : can_advance s = true)
    (hadv : runOne (advance_step tds tid s) dst = (NDactive NOWAKEUP, dst')) :
    runOne (drive_nonmemory_steps_aux2_lemFuel (Nat.succ fl) tds acc [tid]) dst =
      runOne (drive_nonmemory_steps_aux2_lemFuel fl tds acc [tid]) dst' := by
  conv => lhs; unfold drive_nonmemory_steps_aux2_lemFuel
  refine (runOne_bind_active (z := [s]) (s' := dst) ?_).trans ?_
  · rw [runOne_read]
    refine congrArg (fun x => (NDactive x, dst)) ?_
    show (let th_info := match lookupBy (fun x y => x == y) tid
            dst.core_state0.thread_states with
          | some z => z
          | none => failwithI _;
        step_ctx tds dst.layout_state dst.core_file dst.core_extern tid th_info) = _
    rw [hth, lookupBy_single]
    exact hsteps
  · dsimp only [find_can_advance]
    rw [hca, if_pos rfl]
    refine (runOne_bind_active (z := NOWAKEUP) (s' := dst') hadv).trans ?_
    rfl

/-- `advance_step`'s tau arm (Driver.lean:336): thread updated,
    `dr_step_counter` ticked, no wakeup. -/
theorem advance_tau (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (tid : Nat)
    (s : String) (th' : thread_state) (dst : driver_state) :
    runOne (advance_step tds tid (Step_tau2 s TSK_Misc th')) dst =
      (NDactive NOWAKEUP,
       { { dst with dr_step_counter := dst.dr_step_counter + 1 }
           with core_state0 := update_thread_state tid th' dst.core_state0 }) := by
  unfold advance_step
  dsimp only
  refine (runOne_bind_active (z := ()) (s' := dst) (by rfl)).trans ?_
  refine (runOne_bind_active (z := ()) (by rfl)).trans ?_
  rfl

/-- `advance_step`'s tau arm at ANY task kind (calls arc C2 — the RETURN
    round): the `TSK_Return` kind pushes `ME_function_return` on the
    trace (Driver.lean:336), the other kinds do not; the trace is
    existential. -/
theorem advance_tau_tsk (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (tid : Nat)
    (s : String) (tsk : core_tau_step_kind) (th' : thread_state) (dst : driver_state) :
    ∃ tr : List trace_event,
      runOne (advance_step tds tid (Step_tau2 s tsk th')) dst =
        (NDactive NOWAKEUP,
         { { { dst with trace := tr } with dr_step_counter := dst.dr_step_counter + 1 }
             with core_state0 := update_thread_state tid th' dst.core_state0 }) := by
  unfold advance_step
  dsimp only
  cases tsk with
  | TSK_Return sym1 mval_opt =>
    refine ⟨ME_function_return sym1 mval_opt :: dst.trace, ?_⟩
    refine (runOne_bind_active (z := ())
      (s' := { dst with trace := ME_function_return sym1 mval_opt :: dst.trace })
      (by rfl)).trans ?_
    refine (runOne_bind_active (z := ()) (by rfl)).trans ?_
    rfl
  | TSK_Ccall sym1 mvals =>
    refine ⟨dst.trace, ?_⟩
    refine (runOne_bind_active (z := ()) (s' := dst) (by rfl)).trans ?_
    refine (runOne_bind_active (z := ()) (by rfl)).trans ?_
    rfl
  | TSK_Misc =>
    refine ⟨dst.trace, ?_⟩
    refine (runOne_bind_active (z := ()) (s' := dst) (by rfl)).trans ?_
    refine (runOne_bind_active (z := ()) (by rfl)).trans ?_
    rfl

/-- `advance_step`'s with-runstate arm, EVAL kind: `liftCore_run`
    writes the monad's run state back (verbatim here, `hm`), the thread
    is updated, the counter ticked. -/
theorem advance_withrs_eval (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (tid : Nat) (s : String) (m : core_runM thread_state)
    {th' : thread_state} {dst : driver_state}
    (hm : m dst.core_run_state0 = Result (Defined th', dst.core_run_state0)) :
    runOne (advance_step tds tid (Step_with_runstate2 (RSK_eval s) m)) dst =
      (NDactive NOWAKEUP,
       { { dst with dr_step_counter := dst.dr_step_counter + 1 }
           with core_state0 := update_thread_state tid th' dst.core_state0 }) := by
  unfold advance_step
  dsimp only
  refine (runOne_bind_active (z := ()) (s' := dst) (by rfl)).trans ?_
  refine (runOne_bind_active (z := th') (s' := dst)
    (runOne_liftCore_run_of_eq hm)).trans ?_
  refine (runOne_bind_active (z := ()) (by rfl)).trans ?_
  rfl

/-- `advance_step`'s with-runstate arm, TAU kind (`TSK_Misc`). -/
theorem advance_withrs_tau (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (tid : Nat) (s : String) (m : core_runM thread_state)
    {th' : thread_state} {dst : driver_state}
    (hm : m dst.core_run_state0 = Result (Defined th', dst.core_run_state0)) :
    runOne (advance_step tds tid (Step_with_runstate2 (RSK_tau s TSK_Misc) m)) dst =
      (NDactive NOWAKEUP,
       { { dst with dr_step_counter := dst.dr_step_counter + 1 }
           with core_state0 := update_thread_state tid th' dst.core_state0 }) := by
  unfold advance_step
  dsimp only
  refine (runOne_bind_active (z := ()) (s' := dst) (by rfl)).trans ?_
  refine (runOne_bind_active (z := th') (s' := dst)
    (runOne_liftCore_run_of_eq hm)).trans ?_
  refine (runOne_bind_active (z := ()) (by rfl)).trans ?_
  rfl

/-- `liftCore_run` (Driver.lean:245) of a with-runstate monad that
    RAISES: the exception becomes the driver's kill `Other (DErr_core_run
    err)`, the state untouched. -/
theorem runOne_liftCore_run_exception {a : Type}
    {m : core_run_state → exceptM ((t0 a) × core_run_state) core_run_cause}
    {dst : driver_state} {err : core_run_cause}
    (hm : m dst.core_run_state0 = Exception err) :
    runOne (liftCore_run m) dst = (NDkilled (Other (DErr_core_run err)), dst) := by
  unfold liftCore_run
  refine (runOne_bind_active (z := dst) (by rfl)).trans ?_
  rw [show stExceptUndef_run m dst.core_run_state0 = Exception err from hm]
  rfl

/-- `advance_step`'s with-runstate arm, EVAL kind, KILLED: the monad
    raises, the driver kills. -/
theorem advance_withrs_killed_eval (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (tid : Nat) (s : String) (m : core_runM thread_state)
    {dst : driver_state} {err : core_run_cause}
    (hm : m dst.core_run_state0 = Exception err) :
    runOne (advance_step tds tid (Step_with_runstate2 (RSK_eval s) m)) dst =
      (NDkilled (Other (DErr_core_run err)), dst) := by
  unfold advance_step
  dsimp only
  refine (runOne_bind_active (z := ()) (s' := dst) (by rfl)).trans ?_
  exact runOne_bind_killed (runOne_liftCore_run_exception hm)

/-- `advance_step`'s with-runstate arm, TAU kind (`TSK_Misc`), KILLED. -/
theorem advance_withrs_killed_tau (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (tid : Nat) (s : String) (m : core_runM thread_state)
    {dst : driver_state} {err : core_run_cause}
    (hm : m dst.core_run_state0 = Exception err) :
    runOne (advance_step tds tid (Step_with_runstate2 (RSK_tau s TSK_Misc) m)) dst =
      (NDkilled (Other (DErr_core_run err)), dst) := by
  unfold advance_step
  dsimp only
  refine (runOne_bind_active (z := ()) (s' := dst) (by rfl)).trans ?_
  exact runOne_bind_killed (runOne_liftCore_run_exception hm)

/-- E2: the shipped driver's kill reason for a classified failure
    (`liftCore_run`, Driver.lean:245): a raise is `Other (DErr_core_run
    err)`, an undef is `Undef0 loc ubs`. -/
def EvalFail.reason : EvalFail → kill_reason driver_error
  | .kill err => Other (DErr_core_run err)
  | .undef l u => Undef0 l u

/-- `liftCore_run` (Driver.lean:245) of a with-runstate monad that FAILS
    (raises or undefs): the driver kills with the failure's reason. -/
theorem runOne_liftCore_run_fail {a : Type}
    {m : core_run_state → exceptM ((t0 a) × core_run_state) core_run_cause}
    {dst : driver_state} {fl : EvalFail}
    (hm : m dst.core_run_state0 = fl.run a core_run_state dst.core_run_state0) :
    ∃ dst', runOne (liftCore_run m) dst = (NDkilled fl.reason, dst') := by
  cases fl with
  | kill err => exact ⟨dst, runOne_liftCore_run_exception hm⟩
  | undef l u =>
    refine ⟨{ dst with core_run_state0 := dst.core_run_state0 }, ?_⟩
    unfold liftCore_run
    refine (runOne_bind_active (z := dst) (by rfl)).trans ?_
    rw [show stExceptUndef_run m dst.core_run_state0 =
      Result (Undef l u, dst.core_run_state0) from hm]
    refine (runOne_bind_active (z := ()) (by rfl)).trans ?_
    rfl

/-- `advance_step`'s with-runstate arm, EVAL kind, FAILED: the monad
    raises or undefs, the driver kills with the failure's reason. -/
theorem advance_withrs_failed_eval (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (tid : Nat) (s : String) (m : core_runM thread_state)
    {dst : driver_state} {fl : EvalFail}
    (hm : m dst.core_run_state0 = fl.run thread_state core_run_state dst.core_run_state0) :
    ∃ dst', runOne (advance_step tds tid (Step_with_runstate2 (RSK_eval s) m)) dst =
      (NDkilled fl.reason, dst') := by
  obtain ⟨dst', h⟩ := runOne_liftCore_run_fail hm
  refine ⟨dst', ?_⟩
  unfold advance_step
  dsimp only
  refine (runOne_bind_active (z := ()) (s' := dst) (by rfl)).trans ?_
  exact runOne_bind_killed h

/-- `advance_step`'s with-runstate arm, TAU kind (`TSK_Misc`), FAILED. -/
theorem advance_withrs_failed_tau (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (tid : Nat) (s : String) (m : core_runM thread_state)
    {dst : driver_state} {fl : EvalFail}
    (hm : m dst.core_run_state0 = fl.run thread_state core_run_state dst.core_run_state0) :
    ∃ dst', runOne (advance_step tds tid (Step_with_runstate2 (RSK_tau s TSK_Misc) m)) dst =
      (NDkilled fl.reason, dst') := by
  obtain ⟨dst', h⟩ := runOne_liftCore_run_fail hm
  refine ⟨dst', ?_⟩
  unfold advance_step
  dsimp only
  refine (runOne_bind_active (z := ()) (s' := dst) (by rfl)).trans ?_
  exact runOne_bind_killed h

/-- `advance_step`'s action arm (sequential: the request is drawn from
    the request monad, the action id from `fresh_action_id'`, and
    `action_request_sequential2` discharges it — Driver.lean:273-285);
    the discharge outcome is the hypothesis. -/
theorem advance_action {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {tid : Nat} {s : String} {loc : CerbLocation.Loc}
    {req : action_request2 thread_state} {dst dst' : driver_state}
    (hars : runOne (action_request_sequential2 tds loc tid
        dst.core_run_state0.aid_supply req)
        { dst with core_run_state0 :=
            { dst.core_run_state0 with aid_supply :=
                dst.core_run_state0.aid_supply + 1 } } = (NDactive (), dst')) :
    runOne (advance_step tds tid (Step_action_request2 s loc tid false
        (stExceptUndef_return req))) dst = (NDactive NOWAKEUP, dst') := by
  unfold advance_step
  dsimp only
  refine (runOne_bind_active (z := ()) (s' := dst') ?_).trans (by rfl)
  refine (runOne_bind_active (z := req) (s' := dst)
    (runOne_liftCore_run_return req dst)).trans ?_
  unfold perform_action_request2
  dsimp only
  refine (runOne_bind_active
    (z := dst.core_run_state0.aid_supply)
    (s' := { dst with core_run_state0 :=
        { dst.core_run_state0 with aid_supply :=
            dst.core_run_state0.aid_supply + 1 } })
    (runOne_liftCore_run_aid dst)).trans ?_
  exact hars

/-- The action arm, KILLED discharge: the kill propagates through the
    remaining bind (`runOne_bind_killed`). -/
theorem advance_action_killed {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {tid : Nat} {s : String} {loc : CerbLocation.Loc}
    {req : action_request2 thread_state} {dst dst' : driver_state}
    {r : kill_reason driver_error}
    (hars : runOne (action_request_sequential2 tds loc tid
        dst.core_run_state0.aid_supply req)
        { dst with core_run_state0 :=
            { dst.core_run_state0 with aid_supply :=
                dst.core_run_state0.aid_supply + 1 } } = (NDkilled r, dst')) :
    runOne (advance_step tds tid (Step_action_request2 s loc tid false
        (stExceptUndef_return req))) dst = (NDkilled r, dst') := by
  unfold advance_step
  dsimp only
  refine runOne_bind_killed (r := r) (s' := dst') ?_
  refine (runOne_bind_active (z := req) (s' := dst)
    (runOne_liftCore_run_return req dst)).trans ?_
  unfold perform_action_request2
  dsimp only
  refine (runOne_bind_active
    (z := dst.core_run_state0.aid_supply)
    (s' := { dst with core_run_state0 :=
        { dst.core_run_state0 with aid_supply :=
            dst.core_run_state0.aid_supply + 1 } })
    (runOne_liftCore_run_aid dst)).trans ?_
  exact hars

/-- `advance_step`'s memop arm (sequential: `perform_memop_request2`,
    Driver.lean:288; no aid draw, no counter tick). -/
theorem advance_memop {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {tid : Nat} {loc : CerbLocation.Loc} {mop : memop} {cvals : List value}
    {k : value → thread_state} {dst dst' : driver_state}
    (hars : runOne (perform_memop_request2 tds loc mop cvals tid k) dst =
      (NDactive (), dst')) :
    runOne (advance_step tds tid (Step_memop_request2 loc mop cvals tid false k)) dst =
      (NDactive NOWAKEUP, dst') := by
  unfold advance_step
  dsimp only
  refine (runOne_bind_active (z := ()) (s' := dst') ?_).trans (by rfl)
  rw [if_neg (fun h => Bool.noConfusion h)]
  exact hars

/-! ## The memory operations are ONE-LAYER: active or killed
(the concrete model's `storeM`/`loadM`/`allocateObject` never produce
a nondeterministic node — CerbMem.lean:1504/1621/1667; `eqPtrval`'s
`msum` fork is the FORK instance, `complete_memop_vals`). -/

/-- `storeM`'s one-layer result is active or killed. -/
theorem storeM_layer (tds : CerbTags.TagDefsMap) (loc : CerbLocation.Loc) (ty : ctype)
    (lk : Bool) (pv : CerbMem.PointerValue) (mv : CerbMem.MemValue) (σ : Mem) :
    (∃ fp σ', runOne (CerbMem.storeM tds loc ty lk pv mv) σ = (NDactive fp, σ')) ∨
    (∃ r σ', runOne (CerbMem.storeM tds loc ty lk pv mv) σ = (NDkilled r, σ')) := by
  unfold CerbMem.storeM runOne
  dsimp only
  rcases pv with ⟨prov, base⟩
  cases prov <;> cases base <;> dsimp only <;>
    repeat' (first
      | exact Or.inl ⟨_, _, rfl⟩
      | exact Or.inr ⟨_, _, rfl⟩
      | split)

/-- `loadM`'s one-layer result is active or killed. -/
theorem loadM_layer (tds : CerbTags.TagDefsMap) (loc : CerbLocation.Loc) (ty : ctype)
    (pv : CerbMem.PointerValue) (σ : Mem) :
    (∃ p σ', runOne (CerbMem.loadM tds loc ty pv) σ = (NDactive p, σ')) ∨
    (∃ r σ', runOne (CerbMem.loadM tds loc ty pv) σ = (NDkilled r, σ')) := by
  unfold CerbMem.loadM runOne
  dsimp only
  rcases pv with ⟨prov, base⟩
  cases prov <;> cases base <;> dsimp only <;>
    repeat' (first
      | exact Or.inl ⟨_, _, rfl⟩
      | exact Or.inr ⟨_, _, rfl⟩
      | split)

/-- `allocateObject`'s one-layer result is active or killed (the
    out-of-memory kill, CerbMem.lean:1513). -/
theorem allocateObject_layer (tds : CerbTags.TagDefsMap) (tid : Nat) (pref : prefix0)
    (align : CerbMem.IntegerValue) (ty : ctype) (reqAddr : Option Int)
    (initOpt : Option CerbMem.MemValue) (σ : Mem) :
    (∃ pv σ', runOne (CerbMem.allocateObject tds tid pref align ty reqAddr initOpt) σ =
      (NDactive pv, σ')) ∨
    (∃ r σ', runOne (CerbMem.allocateObject tds tid pref align ty reqAddr initOpt) σ =
      (NDkilled r, σ')) := by
  unfold CerbMem.allocateObject runOne
  rcases align with ⟨_, alignN⟩
  dsimp only
  repeat' (first
    | exact Or.inl ⟨_, _, rfl⟩
    | exact Or.inr ⟨_, _, rfl⟩
    | split)

/-- `killM`'s one-layer result is active or killed (kill/free arc K2;
    CerbMem.lean:1555-1580 — deterministic, no `msum`). -/
theorem killM_layer (loc : CerbLocation.Loc) (isDyn : Bool) (pv : CerbMem.PointerValue)
    (σ : Mem) :
    (∃ u σ', runOne (CerbMem.killM loc isDyn pv) σ = (NDactive u, σ')) ∨
    (∃ r σ', runOne (CerbMem.killM loc isDyn pv) σ = (NDkilled r, σ')) := by
  unfold CerbMem.killM runOne
  dsimp only
  rcases pv with ⟨prov, base⟩
  cases prov <;> cases base <;> dsimp only <;>
    repeat' (first
      | exact Or.inl ⟨_, _, rfl⟩
      | exact Or.inr ⟨_, _, rfl⟩
      | split)

/-- `allocateRegion`'s one-layer result is active or killed (the
    out-of-memory kill, CerbMem.lean:1541; kill/free arc K3). -/
theorem allocateRegion_layer (tid : Nat) (pref : prefix0)
    (align size : CerbMem.IntegerValue) (σ : Mem) :
    (∃ pv σ', runOne (CerbMem.allocateRegion tid pref align size) σ = (NDactive pv, σ')) ∨
    (∃ r σ', runOne (CerbMem.allocateRegion tid pref align size) σ = (NDkilled r, σ')) := by
  unfold CerbMem.allocateRegion runOne
  rcases align with ⟨_, alignN⟩
  rcases size with ⟨_, sizeN⟩
  dsimp only
  repeat' (first
    | exact Or.inl ⟨_, _, rfl⟩
    | exact Or.inr ⟨_, _, rfl⟩
    | split)

/-- THE ALLOC REFUSAL ROW (kill/free arc K3): `allocateRegion`'s ONLY
    killed outcome is the out-of-memory kill `Other (MerrOther "out of
    memory")` at `alignedAddr == 0` (CerbMem.lean:1541 — no `failReason`,
    no UB class: a plain `Other`), and it leaves the state untouched. -/
theorem allocateRegion_killed_inv (tid : Nat) (pref : prefix0)
    (align size : CerbMem.IntegerValue) (σ : Mem) {r : kill_reason mem_error} {σ' : Mem}
    (h : runOne (CerbMem.allocateRegion tid pref align size) σ = (NDkilled r, σ')) :
    σ' = σ ∧ r = kill_reason.Other (MerrOther "out of memory") := by
  unfold CerbMem.allocateRegion runOne at h
  rcases align with ⟨_, alignN⟩
  rcases size with ⟨_, sizeN⟩
  dsimp only at h
  split at h
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h
    cases h1
    exact ⟨h2.symm, rfl⟩
  · cases (Prod.mk.inj h).1

/-- THE KILL REFUSAL ROWS (kill/free arc K2): every killed outcome of
    `killM` leaves the state untouched and carries one of exactly three
    engine reasons, at the request's own location — `failReason`
    (CerbMem.lean:1439) through `undefinedFromMem_error`
    (Mem_common.lean:392): `Free_non_matching ↦ UB179a` (a null pointer
    on the static path, a function pointer, no record at the id, a
    non-dynamic origin on the dynamic path, a `Prov_none`/`Prov_device`/
    `Prov_symbolic` pointer), `Free_dead_allocation ↦ UB179b` (a dead
    id), and the NON-UB `Free_out_of_bound ↦ Other` (a pointer not at
    the allocation's base). -/
theorem killM_killed_inv (loc : CerbLocation.Loc) (isDyn : Bool) (pv : CerbMem.PointerValue)
    (σ : Mem) {r : kill_reason mem_error} {σ' : Mem}
    (h : runOne (CerbMem.killM loc isDyn pv) σ = (NDkilled r, σ')) :
    σ' = σ ∧
    (r = Undef0 loc [UB179a_non_matching_allocation_free] ∨
     r = Undef0 loc [UB179b_dead_allocation_free] ∨
     r = kill_reason.Other (MerrUndefinedFree Free_out_of_bound)) := by
  unfold CerbMem.killM runOne at h
  dsimp only at h
  rcases pv with ⟨prov, base⟩
  cases prov <;> cases base <;> dsimp only at h <;>
    repeat' split at h
  -- the active arms are closed by constructor clash; each killed arm
  -- substitutes its reason and is one of the three rows by `rfl`
  all_goals
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    cases h1
    all_goals exact ⟨h2.symm, by first
      | exact .inl rfl
      | exact .inr (.inl rfl)
      | exact .inr (.inr rfl)⟩

/-! `applyMemM_eq_ndProj` (`applyMemM` is the active projection of the
one-layer result) lives in Heap.lean since K1. -/

/-- A one-layer memory operation that `applyMemM` refuses is KILLED. -/
theorem applyMemM_none_killed {α : Type} {m : CerbMem.memM α} {σ : Mem}
    (hlayer : (∃ z σ', runOne m σ = (NDactive z, σ')) ∨
      (∃ r σ', runOne m σ = (NDkilled r, σ')))
    (h : applyMemM m σ = none) : ∃ r σ', runOne m σ = (NDkilled r, σ') := by
  rcases hlayer with ⟨z, σ', hz⟩ | hk
  · rw [applyMemM_eq_ndProj, hz] at h
    cases h
  · exact hk

/-- `liftMem` (Driver.lean:218) of a KILLED one-layer memM computation:
    the kill is lifted by `liftAction`'s `DErr_memory` injection on the
    `Other` arm (Nondeterminism.lean:306), the memory written back. -/
theorem runOne_liftMem_killed {a : Type}
    {m : ndM a String mem_error (mem_constraint CerbMem.IntegerValue) CerbMem.MemState}
    {dst : driver_state} {r : kill_reason mem_error} {σ' : CerbMem.MemState}
    (h : runOne m dst.layout_state = (NDkilled r, σ')) :
    runOne (liftMem m) dst =
      (NDkilled (match r with
        | Undef0 l ubs => Undef0 l ubs
        | Error0 l s => Error0 l s
        | Other err => Other (DErr_memory err)),
       { dst with layout_state := σ' }) := by
  rcases m with ⟨g⟩
  dsimp only [runOne] at h
  show runOne (liftND_lemFuel lemDefaultFuel _ _ _ _ (ND g)) dst = _
  rw [show lemDefaultFuel = Nat.succ 999999 from rfl]
  unfold liftND_lemFuel
  dsimp only [runOne]
  rw [h]
  rw [show (999999 : Nat) = Nat.succ 999998 from rfl]
  unfold liftAction_lemFuel
  cases r <;> rfl

/-- StoreRequest2 discharge, KILLED (Driver.lean:273): the kill is the
    lifted `storeM` kill at the request's own location. -/
theorem ars_store_killed {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {loc : CerbLocation.Loc} {mo : memory_order}
    {ty : ctype} {lk : Bool} {pv : CerbMem.PointerValue} {mv : CerbMem.MemValue}
    {k : Nat → CerbMem.Footprint → thread_state} {tid aid : Nat}
    {dst : driver_state} {r : kill_reason mem_error} {σ' : Mem}
    (h : runOne (CerbMem.storeM tds loc ty lk pv mv) dst.layout_state = (NDkilled r, σ')) :
    runOne (action_request_sequential2 tds loc tid aid
        (StoreRequest2 mo ty lk pv mv k)) dst =
      (NDkilled (match r with
        | Undef0 l ubs => Undef0 l ubs
        | Error0 l s => Error0 l s
        | Other err => Other (DErr_memory err)),
       { dst with layout_state := σ' }) := by
  unfold action_request_sequential2
  dsimp only
  exact runOne_bind_killed (runOne_liftMem_killed h)

/-- LoadRequest2 discharge, KILLED. -/
theorem ars_load_killed {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {loc : CerbLocation.Loc} {mo : memory_order}
    {ty : ctype} {pv : CerbMem.PointerValue}
    {k : Nat → CerbMem.Footprint → CerbMem.MemValue → thread_state}
    {tid aid : Nat} {dst : driver_state} {r : kill_reason mem_error} {σ' : Mem}
    (h : runOne (CerbMem.loadM tds loc ty pv) dst.layout_state = (NDkilled r, σ')) :
    runOne (action_request_sequential2 tds loc tid aid
        (LoadRequest2 mo ty pv k)) dst =
      (NDkilled (match r with
        | Undef0 l ubs => Undef0 l ubs
        | Error0 l s => Error0 l s
        | Other err => Other (DErr_memory err)),
       { dst with layout_state := σ' }) := by
  unfold action_request_sequential2
  dsimp only
  exact runOne_bind_killed (runOne_liftMem_killed h)

/-- CreateRequest2 discharge, KILLED (the out-of-memory kill;
    `allocateObject` discards the thread id, CerbMem.lean:1504). -/
theorem ars_create_killed {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {loc : CerbLocation.Loc} {pref : prefix0}
    {align : CerbMem.IntegerValue} {ty : ctype} {reqAddr : Option Int}
    {initOpt : Option CerbMem.MemValue}
    {k : Nat → CerbMem.PointerValue → thread_state}
    {tid aid : Nat} {dst : driver_state} {r : kill_reason mem_error} {σ' : Mem}
    (h : runOne (CerbMem.allocateObject tds 0 pref align ty reqAddr initOpt)
        dst.layout_state = (NDkilled r, σ')) :
    runOne (action_request_sequential2 tds loc tid aid
        (CreateRequest2 pref align ty reqAddr initOpt k)) dst =
      (NDkilled (match r with
        | Undef0 l ubs => Undef0 l ubs
        | Error0 l s => Error0 l s
        | Other err => Other (DErr_memory err)),
       { dst with layout_state := σ' }) := by
  unfold action_request_sequential2
  dsimp only
  exact runOne_bind_killed (runOne_liftMem_killed h)

/-- KillRequest2 discharge, KILLED (kill/free arc K2; Driver.lean:273):
    the kill is the lifted `killM` kill at the request's own location
    (the reasons: `killM_killed_inv`). -/
theorem ars_kill_killed {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {loc : CerbLocation.Loc} {isDyn : Bool} {pv : CerbMem.PointerValue}
    {k : Nat → thread_state} {tid aid : Nat} {dst : driver_state}
    {r : kill_reason mem_error} {σ' : Mem}
    (h : runOne (CerbMem.killM loc isDyn pv) dst.layout_state = (NDkilled r, σ')) :
    runOne (action_request_sequential2 tds loc tid aid (KillRequest2 isDyn pv k)) dst =
      (NDkilled (match r with
        | Undef0 l ubs => Undef0 l ubs
        | Error0 l s => Error0 l s
        | Other err => Other (DErr_memory err)),
       { dst with layout_state := σ' }) := by
  unfold action_request_sequential2
  dsimp only
  exact runOne_bind_killed (runOne_liftMem_killed h)

/-- AllocRequest2 discharge, KILLED (kill/free arc K3; Driver.lean:273):
    the out-of-memory kill, lifted (`allocateRegion` discards the thread
    id, CerbMem.lean:1533). -/
theorem ars_alloc_killed {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {loc : CerbLocation.Loc} {pref : prefix0}
    {align size : CerbMem.IntegerValue}
    {k : Nat → CerbMem.PointerValue → thread_state}
    {tid aid : Nat} {dst : driver_state} {r : kill_reason mem_error} {σ' : Mem}
    (h : runOne (CerbMem.allocateRegion 0 pref align size) dst.layout_state =
      (NDkilled r, σ')) :
    runOne (action_request_sequential2 tds loc tid aid
        (AllocRequest2 pref align size k)) dst =
      (NDkilled (match r with
        | Undef0 l ubs => Undef0 l ubs
        | Error0 l s => Error0 l s
        | Other err => Other (DErr_memory err)),
       { dst with layout_state := σ' }) := by
  unfold action_request_sequential2
  dsimp only
  exact runOne_bind_killed (runOne_liftMem_killed h)

/-! ## The round's derived readings -/

/-- The denotation is injective on the chain (`Stack_cons2` is a
    constructor). -/
theorem Ctl.toStack_inj {c c' : Ctl} (h : c.toStack = c'.toStack) : c.κ = c'.κ := by
  obtain ⟨κ, p, ℓ, lc, sp⟩ := c
  obtain ⟨κ', p', ℓ', lc', sp'⟩ := c'
  simp only [Ctl.toStack] at h
  show κ = κ'
  induction κ generalizing κ' with
  | nil =>
    cases κ' with
    | nil => rfl
    | cons pc κ' => simp at h
  | cons pc κ ih =>
    cases κ' with
    | nil => simp at h
    | cons pc' κ' =>
      simp only [List.foldr_cons] at h
      injection h with h1 h2 h3
      rw [Prod.ext h1 h2, ih κ' h3]

/-- The thread literal is injective in (expression, env, control) up to
    the control's run-state supplies (E1: `Ctl.sup` is not a thread
    field — it is tied to the run state by `Embeds`). -/
theorem MachineCtx.thread_inj {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl}
    (h : M.thread e ρ ctl = M.thread e' ρ' ctl') :
    e = e' ∧ ρ = ρ' ∧ ctl = { ctl' with sup := ctl.sup } := by
  refine ⟨congrArg thread_state.arena h, congrArg thread_state.env h, ?_⟩
  have h1 := congrArg thread_state.stack0 h
  have h2 := congrArg thread_state.current_proc_opt h
  have h3 := congrArg thread_state.exec_loc h
  have h4 := congrArg thread_state.current_loc h
  obtain ⟨κ, p, ℓ, lc, sp⟩ := ctl
  obtain ⟨κ', p', ℓ', lc', sp'⟩ := ctl'
  simp only [MachineCtx.thread] at h1 h2 h3 h4
  rw [show κ = κ' from Ctl.toStack_inj h1, h2, h3, h4]

/-- THE LOOP-LEVEL READING of a shipped round: one iteration of
    `drive_nonmemory_steps_aux2` at any fuel `fl` and accumulator
    continues at the successor state — the `loop_step_frag` shape,
    at the context's own tagDefs and thread id. -/
theorem CerberusRound.loop_step {M : MachineCtx} {c c' : Config}
    (h : CerberusRound M c c') {dst : driver_state} (hemb : M.Embeds dst c)
    (fl : Nat) (acc : Fmap thread_id (List core_step2)) :
    ∃ (rs' : core_run_state) (tr : List trace_event) (ctr : Nat),
      rs'.labeled = dst.core_run_state0.labeled ∧
      runOne (drive_nonmemory_steps_aux2_lemFuel (Nat.succ fl) M.tagDefs acc [M.tid]) dst =
        runOne (drive_nonmemory_steps_aux2_lemFuel fl M.tagDefs acc [M.tid])
          { dst with
              core_state0 := update_thread_state M.tid (M.thread c'.1 c'.2.1 c'.2.2.1) dst.core_state0,
              layout_state := c'.2.2.2,
              core_run_state0 := rs', trace := tr, dr_step_counter := ctr } := by
  obtain ⟨s, hsteps, hca, rs', tr, ctr, hlab, -, -, hadv⟩ := h dst hemb
  exact ⟨rs', tr, ctr, hlab, loop_step_of_advance fl acc hemb.thread hsteps hca hadv⟩

/-- THE RUNNER-LEVEL READING: the shipped exhaustive runner
    (`CerbND.runND`, CerbND.lean:136) on the advance delivers exactly
    one `Active` execution. -/
theorem CerberusRound.runND {M : MachineCtx} {c c' : Config}
    (h : CerberusRound M c c') {dst : driver_state} (hemb : M.Embeds dst c) :
    ∃ s : core_step2,
      step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
        (M.parent, M.thread c.1 c.2.1 c.2.2.1) = [s] ∧
      ∃ (rs' : core_run_state) (tr : List trace_event) (ctr : Nat),
        CerbND.runND (advance_step M.tagDefs M.tid s) dst =
          [(nd_status.Active NOWAKEUP, ([] : List String),
            { dst with
              core_state0 := update_thread_state M.tid (M.thread c'.1 c'.2.1 c'.2.2.1) dst.core_state0,
              layout_state := c'.2.2.2,
              core_run_state0 := rs', trace := tr, dr_step_counter := ctr })] := by
  obtain ⟨s, hsteps, -, rs', tr, ctr, -, -, -, hadv⟩ := h dst hemb
  exact ⟨s, hsteps, rs', tr, ctr, runND_active hadv⟩

/-- E1 proof device: `loc_split` also normalizing a hypothesis stated at
    `th.current_loc` (the KILL bridges' classifier premise). -/
syntax "loc_split_at" ident ident : tactic
macro_rules
  | `(tactic| loc_split_at $an:ident $h:ident) =>
    `(tactic| (rcases get_loc_cases $an with ⟨loc1, hgl, hlib⟩ | ⟨loc1, hgl, hlib⟩ | ⟨hgl, hlib⟩ <;>
               simp only [locUpdTh, hgl, hlib, Bool.false_eq_true, ↓reduceIte] at $h:ident ⊢))

/-- A value is never a call redex (the `CallOf` disjunct at a value head
    is vacuous). -/
theorem Step.CallOf.not_val {M : MachineCtx} {w : SpikeValA} {fr : context → context}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {out : Config}
    (h : Step.CallOf M (ofValA w) fr ρ ctl σ out) : False := by
  obtain ⟨_, _, _, _, _, _, hc, -⟩ := h
  rw [callRedex?_ofValA] at hc
  cases hc

/-! ## THE CERTIFICATION: mirror step ⇒ shipped round -/

/-- THE UNIFIED STEP-MATCH OVER THE SHIPPED DRIVER: wherever the mirror
    steps at a `Frag` configuration (cons-shaped environment, `esize e ≤
    lemDefaultFuel`), the shipped driver's round at every embedding
    state is exactly that step — one case per redex root, each
    discharged by the engine equation of the redex (`step_ctx_*`,
    Soundness.lean / DriverCollapse.lean) and the matching
    `advance_step` arm. Stated at the context's OWN tagDefs and extern
    map (the driver functions take the reader argument; `loop_step_frag`,
    DriverCollapse.lean, has this theorem's shape at the production
    profile `fmapEmpty` — proved there independently, not derived from
    this theorem; the module header, "WHAT CONSUMES WHAT"). E1: the
    successor thread is the mirror's at the successor control — the
    general arm's location write is `Ctl.upd` (`locUpdTh_thread`); the
    run-state supplies are untouched by every round (the `Embeds` ties
    are carried to the successor control's `sup`). -/
theorem engine_step_matchU {M : MachineCtx}
    {e e' : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    {ρ' : EnvStack} {ctl ctl' : Ctl} {σ σ' : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M (e, ev0 :: evs, ctl, σ) (e', ρ', ctl', σ')) :
    CerberusRound M (e, ev0 :: evs, ctl, σ) (e', ρ', ctl', σ') := by
  intro dst hemb
  obtain ⟨hth, hlay, hfile, hext, hlabd, hsym, hexc⟩ := hemb
  simp only at hth hlay hsym hexc
  subst hlay
  cases hv : toVal e with
  | some w =>
    -- a value steps only under a frame: RETURN (bare) or REMOVE-ANNOT (annotated)
    obtain ⟨wa, -, rfl⟩ := ofValA_of_toVal hv
    cases wa with
    | pure a b v =>
      rcases hs.ctl_cases with ⟨a', heq⟩ | ⟨_, _, _, _, _, _, hc, -⟩ |
          ⟨a1', b1', v', ev0', evs', p, ctx, κ, q, ℓ, lc, sp, he, hρ, rfl, rfl, rfl, rfl, rfl⟩
      · exact (Step.pure_val_elim hs (by rw [heq]; rfl)).elim
      · rw [callRedex?_ofValA] at hc; cases hc
      · obtain ⟨rfl, rfl, rfl⟩ : a = a1' ∧ b = b1' ∧ v = v' := by simpa using ofValA_inj he
        injection hρ with h1 h2
        subst h1 h2
        obtain ⟨tsk, hsteps⟩ := step_ctx_ret v M.tagDefs dst.layout_state dst.core_file
          dst.core_extern M.tid M.parent
          (M.thread (ofValA (.pure a b v)) (ev0 :: evs) ⟨(p, ctx) :: κ, q, ℓ, lc, sp⟩) rfl rfl rfl
        obtain ⟨tr, hadv⟩ := advance_tau_tsk M.tagDefs M.tid "end of procedure" tsk _ dst
        exact ⟨_, hsteps, rfl, dst.core_run_state0, tr, dst.dr_step_counter + 1, rfl, hsym, hexc,
          hadv⟩
    | annot a a2 b ds v =>
      rcases hs.ctl_cases with ⟨a', heq⟩ | ⟨_, _, _, _, _, _, hc, -⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, _, he, -⟩
      case inr.inl => rw [callRedex?_ofValA] at hc; cases hc
      case inr.inr => cases ofValA_inj he
      have hκ' : ctl'.κ = ctl.κ := by rw [heq]; rfl
      -- REMOVE-ANNOT at a non-empty call stack (`Step.ret_annot`): the
      -- engine's tau, in place (no location write — the value arm)
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := Step.annot_val_inv hs hκ'
      refine ⟨_, step_ctx_remove_annot ds v M.tagDefs dst.layout_state dst.core_file
          dst.core_extern M.tid M.parent _ rfl,
        rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
      exact advance_tau M.tagDefs M.tid _ _ dst
  | none =>
  have hnv : toVal e = none := hv
  obtain ⟨ctx, r, hd, hfr⟩ := hf.decomp hnv
  rcases hd.step_factor hs with ⟨r', ρr, ctlr, σr, hnr, hnc, hr, heq⟩ |
    ⟨an, ra, l, pes, rfl, hr⟩ | ⟨an, ra, f, pes, params, body, vs, rfl, hvs, hfl, hlen, hout⟩
  · obtain ⟨he', hρ', hc', hσ'⟩ := Config.mk_inj heq
    subst he' hρ' hc' hσ'
    have hccall := hd.unseq_ccall_false
    have hrj := hd.redex
    cases hrj with
    | @call an ra f pes => exact absurd rfl (hnc an ra f pes)
    | @store an loc ann lk ty pv cv mo =>
      obtain ⟨mv, fp, σ'', hmv, hmem, hout⟩ := hr.store_inv
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      have hsteps := step_ctx_store hd hsz M.tagDefs hmv
        dst.layout_state dst.core_file dst.core_extern M.tid M.parent
        (M.thread e (ev0 :: evs) ctl) rfl
      rw [hccall, MachineCtx.locUpdTh_thread] at hsteps
      refine ⟨_, hsteps, rfl, { dst.core_run_state0 with aid_supply :=
          dst.core_run_state0.aid_supply + 1 },
        ME_store (requestLoc (M.thread e (ev0 :: evs) (ctl.upd an)) loc)
          none ty lk pv mv :: dst.trace,
        dst.dr_step_counter, rfl, hsym, hexc, ?_⟩
      exact advance_action (ars_store_active (tid := M.tid)
        (aid := dst.core_run_state0.aid_supply) hmem)
    | @load an loc ann ty pv mo =>
      obtain ⟨fp, mval, σ'', hmem, hout⟩ := hr.load_inv
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      have hsteps := step_ctx_load hd hsz M.tagDefs
        dst.layout_state dst.core_file dst.core_extern M.tid M.parent
        (M.thread e (ev0 :: evs) ctl) rfl
      rw [hccall, MachineCtx.locUpdTh_thread] at hsteps
      refine ⟨_, hsteps, rfl, { dst.core_run_state0 with aid_supply :=
          dst.core_run_state0.aid_supply + 1 },
        ME_load (requestLoc (M.thread e (ev0 :: evs) (ctl.upd an)) loc)
          none ty pv mval :: dst.trace,
        dst.dr_step_counter, rfl, hsym, hexc, ?_⟩
      exact advance_action (ars_load_active (tid := M.tid)
        (aid := dst.core_run_state0.aid_supply) hmem)
    | @create an loc ann align ty pref =>
      obtain ⟨pv, σ'', hmem, hout⟩ := hr.create_inv
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      have hsteps := step_ctx_create hd hsz M.tagDefs
        dst.layout_state dst.core_file dst.core_extern M.tid M.parent
        (M.thread e (ev0 :: evs) ctl) rfl
      rw [hccall, MachineCtx.locUpdTh_thread] at hsteps
      refine ⟨_, hsteps, rfl, { dst.core_run_state0 with aid_supply :=
          dst.core_run_state0.aid_supply + 1 },
        ME_allocate_object M.tid pref align ty none pv :: dst.trace,
        dst.dr_step_counter, rfl, hsym, hexc, ?_⟩
      exact advance_action (ars_create_active (tid := M.tid)
        (aid := dst.core_run_state0.aid_supply) hmem)
    | @create_op an loc ann pref pe1 pe2 hnvC =>
      obtain ⟨hp1, hp2, hd1, hd2⟩ : PePure pe1 ∧ PePure pe2 ∧
          peDepth pe1 ≤ lemDefaultFuel ∧ peDepth pe2 ≤ lemDefaultFuel := by
        cases hfr with
        | create =>
          rw [valueFromPexprs_pair, valueFromPexpr_val, valueFromPexpr_val] at hnvC
          cases hnvC
        | create_op hnvC' hp1 hp2 hd1 hd2 => exact ⟨hp1, hp2, hd1, hd2⟩
      obtain ⟨al, ty, hv1, hv2, hout⟩ := hr.create_op_inv hnvC
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_create_eval_ws hd hsz hnvC hp1 hp2 hd1 hd2
        M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
        (M.thread e (ev0 :: evs) ctl) rfl
        (by rw [hext]; exact hv1) (by rw [hext]; exact hv2)
      rw [MachineCtx.locUpdTh_thread] at hm
      refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
      exact advance_withrs_eval M.tagDefs M.tid s m (hm dst.core_run_state0)
    | @kill an loc ann kind pv =>
      obtain ⟨σ'', hmem, hout⟩ := hr.kill_inv
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      have hsteps := step_ctx_kill hd hsz M.tagDefs
        dst.layout_state dst.core_file dst.core_extern M.tid M.parent
        (M.thread e (ev0 :: evs) ctl) rfl
      rw [hccall, MachineCtx.locUpdTh_thread] at hsteps
      refine ⟨_, hsteps, rfl, { dst.core_run_state0 with aid_supply :=
          dst.core_run_state0.aid_supply + 1 },
        ME_kill (requestLoc (M.thread e (ev0 :: evs) (ctl.upd an)) loc)
          (is_dynamic kind) pv :: dst.trace,
        dst.dr_step_counter, rfl, hsym, hexc, ?_⟩
      exact advance_action (ars_kill_active (tid := M.tid)
        (aid := dst.core_run_state0.aid_supply) hmem)
    | @kill_op an loc ann kind pe hnvK =>
      obtain ⟨hpK, hdK⟩ : PePure pe ∧ peDepth pe ≤ lemDefaultFuel := by
        cases hfr with
        | kill =>
          rw [show valueFromPexpr (Pexpr [] () (PEval
            (Vobject (OVpointer _)))) = some _ from rfl] at hnvK
          cases hnvK
        | kill_op hnvK' hpK hdK => exact ⟨hpK, hdK⟩
      obtain ⟨pv, hv, hout⟩ := hr.kill_op_inv hnvK
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_kill_eval_ws hd hsz hnvK hpK hdK
        M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
        (M.thread e (ev0 :: evs) ctl) rfl
        (by rw [hext]; exact hv)
      rw [MachineCtx.locUpdTh_thread] at hm
      refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
      exact advance_withrs_eval M.tagDefs M.tid s m (hm dst.core_run_state0)
    | @alloc an loc ann align size pref =>
      obtain ⟨pv, σ'', hmem, hout⟩ := hr.alloc_inv
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      have hsteps := step_ctx_alloc hd hsz M.tagDefs
        dst.layout_state dst.core_file dst.core_extern M.tid M.parent
        (M.thread e (ev0 :: evs) ctl) rfl
      rw [hccall, MachineCtx.locUpdTh_thread] at hsteps
      refine ⟨_, hsteps, rfl, { dst.core_run_state0 with aid_supply :=
          dst.core_run_state0.aid_supply + 1 },
        ME_allocate_region M.tid pref align size pv :: dst.trace,
        dst.dr_step_counter, rfl, hsym, hexc, ?_⟩
      exact advance_action (ars_alloc_active (tid := M.tid)
        (aid := dst.core_run_state0.aid_supply) hmem)
    | @alloc_op an loc ann pref pe1 pe2 hnvA =>
      obtain ⟨hp1, hp2, hd1, hd2⟩ : PePure pe1 ∧ PePure pe2 ∧
          peDepth pe1 ≤ lemDefaultFuel ∧ peDepth pe2 ≤ lemDefaultFuel := by
        cases hfr with
        | alloc =>
          rw [valueFromPexprs_pair, valueFromPexpr_val, valueFromPexpr_val] at hnvA
          cases hnvA
        | alloc_op hnvA' hp1 hp2 hd1 hd2 => exact ⟨hp1, hp2, hd1, hd2⟩
      obtain ⟨al, sz, hv1, hv2, hout⟩ := hr.alloc_op_inv hnvA
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_alloc_eval_ws hd hsz hnvA hp1 hp2 hd1 hd2
        M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
        (M.thread e (ev0 :: evs) ctl) rfl
        (by rw [hext]; exact hv1) (by rw [hext]; exact hv2)
      rw [MachineCtx.locUpdTh_thread] at hm
      refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
      exact advance_withrs_eval M.tagDefs M.tid s m (hm dst.core_run_state0)
    | @beta_pure an pa a1 b1 bty v e2 =>
      rcases hr.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
          ⟨_, _, a1', b1', v', _, _, _, he1, _, hout⟩ |
          ⟨_, _, _, _, _, ds', v', _, _, _, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
          hcall
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · obtain ⟨rfl, rfl, rfl⟩ : a1 = a1' ∧ b1 = b1' ∧ v = v' := by
          simpa using ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_beta_pure hd hsz M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl rfl
        rw [MachineCtx.locUpdTh_thread] at hsteps
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · cases ofValA_inj he1
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · exact (specPat_ne_base hpat).elim
      · exact (specPat_ne_base hpat).elim
      · exact (symPat_ne_base hpat).elim
      · exact (symPat_ne_base hpat).elim
      · exact (tuplePat_ne_base hpatT1).elim
      · exact (tuplePat_ne_base hpatT2).elim
      · exact hcall.not_val.elim
    | @beta_annot an pa a1 a2 b1 bty ds v e2 =>
      rcases hr.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
          ⟨_, _, _, _, v', _, _, _, he1, _, hout⟩ |
          ⟨_, _, a1', a2', b1', ds', v', _, _, _, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
          hcall
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · cases ofValA_inj he1
      · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ : a1 = a1' ∧ a2 = a2' ∧ b1 = b1' ∧ ds = ds' ∧ v = v' := by
          simpa using ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_beta_annot hd hsz M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl rfl
        rw [MachineCtx.locUpdTh_thread] at hsteps
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · exact (specPat_ne_base hpat).elim
      · exact (specPat_ne_base hpat).elim
      · exact (symPat_ne_base hpat).elim
      · exact (symPat_ne_base hpat).elim
      · exact (tuplePat_ne_base hpatT1).elim
      · exact (tuplePat_ne_base hpatT2).elim
      · exact hcall.not_val.elim
    | @wbeta_pure an pa a1 b1 bty v e2 =>
      rcases hr.wseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
          ⟨_, _, a1', b1', v', _, _, _, he1, _, hout⟩ |
          ⟨_, _, _, _, _, ds', v', _, _, _, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, hpatS1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, hpatS2, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
          hcall
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · obtain ⟨rfl, rfl, rfl⟩ : a1 = a1' ∧ b1 = b1' ∧ v = v' := by
          simpa using ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_wseq_pure hd hsz M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl rfl
        rw [MachineCtx.locUpdTh_thread] at hsteps
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · cases ofValA_inj he1
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · exact (symPat_ne_base hpatS1).elim
      · exact (symPat_ne_base hpatS2).elim
      · exact (tuplePat_ne_base hpatT1).elim
      · exact (tuplePat_ne_base hpatT2).elim
      · exact hcall.not_val.elim
    | @wbeta_annot an pa a1 a2 b1 bty ds v e2 =>
      rcases hr.wseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
          ⟨_, _, _, _, v', _, _, _, he1, _, hout⟩ |
          ⟨_, _, a1', a2', b1', ds', v', _, _, _, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, hpatS1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, hpatS2, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
          hcall
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · cases ofValA_inj he1
      · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ : a1 = a1' ∧ a2 = a2' ∧ b1 = b1' ∧ ds = ds' ∧ v = v' := by
          simpa using ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_wseq_annot hd hsz M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl rfl
        rw [MachineCtx.locUpdTh_thread] at hsteps
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · exact (symPat_ne_base hpatS1).elim
      · exact (symPat_ne_base hpatS2).elim
      · exact (tuplePat_ne_base hpatT1).elim
      · exact (tuplePat_ne_base hpatT2).elim
      · exact hcall.not_val.elim
    | @merge an a2 ds1 ds2 b hirr =>
      rcases hr.annot_inv with ⟨hg, hnj, hnc', hnv', b', ρ'', ctl'', σ'', hstep, hout⟩ |
          ⟨a2', ds2', c, hbeq, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩ |
          ⟨hg2, -⟩ | ⟨a2', b1', v', pc', κ', hb', hκ', hout'⟩
      · rw [show annotRooted (Expr a2 (Eannot ds2 b)) = true from rfl] at hg
        cases hg
      · injection hbeq with hb1 hb2
        injection hb2 with hb3 hb4
        subst hb1 hb3 hb4
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_merge hd hirr hsz M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl
        rw [MachineCtx.locUpdTh_thread] at hsteps
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · rw [show annotRooted (Expr a2 (Eannot ds2 b)) = true from rfl] at hg
        cases hg
      · rw [show annotRooted (Expr a2 (Eannot ds2 b)) = true from rfl] at hg2
        cases hg2
      · cases hb'
    | @save an sb ps body =>
      have hdep : ∀ pe ∈ saveParamPexprs ps, peDepth pe ≤ lemDefaultFuel := by
        cases hfr with
        | save _ hdep _ => exact hdep
      rcases hr.save_inv with ⟨cvals, ev0', evs', hρeq, hvals, hout⟩ |
          ⟨cvals, hnvS, hvals, hout⟩
      · obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_save hd hsz hvals M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl rfl
        rw [MachineCtx.locUpdTh_thread] at hsteps
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_save_eval_ws hd hsz hnvS hdep
          M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl
          (by rw [hext]; exact hvals)
        rw [MachineCtx.locUpdTh_thread] at hm
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_withrs_eval M.tagDefs M.tid s m (hm dst.core_run_state0)
    | @if_ an g e2 e3 =>
      have hdg : peDepth g ≤ lemDefaultFuel := by
        cases hfr with
        | if_ _ hdg _ _ => exact hdg
      rcases hr.if_inv with ⟨hg, hout⟩ | ⟨hg, hout⟩
      · obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_if_true_ws hd hsz hdg
          M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl
          (by rw [hext]; exact hg)
        rw [MachineCtx.locUpdTh_thread] at hm
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_withrs_tau M.tagDefs M.tid s m (hm dst.core_run_state0)
      · obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_if_false_ws hd hsz hdg
          M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl
          (by rw [hext]; exact hg)
        rw [MachineCtx.locUpdTh_thread] at hm
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_withrs_tau M.tagDefs M.tid s m (hm dst.core_run_state0)
    | @case_ an pe pats =>
      cases hfr with
      | case_value hbr hbsz =>
        obtain ⟨e'', hsel, hout⟩ := hr.case_value_inv (valueFromPexpr_val _ _)
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_case_value hd hsz hsel M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl
        rw [MachineCtx.locUpdTh_thread] at hsteps
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
    | @run an ra l pes =>
      exact absurd rfl (hnr an ra l pes)
    | @pure_e an pe hnv2 =>
      obtain ⟨hpp, hdp⟩ : PePure pe ∧ peDepth pe ≤ lemDefaultFuel := by
        cases hfr with
        | val_pure v => rw [valueFromPexpr_val] at hnv2; cases hnv2
        | pure_op hnv' hpp hdp => exact ⟨hpp, hdp⟩
      obtain ⟨v, -, hv, hout⟩ := hr.pure_inv hnv2
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_pure_op_ws hd hsz hnv2 hdp
        M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
        (M.thread e (ev0 :: evs) ctl) rfl
        (by rw [hext]; exact hv)
      rw [MachineCtx.locUpdTh_thread] at hm
      refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
      exact advance_withrs_eval M.tagDefs M.tid s m (hm dst.core_run_state0)
    | @load_op an loc ann ty pe2 mo hnv2 =>
      obtain ⟨hp2, hd2⟩ : PePure pe2 ∧ peDepth pe2 ≤ lemDefaultFuel := by
        cases hfr with
        | load =>
          rw [show valueFromPexpr (Pexpr [] () (PEval
            (Vobject (OVpointer _)))) = some _ from rfl] at hnv2
          cases hnv2
        | load_op hnv2' hp2 hd2 => exact ⟨hp2, hd2⟩
      obtain ⟨pv, hv2, hout⟩ := hr.load_op_inv hnv2
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_load_eval_ws hd hsz hnv2 hp2 hd2
        M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
        (M.thread e (ev0 :: evs) ctl) rfl
        (by rw [hext]; exact hv2)
      rw [MachineCtx.locUpdTh_thread] at hm
      refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
      exact advance_withrs_eval M.tagDefs M.tid s m (hm dst.core_run_state0)
    | @beta_spec an pa pb x bty wa e2 =>
      rcases hr.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
          ⟨_, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, _, _, _, ds', v', _, _, hpat, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨pa', pb', x', bty', a1', b1', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', pb', x', bty', a1', a2', b1', ds', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', x', bty', a1', b1', v', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', x', bty', a1', a2', b1', ds', v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
          hcall
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · exact (specPat_ne_base hpat.symm).elim
      · exact (specPat_ne_base hpat.symm).elim
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := specPat_inj hpat
        obtain rfl := ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_beta_spec_pure hd hsz M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl rfl
        rw [MachineCtx.locUpdTh_thread] at hsteps
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := specPat_inj hpat
        obtain rfl := ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_beta_spec_annot hd hsz M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl rfl
        rw [MachineCtx.locUpdTh_thread] at hsteps
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · exact (symPat_ne_spec hpat).elim
      · exact (symPat_ne_spec hpat).elim
      · exact (specPat_ne_tuple hpatT1).elim
      · exact (specPat_ne_tuple hpatT2).elim
      · exact hcall.not_val.elim
    | @memop an mop pes =>
      cases hfr with
      | memop_vals v1 v2 =>
        obtain ⟨pv1, pv2, b, σ'', rfl, rfl, hmem, hout⟩ := hr.memop_vals_inv
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_memop hd hsz rfl rfl M.tagDefs
          dst.layout_state dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl
        rw [hccall, MachineCtx.locUpdTh_thread] at hsteps
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter, rfl,
          hsym, hexc, ?_⟩
        exact advance_memop (ars_memop_active M.tagDefs (by
          rw [eqPtrval_loc_irrel _ default pv1 pv2]; exact hmem))
      | memop_op hnvF hp1 hp2 hpd1 hpd2 =>
        obtain ⟨v1, v2, hv1', hv2', hout⟩ := hr.memop_op_inv hnvF
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_memop_eval_ws hd hsz hnvF
          hpd1 hpd2 M.tagDefs dst.layout_state dst.core_file
          dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl
          (by rw [hext]; exact hv1') (by rw [hext]; exact hv2')
        rw [MachineCtx.locUpdTh_thread] at hm
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_withrs_eval M.tagDefs M.tid s m (hm dst.core_run_state0)
    | @store_op an loc ann ty pe2 pe3 mo hnvR =>
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
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_store_eval_ws hd hsz hnvR
        hp2 hp3 hpd2 hpd3 M.tagDefs dst.layout_state dst.core_file
        dst.core_extern M.tid M.parent
        (M.thread e (ev0 :: evs) ctl) rfl
        (by rw [hext]; exact hv2) (by rw [hext]; exact hv3)
      rw [MachineCtx.locUpdTh_thread] at hm
      refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
      exact advance_withrs_eval M.tagDefs M.tid s m (hm dst.core_run_state0)
    | @beta_sym an pa x bty wa e2 =>
      rcases hr.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
          ⟨_, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, _, _, _, ds', v', _, _, hpat, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨pa', pb', x', bty', a1', b1', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', pb', x', bty', a1', a2', b1', ds', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', x', bty', a1', b1', v', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', x', bty', a1', a2', b1', ds', v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
          hcall
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · exact (symPat_ne_base hpat.symm).elim
      · exact (symPat_ne_base hpat.symm).elim
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · exact (symPat_ne_spec hpat.symm).elim
      · exact (symPat_ne_spec hpat.symm).elim
      · obtain ⟨rfl, rfl, rfl⟩ := symPat_inj hpat
        obtain rfl := ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_beta_sym_pure hd hsz M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl rfl
        rw [MachineCtx.locUpdTh_thread] at hsteps
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · obtain ⟨rfl, rfl, rfl⟩ := symPat_inj hpat
        obtain rfl := ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_beta_sym_annot hd hsz M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl rfl
        rw [MachineCtx.locUpdTh_thread] at hsteps
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · exact (symPat_ne_tuple hpatT1).elim
      · exact (symPat_ne_tuple hpatT2).elim
      · exact hcall.not_val.elim
    | @beta_tuple an pa ls wa e2 =>
      rcases hr.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
          ⟨_, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, _, _, _, ds', v', _, _, hpat, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨pa', ls', a1', b1', vs', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', ls', a1', a2', b1', ds', vs', _, _, hpat, he1, _, hout⟩ |
          hcall
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · exact (tuplePat_ne_base hpat.symm).elim
      · exact (tuplePat_ne_base hpat.symm).elim
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · exact (specPat_ne_tuple hpat.symm).elim
      · exact (specPat_ne_tuple hpat.symm).elim
      · exact (symPat_ne_tuple hpat.symm).elim
      · exact (symPat_ne_tuple hpat.symm).elim
      · obtain ⟨rfl, rfl⟩ := tuplePat_inj hpat
        obtain rfl := ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_sseq_val_pure hd hsz M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl rfl
        rw [MachineCtx.locUpdTh_thread] at hsteps
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · obtain ⟨rfl, rfl⟩ := tuplePat_inj hpat
        obtain rfl := ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_sseq_val_annot hd hsz M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl rfl
        rw [MachineCtx.locUpdTh_thread] at hsteps
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · exact hcall.not_val.elim
    | @wbeta_tuple an pa ls wa e2 =>
      rcases hr.wseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
          ⟨_, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, _, _, _, ds', v', _, _, hpat, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨pa', ls', a1', b1', vs', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', ls', a1', a2', b1', ds', vs', _, _, hpat, he1, _, hout⟩ |
          hcall
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · exact (tuplePat_ne_base hpat.symm).elim
      · exact (tuplePat_ne_base hpat.symm).elim
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · exact (symPat_ne_tuple hpat.symm).elim
      · exact (symPat_ne_tuple hpat.symm).elim
      · obtain ⟨rfl, rfl⟩ := tuplePat_inj hpat
        obtain rfl := ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_wseq_val_pure hd hsz M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl rfl
        rw [MachineCtx.locUpdTh_thread] at hsteps
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · obtain ⟨rfl, rfl⟩ := tuplePat_inj hpat
        obtain rfl := ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_wseq_val_annot hd hsz M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl rfl
        rw [MachineCtx.locUpdTh_thread] at hsteps
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · exact hcall.not_val.elim
    | @wbeta_sym an pa x bty wa e2 =>
      rcases hr.wseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
          ⟨_, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, _, _, _, ds', v', _, _, hpat, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨pa', x', bty', a1', b1', v', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', x', bty', a1', a2', b1', ds', v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          hcall
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · exact (symPat_ne_base hpat.symm).elim
      · exact (symPat_ne_base hpat.symm).elim
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · obtain ⟨rfl, rfl, rfl⟩ := symPat_inj hpat
        obtain rfl := ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_wseq_val_pure hd hsz M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl rfl
        rw [MachineCtx.locUpdTh_thread] at hsteps
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · obtain ⟨rfl, rfl, rfl⟩ := symPat_inj hpat
        obtain rfl := ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_wseq_val_annot hd hsz M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl rfl
        rw [MachineCtx.locUpdTh_thread] at hsteps
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · exact (symPat_ne_tuple hpat).elim
      · exact (symPat_ne_tuple hpat).elim
      · exact hcall.not_val.elim
    | @bound_pure an a1 b1 v =>
      rcases hr.bound_inv with ⟨b', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
          ⟨a1', b1', v', hb, hout⟩ | ⟨_, _, _, _, _, hb, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ | hcall
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · obtain ⟨rfl, rfl, rfl⟩ : a1 = a1' ∧ b1 = b1' ∧ v = v' := by
          simpa using ofValA_inj hb
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_bound_pure hd hsz M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl
        rw [MachineCtx.locUpdTh_thread] at hsteps
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · cases ofValA_inj hb
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · exact hcall.not_val.elim
    | @bound_annot an a1 a2 b1 ds v =>
      rcases hr.bound_inv with ⟨b', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
          ⟨_, _, _, hb, hout⟩ | ⟨a1', a2', b1', ds', v', hb, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ | hcall
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · cases ofValA_inj hb
      · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ : a1 = a1' ∧ a2 = a2' ∧ b1 = b1' ∧ ds = ds' ∧ v = v' := by
          simpa using ofValA_inj hb
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_bound_annot hd hsz M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs) ctl) rfl
        rw [MachineCtx.locUpdTh_thread] at hsteps
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · exact hcall.not_val.elim
  · -- the jump disjunct: the context is discarded, the label read
    -- resolves in the DRIVER'S run state through the tie hQd
    obtain ⟨params, cont, vs, ev0', evs', hρeq, hl, hvs, hout⟩ :=
      hr.jump_inv (by rfl)
    have hdep : ∀ pe' ∈ pes, peDepth pe' ≤ lemDefaultFuel := by
      cases hfr with
      | run _ hdep => exact hdep
    obtain ⟨p, hproc, hQd⟩ := MachineCtx.labels_lookup_some hl
    obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
    subst h1 h2 h3 h4
    obtain ⟨s, m, hsteps, hm⟩ := step_ctx_run_ws hd hsz hl hdep
      M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent p
      (M.thread e (ev0 :: evs) ctl) rfl hproc
      (by rw [hext]; exact hvs)
    rw [MachineCtx.locUpdTh_thread] at hm
    refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl,
      hsym, hexc, ?_⟩
    exact advance_withrs_eval M.tagDefs M.tid s m
      (hm dst.core_run_state0 (by unfold LabeledAt; rw [hext, hlabd]; exact hQd))
  · -- THE CALL: `step_ctx_call_ws` + `advance_withrs_eval` (run state verbatim)
    have hdep : ∀ pe' ∈ pes, peDepth pe' ≤ lemDefaultFuel := by
      cases hfr with
      | call _ hdep => exact hdep
    obtain ⟨h1, h2, h4, h3⟩ := Config.mk_inj hout
    subst h1 h2 h4 h3
    obtain ⟨m, hsteps, hm⟩ := step_ctx_call_ws hd hsz hdep M.tagDefs dst.layout_state
      dst.core_file dst.core_extern M.tid M.parent (M.thread e (ev0 :: evs) ctl) rfl
      (by rw [hext]; exact hvs) (by rw [hfile, hext]; exact hfl) hlen
    rw [MachineCtx.locUpdTh_thread] at hm
    refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl,
      hsym, hexc, ?_⟩
    exact advance_withrs_eval M.tagDefs M.tid _ m (hm dst.core_run_state0)


/-- MATCH-GIVEN-STEP as a relation inclusion (`engine_step_matchU`
    re-read at a configuration successor). -/
theorem Step.toCerberusRound {M : MachineCtx} {e : CoreExpr}
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem} {c' : Config}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M (e, ev0 :: evs, ctl, σ) c') :
    CerberusRound M (e, ev0 :: evs, ctl, σ) c' := by
  obtain ⟨e', ρ', ctl', σ'⟩ := c'
  exact engine_step_matchU hf hsz hs

/-- THE TWO-SIDED ARM, GIVEN A MIRROR STEP: wherever the mirror steps
    at all, `Step` and the shipped round coincide (both directions), for
    every successor. The hypothesis `hstep` is load-bearing: at an
    annotated value the shipped round is the REMOVE-ANNOT tau while the
    mirror does not step (the value protocol) — see the classification. -/
theorem step_iff_cerberusRound {M : MachineCtx} {e : CoreExpr}
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hstep : ∃ c', Step M (e, ev0 :: evs, ctl, σ) c') (c' : Config) :
    Step M (e, ev0 :: evs, ctl, σ) c' ↔ CerberusRound M (e, ev0 :: evs, ctl, σ) c' := by
  constructor
  · exact Step.toCerberusRound hf hsz
  · intro hr
    obtain ⟨c₀, hs₀⟩ := hstep
    have hr₀ := Step.toCerberusRound hf hsz hs₀
    obtain ⟨dst, hemb⟩ := M.embeds_exists (e, ev0 :: evs, ctl, σ)
    obtain ⟨s, hsteps, -, rs', tr, ctr, -, hsym, hexc, hadv⟩ := hr dst hemb
    obtain ⟨s₀, hsteps₀, -, rs₀, tr₀, ctr₀, -, hsym₀, hexc₀, hadv₀⟩ := hr₀ dst hemb
    obtain rfl : s₀ = s := by
      rw [hsteps₀] at hsteps
      exact (List.cons.inj hsteps).1
    rw [hadv₀] at hadv
    have hD := (Prod.mk.inj hadv).2
    obtain ⟨e', ρ', ctl', σ'⟩ := c'
    obtain ⟨e₀, ρ₀, ctl₀, σ₀⟩ := c₀
    have hcs := congrArg (fun d : driver_state => d.core_state0.thread_states) hD
    have hlay := congrArg (fun d : driver_state => d.layout_state) hD
    have hrs := congrArg (fun d : driver_state => d.core_run_state0) hD
    simp only at hcs hlay hrs hsym hexc hsym₀ hexc₀
    rw [update_thread_state_single' M.tid M.parent _ _ _ hemb.thread,
      update_thread_state_single' M.tid M.parent _ _ _ hemb.thread] at hcs
    simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true] at hcs
    obtain ⟨rfl, rfl, hctl⟩ := MachineCtx.thread_inj hcs
    subst hlay
    -- the supplies: read off the (equal) successor run states
    subst hrs
    obtain ⟨κ, p, ℓ, lc, sp⟩ := ctl'
    obtain ⟨κ₀, p₀, ℓ₀, lc₀, sp₀⟩ := ctl₀
    simp only [Ctl.mk.injEq] at hctl
    obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hctl
    obtain ⟨sy, ex⟩ := sp
    obtain ⟨sy₀, ex₀⟩ := sp₀
    simp only at hsym hexc hsym₀ hexc₀
    obtain rfl : sy₀ = sy := hsym₀.symm.trans hsym
    obtain rfl : ex₀ = ex := hexc₀.symm.trans hexc
    exact hs₀

/-! ## The exhaustive per-configuration classification -/

/-- The classification (statement in the module header). -/
inductive RoundClass (M : MachineCtx) (c : Config) : Prop where
  | value_done (a b : List _root_.annot) (v : value) :
      c.1 = ofValA (.pure a b v) →
      (∀ dst, M.Embeds dst c →
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread c.1 c.2.1 c.2.2.1) = [Step_done2 v]) →
      RoundClass M c
  | value_annot (a a2 b : List _root_.annot) (ds : List dyn_annotation) (v : value) :
      c.1 = ofValA (.annot a a2 b ds v) →
      CerberusRound M c (ofValA (.pure a2 b v), c.2.1, c.2.2.1, c.2.2.2) →
      RoundClass M c
  | step (c' : Config) :
      Step M c c' →
      (∀ c'', Step M c c'' ↔ CerberusRound M c c'') →
      RoundClass M c
  | refused :
      toVal c.1 = none →
      (∀ c', ¬ Step M c c') →
      ShippedRefusal M c →
      RoundClass M c
  | open_ :
      toVal c.1 = none →
      (∀ c', ¬ Step M c c') →
      OpenRound M c →
      RoundClass M c

/-- PROGRAM-DONE at a bare value, in the shipped driver's terms (reads
    exactly the two selectors of the value arm: the live control's EMPTY
    STACK selects PROGRAM-DONE over RETURN, `SeqWF`'s no-parent selects it
    over THREAD-DONE). -/
theorem shipped_done {a1 b1 : List _root_.annot} {M : MachineCtx} (hwf : M.SeqWF) (v : value) (ρ : EnvStack)
    {ctl : Ctl} (hκ : ctl.κ = []) (dst : driver_state) :
    step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
      (M.parent, M.thread (ofValA (.pure a1 b1 v)) ρ ctl) = [Step_done2 v] := by
  rw [hwf.parent]
  exact step_ctx_done v M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
    (M.thread (ofValA (.pure a1 b1 v)) ρ ctl) rfl (Ctl.toStack_of_κ_nil hκ)

/-- REMOVE-ANNOT at an annotated value is a shipped round to the bare
    value (env and memory verbatim; no context field read). -/
theorem shipped_remove_annot (M : MachineCtx) (a a2 b : List _root_.annot)
    (ds : List dyn_annotation) (v : value) (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    CerberusRound M (ofValA (.annot a a2 b ds v), ρ, ctl, σ) (ofValA (.pure a2 b v), ρ, ctl, σ) := by
  intro dst hemb
  obtain ⟨hth, hlay, -, -, -, hsym, hexc⟩ := hemb
  simp only at hth hlay
  subst hlay
  refine ⟨_, step_ctx_remove_annot ds v M.tagDefs dst.layout_state dst.core_file
      dst.core_extern M.tid M.parent (M.thread (ofValA (.annot a a2 b ds v)) ρ ctl) rfl,
    rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
  exact advance_tau M.tagDefs M.tid _ _ dst

/-- The arms are mutually exclusive (the classification is a
    partition, not merely a cover): a value at the EMPTY call stack is
    never a mirror step (value protocol; C2: under a frame it is the
    RETURN redex, `complete_ret`), and `step`/`refused` contradict
    directly. -/
theorem RoundClass.value_not_step {M : MachineCtx} {c : Config} {w : SpikeValA}
    (he : c.1 = ofValA w) (hκ : c.2.2.1.κ = []) : ∀ c', ¬ Step M c c' := by
  intro c' hs
  obtain ⟨e, ρ, ctl, σ⟩ := c
  simp only at he hκ
  subst he
  exact hs.val_elim hκ

/-! ## Per-row REFUSAL classification, in the shipped driver's terms

Where the mirror is stuck at one of these redexes, the shipped round
is a KILL (the memory operation's `NDkilled`, lifted by `liftMem`) or
an ILLTYPED report — never a successful round. -/

/-- The refusal classification at a STORE redex: the ILLTYPED report
    when the value does not encode at the lvalue type
    (`step_action`'s Store0 arm, Core_reduction.lean:424), else
    `storeM`'s kill (CerbMem.lean:1667 — the `MerrAccess` UB kills
    arrive as `Undef0`, the ill-typed-memory-value/`MerrOther` kills as
    `Other (DErr_memory _)`), at the request's own location. -/
theorem cerberusRound_refused_store {an : List _root_.annot} (M : MachineCtx)
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
    {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem)
    (hstuck : ∀ c', ¬ Step M (storeRedex an loc ann lk ty pv cv mo, ρ, ctl, σ) c') :
    ShippedRefusal M (storeRedex an loc ann lk ty pv cv mo, ρ, ctl, σ) := by
  have hsz : esize (storeRedex an loc ann lk ty pv cv mo) ≤ lemDefaultFuel := by
    rw [show esize (storeRedex an loc ann lk ty pv cv mo) = 1 from rfl]
    unfold lemDefaultFuel
    omega
  cases hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv with
  | none =>
    refine .error (String.append (CerbLocation.stringFromLocation loc)
        (String.append "the value of a store("
          (String.append (CerbPP.stringFromCore_ctype (Ctype [] (unatomic_ ty)))
            (String.append ") didn't match the lvalue type: "
              (CerbPP.stringFromCore_value cv))))) ?_
    intro dst hemb
    obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
    simp only at hlay
    subst hlay
    exact step_ctx_store_illtyped (Decomp.root Redex.store) hsz M.tagDefs hmv
      dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
  | some mv =>
    have hnone : applyMemM (CerbMem.storeM M.tagDefs
        (requestLoc (locUpdTh an (M.thread (storeRedex an loc ann lk ty pv cv mo) ρ ctl)) loc) ty lk pv mv) σ =
        none := by
      rw [storeM_loc_irrel loc]
      cases hmem : applyMemM (CerbMem.storeM M.tagDefs loc ty lk pv mv) σ with
      | none => rfl
      | some fpσ =>
        obtain ⟨fp, σ'⟩ := fpσ
        exact absurd (Step.store_canonical hmv hmem) (hstuck _)
    obtain ⟨r, σ', hk⟩ := applyMemM_none_killed (storeM_layer _ _ _ _ _ _ _) hnone
    apply ShippedRefusal.killed
    intro dst hemb
    obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
    simp only at hlay
    subst hlay
    have hsteps := step_ctx_store (Decomp.root Redex.store) hsz M.tagDefs hmv
      dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
    rw [show is_unseq_with_ccall CTX = false from rfl] at hsteps
    exact ⟨_, _, hsteps, rfl, advance_action_killed (ars_store_killed hk)⟩

/-- The refusal classification at a LOAD redex: `loadM`'s kill
    (CerbMem.lean:1621 — null/function/out-of-bounds/dead pointers are
    `MerrAccess` UB kills, `Undef0`; the trap representation and
    outside-lifetime kills likewise per `failReason`), at the request's
    own location. -/
theorem cerberusRound_refused_load {an : List _root_.annot} (M : MachineCtx)
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pv : CerbMem.PointerValue} {mo : memory_order}
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem)
    (hstuck : ∀ c', ¬ Step M (loadRedex an loc ann ty pv mo, ρ, ctl, σ) c') :
    ShippedRefusal M (loadRedex an loc ann ty pv mo, ρ, ctl, σ) := by
  have hsz : esize (loadRedex an loc ann ty pv mo) ≤ lemDefaultFuel := by
    rw [show esize (loadRedex an loc ann ty pv mo) = 1 from rfl]
    unfold lemDefaultFuel
    omega
  have hnone : applyMemM (CerbMem.loadM M.tagDefs
      (requestLoc (locUpdTh an (M.thread (loadRedex an loc ann ty pv mo) ρ ctl)) loc) ty pv) σ = none := by
    rw [loadM_loc_irrel loc]
    cases hmem : applyMemM (CerbMem.loadM M.tagDefs loc ty pv) σ with
    | none => rfl
    | some r =>
      obtain ⟨⟨fp, mval⟩, σ'⟩ := r
      exact absurd (Step.load_canonical hmem) (hstuck _)
  obtain ⟨r, σ', hk⟩ := applyMemM_none_killed (loadM_layer _ _ _ _ _) hnone
  apply ShippedRefusal.killed
  intro dst hemb
  obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
  simp only at hlay
  subst hlay
  have hsteps := step_ctx_load (Decomp.root Redex.load) hsz M.tagDefs
    dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
  rw [show is_unseq_with_ccall CTX = false from rfl] at hsteps
  exact ⟨_, _, hsteps, rfl, advance_action_killed (ars_load_killed hk)⟩

/-- The refusal classification at a CREATE redex: the out-of-memory
    kill (CerbMem.lean:1513, `Other (MerrOther "out of memory")`, lifted
    to `Other (DErr_memory _)`) — the arm the budget's coupling
    inequality excludes (`create_atomic`, K2.5). -/
theorem cerberusRound_refused_create {an : List _root_.annot} (M : MachineCtx)
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0}
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem)
    (hstuck : ∀ c', ¬ Step M (createRedex an loc ann align ty pref, ρ, ctl, σ) c') :
    ShippedRefusal M (createRedex an loc ann align ty pref, ρ, ctl, σ) := by
  have hsz : esize (createRedex an loc ann align ty pref) ≤ lemDefaultFuel := by
    rw [show esize (createRedex an loc ann align ty pref) = 1 from rfl]
    unfold lemDefaultFuel
    omega
  have hnone : applyMemM (CerbMem.allocateObject M.tagDefs 0 pref align ty none none) σ =
      none := by
    cases hmem : applyMemM (CerbMem.allocateObject M.tagDefs 0 pref align ty none none) σ with
    | none => rfl
    | some r =>
      obtain ⟨pv, σ'⟩ := r
      exact absurd (Step.create_canonical hmem) (hstuck _)
  obtain ⟨r, σ', hk⟩ := applyMemM_none_killed (allocateObject_layer _ _ _ _ _ _ _ _) hnone
  apply ShippedRefusal.killed
  intro dst hemb
  obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
  simp only at hlay
  subst hlay
  have hsteps := step_ctx_create (Decomp.root Redex.create) hsz M.tagDefs
    dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
  rw [show is_unseq_with_ccall CTX = false from rfl] at hsteps
  exact ⟨_, _, hsteps, rfl, advance_action_killed (ars_create_killed hk)⟩

/-- The refusal classification at a KILL redex (kill/free arc K2):
    `killM`'s kill at the request's own location — one of the three
    reasons of `killM_killed_inv` (UB179a non-matching, UB179b dead,
    the non-UB out-of-bound `Other`), lifted through `liftMem`. -/
theorem cerberusRound_refused_kill {an : List _root_.annot} (M : MachineCtx)
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
    {pv : CerbMem.PointerValue} (ρ : EnvStack) (ctl : Ctl) (σ : Mem)
    (hstuck : ∀ c', ¬ Step M (killRedex an loc ann kind pv, ρ, ctl, σ) c') :
    ShippedRefusal M (killRedex an loc ann kind pv, ρ, ctl, σ) := by
  have hsz : esize (killRedex an loc ann kind pv) ≤ lemDefaultFuel := by
    rw [show esize (killRedex an loc ann kind pv) = 1 from rfl]
    unfold lemDefaultFuel
    omega
  have hnone : applyMemM (CerbMem.killM
      (requestLoc (locUpdTh an (M.thread (killRedex an loc ann kind pv) ρ ctl)) loc) (is_dynamic kind) pv) σ =
      none := by
    rw [killM_loc_irrel loc]
    cases hmem : applyMemM (CerbMem.killM loc (is_dynamic kind) pv) σ with
    | none => rfl
    | some uσ =>
      obtain ⟨⟨⟩, σ'⟩ := uσ
      exact absurd (Step.kill_canonical hmem) (hstuck _)
  obtain ⟨r, σ', hk⟩ := applyMemM_none_killed (killM_layer _ _ _ _) hnone
  apply ShippedRefusal.killed
  intro dst hemb
  obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
  simp only at hlay
  subst hlay
  have hsteps := step_ctx_kill (Decomp.root Redex.kill) hsz M.tagDefs
    dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
  rw [show is_unseq_with_ccall CTX = false from rfl] at hsteps
  exact ⟨_, _, hsteps, rfl, advance_action_killed (ars_kill_killed hk)⟩

/-- The refusal classification at an ALLOC redex (kill/free arc K3): the
    out-of-memory kill (CerbMem.lean:1541, `Other (MerrOther "out of
    memory")`, lifted to `Other (DErr_memory _)`) — the arm the budget's
    coupling inequality excludes (`alloc_atomic`). -/
theorem cerberusRound_refused_alloc {an : List _root_.annot} (M : MachineCtx)
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {align size : CerbMem.IntegerValue} {pref : prefix0}
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem)
    (hstuck : ∀ c', ¬ Step M (allocRedex an loc ann align size pref, ρ, ctl, σ) c') :
    ShippedRefusal M (allocRedex an loc ann align size pref, ρ, ctl, σ) := by
  have hsz : esize (allocRedex an loc ann align size pref) ≤ lemDefaultFuel := by
    rw [show esize (allocRedex an loc ann align size pref) = 1 from rfl]
    unfold lemDefaultFuel
    omega
  have hnone : applyMemM (CerbMem.allocateRegion 0 pref align size) σ = none := by
    cases hmem : applyMemM (CerbMem.allocateRegion 0 pref align size) σ with
    | none => rfl
    | some r =>
      obtain ⟨pv, σ'⟩ := r
      exact absurd (Step.alloc_canonical hmem) (hstuck _)
  obtain ⟨r, σ', hk⟩ := applyMemM_none_killed (allocateRegion_layer _ _ _ _ _) hnone
  apply ShippedRefusal.killed
  intro dst hemb
  obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
  simp only at hlay
  subst hlay
  have hsteps := step_ctx_alloc (Decomp.root Redex.alloc) hsz M.tagDefs
    dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
  rw [show is_unseq_with_ccall CTX = false from rfl] at hsteps
  exact ⟨_, _, hsteps, rfl, advance_action_killed (ars_alloc_killed hk)⟩

/-- The refusal classification at a value-scrutinee CASE redex: the
    ILLTYPED no-match report (one_step0's Ecase value arm,
    Core_reduction.lean:353). -/
theorem cerberusRound_refused_case {an : List _root_.annot} (M : MachineCtx)
    {b : List _root_.annot} {cval : value} {pats : List (pattern × CoreExpr)}
    (hsz : esize (caseRedex an (Pexpr b () (PEval cval)) pats) ≤ lemDefaultFuel)
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem)
    (hstuck : ∀ c', ¬ Step M (caseRedex an (Pexpr b () (PEval cval)) pats, ρ, ctl, σ) c') :
    ShippedRefusal M (caseRedex an (Pexpr b () (PEval cval)) pats, ρ, ctl, σ) := by
  have hsel : select_case subst_sym_expr cval pats = none := by
    cases hsel : select_case subst_sym_expr cval pats with
    | none => rfl
    | some e' =>
      exact absurd (Step.case_value (valueFromPexpr_val _ _) hsel) (hstuck _)
  refine .error (String.append "Ecase, mismatched ==> "
      (CerbPP.stringFromCore_expr (caseRedex an (Pexpr b () (PEval cval)) pats))) ?_
  intro dst hemb
  obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
  simp only at hlay
  subst hlay
  exact step_ctx_case_illtyped (Decomp.root (Redex.case_ _ _)) hsz hsel M.tagDefs
    dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl

/-! ## The discharge-device readings (PROOF DEVICES — `outcomesU`)

The four completeness pairs over the hand-written discharge (`store`
and `case` in Soundness.lean, `load` and `create` here) are kept as
proof devices of this module's classification. They appear in no
export's statement. -/

/-- LOAD IS TWO-SIDED at the discharge device. -/
theorem engine_complete_loadU {an : List _root_.annot} (M : MachineCtx) (aid : Nat)
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pv : CerbMem.PointerValue} {mo : memory_order}
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    ∃ o, outcomesU M aid (loadRedex an loc ann ty pv mo) ρ ctl σ = [o] ∧
      EngineMatchU M (loadRedex an loc ann ty pv mo) ρ ctl σ o := by
  have hsz : esize (loadRedex an loc ann ty pv mo) ≤ lemDefaultFuel := by
    rw [show esize (loadRedex an loc ann ty pv mo) = 1 from rfl]
    unfold lemDefaultFuel
    omega
  cases hmem : applyMemM (CerbMem.loadM M.tagDefs loc ty pv) σ with
  | some r =>
    obtain ⟨⟨fp, mval⟩, σ'⟩ := r
    refine ⟨_, ?_, .step (Step.load_canonical hmem)⟩
    unfold outcomesU engineStepsU loadRedex
    rw [step_ctx_load (Decomp.root (Redex.load)) hsz M.tagDefs σ
      M.file M.extern M.tid M.parent (M.thread _ ρ ctl) rfl]
    simp only [List.map_cons, List.map_nil]
    rw [dischargeStep_load_active hmem]
    simp only [MachineCtx.locUpdTh_thread]
    try rfl
  | none =>
    refine ⟨dischargeStep M.tagDefs aid M.runState σ (Step_action_request2
        "LoadRequest" (requestLoc (locUpdTh an (M.thread (loadRedex an loc ann ty pv mo) ρ ctl)) loc) M.tid
        (is_unseq_with_ccall CTX)
        (stExceptUndef_return (LoadRequest2 mo ty pv (fun _ fp mval =>
          { locUpdTh an (M.thread (loadRedex an loc ann ty pv mo) ρ ctl) with
            arena := apply_ctx CTX (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval
                (valueFromMemValue mval).2)))))) })))),
      ?_, ?_⟩
    · unfold outcomesU engineStepsU loadRedex
      rw [step_ctx_load (Decomp.root (Redex.load)) hsz M.tagDefs σ
        M.file M.extern M.tid M.parent (M.thread _ ρ ctl) rfl]
      rfl
    · refine .refused (dischargeStep_load_refusal hmem) (fun out hstep => ?_) rfl
      obtain ⟨fp', mval', σ'', hmem', -⟩ := hstep.load_inv
      rw [hmem] at hmem'
      cases hmem'

/-- CREATE IS TWO-SIDED at the discharge device. -/
theorem engine_complete_createU {an : List _root_.annot} (M : MachineCtx) (aid : Nat)
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0}
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    ∃ o, outcomesU M aid (createRedex an loc ann align ty pref) ρ ctl σ = [o] ∧
      EngineMatchU M (createRedex an loc ann align ty pref) ρ ctl σ o := by
  have hsz : esize (createRedex an loc ann align ty pref) ≤ lemDefaultFuel := by
    rw [show esize (createRedex an loc ann align ty pref) = 1 from rfl]
    unfold lemDefaultFuel
    omega
  have hirr := allocateObject_arg_irrel M.tagDefs 0 0 pref align ty (get_with_address an) none none
  cases hmem : applyMemM (CerbMem.allocateObject M.tagDefs 0 pref align ty none none) σ with
  | some r =>
    obtain ⟨pv, σ'⟩ := r
    refine ⟨_, ?_, .step (Step.create_canonical hmem)⟩
    unfold outcomesU engineStepsU createRedex
    rw [step_ctx_create (Decomp.root (Redex.create)) hsz M.tagDefs σ
      M.file M.extern M.tid M.parent (M.thread _ ρ ctl) rfl]
    simp only [List.map_cons, List.map_nil]
    rw [dischargeStep_create_active (hirr ▸ hmem)]
    simp only [MachineCtx.locUpdTh_thread]
    try rfl
  | none =>
    refine ⟨dischargeStep M.tagDefs aid M.runState σ (Step_action_request2
        "CreateRequest" (requestLoc (locUpdTh an (M.thread (createRedex an loc ann align ty pref) ρ ctl)) loc) M.tid
        (is_unseq_with_ccall CTX)
        (stExceptUndef_return (CreateRequest2 pref align ty
          (get_with_address an) none (fun _ pv =>
          { locUpdTh an (M.thread (createRedex an loc ann align ty pref) ρ ctl) with
            arena := apply_ctx CTX (Expr [] (Epure (Pexpr [] ()
              (PEval (Vobject (OVpointer pv)))))) })))),
      ?_, ?_⟩
    · unfold outcomesU engineStepsU createRedex
      rw [step_ctx_create (Decomp.root (Redex.create)) hsz M.tagDefs σ
        M.file M.extern M.tid M.parent (M.thread _ ρ ctl) rfl]
      rfl
    · refine .refused (dischargeStep_create_refusal (hirr ▸ hmem)) (fun out hstep => ?_) rfl
      obtain ⟨pv', σ'', hmem', -⟩ := hstep.create_inv
      rw [hmem] at hmem'
      cases hmem'

/-- From a discharge-device completeness pair to its refusal reading. -/
theorem EngineMatchU.refusal_of_stuck {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack}
    {ctl : Ctl} {σ : Mem} {o : EngineOutcome} (hm : EngineMatchU M e ρ ctl σ o)
    (hnv : toVal e = none) (hstuck : ∀ c', ¬ Step M (e, ρ, ctl, σ) c') :
    o.isRefusal := by
  cases hm with
  | step hs => exact (hstuck _ hs).elim
  | removeAnnot he => subst he; simp [toVal, ofVal] at hnv
  | done he => subst he; simp [toVal, ofVal] at hnv
  | refused hr _ _ => exact hr

/-! ## MIRROR COMPLETENESS, PER CONSTRUCTOR (commit 2 of the slice)

For every redex root the decomposition `Frag.decomp` can deliver, a
lemma `complete_<redex>` classifies the configuration: the mirror
steps, or the shipped round is a `ShippedRefusal`, or the shape is a
registered `OpenRound` gap. Lifting a redex step to the whole
configuration is `Decomp.lift_step`; the engine facts are the
`step_ctx_*` equations (Soundness.lean, DriverCollapse.lean) and the
shape/panic variants proved here. -/

/-- A step of the redex lifts through the decomposition context (the
    converse of `Decomp.step_factor`'s first disjunct): each `Decomp`
    frame is a `Step` congruence rule, whose jump and call guards are
    discharged by the redex being neither a run nor a call redex (E1: the
    successor control is the redex step's own). -/
theorem Decomp.lift_step {M : MachineCtx} {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (hd : Decomp e ctx r)
    (hnr : ∀ (an : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)), r ≠ runRedex an ra l pes)
    (hnc : ∀ (an : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)), r ≠ callRedex an ra f pes)
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {r' : CoreExpr} {ρ' : EnvStack} {ctl' : Ctl} {σ' : Mem}
    (hs : Step M (r, ρ, ctl, σ) (r', ρ', ctl', σ')) :
    Step M (e, ρ, ctl, σ) (apply_ctx ctx r', ρ', ctl', σ') := by
  have hnj : jumpRedex? r = none := by
    cases hj : jumpRedex? r with
    | none => rfl
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      obtain ⟨an, ra, hr⟩ := hd.redex.jumpRedex?_some_inv hj
      exact absurd hr (hnr an ra l pes)
  have hncall : callRedex? r = none := (Decomp.root hd.redex).callRedex?_none hnc
  induction hd with
  | root _ => exact hs
  | sseq hd ih =>
    exact Step.sseq_ctx (hd.jumpRedex?_eq.trans hnj) (hd.callRedex?_none hnc) hd.toVal_none
      (ih hnr hnc hs hnj hncall)
  | sseq_spec hd ih =>
    exact Step.sseq_ctx (hd.jumpRedex?_eq.trans hnj) (hd.callRedex?_none hnc) hd.toVal_none
      (ih hnr hnc hs hnj hncall)
  | sseq_sym hd ih =>
    exact Step.sseq_ctx (hd.jumpRedex?_eq.trans hnj) (hd.callRedex?_none hnc) hd.toVal_none
      (ih hnr hnc hs hnj hncall)
  | annot hroot _ _ hd ih =>
    exact Step.annot_ctx (hd.jumpRedex?_eq.trans hnj) (hd.callRedex?_none hnc) hd.toVal_none
      hroot (ih hnr hnc hs hnj hncall)
  | wseq hd ih =>
    exact Step.wseq_ctx (hd.jumpRedex?_eq.trans hnj) (hd.callRedex?_none hnc) hd.toVal_none
      (ih hnr hnc hs hnj hncall)
  | bound hd ih =>
    exact Step.bound_ctx (hd.jumpRedex?_eq.trans hnj) (hd.callRedex?_none hnc) hd.toVal_none
      (ih hnr hnc hs hnj hncall)
  | sseq_tuple hd ih =>
    exact Step.sseq_ctx (hd.jumpRedex?_eq.trans hnj) (hd.callRedex?_none hnc) hd.toVal_none
      (ih hnr hnc hs hnj hncall)
  | wseq_tuple hd ih =>
    exact Step.wseq_ctx (hd.jumpRedex?_eq.trans hnj) (hd.callRedex?_none hnc) hd.toVal_none
      (ih hnr hnc hs hnj hncall)
  | wseq_sym hd ih =>
    exact Step.wseq_ctx (hd.jumpRedex?_eq.trans hnj) (hd.callRedex?_none hnc) hd.toVal_none
      (ih hnr hnc hs hnj hncall)

/-! `get_ctx`'s plain-`Eannot` arm (Core_reduction.lean:375) at a body
whose head is a sequencing frame or an action: the outer irreducibility
test and the double-annotation arm both decide by the head constructor. -/

theorem get_ctx_annot_sseq {a a' : List _root_.annot} {ds : List dyn_annotation}
    {pat : pattern} {e1 e2 : CoreExpr} (n : Nat) :
    get_ctx_lemFuel (n+1) (Expr a (Eannot ds (Expr a' (Esseq pat e1 e2)))) =
      List.map (fun q => (Cannot a ds q.1, q.2))
        (get_ctx_lemFuel n (Expr a' (Esseq pat e1 e2))) := rfl

theorem get_ctx_annot_wseq {a a' : List _root_.annot} {ds : List dyn_annotation}
    {pat : pattern} {e1 e2 : CoreExpr} (n : Nat) :
    get_ctx_lemFuel (n+1) (Expr a (Eannot ds (Expr a' (Ewseq pat e1 e2)))) =
      List.map (fun q => (Cannot a ds q.1, q.2))
        (get_ctx_lemFuel n (Expr a' (Ewseq pat e1 e2))) := rfl

theorem get_ctx_annot_action {a a' : List _root_.annot} {ds : List dyn_annotation}
    {p : generic_paction core_run_annotation Unit sym} (n : Nat) :
    get_ctx_lemFuel (n+1) (Expr a (Eannot ds (Expr a' (Eaction p)))) =
      List.map (fun q => (Cannot a ds q.1, q.2))
        (get_ctx_lemFuel n (Expr a' (Eaction p))) := rfl

theorem get_ctx_annot_bound {a a' : List _root_.annot} {ds : List dyn_annotation}
    {b : CoreExpr} (n : Nat) :
    get_ctx_lemFuel (n+1) (Expr a (Eannot ds (Expr a' (Ebound b)))) =
      List.map (fun q => (Cannot a ds q.1, q.2))
        (get_ctx_lemFuel n (Expr a' (Ebound b))) := rfl

/-- Rebuilding a decomposition's hole with an ACTION node keeps the
    frames reducible (the head of every frame is `Esseq`/`Ewseq`/an
    action; an annotation frame's body is never annotation-rooted —
    `Decomp.annot`'s `hroot`). -/
theorem Decomp.rebuild_not_irreducible {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (hd : Decomp e ctx r) (a0 : List _root_.annot)
    (p : generic_paction core_run_annotation Unit sym) :
    is_irreducible (apply_ctx ctx (Expr a0 (Eaction p))) = false := by
  induction hd with
  | root _ => rfl
  | sseq _ _ => rfl
  | sseq_spec _ _ => rfl
  | sseq_sym _ _ => rfl
  | wseq _ _ => rfl
  | bound _ _ => rfl
  | sseq_tuple _ _ => rfl
  | wseq_tuple _ _ => rfl
  | wseq_sym _ _ => rfl
  | annot hroot _ _ hd _ =>
    cases hd with
    | root _ => rfl
    | sseq _ => rfl
    | sseq_spec _ => rfl
    | sseq_sym _ => rfl
    | wseq _ => rfl
    | bound _ => rfl
    | sseq_tuple _ => rfl
    | wseq_tuple _ => rfl
    | wseq_sym _ => rfl
    | annot _ _ _ _ => simp [annotRooted, apply_ctx] at hroot

/-- Rebuilding a decomposition's hole with an ACTION node keeps the
    decomposition: the engine's `get_ctx` at the rebuilt arena is the
    singleton `[(ctx, action)]`, at the ORIGINAL arena's size bound
    (every frame draws one fuel level, the root one). The successor of a
    load/store ACTION_EVAL round is such a rebuilt arena
    (`step_ctx_load_eval_ws'`/`store_eval_ws'`). -/
theorem Decomp.get_ctx_rebuild_action {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (hd : Decomp e ctx r) (a0 : List _root_.annot)
    (p : generic_paction core_run_annotation Unit sym) :
    ∀ n : Nat, esize e ≤ n →
      get_ctx_lemFuel n (apply_ctx ctx (Expr a0 (Eaction p))) =
        [(ctx, Expr a0 (Eaction p))] := by
  induction hd with
  | @root r0 hr =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      ⟨n - 1, by have := esize_pos r0; omega⟩
    exact get_ctx_action m
  | @sseq an pa bty e1 e2 ctx' r' hd ih =>
    intro n hn
    rw [esize_sseq] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    show get_ctx_lemFuel (m+1)
      (Expr an (Esseq (Pattern pa (CaseBase (none, bty)))
        (apply_ctx ctx' (Expr a0 (Eaction p))) e2)) = _
    rw [get_ctx_sseq (hd.rebuild_not_irreducible a0 p) m, ih m (by omega)]
    rfl
  | @sseq_spec an pa pb x bty e1 e2 ctx' r' hd ih =>
    intro n hn
    rw [esize_sseq] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    show get_ctx_lemFuel (m+1)
      (Expr an (Esseq (specPat pa pb x bty) (apply_ctx ctx' (Expr a0 (Eaction p))) e2)) = _
    rw [get_ctx_sseq (hd.rebuild_not_irreducible a0 p) m, ih m (by omega)]
    rfl
  | @sseq_sym an pa x bty e1 e2 ctx' r' hd ih =>
    intro n hn
    rw [esize_sseq] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    show get_ctx_lemFuel (m+1)
      (Expr an (Esseq (symPat pa x bty) (apply_ctx ctx' (Expr a0 (Eaction p))) e2)) = _
    rw [get_ctx_sseq (hd.rebuild_not_irreducible a0 p) m, ih m (by omega)]
    rfl
  | @wseq an pa bty e1 e2 ctx' r' hd ih =>
    intro n hn
    rw [esize_wseq] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    show get_ctx_lemFuel (m+1)
      (Expr an (Ewseq (Pattern pa (CaseBase (none, bty)))
        (apply_ctx ctx' (Expr a0 (Eaction p))) e2)) = _
    rw [get_ctx_wseq (hd.rebuild_not_irreducible a0 p) m, ih m (by omega)]
    rfl
  | @sseq_tuple an pa ls e1 e2 ctx' r' hd ih =>
    intro n hn
    rw [esize_sseq] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    show get_ctx_lemFuel (m+1)
      (Expr an (Esseq (tuplePat pa ls) (apply_ctx ctx' (Expr a0 (Eaction p))) e2)) = _
    rw [get_ctx_sseq (hd.rebuild_not_irreducible a0 p) m, ih m (by omega)]
    rfl
  | @wseq_tuple an pa ls e1 e2 ctx' r' hd ih =>
    intro n hn
    rw [esize_wseq] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    show get_ctx_lemFuel (m+1)
      (Expr an (Ewseq (tuplePat pa ls) (apply_ctx ctx' (Expr a0 (Eaction p))) e2)) = _
    rw [get_ctx_wseq (hd.rebuild_not_irreducible a0 p) m, ih m (by omega)]
    rfl
  | @wseq_sym an pa x bty e1 e2 ctx' r' hd ih =>
    intro n hn
    rw [esize_wseq] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    show get_ctx_lemFuel (m+1)
      (Expr an (Ewseq (symPat pa x bty) (apply_ctx ctx' (Expr a0 (Eaction p))) e2)) = _
    rw [get_ctx_wseq (hd.rebuild_not_irreducible a0 p) m, ih m (by omega)]
    rfl
  | @bound an b ctx' r' hd ih =>
    intro n hn
    rw [esize_bound] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    show get_ctx_lemFuel (m+1)
      (Expr an (Ebound (apply_ctx ctx' (Expr a0 (Eaction p))))) = _
    rw [get_ctx_bound (hd.rebuild_not_irreducible a0 p) m, ih m (by omega)]
    rfl
  | @annot an ds b ctx' r' hroot hirr hmap hd ih =>
    intro n hn
    rw [esize_annot] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have ih' := ih m (by omega)
    show get_ctx_lemFuel (m+1)
      (Expr an (Eannot ds (apply_ctx ctx' (Expr a0 (Eaction p))))) = _
    -- the plain-`Eannot` arm of `get_ctx` (Core_reduction.lean:375): the
    -- body's head is a frame or the action, never an annotation
    cases hd with
    | root _ =>
      dsimp only [apply_ctx] at ih' ⊢
      rw [get_ctx_annot_action m, ih']; rfl
    | sseq _ =>
      dsimp only [apply_ctx] at ih' ⊢
      rw [get_ctx_annot_sseq m, ih']; rfl
    | sseq_spec _ =>
      dsimp only [apply_ctx] at ih' ⊢
      rw [get_ctx_annot_sseq m, ih']; rfl
    | sseq_sym _ =>
      dsimp only [apply_ctx] at ih' ⊢
      rw [get_ctx_annot_sseq m, ih']; rfl
    | wseq _ =>
      dsimp only [apply_ctx] at ih' ⊢
      rw [get_ctx_annot_wseq m, ih']; rfl
    | bound _ =>
      dsimp only [apply_ctx] at ih' ⊢
      rw [get_ctx_annot_bound m, ih']; rfl
    | sseq_tuple _ =>
      dsimp only [apply_ctx] at ih' ⊢
      rw [get_ctx_annot_sseq m, ih']; rfl
    | wseq_tuple _ =>
      dsimp only [apply_ctx] at ih' ⊢
      rw [get_ctx_annot_wseq m, ih']; rfl
    | wseq_sym _ =>
      dsimp only [apply_ctx] at ih' ⊢
      rw [get_ctx_annot_wseq m, ih']; rfl
    | annot _ _ _ _ => simp [annotRooted, apply_ctx] at hroot

/-- The right unit law of the engine's state-except monad. -/
theorem stExceptUndef_bind_return_right {a b c : Type}
    (m : c → exceptM (t0 a × b) core_run_cause) :
    stExceptUndef_bind m (fun z => stExceptUndef_return (b := b) z) = m := by
  funext st
  unfold stExceptUndef_bind
  cases hm : m st with
  | Result p =>
    obtain ⟨z, st'⟩ := p
    cases z <;> rfl
  | Exception err => rfl

/-! ### The binding betas at any value (the engine's LETS arms are
value-generic; the mirror's rules select the well-typed values) -/

/-- LETS-PURE at the Specified-binder pattern, ANY bound value (the
    engine binds through `update_env`, whose mismatch arm is a panic;
    `step_ctx_beta_spec_pure` is the `Vloaded (LVspecified _)`
    instance). -/
theorem step_ctx_beta_spec_pure' {an a1 b1 : List _root_.annot} {e : CoreExpr} {ctx : context}
    {pa pb : List _root_.annot} {x : sym} {bty : core_base_type}
    {v : value} {e2 : CoreExpr}
    (hd : Decomp e ctx (Expr an (Esseq (specPat pa pb x bty) (ofValA (.pure a1 b1 v)) e2)))
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
            env := update_env (specPat pa pb x bty) v (ev0 :: evs),
            arena := apply_ctx ctx e2 })] := by
  have hget : get_ctx th.arena =
      [(ctx, Expr an (Esseq (specPat pa pb x bty) (ofValA (.pure a1 b1 v)) e2))] := by
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

/-- LETS-ANNOT at the Specified-binder pattern, ANY bound value. -/
theorem step_ctx_beta_spec_annot' {an a1 a2 b1 : List _root_.annot} {e : CoreExpr} {ctx : context}
    {pa pb : List _root_.annot} {x : sym} {bty : core_base_type}
    {ds : List dyn_annotation} {v : value} {e2 : CoreExpr}
    (hd : Decomp e ctx (Expr an (Esseq (specPat pa pb x bty) (ofValA (.annot a1 a2 b1 ds v)) e2)))
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
            env := update_env (specPat pa pb x bty) v (ev0 :: evs),
            arena := apply_ctx ctx (Expr [] (Eannot ds e2)) })] := by
  have hget : get_ctx th.arena =
      [(ctx, Expr an (Esseq (specPat pa pb x bty) (ofValA (.annot a1 a2 b1 ds v)) e2))] := by
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

/-- `update_env_aux` (Core_aux.lean:861) at the Specified binder and a
    value that is NOT `Vloaded (LVspecified _)`: the pattern-mismatch
    PANIC. -/
theorem update_env_aux_spec_mismatch (pa pb : List _root_.annot) (x : sym)
    (bty : core_base_type) (v : value) (ev0 : Fmap sym value)
    (hv : ∀ ov, v ≠ Vloaded (LVspecified ov)) :
    ∃ msg, update_env_aux (specPat pa pb x bty) v ev0 = (failwithI msg : Fmap sym value) := by
  unfold update_env_aux
  rw [show lemDefaultFuel = Nat.succ 999999 from rfl]
  unfold update_env_aux_lemFuel
  unfold specPat
  cases v with
  | Vloaded lv =>
    cases lv with
    | LVspecified ov => exact absurd rfl (hv ov)
    | LVunspecified ty => exact ⟨_, rfl⟩
  | _ => exact ⟨_, rfl⟩

/-- E2: `update_env_aux` at a flat TUPLE binder and a non-tuple value —
    the mismatch PANIC (Core_aux.lean:861, the `CaseCtor ctor1 pats, _`
    arm). -/
theorem update_env_aux_tuple_mismatch (pa : List _root_.annot) (ls : List TupleLeaf)
    (v : value) (ev0 : Fmap sym value)
    (hv : ∀ vs, v ≠ Vtuple vs) :
    ∃ msg, update_env_aux (tuplePat pa ls) v ev0 = (failwithI msg : Fmap sym value) := by
  unfold update_env_aux
  rw [show lemDefaultFuel = Nat.succ 999999 from rfl]
  unfold update_env_aux_lemFuel
  unfold tuplePat
  cases v with
  | Vtuple vs => exact absurd rfl (hv vs)
  | _ => exact ⟨_, rfl⟩

/-! ### The classification, per redex root -/

/-- STORE: ILLTYPED when the value does not encode at the lvalue type;
    otherwise `storeM`'s verdict — active (the mirror step) or killed. -/
theorem complete_store {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
    {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    (hd : Decomp e ctx (storeRedex an loc ann lk ty pv cv mo))
    (hsz : esize e ≤ lemDefaultFuel) (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ρ, ctl, σ) := by
  have hnr : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      storeRedex an loc ann lk ty pv cv mo ≠ runRedex an' ra l pes := by
    intro an' ra l pes h; cases h
  have hnc : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)),
      storeRedex an loc ann lk ty pv cv mo ≠ callRedex an' ra f pes := by
    intro an' ra f pes h; cases h
  cases hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv with
  | none =>
    refine .inr (.inl (.error (String.append (CerbLocation.stringFromLocation loc)
        (String.append "the value of a store("
          (String.append (CerbPP.stringFromCore_ctype (Ctype [] (unatomic_ ty)))
            (String.append ") didn't match the lvalue type: "
              (CerbPP.stringFromCore_value cv))))) ?_))
    intro dst hemb
    obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
    simp only at hlay
    subst hlay
    exact step_ctx_store_illtyped hd hsz M.tagDefs hmv
      dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
  | some mv =>
    cases hmem : applyMemM (CerbMem.storeM M.tagDefs loc ty lk pv mv) σ with
    | some fpσ =>
      obtain ⟨fp, σ'⟩ := fpσ
      exact .inl ⟨_, hd.lift_step hnr hnc (Step.store_canonical hmv hmem)⟩
    | none =>
      have hnone : applyMemM (CerbMem.storeM M.tagDefs
          (requestLoc (locUpdTh an (M.thread e ρ ctl)) loc) ty lk pv mv) σ = none := by
        rw [storeM_loc_irrel loc]; exact hmem
      obtain ⟨r, σ', hk⟩ := applyMemM_none_killed (storeM_layer _ _ _ _ _ _ _) hnone
      refine .inr (.inl ?_)
      apply ShippedRefusal.killed
      intro dst hemb
      obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      have hsteps := step_ctx_store hd hsz M.tagDefs hmv
        dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
      rw [hd.unseq_ccall_false] at hsteps
      exact ⟨_, _, hsteps, rfl, advance_action_killed (ars_store_killed hk)⟩

/-- LOAD: `loadM`'s verdict — active (the mirror step) or killed. -/
theorem complete_load {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pv : CerbMem.PointerValue} {mo : memory_order}
    (hd : Decomp e ctx (loadRedex an loc ann ty pv mo))
    (hsz : esize e ≤ lemDefaultFuel) (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ρ, ctl, σ) := by
  have hnr : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      loadRedex an loc ann ty pv mo ≠ runRedex an' ra l pes := by
    intro an' ra l pes h; cases h
  have hnc : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)),
      loadRedex an loc ann ty pv mo ≠ callRedex an' ra f pes := by
    intro an' ra f pes h; cases h
  cases hmem : applyMemM (CerbMem.loadM M.tagDefs loc ty pv) σ with
  | some r =>
    obtain ⟨⟨fp, mval⟩, σ'⟩ := r
    exact .inl ⟨_, hd.lift_step hnr hnc (Step.load_canonical hmem)⟩
  | none =>
    have hnone : applyMemM (CerbMem.loadM M.tagDefs
        (requestLoc (locUpdTh an (M.thread e ρ ctl)) loc) ty pv) σ = none := by
      rw [loadM_loc_irrel loc]; exact hmem
    obtain ⟨r, σ', hk⟩ := applyMemM_none_killed (loadM_layer _ _ _ _ _) hnone
    refine .inr (.inl ?_)
    apply ShippedRefusal.killed
    intro dst hemb
    obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
    simp only at hlay
    subst hlay
    have hsteps := step_ctx_load hd hsz M.tagDefs
      dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
    rw [hd.unseq_ccall_false] at hsteps
    exact ⟨_, _, hsteps, rfl, advance_action_killed (ars_load_killed hk)⟩

/-- CREATE: `allocateObject`'s verdict — active (the mirror step) or
    the out-of-memory kill. -/
theorem complete_create {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0}
    (hd : Decomp e ctx (createRedex an loc ann align ty pref))
    (hsz : esize e ≤ lemDefaultFuel) (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ρ, ctl, σ) := by
  have hnr : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      createRedex an loc ann align ty pref ≠ runRedex an' ra l pes := by
    intro an' ra l pes h; cases h
  have hnc : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)),
      createRedex an loc ann align ty pref ≠ callRedex an' ra f pes := by
    intro an' ra f pes h; cases h
  cases hmem : applyMemM (CerbMem.allocateObject M.tagDefs 0 pref align ty none none) σ with
  | some r =>
    obtain ⟨pv, σ'⟩ := r
    exact .inl ⟨_, hd.lift_step hnr hnc (Step.create_canonical hmem)⟩
  | none =>
    obtain ⟨r, σ', hk⟩ := applyMemM_none_killed (allocateObject_layer _ _ _ _ _ _ _ _) hmem
    refine .inr (.inl ?_)
    apply ShippedRefusal.killed
    intro dst hemb
    obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
    simp only at hlay
    subst hlay
    have hsteps := step_ctx_create hd hsz M.tagDefs
      dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
    rw [hd.unseq_ccall_false] at hsteps
    exact ⟨_, _, hsteps, rfl, advance_action_killed (ars_create_killed hk)⟩

/-- KILL (kill/free arc K2): `killM`'s verdict at the request's own
    location — active (the mirror step) or one of the three kills of
    `killM_killed_inv` (UB179a non-matching: null on the static path,
    function pointer, no record, non-dynamic origin on the dynamic
    path, other provenance; UB179b dead; the non-UB out-of-bound
    `Other`). Stated at any `kind`: the static restriction is
    `Frag.kill`'s, not the engine's. -/
theorem complete_kill {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
    {pv : CerbMem.PointerValue}
    (hd : Decomp e ctx (killRedex an loc ann kind pv))
    (hsz : esize e ≤ lemDefaultFuel) (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ρ, ctl, σ) := by
  have hnr : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      killRedex an loc ann kind pv ≠ runRedex an' ra l pes := by
    intro an' ra l pes h; cases h
  have hnc : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)),
      killRedex an loc ann kind pv ≠ callRedex an' ra f pes := by
    intro an' ra f pes h; cases h
  cases hmem : applyMemM (CerbMem.killM loc (is_dynamic kind) pv) σ with
  | some uσ =>
    obtain ⟨⟨⟩, σ'⟩ := uσ
    exact .inl ⟨_, hd.lift_step hnr hnc (Step.kill_canonical hmem)⟩
  | none =>
    have hnone : applyMemM (CerbMem.killM
        (requestLoc (locUpdTh an (M.thread e ρ ctl)) loc) (is_dynamic kind) pv) σ = none := by
      rw [killM_loc_irrel loc]; exact hmem
    obtain ⟨r, σ', hk⟩ := applyMemM_none_killed (killM_layer _ _ _ _) hnone
    refine .inr (.inl ?_)
    apply ShippedRefusal.killed
    intro dst hemb
    obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
    simp only at hlay
    subst hlay
    have hsteps := step_ctx_kill hd hsz M.tagDefs
      dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
    rw [hd.unseq_ccall_false] at hsteps
    exact ⟨_, _, hsteps, rfl, advance_action_killed (ars_kill_killed hk)⟩

/-- ALLOC (kill/free arc K3): `allocateRegion`'s verdict — active (the
    mirror step) or the out-of-memory kill, its ONLY refusal
    (`allocateRegion_killed_inv`). -/
theorem complete_alloc {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {align size : CerbMem.IntegerValue} {pref : prefix0}
    (hd : Decomp e ctx (allocRedex an loc ann align size pref))
    (hsz : esize e ≤ lemDefaultFuel) (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ρ, ctl, σ) := by
  have hnr : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      allocRedex an loc ann align size pref ≠ runRedex an' ra l pes := by
    intro an' ra l pes h; cases h
  have hnc : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)),
      allocRedex an loc ann align size pref ≠ callRedex an' ra f pes := by
    intro an' ra f pes h; cases h
  cases hmem : applyMemM (CerbMem.allocateRegion 0 pref align size) σ with
  | some r =>
    obtain ⟨pv, σ'⟩ := r
    exact .inl ⟨_, hd.lift_step hnr hnc (Step.alloc_canonical hmem)⟩
  | none =>
    obtain ⟨r, σ', hk⟩ := applyMemM_none_killed (allocateRegion_layer _ _ _ _ _) hmem
    refine .inr (.inl ?_)
    apply ShippedRefusal.killed
    intro dst hemb
    obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
    simp only at hlay
    subst hlay
    have hsteps := step_ctx_alloc hd hsz M.tagDefs
      dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
    rw [hd.unseq_ccall_false] at hsteps
    exact ⟨_, _, hsteps, rfl, advance_action_killed (ars_alloc_killed hk)⟩

/-- LETS-PURE at the wildcard pattern: always a mirror step (cons env). -/
theorem complete_beta_pure {an a1 b1 : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {bty : core_base_type} {v : value} {e2 : CoreExpr}
    (hd : Decomp e ctx (Expr an (Esseq (Pattern pa (CaseBase (none, bty))) (ofValA (.pure a1 b1 v)) e2)))
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ev0 :: evs, ctl, σ) :=
  .inl ⟨_, hd.lift_step (fun _ _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h) Step.sseq_pure⟩

/-- LETS-ANNOT at the wildcard pattern: always a mirror step. -/
theorem complete_beta_annot {an a1 a2 b1 : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {bty : core_base_type} {ds : List dyn_annotation}
    {v : value} {e2 : CoreExpr}
    (hd : Decomp e ctx (Expr an (Esseq (Pattern pa (CaseBase (none, bty))) (ofValA (.annot a1 a2 b1 ds v)) e2)))
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ev0 :: evs, ctl, σ) :=
  .inl ⟨_, hd.lift_step (fun _ _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h) Step.sseq_annot⟩

/-- LETW-PURE at the wildcard pattern: always a mirror step. -/
theorem complete_wbeta_pure {an a1 b1 : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {bty : core_base_type} {v : value} {e2 : CoreExpr}
    (hd : Decomp e ctx (Expr an (Ewseq (Pattern pa (CaseBase (none, bty))) (ofValA (.pure a1 b1 v)) e2)))
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ev0 :: evs, ctl, σ) :=
  .inl ⟨_, hd.lift_step (fun _ _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h) Step.wseq_pure⟩

/-- LETW-ANNOT at the wildcard pattern: always a mirror step. -/
theorem complete_wbeta_annot {an a1 a2 b1 : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {bty : core_base_type} {ds : List dyn_annotation}
    {v : value} {e2 : CoreExpr}
    (hd : Decomp e ctx (Expr an (Ewseq (Pattern pa (CaseBase (none, bty))) (ofValA (.annot a1 a2 b1 ds v)) e2)))
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ev0 :: evs, ctl, σ) :=
  .inl ⟨_, hd.lift_step (fun _ _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h) Step.wseq_annot⟩

/-- ANNOTS merge: always a mirror step. -/
theorem complete_merge {an a2 : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {ds1 ds2 : List dyn_annotation} {b : CoreExpr}
    (hd : Decomp e ctx (Expr an (Eannot ds1 (Expr a2 (Eannot ds2 b)))))
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ρ, ctl, σ) :=
  .inl ⟨_, hd.lift_step (fun _ _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h) Step.annot_merge⟩

/-- CASE at a value scrutinee: the selected branch (the mirror step) or
    the ILLTYPED no-match report. -/
theorem complete_case {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {b : List _root_.annot} {cval : value} {pats : List (pattern × CoreExpr)}
    (hd : Decomp e ctx (caseRedex an (Pexpr b () (PEval cval)) pats))
    (hsz : esize e ≤ lemDefaultFuel) (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ρ, ctl, σ) := by
  cases hsel : select_case subst_sym_expr cval pats with
  | some e' =>
    exact .inl ⟨_, hd.lift_step (fun _ _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
      (Step.case_value (valueFromPexpr_val _ _) hsel)⟩
  | none =>
    refine .inr (.inl (.error (String.append "Ecase, mismatched ==> "
      (CerbPP.stringFromCore_expr (caseRedex an (Pexpr b () (PEval cval)) pats))) ?_))
    intro dst hemb
    obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
    simp only at hlay
    subst hlay
    exact step_ctx_case_illtyped hd hsz hsel M.tagDefs
      dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl

/-- LETS at the Specified binder, any bound value: a `Specified` payload
    (bare or annotated) is the mirror step; any other value is the
    binding PANIC (`update_env_aux`'s mismatch arm). -/
theorem complete_beta_spec {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {pa pb : List _root_.annot} {x : sym} {bty : core_base_type}
    {wa : SpikeValA} {e2 : CoreExpr}
    (hd : Decomp e ctx (Expr an (Esseq (specPat pa pb x bty) (ofValA wa) e2)))
    (hsz : esize e ≤ lemDefaultFuel)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ev0 :: evs, ctl, σ) := by
  have hnr : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      Expr an (Esseq (specPat pa pb x bty) (ofValA wa) e2) ≠ runRedex an' ra l pes := by
    intro an' ra l pes h; cases h
  have hnc : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)),
      Expr an (Esseq (specPat pa pb x bty) (ofValA wa) e2) ≠ callRedex an' ra f pes := by
    intro an' ra f pes h; cases h
  cases wa with
  | pure a1 b1 v =>
    by_cases hspec : ∃ ov, v = Vloaded (LVspecified ov)
    · obtain ⟨ov, rfl⟩ := hspec
      exact .inl ⟨_, hd.lift_step hnr hnc Step.sseq_spec_pure⟩
    · obtain ⟨msg, hmsg⟩ := update_env_aux_spec_mismatch pa pb x bty v ev0
        (fun ov h => hspec ⟨ov, h⟩)
      refine .inr (.inl (.panic_env msg ?_))
      intro dst hemb
      obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      refine ⟨_, _, evs, step_ctx_beta_spec_pure' hd hsz M.tagDefs dst.layout_state
        dst.core_file dst.core_extern M.tid M.parent (M.thread _ (ev0 :: evs) ctl) rfl rfl, ?_⟩
      show update_env (specPat pa pb x bty) v (ev0 :: evs) = _
      rw [update_env_cons, hmsg]
  | annot a1 a2 b1 ds v =>
    by_cases hspec : ∃ ov, v = Vloaded (LVspecified ov)
    · obtain ⟨ov, rfl⟩ := hspec
      exact .inl ⟨_, hd.lift_step hnr hnc Step.sseq_spec_annot⟩
    · obtain ⟨msg, hmsg⟩ := update_env_aux_spec_mismatch pa pb x bty v ev0
        (fun ov h => hspec ⟨ov, h⟩)
      refine .inr (.inl (.panic_env msg ?_))
      intro dst hemb
      obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      refine ⟨_, _, evs, step_ctx_beta_spec_annot' hd hsz M.tagDefs dst.layout_state
        dst.core_file dst.core_extern M.tid M.parent (M.thread _ (ev0 :: evs) ctl) rfl rfl, ?_⟩
      show update_env (specPat pa pb x bty) v (ev0 :: evs) = _
      rw [update_env_cons, hmsg]

/-- LETS at the plain-symbol binder, ANY value (E1): both betas are
    mirror steps (`Step.sseq_sym_pure`, `Step.sseq_sym_annot`) — the
    pre-E1 `BareHead` restriction and its OUT-OF-SCOPE row are retired. -/
theorem complete_beta_sym {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {x : sym} {bty : core_base_type}
    {wa : SpikeValA} {e2 : CoreExpr}
    (hd : Decomp e ctx (Expr an (Esseq (symPat pa x bty) (ofValA wa) e2)))
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ev0 :: evs, ctl, σ) := by
  have hnr : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      Expr an (Esseq (symPat pa x bty) (ofValA wa) e2) ≠ runRedex an' ra l pes := by
    intro an' ra l pes h; cases h
  have hnc : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)),
      Expr an (Esseq (symPat pa x bty) (ofValA wa) e2) ≠ callRedex an' ra f pes := by
    intro an' ra f pes h; cases h
  cases wa with
  | pure a1 b1 v => exact .inl ⟨_, hd.lift_step hnr hnc Step.sseq_sym_pure⟩
  | annot a1 a2 b1 ds v => exact .inl ⟨_, hd.lift_step hnr hnc Step.sseq_sym_annot⟩

/-- E2: LETS/LETW at a flat TUPLE binder, any bound value: a tuple
    payload (bare or annotated) is the mirror step; any other value is the
    binding PANIC (`update_env_aux`'s mismatch arm). -/
theorem complete_beta_tuple {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {ls : List TupleLeaf} {wa : SpikeValA} {e2 : CoreExpr}
    (hd : Decomp e ctx (Expr an (Esseq (tuplePat pa ls) (ofValA wa) e2)))
    (hsz : esize e ≤ lemDefaultFuel)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ev0 :: evs, ctl, σ) := by
  have hnr : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      Expr an (Esseq (tuplePat pa ls) (ofValA wa) e2) ≠ runRedex an' ra l pes := by
    intro an' ra l pes h; cases h
  have hnc : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)),
      Expr an (Esseq (tuplePat pa ls) (ofValA wa) e2) ≠ callRedex an' ra f pes := by
    intro an' ra f pes h; cases h
  cases wa with
  | pure a1 b1 v =>
    by_cases htup : ∃ vs, v = Vtuple vs
    · obtain ⟨vs, rfl⟩ := htup
      exact .inl ⟨_, hd.lift_step hnr hnc Step.sseq_tuple_pure⟩
    · obtain ⟨msg, hmsg⟩ := update_env_aux_tuple_mismatch pa ls v ev0
        (fun vs h => htup ⟨vs, h⟩)
      refine .inr (.inl (.panic_env msg ?_))
      intro dst hemb
      obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      refine ⟨_, _, evs, step_ctx_sseq_val_pure hd hsz M.tagDefs dst.layout_state
        dst.core_file dst.core_extern M.tid M.parent (M.thread _ (ev0 :: evs) ctl) rfl rfl, ?_⟩
      show update_env (tuplePat pa ls) v (ev0 :: evs) = _
      rw [update_env_cons, hmsg]
  | annot a1 a2 b1 ds v =>
    by_cases htup : ∃ vs, v = Vtuple vs
    · obtain ⟨vs, rfl⟩ := htup
      exact .inl ⟨_, hd.lift_step hnr hnc Step.sseq_tuple_annot⟩
    · obtain ⟨msg, hmsg⟩ := update_env_aux_tuple_mismatch pa ls v ev0
        (fun vs h => htup ⟨vs, h⟩)
      refine .inr (.inl (.panic_env msg ?_))
      intro dst hemb
      obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      refine ⟨_, _, evs, step_ctx_sseq_val_annot hd hsz M.tagDefs dst.layout_state
        dst.core_file dst.core_extern M.tid M.parent (M.thread _ (ev0 :: evs) ctl) rfl rfl, ?_⟩
      show update_env (tuplePat pa ls) v (ev0 :: evs) = _
      rw [update_env_cons, hmsg]

/-- E2: LETS/LETW at a flat TUPLE binder, any bound value: a tuple
    payload (bare or annotated) is the mirror step; any other value is the
    binding PANIC (`update_env_aux`'s mismatch arm). -/
theorem complete_wbeta_tuple {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {ls : List TupleLeaf} {wa : SpikeValA} {e2 : CoreExpr}
    (hd : Decomp e ctx (Expr an (Ewseq (tuplePat pa ls) (ofValA wa) e2)))
    (hsz : esize e ≤ lemDefaultFuel)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ev0 :: evs, ctl, σ) := by
  have hnr : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      Expr an (Ewseq (tuplePat pa ls) (ofValA wa) e2) ≠ runRedex an' ra l pes := by
    intro an' ra l pes h; cases h
  have hnc : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)),
      Expr an (Ewseq (tuplePat pa ls) (ofValA wa) e2) ≠ callRedex an' ra f pes := by
    intro an' ra f pes h; cases h
  cases wa with
  | pure a1 b1 v =>
    by_cases htup : ∃ vs, v = Vtuple vs
    · obtain ⟨vs, rfl⟩ := htup
      exact .inl ⟨_, hd.lift_step hnr hnc Step.wseq_tuple_pure⟩
    · obtain ⟨msg, hmsg⟩ := update_env_aux_tuple_mismatch pa ls v ev0
        (fun vs h => htup ⟨vs, h⟩)
      refine .inr (.inl (.panic_env msg ?_))
      intro dst hemb
      obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      refine ⟨_, _, evs, step_ctx_wseq_val_pure hd hsz M.tagDefs dst.layout_state
        dst.core_file dst.core_extern M.tid M.parent (M.thread _ (ev0 :: evs) ctl) rfl rfl, ?_⟩
      show update_env (tuplePat pa ls) v (ev0 :: evs) = _
      rw [update_env_cons, hmsg]
  | annot a1 a2 b1 ds v =>
    by_cases htup : ∃ vs, v = Vtuple vs
    · obtain ⟨vs, rfl⟩ := htup
      exact .inl ⟨_, hd.lift_step hnr hnc Step.wseq_tuple_annot⟩
    · obtain ⟨msg, hmsg⟩ := update_env_aux_tuple_mismatch pa ls v ev0
        (fun vs h => htup ⟨vs, h⟩)
      refine .inr (.inl (.panic_env msg ?_))
      intro dst hemb
      obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      refine ⟨_, _, evs, step_ctx_wseq_val_annot hd hsz M.tagDefs dst.layout_state
        dst.core_file dst.core_extern M.tid M.parent (M.thread _ (ev0 :: evs) ctl) rfl rfl, ?_⟩
      show update_env (tuplePat pa ls) v (ev0 :: evs) = _
      rw [update_env_cons, hmsg]

/-- E2: LETW at the plain-symbol binder, ANY value: both betas are mirror
    steps (`Step.wseq_sym_pure`, `Step.wseq_sym_annot`). -/
theorem complete_wbeta_sym {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {pa : List _root_.annot} {x : sym} {bty : core_base_type}
    {wa : SpikeValA} {e2 : CoreExpr}
    (hd : Decomp e ctx (Expr an (Ewseq (symPat pa x bty) (ofValA wa) e2)))
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ev0 :: evs, ctl, σ) := by
  have hnr : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      Expr an (Ewseq (symPat pa x bty) (ofValA wa) e2) ≠ runRedex an' ra l pes := by
    intro an' ra l pes h; cases h
  have hnc : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)),
      Expr an (Ewseq (symPat pa x bty) (ofValA wa) e2) ≠ callRedex an' ra f pes := by
    intro an' ra f pes h; cases h
  cases wa with
  | pure a1 b1 v => exact .inl ⟨_, hd.lift_step hnr hnc Step.wseq_sym_pure⟩
  | annot a1 a2 b1 ds v => exact .inl ⟨_, hd.lift_step hnr hnc Step.wseq_sym_annot⟩

/-- E1: REMOVE-BOUND at a bare value — always a mirror step. -/
theorem complete_bound_pure {an a1 b1 : List _root_.annot} {M : MachineCtx} {e : CoreExpr}
    {ctx : context} {v : value}
    (hd : Decomp e ctx (Expr an (Ebound (ofValA (.pure a1 b1 v)))))
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ρ, ctl, σ) :=
  .inl ⟨_, hd.lift_step (fun _ _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
    Step.bound_pure⟩

/-- E1: REMOVE-BOUND at an annotated value — always a mirror step. -/
theorem complete_bound_annot {an a1 a2 b1 : List _root_.annot} {M : MachineCtx} {e : CoreExpr}
    {ctx : context} {ds : List dyn_annotation} {v : value}
    (hd : Decomp e ctx (Expr an (Ebound (ofValA (.annot a1 a2 b1 ds v)))))
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ρ, ctl, σ) :=
  .inl ⟨_, hd.lift_step (fun _ _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
    Step.bound_annot⟩

/-! ### The operand-evaluation rows: shape lemmas (the engine's step is
the with-runstate evaluation step whatever the operand evaluates to)
and the panic variants -/

/-- Eif: the engine's step at any guard is ONE `RSK_tau _ TSK_Misc`
    with-runstate step (shape only). -/
theorem step_ctx_if_shape {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
    (hd : Decomp e ctx (ifRedex an g e2 e3))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_tau s TSK_Misc) m] := by
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
     exact ⟨_, _, rfl⟩)

/-- Eif at a guard that evaluates to a NON-BOOLEAN value: the redex's
    own monad is the engine's panic (one_step0's Eif arm,
    Core_reduction.lean:353: "TODO(use the core_runM) ILLTYPED, the
    first operand of an Eif didn't evaluated to a boolean"), under
    step_ctx's TAU_WITH_RUNSTATE wrapper. -/
theorem step_ctx_if_panic {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr} {v : value}
    (hd : Decomp e ctx (ifRedex an g e2 e3))
    (hsz : esize e ≤ lemDefaultFuel)
    (hdg : peDepth g ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hg : evalPexpr tds ext th.env g = some v)
    (hvt : v ≠ Vtrue) (hvf : v ≠ Vfalse) :
    ∃ (s : String) (m : core_runM thread_state)
      (inst : Inhabited (core_run_state →
        exceptM (t0 (List (Fmap sym value) × CoreExpr) × core_run_state) core_run_cause))
      (step_m : core_run_state →
        exceptM (t0 (List (Fmap sym value) × CoreExpr) × core_run_state) core_run_cause)
      (k : (List (Fmap sym value) × CoreExpr) → core_run_state →
        exceptM (t0 thread_state × core_run_state) core_run_cause)
      (msg : String),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_tau s TSK_Misc) m] ∧
      m = stExceptUndef_bind step_m k ∧
      ∀ rs, step_m rs = @failwithI _ inst msg rs := by
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
     exact ⟨_, _, _, _, _, _, rfl, rfl, fun rs => by
       rw [stExceptUndef_bind_apply, full_eval_bridge hg hdg σ file,
         stExceptUndef_return_apply]
       cases v with
       | Vtrue => exact absurd rfl hvt
       | Vfalse => exact absurd rfl hvf
       | _ => rfl⟩)

/-- Erun: the engine's step at a current procedure is ONE `RSK_eval`
    with-runstate step (shape only). -/
theorem step_ctx_run_shape {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {l : sym} {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (runRedex an ra l pes))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] := by
  have hget : get_ctx th.arena = [(ctx, runRedex an ra l pes)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold runRedex
  cases ctx <;>
    (exact ⟨_, _, rfl⟩)

/-- Erun at a label the run state's two-level `labeled` table does not
    resolve (at the extern-resolved current procedure): the step's monad
    IS the engine's panic "Erun couldn't resolve label" (step_ctx's Erun
    arm, Core_reduction.lean:484). -/
theorem step_ctx_run_unresolved {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {l : sym} {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (runRedex an ra l pes))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (p : sym) (th : thread_state)
    (harena : th.arena = e)
    (hproc : th.current_proc_opt = some p)
    (rs : core_run_state)
    (hnone : Lem_Maybe.bind0
      (fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
        (resolveExtern ext p) rs.labeled)
      (fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) l)
      = none) :
    ∃ (s : String) (m : core_runM thread_state)
      (inst : Inhabited (core_run_state →
        exceptM (t0 thread_state × core_run_state) core_run_cause)) (msg : String),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      m rs = @failwithI _ inst msg rs := by
  have hget : get_ctx th.arena = [(ctx, runRedex an ra l pes)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold runRedex
  cases ctx <;> (loc_split an) <;>
    (try dsimp only
     rw [hproc]
     exact ⟨_, _, _, _, rfl, by
       rw [stExceptUndef_bind_apply, runSE_read_apply]
       try dsimp only []
       cases hres : fmapLookupBy (fun (sym1 : sym) (sym2 : sym) =>
           Lem_Basic_classes.ordCompare sym1 sym2) p ext with
       | none =>
         rw [show resolveExtern ext p = p by
           unfold resolveExtern; rw [hres]] at hnone
         try dsimp only []
         rw [hnone]
       | some y =>
         rw [show resolveExtern ext p = y by
           unfold resolveExtern; rw [hres]] at hnone
         try dsimp only []
         rw [hnone]⟩)

/-- Erun at a thread WITHOUT a current procedure: the step's monad is
    the `labeled` read keyed by the engine's panic `failwithI
    "Core_reduction ==> Erun outside of a proc"` (step_ctx's Erun arm,
    Core_reduction.lean:484 — `current_proc := failwithI …`, then the
    extern-resolved lookup at that key), bound to the arm's
    continuation. -/
theorem step_ctx_run_noproc {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {l : sym} {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (runRedex an ra l pes))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hproc : th.current_proc_opt = none) :
    ∃ (s : String) (inst : Inhabited sym)
      (k : Option (List (sym × core_base_type) × CoreExpr) → core_run_state →
        exceptM (t0 thread_state × core_run_state) core_run_cause),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s)
          (stExceptUndef_bind
            (runSE (state_except_read (fun rs : core_run_state =>
              Lem_Maybe.bind0
                (fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
                    Lem_Basic_classes.ordCompare s1 s2)
                  (resolveExtern ext (@failwithI sym inst
                    "Core_reduction ==> Erun outside of a proc")) rs.labeled)
                (fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
                  Lem_Basic_classes.ordCompare s1 s2) l))))
            k)] := by
  have hget : get_ctx th.arena = [(ctx, runRedex an ra l pes)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold runRedex
  cases ctx <;> (loc_split an) <;>
    (try dsimp only
     rw [hproc]
     exact ⟨_, _, _, rfl⟩)

/-- Esave with non-value initializers: the engine's step is ONE
    `RSK_eval` with-runstate step (shape only). -/
theorem step_ctx_save_eval_shape {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr}
    (hd : Decomp e ctx (saveRedex an sb ps body))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs (saveParamPexprs ps) = none)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] := by
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
     exact ⟨_, _, rfl⟩)

/-- E2: PURE at any covered non-value operand: the engine's step is ONE
    `RSK_eval` with-runstate step (shape only). -/
theorem step_ctx_pure_op_shape {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {pe : generic_pexpr Unit sym}
    (hd : Decomp e ctx (pureRedex an pe))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexpr pe = none)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] := by
  obtain ⟨s, m, hsteps, -⟩ := step_ctx_pure_op_raw hd hsz hnv tds σ file ext tid parent th harena
  exact ⟨s, m, hsteps⟩

/-- The plain-symbol instance (E1's statement). -/
theorem step_ctx_pure_sym_shape {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {pb : List _root_.annot} {x : sym}
    (hd : Decomp e ctx (pureRedex an (Pexpr pb () (PEsym x))))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] :=
  step_ctx_pure_op_shape hd hsz rfl tds σ file ext tid parent th harena

/-- Load ACTION_EVAL at ANY evaluated pointer-operand value: the raw
    with-runstate singleton rebuilding the action with the value
    (`step_ctx_load_eval_ws` is the pointer instance). -/
theorem step_ctx_load_eval_ws' {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 : generic_pexpr Unit sym} {mo : memory_order} {v : value}
    (hd : Decomp e ctx (loadOpRedex an loc ann ty pe2 mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv2 : valueFromPexpr pe2 = none)
    (hp2 : PePure pe2)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv2 : evalPexpr tds ext th.env pe2 = some v) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Result (Defined { locUpdTh an th with
        arena := apply_ctx ctx (Expr an (Eaction (Paction polarity.Pos (Action loc ann
          (Load0 (Pexpr [] () (PEval (Vctype ty))) (Pexpr [] () (PEval v)) mo))))) }, rs) := by
  have hget : get_ctx th.arena = [(ctx, loadOpRedex an loc ann ty pe2 mo)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold loadOpRedex
  cases ctx <;> dsimp only [step_action]
  all_goals (
    (rw [act_valueFromPexpr_none hp2 hnv2]
     dsimp only [act_valueFromPexpr, valueFromPexpr]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge (v := Vctype ty) (evalPexpr_val _ _ _ _ _) (peDepth_val_le _ _) σ file,
     full_eval_bridge hv2 hd2 σ file]
     dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
     return1, except_return]
     rfl)
  )
/-- Load ACTION_EVAL: the engine's step is ONE `RSK_eval` with-runstate
    step whatever the operand evaluates to (shape only). -/
theorem step_ctx_load_eval_shape {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 : generic_pexpr Unit sym} {mo : memory_order}
    (hd : Decomp e ctx (loadOpRedex an loc ann ty pe2 mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv2 : valueFromPexpr pe2 = none)
    (hp2 : PePure pe2)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] := by
  have hget : get_ctx th.arena = [(ctx, loadOpRedex an loc ann ty pe2 mo)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold loadOpRedex
  cases ctx <;> dsimp only [step_action]
  all_goals (
    (rw [act_valueFromPexpr_none hp2 hnv2]
     dsimp only [act_valueFromPexpr, valueFromPexpr]
     exact ⟨_, _, rfl⟩)
  )
/-- Kill ACTION_EVAL at ANY evaluated operand value (kill/free arc K2;
    `step_ctx_kill_eval_ws`, DriverCollapse.lean, is the pointer
    instance): the engine rebuilds `Kill kind (mk_value_pe cval)` for
    any `cval` — the pointer test is the next round's. -/
theorem step_ctx_kill_eval_ws' {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
    {pe : generic_pexpr Unit sym} {v : value}
    (hd : Decomp e ctx (killOpRedex an loc ann kind pe))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexpr pe = none)
    (hp : PePure pe)
    (hdp : peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv : evalPexpr tds ext th.env pe = some v) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Result (Defined { locUpdTh an th with
        arena := apply_ctx ctx (Expr an (Eaction (Paction polarity.Pos (Action loc ann
          (Kill kind (Pexpr [] () (PEval v))))))) }, rs) := by
  have hget : get_ctx th.arena = [(ctx, killOpRedex an loc ann kind pe)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold killOpRedex
  cases ctx <;> dsimp only [step_action]
  all_goals (
    (rw [act_valueFromPexpr_none hp hnv]
     dsimp only [act_valueFromPexpr, valueFromPexpr]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge hv hdp σ file]
     dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
     return1, except_return]
     rfl)
  )
/-- Kill ACTION_EVAL: the engine's step is ONE `RSK_eval` with-runstate
    step whatever the operand evaluates to (shape only). -/
theorem step_ctx_kill_eval_shape {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
    {pe : generic_pexpr Unit sym}
    (hd : Decomp e ctx (killOpRedex an loc ann kind pe))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexpr pe = none)
    (hp : PePure pe)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] := by
  have hget : get_ctx th.arena = [(ctx, killOpRedex an loc ann kind pe)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold killOpRedex
  cases ctx <;>
    (dsimp only
     rw [step_action_kill_eval (act_valueFromPexpr_none hp hnv)]
     exact ⟨_, _, rfl⟩)

/-- Store ACTION_EVAL at ANY evaluated pointer-operand value
    (`step_ctx_store_eval_ws` is the pointer instance). -/
theorem step_ctx_store_eval_ws' {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order}
    {v : value} {cv : value}
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
    (hv2 : evalPexpr tds ext th.env pe2 = some v)
    (hv3 : evalPexpr tds ext th.env pe3 = some cv) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Result (Defined { locUpdTh an th with
        arena := apply_ctx ctx (Expr an (Eaction (Paction polarity.Pos (Action loc ann
          (Store0 false (Pexpr [] () (PEval (Vctype ty))) (Pexpr [] () (PEval v))
            (Pexpr [] () (PEval cv)) mo))))) }, rs) := by
  have hget : get_ctx th.arena = [(ctx, storeOpRedex an loc ann ty pe2 pe3 mo)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold storeOpRedex
  cases ctx <;>
    (dsimp only
     rw [step_action_store_eval (.inr (act_none_of_pair hp2 hp3 hnv)) hp3.not_constrained]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge (v := Vctype ty) (evalPexpr_val _ _ _ _ _) (peDepth_val_le _ _) σ file,
       full_eval_bridge hv2 hd2 σ file, full_eval_bridge hv3 hd3 σ file]
     dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
       return1, except_return]
     rfl)

/-- Store ACTION_EVAL: the engine's step is ONE `RSK_eval` with-runstate
    step whatever the operands evaluate to (shape only). -/
theorem step_ctx_store_eval_shape {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order}
    (hd : Decomp e ctx (storeOpRedex an loc ann ty pe2 pe3 mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe2, pe3] = none)
    (hp2 : PePure pe2) (hp3 : PePure pe3)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] := by
  have hget : get_ctx th.arena = [(ctx, storeOpRedex an loc ann ty pe2 pe3 mo)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold storeOpRedex
  cases ctx <;>
    (dsimp only
     rw [step_action_store_eval (.inr (act_none_of_pair hp2 hp3 hnv)) hp3.not_constrained]
     exact ⟨_, _, rfl⟩)

/-- Alloc ACTION_EVAL at ANY evaluated operand values (kill/free arc K3;
    `step_ctx_alloc_eval_ws`, DriverCollapse.lean, is the integer
    instance): the engine rebuilds `Alloc0 (mk_value_pe cval1)
    (mk_value_pe cval2) pref` for any pair — the integer test is the next
    round's. -/
theorem step_ctx_alloc_eval_ws' {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0} {v1 v2 : value}
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
    (hv1 : evalPexpr tds ext th.env pe1 = some v1)
    (hv2 : evalPexpr tds ext th.env pe2 = some v2) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Result (Defined { locUpdTh an th with
        arena := apply_ctx ctx (Expr an (Eaction (Paction polarity.Pos (Action loc ann
          (Alloc0 (Pexpr [] () (PEval v1)) (Pexpr [] () (PEval v2)) pref))))) }, rs) := by
  have hget : get_ctx th.arena = [(ctx, allocOpRedex an loc ann pe1 pe2 pref)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold allocOpRedex
  cases ctx <;>
    (dsimp only
     rw [step_action_alloc_eval (act_none_of_pair hp1 hp2 hnv)]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge hv1 hd1 σ file, full_eval_bridge hv2 hd2 σ file]
     dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
       return1, except_return]
     rfl)

/-- Alloc ACTION_EVAL: the engine's step is ONE `RSK_eval` with-runstate
    step whatever the operands evaluate to (shape only). -/
theorem step_ctx_alloc_eval_shape {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
    (hd : Decomp e ctx (allocOpRedex an loc ann pe1 pe2 pref))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hp1 : PePure pe1) (hp2 : PePure pe2)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] := by
  have hget : get_ctx th.arena = [(ctx, allocOpRedex an loc ann pe1 pe2 pref)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold allocOpRedex
  cases ctx <;>
    (dsimp only
     rw [step_action_alloc_eval (act_none_of_pair hp1 hp2 hnv)]
     exact ⟨_, _, rfl⟩)

/-- Memop-operand EVAL: the engine's step is ONE `RSK_eval` with-runstate
    step whatever the operands evaluate to (shape only). -/
theorem step_ctx_memop_eval_shape {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {mop : memop} {pe1 pe2 : generic_pexpr Unit sym}
    (hd : Decomp e ctx (memopRedex an mop [pe1, pe2]))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] := by
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
     exact ⟨_, _, rfl⟩)

/-! ### ILLTYPED at the rebuilt action (the second round of gap (b)) -/

/-- A positive load whose (evaluated) pointer operand is NOT a pointer
    value, at any decomposition frame: the engine's step list is the
    ILLTYPED report `[Step_error2 "Load"]` (step_action's Load0 arm,
    `some _, some _ => ACTION_ILLTYPED "Load"`, Core_reduction.lean:424;
    process_action's `ACTION_ILLTYPED str => Step_error2 str`). The
    arena is the SUCCESSOR of a load ACTION_EVAL round
    (`step_ctx_load_eval_ws'`), stated through the original
    decomposition `hd` and its size bound. -/
theorem step_ctx_load_illtyped' {an : List _root_.annot} {e : CoreExpr} {ctx : context} {r : CoreExpr}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {v : value} {mo : memory_order}
    (hd : Decomp e ctx r) (hsz : esize e ≤ lemDefaultFuel)
    (hv : ∀ pv, v ≠ Vobject (OVpointer pv))
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = apply_ctx ctx (Expr an (Eaction (Paction polarity.Pos
      (Action loc ann (Load0 (Pexpr [] () (PEval (Vctype ty)))
        (Pexpr [] () (PEval v)) mo)))))) :
    step_ctx tds σ file ext tid (parent, th) = [Step_error2 "Load"] := by
  have hget : get_ctx th.arena = [(ctx, Expr an (Eaction (Paction polarity.Pos
      (Action loc ann (Load0 (Pexpr [] () (PEval (Vctype ty)))
        (Pexpr [] () (PEval v)) mo)))))] := by
    rw [harena]; exact hd.get_ctx_rebuild_action an _ lemDefaultFuel hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  rcases v with ov | lv | _ | _ | _ | _ | ⟨_, _⟩ | _ <;> (try (cases ov)) <;>
    cases ctx <;>
      (dsimp only [step_action]
       dsimp only [act_valueFromPexpr, valueFromPexpr])
  all_goals first
    | rfl
    | exact absurd rfl (hv _)

/-- The store twin: `[Step_error2 "Store"]` (step_action's Store0 arm,
    `some _, some _, some _ => ACTION_ILLTYPED "Store"`). -/
theorem step_ctx_store_illtyped' {an : List _root_.annot} {e : CoreExpr} {ctx : context} {r : CoreExpr}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {v cv : value} {mo : memory_order}
    (hd : Decomp e ctx r) (hsz : esize e ≤ lemDefaultFuel)
    (hv : ∀ pv, v ≠ Vobject (OVpointer pv))
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = apply_ctx ctx (Expr an (Eaction (Paction polarity.Pos
      (Action loc ann (Store0 false (Pexpr [] () (PEval (Vctype ty)))
        (Pexpr [] () (PEval v)) (Pexpr [] () (PEval cv)) mo)))))) :
    step_ctx tds σ file ext tid (parent, th) = [Step_error2 "Store"] := by
  have hget : get_ctx th.arena = [(ctx, Expr an (Eaction (Paction polarity.Pos
      (Action loc ann (Store0 false (Pexpr [] () (PEval (Vctype ty)))
        (Pexpr [] () (PEval v)) (Pexpr [] () (PEval cv)) mo)))))] := by
    rw [harena]; exact hd.get_ctx_rebuild_action an _ lemDefaultFuel hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  rcases v with ov | lv | _ | _ | _ | _ | ⟨_, _⟩ | _ <;> (try (cases ov)) <;>
    cases ctx <;>
      (dsimp only [step_action]
       dsimp only [act_valueFromPexpr, valueFromPexpr])
  all_goals first
    | rfl
    | exact absurd rfl (hv _)

/-- The kill twin: `[Step_error2 "Kill"]` (step_action's Kill arm,
    `some _ => ACTION_ILLTYPED "Kill"`, at a non-pointer evaluated
    operand; kill/free arc K2). -/
theorem step_ctx_kill_illtyped' {an : List _root_.annot} {e : CoreExpr} {ctx : context} {r : CoreExpr}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
    {v : value}
    (hd : Decomp e ctx r) (hsz : esize e ≤ lemDefaultFuel)
    (hv : ∀ pv, v ≠ Vobject (OVpointer pv))
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = apply_ctx ctx (Expr an (Eaction (Paction polarity.Pos
      (Action loc ann (Kill kind (Pexpr [] () (PEval v)))))))) :
    step_ctx tds σ file ext tid (parent, th) = [Step_error2 "Kill"] := by
  have hget : get_ctx th.arena = [(ctx, Expr an (Eaction (Paction polarity.Pos
      (Action loc ann (Kill kind (Pexpr [] () (PEval v)))))))] := by
    rw [harena]; exact hd.get_ctx_rebuild_action an _ lemDefaultFuel hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  rcases v with ov | lv | _ | _ | _ | _ | ⟨_, _⟩ | _ <;> (try (cases ov)) <;>
    cases ctx <;>
      (dsimp only [step_action]
       dsimp only [act_valueFromPexpr, valueFromPexpr])
  all_goals first
    | rfl
    | exact absurd rfl (hv _)

/-- The alloc twin (kill/free arc K3): `[Step_error2 "Alloc"]` (step_action's
    Alloc0 arm, `some _, some _ => ACTION_ILLTYPED "Alloc"`) at an evaluated
    operand pair that is NOT two integers. -/
theorem step_ctx_alloc_illtyped' {an : List _root_.annot} {e : CoreExpr} {ctx : context} {r : CoreExpr}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {pref : prefix0}
    {v1 v2 : value}
    (hd : Decomp e ctx r) (hsz : esize e ≤ lemDefaultFuel)
    (hv : ∀ i1 i2, ¬ (v1 = Vobject (OVinteger i1) ∧ v2 = Vobject (OVinteger i2)))
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = apply_ctx ctx (Expr an (Eaction (Paction polarity.Pos
      (Action loc ann (Alloc0 (Pexpr [] () (PEval v1)) (Pexpr [] () (PEval v2)) pref)))))) :
    step_ctx tds σ file ext tid (parent, th) = [Step_error2 "Alloc"] := by
  have hget : get_ctx th.arena = [(ctx, Expr an (Eaction (Paction polarity.Pos
      (Action loc ann (Alloc0 (Pexpr [] () (PEval v1)) (Pexpr [] () (PEval v2)) pref)))))] := by
    rw [harena]; exact hd.get_ctx_rebuild_action an _ lemDefaultFuel hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  rcases v1 with ov1 | lv1 | _ | _ | _ | _ | ⟨_, _⟩ | _ <;> (try (cases ov1)) <;>
    cases ctx <;>
      (dsimp only [step_action]
       dsimp only [act_valueFromPexpr, valueFromPexpr])
  all_goals first
    | rfl
    | (rcases v2 with ov2 | lv2 | _ | _ | _ | _ | ⟨_, _⟩ | _ <;> (try (cases ov2)) <;>
        (try dsimp only) <;>
        first
          | rfl
          | exact absurd ⟨rfl, rfl⟩ (hv _ _))

/-! ### The operand-evaluation rows: the KILL equations (an operand the
mirror evaluator does not evaluate and the engine REJECTS — the
classifier `evalClass`/`evalClassList` answers `.kill err`, EvalClass.lean:
the step's monad raises exactly `err` at every run state) -/

/-- Eif at a guard the engine rejects. -/
theorem step_ctx_if_fail {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr} {fl : EvalFail}
    (hd : Decomp e ctx (ifRedex an g e2 e3))
    (hsz : esize e ≤ lemDefaultFuel)
    (hpg : PePure g) (hdg : peDepth g ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hf : (evalClass tds th.current_loc ext file th.env g).fail? = some fl) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_tau s TSK_Misc) m] ∧
      ∀ rs, m rs = fl.run thread_state core_run_state rs := by
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
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [stExceptUndef_bind_apply, stExceptUndef_bind_apply,
       full_eval_bridge_fail hpg hf hdg σ]
     cases fl <;> rfl)

/-- … the kill face (E1's statement). -/
theorem step_ctx_if_kill {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr} {err : core_run_cause}
    (hd : Decomp e ctx (ifRedex an g e2 e3))
    (hsz : esize e ≤ lemDefaultFuel)
    (hpg : PePure g) (hdg : peDepth g ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hk : evalClass tds th.current_loc ext file th.env g = .kill err) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_tau s TSK_Misc) m] ∧
      ∀ rs, m rs = Exception err :=
  step_ctx_if_fail hd hsz hpg hdg tds σ file ext tid parent th harena (fl := .kill err) (by rw [hk]; rfl)

/-- Erun at a registered label whose zipped arguments the engine rejects
    (the fold raises at the first rejected argument). -/
theorem step_ctx_run_fail {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {l : sym} {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (runRedex an ra l pes))
    (hsz : esize e ≤ lemDefaultFuel)
    {Q : LabelMap} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (hl : lookupLabel Q l = some (params, cont))
    (hpes : ∀ pe ∈ pes, PePure pe)
    (hdep : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (p : sym) (th : thread_state)
    (harena : th.arena = e)
    (hproc : th.current_proc_opt = some p) {fl : EvalFail}
    (hf : (evalClassFold tds th.current_loc ext file th.env (zipArgs params pes)).fail? = some fl) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, LabeledAt rs (resolveExtern ext p) Q → m rs = fl.run thread_state core_run_state rs := by
  have hget : get_ctx th.arena = [(ctx, runRedex an ra l pes)] := by
    rw [harena]; exact hd.get_ctx_default hsz
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
     refine ⟨_, _, rfl, fun rs hQ => ?_⟩
     replace hQ : (fmapLookupBy (fun (sym1 : sym) (sym2 : sym) =>
       Lem_Basic_classes.ordCompare sym1 sym2) (resolveExtern ext p)
       rs.labeled) = some Q := hQ
     rw [stExceptUndef_bind_apply, runSE_read_apply]
     try dsimp only []
     cases hres : fmapLookupBy (fun (sym1 : sym) (sym2 : sym) =>
         Lem_Basic_classes.ordCompare sym1 sym2) p ext with
     | none =>
       rw [show resolveExtern ext p = p by
         unfold resolveExtern; rw [hres]] at hQ
       try dsimp only []
       rw [hQ, bind0_some, hl']
       try dsimp only []
       rw [stExceptUndef_bind_apply,
         foldM_args_fail _ (fun _ _ _ _ _ => rfl) params pes th.env rs hpes hdep hf]
       cases fl <;> rfl
     | some y =>
       rw [show resolveExtern ext p = y by
         unfold resolveExtern; rw [hres]] at hQ
       try dsimp only []
       rw [hQ, bind0_some, hl']
       try dsimp only []
       rw [stExceptUndef_bind_apply,
         foldM_args_fail _ (fun _ _ _ _ _ => rfl) params pes th.env rs hpes hdep hf]
       cases fl <;> rfl)

/-- … the kill face (E1's statement). -/
theorem step_ctx_run_kill {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {l : sym} {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (runRedex an ra l pes))
    (hsz : esize e ≤ lemDefaultFuel)
    {Q : LabelMap} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (hl : lookupLabel Q l = some (params, cont))
    (hpes : ∀ pe ∈ pes, PePure pe)
    (hdep : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (p : sym) (th : thread_state)
    (harena : th.arena = e)
    (hproc : th.current_proc_opt = some p) {err : core_run_cause}
    (hk : evalClassFold tds th.current_loc ext file th.env (zipArgs params pes) =
      .kill err) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, LabeledAt rs (resolveExtern ext p) Q → m rs = Exception err :=
  step_ctx_run_fail hd hsz hl hpes hdep tds σ file ext tid parent p th harena hproc (fl := .kill err) (by rw [hk]; rfl)

/-- Esave whose initializers the engine rejects. -/
theorem step_ctx_save_eval_fail {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr} {fl : EvalFail}
    (hd : Decomp e ctx (saveRedex an sb ps body))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs (saveParamPexprs ps) = none)
    (hp : ∀ pe ∈ saveParamPexprs ps, PePure pe)
    (hdep : ∀ pe ∈ saveParamPexprs ps, peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hf : (evalClassList tds th.current_loc ext file th.env (saveParamPexprs ps)).fail? = some fl) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = fl.run thread_state core_run_state rs := by
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
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [stExceptUndef_bind_apply, stExceptUndef_bind_apply,
       mapM_save_fail (tds := tds) (σ := σ) (file := file)
         (fun pe => stExceptUndef_bind
           (E.eval_pexpr20 (a := core_run_state) tds th ext σ file pe)
           (fun x => match x with
             | Sum.inl pe' => stExceptUndef_return pe'
             | Sum.inr cval => stExceptUndef_return (mk_value_pe cval)))
         (fun _ _ => rfl) _ ?_ ps hp hdep hf rs] <;>
       first
         | (cases fl <;> rfl)
         | (intro p rs'
            rfl))

/-- … the kill face (E1's statement). -/
theorem step_ctx_save_eval_kill {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr} {err : core_run_cause}
    (hd : Decomp e ctx (saveRedex an sb ps body))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs (saveParamPexprs ps) = none)
    (hp : ∀ pe ∈ saveParamPexprs ps, PePure pe)
    (hdep : ∀ pe ∈ saveParamPexprs ps, peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hk : evalClassList tds th.current_loc ext file th.env (saveParamPexprs ps) =
      .kill err) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Exception err :=
  step_ctx_save_eval_fail hd hsz hnv hp hdep tds σ file ext tid parent th harena (fl := .kill err) (by rw [hk]; rfl)

/-- E2: PURE at any covered non-value operand the classifier FAILS
    (raise or undef): one `RSK_eval` step whose monad delivers the
    failure at every run state. -/
theorem step_ctx_pure_op_fail {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {pe : generic_pexpr Unit sym} {fl : EvalFail}
    (hd : Decomp e ctx (pureRedex an pe))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexpr pe = none) (hp : PePure pe) (hdp : peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hf : (evalClass tds th.current_loc ext file th.env pe).fail? = some fl) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = fl.run thread_state core_run_state rs := by
  obtain ⟨s, m, hsteps, hm⟩ := step_ctx_pure_op_raw hd hsz hnv tds σ file ext tid parent th harena
  refine ⟨s, m, hsteps, fun rs => ?_⟩
  rw [hm rs]
  exact stExceptUndef_bind_fail_apply _
    (stExceptUndef_bind_fail_apply _ (by rw [full_eval_bridge_fail hp hf hdp σ]))

/-- The plain-symbol instance. -/
theorem step_ctx_pure_sym_fail {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {pb : List _root_.annot} {x : sym} {fl : EvalFail}
    (hd : Decomp e ctx (pureRedex an (Pexpr pb () (PEsym x))))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hf : (evalClass tds th.current_loc ext file th.env (Pexpr pb () (PEsym x))).fail? = some fl) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = fl.run thread_state core_run_state rs :=
  step_ctx_pure_op_fail hd hsz rfl (.sym pb x) (peDepth_sym_le pb x) tds σ file ext tid parent th
    harena hf

/-- … the kill face (E1's statement). -/
theorem step_ctx_pure_sym_kill {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {pb : List _root_.annot} {x : sym} {err : core_run_cause}
    (hd : Decomp e ctx (pureRedex an (Pexpr pb () (PEsym x))))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hk : evalClass tds th.current_loc ext file th.env (Pexpr pb () (PEsym x)) =
      .kill err) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Exception err :=
  step_ctx_pure_sym_fail hd hsz tds σ file ext tid parent th harena (fl := .kill err) (by rw [hk]; rfl)

/-- Load ACTION_EVAL whose pointer operand the engine rejects. -/
theorem step_ctx_load_eval_fail {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 : generic_pexpr Unit sym} {mo : memory_order} {fl : EvalFail}
    (hd : Decomp e ctx (loadOpRedex an loc ann ty pe2 mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv2 : valueFromPexpr pe2 = none)
    (hp2 : PePure pe2)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hf : (evalClass tds th.current_loc ext file th.env pe2).fail? = some fl) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = fl.run thread_state core_run_state rs := by
  have hget : get_ctx th.arena = [(ctx, loadOpRedex an loc ann ty pe2 mo)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold loadOpRedex
  cases ctx <;>
    (dsimp only
     rw [step_action_load_eval (.inr (act_valueFromPexpr_none hp2 hnv2))]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge (v := Vctype ty) (evalPexpr_val _ _ _ _ _) (peDepth_val_le _ _) σ file,
       full_eval_bridge_fail hp2 hf hd2 σ]
     cases fl <;>
       (dsimp only [EvalFail.run, stExceptUndef_bind, stExceptUndef_return, stExpect_return,
          return1, except_return]
        rfl))

/-- … the kill face (E1's statement). -/
theorem step_ctx_load_eval_kill {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 : generic_pexpr Unit sym} {mo : memory_order} {err : core_run_cause}
    (hd : Decomp e ctx (loadOpRedex an loc ann ty pe2 mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv2 : valueFromPexpr pe2 = none)
    (hp2 : PePure pe2)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hk : evalClass tds th.current_loc ext file th.env pe2 = .kill err) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Exception err :=
  step_ctx_load_eval_fail hd hsz hnv2 hp2 hd2 tds σ file ext tid parent th harena (fl := .kill err) (by rw [hk]; rfl)

/-- Kill ACTION_EVAL whose operand the engine rejects (kill/free arc K2). -/
theorem step_ctx_kill_eval_fail {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
    {pe : generic_pexpr Unit sym} {fl : EvalFail}
    (hd : Decomp e ctx (killOpRedex an loc ann kind pe))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexpr pe = none)
    (hp : PePure pe)
    (hdp : peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hf : (evalClass tds th.current_loc ext file th.env pe).fail? = some fl) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = fl.run thread_state core_run_state rs := by
  have hget : get_ctx th.arena = [(ctx, killOpRedex an loc ann kind pe)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold killOpRedex
  cases ctx <;>
    (dsimp only
     rw [step_action_kill_eval (act_valueFromPexpr_none hp hnv)]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge_fail hp hf hdp σ]
     cases fl <;>
       (dsimp only [EvalFail.run, stExceptUndef_bind, stExceptUndef_return, stExpect_return,
          return1, except_return]
        rfl))

/-- … the kill face (E1's statement). -/
theorem step_ctx_kill_eval_kill {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
    {pe : generic_pexpr Unit sym} {err : core_run_cause}
    (hd : Decomp e ctx (killOpRedex an loc ann kind pe))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexpr pe = none)
    (hp : PePure pe)
    (hdp : peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hk : evalClass tds th.current_loc ext file th.env pe = .kill err) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Exception err :=
  step_ctx_kill_eval_fail hd hsz hnv hp hdp tds σ file ext tid parent th harena (fl := .kill err) (by rw [hk]; rfl)

/-- Store ACTION_EVAL whose POINTER operand the engine rejects (the
    first operand evaluated after the type). -/
theorem step_ctx_store_eval_fail2 {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order} {fl : EvalFail}
    (hd : Decomp e ctx (storeOpRedex an loc ann ty pe2 pe3 mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe2, pe3] = none)
    (hp2 : PePure pe2) (hp3 : PePure pe3)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hf : (evalClass tds th.current_loc ext file th.env pe2).fail? = some fl) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = fl.run thread_state core_run_state rs := by
  have hget : get_ctx th.arena = [(ctx, storeOpRedex an loc ann ty pe2 pe3 mo)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold storeOpRedex
  cases ctx <;>
    (dsimp only
     rw [step_action_store_eval (.inr (act_none_of_pair hp2 hp3 hnv)) hp3.not_constrained]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge (v := Vctype ty) (evalPexpr_val _ _ _ _ _) (peDepth_val_le _ _) σ file,
       full_eval_bridge_fail hp2 hf hd2 σ]
     cases fl <;>
       (dsimp only [EvalFail.run, stExceptUndef_bind, stExceptUndef_return, stExpect_return,
          return1, except_return]
        rfl))

/-- … the kill face (E1's statement). -/
theorem step_ctx_store_eval_kill2 {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order} {err : core_run_cause}
    (hd : Decomp e ctx (storeOpRedex an loc ann ty pe2 pe3 mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe2, pe3] = none)
    (hp2 : PePure pe2) (hp3 : PePure pe3)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hk : evalClass tds th.current_loc ext file th.env pe2 = .kill err) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Exception err :=
  step_ctx_store_eval_fail2 hd hsz hnv hp2 hp3 hd2 tds σ file ext tid parent th harena (fl := .kill err) (by rw [hk]; rfl)

/-- Store ACTION_EVAL whose pointer operand evaluates and whose VALUE
    operand the engine rejects. -/
theorem step_ctx_store_eval_fail3 {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order} {v : value}
    {fl : EvalFail}
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
    (hv2 : evalPexpr tds ext th.env pe2 = some v)
    (hf : (evalClass tds th.current_loc ext file th.env pe3).fail? = some fl) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = fl.run thread_state core_run_state rs := by
  have hget : get_ctx th.arena = [(ctx, storeOpRedex an loc ann ty pe2 pe3 mo)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold storeOpRedex
  cases ctx <;>
    (dsimp only
     rw [step_action_store_eval (.inr (act_none_of_pair hp2 hp3 hnv)) hp3.not_constrained]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge (v := Vctype ty) (evalPexpr_val _ _ _ _ _) (peDepth_val_le _ _) σ file,
       full_eval_bridge hv2 hd2 σ file, full_eval_bridge_fail hp3 hf hd3 σ]
     cases fl <;>
       (dsimp only [EvalFail.run, stExceptUndef_bind, stExceptUndef_return, stExpect_return,
          return1, except_return]
        rfl))

/-- … the kill face (E1's statement). -/
theorem step_ctx_store_eval_kill3 {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order} {v : value}
    {err : core_run_cause}
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
    (hv2 : evalPexpr tds ext th.env pe2 = some v)
    (hk : evalClass tds th.current_loc ext file th.env pe3 = .kill err) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Exception err :=
  step_ctx_store_eval_fail3 hd hsz hnv hp2 hp3 hd2 hd3 tds σ file ext tid parent th harena hv2 (fl := .kill err) (by rw [hk]; rfl)

/-- Alloc ACTION_EVAL whose ALIGNMENT operand (the first evaluated) the
    engine rejects (kill/free arc K3). -/
theorem step_ctx_alloc_eval_fail1 {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0} {fl : EvalFail}
    (hd : Decomp e ctx (allocOpRedex an loc ann pe1 pe2 pref))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hp1 : PePure pe1) (hp2 : PePure pe2)
    (hd1 : peDepth pe1 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hf : (evalClass tds th.current_loc ext file th.env pe1).fail? = some fl) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = fl.run thread_state core_run_state rs := by
  have hget : get_ctx th.arena = [(ctx, allocOpRedex an loc ann pe1 pe2 pref)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold allocOpRedex
  cases ctx <;>
    (dsimp only
     rw [step_action_alloc_eval (act_none_of_pair hp1 hp2 hnv)]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge_fail hp1 hf hd1 σ]
     cases fl <;>
       (dsimp only [EvalFail.run, stExceptUndef_bind, stExceptUndef_return, stExpect_return,
          return1, except_return]
        rfl))

/-- … the kill face (E1's statement). -/
theorem step_ctx_alloc_eval_kill1 {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0} {err : core_run_cause}
    (hd : Decomp e ctx (allocOpRedex an loc ann pe1 pe2 pref))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hp1 : PePure pe1) (hp2 : PePure pe2)
    (hd1 : peDepth pe1 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hk : evalClass tds th.current_loc ext file th.env pe1 = .kill err) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Exception err :=
  step_ctx_alloc_eval_fail1 hd hsz hnv hp1 hp2 hd1 tds σ file ext tid parent th harena (fl := .kill err) (by rw [hk]; rfl)

/-- Alloc ACTION_EVAL whose alignment operand evaluates and whose SIZE
    operand the engine rejects (kill/free arc K3). -/
theorem step_ctx_alloc_eval_fail2 {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0} {v1 : value}
    {fl : EvalFail}
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
    (hv1 : evalPexpr tds ext th.env pe1 = some v1)
    (hf : (evalClass tds th.current_loc ext file th.env pe2).fail? = some fl) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = fl.run thread_state core_run_state rs := by
  have hget : get_ctx th.arena = [(ctx, allocOpRedex an loc ann pe1 pe2 pref)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold allocOpRedex
  cases ctx <;>
    (dsimp only
     rw [step_action_alloc_eval (act_none_of_pair hp1 hp2 hnv)]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge hv1 hd1 σ file, full_eval_bridge_fail hp2 hf hd2 σ]
     cases fl <;>
       (dsimp only [EvalFail.run, stExceptUndef_bind, stExceptUndef_return, stExpect_return,
          return1, except_return]
        rfl))

/-- … the kill face (E1's statement). -/
theorem step_ctx_alloc_eval_kill2 {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0} {v1 : value}
    {err : core_run_cause}
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
    (hv1 : evalPexpr tds ext th.env pe1 = some v1)
    (hk : evalClass tds th.current_loc ext file th.env pe2 = .kill err) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Exception err :=
  step_ctx_alloc_eval_fail2 hd hsz hnv hp1 hp2 hd1 hd2 tds σ file ext tid parent th harena hv1 (fl := .kill err) (by rw [hk]; rfl)

/-- Memop-operand EVAL whose operand list the engine rejects (the map
    raises at the first rejected operand). -/
theorem step_ctx_memop_eval_fail {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {mop : memop} {pe1 pe2 : generic_pexpr Unit sym} {fl : EvalFail}
    (hd : Decomp e ctx (memopRedex an mop [pe1, pe2]))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hp1 : PePure pe1) (hp2 : PePure pe2)
    (hd1 : peDepth pe1 ≤ lemDefaultFuel)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hf : (evalClassList tds th.current_loc ext file th.env [pe1, pe2]).fail? = some fl) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = fl.run thread_state core_run_state rs := by
  have hget : get_ctx th.arena = [(ctx, memopRedex an mop [pe1, pe2])] := by
    rw [harena]; exact hd.get_ctx_default hsz
  have hp : ∀ pe ∈ [pe1, pe2], PePure pe := by
    intro pe hpe
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
    rcases hpe with rfl | rfl <;> assumption
  have hdp : ∀ pe ∈ [pe1, pe2], peDepth pe ≤ lemDefaultFuel := by
    intro pe hpe
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
    rcases hpe with rfl | rfl <;> assumption
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
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [stExceptUndef_bind_apply, stExceptUndef_bind_apply,
       mapM_eval1_fail (tds := tds) (σ := σ) (file := file)
         _ ?_ [pe1, pe2] hp hdp hf rs] <;>
       first
         | (intro pe rs'
            rfl)
         | (cases fl <;> (try (loc_split an)) <;> rfl))

/-- … the kill face (E1's statement). -/
theorem step_ctx_memop_eval_kill {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {mop : memop} {pe1 pe2 : generic_pexpr Unit sym} {err : core_run_cause}
    (hd : Decomp e ctx (memopRedex an mop [pe1, pe2]))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hp1 : PePure pe1) (hp2 : PePure pe2)
    (hd1 : peDepth pe1 ≤ lemDefaultFuel)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hk : evalClassList tds th.current_loc ext file th.env [pe1, pe2] = .kill err) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Exception err :=
  step_ctx_memop_eval_fail hd hsz hnv hp1 hp2 hd1 hd2 tds σ file ext tid parent th harena (fl := .kill err) (by rw [hk]; rfl)

/-- Create ACTION_EVAL (E1) at ANY evaluated operand values (kill/free arc K3;
    `step_ctx_create_eval_ws`, DriverCollapse.lean, is the integer
    instance): the engine rebuilds `Create (mk_value_pe cval1)
    (mk_value_pe cval2) pref` for any pair — the integer test is the next
    round's. -/
theorem step_ctx_create_eval_ws' {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0} {v1 v2 : value}
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
    (hv1 : evalPexpr tds ext th.env pe1 = some v1)
    (hv2 : evalPexpr tds ext th.env pe2 = some v2) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Result (Defined { locUpdTh an th with
        arena := apply_ctx ctx (Expr an (Eaction (Paction polarity.Pos (Action loc ann
          (Create (Pexpr [] () (PEval v1)) (Pexpr [] () (PEval v2)) pref))))) }, rs) := by
  have hget : get_ctx th.arena = [(ctx, createOpRedex an loc ann pe1 pe2 pref)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold createOpRedex
  cases ctx <;>
    (dsimp only
     rw [step_action_create_eval (act_none_of_pair hp1 hp2 hnv)]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge hv1 hd1 σ file, full_eval_bridge hv2 hd2 σ file]
     dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
       return1, except_return]
     rfl)

/-- Create ACTION_EVAL (E1): the engine's step is ONE `RSK_eval` with-runstate
    step whatever the operands evaluate to (shape only). -/
theorem step_ctx_create_eval_shape {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
    (hd : Decomp e ctx (createOpRedex an loc ann pe1 pe2 pref))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hp1 : PePure pe1) (hp2 : PePure pe2)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] := by
  have hget : get_ctx th.arena = [(ctx, createOpRedex an loc ann pe1 pe2 pref)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold createOpRedex
  cases ctx <;>
    (dsimp only
     rw [step_action_create_eval (act_none_of_pair hp1 hp2 hnv)]
     exact ⟨_, _, rfl⟩)

/-- The create twin (E1): `[Step_error2 "Create"]` (step_action's
    Create arm, `some _, some _ => ACTION_ILLTYPED "Create"`) at an evaluated
    operand pair that is NOT an integer and a ctype. -/
theorem step_ctx_create_illtyped' {an : List _root_.annot} {e : CoreExpr} {ctx : context} {r : CoreExpr}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {pref : prefix0}
    {v1 v2 : value}
    (hd : Decomp e ctx r) (hsz : esize e ≤ lemDefaultFuel)
    (hv : ∀ i1 ty, ¬ (v1 = Vobject (OVinteger i1) ∧ v2 = Vctype ty))
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = apply_ctx ctx (Expr an (Eaction (Paction polarity.Pos
      (Action loc ann (Create (Pexpr [] () (PEval v1)) (Pexpr [] () (PEval v2)) pref)))))) :
    step_ctx tds σ file ext tid (parent, th) = [Step_error2 "Create"] := by
  have hget : get_ctx th.arena = [(ctx, Expr an (Eaction (Paction polarity.Pos
      (Action loc ann (Create (Pexpr [] () (PEval v1)) (Pexpr [] () (PEval v2)) pref)))))] := by
    rw [harena]; exact hd.get_ctx_rebuild_action an _ lemDefaultFuel hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  rcases v1 with ov1 | lv1 | _ | _ | _ | _ | ⟨_, _⟩ | _ <;> (try (cases ov1)) <;>
    cases ctx <;>
      (dsimp only [step_action]
       dsimp only [act_valueFromPexpr, valueFromPexpr])
  all_goals first
    | rfl
    | (rcases v2 with ov2 | lv2 | _ | _ | _ | _ | ⟨_, _⟩ | _ <;> (try (cases ov2)) <;>
        (try dsimp only) <;>
        first
          | rfl
          | exact absurd ⟨rfl, rfl⟩ (hv _ _))

/-! ### The operand-evaluation rows: the KILL equations (an operand the
mirror evaluator does not evaluate and the engine REJECTS — the
classifier `evalClass`/`evalClassList` answers `.kill err`, EvalClass.lean:
the step's monad raises exactly `err` at every run state) -/

/-- Create ACTION_EVAL (E1) whose ALIGNMENT operand (the first evaluated) the
    engine rejects (kill/free arc K3). -/
theorem step_ctx_create_eval_fail1 {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0} {fl : EvalFail}
    (hd : Decomp e ctx (createOpRedex an loc ann pe1 pe2 pref))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hp1 : PePure pe1) (hp2 : PePure pe2)
    (hd1 : peDepth pe1 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hf : (evalClass tds th.current_loc ext file th.env pe1).fail? = some fl) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = fl.run thread_state core_run_state rs := by
  have hget : get_ctx th.arena = [(ctx, createOpRedex an loc ann pe1 pe2 pref)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold createOpRedex
  cases ctx <;>
    (dsimp only
     rw [step_action_create_eval (act_none_of_pair hp1 hp2 hnv)]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge_fail hp1 hf hd1 σ]
     cases fl <;>
       (dsimp only [EvalFail.run, stExceptUndef_bind, stExceptUndef_return, stExpect_return,
          return1, except_return]
        rfl))

/-- … the kill face (E1's statement). -/
theorem step_ctx_create_eval_kill1 {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0} {err : core_run_cause}
    (hd : Decomp e ctx (createOpRedex an loc ann pe1 pe2 pref))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hp1 : PePure pe1) (hp2 : PePure pe2)
    (hd1 : peDepth pe1 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hk : evalClass tds th.current_loc ext file th.env pe1 = .kill err) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Exception err :=
  step_ctx_create_eval_fail1 hd hsz hnv hp1 hp2 hd1 tds σ file ext tid parent th harena (fl := .kill err) (by rw [hk]; rfl)

/-- Create ACTION_EVAL (E1) whose alignment operand evaluates and whose SIZE
    operand the engine rejects (kill/free arc K3). -/
theorem step_ctx_create_eval_fail2 {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0} {v1 : value}
    {fl : EvalFail}
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
    (hv1 : evalPexpr tds ext th.env pe1 = some v1)
    (hf : (evalClass tds th.current_loc ext file th.env pe2).fail? = some fl) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = fl.run thread_state core_run_state rs := by
  have hget : get_ctx th.arena = [(ctx, createOpRedex an loc ann pe1 pe2 pref)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold createOpRedex
  cases ctx <;>
    (dsimp only
     rw [step_action_create_eval (act_none_of_pair hp1 hp2 hnv)]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge hv1 hd1 σ file, full_eval_bridge_fail hp2 hf hd2 σ]
     cases fl <;>
       (dsimp only [EvalFail.run, stExceptUndef_bind, stExceptUndef_return, stExpect_return,
          return1, except_return]
        rfl))

/-- … the kill face (E1's statement). -/
theorem step_ctx_create_eval_kill2 {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0} {v1 : value}
    {err : core_run_cause}
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
    (hv1 : evalPexpr tds ext th.env pe1 = some v1)
    (hk : evalClass tds th.current_loc ext file th.env pe2 = .kill err) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Exception err :=
  step_ctx_create_eval_fail2 hd hsz hnv hp1 hp2 hd1 hd2 tds σ file ext tid parent th harena hv1 (fl := .kill err) (by rw [hk]; rfl)

/-! ### The operand-evaluation rows, classified -/

/-- Eif: a boolean guard is the mirror step; a non-boolean value is the
    engine's PANIC; a guard the classifier rejects is the KILL `Other
    (DErr_core_run err)`; a guard the classifier leaves uncovered (an
    accepted-but-unmirrored leaf; the whole guard's outcome not
    characterized) is the residual `eval_uncovered`. -/
theorem complete_if {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
    (hd : Decomp e ctx (ifRedex an g e2 e3))
    (hsz : esize e ≤ lemDefaultFuel) (hpg : PePure g) (hdg : peDepth g ≤ lemDefaultFuel)
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ρ, ctl, σ) := by
  have hnr : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      ifRedex an g e2 e3 ≠ runRedex an' ra l pes := by
    intro an' ra l pes h; cases h
  have hnc : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)),
      ifRedex an g e2 e3 ≠ callRedex an' ra f pes := by
    intro an' ra f pes h; cases h
  cases hg : evalPexpr M.tagDefs M.extern ρ g with
  | none =>
    have hstuck : ∀ c'', ¬ Step M (e, ρ, ctl, σ) c'' := by
      intro c'' hs
      rcases hd.step_factor hs with ⟨r', ρr, ctlr, σr, -, -, hr, -⟩ | ⟨an', ra, l, pes, heq, -⟩ |
          ⟨_, _, _, _, _, _, _, hceq, -⟩
      · rcases hr.if_inv with ⟨hg', -⟩ | ⟨hg', -⟩ <;> (rw [hg] at hg'; cases hg')
      · exact absurd heq (hnr an' ra l pes)
      · cases hceq
    have hshape : ∀ dst, M.Embeds dst (e, ρ, ctl, σ) →
        ∃ (rsk : runstate_step_kind) (m : core_runM thread_state),
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread e ρ ctl) = [Step_with_runstate2 rsk m] := by
      intro dst hemb
      obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      obtain ⟨s, m, hsteps⟩ := step_ctx_if_shape hd hsz M.tagDefs dst.layout_state
        dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
      exact ⟨_, _, hsteps⟩
    rcases evalClass_of_none ctl.curLoc M.file hg with ⟨fl, hf⟩ | hu
    · refine .inr (.inl (.killed fl.reason ?_))
      intro dst hemb
      obtain ⟨-, hlay, hfile, hext, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_if_fail hd hsz hpg hdg M.tagDefs
        dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
        (by rw [hext, hfile]; exact hf)
      obtain ⟨dst', hadv⟩ := advance_withrs_failed_tau M.tagDefs M.tid s m
        (hm dst.core_run_state0)
      exact ⟨_, dst', hsteps, rfl, hadv⟩
    · exact .inr (.inr (.eval_uncovered g hstuck
        (by rw [hd.operandsOf_eq]; exact List.mem_singleton.mpr rfl) hpg hu hshape))
  | some v =>
    by_cases hvt : v = Vtrue
    · subst hvt
      exact .inl ⟨_, hd.lift_step hnr hnc (Step.if_true hg)⟩
    · by_cases hvf : v = Vfalse
      · subst hvf
        exact .inl ⟨_, hd.lift_step hnr hnc (Step.if_false hg)⟩
      · refine .inr (.inl (.panic ?_))
        intro dst hemb
        obtain ⟨-, hlay, -, hext, -, -, -⟩ := hemb
        simp only at hlay
        subst hlay
        obtain ⟨s, m, inst, step_m, k, msg, hsteps, hm, hpan⟩ :=
          step_ctx_if_panic hd hsz hdg M.tagDefs dst.layout_state dst.core_file
            dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
            (by rw [hext]; exact hg) hvt hvf
        exact ⟨_, _, _, inst, step_m, k, msg, hsteps, hm, hpan dst.core_run_state0⟩

/-- Erun at a context with a current procedure: a registered label with
    evaluable arguments is the mirror step (the context is discarded);
    an unregistered label is the engine's PANIC; a zipped argument the
    classifier rejects is the KILL `Other (DErr_core_run err)`; a zipped
    argument the classifier leaves uncovered (an accepted-but-unmirrored
    leaf; the whole argument's outcome not characterized) is the residual
    `eval_uncovered`; every zipped argument evaluating but a SURPLUS
    argument not is the residual `run_surplus`. -/
theorem complete_run {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {l : sym} {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (runRedex an ra l pes))
    (hsz : esize e ≤ lemDefaultFuel)
    (hpes : ∀ pe ∈ pes, PePure pe)
    (hdep : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel)
    {ctl : Ctl} {p : sym} (hproc : ctl.proc = some p)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (σ : Mem) :
    RoundComplete M (e, ev0 :: evs, ctl, σ) := by
  have hj : jumpRedex? e = some (l, pes) := hd.jumpRedex?_eq
  cases hl : lookupLabel (M.labelsAt ctl.proc) l with
  | some pc =>
    obtain ⟨params, cont⟩ := pc
    cases hvs : evalPexprs M.tagDefs M.extern (ev0 :: evs) pes with
    | some vs => exact .inl ⟨_, Step.run hj hl hvs⟩
    | none =>
      have hstuck : ∀ c'', ¬ Step M (e, ev0 :: evs, ctl, σ) c'' := by
        intro c'' hs
        obtain ⟨params', cont', vs', ev0', evs', -, -, hvs', -⟩ := hs.jump_inv hj
        rw [hvs] at hvs'
        cases hvs'
      have hshape : ∀ dst, M.Embeds dst (e, ev0 :: evs, ctl, σ) →
          ∃ (rsk : runstate_step_kind) (m : core_runM thread_state),
          step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
            (M.parent, M.thread e (ev0 :: evs) ctl) = [Step_with_runstate2 rsk m] := by
        intro dst hemb
        obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
        simp only at hlay
        subst hlay
        obtain ⟨s, m, hsteps⟩ := step_ctx_run_shape hd hsz M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent (M.thread _ _ ctl) rfl
        exact ⟨_, _, hsteps⟩
      have hfail : ∀ (fl : EvalFail),
          (evalClassFold M.tagDefs ctl.curLoc M.extern M.file (ev0 :: evs)
            (zipArgs params pes)).fail? = some fl →
          RoundComplete M (e, ev0 :: evs, ctl, σ) := by
        intro fl hf
        obtain ⟨p', hp', hQ⟩ := MachineCtx.labels_lookup_some hl
        obtain rfl : p = p' := Option.some.inj (hproc.symm.trans hp')
        refine .inr (.inl (.killed fl.reason ?_))
        intro dst hemb
        obtain ⟨-, hlay, hfile, hext, hlabd, -, -⟩ := hemb
        simp only at hlay
        subst hlay
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_run_fail hd hsz hl hpes hdep M.tagDefs
          dst.layout_state dst.core_file dst.core_extern M.tid M.parent p
          (M.thread _ _ ctl) rfl hproc (by rw [hext, hfile]; exact hf)
        obtain ⟨dst', hadv⟩ := advance_withrs_failed_eval M.tagDefs M.tid s m
          (hm dst.core_run_state0 (by unfold LabeledAt; rw [hext, hlabd]; exact hQ))
        exact ⟨_, dst', hsteps, rfl, hadv⟩
      cases hcl : evalClassFold M.tagDefs ctl.curLoc M.extern M.file (ev0 :: evs)
          (zipArgs params pes) with
      | kill err => exact hfail _ (by rw [hcl]; rfl)
      | undef l u => exact hfail _ (by rw [hcl]; rfl)
      | uncovered pe =>
        obtain ⟨hmem, hu⟩ := evalClassFold_uncovered hcl
        have hmem' : pe ∈ pes := zipArgs_sub hmem
        exact .inr (.inr (.eval_uncovered pe hstuck
          (by rw [hd.operandsOf_eq]; exact hmem') (hpes pe hmem') hu hshape))
      | vals vs' =>
        exact .inr (.inr (.run_surplus l pes p params cont hstuck hj hproc hl
          ⟨vs', (evalClassFold_vals_iff _ _ _ _ _ _ _).mp hcl⟩ hvs hshape))
  | none =>
    refine .inr (.inl (.panic ?_))
    intro dst hemb
    obtain ⟨-, hlay, -, hext, hlabd, -, -⟩ := hemb
    simp only at hlay
    subst hlay
    have hnone : Lem_Maybe.bind0
        (fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
          (resolveExtern dst.core_extern p) dst.core_run_state0.labeled)
        (fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) l)
        = none := by
      rw [hext, hlabd]
      have hlab := MachineCtx.labelsAt_eq_of_proc (M := M) hproc
      cases hQ : fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
          Lem_Basic_classes.ordCompare s1 s2) (M.resolveProc p) M.runState.labeled with
      | none =>
        rw [show resolveExtern M.extern p = M.resolveProc p from rfl, hQ]
        rfl
      | some Q =>
        rw [hQ] at hlab
        rw [show resolveExtern M.extern p = M.resolveProc p from rfl, hQ, bind0_some]
        rw [show (M.labelsAt ctl.proc) = Q from hlab] at hl
        exact hl
    obtain ⟨s, m, inst, msg, hsteps, hpan⟩ := step_ctx_run_unresolved hd hsz M.tagDefs
      dst.layout_state dst.core_file dst.core_extern M.tid M.parent p (M.thread _ _ ctl) rfl
      hproc dst.core_run_state0 hnone
    exact ⟨_, _, _, inst, m, (fun z => stExceptUndef_return z), msg, hsteps,
      (stExceptUndef_bind_return_right m).symm, hpan⟩

/-- Esave: value initializers are the entry step, evaluable initializers
    the evaluation step; an initializer the classifier rejects is the
    KILL `Other (DErr_core_run err)`; an initializer the classifier leaves
    uncovered (an accepted-but-unmirrored leaf; the whole initializer's
    outcome not characterized) is the residual `eval_uncovered`. -/
theorem complete_save {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr}
    (hd : Decomp e ctx (saveRedex an sb ps body))
    (hsz : esize e ≤ lemDefaultFuel)
    (hp : ∀ pe ∈ saveParamPexprs ps, PePure pe)
    (hdep : ∀ pe ∈ saveParamPexprs ps, peDepth pe ≤ lemDefaultFuel)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ev0 :: evs, ctl, σ) := by
  have hnr : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      saveRedex an sb ps body ≠ runRedex an' ra l pes := by
    intro an' ra l pes h; cases h
  have hnc : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)),
      saveRedex an sb ps body ≠ callRedex an' ra f pes := by
    intro an' ra f pes h; cases h
  cases hvals : valueFromPexprs (saveParamPexprs ps) with
  | some cvals => exact .inl ⟨_, hd.lift_step hnr hnc (Step.save hvals)⟩
  | none =>
    cases hev : evalPexprs M.tagDefs M.extern (ev0 :: evs) (saveParamPexprs ps) with
    | some cvals => exact .inl ⟨_, hd.lift_step hnr hnc (Step.save_eval hvals hev)⟩
    | none =>
      have hstuck : ∀ c'', ¬ Step M (e, ev0 :: evs, ctl, σ) c'' := by
        intro c'' hs
        rcases hd.step_factor hs with ⟨r', ρr, ctlr, σr, -, -, hr, -⟩ | ⟨an', ra, l, pes, heq, -⟩ |
            ⟨_, _, _, _, _, _, _, hceq, -⟩
        · rcases hr.save_inv with ⟨_, _, _, -, hvals', -⟩ | ⟨_, -, hev', -⟩
          · rw [hvals] at hvals'; cases hvals'
          · rw [hev] at hev'; cases hev'
        · exact absurd heq (hnr an' ra l pes)
        · cases hceq
      have hshape : ∀ dst, M.Embeds dst (e, ev0 :: evs, ctl, σ) →
          ∃ (rsk : runstate_step_kind) (m : core_runM thread_state),
          step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
            (M.parent, M.thread e (ev0 :: evs) ctl) = [Step_with_runstate2 rsk m] := by
        intro dst hemb
        obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
        simp only at hlay
        subst hlay
        obtain ⟨s, m, hsteps⟩ := step_ctx_save_eval_shape hd hsz hvals M.tagDefs
          dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ _ ctl) rfl
        exact ⟨_, _, hsteps⟩
      rcases evalClassList_of_none ctl.curLoc M.file hev with ⟨fl, hf⟩ | ⟨pe, hu⟩
      · refine .inr (.inl (.killed fl.reason ?_))
        intro dst hemb
        obtain ⟨-, hlay, hfile, hext, -, -, -⟩ := hemb
        simp only at hlay
        subst hlay
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_save_eval_fail hd hsz hvals hp hdep M.tagDefs
          dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ _ ctl) rfl
          (by rw [hext, hfile]; exact hf)
        obtain ⟨dst', hadv⟩ := advance_withrs_failed_eval M.tagDefs M.tid s m
          (hm dst.core_run_state0)
        exact ⟨_, dst', hsteps, rfl, hadv⟩
      · obtain ⟨hmem, hu'⟩ := evalClassList_uncovered hu
        exact .inr (.inr (.eval_uncovered pe hstuck
          (by rw [hd.operandsOf_eq]; exact hmem) (hp pe hmem) hu' hshape))

/-- E2: PURE at ANY covered non-value operand: the mirror step where the
    operand evaluates; a KILL (raise — `Other (DErr_core_run err)` — or
    undef — `Undef0 loc ubs`) where the classifier fails it; the residual
    `eval_uncovered` where the classifier leaves it uncovered. -/
theorem complete_pure_op {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {pe : generic_pexpr Unit sym}
    (hd : Decomp e ctx (pureRedex an pe))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexpr pe = none) (hp : PePure pe) (hdp : peDepth pe ≤ lemDefaultFuel)
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ρ, ctl, σ) := by
  have hnr : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      pureRedex an pe ≠ runRedex an' ra l pes := by
    intro an' ra l pes h; cases h
  have hnc : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)),
      pureRedex an pe ≠ callRedex an' ra f pes := by
    intro an' ra f pes h; cases h
  cases hv : evalPexpr M.tagDefs M.extern ρ pe with
  | some v => exact .inl ⟨_, hd.lift_step hnr hnc (Step.pure_eval hnv hv)⟩
  | none =>
    have hstuck : ∀ c'', ¬ Step M (e, ρ, ctl, σ) c'' := by
      intro c'' hs
      rcases hd.step_factor hs with ⟨r', ρr, ctlr, σr, -, -, hr, -⟩ | ⟨an', ra, l, pes, heq, -⟩ |
          ⟨_, _, _, _, _, _, _, hceq, -⟩
      · obtain ⟨v, -, hv', -⟩ := hr.pure_inv hnv
        rw [hv] at hv'; cases hv'
      · exact absurd heq (hnr an' ra l pes)
      · cases hceq
    have hshape : ∀ dst, M.Embeds dst (e, ρ, ctl, σ) →
        ∃ (rsk : runstate_step_kind) (m : core_runM thread_state),
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread e ρ ctl) = [Step_with_runstate2 rsk m] := by
      intro dst hemb
      obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      obtain ⟨s, m, hsteps⟩ := step_ctx_pure_op_shape hd hsz hnv M.tagDefs
        dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
      exact ⟨_, _, hsteps⟩
    rcases evalClass_of_none ctl.curLoc M.file hv with ⟨fl, hf⟩ | hu
    · refine .inr (.inl (.killed fl.reason ?_))
      intro dst hemb
      obtain ⟨-, hlay, hfile, hext, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_pure_op_fail hd hsz hnv hp hdp M.tagDefs
        dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
        (by rw [hext, hfile]; exact hf)
      obtain ⟨dst', hadv⟩ := advance_withrs_failed_eval M.tagDefs M.tid s m
        (hm dst.core_run_state0)
      exact ⟨_, dst', hsteps, rfl, hadv⟩
    · exact .inr (.inr (.eval_uncovered pe hstuck
        (by rw [hd.operandsOf_eq]; exact List.mem_singleton.mpr rfl) hp hu hshape))

/-- The plain-symbol instance (E1's statement). -/
theorem complete_pure_sym {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {pb : List _root_.annot} {x : sym}
    (hd : Decomp e ctx (pureRedex an (Pexpr pb () (PEsym x))))
    (hsz : esize e ≤ lemDefaultFuel) (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ρ, ctl, σ) :=
  complete_pure_op hd hsz rfl (.sym pb x) (peDepth_sym_le pb x) ρ ctl σ

/-- Load ACTION_EVAL: a pointer-valued operand is the mirror step; a
    non-pointer value is ILLTYPED AT DISTANCE ONE (the engine's
    evaluation round succeeds into the ill-typed load, whose next step
    list is `[Step_error2 "Load"]` — `ShippedRefusal.error_next`); an
    operand the classifier rejects is the KILL `Other (DErr_core_run err)`;
    an operand the classifier leaves uncovered (an accepted-but-unmirrored
    leaf; the whole operand's outcome not characterized) is the residual
    `eval_uncovered`. -/
theorem complete_load_op {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 : generic_pexpr Unit sym} {mo : memory_order}
    (hd : Decomp e ctx (loadOpRedex an loc ann ty pe2 mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv2 : valueFromPexpr pe2 = none) (hp2 : PePure pe2)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ρ, ctl, σ) := by
  have hnr : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      loadOpRedex an loc ann ty pe2 mo ≠ runRedex an' ra l pes := by
    intro an' ra l pes h; cases h
  have hnc : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)),
      loadOpRedex an loc ann ty pe2 mo ≠ callRedex an' ra f pes := by
    intro an' ra f pes h; cases h
  cases hv2 : evalPexpr M.tagDefs M.extern ρ pe2 with
  | none =>
    have hstuck : ∀ c'', ¬ Step M (e, ρ, ctl, σ) c'' := by
      intro c'' hs
      rcases hd.step_factor hs with ⟨r', ρr, ctlr, σr, -, -, hr, -⟩ | ⟨an', ra, l, pes, heq, -⟩ |
          ⟨_, _, _, _, _, _, _, hceq, -⟩
      · obtain ⟨pv, hv2', -⟩ := hr.load_op_inv hnv2
        rw [hv2] at hv2'; cases hv2'
      · exact absurd heq (hnr an' ra l pes)
      · cases hceq
    have hshape : ∀ dst, M.Embeds dst (e, ρ, ctl, σ) →
        ∃ (rsk : runstate_step_kind) (m : core_runM thread_state),
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread e ρ ctl) = [Step_with_runstate2 rsk m] := by
      intro dst hemb
      obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      obtain ⟨s, m, hsteps⟩ := step_ctx_load_eval_shape hd hsz hnv2 hp2 M.tagDefs
        dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
      exact ⟨_, _, hsteps⟩
    rcases evalClass_of_none ctl.curLoc M.file hv2 with ⟨fl, hf⟩ | hu
    · refine .inr (.inl (.killed fl.reason ?_))
      intro dst hemb
      obtain ⟨-, hlay, hfile, hext, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_load_eval_fail hd hsz hnv2 hp2 hd2 M.tagDefs
        dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
        (by rw [hext, hfile]; exact hf)
      obtain ⟨dst', hadv⟩ := advance_withrs_failed_eval M.tagDefs M.tid s m
        (hm dst.core_run_state0)
      exact ⟨_, dst', hsteps, rfl, hadv⟩
    · exact .inr (.inr (.eval_uncovered pe2 hstuck
        (by rw [hd.operandsOf_eq]; exact List.mem_singleton.mpr rfl) hp2 hu hshape))
  | some v =>
    by_cases hptr : ∃ pv, v = Vobject (OVpointer pv)
    · obtain ⟨pv, rfl⟩ := hptr
      exact .inl ⟨_, hd.lift_step hnr hnc (Step.load_eval hnv2 hv2)⟩
    · -- ILLTYPED AT DISTANCE ONE: the evaluation round succeeds into the
      -- ill-typed load, whose next step list is `[Step_error2 "Load"]`
      have hv' : ∀ pv, v ≠ Vobject (OVpointer pv) := fun pv h => hptr ⟨pv, h⟩
      refine .inr (.inl (.error_next
        (apply_ctx ctx (Expr an (Eaction (Paction polarity.Pos (Action loc ann
          (Load0 (Pexpr [] () (PEval (Vctype ty))) (Pexpr [] () (PEval v)) mo))))), ρ, ctl.upd an, σ)
        "Load" ?_ ?_))
      · intro dst hemb
        obtain ⟨-, hlay, -, hext, -, hsym, hexc⟩ := hemb
        simp only at hlay hsym hexc
        subst hlay
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_load_eval_ws' hd hsz hnv2 hp2 hd2
          M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
          (M.thread _ ρ ctl) rfl (by rw [hext]; exact hv2)
        rw [MachineCtx.locUpdTh_thread] at hm
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace,
          dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_withrs_eval M.tagDefs M.tid s m (hm dst.core_run_state0)
      · intro dst hemb
        obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
        simp only at hlay
        subst hlay
        exact step_ctx_load_illtyped' hd hsz hv' M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ (ctl.upd an)) rfl

/-- Kill-operand EVAL (kill/free arc K2): a pointer-evaluating operand
    is the mirror step; a non-pointer value is ILLTYPED AT DISTANCE ONE
    (the rebuilt action's `some _ => ACTION_ILLTYPED "Kill"`); an operand
    the classifier rejects is the KILL `Other (DErr_core_run err)`; an
    operand the classifier leaves uncovered is the residual
    `eval_uncovered`. Stated at any `kind`. -/
theorem complete_kill_op {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
    {pe : generic_pexpr Unit sym}
    (hd : Decomp e ctx (killOpRedex an loc ann kind pe))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexpr pe = none) (hp : PePure pe)
    (hdp : peDepth pe ≤ lemDefaultFuel)
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ρ, ctl, σ) := by
  have hnr : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      killOpRedex an loc ann kind pe ≠ runRedex an' ra l pes := by
    intro an' ra l pes h; cases h
  have hnc : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)),
      killOpRedex an loc ann kind pe ≠ callRedex an' ra f pes := by
    intro an' ra f pes h; cases h
  cases hv : evalPexpr M.tagDefs M.extern ρ pe with
  | none =>
    have hstuck : ∀ c'', ¬ Step M (e, ρ, ctl, σ) c'' := by
      intro c'' hs
      rcases hd.step_factor hs with ⟨r', ρr, ctlr, σr, -, -, hr, -⟩ | ⟨an', ra, l, pes, heq, -⟩ |
          ⟨_, _, _, _, _, _, _, hceq, -⟩
      · obtain ⟨pv, hv', -⟩ := hr.kill_op_inv hnv
        rw [hv] at hv'; cases hv'
      · exact absurd heq (hnr an' ra l pes)
      · cases hceq
    have hshape : ∀ dst, M.Embeds dst (e, ρ, ctl, σ) →
        ∃ (rsk : runstate_step_kind) (m : core_runM thread_state),
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread e ρ ctl) = [Step_with_runstate2 rsk m] := by
      intro dst hemb
      obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      obtain ⟨s, m, hsteps⟩ := step_ctx_kill_eval_shape hd hsz hnv hp M.tagDefs
        dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
      exact ⟨_, _, hsteps⟩
    rcases evalClass_of_none ctl.curLoc M.file hv with ⟨fl, hf⟩ | hu
    · refine .inr (.inl (.killed fl.reason ?_))
      intro dst hemb
      obtain ⟨-, hlay, hfile, hext, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_kill_eval_fail hd hsz hnv hp hdp M.tagDefs
        dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
        (by rw [hext, hfile]; exact hf)
      obtain ⟨dst', hadv⟩ := advance_withrs_failed_eval M.tagDefs M.tid s m
        (hm dst.core_run_state0)
      exact ⟨_, dst', hsteps, rfl, hadv⟩
    · exact .inr (.inr (.eval_uncovered pe hstuck
        (by rw [hd.operandsOf_eq]; exact List.mem_singleton.mpr rfl) hp hu hshape))
  | some v =>
    by_cases hptr : ∃ pv, v = Vobject (OVpointer pv)
    · obtain ⟨pv, rfl⟩ := hptr
      exact .inl ⟨_, hd.lift_step hnr hnc (Step.kill_eval hnv hv)⟩
    · -- ILLTYPED AT DISTANCE ONE: the evaluation round succeeds into the
      -- ill-typed kill, whose next step list is `[Step_error2 "Kill"]`
      have hv' : ∀ pv, v ≠ Vobject (OVpointer pv) := fun pv h => hptr ⟨pv, h⟩
      refine .inr (.inl (.error_next
        (apply_ctx ctx (Expr an (Eaction (Paction polarity.Pos (Action loc ann
          (Kill kind (Pexpr [] () (PEval v))))))), ρ, ctl.upd an, σ)
        "Kill" ?_ ?_))
      · intro dst hemb
        obtain ⟨-, hlay, -, hext, -, hsym, hexc⟩ := hemb
        simp only at hlay hsym hexc
        subst hlay
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_kill_eval_ws' hd hsz hnv hp hdp
          M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
          (M.thread _ ρ ctl) rfl (by rw [hext]; exact hv)
        rw [MachineCtx.locUpdTh_thread] at hm
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace,
          dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
        exact advance_withrs_eval M.tagDefs M.tid s m (hm dst.core_run_state0)
      · intro dst hemb
        obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
        simp only at hlay
        subst hlay
        exact step_ctx_kill_illtyped' hd hsz hv' M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ (ctl.upd an)) rfl

/-- Alloc-operand EVAL (kill/free arc K3): two integer-evaluating
    operands are the mirror step; an evaluable pair that is NOT two
    integers is ILLTYPED AT DISTANCE ONE (the rebuilt action's `some _,
    some _ => ACTION_ILLTYPED "Alloc"`); the first operand (alignment
    before size, the engine's order) the classifier rejects is the KILL
    `Other (DErr_core_run err)`; the first operand the classifier leaves
    uncovered is the residual `eval_uncovered`. -/
theorem complete_alloc_op {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
    (hd : Decomp e ctx (allocOpRedex an loc ann pe1 pe2 pref))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hp1 : PePure pe1) (hp2 : PePure pe2)
    (hd1 : peDepth pe1 ≤ lemDefaultFuel) (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ρ, ctl, σ) := by
  have hnr : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      allocOpRedex an loc ann pe1 pe2 pref ≠ runRedex an' ra l pes := by
    intro an' ra l pes h; cases h
  have hnc : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)),
      allocOpRedex an loc ann pe1 pe2 pref ≠ callRedex an' ra f pes := by
    intro an' ra f pes h; cases h
  have hshape : ∀ dst, M.Embeds dst (e, ρ, ctl, σ) →
      ∃ (rsk : runstate_step_kind) (m : core_runM thread_state),
      step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
        (M.parent, M.thread e ρ ctl) = [Step_with_runstate2 rsk m] := by
    intro dst hemb
    obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
    simp only at hlay
    subst hlay
    obtain ⟨s, m, hsteps⟩ := step_ctx_alloc_eval_shape hd hsz hnv hp1 hp2 M.tagDefs
      dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
    exact ⟨_, _, hsteps⟩
  cases hv1 : evalPexpr M.tagDefs M.extern ρ pe1 with
  | none =>
    have hstuck : ∀ c'', ¬ Step M (e, ρ, ctl, σ) c'' := by
      intro c'' hs
      rcases hd.step_factor hs with ⟨r', ρr, ctlr, σr, -, -, hr, -⟩ | ⟨an', ra, l, pes, heq, -⟩ |
          ⟨_, _, _, _, _, _, _, hceq, -⟩
      · obtain ⟨al, sz, hv1', -, -⟩ := hr.alloc_op_inv hnv
        rw [hv1] at hv1'; cases hv1'
      · exact absurd heq (hnr an' ra l pes)
      · cases hceq
    rcases evalClass_of_none ctl.curLoc M.file hv1 with ⟨fl, hf⟩ | hu
    · refine .inr (.inl (.killed fl.reason ?_))
      intro dst hemb
      obtain ⟨-, hlay, hfile, hext, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_alloc_eval_fail1 hd hsz hnv hp1 hp2 hd1
        M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
        (M.thread _ ρ ctl) rfl (by rw [hext, hfile]; exact hf)
      obtain ⟨dst', hadv⟩ := advance_withrs_failed_eval M.tagDefs M.tid s m
        (hm dst.core_run_state0)
      exact ⟨_, dst', hsteps, rfl, hadv⟩
    · exact .inr (.inr (.eval_uncovered pe1 hstuck
        (by rw [hd.operandsOf_eq]; exact List.mem_cons_self ..) hp1 hu hshape))
  | some v1 =>
    cases hv2 : evalPexpr M.tagDefs M.extern ρ pe2 with
    | none =>
      have hstuck : ∀ c'', ¬ Step M (e, ρ, ctl, σ) c'' := by
        intro c'' hs
        rcases hd.step_factor hs with ⟨r', ρr, ctlr, σr, -, -, hr, -⟩ | ⟨an', ra, l, pes, heq, -⟩ |
            ⟨_, _, _, _, _, _, _, hceq, -⟩
        · obtain ⟨al, sz, -, hv2', -⟩ := hr.alloc_op_inv hnv
          rw [hv2] at hv2'; cases hv2'
        · exact absurd heq (hnr an' ra l pes)
        · cases hceq
      rcases evalClass_of_none ctl.curLoc M.file hv2 with ⟨fl, hf⟩ | hu
      · refine .inr (.inl (.killed fl.reason ?_))
        intro dst hemb
        obtain ⟨-, hlay, hfile, hext, -, -, -⟩ := hemb
        simp only at hlay
        subst hlay
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_alloc_eval_fail2 hd hsz hnv hp1 hp2 hd1 hd2
          M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
          (M.thread _ ρ ctl) rfl (by rw [hext]; exact hv1) (by rw [hext, hfile]; exact hf)
        obtain ⟨dst', hadv⟩ := advance_withrs_failed_eval M.tagDefs M.tid s m
          (hm dst.core_run_state0)
        exact ⟨_, dst', hsteps, rfl, hadv⟩
      · exact .inr (.inr (.eval_uncovered pe2 hstuck
          (by rw [hd.operandsOf_eq]; exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
          hp2 hu hshape))
    | some v2 =>
      by_cases hint : ∃ i1 i2, v1 = Vobject (OVinteger i1) ∧ v2 = Vobject (OVinteger i2)
      · obtain ⟨i1, i2, rfl, rfl⟩ := hint
        exact .inl ⟨_, hd.lift_step hnr hnc (Step.alloc_eval hnv hv1 hv2)⟩
      · -- ILLTYPED AT DISTANCE ONE (the alloc twin)
        have hv' : ∀ i1 i2, ¬ (v1 = Vobject (OVinteger i1) ∧ v2 = Vobject (OVinteger i2)) :=
          fun i1 i2 h => hint ⟨i1, i2, h⟩
        refine .inr (.inl (.error_next
          (apply_ctx ctx (Expr an (Eaction (Paction polarity.Pos (Action loc ann
            (Alloc0 (Pexpr [] () (PEval v1)) (Pexpr [] () (PEval v2)) pref))))), ρ, ctl.upd an, σ)
          "Alloc" ?_ ?_))
        · intro dst hemb
          obtain ⟨-, hlay, -, hext, -, hsym, hexc⟩ := hemb
          simp only at hlay hsym hexc
          subst hlay
          obtain ⟨s, m, hsteps, hm⟩ := step_ctx_alloc_eval_ws' hd hsz hnv hp1 hp2 hd1 hd2
            M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
            (M.thread _ ρ ctl) rfl (by rw [hext]; exact hv1) (by rw [hext]; exact hv2)
          rw [MachineCtx.locUpdTh_thread] at hm
          refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace,
            dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
          exact advance_withrs_eval M.tagDefs M.tid s m (hm dst.core_run_state0)
        · intro dst hemb
          obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
          simp only at hlay
          subst hlay
          exact step_ctx_alloc_illtyped' hd hsz hv' M.tagDefs dst.layout_state
            dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ (ctl.upd an)) rfl

/-- Alloc-operand EVAL (kill/free arc K3): two integer-evaluating
    operands are the mirror step; an evaluable pair that is NOT two
    integers is ILLTYPED AT DISTANCE ONE (the rebuilt action's `some _,
    some _ => ACTION_ILLTYPED "Create"`); the first operand (alignment
    before size, the engine's order) the classifier rejects is the KILL
    `Other (DErr_core_run err)`; the first operand the classifier leaves
    uncovered is the residual `eval_uncovered`. -/
theorem complete_create_op {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
    (hd : Decomp e ctx (createOpRedex an loc ann pe1 pe2 pref))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hp1 : PePure pe1) (hp2 : PePure pe2)
    (hd1 : peDepth pe1 ≤ lemDefaultFuel) (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ρ, ctl, σ) := by
  have hnr : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      createOpRedex an loc ann pe1 pe2 pref ≠ runRedex an' ra l pes := by
    intro an' ra l pes h; cases h
  have hnc : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)),
      createOpRedex an loc ann pe1 pe2 pref ≠ callRedex an' ra f pes := by
    intro an' ra f pes h; cases h
  have hshape : ∀ dst, M.Embeds dst (e, ρ, ctl, σ) →
      ∃ (rsk : runstate_step_kind) (m : core_runM thread_state),
      step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
        (M.parent, M.thread e ρ ctl) = [Step_with_runstate2 rsk m] := by
    intro dst hemb
    obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
    simp only at hlay
    subst hlay
    obtain ⟨s, m, hsteps⟩ := step_ctx_create_eval_shape hd hsz hnv hp1 hp2 M.tagDefs
      dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
    exact ⟨_, _, hsteps⟩
  cases hv1 : evalPexpr M.tagDefs M.extern ρ pe1 with
  | none =>
    have hstuck : ∀ c'', ¬ Step M (e, ρ, ctl, σ) c'' := by
      intro c'' hs
      rcases hd.step_factor hs with ⟨r', ρr, ctlr, σr, -, -, hr, -⟩ | ⟨an', ra, l, pes, heq, -⟩ |
          ⟨_, _, _, _, _, _, _, hceq, -⟩
      · obtain ⟨al, sz, hv1', -, -⟩ := hr.create_op_inv hnv
        rw [hv1] at hv1'; cases hv1'
      · exact absurd heq (hnr an' ra l pes)
      · cases hceq
    rcases evalClass_of_none ctl.curLoc M.file hv1 with ⟨fl, hf⟩ | hu
    · refine .inr (.inl (.killed fl.reason ?_))
      intro dst hemb
      obtain ⟨-, hlay, hfile, hext, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_create_eval_fail1 hd hsz hnv hp1 hp2 hd1
        M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
        (M.thread _ ρ ctl) rfl (by rw [hext, hfile]; exact hf)
      obtain ⟨dst', hadv⟩ := advance_withrs_failed_eval M.tagDefs M.tid s m
        (hm dst.core_run_state0)
      exact ⟨_, dst', hsteps, rfl, hadv⟩
    · exact .inr (.inr (.eval_uncovered pe1 hstuck
        (by rw [hd.operandsOf_eq]; exact List.mem_cons_self ..) hp1 hu hshape))
  | some v1 =>
    cases hv2 : evalPexpr M.tagDefs M.extern ρ pe2 with
    | none =>
      have hstuck : ∀ c'', ¬ Step M (e, ρ, ctl, σ) c'' := by
        intro c'' hs
        rcases hd.step_factor hs with ⟨r', ρr, ctlr, σr, -, -, hr, -⟩ | ⟨an', ra, l, pes, heq, -⟩ |
            ⟨_, _, _, _, _, _, _, hceq, -⟩
        · obtain ⟨al, sz, -, hv2', -⟩ := hr.create_op_inv hnv
          rw [hv2] at hv2'; cases hv2'
        · exact absurd heq (hnr an' ra l pes)
        · cases hceq
      rcases evalClass_of_none ctl.curLoc M.file hv2 with ⟨fl, hf⟩ | hu
      · refine .inr (.inl (.killed fl.reason ?_))
        intro dst hemb
        obtain ⟨-, hlay, hfile, hext, -, -, -⟩ := hemb
        simp only at hlay
        subst hlay
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_create_eval_fail2 hd hsz hnv hp1 hp2 hd1 hd2
          M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
          (M.thread _ ρ ctl) rfl (by rw [hext]; exact hv1) (by rw [hext, hfile]; exact hf)
        obtain ⟨dst', hadv⟩ := advance_withrs_failed_eval M.tagDefs M.tid s m
          (hm dst.core_run_state0)
        exact ⟨_, dst', hsteps, rfl, hadv⟩
      · exact .inr (.inr (.eval_uncovered pe2 hstuck
          (by rw [hd.operandsOf_eq]; exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
          hp2 hu hshape))
    | some v2 =>
      by_cases hint : ∃ i1 ty, v1 = Vobject (OVinteger i1) ∧ v2 = Vctype ty
      · obtain ⟨i1, ty, rfl, rfl⟩ := hint
        exact .inl ⟨_, hd.lift_step hnr hnc (Step.create_eval hnv hv1 hv2)⟩
      · -- ILLTYPED AT DISTANCE ONE (the create twin)
        have hv' : ∀ i1 ty, ¬ (v1 = Vobject (OVinteger i1) ∧ v2 = Vctype ty) :=
          fun i1 ty h => hint ⟨i1, ty, h⟩
        refine .inr (.inl (.error_next
          (apply_ctx ctx (Expr an (Eaction (Paction polarity.Pos (Action loc ann
            (Create (Pexpr [] () (PEval v1)) (Pexpr [] () (PEval v2)) pref))))), ρ, ctl.upd an, σ)
          "Create" ?_ ?_))
        · intro dst hemb
          obtain ⟨-, hlay, -, hext, -, hsym, hexc⟩ := hemb
          simp only at hlay hsym hexc
          subst hlay
          obtain ⟨s, m, hsteps, hm⟩ := step_ctx_create_eval_ws' hd hsz hnv hp1 hp2 hd1 hd2
            M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
            (M.thread _ ρ ctl) rfl (by rw [hext]; exact hv1) (by rw [hext]; exact hv2)
          rw [MachineCtx.locUpdTh_thread] at hm
          refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace,
            dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
          exact advance_withrs_eval M.tagDefs M.tid s m (hm dst.core_run_state0)
        · intro dst hemb
          obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
          simp only at hlay
          subst hlay
          exact step_ctx_create_illtyped' hd hsz hv' M.tagDefs dst.layout_state
            dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ (ctl.upd an)) rfl

/-- Memop-operand EVAL (any memop): evaluable operands are the mirror
    step; the first operand (in the engine's left-to-right order) the
    classifier rejects is the KILL `Other (DErr_core_run err)`; the first
    operand the classifier leaves uncovered (an accepted-but-unmirrored
    leaf; the whole operand's outcome not characterized) is the residual
    `eval_uncovered`. -/
theorem complete_memop_op {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {mop : memop} {pe1 pe2 : generic_pexpr Unit sym}
    (hd : Decomp e ctx (memopRedex an mop [pe1, pe2]))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hp1 : PePure pe1) (hp2 : PePure pe2)
    (hd1 : peDepth pe1 ≤ lemDefaultFuel) (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ρ, ctl, σ) := by
  have hnr : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      memopRedex an mop [pe1, pe2] ≠ runRedex an' ra l pes := by
    intro an' ra l pes h; cases h
  have hnc : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)),
      memopRedex an mop [pe1, pe2] ≠ callRedex an' ra f pes := by
    intro an' ra f pes h; cases h
  have hshape : ∀ dst, M.Embeds dst (e, ρ, ctl, σ) →
      ∃ (rsk : runstate_step_kind) (m : core_runM thread_state),
      step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
        (M.parent, M.thread e ρ ctl) = [Step_with_runstate2 rsk m] := by
    intro dst hemb
    obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
    simp only at hlay
    subst hlay
    obtain ⟨s, m, hsteps⟩ := step_ctx_memop_eval_shape hd hsz hnv M.tagDefs
      dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
    exact ⟨_, _, hsteps⟩
  -- the FAILURE at a classified operand list (MAP-shaped: the engine's
  -- `stExceptUndef_mapM`)
  have hfail : ∀ (fl : EvalFail),
      (evalClassList M.tagDefs ctl.curLoc M.extern M.file ρ [pe1, pe2]).fail? = some fl →
      RoundComplete M (e, ρ, ctl, σ) := by
    intro fl hf
    refine .inr (.inl (.killed fl.reason ?_))
    intro dst hemb
    obtain ⟨-, hlay, hfile, hext, -, -, -⟩ := hemb
    simp only at hlay
    subst hlay
    obtain ⟨s, m, hsteps, hm⟩ := step_ctx_memop_eval_fail hd hsz hnv hp1 hp2 hd1 hd2
      M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
      (M.thread _ ρ ctl) rfl (by rw [hext, hfile]; exact hf)
    obtain ⟨dst', hadv⟩ := advance_withrs_failed_eval M.tagDefs M.tid s m (hm dst.core_run_state0)
    exact ⟨_, dst', hsteps, rfl, hadv⟩
  -- an operand list the mirror does not evaluate: the classifier decides
  have hrest : (∀ c'', ¬ Step M (e, ρ, ctl, σ) c'') →
      evalPexprs M.tagDefs M.extern ρ [pe1, pe2] = none →
      RoundComplete M (e, ρ, ctl, σ) := by
    intro hstuck hev
    cases hcl : evalClassList M.tagDefs ctl.curLoc M.extern M.file ρ [pe1, pe2] with
    | kill err => exact hfail _ (by rw [hcl]; rfl)
    | undef l u => exact hfail _ (by rw [hcl]; rfl)
    | uncovered q =>
      obtain ⟨hmem, hu⟩ := evalClassList_uncovered hcl
      have hpq : PePure q := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl <;> assumption
      exact .inr (.inr (.eval_uncovered q hstuck (by rw [hd.operandsOf_eq]; exact hmem) hpq hu
        hshape))
    | vals vs =>
      rw [(evalClassList_vals_iff _ _ _ _ _ _ _).mp hcl] at hev
      cases hev
  cases hv1 : evalPexpr M.tagDefs M.extern ρ pe1 with
  | none =>
    have hstuck : ∀ c'', ¬ Step M (e, ρ, ctl, σ) c'' := by
      intro c'' hs
      rcases hd.step_factor hs with ⟨r', ρr, ctlr, σr, -, -, hr, -⟩ | ⟨an', ra, l, pes, heq, -⟩ |
          ⟨_, _, _, _, _, _, _, hceq, -⟩
      · obtain ⟨v1, v2, hv1', -, -⟩ := hr.memop_op_inv hnv
        rw [hv1] at hv1'; cases hv1'
      · exact absurd heq (hnr an' ra l pes)
      · cases hceq
    exact hrest hstuck (by rw [evalPexprs_cons, hv1]; rfl)
  | some v1 =>
    cases hv2 : evalPexpr M.tagDefs M.extern ρ pe2 with
    | none =>
      have hstuck : ∀ c'', ¬ Step M (e, ρ, ctl, σ) c'' := by
        intro c'' hs
        rcases hd.step_factor hs with ⟨r', ρr, ctlr, σr, -, -, hr, -⟩ | ⟨an', ra, l, pes, heq, -⟩ |
            ⟨_, _, _, _, _, _, _, hceq, -⟩
        · obtain ⟨v1', v2, -, hv2', -⟩ := hr.memop_op_inv hnv
          rw [hv2] at hv2'; cases hv2'
        · exact absurd heq (hnr an' ra l pes)
        · cases hceq
      exact hrest hstuck (by rw [evalPexprs_cons, hv1, evalPexprs_cons, hv2]; rfl)
    | some v2 => exact .inl ⟨_, hd.lift_step hnr hnc (Step.memop_eval hnv hv1 hv2)⟩

/-- Store ACTION_EVAL: a pointer-valued pointer operand with an
    evaluable value operand is the mirror step; a non-pointer pointer
    operand is ILLTYPED AT DISTANCE ONE (`[Step_error2 "Store"]` on the
    next round — `ShippedRefusal.error_next`); the first operand (pointer
    before value, the engine's order) the classifier rejects is the KILL
    `Other (DErr_core_run err)`; the first operand the classifier leaves
    uncovered (an accepted-but-unmirrored leaf; the whole operand's
    outcome not characterized) is the residual `eval_uncovered`. -/
theorem complete_store_op {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order}
    (hd : Decomp e ctx (storeOpRedex an loc ann ty pe2 pe3 mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe2, pe3] = none)
    (hp2 : PePure pe2) (hp3 : PePure pe3)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel) (hd3 : peDepth pe3 ≤ lemDefaultFuel)
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ρ, ctl, σ) := by
  have hnr : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      storeOpRedex an loc ann ty pe2 pe3 mo ≠ runRedex an' ra l pes := by
    intro an' ra l pes h; cases h
  have hnc : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)),
      storeOpRedex an loc ann ty pe2 pe3 mo ≠ callRedex an' ra f pes := by
    intro an' ra f pes h; cases h
  have hshape : ∀ dst, M.Embeds dst (e, ρ, ctl, σ) →
      ∃ (rsk : runstate_step_kind) (m : core_runM thread_state),
      step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
        (M.parent, M.thread e ρ ctl) = [Step_with_runstate2 rsk m] := by
    intro dst hemb
    obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
    simp only at hlay
    subst hlay
    obtain ⟨s, m, hsteps⟩ := step_ctx_store_eval_shape hd hsz hnv hp2 hp3 M.tagDefs
      dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
    exact ⟨_, _, hsteps⟩
  cases hv2 : evalPexpr M.tagDefs M.extern ρ pe2 with
  | none =>
    have hstuck : ∀ c'', ¬ Step M (e, ρ, ctl, σ) c'' := by
      intro c'' hs
      rcases hd.step_factor hs with ⟨r', ρr, ctlr, σr, -, -, hr, -⟩ | ⟨an', ra, l, pes, heq, -⟩ |
          ⟨_, _, _, _, _, _, _, hceq, -⟩
      · obtain ⟨pv, cv', hv2', -, -⟩ := hr.store_op_inv hnv
        rw [hv2] at hv2'; cases hv2'
      · exact absurd heq (hnr an' ra l pes)
      · cases hceq
    rcases evalClass_of_none ctl.curLoc M.file hv2 with ⟨fl, hf⟩ | hu
    · refine .inr (.inl (.killed fl.reason ?_))
      intro dst hemb
      obtain ⟨-, hlay, hfile, hext, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_store_eval_fail2 hd hsz hnv hp2 hp3 hd2
        M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
        (M.thread _ ρ ctl) rfl (by rw [hext, hfile]; exact hf)
      obtain ⟨dst', hadv⟩ := advance_withrs_failed_eval M.tagDefs M.tid s m
        (hm dst.core_run_state0)
      exact ⟨_, dst', hsteps, rfl, hadv⟩
    · exact .inr (.inr (.eval_uncovered pe2 hstuck
        (by rw [hd.operandsOf_eq]; exact List.mem_cons_self ..) hp2 hu hshape))
  | some v =>
    cases hv3 : evalPexpr M.tagDefs M.extern ρ pe3 with
    | none =>
      have hstuck : ∀ c'', ¬ Step M (e, ρ, ctl, σ) c'' := by
        intro c'' hs
        rcases hd.step_factor hs with ⟨r', ρr, ctlr, σr, -, -, hr, -⟩ | ⟨an', ra, l, pes, heq, -⟩ |
            ⟨_, _, _, _, _, _, _, hceq, -⟩
        · obtain ⟨pv, cv', -, hv3', -⟩ := hr.store_op_inv hnv
          rw [hv3] at hv3'; cases hv3'
        · exact absurd heq (hnr an' ra l pes)
        · cases hceq
      rcases evalClass_of_none ctl.curLoc M.file hv3 with ⟨fl, hf⟩ | hu
      · refine .inr (.inl (.killed fl.reason ?_))
        intro dst hemb
        obtain ⟨-, hlay, hfile, hext, -, -, -⟩ := hemb
        simp only at hlay
        subst hlay
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_store_eval_fail3 hd hsz hnv hp2 hp3 hd2 hd3
          M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
          (M.thread _ ρ ctl) rfl (by rw [hext]; exact hv2) (by rw [hext, hfile]; exact hf)
        obtain ⟨dst', hadv⟩ := advance_withrs_failed_eval M.tagDefs M.tid s m
          (hm dst.core_run_state0)
        exact ⟨_, dst', hsteps, rfl, hadv⟩
      · exact .inr (.inr (.eval_uncovered pe3 hstuck
          (by rw [hd.operandsOf_eq]; exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
          hp3 hu hshape))
    | some cv =>
      by_cases hptr : ∃ pv, v = Vobject (OVpointer pv)
      · obtain ⟨pv, rfl⟩ := hptr
        exact .inl ⟨_, hd.lift_step hnr hnc (Step.store_eval hnv hv2 hv3)⟩
      · -- ILLTYPED AT DISTANCE ONE (the store twin)
        have hv' : ∀ pv, v ≠ Vobject (OVpointer pv) := fun pv h => hptr ⟨pv, h⟩
        refine .inr (.inl (.error_next
          (apply_ctx ctx (Expr an (Eaction (Paction polarity.Pos (Action loc ann
            (Store0 false (Pexpr [] () (PEval (Vctype ty))) (Pexpr [] () (PEval v))
              (Pexpr [] () (PEval cv)) mo))))), ρ, ctl.upd an, σ)
          "Store" ?_ ?_))
        · intro dst hemb
          obtain ⟨-, hlay, -, hext, -, hsym, hexc⟩ := hemb
          simp only at hlay hsym hexc
          subst hlay
          obtain ⟨s, m, hsteps, hm⟩ := step_ctx_store_eval_ws' hd hsz hnv hp2 hp3 hd2 hd3
            M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
            (M.thread _ ρ ctl) rfl (by rw [hext]; exact hv2) (by rw [hext]; exact hv3)
          rw [MachineCtx.locUpdTh_thread] at hm
          refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace,
            dst.dr_step_counter + 1, rfl, hsym, hexc, ?_⟩
          exact advance_withrs_eval M.tagDefs M.tid s m (hm dst.core_run_state0)
        · intro dst hemb
          obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
          simp only at hlay
          subst hlay
          exact step_ctx_store_illtyped' hd hsz hv' M.tagDefs dst.layout_state
            dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ (ctl.upd an)) rfl

/-! ### The memop row: the pointer-equality fork and the driver's
INVALID-memop panic -/

/-- `eqPtrval`'s one-layer result is active, or the differing-provenance
    `msum` fork (CerbMem.lean:1766): a nondeterministic node with the two
    branches "using provenance" (false) and "ignoring provenance"
    (address equality). -/
theorem eqPtrval_layer (l : CerbLocation.Loc) (pv1 pv2 : CerbMem.PointerValue) (σ : Mem) :
    (∃ b, runOne (CerbMem.eqPtrval l pv1 pv2) σ = (NDactive b, σ)) ∨
    (∃ a1 a2 : Int, runOne (CerbMem.eqPtrval l pv1 pv2) σ =
      (NDnd "pointer equality"
        [("using provenance", CerbMem.memReturn false),
         ("ignoring provenance", CerbMem.memReturn (a1 == a2))], σ)) := by
  unfold CerbMem.eqPtrval
  repeat' (first
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr ⟨_, _, rfl⟩
    | split
    | dsimp only)

/-- `nd_bind_lemFuel` at a successor fuel, active left operand. -/
theorem runOne_bindF_active {a b cs err info st : Type} (n : Nat)
    {m : ndM a info err cs st} {f : a → ndM b info err cs st} {s s' : st} {z : a}
    (h : runOne m s = (NDactive z, s')) :
    runOne (nd_bind_lemFuel (Nat.succ n) m f) s = runOne (f z) s' := by
  rcases m with ⟨g⟩
  dsimp only [runOne] at h
  unfold nd_bind_lemFuel
  dsimp only [runOne]
  rw [h]
  dsimp only
  rcases hf : f z with ⟨g'⟩
  rfl

/-- `nd_bind` (fuel `CerbFuel.driverFuel = 10^8`, the drive-cone budget
    since the fuel arc; `CerbND.nd_bind_wrapper_defeq`), forking left
    operand: the fork survives with the same arity, every branch carrying
    the continuation at the decremented fuel (Nondeterminism.lean:188). -/
theorem runOne_bind_nd {a b cs err info st : Type}
    {m : ndM a info err cs st} (f : a → ndM b info err cs st) {s s' : st}
    {i : info} {bs : List (info × ndM a info err cs st)}
    (h : runOne m s = (NDnd i bs, s')) :
    ∃ bs' : List (info × ndM b info err cs st),
      runOne (nd_bind m f) s = (NDnd i bs', s') ∧
      bs'.length = bs.length ∧
      ∀ p' ∈ bs', ∃ p ∈ bs, p'.2 = nd_bind_lemFuel 99999999 p.2 f := by
  rcases m with ⟨g⟩
  dsimp only [runOne] at h
  have hb : runOne (nd_bind (ND g) f) s =
      (NDnd i (bs.map (fun p => (p.1, nd_bind_lemFuel 99999999 p.2 f))), s') := by
    show runOne (nd_bind_lemFuel CerbFuel.driverFuel (ND g) f) s = _
    rw [show CerbFuel.driverFuel = Nat.succ 99999999 from rfl]
    conv => lhs; unfold nd_bind_lemFuel
    dsimp only [runOne]
    rw [h]
  refine ⟨_, hb, by simp, ?_⟩
  intro p' hp'
  rw [List.mem_map] at hp'
  obtain ⟨p, hp, rfl⟩ := hp'
  exact ⟨p, hp, rfl⟩

/-- `liftND_lemFuel` at a double-successor fuel, active operand. -/
theorem runOne_liftNDF_active {a cs err1 err2 info1 info2 st1 st2 : Type} (n : Nat)
    (get2 : st2 → st1) (put1 : st2 → st1 → st2) (li : info1 → info2) (le : err1 → err2)
    {m : ndM a info1 err1 cs st1} {s2 : st2} {z : a} {s1' : st1}
    (h : runOne m (get2 s2) = (NDactive z, s1')) :
    runOne (liftND_lemFuel (Nat.succ (Nat.succ n)) get2 put1 li le m) s2 =
      (NDactive z, put1 s2 s1') := by
  rcases m with ⟨g⟩
  dsimp only [runOne] at h
  unfold liftND_lemFuel
  dsimp only [runOne]
  rw [h]
  unfold liftAction_lemFuel
  rfl

/-- `liftND_lemFuel` at a double-successor fuel, forking operand: the
    fork survives with the same arity, every branch lifted at the
    decremented fuel, the info mapped (Nondeterminism.lean:306). -/
theorem runOne_liftNDF_nd {a cs err1 err2 info1 info2 st1 st2 : Type} (n : Nat)
    (get2 : st2 → st1) (put1 : st2 → st1 → st2) (li : info1 → info2) (le : err1 → err2)
    {m : ndM a info1 err1 cs st1} {s2 : st2} {i : info1}
    {bs : List (info1 × ndM a info1 err1 cs st1)} {s1' : st1}
    (h : runOne m (get2 s2) = (NDnd i bs, s1')) :
    ∃ bs' : List (info2 × ndM a info2 err2 cs st2),
      runOne (liftND_lemFuel (Nat.succ (Nat.succ n)) get2 put1 li le m) s2 =
        (NDnd (li i) bs', put1 s2 s1') ∧
      bs'.length = bs.length ∧
      ∀ p' ∈ bs', ∃ p ∈ bs, p'.2 = liftND_lemFuel n get2 put1 li le p.2 := by
  rcases m with ⟨g⟩
  dsimp only [runOne] at h
  have hb : runOne (liftND_lemFuel (Nat.succ (Nat.succ n)) get2 put1 li le (ND g)) s2 =
      (liftAction_lemFuel (Nat.succ n) get2 put1 li le (NDnd i bs), put1 s2 s1') := by
    conv => lhs; unfold liftND_lemFuel
    dsimp only [runOne]
    rw [h]
  have hc : ∃ F : info1 × ndM a info1 err1 cs st1 → info2 × ndM a info2 err2 cs st2,
      liftAction_lemFuel (Nat.succ n) get2 put1 li le (NDnd i bs) = NDnd (li i) (bs.map F) ∧
      ∀ p, (F p).2 = liftND_lemFuel n get2 put1 li le p.2 := by
    apply Exists.intro
    constructor
    · conv => lhs; unfold liftAction_lemFuel
    · intro p
      rcases p with ⟨pi, pm⟩
      rfl
  obtain ⟨F, hF, hF2⟩ := hc
  refine ⟨bs.map F, by rw [hb, hF], by simp, ?_⟩
  intro p' hp'
  rw [List.mem_map] at hp'
  obtain ⟨p, hp, rfl⟩ := hp'
  exact ⟨p, hp, hF2 p⟩

/-- The shipped exhaustive runner (CerbND.lean:89) at an active
    one-layer result: one execution. -/
theorem runNDFuel_active {a info err cs st : Type} [Inhabited a] [Inhabited st] (n : Nat)
    {m : ndM a info err cs st} {s s' : st} {z : a}
    (h : runOne m s = (NDactive z, s')) :
    CerbND.runNDFuel (Nat.succ n) m s = [(nd_status.Active z, ([] : List String), s')] := by
  rcases m with ⟨g⟩
  dsimp only [runOne] at h
  conv => lhs; unfold CerbND.runNDFuel
  dsimp only
  rw [h]

/-- The shipped exhaustive runner at a forking one-layer result: every
    branch is explored, results prepended (CerbND.lean:89, mirroring
    smt2.ml:75-82). -/
theorem runNDFuel_nd {a info err cs st : Type} [Inhabited a] [Inhabited st] (n : Nat)
    {m : ndM a info err cs st} {s s' : st} {i : info}
    {bs : List (info × ndM a info err cs st)}
    (h : runOne m s = (NDnd i bs, s')) :
    CerbND.runNDFuel (Nat.succ n) m s =
      bs.foldl (fun acc p => CerbND.runNDFuel n p.2 s' ++ acc) [] := by
  rcases m with ⟨g⟩
  dsimp only [runOne] at h
  conv => lhs; unfold CerbND.runNDFuel
  dsimp only
  rw [h]

/-- A left fold of singleton-producing appends has the list's length. -/
theorem foldl_append_singletons_length {α β : Type} (g : α → List β) (bs : List α)
    (init : List β) (hg : ∀ p ∈ bs, (g p).length = 1) :
    (bs.foldl (fun acc p => g p ++ acc) init).length = init.length + bs.length := by
  induction bs generalizing init with
  | nil => simp
  | cons p bs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (g p ++ init) (fun q hq => hg q (List.mem_cons_of_mem p hq)),
      List.length_append, hg p (List.mem_cons_self ..)]
    omega

/-- Activity through a bind at a successor fuel. -/
theorem bind_branch_active {a b cs err info st : Type} (n : Nat)
    {m : ndM a info err cs st} {f : a → ndM b info err cs st} {s : st}
    (h : ∃ z s', runOne m s = (NDactive z, s'))
    (hf : ∀ z s', ∃ z' s'', runOne (f z) s' = (NDactive z', s'')) :
    ∃ z' s'', runOne (nd_bind_lemFuel (Nat.succ n) m f) s = (NDactive z', s'') := by
  obtain ⟨z, s', hz⟩ := h
  obtain ⟨z', s'', hf'⟩ := hf z s'
  exact ⟨z', s'', (runOne_bindF_active n hz).trans hf'⟩

/-- THE FORK: at pointer operands whose `eqPtrval` forks, the shipped
    advance of the memop step is explored by `CerbND.runND` into TWO
    executions (both active: the "using provenance" and the "ignoring
    provenance" answers, each installed by the memop continuation). -/
theorem memop_fork {tds : Fmap sym (CerbLocation.Loc × tag_definition)} {tid : Nat}
    {loc : CerbLocation.Loc} {pv1 pv2 : CerbMem.PointerValue} {k : value → thread_state}
    {dst : driver_state} {a1 a2 : Int}
    (hnd : runOne (CerbMem.eqPtrval loc pv1 pv2) dst.layout_state =
      (NDnd "pointer equality"
        [("using provenance", CerbMem.memReturn false),
         ("ignoring provenance", CerbMem.memReturn (a1 == a2))], dst.layout_state)) :
    2 ≤ (CerbND.runND (advance_step tds tid (Step_memop_request2 loc PtrEq
      [Vobject (OVpointer pv1), Vobject (OVpointer pv2)] tid false k)) dst).length := by
  -- the lifted fork (liftMem = liftND at lemDefaultFuel = succ (succ 999998))
  obtain ⟨bs1, h1, hlen1, hmem1⟩ := runOne_liftNDF_nd 999998
    (fun (d : driver_state) => d.layout_state)
    (fun (d : driver_state) (m : CerbMem.MemState) => { d with layout_state := m })
    (fun (s : String) => SK_misc ["memory", s]) DErr_memory hnd
  have h1' : runOne (liftMem (CerbMem.eqPtrval loc pv1 pv2)) dst =
      (NDnd (SK_misc ["memory", "pointer equality"]) bs1,
       { dst with layout_state := dst.layout_state }) := h1
  -- the debug print, then the lifted memory operation
  have hA : runOne (nd_bind (print_debug 2 [DB_driver] (fun (u : Unit) => match u with | () => "PtrEq"))
      (fun (_ : Unit) => liftMem (CerbMem.eqPtrval loc pv1 pv2))) dst =
      (NDnd (SK_misc ["memory", "pointer equality"]) bs1,
       { dst with layout_state := dst.layout_state }) :=
    (runOne_bind_active (z := ()) (s' := dst) (by rfl)).trans h1'
  -- the boolean-to-value continuation
  obtain ⟨bs2, hB, hlen2, hmem2⟩ := runOne_bind_nd
    (fun (is_eq : Bool) => nd_return (k (if is_eq then Vtrue else Vfalse))) hA
  -- the thread install
  obtain ⟨bs3, hC, hlen3, hmem3⟩ := runOne_bind_nd
    (fun (th_st' : thread_state) => nd_update (fun (dr_st : driver_state) =>
      update_core_state (update_thread_state tid th_st' dr_st.core_state0) dr_st)) hB
  have hP : runOne (perform_memop_request2 tds loc PtrEq
      [Vobject (OVpointer pv1), Vobject (OVpointer pv2)] tid k) dst =
      (NDnd (SK_misc ["memory", "pointer equality"]) bs3,
       { dst with layout_state := dst.layout_state }) := by
    unfold perform_memop_request2
    dsimp only
    exact hC
  -- the advance (no wakeup continuation)
  obtain ⟨bs4, hD, hlen4, hmem4⟩ := runOne_bind_nd
    (fun (u : Unit) => match u with | () => nd_return NOWAKEUP) hP
  have hD' : runOne (advance_step tds tid (Step_memop_request2 loc PtrEq
      [Vobject (OVpointer pv1), Vobject (OVpointer pv2)] tid false k)) dst =
      (NDnd (SK_misc ["memory", "pointer equality"]) bs4,
       { dst with layout_state := dst.layout_state }) := by
    unfold advance_step
    dsimp only
    rw [if_neg (fun h => Bool.noConfusion h)]
    exact hD
  -- every branch of the advance is one active execution
  have hact : ∀ p ∈ bs4, ∃ z s'', runOne p.2 { dst with layout_state := dst.layout_state } =
      (NDactive z, s'') := by
    intro p4 hp4
    obtain ⟨p3, hp3, hp4e⟩ := hmem4 p4 hp4
    obtain ⟨p2, hp2, hp3e⟩ := hmem3 p3 hp3
    obtain ⟨p1, hp1, hp2e⟩ := hmem2 p2 hp2
    obtain ⟨p0, hp0, hp1e⟩ := hmem1 p1 hp1
    rw [hp4e, hp3e, hp2e, hp1e]
    refine bind_branch_active 99999998 (bind_branch_active 99999998 (bind_branch_active 99999998 ?_
      (fun z s' => ⟨_, _, rfl⟩)) (fun z s' => ⟨_, _, rfl⟩))
      (fun z s' => by cases z; exact ⟨_, _, rfl⟩)
    -- the lifted memory branch: one of the two `memReturn`s
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp0
    rcases hp0 with rfl | rfl <;>
      exact ⟨_, _, runOne_liftNDF_active 999996 _ _ _ _ rfl⟩
  -- the runner explores both branches
  show 2 ≤ (CerbND.runNDFuel CerbFuel.driverFuel _ dst).length
  rw [show CerbFuel.driverFuel = Nat.succ 99999999 from rfl, runNDFuel_nd 99999999 hD',
    foldl_append_singletons_length (fun p => CerbND.runNDFuel 99999999 p.2
      { dst with layout_state := dst.layout_state }) bs4 [] ?_]
  · simp only [List.length_nil, Nat.zero_add]
    rw [hlen4, hlen3, hlen2, hlen1]
    simp
  · intro p hp
    obtain ⟨z, s'', hz⟩ := hact p hp
    rw [runNDFuel_active 99999998 hz]
    rfl

/-- The driver's memop discharge at `PtrEq` operands that are NOT both
    pointers: the `INVALID memop request` panic (Driver.lean:288, under
    the discharge's install bind). -/
theorem perform_memop_ptreq_panic (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (loc : CerbLocation.Loc) (tid : Nat) (k : value → thread_state) (v1 v2 : value)
    (hnp : ¬ ∃ pv1 pv2, v1 = Vobject (OVpointer pv1) ∧ v2 = Vobject (OVpointer pv2)) :
    ∃ (msg : String) (g : thread_state → ndM Unit step_kind driver_error
        (mem_constraint CerbMem.IntegerValue) driver_state),
      perform_memop_request2 tds loc PtrEq [v1, v2] tid k = nd_bind (failwithI msg) g := by
  unfold perform_memop_request2
  rcases v1 with ov1 | lv1 | _ | _ | _ | _ | ⟨_, _⟩ | _ <;>
  rcases v2 with ov2 | lv2 | _ | _ | _ | _ | ⟨_, _⟩ | _ <;>
  (try (cases ov1)) <;> (try (cases ov2)) <;>
  first
    | exact absurd ⟨_, _, rfl, rfl⟩ hnp
    | exact ⟨_, _, rfl⟩

/-- MEMOP `PtrEq` at value operands: pointer operands with a
    deterministic `eqPtrval` are the mirror step; the
    differing-provenance fork is FORK; non-pointer operands are the
    driver's memop PANIC. -/
theorem complete_memop_vals {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {v1 v2 : value}
    (hd : Decomp e ctx (memopPtrEqVals an v1 v2))
    (hsz : esize e ≤ lemDefaultFuel) (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ρ, ctl, σ) := by
  have hnr : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (l : sym)
      (pes : List (generic_pexpr Unit sym)),
      memopPtrEqVals an v1 v2 ≠ runRedex an' ra l pes := by
    intro an' ra l pes h; cases h
  have hnc : ∀ (an' : List _root_.annot) (ra : core_run_annotation) (f : sym)
      (pes : List (generic_pexpr Unit sym)),
      memopPtrEqVals an v1 v2 ≠ callRedex an' ra f pes := by
    intro an' ra f pes h; cases h
  by_cases hptrs : ∃ pv1 pv2, v1 = Vobject (OVpointer pv1) ∧ v2 = Vobject (OVpointer pv2)
  · obtain ⟨pv1, pv2, rfl, rfl⟩ := hptrs
    rcases eqPtrval_layer default pv1 pv2 σ with ⟨b, hb⟩ | ⟨a1, a2, hnd⟩
    · have hmem : applyMemM (CerbMem.eqPtrval default pv1 pv2) σ = some (b, σ) := by
        rw [applyMemM_eq_ndProj, hb]; rfl
      exact .inl ⟨_, hd.lift_step hnr hnc
        (Step.memop_ptreq (valueFromPexpr_val _ _) (valueFromPexpr_val _ _) hmem)⟩
    · refine .inr (.inl (.fork ?_))
      intro dst hemb
      obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      have hsteps := step_ctx_memop hd hsz rfl rfl M.tagDefs dst.layout_state
        dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
      rw [hd.unseq_ccall_false] at hsteps
      refine ⟨_, hsteps, rfl, ?_⟩
      exact memop_fork (by rw [eqPtrval_loc_irrel _ default]; exact hnd)
  · obtain ⟨msg, g, hpm⟩ := perform_memop_ptreq_panic M.tagDefs
      (locUpdTh an (M.thread e ρ ctl)).current_loc M.tid
      (fun cval => { locUpdTh an (M.thread e ρ ctl) with
        arena := apply_ctx ctx (Expr [] (Epure (Pexpr [] () (PEval cval)))) }) v1 v2 hptrs
    refine .inr (.inl (.panic_memop msg ?_))
    intro dst hemb
    obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
    simp only at hlay
    subst hlay
    have hsteps := step_ctx_memop hd hsz rfl rfl M.tagDefs dst.layout_state
      dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl
    rw [hd.unseq_ccall_false] at hsteps
    exact ⟨_, _, _, _, _, g, hsteps, hpm⟩

/-- Erun at a context WITHOUT a current procedure: the engine's PANIC
    in the label lookup's key (`ShippedRefusal.panic_noproc`; the
    mirror's label map is empty, fail-closed). -/
theorem complete_run_noproc {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {l : sym} {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (runRedex an ra l pes))
    (hsz : esize e ≤ lemDefaultFuel)
    {ctl : Ctl} (hproc : ctl.proc = none) (ρ : EnvStack) (σ : Mem) :
    RoundComplete M (e, ρ, ctl, σ) := by
  refine .inr (.inl (.panic_noproc "Core_reduction ==> Erun outside of a proc" hproc ?_))
  intro dst hemb
  obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
  simp only at hlay
  subst hlay
  obtain ⟨s, inst, k, hsteps⟩ := step_ctx_run_noproc hd hsz M.tagDefs dst.layout_state
    dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ ctl) rfl hproc
  exact ⟨s, l, inst, k, hsteps⟩

/-! ### The call rows (calls arc C2): the PCALL round classified -/

/-- The Eproc argument map (`stExceptUndef_mapM` over `full_eval_pexpr`)
    delivers the first classified failure among the arguments (the
    MAP-shaped list, `evalClassList`). -/
theorem mapM_full_eval_fail {th : thread_state}
    {tds : Fmap sym (CerbLocation.Loc × tag_definition)} {σ : Mem}
    {file : generic_file Unit core_run_annotation} {ext : Fmap sym sym}
    (f : generic_pexpr Unit sym → core_run_state →
      exceptM ((t0 value × core_run_state)) core_run_cause)
    (hf : ∀ (pe : generic_pexpr Unit sym) (rs' : core_run_state),
      f pe rs' = full_eval_pexpr tds th ext σ file pe rs')
    (pes : List (generic_pexpr Unit sym)) {fl : EvalFail}
    (hp : ∀ pe ∈ pes, PePure pe) (hd : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel)
    (h : (evalClassList tds th.current_loc ext file th.env pes).fail? = some fl)
    (rs : core_run_state) :
    stExceptUndef_mapM f pes rs = fl.run (List value) core_run_state rs := by
  let X := { pe : generic_pexpr Unit sym // pe ∈ pes }
  have hmap : pes = (pes.attach.map Subtype.val) := (List.attach_map_subtype_val pes).symm
  have hfold : stExceptUndef_mapM f pes rs =
      stExceptUndef_mapM (fun (x : X) => f x.val) pes.attach rs := by
    conv => lhs; rw [hmap]
    unfold stExceptUndef_mapM stExpect_mapM
    rw [List.map_map]
    rfl
  have hval : ∀ (x : X) (rs' : core_run_state) (v : value),
      evalPexpr tds ext th.env x.val = some v → f x.val rs' = Result (Defined v, rs') := by
    intro x rs' v hv
    rw [hf, full_eval_bridge hv (hd x.val x.property) σ file]
    rfl
  have hfail : ∀ (x : X) (rs' : core_run_state) (fl' : EvalFail),
      (evalClass tds th.current_loc ext file th.env x.val).fail? = some fl' →
      f x.val rs' = fl'.run value core_run_state rs' := by
    intro x rs' fl' hf'
    rw [hf, full_eval_bridge_fail (hp x.val x.property) hf' (hd x.val x.property) σ]
  have hcls : (evalClassList tds th.current_loc ext file th.env
      (pes.attach.map Subtype.val)).fail? = some fl := by
    rw [← hmap]; exact h
  rw [hfold]
  exact stExceptUndef_mapM_class_fail (fun (x : X) => f x.val) Subtype.val (fun _ v => v)
    hval hfail pes.attach hcls rs

/-- … the kill face (E1's statement, verbatim). -/
theorem mapM_full_eval_kill {th : thread_state}
    {tds : Fmap sym (CerbLocation.Loc × tag_definition)} {σ : Mem}
    {file : generic_file Unit core_run_annotation} {ext : Fmap sym sym}
    (f : generic_pexpr Unit sym → core_run_state →
      exceptM ((t0 value × core_run_state)) core_run_cause)
    (hf : ∀ (pe : generic_pexpr Unit sym) (rs' : core_run_state),
      f pe rs' = full_eval_pexpr tds th ext σ file pe rs')
    (pes : List (generic_pexpr Unit sym)) {err : core_run_cause}
    (hp : ∀ pe ∈ pes, PePure pe) (hd : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel)
    (h : evalClassList tds th.current_loc ext file th.env pes = .kill err)
    (rs : core_run_state) :
    stExceptUndef_mapM f pes rs = Exception err :=
  mapM_full_eval_fail f hf pes (fl := .kill err) hp hd (by rw [h]; rfl) rs

/-- The PCALL round whose ARGUMENTS the classifier rejects: the monad
    RAISES the classified error before `call_proc` is reached (the
    engine's evaluation order — arguments first). -/
theorem step_ctx_call_fail_args {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {f : sym} {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (callRedex an ra f pes))
    (hsz : esize e ≤ lemDefaultFuel)
    (hpes : ∀ pe ∈ pes, PePure pe)
    (hdep : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) {fl : EvalFail}
    (hf : (evalClassList tds th.current_loc ext file th.env pes).fail? = some fl) :
    ∃ m : core_runM thread_state,
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval "Eproc") m] ∧
      ∀ rs, m rs = fl.run thread_state core_run_state rs := by
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
       mapM_full_eval_fail _ (fun _ _ => rfl) pes hpes hdep hf rs]
     cases fl <;> rfl)

/-- … the kill face (E1's statement). -/
theorem step_ctx_call_kill_args {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {f : sym} {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (callRedex an ra f pes))
    (hsz : esize e ≤ lemDefaultFuel)
    (hpes : ∀ pe ∈ pes, PePure pe)
    (hdep : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e) {err : core_run_cause}
    (hk : evalClassList tds th.current_loc ext file th.env pes = .kill err) :
    ∃ m : core_runM thread_state,
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval "Eproc") m] ∧
      ∀ rs, m rs = Exception err :=
  step_ctx_call_fail_args hd hsz hpes hdep tds σ file ext tid parent th harena (fl := .kill err) (by rw [hk]; rfl)

/-- THE CALL, classified (the per-constructor completeness obligation at
    `Eproc`): the mirror steps iff the arguments evaluate (mirror
    evaluator), the procedure is found (`lookupProc`) and the arity
    matches; otherwise the shipped round is a KILL — `call_proc`'s two
    `Illformed_program` messages verbatim (unknown procedure; wrong
    number of arguments) or the classifier's kill for a rejected argument
    — or the argument residual `eval_uncovered`. The engine evaluates the
    arguments BEFORE `call_proc`, so an argument kill takes precedence
    over an unknown procedure; the classification follows that order. -/
theorem complete_call {an : List _root_.annot} {M : MachineCtx} {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {f : sym} {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (callRedex an ra f pes))
    (hsz : esize e ≤ lemDefaultFuel)
    (hpes : ∀ pe ∈ pes, PePure pe)
    (hdep : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel)
    (ρ : EnvStack) (ctl : Ctl) (σ : Mem) :
    RoundComplete M (e, ρ, ctl, σ) := by
  have hc : callRedex? e = some (ctx, f, pes) := hd.callRedex?_some
  cases hvs : evalPexprs M.tagDefs M.extern ρ pes with
  | some vs =>
    cases hf : lookupProc M.file M.extern f with
    | some pb =>
      obtain ⟨params, body⟩ := pb
      by_cases hlen : params.length = vs.length
      · exact .inl ⟨_, Step.call hc hvs hf hlen⟩
      · -- ARITY MISMATCH: `call_proc`'s kill, verbatim
        refine .inr (.inl (.killed (Other (DErr_core_run (Illformed_program
          (String.append "calling procedure `"
            (String.append (show_symbol f)
              (String.append "' with the wrong number of args: |args|="
                (String.append (Lem_String_extra.stringFromNat vs.length)
                  (String.append "expecting: "
                    (Lem_String_extra.stringFromNat params.length))))))))) ?_))
        intro dst hemb
        obtain ⟨-, hlay, hfile, hext, -, -, -⟩ := hemb
        simp only at hlay
        subst hlay
        obtain ⟨m, hsteps, hm⟩ := step_ctx_call_arity hd hsz hdep M.tagDefs dst.layout_state
          dst.core_file dst.core_extern M.tid M.parent (M.thread e ρ ctl) rfl
          (by rw [hext]; exact hvs) (by rw [hfile, hext]; exact hf) hlen
        exact ⟨_, dst, hsteps, rfl,
          advance_withrs_killed_eval M.tagDefs M.tid _ m (hm dst.core_run_state0)⟩
    | none =>
      -- UNKNOWN PROCEDURE: `call_proc`'s kill, verbatim
      refine .inr (.inl (.killed (Other (DErr_core_run (Illformed_program
        (String.append "calling an unknown procedure: " (show_symbol f))))) ?_))
      intro dst hemb
      obtain ⟨-, hlay, hfile, hext, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      obtain ⟨m, hsteps, hm⟩ := step_ctx_call_unknown hd hsz hdep M.tagDefs dst.layout_state
        dst.core_file dst.core_extern M.tid M.parent (M.thread e ρ ctl) rfl
        (by rw [hext]; exact hvs) (by rw [hfile, hext]; exact hf)
      exact ⟨_, dst, hsteps, rfl,
        advance_withrs_killed_eval M.tagDefs M.tid _ m (hm dst.core_run_state0)⟩
  | none =>
    have hstuck : ∀ c'', ¬ Step M (e, ρ, ctl, σ) c'' := by
      intro c'' hs
      obtain ⟨_, _, vs', hvs', -⟩ := hs.call_inv hc
      rw [hvs] at hvs'
      cases hvs'
    have hshape : ∀ dst, M.Embeds dst (e, ρ, ctl, σ) →
        ∃ (rsk : runstate_step_kind) (m : core_runM thread_state),
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread e ρ ctl) = [Step_with_runstate2 rsk m] := by
      intro dst hemb
      obtain ⟨-, hlay, -, -, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      obtain ⟨m, hsteps⟩ := step_ctx_call_shape hd hsz M.tagDefs dst.layout_state
        dst.core_file dst.core_extern M.tid M.parent (M.thread _ _ ctl) rfl
      exact ⟨_, _, hsteps⟩
    have hfail : ∀ (fl : EvalFail),
        (evalClassList M.tagDefs ctl.curLoc M.extern M.file ρ pes).fail? = some fl →
        RoundComplete M (e, ρ, ctl, σ) := by
      intro fl hf
      refine .inr (.inl (.killed fl.reason ?_))
      intro dst hemb
      obtain ⟨-, hlay, hfile, hext, -, -, -⟩ := hemb
      simp only at hlay
      subst hlay
      obtain ⟨m, hsteps, hm⟩ := step_ctx_call_fail_args hd hsz hpes hdep M.tagDefs
        dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ _ ctl) rfl
        (by rw [hext, hfile]; exact hf)
      obtain ⟨dst', hadv⟩ := advance_withrs_failed_eval M.tagDefs M.tid _ m (hm dst.core_run_state0)
      exact ⟨_, dst', hsteps, rfl, hadv⟩
    cases hcl : evalClassList M.tagDefs ctl.curLoc M.extern M.file ρ pes with
    | kill err => exact hfail _ (by rw [hcl]; rfl)
    | undef l u => exact hfail _ (by rw [hcl]; rfl)
    | uncovered pe =>
      obtain ⟨hmem, hu⟩ := evalClassList_uncovered hcl
      exact .inr (.inr (.eval_uncovered pe hstuck
        (by rw [hd.operandsOf_eq]; exact hmem) (hpes pe hmem) hu hshape))
    | vals vs' =>
      rw [(evalClassList_vals_iff _ _ _ _ _ _ _).mp hcl] at hvs
      cases hvs

/-- THE RETURN, classified: a VALUE at a NON-EMPTY call stack ALWAYS steps
    — RETURN at a bare value (`Step.ret`; the engine's arm has no failure
    channel but the empty-env panic, excluded by the cons-shaped env),
    REMOVE-ANNOT at an annotated one (`Step.ret_annot`). At the empty
    stack a value is the terminal (`cerberusRound_classify`'s value arms). -/
theorem complete_ret {M : MachineCtx} (w : SpikeValA) (ev0 : Fmap sym value)
    (evs : List (Fmap sym value)) (pc : Option sym × context)
    (κ : List (Option sym × context)) (q : Option sym) (ℓ : exec_location)
    (lc : CerbLocation.Loc) (sp : RunSup) (σ : Mem) :
    RoundComplete M (ofValA w, ev0 :: evs, ⟨pc :: κ, q, ℓ, lc, sp⟩, σ) := by
  obtain ⟨p, ctx⟩ := pc
  cases w with
  | pure a b v => exact .inl ⟨_, Step.ret⟩
  | annot a a2 b ds v => exact .inl ⟨_, Step.ret_annot⟩

/-! ### THE ASSEMBLED COMPLETENESS THEOREM -/

/-- MIRROR COMPLETENESS ON THE FRAGMENT: at every non-value `Frag`
    configuration (cons-shaped environment, `esize e ≤ lemDefaultFuel`),
    the mirror steps, or the shipped round is a classified refusal
    (`ShippedRefusal`: ILLTYPED / KILL / FORK / PANIC), or the
    configuration is one of the registered gaps (`OpenRound`). One
    lemma per redex root of the fragment (`complete_*`), dispatched by
    the decomposition `Frag.decomp`. -/
theorem frag_round_complete {M : MachineCtx}
    {e : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {ctl : Ctl} {σ : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel) (hnv : toVal e = none) :
    RoundComplete M (e, ev0 :: evs, ctl, σ) := by
  obtain ⟨ctx, r, hd, hfr⟩ := hf.decomp hnv
  have hrj := hd.redex
  cases hrj with
  | store => exact complete_store hd hsz _ _ _
  | load => exact complete_load hd hsz _ _ _
  | create => exact complete_create hd hsz _ _ _
  | kill => exact complete_kill hd hsz _ _ _
  | @kill_op an loc ann kind pe hnvK =>
    obtain ⟨hpK, hdK⟩ : PePure pe ∧ peDepth pe ≤ lemDefaultFuel := by
      cases hfr with
      | kill =>
        rw [show valueFromPexpr (Pexpr [] () (PEval
          (Vobject (OVpointer _)))) = some _ from rfl] at hnvK
        cases hnvK
      | kill_op hnvK' hpK hdK => exact ⟨hpK, hdK⟩
    exact complete_kill_op hd hsz hnvK hpK hdK _ _ _
  | alloc => exact complete_alloc hd hsz _ _ _
  | @create_op an loc ann pref pe1 pe2 hnvC =>
    obtain ⟨hp1, hp2, hd1, hd2⟩ : PePure pe1 ∧ PePure pe2 ∧
        peDepth pe1 ≤ lemDefaultFuel ∧ peDepth pe2 ≤ lemDefaultFuel := by
      cases hfr with
      | create =>
        rw [valueFromPexprs_pair, valueFromPexpr_val, valueFromPexpr_val] at hnvC
        cases hnvC
      | create_op hnvC' hp1 hp2 hd1 hd2 => exact ⟨hp1, hp2, hd1, hd2⟩
    exact complete_create_op hd hsz hnvC hp1 hp2 hd1 hd2 _ _ _
  | bound_pure => exact complete_bound_pure hd _ _ _
  | bound_annot => exact complete_bound_annot hd _ _ _
  | @alloc_op an loc ann pref pe1 pe2 hnvA =>
    obtain ⟨hp1, hp2, hd1, hd2⟩ : PePure pe1 ∧ PePure pe2 ∧
        peDepth pe1 ≤ lemDefaultFuel ∧ peDepth pe2 ≤ lemDefaultFuel := by
      cases hfr with
      | alloc =>
        rw [valueFromPexprs_pair, valueFromPexpr_val, valueFromPexpr_val] at hnvA
        cases hnvA
      | alloc_op hnvA' hp1 hp2 hd1 hd2 => exact ⟨hp1, hp2, hd1, hd2⟩
    exact complete_alloc_op hd hsz hnvA hp1 hp2 hd1 hd2 _ _ _
  | beta_pure => exact complete_beta_pure hd _ _ _ _
  | beta_annot => exact complete_beta_annot hd _ _ _ _
  | merge hirr => exact complete_merge hd _ _ _
  | save sb ps body =>
    obtain ⟨hp, hdep⟩ : (∀ pe ∈ saveParamPexprs ps, PePure pe) ∧
        (∀ pe ∈ saveParamPexprs ps, peDepth pe ≤ lemDefaultFuel) := by
      cases hfr with
      | save hp hdep _ => exact ⟨hp, hdep⟩
    exact complete_save hd hsz hp hdep _ _ _ _
  | if_ g e2 e3 =>
    obtain ⟨hpg, hdg⟩ : PePure g ∧ peDepth g ≤ lemDefaultFuel := by
      cases hfr with
      | if_ hpg hdg _ _ => exact ⟨hpg, hdg⟩
    exact complete_if hd hsz hpg hdg _ _ _
  | case_ pe pats =>
    cases hfr with
    | case_value hbr hbsz => exact complete_case hd hsz _ _ _
  | run ra l pes =>
    obtain ⟨hpes, hdep⟩ : (∀ pe ∈ pes, PePure pe) ∧
        (∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel) := by
      cases hfr with
      | run hpes hdep => exact ⟨hpes, hdep⟩
    cases hp : ctl.proc with
    | none => exact complete_run_noproc hd hsz hp _ _
    | some p => exact complete_run hd hsz hpes hdep hp _ _ _
  | @pure_e an pe hnv2 =>
    obtain ⟨hpp, hdp⟩ : PePure pe ∧ peDepth pe ≤ lemDefaultFuel := by
      cases hfr with
      | val_pure v => rw [valueFromPexpr_val] at hnv2; cases hnv2
      | pure_op hnv' hpp hdp => exact ⟨hpp, hdp⟩
    exact complete_pure_op hd hsz hnv2 hpp hdp _ _ _
  | @load_op an loc ann ty pe2 mo hnv2 =>
    obtain ⟨hp2, hd2⟩ : PePure pe2 ∧ peDepth pe2 ≤ lemDefaultFuel := by
      cases hfr with
      | load =>
        rw [show valueFromPexpr (Pexpr [] () (PEval
          (Vobject (OVpointer _)))) = some _ from rfl] at hnv2
        cases hnv2
      | load_op hnv2' hp2 hd2 => exact ⟨hp2, hd2⟩
    exact complete_load_op hd hsz hnv2 hp2 hd2 _ _ _
  | beta_spec => exact complete_beta_spec hd hsz _ _ _ _
  | @memop an mop pes =>
    cases hfr with
    | memop_vals v1 v2 => exact complete_memop_vals hd hsz _ _ _
    | memop_op hnvF hp1 hp2 hpd1 hpd2 =>
      exact complete_memop_op hd hsz hnvF hp1 hp2 hpd1 hpd2 _ _ _
  | @store_op an loc ann ty pe2 pe3 mo hnvR =>
    obtain ⟨hp2, hp3, hpd2, hpd3⟩ :
        PePure pe2 ∧ PePure pe3 ∧
        peDepth pe2 ≤ lemDefaultFuel ∧ peDepth pe3 ≤ lemDefaultFuel := by
      cases hfr with
      | store =>
        rw [valueFromPexprs_pair, valueFromPexpr_val, valueFromPexpr_val] at hnvR
        cases hnvR
      | store_op hnv' hp2 hp3 hpd2 hpd3 => exact ⟨hp2, hp3, hpd2, hpd3⟩
    exact complete_store_op hd hsz hnvR hp2 hp3 hpd2 hpd3 _ _ _
  | beta_sym => exact complete_beta_sym hd _ _ _ _
  | wbeta_pure => exact complete_wbeta_pure hd _ _ _ _
  | wbeta_annot => exact complete_wbeta_annot hd _ _ _ _
  | beta_tuple => exact complete_beta_tuple hd hsz _ _ _ _
  | wbeta_tuple => exact complete_wbeta_tuple hd hsz _ _ _ _
  | wbeta_sym => exact complete_wbeta_sym hd _ _ _ _
  | call ra f pes =>
    obtain ⟨hpes, hdep⟩ : (∀ pe ∈ pes, PePure pe) ∧
        (∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel) := by
      cases hfr with
      | call hpes hdep => exact ⟨hpes, hdep⟩
    exact complete_call hd hsz hpes hdep _ _ _

/-- THE CLASSIFICATION THEOREM (the exhaustive sum form): every
    well-sized `Frag` configuration at a sequentially well-formed
    context with a cons-shaped env stack falls into exactly one
    `RoundClass` arm; the `step` arm is two-sided given its mirror
    step; the `refused` arm carries the shipped driver's refusal
    (`frag_round_complete`); the `open_` arm names a registered gap. -/
theorem cerberusRound_classify {M : MachineCtx} (hwf : M.SeqWF) {ctl : Ctl} (hκ : ctl.κ = [])
    {e : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {σ : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel) :
    RoundClass M (e, ev0 :: evs, ctl, σ) := by
  cases hv : toVal e with
  | some w =>
    obtain ⟨wa, -, he⟩ := ofValA_of_toVal hv
    cases wa with
    | pure a b v =>
      refine .value_done a b v he.symm ?_
      intro dst _
      rw [← he]
      exact shipped_done hwf v (ev0 :: evs) hκ dst
    | annot a a2 b ds v =>
      refine .value_annot a a2 b ds v he.symm ?_
      show CerberusRound M (e, ev0 :: evs, ctl, σ) (ofValA (.pure a2 b v), ev0 :: evs, ctl, σ)
      rw [← he]
      exact shipped_remove_annot M a a2 b ds v (ev0 :: evs) ctl σ
  | none =>
    by_cases hstep : ∃ c', Step M (e, ev0 :: evs, ctl, σ) c'
    · obtain ⟨c', hs⟩ := hstep
      exact .step c' hs (step_iff_cerberusRound hf hsz ⟨c', hs⟩)
    · rcases frag_round_complete (M := M) (ev0 := ev0) (evs := evs) (σ := σ) hf hsz hv with
          ⟨c', hs⟩ | hr | ho
      · exact absurd ⟨c', hs⟩ hstep
      · exact .refused hv (fun c' hs => hstep ⟨c', hs⟩) hr
      · exact .open_ hv (fun c' hs => hstep ⟨c', hs⟩) ho

end CerberusHeapLang
