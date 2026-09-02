# CALLS arc — read-only design spike (2026-09-02)

[AGENT] Design spike, no code. Branch `design-kill-calls` @ 0395dba. Scope:
procedures with specifications over Cerberus Core, recursive fib as the
flagship (DECISIONS 2026-08-31 "Direction: the calls arc"; 2026-09-02 "THE
DEMO IS CLASSICAL SEPARATION LOGIC OVER CORE" — procedures with specs incl.
recursion are in the demo's scope). Every file:line below is MEASURED
against the pinned generated tree at `.cerberus-ws/lean_frontend/generated/`
(one-line generated definitions: the column is given where it matters) or
the package sources; ESTIMATES are labelled. Quotes are verbatim except that
runs of whitespace in the generated one-liners are collapsed to one space.

Governing rulings: one change at a time; the genuine-driver rule; mirror
completeness as a per-constructor obligation (DECISIONS, H-1 disposition);
the downgraded substitution ruling (settled here by evidence, Q5).

## 0. Recommendation in one screen

- Call form for the demo: **`Eproc`**, not `Eccall` (§1.1, §1.4): same
  driver path as every current rule; `Eccall` (function pointers, another
  scheduler path) is the extension package's compiled-Core concern.
- **The mirror configuration grows**: a call replaces the arena and pushes
  the caller's context on `stack0`; the return pops and `apply_ctx`-plugs.
  `stack`, `proc`, `execLoc` leave `MachineCtx` for a live `Ctl` (Q1, Q3).
- **Spec form: a procedure-spec table `Π`**, twin of `Ls`; a call clause in
  `wps.pre`/`wpt.pre` beside the jump clause; `procSpecs` verifies every
  body assuming `Π`; the one Löb stays in the CPS collapse `wps_sound` (Q1,
  Q2) — RefinedC's `typed_function`/`fntbl_entry` + one `iLöb` shape (Q7).
- Recursive fib keeps today's shipped-pipeline statement shape over an
  N-procedure `prodFileOf`, with an exponential round count as `hfuel` (Q4).
- Size (ESTIMATE): one configuration refactor (~200 statements) + ~200 new
  declarations over four slices; risks Q6.

## 1. Engine facts (all MEASURED)

### 1.1 The two call forms and the redex search

Core.lean:1217 `| Eccall : a → (generic_pexpr bty sym) → (generic_pexpr bty
sym) → List (generic_pexpr bty sym) → generic_expr_ a bty sym /- C function
call -/`; Core.lean:1219 `| Eproc : a → (generic_name sym) → List
(generic_pexpr bty sym) → generic_expr_ a bty sym /- Core procedure call -/`.
`get_ctx` treats both as redexes with no descent (Core_reduction.lean:375):
`| Eccall _ _ _ _ => [(CTX, expr1)] | Eproc _ _ _ => [(CTX, expr1)]`.
`has_ccall` (Core_reduction.lean:359): `| Eccall _ _ _ _ => true | Eproc _ _
_ => false` — an `Eproc` under `Eunseq` does not set `is_unseq_with_ccall`.

### 1.2 The `Eproc` round in `step_ctx` (Core_reduction.lean:484, col ≈18083)

```
| Eproc _ ( Sym psym) pes => /- reduction: PCALL -/
  Step_with_runstate2 (RSK_eval "Eproc") ( stExceptUndef_bind
    (stExceptUndef_mapM full_eval_pexpr' pes) (fun (cvals : List (value)) => stExceptUndef_bind
      (runEU ( except_bind (call_proc core_extern1 file1 psym cvals) exception_undef_return ))
      (fun (p : (Fmap (sym) (value) ×generic_expr (core_run_annotation) (Unit) (sym))) => match p with | (proc_env, expr1) =>
        stExceptUndef_return { { { { { th_st with current_proc_opt := some psym }
          with env := proc_env :: th_st.env }
          with exec_loc := push_exec_loc psym th_st.current_loc th_st.exec_loc }
          with stack0 := Stack_cons2 th_st.current_proc_opt ctx th_st.stack0 }
          with arena := expr1 } )) )
```
(`| Eproc a ( Impl iCst) pes => …` is the implementation-constant arm —
`Step_fs2`/`process_impl_proc` — out of scope.) ONE round evaluates all
arguments AND performs the call; there is no separate operand-evaluation arm
(unlike Esave/Load, the H-1 lesson); the operand evaluator is
`full_eval_pexpr'`, the one `Erun` uses and `evalPexprs` is certified
against (Step.lean, `Step.run` docstring).

`call_proc` (Core_run.lean:93): looks `psym` up in `file1.stdlib`, then
extern-resolved in `file1.funs`, requiring `Proc _ _ bTy params body`; `if not ((List.length params) == (List.length cvals)) then fail0
(Illformed_program ("calling procedure `…' with the wrong number of args…"))
else let env1 := foldl2 (fun acc (sym1, _) cval => fmapAddBy … sym1 cval acc)
fmapEmpty params cvals; except_return (env1, body)`; unknown procedure:
`fail0 (Illformed_program ("calling an unknown procedure: " …))`. The
parameters are bound in a FRESH frame pushed on the env stack.
`push_exec_loc` (Core_run_aux.lean:380) conses `(sym1, loc1)` onto
`ELoc_normal xs` (exec_location: Core_run_aux.lean:57); never popped.

### 1.3 RETURN (Core_reduction.lean:484, col ≈1582): the value arm at a non-empty stack

```
| Stack_cons2 parent_proc_opt caller_ctx sk' => ( /- reached the end of the execution of a procedure. -/
  let tsk := match th_st.current_proc_opt with
    | some psym => (match (fmapLookupBy … psym file1.funinfo) with
        | some (_, _, ret_ty, _, _, _) => TSK_Return psym ((memValueFromValue _lemReader_tagDefs) ret_ty cval)
        | none => TSK_Misc) | none => TSK_Misc;
  /- reduction: RETURN -/
  Step_tau2 "end of procedure" tsk ( match th_st.env with
    | [] => (failwithI "end of proc, found an empty Core_run env" : thread_state)
    | _ :: env' => { { { { th_st with current_proc_opt := parent_proc_opt } with env := env' }
        with stack0 := sk' } with arena := apply_ctx caller_ctx (Expr e_annots (Epure (mk_value_pe cval))) } ))
```
Core has no return statement: the callee's arena reducing to a bare value at
`Stack_cons2` IS the return. The caller receives the value plugged into its
SAVED context (`apply_ctx caller_ctx`, the mirror's `Decomp.step_factor`
`apply_ctx`); the env stack pops one frame; `current_proc_opt` is restored
from the frame; `exec_loc` is NOT. At `Stack_empty` the value arm is
PROGRAM-DONE as today; annotated values take REMOVE-ANNOT first. Types:
`thread_state` (Core_run_aux.lean:291–296: `arena, stack0, errno, env : List
(Fmap sym value), current_proc_opt : Option sym, exec_loc, current_loc`);
`stack` (191–203: `Stack_cons2 : Option sym /- name of the current Core
procedure, if any -/ → context → stack a → stack a`; `Stack_cons` is a
`failwithI` panic in `step_ctx`); `context` (105: `CTX | Cunseq | Cwseq |
Csseq | Cannot | Cbound`).

### 1.4 The driver at a call and at a return

`can_advance` (Driver.lean:310): `| Step_ccall2 _ _ => false |
Step_with_runstate2 _ _ => true | Step_tau2 _ _ _ => true | …`. So the
`Eproc` round and the RETURN round are advanced IN PLACE by
`drive_nonmemory_steps_aux2` (Driver.lean:346) via `advance_step`
(Driver.lean:336):
```
| Step_with_runstate2 rsk step_m => nd_bind ( match rsk with
    | RSK_tau _ ( TSK_Return sym1 mval_opt) => nd_update (fun dr_st => { dr_st with trace := ME_function_return sym1 mval_opt :: dr_st.trace })
    | _ => nd_return () ) (fun () => nd_bind (liftCore_run step_m) (fun th_st' => nd_bind
    (nd_update (fun dr_st => { { dr_st with dr_step_counter := dr_st.dr_step_counter + 1 } with core_state0 := update_thread_state tid1 th_st' dr_st.core_state0 })) (fun () => nd_return NOWAKEUP )) )
```
and the `Step_tau2 debug_str tsk th_st'` arm is the same minus
`liftCore_run`. A call is ONE round, a return ONE round (plus a trace push
when `funinfo` has the procedure; `prodFile.funinfo = fmapEmpty` gives
`TSK_Misc`). Both are covered by existing iteration lemmas:
`loop_step_withrs_eval` (DriverCollapse.lean:635; premise `hm : m
dst.core_run_state0 = Result (Defined th', dst.core_run_state0)` — the call
only READS the run state through `runEU`) and `loop_step_tau`
(DriverCollapse.lean:266; to be generalized from `TSK_Misc` over `tsk`).

`liftCore_run` (Driver.lean:245): `… | Defined z => nd_return z | Undef loc1
ubs => kill (Undef0 loc1 ubs) | Error loc1 str => kill (Error0 loc1 str) |
Exception err => kill (Other (DErr_core_run err))`. `call_proc`'s two
failures (unknown procedure, arity) are TRANSPARENT KILLS `Other
(DErr_core_run (Illformed_program …))` — classifiable at the kernel, unlike
`failwithI` panics.

`Eccall` (Core_reduction.lean:484, col ≈15649) is `Step_ccall2 current_tid
(…)`: `pe` must evaluate to `Vloaded (LVspecified (OVpointer pv))`, resolved
by `CerbMem.casePtrval pv … case_funptrval (CerbMem.caseFunsymOpt mem_st
pv)` (`none → stExceptUndef_undef … [UB_CERB003_invalid_function_pointer]`),
then the same `call_proc` and thread update as `Eproc`. The driver handles
it in `process_core_step2` (Driver.lean:377): `| Step_ccall2 tid1 step_m =>
nd_bind (liftCore_run step_m) (fun th_st' => nd_bind (nd_update (…
dr_step_counter + 1 … update_thread_state …)) (fun () => driver21
with_concurrency))` — one `driver2_lemFuel` unit per call.

### 1.5 Labels across a call

`labeled` is a whole-file, procedure-keyed map installed ONCE:
`collect_labeled_continuations_NEW` (Core_aux.lean:853) folds `collect_saves
e` per `Proc _ _ _ _ e` over `fmapUnionBy … file1.stdlib file1.funs`;
`initial_core_run_state(_given)` installs it (Core_run_aux.lean:400/406);
never rebuilt. `Erun` (Core_reduction.lean:484, col ≈18997) reads it
two-level at `th_st.current_proc_opt` (`none => failwithI "Core_reduction
==> Erun outside of a proc"`), extern-resolved: `Lem_Maybe.bind0
(fmapLookupBy … proc_sym run_st.labeled) (fmapLookupBy … sym1)`. The callee's
labels come into scope purely because the call wrote `current_proc_opt`;
`MachineCtx.labels` (Step.lean:379) computes this read from `M.proc` — with
calls it is at the LIVE procedure.

### 1.6 Environment discipline

`update_env` (Core_aux.lean:868) writes the HEAD frame only (`| env1 :: xs =>
update_env_aux pat cval env1 :: xs`; `[]` panics). `lookup_env`
(Core_aux.lean:872) searches ALL frames top-down (`| env1 :: xs => match
fmapLookupBy … sym1 env1 with | none => lookup_env sym1 xs | some ret => some
ret`). The evaluator's `PEsym` arm (Core_eval.lean:145) falls back on a total
miss to `file1.funs`: a `Proc` symbol evaluates to a null `void` pointer,
anything else is `Unresolved_symbol`. Consequences in Q5.

### 1.7 Size/fuel accounting

`esize` (Soundness.lean:262) and `pot` (Potential.lean:42) give `Eproc` the
default leaf weights (1 and 2). `get_ctx` does not descend into the call, so
the per-round redex-search bound is on the CURRENT arena only: the callee
body needs its own static `pot body ≤ lemDefaultFuel`, exactly the `hQpot`
premise registered label bodies carry (`wpt_engine_boundU`,
TotalAdequacy.lean:506).

## 2. Package facts the design rests on (MEASURED)

`MachineCtx` (Step.lean:322–333) carries `stack`, `proc`, `execLoc` as
"immutable"; `MachineCtx.thread` (340) rebuilds the thread from `(e, ρ)`;
`SeqWF` (355) = `stack = Stack_empty ∧ parent = none`, documented "Permanent
for the supported fragment (procedure return is outside it)"; `primStep`
(Lang.lean:46–49) pins `q.1.M = p.1.M`. `Step M : CoreExpr × EnvStack × Mem
→ … → Prop` (Step.lean:1034). Two context disciplines today: PRESERVING
(every redex; `Decomp.step_factor`, Soundness.lean:799, first disjunct `out =
(apply_ctx ctx r', ρ', σ')`) and DISCARDING (`Step.run`, Step.lean:1298); a
call is a third, CAPTURING. Judgments: `LabelSpec` (Wps.lean:83), `wps.pre`
(116), `wps_run` (245), `wps_frame_labels` (418), `wps_seq` (748, direct Löb
over the Esseq frame), `blockSpecs`/`blockSpecs_intro` (2284/2299, no Löb),
`wps_sound` (2364, the one `iloeb`); `LabelSpecT` (Wpt.lean:77), `wpt_run`
(587), `wpt_seq` (1229), `wpt_sound` (2350). Adequacy/production: `driveU`
(Adequacy.lean:170), `engine_adequacyU` (898), `wpt_drive_aux`/
`wpt_engine_boundU` (TotalAdequacy.lean:359/506), `loop_step_frag`
(DriverCollapse.lean:1149; `hproc : th₀.current_proc_opt = some p`),
`DriverDoneAt` (ProdLoop.lean:50), `prodFile` (ProdEntry.lean:102: `funs :=
fmapAddBy … mainSym (mainDecl e) fmapEmpty`), `mainDecl` (94), `prodThread`
(244: `stack0 := Stack_empty, current_proc_opt := some mainSym, exec_loc :=
ELoc_normal [(mainSym, other "Driver.drive")]`), `prod_run_eqJ` (332),
`fib_labeledAt_production` (397), `fib_certified_production`
(ProdLoopExhibit.lean:74, `hfuel : 2 * n.toNat + 6 ≤ lemDefaultFuel`).
Configuration-shape footprint (grep, lines): `Step M (`/`Step M c`/
`CerberusRound M` 94 (Step 56, Round 16, Soundness 8, Rules 5, others 9);
`M.thread` 77 over 8 files; `M.stack`/`SeqWF` 24 over 6 files; `M.proc` 5;
package `theorem`/`lemma` declarations 951. `EnvLaws.lean`: `SymFrame`
(261), `envAdd_lookup` (280); `bindArgs` (Step.lean:716).

## 3. Design questions

### Q1. The judgment at a procedure boundary

**`MachineCtx` is single-procedure by construction**: `SeqWF.stack =
Stack_empty` is a premise of every general adequacy theorem, `proc` is
static, `primStep` pins `M`. A call writes `proc`, `stack0`, `exec_loc`
(§1.2), so `M` cannot stay pinned.

**Proposal — the live control component.** Move exactly the three written
fields into a live `Ctl`:
```lean
structure Ctl where
  κ : List (Option sym × context)   -- the Stack_cons2 chain: (caller's proc, caller's ctx)
  proc : Option sym                 -- current_proc_opt
  execLoc : exec_location           -- exec_loc (written on call, never popped)
abbrev Config := CoreExpr × EnvStack × Ctl × Mem
def MachineCtx.thread (M) (e) (ρ) (c) : thread_state :=
  { arena := e, stack0 := c.κ.foldr (fun (p, ctx) sk => Stack_cons2 p ctx sk) Stack_empty,
    errno := M.errno, env := ρ, current_proc_opt := c.proc, exec_loc := c.execLoc,
    current_loc := M.currentLoc }
```
`M` keeps `tagDefs, file, extern, tid, parent, errno, currentLoc, runState`
(unwritten on the fragment path; `current_loc` stays pinned — the README's
mover to make it live is a separate change). `SeqWF` shrinks to `parent =
none`; "empty stack, in procedure `p`" become ENTRY facts about `c₀ = ⟨[],
some p, ℓ₀⟩`. Alternative weighed — the whole `thread_state` as the live
tuple (retires `M.thread`): rejected for this arc; every Iris rule would
carry a thread record and it bundles the `current_loc` mover in.

**Labels.** `MachineCtx.labels` becomes `labelsAt M (p : Option sym)`; the
judgment is indexed by the procedure it verifies: `wps M f Ls Π Ψ e ρ` — `f`
the current procedure, `Ls` ITS label spec (`procSpecs` instantiates `Ls :=
Lsₚ f` from a table `Lsₚ : sym → LabelSpec GF`), `Π` the procedure table;
the jump clause reads `lookupLabel (labelsAt M (some f)) l`. (Keeping
`M.proc` static with an invariant `c.proc = M.proc` was weighed — less churn,
but a duplicated field with an agreement side condition; rejected.)

**Spec form and call rule.**
```lean
/-- Procedure specification table: per procedure and argument values,
    a precondition and a postcondition on the delivered value. -/
abbrev ProcSpec (GF) : Type := sym → List value → IProp GF × (value → IProp GF)

theorem wps_call {Ψ} (a : List annot) (f : sym) (pes : List (generic_pexpr Unit sym))
    {params : List (sym × core_base_type)} {body : CoreExpr} {vs : List value}
    (hf : lookupProc M.file f = some (params, body))          -- call_proc's funs read
    (hlen : params.length = vs.length)                        -- call_proc's arity check
    (hvs : evalPexprs M.tagDefs M.extern ρ pes = some vs) :
    (Π f vs).1 ∗ (∀ ret, (Π f vs).2 ret -∗ |={⊤}=> Ψ (.pure ret) ρ)
      ⊢ wps M g Ls Π Ψ (Expr a (Eproc () (Sym f) pes)) ρ
```
(`g` is the caller's procedure; the rule fires at the root redex and composes
under `Esseq` via `wps_seq`, whose continuation IS the caller's saved context
— Reynolds/O'Hearn's shape: pre, then post handed to the rest of the caller
at its own env.) Proved from a CALL CLAUSE in `wps.pre` beside the jump
clause (`callRedex? e = some (f, pes)`):
```lean
    | some (f, pes) => iprop(|={⊤}=> ∃ params body vs,
        ⌜lookupProc M.file f = some (params, body)⌝ ∗ ⌜params.length = vs.length⌝ ∗
        ⌜evalPexprs M.tagDefs M.extern ρ pes = some vs⌝ ∗
        (Π f vs).1 ∗ ▷ ∀ ret, (Π f vs).2 ret -∗ F Ψ (Expr [] (Epure (Pexpr [] () (PEval ret)))) ρ)
```
The `▷` pays for the return round; contractivity is as for the step clause.

**The procedure-verification judgment** (the twin of `blockSpecs`):
```lean
abbrev procSpecs (M) (Lsₚ : sym → LabelSpec GF) (Π : ProcSpec GF) : IProp GF :=
  iprop(∀ f params body vs (ρ : EnvStack), ⌜lookupProc M.file f = some (params, body)⌝ →
    ⌜params.length = vs.length⌝ →
    (Π f vs).1 -∗ wps M f (Lsₚ f) Π (fun w _ => (Π f vs).2 w.val) body (procEnv params vs :: ρ))
```
`procEnv params vs := foldl2 (fmapAddBy …) fmapEmpty params vs` (call_proc's
fold, verbatim); `∀ ρ` is forced by §1.6 (Q5). `procSpecs_intro` is
`blockSpecs_intro`'s twin: one proof per body, no Löb.

**The collapse** becomes CPS over the ambient control state (RefinedC's
`stmt_wp_def`, lifting.v:1002–1003, has the same shape):
```lean
theorem wps_sound : blockSpecs M f Ls Π Ψ ∗ procSpecs M Lsₚ Π ⊢
    wps M f Ls Π Ψ e ρ -∗ ∀ (c : Ctl) (Φ), ⌜c.proc = some f⌝ -∗
      (∀ w ρ', Ψ w ρ' -∗ WP ⟨ofVal w, ρ', c, M⟩ {{Φ}}) -∗ WP ⟨e, ρ, c, M⟩ {{Φ}}
```
At `c.κ = []` the value premise is `Φ`, recovering today's statement. At a
call step the Löb IH (generalized over `e ρ c Φ`) is applied to the callee
body at `⟨body, procEnv :: ρ, push c, M⟩`; a value at `push c` is NOT a
Language value (`toValRt` requires `c.κ = []`), its only step is `Step.ret`
to `⟨apply_ctx ctx (pure w), ρ'.tail, c, M⟩`, and the call clause supplies
the rest. Required lemma `Step.env_tail_eq`: every non-call/return step
preserves `ρ.tail` (§1.6; every current rule binds through `update_env`).

**Total judgment.** `ProcSpecT GF := sym → Nat → List value → IProp GF ×
(value → IProp GF)` carries the callee's budget `m` (the `LabelSpecT`
precedent). Call clause at budget `k`: `∃ m k', ⌜1 + m + 1 + k' ≤ k⌝ ∗ (Π f
m vs).1 ∗ ∀ ret, (Π f m vs).2 ret -∗ wpt M g Ls Π k' Ψ (pure ret) ρ` (call
round + callee budget + return round + continuation); `wpt` is defined by
strong recursion on `k` (the continuation sits at `k' < k`); `procSpecsT`
verifies each body at its own `m`. Budgets are additive across calls (Q4).

### Q2. Recursion

(a) Löb per exhibit — `iloeb` on `wps … fibBody` assuming a later-guarded
spec for the recursive call. (b) Spec table — assume `Π` for ALL procedures
while verifying each body (`procSpecs`), Löb only in `wps_sound`. Choice:
**(b)**: the classical form (Hoare's rule for recursive procedures; the
package's `goto` treatment), the engine's referent (`call_proc` is a pure
file lookup), and RefinedC's shape:
`typed_function` is `Persistent` (function.v:67), `function_ptr_type` owns
`fntbl_entry f fn ∗ ▷ typed_function fn fp` (function.v:106–109), and the
recursive knot is tied ONCE by `iLöb` over the conjunction of every
function's `typed_function` (tutorial/adequacy/adequacy.v:108–128: `iAssert
(typed_function … ∗ … ) … iLöb as "IH" … adequacy_solve_typed_function
type_…`) — where our `wps_sound` Löb sits. (a) would put a `▷` in every
recursive exhibit's spec and does not scale to mutual recursion.

### Q3. The mirror and its certification

New mirror rules (Step.lean), mirroring §1.2–1.3 line for line:
```lean
| call {a} {f pes params body vs} {ρ : EnvStack} {c : Ctl} {ctx : context} {σ}
    (hd : Decomp e ctx (Expr a (Eproc () (Sym f) pes)))     -- get_ctx: [(CTX, expr1)] under the spine
    (hvs : evalPexprs M.tagDefs M.extern ρ pes = some vs)
    (hf : lookupProc M.file f = some (params, body)) (hlen : params.length = vs.length) :
    Step M (e, ρ, c, σ)
         (body, procEnv params vs :: ρ,
          ⟨(c.proc, ctx) :: c.κ, some f, push_exec_loc f M.currentLoc c.execLoc⟩, σ)
| ret {w : value} {a} {ev0 evs} {p ctx κ} {q : Option sym} {ℓ} {σ} :
    Step M (Expr a (Epure (Pexpr [] () (PEval w))), ev0 :: evs, ⟨(p, ctx) :: κ, q, ℓ⟩, σ)
         (apply_ctx ctx (Expr a (Epure (mk_value_pe w))), evs, ⟨κ, p, ℓ⟩, σ)
```
Every existing rule threads `c` unchanged. `Decomp.step_factor` gains a
third disjunct (call). The `sseq_ctx`/`wseq_ctx`/`annot_ctx` congruences stay
guarded by `jumpRedex? e1 = none` only — a call under a frame IS a step of
the framed term (the frame is captured in `ctx`); `Language.Context` remains
absent for today's reason. `Frag` gains `call (hdep : ∀ pe ∈ pes, peDepth pe
≤ lemDefaultFuel) : Frag (procRedex f pes)` and `Redex.call`; callee bodies'
`Frag`/`pot` bounds are per-procedure static premises `hPf`/`hPpot` over
`lookupProc M.file`, twins of `hQf`/`hQpot`.

Certification: `step_ctx_call` — `step_ctx … (M.thread e ρ c) =
[Step_with_runstate2 (RSK_eval "Eproc") m]` with `m rs = Result (Defined
(M.thread body … (push …)), rs)`; `step_ctx_ret` — `[Step_tau2 "end of
procedure" tsk (M.thread (apply_ctx …) evs ⟨κ, p, ℓ⟩)]`. Both feed the
existing iteration lemmas (`loop_step_withrs_eval`, `loop_step_tau` over
`tsk`), so `loop_step_frag`'s conclusion shape is UNCHANGED
(`update_thread_state 0 (M.thread e' ρ' c') …`; run state, trace and counter
existential): the round's writes to `current_proc_opt`, env and stack all
sit inside the single thread record the equation already writes.
`engine_step_matchU` is restated over `Config` with `M.thread e' ρ' c'`.

Completeness classification at a call: (i) unknown procedure → singleton
`kill (Other (DErr_core_run (Illformed_program …)))` (§1.4, transparent);
(ii) arity mismatch → same channel; (iii) argument evaluation failure → the
evaluator's channels as for `Erun` (`Undef` → kill; `failwithI` opaque); (iv)
`Eproc (Impl _)` → outside the fragment. RETURN's one refusal (`env = []`,
`failwithI`) is unreachable: invariant `ρ.length = 1 + c.κ.length`.

### Q4. The production statement

`prodFile` becomes `prodFileOf (procs : List (sym × List (sym ×
core_base_type) × CoreExpr)) (main : CoreExpr)`: `funs` = `mainDecl main`
plus `Proc CerbLocation.unknown none bty params body` per entry, `funinfo :=
fmapEmpty` (returns are `TSK_Misc`). `collect_labeled_continuations_NEW`
yields one fiber per `Proc`; the tie becomes `LabeledAt rs f (Q f)` per
procedure, derived by computation as `fib_labeledAt_production` is.
`prod_run_eqJ` takes the per-procedure ties and the entry control `⟨[], some
mainSym, ELoc_normal [(mainSym, other "Driver.drive")]⟩` (= `prodThread`);
`DriverDoneAt`'s final thread has `stack0 = Stack_empty` — the last return
pops to `κ = []`, as `finalize_done` requires. Recursive fib:
```lean
theorem fib_rec_certified_production (sup : Nat) (n : Int) (hn : 0 ≤ n) (btys…)
    (hfuel : fibRounds n.toNat + 2 ≤ lemDefaultFuel) (fs : CerbFS.FsState) (args : List String) :
    ∃ dres dst', CerbND.runND (_root_.drive fmapEmpty false (prodFileOf [fibProc …] (mainCall n)) args)
        ((initial_driver_state sup (prodFileOf …) fs).1) = [(nd_status.Active dres, [], dst')] ∧
      dres.dres_core_value = ivVal (fibSpec n.toNat) ∧ dres.dres_blocked = false ∧ …
```
Budget (ESTIMATE, pinned by the exhibit): body `if n < 2 then pure(n) else
let x = fib(n−1) in let y = fib(n−2) in pure(x+y)` costs per activation ≈ 1
(guard) + 2×(call + return) + 3 (two binding betas, exit evaluation) ≈ 9
rounds plus the two recursive activations: `fibRounds(n) = fibRounds(n−1) +
fibRounds(n−2) + 9` for `n ≥ 2`, so `fibRounds n ≤ 9·fibSpec(n+2)`; with
`lemDefaultFuel = 10^6`, `n ≤ 25` (`fibSpec 27 = 196418`) is in budget. The
total lane sets `ProcSpecT`'s `m := fibRounds n` with the additive clause.

### Q5. Argument passing (the downgraded ruling, settled by evidence)

Measured: (1) `call_proc` binds the parameters into a FRESH frame by
`foldl2 (fmapAddBy …) fmapEmpty params cvals` — a `SymFrame`, so parameter
reads come from `envAdd_lookup`, no frame-shape pins; (2) the frame is PUSHED
(`env := proc_env :: th_st.env`), the caller's frames below untouched since
`update_env` writes only the head (§1.6); (3) RETURN pops exactly one frame
(`_ :: env' => env := env'`), so the caller's env is restored VERBATIM — a
theorem (`Step.env_tail_eq` + the pop), not an assumption; (4) `lookup_env`
searches all frames, so an unbound symbol would read the caller's variables
or fall back to `file.funs`. Hence `procSpecs` quantifies ALL tails `ρ`; a
body whose free symbols are its parameters/locals never reaches the tail —
no closedness side condition in the logic. `EnvLaws` grows by
`procEnv_symFrame` and `lookup_env_cons_of_mem`. Substitution appears
nowhere: the forcing fact is `call_proc`'s env fold.

### Q6. Risks, size, slicing (ESTIMATES unless marked)

Modules touched: Step, Soundness, Round, Lang, Wps, Wpt, Rules, Adequacy,
TotalAdequacy, DriverCollapse, ProdLoop, ProdEntry, EnvLaws, API, Audit; new
`FibRecExhibit.lean`. Slices, one change each:
1. **C1 — configuration generalization** (internals refactor with a declared
   statement-surface change: `Config`/`MachineCtx`/`M.thread` types). `Ctl`,
   `M.thread e ρ c`, `labelsAt`, `SeqWF` → entry facts, every rule threaded
   with `c` unchanged, `toValRt` at `κ = []`, `engine_step_matchU`/
   `loop_step_frag`/`driveU` restated. No new rules. Signature snapshot
   pre/post committed; the diff must be exactly the type change. ~200
   statement edits (measured footprint §2: 94 + 77 + 24 + 5 lines), ~25 new
   small lemmas.
2. **C2 — mirror + certification** (spec addition): `Step.call`/`Step.ret`,
   `Frag.call`, `Redex.call`, `Decomp.step_factor` third disjunct,
   `step_ctx_call`/`_ret`, `loop_step_tau` over `tsk`, `Step.env_tail_eq`,
   completeness rows (i)–(ii) as KILL facts. ~50 declarations.
3. **C3 — judgment + rules** (spec addition): `ProcSpec(T)`, call clauses,
   `wps_call`/`wpt_call`, `procSpecs(T)_intro`, CPS `wps_sound`/`wpt_sound`,
   `wps_seq`/`wpt_seq` call case, frame twin, premises `hPf`/`hPpot`,
   `wpt_drive_aux` accounting, `prodFileOf` + per-procedure `LabeledAt`. ~80.
4. **C4 — the exhibit**: recursive fib partial (PROVISIONAL over `driveU`),
   total (`fibRounds`), production. ~50. Later: even/odd mutual recursion.

Top risks: (R1) C1 re-elaborates Soundness.lean (4436 lines) and Step.lean
(2186) wholesale — the grind tripwire is real; mitigate by mechanical
threading (no proof changes), capped per-module builds. (R2) The CPS
collapse and the `wps_seq`/`wpt_seq` inductions (the largest proofs) gain a
case each; a wrong `Ctl` (e.g. omitting `execLoc`, so `M.thread` cannot be
exact) means redoing C1. (R3) The total budget is exponential; `hfuel` must
be stated on every surface. (R4) `Eccall` stays out; compiled C in the demo
would reopen `process_core_step2` and memory-model function pointers.

Pre-registered criteria ([AGENT], proposed): fib's body proof uses `wps_call`
twice, no `iloeb`/`Step` constructor/drive chain; `wps_sound` at `c.κ = []`
is definitionally today's; `loop_step_frag`'s shape survives C2; rows
(i)/(ii) are KILL facts. Any failure: park and re-adjudicate before C3.

### Q7. RefinedC alignment

RefinedC (measured) ↔ proposal: `fn_params = {fp_atys, fp_Pa, fp_rtype,
fp_fr : rtype → fn_ret{fr_rty, fr_R}}` (function.v:42–51) ↔ `Π f vs = (Pre,
Post)` with the return variable existential inside `Post`; `typed_function
fn fp := ∀ x, ⌜layouts⌝ ∗ □ ∀ lsa lsv, Qinit -∗ introduce_typed_stmt fn (lsa
++ lsv) (fn_ret_prop …)` (function.v:59–65) ↔ a `procSpecs` entry;
`typed_call v P vl tys T := P -∗ ([∗ list] v;ty∈vl;tys, v ◁ᵥ ty) -∗
typed_val_expr (Call v (Val <$> vl)) T` (programs.v:117) and
`type_call_fnptr` (function.v:131–137) ↔ `wps_call`; `fntbl_entry`
(caesium/ghost_state.v:120–124, persistent `ghost_map` element) ↔ the pure
`lookupProc M.file f = some …`; `wp_call` (lifting.v:1046) ↔ `Step.call` +
the collapse case; `stmt_wp_def` CPS (lifting.v:1002) ↔ CPS `wps_sound`; the
single `iLöb` (tutorial adequacy.v:128; `tac_typed_single_block_rec`,
automation.v:119–127) ↔ the collapse Löb. Decision points for the literal
port: (D1) spec table as a PARAMETER vs an Iris-persistent assertion —
`Eproc` names a file symbol, so a parameter is the honest referent; the
persistent form is a wrapper (`□ ∀ vs, Pre -∗ wps …`) added when function
pointers (`Eccall`, `caseFunsymOpt`) arrive. (D2) Arguments as VALUES in an
env frame vs RefinedC's argument LOCATIONS `lsa` — forcing fact `call_proc`'s
fold; address-taken locals are `create`d in compiled Core, so `lsa` is the
compiled-Core shape. (D3) Return: Caesium's `Return v` + `fn_ret_prop`'s
`‖={⊤}=‖ ∃ x, …` vs body-value delivery — same content, the post applied at
the RETURN step's `▷`. (D4) Labels: RefinedC substitutes locations for names
(`introduce_typed_stmt`, function.v:5–8); we bind in the env — the settled
downgrade; `Lsₚ f` is their per-function `Q`.
