# While-lang growth readiness review (2026-08-31)

[AGENT] Growth-readiness review, dispatched on operator order: the demo
is to be extended with "all the while-lang structure (enough we can
write some simple example like 'fib' or list reverse in core and verify
it)". This document derives the gap analysis independently from the
sources: the cerberus-heaplang modules on this branch, the pinned
engine (`.cerberus-ws/lean_frontend/generated/`, pin per
`scripts/semantics-pin.env`), the RefinedC donor
(`deps/refinedc/theories/caesium/lifting.v`, read-only), and the
cerberus OCaml driver executed on tiny C programs
(`--nolibc [--sequentialise] --pp=core`; transcripts quoted below were
produced 2026-08-31 from `/tmp` scratch; the two C sources are inlined
in §2.1 so the derivation is reproducible).

Verdict up front: the architecture (mirror Step → Iris logic →
per-rule engine certification → production export) EXTENDS to the
while-lang goal, but four things change form and must be re-decided
before the arc, not during it: (R1) `Erun` discards its evaluation
context, which falsifies the `Language.Context`/wp_bind route for
sequencing; (R2) the environment becomes live state, which restates
every existing rule; (R3) the `esize e₀ + n ≤ lemDefaultFuel` fuel
side condition and the `hterm` in-budget termination hypothesis are
untenable under loops in their current shapes; (R4) elaborated-C Core
(as opposed to authored Core) breaks the ND-singleton/production-run
equation and the run-state-verbatim discharge partition. R4 is
avoidable by scoping the arc to AUTHORED Core programs (which is what
the operator's phrasing "write ... in core" licenses); R1–R3 are not
avoidable and are the headline findings.

---

## 1. Current support inventory (from sources, not docs claims)

### 1.1 The mirror step relation (`CerberusHeapLang/Step.lean`)

`Step : CoreExpr × Mem → CoreExpr × Mem → Prop`, eight rules:

| rule | shape | notes |
|---|---|---|
| `store` | positive `Store0`, canonical `PEval` operands | fused request+discharge via `applyMemM (storeM …)`; result `{DA_pos [] fp}unit` |
| `load` | positive `Load0`, canonical operands | fused via `loadM` |
| `create` | positive `Create`, canonical operands | fused via `allocateObject 0 … none none`; bare pointer result |
| `sseq_pure` | `lets _ = v in E2 → E2` | WILDCARD pattern only (`CaseBase (none, bty)`) |
| `sseq_annot` | `lets _ = {A}v in E2 → {A}E2` | wildcard only |
| `sseq_ctx` | congruence under `Esseq` e1 | |
| `annot_ctx` | congruence under `Eannot` (guarded `annotRooted b = false`) | |
| `annot_merge` | `{A}{B}E → {A++B}E` | |

Frozen context (Step.lean header + `Soundness.lean` §frozen):
tagDefs = extern = `fmapEmpty`, default file, tid 0, no parent,
`env = [fmapEmpty]` (wildcard patterns keep it frozen — `update_env`
identity, Core_aux.lean:861), `spikeRunState` with `labeled =
fmapEmpty`, `spikeThread` with `current_proc_opt := none`,
`stack0 := Stack_empty`. Actions are positive-only, non-library
locations, canonical `[]` node-annotation lists.

### 1.2 Certification status (`Soundness.lean`)

- `FragP` — the fragment cone: bare pure values, the three canonical
  actions, wildcard `Esseq`, `Eannot`. Closed under Step
  (`FragP.step`).
- `Decomp e ctx r` — mirror of `get_ctx` (fuelled), with per-layer
  matcher facts; `Decomp.get_ctx_default` needs `esize e ≤
  lemDefaultFuel` (fuel honesty: get_ctx's exhaustion leaf is the
  opaque `fuelExhausted`).
- Per-rule context-undisturbed engine equations (`step_ctx_done`,
  `step_ctx_remove_annot`, `step_ctx_store[_illtyped]`,
  `step_ctx_load`, `step_ctx_create`, `step_ctx_beta_pure/annot`,
  `step_ctx_merge`) with the [USER 2026-08-30] three-way partition
  (untouched-unread / read-only-under-WF / touched) per component.
- `dischargeStep` — the Driver.lean:273 protocol projected to
  `(thread_state, MemState)`. Covers EXACTLY four `core_step2`
  forms: `Step_tau2`, `Step_done2`, `Step_error2`, and
  `Step_action_request2` whose request is
  Store/Load/CreateRequest2. Everything else — including
  `Step_with_runstate2`, `Step_memop_request2`, `Step_nd2`,
  `KillRequest2`, `AllocRequest2` — is `offFragment` (a refusal).
- `engine_complete` — at every `FragP` configuration within the
  esize budget, the engine's outcome list is a SINGLETON matched by
  Step (step / the D1 remove-annot+done value protocol / a refusal
  at a provably Step-stuck configuration).

### 1.3 The rule set (`Rules.lean`, `Lang.lean`)

- `Language CoreExpr Mem Empty SpikeVal` instance; state is the
  MemState ONLY. One `Language.Context` instance: the `Csseq` frame
  (`instContextSseq`) — this is what gives `wp_bind` for real
  strong sequencing. The Eannot frame is deliberately NOT a Context
  (merge races descent); it is handled by the Löb-proved commuting
  lemmas `wp_annot_reindex` / `wp_annot`.
- Small axioms `wp_store` (full ownership) and `wp_load` (any
  fraction, `cellLoadTrap = false` premise), both UB-excluding, both
  with exact-annotation postconditions
  (`⌜w = SpikeVal.annot [DA_pos [] fp] …⌝`).
- NO `wp_create` — registered design finding (slice-B D26, restated
  in ProdEntry.lean header): `allocateObject` kills ("out of
  memory", CerbMem.lean:1477 `alignedAddr == 0`) from
  configurations cell ownership does not constrain; a sound
  `wp_create` needs an allocator-cursor resource in the state
  interpretation. Cold-start programs run creates on the
  production-pinned initial memory instead, where success is a
  theorem.
- `wp_sseq` (wildcard): `wp_bind` through `instContextSseq` + the
  two betas as `wp_lift_pure_det_step_no_fork` + `wp_annot`.
- `triple_frame`, `triple_conseq`, `triple_seq`, `spike_wp_wand`;
  the exhibits (store/frame; sequential disjoint stores).

### 1.4 The value protocol (`SpikeVal`)

`SpikeVal ::= pure v | annot ds v` — mirror of `is_irreducible`'s
two value shapes (Core_reduction.lean:293), with `merge` mirroring
the ANNOTS `(++)`. Recorded divergence D1: the engine's top-level
`{A}v → v` tau is composed into the readout
(`EngineMatch.removeAnnot` + `SpikeVal.val` erasure), not into Step.

### 1.5 Exported statement shapes (`Adequacy.lean`, `ProdEntry.lean`)

- `SemTriple e P post` (engine vocabulary only): ∀ frame cell-map
  `R` with `P ##ₘ R`, ∀ σ with `Sat σ (P ∪ R)`, ∀ fuel `n` and
  action-id supply, **hypothesis `esize e + n ≤ lemDefaultFuel`** →
  drive never kills, never derails, and any delivered `(v, σ')`
  splits as `Q ∪ R` with `post v Q`, the SAME `R` verbatim.
  Termination is NOT claimed (`.more` unconstrained).
- `ProvenTriple` — the only WP-mentioning definition in the export;
  `semantic_triple_sound : ProvenTriple → SemTriple` (via
  `spike_engine_adequacy` ← `spike_step_adequacy` ←
  `wp_strong_adequacy_gen` with in-proof `SpikeGS` construction);
  `semantic_frame` moves a named frame across.
- `prod_run_eq` / `sem_triple_prod` (ProdEntry.lean): the SHIPPED
  pipeline `CerbND.runND (Driver.drive …) (initial_driver_state …)`
  on a synthetic one-`main` file equals EXACTLY ONE `Active`
  execution. Hypotheses to scrutinize under loops:
  `hterm : ∀ aids, drive aids k … = .done v σfin` (a CONCRETE step
  count `k`), `hfuel : esize e + k + 2 ≤ lemDefaultFuel`, and (for
  `sem_triple_prod`) the prefix-collapse equation `hpre`.

### 1.6 Audit boundary (`Audit.lean`, restructure notes)

285 theorems; exact cones: classical trio everywhere, plus the one
declared temporal boundary `runEffectful` module-scoped to
`ProdEntry`/`ProdExhibit` (enters through `initial_driver_state`'s
effectful `sym_supply` seam in the STATEMENTS). Boundary gate
plant-tested both directions. Nothing in the growth below adds an
axiom; new engine surface (label maps, memops, kill) is ordinary
generated code.

---

## 2. The target, derived

### 2.1 What the driver says a loop is

Sources elaborated (both transcripts on this checkout, oracle
`--nolibc --pp=core`, and again with `--sequentialise`):

```c
/* fib.c */
int main(void) {
  int a = 0; int b = 1; int n = 10;
  while (n > 0) { int t = a + b; a = b; b = t; n = n - 1; }
  return a;
}
/* listrev.c */
struct node { struct node *next; int val; };
struct node *rev(struct node *p) {
  struct node *q = 0;
  while (p != 0) {
    struct node *t = p->next; p->next = q; q = p; p = t;
  }
  return q;
}
```

Key shapes in the elaborated Core (fib, abridged — verbatim lines):

```
save while_515: unit (a: pointer:= a, b: pointer:= b, n: pointer:= n) in
  let strong a_520: loaded integer = bound( …guard… ) in
  let strong a_516: boolean = case a_520 of … end in
  if a_516 then
    let strong t: pointer = create(…) in
    …body stores/loads…
    kill('signed int', t) ;
    save continue_513: unit (…) in pure(Unit) ;
    run while_515(a, b, n)
  else pure(Unit) ;
save break_514: unit (…) in pure(Unit) ;
… load a … ; kill a,b,n ; run ret_512(conv_loaded_int(…)) ; …dead kills… ;
save ret_512: loaded integer (a_557: loaded integer:= Specified(0)) in
  pure(a_557)
```

Findings a paper analysis would miss, each verified against the
generated engine sources:

1. **The loop is `Esave`/`Erun` with parameters, and `run` is a
   context-DISCARDING jump.** step_ctx's `Erun` arm
   (Core_reduction.lean:484) evaluates the argument pexprs
   (`full_eval_pexpr'` each), folds `update_env (mk_sym_pat …)` over
   them, and returns `{th_st with env := env', arena := cont_expr}` —
   **no `apply_ctx ctx`**. The surrounding evaluation context
   (including any live `Esseq` continuation — see the dead
   `kill`s after `run ret_512` above, and `run while_515` sitting
   under the whole `save … ; save break … ; …` sseq spine) is thrown
   away.
2. **Why that is correct: label continuations are collected
   sseq-extended.** `collect_labeled_continuations_NEW` →
   `m_collect_saves_aux` (Core_aux.lean:853, 843): a save found in
   `e1` of `Esseq pat e1 e2` is registered with body
   `Expr annots (Esseq pat body e2)` — i.e. the registered
   continuation of `while_515` is the save body PLUS the entire rest
   of the procedure. The label map lives in
   `core_run_state.labeled`, is populated once at
   `initial_core_run_state` (Core_run_aux.lean:395 — already
   exercised by ProdEntry's `prodPostGlobals`), and is never written
   afterwards on the sequential path — a static per-procedure block
   map, exactly Caesium's `f_code`.
3. **`Erun` reads thread/run context the frozen demo context zeroes
   out**: `current_proc_opt` must be `some` (else `failwithI`),
   `extern` is consulted for the proc symbol, and the
   `labeled` lookup must succeed (else `failwithI "Erun couldn't
   resolve label"`). `spikeThread` has `current_proc_opt := none`
   and `spikeRunState.labeled = fmapEmpty` — the frozen context
   itself must change.
4. **`Eif` is a single engine step with a BIG-STEP guard.**
   one_step0's Eif arm (Core_reduction.lean:353) emits
   `TAU_WITH_RUNSTATE` whose monad runs `full_eval_pexpr1 pe1` (the
   fuelled full evaluator, its exhaustion leaf an `Undef`-shaped
   `fuelExhausted`) and dispatches on `Vtrue`/`Vfalse`; any other
   value is `failwithI` — a PANIC channel (total default value in
   Lean), NOT a refusal. Surfaces as `Step_with_runstate2` — a
   core_step2 form the discharge mirror currently maps to
   `offFragment`.
5. **`Ecase` is small-step in the scrutinee, substitution-based in
   the branch.** Value scrutinee: `select_case subst_sym_expr cval
   pat_es` → TAU into the SUBSTITUTED branch (or ILLTYPED refusal on
   no match). Non-value scrutinee: one `eval_pexpr1` step per engine
   step (EVAL arm) — different granularity from Eif's guard.
6. **Bindings are env-based and unavoidable.** Non-wildcard
   `Esseq`/`Elet` betas call `update_env pat cval env` (TAU carries
   the new env); `Esave` entry folds parameter bindings into env;
   `Erun` rebinds; pexpr evaluation resolves `PEsym` against
   `th_st.env`. There is no way to name an action's result except an
   `Esseq` binding pattern, so ANY loop program makes the
   environment live state. Env frames are per-procedure (pushed by
   calls, popped by RETURN); within a procedure the head frame grows
   monotonically.
7. **Action operands in real programs are not canonical values.**
   `store('signed int', a, conv_loaded_int(…))` has `PEsym`/`PEcall`
   operands: step_action first takes an `ACTION_EVAL` step (one
   engine step full-evaluating ALL operands, rebuilding the action
   with `mk_value_pe`), and only the NEXT step issues the request.
   The current Step/FragP action rules accept only `PEval` operand
   shapes — insufficient for any program with variables.
8. **Elaborated-only surface** (absent from authored Core, present
   in every elaborated program): `Ewseq` everywhere (even
   `--sequentialise` keeps `let weak`), `Eunseq` (removed by
   `--sequentialise`), **negative actions** (`neg(store …)` for
   every C assignment, NOT removed by `--sequentialise`), `Ebound`
   around every full-expression, `nd(…)` in Unspecified-guard
   branches (unreachable under Specified preconditions), stdlib
   `PEcall`s (`conv_int`, `catch_exceptional_condition_add`, …)
   which need the real `file.stdlib`, and `undef(<<UB036…>>)`
   leaves in untaken case branches.
9. **listrev additionally needs**: `memop(PtrNe, …)` — an `Ememop`,
   surfacing as `Step_memop_request2` (another undischargeable form
   today) with the memory model deciding pointer inequality;
   `member_shift` (`PEmember_shift`) which reads tagDefs for struct
   layout; struct-typed allocations with loads/stores at MEMBER
   type at interior offsets — sub-allocation footprints, which the
   allocation-rooted cell granularity cannot express (registered
   growth step in Heap.lean's header); pointer-typed cells
   (`'struct node*'` cells holding `Specified(NULL)`/pointers, so
   decode/encode lemmas for pointer memvalues); `kill` (KillRequest2
   → `killM`) at scope exits — including the C-shaped need to
   consume a points-to (ghost deletion).
10. **ND is NOT singleton on elaborated Core.** `unseq(load(a),
    load(b))` (fib's `a + b`) has two reducible components →
    `get_ctx_unseq` yields a two-element decomposition list → the
    step list has two entries → the production driver `pick`s
    (Driver.lean:355 `new_drive_core_threads`; `Step_nd2` also
    `pick`s). `runND`'s result is then not a singleton list.
    `--sequentialise` removes `unseq` but not negative stores; the
    Neg0 path (step_ctx) performs `break_at_bound_and_sseq` context
    surgery, introduces `Eexcluded` nodes, and DRAWS
    `fresh_excluded_id`/`fresh_symbol0` — i.e. it WRITES
    `core_run_state` (excluded_supply, sym_supply), breaking the
    "request monad returns the run state verbatim" discharge
    invariant.
11. **`Ebound` discards annotations**: REMOVE-BOUND
    (`bound({A}v) → v`, step_ctx) drops the dyn-annotation payload
    entirely at bound boundaries.

### 2.2 The two target lanes

**Lane T1 — AUTHORED Core fib and list-reverse** (what "write some
simple example … in core" needs, and the recommended arc scope).
Authored programs can use positive actions, `Esseq` (no
`Ewseq`/`Eunseq`/`Ebound`/`neg`), direct `PEop` arithmetic (Core
integers are mathematical — no stdlib, no overflow machinery), and a
no-struct list encoding. Concrete authored fib (AST shapes; `x:τ`
abbreviates `Pattern [] (CaseBase (some x, τ))`):

```
lets a:pointer  = create(align int, int) in
lets b:pointer  = create(align int, int) in
lets n:pointer  = create(align int, int) in
lets _ = store(int, sym a, Specified 0) in       -- operand PEsym: needs the
lets _ = store(int, sym b, Specified 1) in       -- ACTION_EVAL pre-step rule
lets _ = store(int, sym n, Specified 10) in
save loop: unit () in                            -- no params: a,b,n are in env
  lets xl:loaded integer = load(int, sym n) in
  case (sym xl) of
  | Specified(x:integer) =>
      if (sym x > val 0) then                    -- Eif, PEop guard → Vtrue/Vfalse
        lets al = load(int, sym a) in case … Specified(av) =>
        lets bl = load(int, sym b) in case … Specified(bv) =>
        lets _ = store(int, sym b, Specified(sym av + sym bv)) in
        lets _ = store(int, sym a, Specified(sym bv)) in
        lets _ = store(int, sym n, Specified(sym x - val 1)) in
        run loop()                               -- the back-edge
      else pure(Unit)
  | Unspecified(_) => pure(Unit)   -- dead under the precondition
;                                  -- ← the save's sseq continuation:
lets rl = load(int, sym a) in
lets _ = kill(int, sym a) in lets _ = kill(int, sym b) in
lets _ = kill(int, sym n) in
pure(sym rl)
```

(No temp cell `t` is needed: authored code carries `av`/`bv` in the
environment. The elaborated version allocates `t` INSIDE the loop —
see the wp_create consequence in §3.)

Authored list-reverse, no-struct encoding: a cons cell = two
independent allocations (`vcell : int`, `ncell : 'signed int*'` —
or any pointer ctype) with `next` pointing at the next pair's
`ncell`; null test via `memop(PtrNe, sym p, PEval(NULL ty))`;
`isList p [v₁…vₖ]` the standard recursive predicate. The C-struct
version is lane T2.

Exact construct/evaluation-form requirements:

| needed by | constructs / forms |
|---|---|
| both | `Esseq` with BINDING patterns (env update); `Eif` with big-step guard eval; `Ecase` + `select_case`/`subst_sym_expr` (Specified/Unspecified unwrap, tuple patterns); `Esave` entry (param binding); `Erun` (label lookup, arg eval, context discard); action-operand `ACTION_EVAL` pre-steps; pexpr evaluation: `PEsym`, `PEval`, `PEop` (arith + comparison → `Vtrue/Vfalse`), `PEctor` (`Cspecified`, `Ctuple`); `create` at the WP level if allocation occurs mid-program; `kill` (+ ghost deletion); non-empty `labeled` map + `current_proc_opt = some` in the frozen context |
| fib only | integer cells only (already supported at cell level) |
| list-reverse | pointer-typed cells (pointer encode/decode `StorableAt`/`decodeCell` facts); `Ememop` `PtrNe`/`PtrEq` (+ `Step_memop_request2` discharge; UB-exclusion premises for the provenance kill arms); `isList` representation predicate |
| T2 (elaborated C) additionally | `Ewseq` (+ tuple-pattern betas); `Eunseq` (+ multi-decomposition ND); negative actions (`Ebound`, `break_at_bound_and_sseq`, `Eexcluded`, run-state counter ticks, `do_race`/exclusion bookkeeping); `Ebound` + REMOVE-BOUND (annotation-discarding); stdlib `PEcall` resolution (real `file.stdlib`); `PEif`/`PElet`/`PEcase`/`PEundef` inside guards (interior to `full_eval` — free); struct tagDefs + `member_shift` + sub-allocation cell granularity; proc calls (`Eproc`, stack push/pop, RETURN) if `rev` is a real procedure |

---

## 3. Extension vs rework, per item

Legend: EXTEND = add rules + certification cases + WP lemmas in the
existing pattern, no new qualifiers on existing exports. REWORK =
something existing changes form. Every REWORK is a headline.

### R1 (REWORK, headline): `Erun` kills the wp_bind route for sequencing

The engine's jump replaces the WHOLE arena, discarding the
decomposition context (§2.1 items 1–2). Consequences, in order:

- The mirror Step cannot express `run` as a local rule of the redex:
  a local `Erun → cont` rule plus `sseq_ctx` would derive
  `K[run l] → K[cont]`, but the engine does `K[run l] → cont`. The
  rule must be GLOBAL: `Decomp e ctx (Erun-redex) → Step (e,σ) (cont…)`.
- With that global rule in Step, `instContextSseq` is FALSE:
  `primStep_fill` (a step of `e1` lifts to a step of
  `Esseq pat e1 e2`) fails when `e1`'s step is a jump (both sides
  step, but to different terms), and `primStep_fill_inv` fails
  symmetrically. iris-lean's `Language.Context` is unconditional in
  the hole, so the instance cannot be kept, and `wp_bind` — the
  current backbone of `wp_sseq`/`triple_seq` — is gone for Esseq.
- The legitimate fix is the donor's statement stratification,
  adapted. Caesium (lifting.v): `stmt_wp_def E Q Ψ s := ∀ Φ rf,
  ⌜Q = rf.(rf_fn).(f_code)⌝ -∗ (∀ v, Ψ v -∗ WP …Return v…{{Φ}}) -∗
  WP to_rtstmt rf s {{Φ}}` (lifting.v:1002); `wps_goto`
  (:1112): `Q !! b = Some s → ▷ WPs s {{Q,Ψ}} -∗ WPs (Goto b)`;
  `wps_block P b Q Ψ := □(P -∗ WPs Goto b {{Q,Ψ}})` and
  `wps_block_rec` (:1306-1319): a ∗-map of block invariants proved
  mutually under □, discharged by ONE `iLöb` + `wps_goto`'s later.
  Port shape here: a derived statement-level WP over Core
  configurations, indexed by the STATIC label map (the analogue of
  `⌜Q = rf.f_code⌝` is a pure hypothesis equating the index with
  the frozen/production `core_run_state.labeled` for the current
  proc — legitimate because nothing writes `labeled` on the
  positive sequential path); `wp_run` mirrors `wps_goto` (label
  lookup premise + ▷); the loop rule is `wps_block_rec` verbatim
  (Löb is already house practice — `wp_annot` is Löb-proved).
- Sequencing WITHOUT `Language.Context`: the engine gives the exact
  fact that makes a direct proof go through — a jump's successor is
  context-INDEPENDENT. So the jump case of a hand-proved
  `wps_sseq` unfolds `e1`'s WP one step: both `e1` and
  `Esseq pat e1 e2` step to the SAME configuration `cont`, and the
  WP transfers. The non-jump cases are the current frame/beta cases.
  This is the `wp_annot` proof pattern (one-step unfold + Löb), paid
  once for Esseq. The engine-side certification needs
  `Decomp`-level factorization restated: a step of a decomposed term
  is EITHER a rebuilt redex step (as now, `Decomp.step_factor`) OR
  the global jump — the factor theorem gains one disjunct.
- Decision needed before the arc: whether the statement WP is a new
  sealed definition (donor-faithful, recommended — it also carries
  the return/`Ψ` slot that `run ret_…` needs) or an unfolded
  `∀ Φ`-style abbreviation over the existing WP. Either way
  `wp_sseq`'s current statement survives as the no-jump corollary;
  `triple_seq` restates over the statement WP.

### R2 (REWORK, headline): the environment becomes live state

Binding patterns force `env` into the configuration (§2.1 item 6).
Everything currently proved is stated over `CoreExpr × Mem` with env
frozen at `[fmapEmpty]`; that shape cannot express `lets x = load(…)`.

- Recommended shape: put env in the LANGUAGE EXPRESSION, not the
  Iris state: `E := CoreExpr × EnvStack`, `Val := SpikeVal ×
  EnvStack` (toVal/ofVal act componentwise; the partial bijection
  laws survive). Why expression-side: the betas/save/run update env
  deterministically and state-independently, so they remain
  `wp_lift_pure_det_step_no_fork` lifts; no new ghost state, no
  stateInterp change; `Mem` and every memory lemma (Heap.lean, the
  small axioms' proofs) are untouched. The alternative (env as an
  Iris ghost resource `envIs`) turns every beta into a
  state-updating atomic step and adds a ghost heap — more donor-ish
  for nothing, since Caesium has no env (locals are memory) and
  offers no precedent either way.
- Cost is breadth, not depth: Step's 8 rules + inversions, `FragP`,
  `Decomp`, all `step_ctx_*`/`engineSteps_*` equations (env moves
  from read-only-under-WF to TOUCHED in the D14 partition for the
  binding betas — the partition row changes, with the engine cite
  `update_env`, Core_aux.lean:861/868), `drive` (unchanged — it
  already threads full `thread_state`, which contains env),
  adequacy statements (value readout now carries a final env, which
  exported posts ignore via projection). Mechanical, but it touches
  every file; do it FIRST and alone (see ordering).
- Note `lookup_env` failure (unbound `PEsym`) is an eval error
  channel inside `full_eval` — excluded by well-formedness premises
  (closed-under-env programs), same style as the existing `henv`
  nonemptiness premise.

### R3 (REWORK, headline): fuel and termination accounting under loops

Two distinct budgets are currently conflated into per-run
hypotheses that die under loops:

- **`esize e₀ + n ≤ lemDefaultFuel` (SemTriple, drive lemmas) is
  untenable**: `n` is the total step count; a loop makes it
  unbounded while the REAL constraint — get_ctx's fuel — is
  per-step and depends only on the CURRENT term's depth. The
  legitimate fix: replace the additive bound by a reachability
  invariant `∀ reachable e', esize e' ≤ B(prog)` with `B` a static
  measure: steps grow esize by ≤ 1 transiently (action wrap), betas
  shrink, merges shrink, and the jump RESETS esize to the (static)
  registered continuation's size — so a `B = max(esize e₀, max over
  labeled conts) + c` invariant closes by the same case analysis as
  `Step.esize_succ`. `drive_classify`'s induction restates with the
  invariant instead of the decreasing sum. This changes SemTriple's
  hypothesis line (a strengthening-of-form, one-time restatement;
  the new hypothesis is program-static, loop-length-independent).
  A second, analogous per-step budget appears with guards: the pexpr
  evaluator's own fuel (`full_eval_pexpr_lemFuel lemDefaultFuel`,
  Core_reduction.lean:94 — exhaustion is an opaque Undef-shaped
  leaf) needs a static pexpr-size side condition on guard/operand
  rules, same honesty pattern.
- **`hterm : ∀ aids, drive aids k … = .done v σfin` at a concrete
  `k` (prod_run_eq / sem_triple_prod) is untenable for
  symbolic-length loops** and awkward already for fib(10). The
  legitimate fix has three parts: (i) a drive-MONOTONICITY lemma
  (drive is deterministic per aids-supply; `done` at `k` implies
  `done` at every `k' ≥ k` with the same result) so the hypothesis
  becomes `∃ k ≤ budget`; (ii) derive that existential from a loop
  VARIANT: a per-iteration step-count bound function
  (`steps(n) ≤ c·n + d`, proved by the same induction that proves
  the loop's total-correctness invariant), giving symbolic
  termination-within-budget under the honest hypothesis
  `c·n + d ≤ driver-fuel`; (iii) NOT fuel parametricity of the
  engine — that is an upstream change (`fuelExhausted` is
  deliberately opaque, fail-closed; the spike report already scoped
  it out) and should stay a named non-goal, since the driver really
  does bail at 10^6 rounds. SemTriple itself needs NO termination
  hypothesis — it is already partial-correctness ∀n; only the
  production singleton-run equation needs (i)+(ii). Note
  `driver2_lemFuel lemDefaultFuel` (10^6 driver rounds) is the
  binding run-length budget, distinct from get_ctx's depth fuel.

### R4 (REWORK if lane T2 is in scope; avoidable by scoping to T1):
elaborated-C Core breaks singleton-ND and the verbatim-run-state
discharge

- Multi-reducible `Eunseq` (every `a + b`) makes the engine step
  list multi-element; the driver `pick`s; `runND` returns multiple
  executions; `prod_run_eq`'s "the run IS the singleton Active
  execution" equation is falsified as stated. Recovering it needs a
  confluence/commutation argument over independent loads (a real
  theorem, not bookkeeping) or a sequentialised+positivised input.
- Negative actions (every elaborated C assignment; NOT removed by
  `--sequentialise`) draw `fresh_excluded_id`/`fresh_symbol0` —
  the run state becomes TOUCHED, breaking `dischargeStep`'s
  "request monad returns rs verbatim, ∀ rs" projection; they also
  require `Ebound` and rewrite the arena via
  `break_at_bound_and_sseq` (with `failwithI` on `NO_BOUND`), plus
  the `do_race`/`Eexcluded`/`add_exclusion` machinery, and the
  `wp_annot_reindex` "annotations never influence stepping" lockstep
  argument must be re-examined (with `DA_neg`/exclusions in play,
  `do_race` reads them in `one_step_unseq_aux`).
- Verdict: keep lane T2 OUT of the while-lang arc; author the
  exhibits in Core (T1: positive, sseq-only, unseq-free — §2.2
  keeps every engine step list a singleton, checked arm-by-arm
  against `get_ctx`: Eif/Ecase/Esave/Erun/actions/Epure all return
  `[(CTX, e)]` or a single mapped descent). Record T2's items as a
  priced ledger for the elaborated-C arc.

### Per-item table for the remaining capabilities

| capability | class | reason (one line each) |
|---|---|---|
| `Eif` rule | EXTEND | singleton root redex; one `Step_with_runstate2`; guard via the engine's own `full_eval_pexpr` as an oracle hypothesis (`= Vtrue`/`Vfalse`); determinism SURVIVES (see below) |
| discharge of `Step_with_runstate2` | EXTEND | new `dischargeStep` arm mirroring `liftCore_run` (Driver.lean:245,336): run the monad on rs, `Defined → next`, `Undef → killed`; pexpr evaluation is state-verbatim BY THE SHAPE of `runEU` (the eval computation is state-polymorphic), one lemma |
| non-boolean Eif guard / unresolvable label / no current proc | EXTEND (honesty note) | these are `failwithI` PANIC channels, not refusals — they return `Inhabited` defaults in proofs; they must be EXCLUDED by well-formedness premises (guard-boolean, label-registered, proc-set), never classified as refusals; same pattern as the existing `henv` premise |
| `Ecase` rules | EXTEND | value scrutinee: TAU with `select_case subst_sym_expr v pats = some e'` as a rule hypothesis; no-match ILLTYPED is a certified refusal (D23 pattern); non-value scrutinee: one small-step `eval_pexpr1` rule; needs two mechanical lemmas — FragP and esize are preserved by `subst_sym_expr` (substitution fills pexpr leaves; the expr spine is unchanged) |
| `Esave` entry rule | EXTEND | one_step0 tau binding params into env; singleton; (params-evaluated shape first — the EVAL arm is small-step `mapM`) |
| `wp_run` + loop rule | EXTEND on top of R1 | once the statement WP exists, `wps_goto`+`wps_block_rec` port literally (▷ + □ + Löb); the label-map hypothesis is pure |
| action-operand `ACTION_EVAL` pre-step | EXTEND | one rule per action shape: an engine step full-evaluating operands to `mk_value_pe` forms (hypothesis-carrying); mandatory for ANY program with variables |
| `Ewseq` (wildcard/tuple) | EXTEND | known cost from slice A D6: ~3 rules, every inversion gains arms; only needed for T2 (authored programs use sseq) |
| `kill` / `wp_kill` | EXTEND | KillRequest2 discharge arm + `killM` success lemma from CellCoh liveness; ghost side: iris-lean HAS `ghost_map_delete` (Iris/Instances/Lib/GhostMap.lean:369) — a small `genHeap_delete` wrapper is needed in GenHeap (alloc/update/valid exist, delete does not); Coh is preserved by cell removal (Sat.mono already shrinks) |
| `wp_create` (mid-program allocation) | EXTEND with a CHANGED-SHAPE stateInterp (borderline; flag it) | the registered D26 allocator-cursor resource: add the cursor (`lastAddress`/`nextAllocId` facts) to Coh/stateInterp so `alignedAddr ≠ 0` is derivable; touches stateInterp and every rule's interp-open/close but no statement shapes; needed by elaborated loop bodies (create-per-iteration) and by list building — authored exhibits CAN dodge it by hoisting creates into the cold-start prefix (ProdEntry pattern), but the loop arc should stop dodging |
| `Ememop` PtrNe/PtrEq | EXTEND | new `Step_memop_request2` discharge arm + memM lemma for the pointer-comparison op; UB-exclusion premises for provenance kill arms (both-live or null operands), supplied by `isList`/points-to |
| pointer-typed cells | EXTEND | new `StorableAt`/decode instances for pointer memvalues (funptrmap-independence holds for data pointers; provenance rides in `AbsByte.prov`, cell-local); verify `bytes_fpm`/`stored_dec` at pointer type once |
| struct cells / `member_shift` / interior offsets | REWORK of cell granularity (T2 / C-shaped listrev only) | loads at member type inside one allocation break one-cell-per-allocation; the registered growth step (Heap.lean header): per-byte or per-member ghost heap + allocation-metadata heap |
| tagDefs / stdlib / labeled context | EXTEND (broad restatement) | frozen-context constants change (`spikeThread.current_proc_opt`, `spikeRunState.labeled`, non-default file for T2 stdlib); every `engineSteps_*` corollary and `drive` restate against the new frozen profile — mechanical but wide; the store rule already quantifies tagDefs |
| `SpikeVal` at join points | EXTEND (style rule) | branches deliver values with DIFFERENT annotation payloads (store-residue vs bare; `Ebound` even discards them); exact-annotation postconditions (`⌜w = .annot [DA_pos [] fp] …⌝`) must give way to annotation-insensitive posts (`w.val = v`, or `∃ ds`-quantified) at and above joins; `merge`/`mergeInto` machinery itself survives unchanged |
| ND-collapse under `Eif` | EXTEND (verified) | determinism survives: Eif/Ecase/Esave/Erun/actions are all singleton `get_ctx` roots; the only ND sources are `Eunseq` multi-decomposition, `End`, and driver `pick` on >1 lists — all outside lane T1 |
| `isList` | EXTEND | plain structural recursion on the abstract list (standard SL list predicate); no step-indexing needed — cells are first-order byte lists, the predicate has no self-reference through ▷; only `wps_block_rec`'s □/▷ uses the step-index, and that is donor-standard |
| `DriverCollapse`/`ProdEntry` growth | EXTEND | `prod_loop_done` gains one iteration case per new step form (the report's noted linear cost); `find_can_advance` returns true for `Step_with_runstate2`/`Step_memop_request2`, so the nonmemory loop and `process_core_step2` collapse the same way; note production `can_advance` PANICS on `Step_error2` (failwithI) — the WP's refusal-exclusion already keeps that unreachable, keep the note in the collapse header |

---

## 4. Summary table

| capability | needed by | class | one-line reason |
|---|---|---|---|
| Erun jump vs wp_bind (statement WP, wps_block_rec port) | fib, listrev | **REWORK** | engine discards the eval context at `run`; `Language.Context`(Csseq) is false in the extended relation |
| live environment in the configuration | fib, listrev | **REWORK** | binding patterns/save/run all update env; every current statement assumes it frozen |
| fuel: additive esize bound → reachability invariant | fib, listrev | **REWORK** | `esize e₀ + n ≤ 10^6` unbounded under loops; real constraint is per-step depth |
| termination: concrete-k `hterm` → monotonicity + variant bound | prod exports | **REWORK** | in-budget hypothesis untenable at symbolic loop length; SemTriple itself stays partial and survives as-is |
| elaborated-C lane (unseq ND, neg actions, Ebound surgery) | T2 only | **REWORK** (defer) | multi-element step lists kill the singleton run equation; neg actions write the run state |
| struct member access granularity | C-shaped listrev | **REWORK** (defer) | sub-allocation footprints vs allocation-rooted cells (registered) |
| wp_create / allocator cursor | listrev, elaborated fib | EXTEND (changed-shape interp) | registered D26 resource; interp gains a cursor component |
| Eif + Step_with_runstate2 discharge | fib, listrev | EXTEND | singleton redex, big-step guard as oracle hypothesis |
| Ecase + substitution lemmas | fib, listrev | EXTEND | selection-equation hypotheses; FragP/esize closed under subst |
| Esave entry, action-operand eval pre-steps | fib, listrev | EXTEND | new rules in the existing per-rule pattern |
| kill + genHeap_delete | fib, listrev | EXTEND | `ghost_map_delete` exists; GenHeap wrapper missing |
| Ememop PtrNe + pointer cells | listrev | EXTEND | new discharge arm + pointer encode/decode facts |
| join-insensitive postconditions | fib, listrev | EXTEND (style) | branch annotations differ; posts must speak `w.val` |
| frozen-context restatement (labeled, current_proc) | fib, listrev | EXTEND (broad) | Erun reads them; mechanical but touches every engineSteps lemma |
| isList | listrev | EXTEND | plain recursion, no step-indexing |
| Ewseq | T2 | EXTEND | known linear cost (slice A D6) |

Derived tallies: 4 REWORK items in the arc's path (R1–R3 + the
changed-shape stateInterp for wp_create), 2 REWORK items deferrable
by scoping (elaborated-C lane, struct granularity), ~10 EXTEND items.

---

## 5. Recommended slice ordering (riskiest first)

0. **S0 — jump-layer feasibility probe (the riskiest item, priced
   cheaply).** Before any brief: a throwaway probe proving, over a
   2-3 rule toy Step WITH env and a global jump rule, (a) the
   statement-WP definition elaborates in iris-lean and `wps_goto` +
   `wps_block_rec` port (Löb + ▷ + □), (b) the jump-aware sequencing
   lemma's "same successor" proof goes through without
   `Language.Context`. Kill criterion: if (b) needs a new WP
   definition inside iris-lean itself, stop and report. This
   de-risks R1+R2's interaction before the mechanical volume is
   paid.
1. **S1 — the environment rework (R2), alone.** Restate
   Step/FragP/Decomp/certification/adequacy over env-carrying
   configurations with the SAME construct set; re-run the full gate.
   No new constructs in this slice — it is a pure re-plumbing whose
   green bar is "285-theorem sweep restored".
2. **S2 — pexpr evaluation + Eif + Ecase + binding Esseq + operand
   pre-steps.** The straight-line while-lang body, certified
   (new `dischargeStep` arm; per-rule engine equations; refusal vs
   panic-channel honesty notes). Exhibit: branch-on-loaded-value
   program end-to-end.
3. **S3 — Esave/Erun + the statement WP + the loop rule (R1 landed
   for real).** Frozen-context restatement (labeled map,
   current_proc), global jump rule, factor-theorem disjunct,
   `wp_run`, `wps_block_rec` port; fuel invariant (R3 part 1).
   Exhibit: AUTHORED fib verified against the engine
   (`semantic_triple_sound` shape), with the loop invariant
   `a↦fib(i) ∗ b↦fib(i+1) ∗ n↦10−i`.
4. **S4 — kill + wp_create/cursor + PtrNe + pointer cells +
   isList.** Exhibit: authored list-reverse.
5. **S5 — production exports under loops (R3 part 2).** Drive
   monotonicity, variant-derived step bounds, `prod_run_eq` for the
   fib file; join-insensitive post restatement of the prod exhibits.
6. **Deferred, recorded as priced non-goals of this arc:**
   elaborated-C lane (Ewseq/Eunseq/neg/Ebound/stdlib — R4), struct
   member granularity, proc calls (`Eproc`/stack/RETURN), fuel
   parametricity upstream.
