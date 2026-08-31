# Phase-2 S3 slice notes: the jump/loop certification

[AGENT] S3 worker record, per the two-phase arc plan
(`2026-08-31_two-phase-arc-plan.md` §Phase 2 + the acceptance
AMENDMENT), the S0 probe prescription
(`2026-08-31_s0-probe-report.md` §6 S3), the phase-1 notes' S3 risk
read (`2026-08-31_phase1-notes.md` §2), and the readiness review's
Erun/WF findings (`2026-08-31_while-lang-readiness.md`).

Commits: S3.1 `ad79ff0` (the jump layer in the mirror + wps strata),
S3.2 `9ab441f` (the engine certification), S3.3 (this commit: the
J-cone completeness, the jump-profile drive/adequacy lane, THE
END-TO-END CERTIFIED LOOP, this record). Gates green at each commit
(`scripts/test_unit.sh`: grep ban + both packages with in-build
audits).

## 1. The jump-clause design (the Q↔labeled relation, DECIDED)

- `Q` is the CURRENT PROCEDURE's label map, carried in the runtime
  tuple (`CoreRt.lbl : LabelMap`, `LabelMap =
  labeled_continuations core_run_annotation`, Core_run_aux.lean:187)
  — Caesium's `to_rtstmt rf` carrying `f_code` (lifting.v:1002), the
  probe's `TRt.fn`. `Step` takes it as a leading index; `primStep`
  pins the successor's map (`r'.lbl = r.lbl`) — nothing writes
  `labeled` on the sequential path.
- The tie to the engine's TWO-LEVEL `core_run_state.labeled` is the
  pure equation `LabeledAt rs p Q :=
  fmapLookupBy ord p rs.labeled = some Q` on the QUANTIFIED run
  state, with `current_proc_opt = some p` (the proc-carrying frozen
  profile `procThread`) and the frozen `extern = fmapEmpty` making
  step_ctx's proc redirect the identity fallback
  (Core_reduction.lean:484). This is the donor's `⌜Q = rf.f_code⌝`
  in run-state form — the frozen-context restatement the mission
  offered, executed via the tuple + the equation.
- `jumpRedex?` (Step.lean) is the syntactic image of the engine's
  context-discard: get_ctx's leftmost path (Esseq-left, Eannot
  descent GUARDED by the merge-redex arm order) answering whether
  the hole holds an `Erun`. `jumpRedex? (Esseq pat e1 e2) =
  jumpRedex? e1` is what makes the wps jump clause a sequencing
  TRANSFER (probe report §3 case 2).
- The `wps.pre` jump clause (all pure but `Ls`):
  `|={⊤}=> ∃ params cont vs ev0 evs, ⌜ρ = ev0 :: evs⌝ ∗
  ⌜lookupLabel Q l = some (params, cont)⌝ ∗
  ⌜evalPexprs ρ pes = some vs⌝ ∗ Ls l vs ρ` — label resolution,
  argument evaluation by the PURE evaluator at the CURRENT env, the
  cons-env WF fact (the `update_env` empty-stack panic exclusion),
  and the per-label precondition; tracking stops (the label-context
  logic's discipline — no Φ-clash).
- WF premises throughout are RULE premises, never absorbed: the
  no-current-proc, unresolvable-label, non-boolean-guard, and
  empty-env failwithI PANIC channels are excluded because the rules
  fire only where the facts hold; in the drive lane the WP is the
  well-formedness oracle (§4).
- **[AGENT] design refinement within mission item (i)** — the
  per-label precondition is ENV-INDEXED:
  `LabelSpec GF = sym → List value → EnvStack → IProp GF`
  (S2's was env-blind). Forcing fact: the engine env frames are
  LemLib `Fmap`s (TreeMap-backed since arc-6); a body's parameter
  lookup after the jump's `update_env` fold sits on the quantified
  base frame, and lookup-after-add on an ARBITRARY frame needs
  comparator lawfulness (`Std.TransCmp` for the digest order) that
  is not shipped and is a mini-project to derive. Env-indexed label
  assertions are the classical de Bruin form anyway (label
  assumptions range over the whole state); the exhibit's invariant
  pins the frame SHAPE (`IsXFrame`), keeping every map operation at
  concrete keys/structures where reduction is definitional. The
  probe's env-blind `Ls` was an artifact of the toy's assoc-list
  env. Named seam (S4+): generic Fmap add/lookup laws via a
  `TransCmp` instance for `lemCmpToOrd symbol_compare`, needed the
  day a program's label body must read bindings made on arbitrary
  unpinned frames.

## 2. Certification status per construct

| construct | mirror rule | engine equation (context undisturbed) | granularity |
|---|---|---|---|
| Erun | `Step.run` (global, jumpRedex?-keyed; cons env; pure-eval args) | `stepDischarge_run`: at a proc-carrying thread whose arena DecompJ-decomposes to a registered run, the engine's ONE step replaces the WHOLE ARENA by the registered continuation with parameters rebound (`bindArgs` = the engine's foldM, `foldM_args_bridge`); `ctx` appears NOWHERE in the successor; run state read (labeled fiber via `LabeledAt`) and returned VERBATIM (`state_except_read` + runEU-lifted args) | one step, big-step args |
| Esave | `Step.save` (valueFromPexprs fast-path; cons env) | `step_ctx_save`: TAU, env rebound by the parameter fold (= `bindSaveParams`), everything else verbatim | one TAU; the non-value-params EVAL arm not mirrored (absence of a step; authored saves carry value initializers) |
| Eif | `Step.if_true/if_false` (pure-evaluator guard premise) | `stepDischarge_if_true/false`: ONE Step_with_runstate2, guard big-step through `full_eval_pexpr` (the bridge), ∀ run states, state/env verbatim | one step, big-step guard — the measured granularity |
| Ecase (value scrutinee) | `Step.case_value` (valueFromPexpr + select_case premises; the no-match ILLTYPED is a refusal = absent premise; PEconstrained PANIC excluded by the premise) | `step_ctx_case_value`: TAU into the substituted branch | one TAU |
| Ecase (EVAL arm) | NOT mirrored this slice | — | small-step scrutinee measured (one_step0's `eval_pexpr1` EVAL); deferred WITH the substitution-closure lemmas (FragJ/esize closed under `subst_sym_expr`) to S4 — Ecase is also outside `FragJ` until then |

Supporting layers, all trio-exact and pin-guarded in Audit.lean:

- **The evaluator bridge** (`PePure`/`peDepth`; `step_eval_bridge` →
  `pull_bridge` → `aux2_bridge` → `full_eval_bridge`): the pure
  mirror evaluator (`evalPexpr`: PEval / PEsym at the frozen extern
  / integer-`PEop` in the engine's operand order, e.g. `OpGt` =
  `ltIval v2 v1`) certified against the engine's whole tower —
  `pull_constrained` is annotation renormalization on the covered
  grammar, ONE `step_eval_pexpr` call evaluates full-depth, ONE
  `eval_pexpr_aux2`/`full_eval_pexpr` iteration finishes,
  state-VERBATIM by the runEU shape. Fuel honesty: `peDepth pe ≤
  lemDefaultFuel` side conditions (the engine's own budgets, fresh
  per call).
- **`RedexJ`/`DecompJ`** (all four new shapes are singleton get_ctx
  roots) with **`DecompJ.step_factor` — THE FACTOR THEOREM WITH THE
  JUMP DISJUNCT** (readiness R1): a step of a decomposed term either
  rebuilds its redex's step in context (and the redex is provably
  NOT a run redex), or the redex is a registered run and the step is
  the redex's OWN step — the context discarded. The phase-1
  `Decomp.step_factor` statement SURVIVES (its jump disjuncts are
  vacuous — `Decomp.jumpRedex?_none`).
- **The probe pair on Core**: `Step.jump_inv` (at a jump redex EVERY
  step is THE jump, successor decomposition-independent) and
  `Step.run_of_jumpRedex` (reducibility) — one-level `cases` because
  the congruence guards pay (§3).
- **`engine_step_matchJ` — the step-match completeness at the jump
  profile**: wherever the MIRROR steps at a `FragJ` configuration
  with the label tie, the engine's discharged behavior list is
  EXACTLY the matching singleton. This is a deliberate SHAPE CHANGE
  from phase 1's `engine_complete` (which classified refusals at
  mirror-stuck configurations): match-given-step + the WP's NotStuck
  is complete for the adequacy lane and dissolves the readiness
  review's WF-threading problem — the inversions extract the
  panic-exclusion facts from the given step. `engine_complete`
  itself survives VERBATIM on the phase-1 cone.
- **`dischargeStep`** gains the `Step_with_runstate2` arm — the
  sequential driver's `liftCore_run` protocol (Driver.lean:245/336)
  projected: Defined continues, Undef/Error kill, Exception is
  off-protocol; run state dropped in the projection and returned
  verbatim by every fragment monad (D14 partition: `labeled` is
  READ-ONLY-UNDER-WF for Erun; guard/arg evaluation never touches
  the run state).
- **The jump-profile drive lane** (Adequacy.lean): `driveJ` (run
  state a parameter), `drive_classifyJ` (in-budget accounting:
  additive per segment + the STATIC per-label bound absorbing the R3
  jump reset — `FragJ.esize_step_bound`), `engine_adequacyJ`
  (engine-only conclusion; reuses `spike_step_adequacy` unchanged —
  the Iris layer is profile-independent).

## 3. Statement-change findings (the frozen-corpus diff)

Instrument re-run: `scripts/signature_snapshot.lean` → committed
`2026-08-31_phase2-s3-signatures-post.txt` (this tree), name-keyed
diff against `2026-08-31_phase1-signatures-post.txt` (derived tally;
parser counts every dumped entry kind incl. ctor/rec):

- **UNCHANGED: 817** — including, verbatim: `SemTriple`, `Sat(.mono)`,
  `semantic_triple_sound`, `semantic_frame`, `ProvenTriple`(type),
  `engine_complete`, `EngineOutcome(.isRefusal)`, `drive`,
  `drive_classify`-adjacent value lemmas, the whole prod layer
  (`prod_run_eq`, `sem_triple_prod`, all `exhibit*`), `triple`,
  `triple_frame/conseq`, `wp_ofVal`, the Heap layer, `wps` itself,
  `wps_unfold`, `wps_run`-adjacent S2 rules **`wps_seq`,
  `wps_store`, `wps_load`, `wps_wand`, `wps_frame`,
  `wps_annot(_reindex)`, `wps_ofVal`, `wps_value_inv`** (their
  STATEMENTS survived the jump clause verbatim, proofs gained jump
  cases — the S2 design's promise held), the StmtProbe, and the
  whole engine-side per-rule equation set.
- **REMOVED: 4 = exactly the pre-declared retirements**:
  `Step.env_invariant`, `Step.env_invariant'` (the jump/save rebind
  the env; survivors: `Step.env_cons` — cons-shape preservation, the
  fact the sequencing proofs actually need — and the cone-scoped
  `FragP.step_env`/`Step.env_invariant_frag`), `instContextSseq`
  (falsified by the jump: `Context.primStep_fill` cannot hold when
  `K[run …] --> cont`; retirement note in Lang.lean),
  `wp_env_invariant` (survivor: `wp_env_invariant_stable` over the
  new `EnvStable` cone — see the triple_seq finding).
- **CHANGED: 78**, every one in the classes below (itemized):
  - **Pre-declared**: `wps_sound` gains the `blockSpecs` premise
    (+ the Löb-tied jump case; the donor `wps_block_rec` analog).
  - **(J1) label-tuple plumbing** [mission item (i)'s carrier —
    the S1 precedent class]: `CoreRt`/`CoreRVal` gain `lbl` → their
    ctor/recursor/projection machinery (~25 auto-generated entries),
    `toValRt_mk`/`ofValRt_mk`/`toValRt_of_toVal(_none)`,
    `CoreRVal.merge_mk`, `primStep_eq`, the three det lemmas,
    `drive_classify`/`spike_engine_adequacy` (tuples pinned at the
    frozen `spikeLbl = fmapEmpty` — the `spikeEnv` precedent),
    `wp_store`/`wp_load` (label-GENERAL: `Q` quantified — a
    strengthening).
  - **(J2) Step-relation restatement** [mission item (ii)]: the
    `Step` inductive (leading `Q` index; `sseq_ctx`/`annot_ctx` gain
    the `jumpRedex? _ = none` guards — the syntactic image of the
    engine's context discard, the price that makes `jump_inv`
    one-level; four new rules) + its recursors/ctors;
    `sseq_inv`/`annot_inv` gain the jump disjuncts (the factor
    theorem's disjunct at the node level); the remaining inversions/
    canonical instances/`val_elim`/`toVal_none` gain the `Q` index;
    `Decomp.rebuild`/`Decomp.step_factor`/`FragP.step` (Q index
    only; conclusions unchanged); `EngineMatch` pins `Step spikeLbl`.
  - **Forced findings** (consequences of the pre-declared
    retirements, each with the route recorded):
    - `triple_seq` gains an `EnvStable e1` hypothesis: for an
      arbitrary jump-capable `e1` the delivered env is not the entry
      env and `h2`'s `spikeEnv`-pinned triple says nothing about the
      continuation there. `EnvStable` (env-write-free sub-grammar,
      weaker than FragP — no action-canonicity or location side
      conditions, so the frozen exhibits' quantified locations pass)
      + `wp_env_invariant_stable` replace the retired route; every
      existing user passes `.action _ _`.
    - `Step.esize_succ` is FragP-scoped (the unconditional form is
      false: the jump resets to the registered continuation — R3 —
      and the branch/entry rules surface unmeasured subterms);
      `esize` itself extended with Eif/Esave arms (def-body delta,
      values unchanged on the phase-1 cone; visible as
      `esize.eq_def`).
    - `wp_annot(_reindex)`/`wp_sseq` pinned at `spikeLbl`: at a
      populated label map the BASE-WP annotation-lockstep argument
      breaks exactly at a jump (the jump discards the `Eannot`
      wrapper; both wraps land on one continuation owing different
      posts) and `wp_sseq` has the probe report §1 Φ-clash. Their
      label-GENERAL forms are the wps stratum (`wps_annot*`,
      `wps_seq`) — where the post-independent jump clause makes the
      transfers formula-identity. Recorded as the S3 statement of
      the strata split.
  - Artifact: `nd_bind_lemFuel.eq_def` (trailing-separator diff
    only — no change).
- **Type-invisible def-body deltas, hand-audited** (the S1
  `ProvenTriple` precedent): `LabelSpec` (env-indexed — §1),
  `wps.pre` (the jump clause), `dischargeStep` (the with-runstate
  arm), `ProvenTriple` (tuple pinned at `spikeLbl`), `Reach` (lbl
  threading), `mergeInto` (3-field patterns), `esize` (extended),
  `spikeThread`-adjacent none.
- **ADDED: 255** (new content): the label-context/evaluator/binding
  layer in Step.lean, the S3 wps rules (`wps_run`, `wps_if_true/
  false`, `wps_save`, `wps_case_value`, `blockSpecs(_intro,
  _intro_variant)`), the whole certification §2 layer, the J-drive
  lane, and LoopExhibit.

Boundary: module set unchanged — `LoopExhibit` is a NEW non-boundary
module (imports Adequacy + Wps only; no new engine imports; no
`runEffectful` anywhere in its cone); boundary theorem count 34 = 34
(ProdEntry/ProdExhibit untouched). Sweep: 417 → 542 boundary-swept
theorems (never decreased); banned-axiom sweep 1150 constants clean;
all pre-existing pins byte-identical; +6 S3 pins
(`stepDischarge_run`, `DecompJ.step_factor`, `engine_step_matchJ`,
`wps_sound`, `engine_adequacyJ`, `counter_loop_certified`), each
exactly the classical trio.

## 4. The loop rules

Both over the certified jump layer, donor-shaped:

- **The per-label invariant rule (partial, the default)** —
  `blockSpecs_intro`: assemble
  `blockSpecs Q Ls Ψ = □ ∀ l params cont vs ev0 evs,
  ⌜lookupLabel Q l = some (params, cont)⌝ -∗ Ls l vs (ev0::evs) -∗
  wps Q Ls Ψ cont (bindArgs params vs (ev0::evs))`
  from per-label proofs needing NO Löb and no mutual assumption —
  the jump clause breaks the back-edge circularity (each body's own
  back edges discharge against `Ls` via `wps_run`). The donor
  `wps_block_rec`'s mutual-□ + iLöb splits exactly as in the probe:
  the ONE Löb lands in `wps_sound` (pre-declared premise), which is
  simultaneously the stmt-WP-to-base-WP collapse and the place the
  jump clause is CERTIFIED against the step relation
  (`Step.run_of_jumpRedex` reducibility + `Step.jump_inv`
  same-successor).
- **The invariant+variant rule** — `blockSpecs_intro_variant`
  (μ : sym → List value → Nat): prove each body assuming the block
  specs only for STRICTLY SMALLER measures; classical well-founded
  (strong Nat) induction, no Löb, no step-indexing. Its step-bound
  PRODUCT (per-iteration bounds → the unconditional production
  `.done` equation) is deliberately NOT cashed here — that is the
  termination-accounting slot's item (arc plan); this slice's
  exports carry the sanctioned in-budget hypotheses.

## 5. THE EXHIBIT — the end-to-end certified counter loop

`CerberusHeapLang/LoopExhibit.lean`. The program (authored Core, all
metadata quantified):

    save loop: (x : integer := n) in
      if (x > 0) then
        lets _ = store(int, c, Specified 7) in run loop(x - 1)
      else pure(Unit)

Esave entry, real big-step `x > 0` guard through the certified
evaluator, the store under the loop through the certified store
axiom, a REAL context-discarding back edge with the computed
argument `x - 1`. Verified by `blockSpecs_intro` + `wps_sound`,
exported through `engine_adequacyJ`. The final theorem, verbatim:

```lean
theorem counter_loop_certified {GF : BundledGFunctors} [SpikeGpreS GF]
    (sbty : core_base_type) (idx addr : Int) (bs0 : List CerbMem.AbsByte)
    (n : Int) (hn : 0 ≤ n)
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (σ₀ : Mem)
    (hcoh : Coh σ₀ ((Iris.Std.PartialMap.singleton idx
      (SpikeCell.mk addr intTy bs0)) : SpikeHeapF SpikeCell))
    (nsteps : Nat) (aids : Nat → Nat)
    (hfuel : 4 + nsteps ≤ lemDefaultFuel)
    (hfuel2 : 3 + nsteps ≤ lemDefaultFuel) :
    let prog := loopProg loc ann ra mo bty xbty sbty (cellPtr idx addr) n
    let rs := loopRS loc ann ra mo bty xbty (cellPtr idx addr)
    (∀ r, driveJ rs aids nsteps
      (procThread loopProcSym prog [fmapEmpty]) σ₀ ≠ .killed r) ∧
    (driveJ rs aids nsteps
      (procThread loopProcSym prog [fmapEmpty]) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      driveJ rs aids nsteps
        (procThread loopProcSym prog [fmapEmpty]) σ₀ = .done v σ' →
      v = Vunit ∧ ∃ bs',
        ((n = 0 ∧ bs' = bs0) ∨ (0 < n ∧ bs' = sevenBytes)) ∧
        ∃ i a, cellPtr idx addr = cellPtr i a ∧
          CellCoh σ' i ⟨a, intTy, bs'⟩)
```

Engine vocabulary only in the conclusion; cone = exactly the
classical trio (pin-guarded). The data-dependent post (`n = 0` →
cell untouched; `0 < n` → the stored image) is the point: the loop's
branches, back edge, and store all really happened in the engine's
own {step_ctx → sequential-discharge} loop, at a run state whose
`labeled` carries the registered continuation. Partial correctness
(`.more` unconstrained); the two fuel hypotheses are the engine's
own budgets in the sanctioned in-budget interim form.

Honesty notes on the exhibit:
- The env-frame invariant `IsXFrame`/`XReady` pins the reachable
  head-frame structure (one-node tree at the counter symbol),
  making every evaluator lookup definitional — the §1 seam.
- `loopQ`'s continuation equals the save body, matching the
  registration discipline for a trailing-position save; a
  `collect_labeled_continuations`-computed-Q bonus equation was NOT
  proved this slice (the production tie for authored programs is the
  production-layer item; recorded).
- `driveJ`'s run state is constant through the run — honest because
  the certification proves every fragment monad returns it verbatim;
  the REAL driver additionally ticks `aid_supply`, which the
  fragment ignores (the phase-1 D2 discipline, unchanged).

## 6. Frictions (for S4)

- **Subst-orientation** bites constantly in the new inversions'
  aftermath (the phase-1 note confirmed again): the surviving
  variable LEFT; `obtain rfl : kept = killed := h.symm`.
- **Spelling-stability under dsimp**: proofs that `rw` against
  engine-term shapes must either stay binder-free (rw skips
  binders — the `stExceptUndef_bind_apply`-chain discipline used in
  `stepDischarge_run`) or take the fold/discharge bodies ABSTRACT
  with pointwise `rfl` hypotheses (`foldM_args_bridge`); dsimp
  normalizes match-lambdas to projections and breaks syntactic rw.
- **Matcher strictness**: `update_env_aux` at a sym pattern needs
  the VALUE's constructor or an `unfold`+`dsimp [mk_sym_pat]` before
  it reduces (the wildcard arm did not — the compiled matcher
  examines the value column for the deeper arms).
- **TreeMap internals reduce** for concrete-structure trees via the
  `simp` unfold set in `treeMap_get?_insert_empty` (no ordering
  laws needed); arbitrary-tree facts need `TransCmp` — the named
  seam.
- **Fmap BEq instances differ**: `update_env` uses the
  MapKeyType-derived comparator-BEq, NOT the structural `BEq sym`;
  statements about engine-produced adds must use
  `instBEqOfMapKeyType` explicitly (`envAdd`).

## 7. Risk read for S4 (fib + array-sum + termination accounting)

- **fib needs Ecase + binding Esseq**: the value-scrutinee Ecase
  rule and its engine equation exist; missing are (a) the BINDING
  sseq betas (non-wildcard patterns — new Step rules + engineSteps
  equations in the existing pattern; env-write discipline already
  absorbed by S3's env_cons/EnvStable split), (b) the two
  substitution-closure lemmas (FragJ and esize preserved by
  `subst_sym_expr`) so Ecase can join `FragJ` — priced mechanical
  but wide (the fuelled subst def), and (c) the Ecase EVAL arm
  (small-step scrutinee) if scrutinees are not pre-bound symbols.
- **The env-map seam WILL bind**: fib's `lets al = load(a) in …`
  binds loaded values on frames that also carry other bindings; the
  exhibit's one-key frame pin does not scale to two keys unless the
  invariant pins two-node shapes (doable, ugly) — budget the
  `TransCmp (lemCmpToOrd symbol_compare)` instance + the
  Std.TreeMap law bridge (String order transitivity via
  `digest_compare`'s real definition — it is NOT extern) as the
  clean fix. After it, `fmapLookupBy`-after-`fmapAddBy` laws are
  Std one-liners and the frame pins disappear from invariants.
- **Array-sum**: pointer arithmetic through the evaluator
  (`PEarray_shift` or memops) is NOT in `PePure` — extend the
  mirror evaluator + bridge (same per-constructor pattern); big-sep
  pre-states ride the existing bigSepM machinery (`bigSepM_insert`/
  `singleton` verified usable).
- **Termination accounting**: `blockSpecs_intro_variant` is the
  derivation-principle half; the step-bound product needs (i) drive
  monotonicity (deliberately untouched per mission), (ii) the
  per-iteration bound extraction — plan them against `driveJ`
  first (its constant run state simplifies the induction), then the
  production `prod_run_eq` face.
- **Production tie**: `loopRS` is hand-built; wiring authored-Core
  programs through `initial_core_run_state`'s
  `collect_labeled_continuations` (so `LabeledAt` is DERIVED, not
  hypothesized) is a small `decide`-grade equation per program but
  touches the effectful `sym_supply` seam — keep it in the
  boundary modules.
