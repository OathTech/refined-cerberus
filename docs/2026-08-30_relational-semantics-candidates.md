# Relational semantics for Core: candidates memo

**Status: DRAFT — recon/evaluation deliverable, not a charter.**
Date: 2026-08-30. Provenance: [AGENT: arc-2 recon worker], read-only
survey of (1) the cerberus-lean Lem sources and Lean engine, (2) the
park branch `arc/segment-ladder` relational-semantics artifacts, (3)
iris-lean's ProgramLogic interface at the repo pin, against the port
map's consumer contract (`docs/2026-08-29_port-map-draft.md` §1.3,
agenda items 1/2/17). Two survey subagents' findings were folded in;
every load-bearing claim carries a file:line cite. Claims I could not
settle from source are in §6 (open questions), not guessed.

## Governing rulings (the criterion this memo was written under)

- [USER 2026-08-29], the framing criterion (verbatim): "what gives us
  the most sane and legitimate relational semantics for Core that can
  scale to what RefinedC's layers need?"
- [USER 2026-08-29], course correction 1 (verbatim): "we are going to
  build on top of the actual cerberus-lean operational semantics. No
  rebuilding the whole stack or whatever. This will be legitimately
  built on cerberus-lean, or it is off target." (Consequence: the
  original brief's candidate (a), a fresh relational rendering
  mirrored from the Lem sources, is STRUCK as a foundation candidate
  — §3.0 records why in one paragraph.)
- [USER 2026-08-29], course correction 2 (verbatim): "the
  cerberus-lean operational semantics is the ***only*** semantics
  that we trust. The relational semantics is a derived layer on top
  of it." (Consequence: every candidate is a DERIVED layer with no
  independent semantic authority; layer/engine disagreement is by
  definition a defect in the derived layer; the legitimacy axis is
  the derivation theorem — what connects the candidate down to the
  engine, characterization vs one-direction soundness, and its cost.)
- [USER 2026-08-29], course correction 3 (verbatim): "the intended
  end state of all of this is an adequacy result that can be stated
  *exclusively* over the cerberus-lean semantics"; and: "We are
  building a reasoning capability for cerberus-lean's operational
  semantics — 'mirroring' without proof is valueless." (Consequence:
  each candidate's bottom line states the END-TO-END adequacy
  statement it enables — quantified only over cerberus-lean semantic
  objects, no relational-layer vocabulary in the final statement —
  and how far its derivation theorem carries. A candidate that cannot
  discharge into an engine-only statement is disqualified.)
- Trust context: the reasoning-era prototype is ruled
  highly-untrusted-as-design (DECISIONS.md 2026-08-29), but [USER
  2026-08-29] upgraded its relational-semantics work to DESIGN DONOR
  status for this question ("we built quite a bit of this on the
  failed design prototype, so we may already have a design donor
  here"). Park-branch material below is evaluated on merits and
  labeled [park, design-donor per USER 2026-08-29].

Path conventions: `CL/` = `/home/dev/projects/cerberus-lean-proj/cerberus-lean/`;
`IRIS/` = `/home/dev/projects/cerberus-lean-proj/deps/iris-lean/Iris/Iris/ProgramLogic/`
(checkout HEAD `34390a01` — verified identical to this repo's
lakefile.toml iris pin, so the signatures cited are the pinned ones);
`park:` = `git -C CL show arc/segment-ladder:` paths.

---

## 1. The consumer contract

What the relational layer must ultimately provide, from iris-lean's
interface at the pin plus the port map's WP-lemma stratum.

### 1.1 The iris-lean language/WP/adequacy interface (pin 34390a01)

- `Language Expr State Obs Val` = `PrimStep Expr State (List Obs)`
  (`primStep : Expr × State → Obs → Expr × State × List Expr → Prop`)
  + `ToVal Expr Val` + `val_stuck` (IRIS/Language.lean:115-121, class
  `PrimStep` at :70).
- WP is defined against an `IrisGS_gen` instance whose core datum is
  `stateInterp : State → Nat → List Obs → Nat → IProp GF`
  (IRIS/WeakestPre.lean:40-45).
- Lifting: `wp_lift_step` (IRIS/Lifting.lean:77),
  `wp_lift_atomic_step` (:156), pure steps via the `PureExec` class
  (IRIS/Language.lean:423, Lifting.lean:186-214).
- Bind: `wp_bind (K : Expr → Expr) [Language.Context K]`
  (IRIS/WeakestPre.lean:434); `Language.Context` (IRIS/Language.lean:270)
  needs only `toVal_eq_none_fill` / `primStep_fill` /
  `primStep_fill_inv` for a FUNCTION K — a full `EctxLanguage`
  (IRIS/EctxLanguage.lean:150) is NOT required for wp_bind.
- Atomicity: `Atomic a e` (IRIS/Language.lean:248) — needed for the
  typing layer's mask dance (port map agenda item 10; `wp_atomic`
  consumption at RefinedC programs.v:1389).
- Adequacy: `wp_adequacy_gen` (IRIS/Adequacy.lean:302) concludes
  `adequate s e σ (fun v _ => φ v)`, i.e. ∀ thread-pool-reachable
  configurations, result values satisfy φ and (at `.NotStuck`)
  nothing is stuck (`adequate_alt`, IRIS/Adequacy.lean:251;
  no-fork variant `AdequateNoFork` :245).

### 1.2 What RefinedC's layers consume from the language instance

From the port map (authoritative; summarized here): the ~55
per-construct WP lemma library (§1.3 stratum iii — one `wp_*`/`wps_*`
lemma per language construct, e.g. `wp_binop_det`, `wp_deref`,
`wps_assign`, `wps_goto`), the assertion layer (stratum ii: byte
points-to, `loc_in_bounds`, `alloc_alive`, `fntbl_entry`), structural
WP artifacts (stratum iv: `Wp` instance, derived statement-WP `WPs`
over a label map, `wp_call_bind`, reflected syntax `W` +
context-finders for syntax-directed bind — agenda item 16), and
adequacy plumbing (stratum v). The typing judgments are
SYNTAX-INDEXED: `typed_val_expr (e : expr) T := ∀ Φ, … -∗ WP e {{Φ}}`
(RefinedC programs.v:96) — so whatever plays `expr` must expose the
program construct the rule dispatches on. The port's referent
fragment is sequentialised/evaluated Core, Eunseq excluded from
fragment 1 (brief; see §2.5 for what the sources actually say about
sequentialisation).

Consequences for the step relation, stated concretely:

1. It must instantiate `Language` (or at minimum support the
   `Language.Context`-based bind) and `Atomic` for memory ops.
2. It must support per-construct lifting lemmas STATED OVER PROGRAM
   SYNTAX and quantified over all programs/states — not per-program
   facts.
3. `stateInterp` must decompose into frameable resources (the port
   map's stratum ii); the state carried by the step relation must be
   splittable into interpreted (heap/alloc) and control components.
4. Its adequacy must discharge into an engine-only statement
   (governing ruling 3): the final theorem quantifies over
   `CerbND.runND`-enumerated outcomes of the actual engine, with no
   relational vocabulary.

---

## 2. What exists

### 2.1 The engine of record (cerberus-lean, mainline)

The differential lanes validate the pair `CerbND.runND ∘ Driver.drive`
(and `RelSem.Cerb.callND` for the 117 per-function verify lanes —
CL/lean_frontend/relsemcore/RelSem/Call.lean:202):

- `Driver.drive` (CL/lean_frontend/generated/Driver.lean:500) is a
  pure total function returning a REIFIED ND TREE:
  `ndM driver_result step_kind driver_error (mem_constraint …) driver_state`.
  `ndM` (generated/Nondeterminism.lean:131) is a state-passing tree
  whose node alphabet `nd_action` (:117) is
  `NDactive | NDkilled (kill_reason) | NDnd | NDguard | NDbranch | NDstep`;
  UB rides the kill channel (`kill_reason = Undef0 | Error0 | Other`,
  Nondeterminism.lean:54), never stuckness.
- `CerbND.runND` (CL/lean_frontend/CerbND.lean:136; worker
  `runNDFuel` :89) is the fueled exhaustive enumerator returning the
  list of `(nd_status, trace, final state)` triples; branch order
  deliberately mirrors OCaml smt2.ml (CerbND.lean:80-88). Recorded
  divergence: NO constraint pruning — `NDguard` always continues and
  `NDbranch` explores both arms (CerbND.lean:5-14, 115-124), unlike
  OCaml's check_sat path. Fuel = tree depth, budget
  `ndDefaultFuel = lemDefaultFuel` (= 10^6, CerbND.lean:71).
- The per-Core-step content is NOT in the ndM tree for sequential
  code: the driver loop `driver2` (generated/Driver.lean:380/:386) →
  `drive_nonmemory_steps_aux2` (:345/:351) calls
  `Core_reduction.step_ctx` per thread and GREEDILY advances every
  `can_advance` step without minting an ND node (the Lem source's
  fast-path, CL/frontend/model/driver.lem:1062-1274). One driver
  iteration of a sequential program contains nearly the whole program
  ([park] arc-16 S1 record §1, re-verified against the mainline
  generated Driver.lean:346-351 in this session). Deterministic
  segments are ONE `NDactive` node (bind-collapse,
  Nondeterminism.lean nd_bind).
- `step_ctx` (CL/lean_frontend/generated/Core_reduction.lean:484;
  Lem spec CL/frontend/model/core_reduction.lem:1087) is a total
  function from a thread configuration to the LIST of offered steps
  `List core_step2` — successor-set form, i.e. already a relation in
  function clothing. The step alphabet `core_step2`
  (core_reduction.lem:113) has 12 constructors (tau / eval /
  action-request / memop-request / ccall / done / blocked / error /
  spawn / fs / nd); memory actions are CPS-carrying `action_request2`
  records (core_reduction.lem:67).
- The final value is NOT read off the final configuration:
  `finalize` (generated/Driver.lean:423) computes `dres_core_value`
  by `Driver.hack` (:391/:395), a second fueled pure-expression
  forcer over the final arena. Adequacy postconditions about "the
  result" relate to `hack`'s output.
- Totality/trust status: the exec cone is gate-enforced total (20
  generated modules + CerbND, empty allowlist,
  CL/scripts/check_exec_totality.sh:53-57); in-repo axiom census
  zero; the one residual axiom is `LemLib.runEffectful` in the
  lem-lean dependency (CL/lean_frontend/DESIGN.md:80-88) — a
  boundary-list entry this repo's Audit.lean will need when the
  semantics dependency lands.

### 2.2 The mainline ALREADY carries a derived relational spine

Not park material — this survived the semantics-first split as the
`RelSemCore` lib (CL/lean_frontend/lakefile.toml:124-127; split
record docs/2026-08-31_semantics-first-split.md:24-40):

- `RelSem.Machine` (relsemcore/RelSem/Machine.lean): configurations
  `MExpr = running (ndM …) | done (Outcome)` (:54), the observation
  function `app : ndM → S → nd_action × S` (:96) — documented as
  "the ONLY way the relational layer consumes the generated code" —
  and `inductive Step (γ : CsSem C S) : Config → Config → Prop`
  (:131) with 7 arms, each premised on one `app` equation. `CsSem`
  (:105) abstracts the constraint discipline: `CsSem.exhaustive`
  (:112) matches the runner's no-pruning behavior; `CsSem.ofEval`
  (:123) is the pruning shape.
- `RelSem.RunND` (relsemcore/RelSem/RunND.lean): **the derivation
  theorem, proved, about the production runner**:
  `runND_sound` (:190) — every triple `CerbND.runND` enumerates is
  the endpoint of a `Steps (CsSem.exhaustive)` trace. Plus
  `runNDFuel_sound` (:128), fuel monotonicity (:202), `Behaviors`
  (:302).
- `RelSem.Cerberus` (relsemcore/RelSem/Cerberus.lean): the driver
  instantiation `DStep` (:55), `initConfig` (:65), and — decisive
  for governing ruling 3 — the ENGINE-ONLY statement forms already
  exist here: `HarnessAdequate` (:268) is literally
  `∀ out tr st', (out,tr,st') ∈ CerbND.runND (drive …) (initial_driver_state …) → ∃ r, out = Active r ∧ spec r`
  — quantified exclusively over cerberus-lean semantic objects.
  `seqModel : ExecModel` (:308) fixes `isUB` as a killed-`Undef0`
  VALUE (relsemcore/RelSem/ExecModel.lean:33-44: "UB is a VALUE of
  the model … never encoded as stuckness").

So the bottom rung of every candidate below — a small-step relation
over the engine's ND tree, sound against the production runner — is
already on the mainline the semantics pin will target.

### 2.3 The Lem spec: what relational structure the SPEC has
(read per correction 1 as documentation of what the Lean artifacts
mean, not as a foundation)

- There is NO declarative/indreln Core semantics anywhere in the Lem
  tree: `frontend/ott/core-ott/core.ott` is grammar-only (no defns);
  Lem's `indreln` appears nowhere in `frontend/model/`. The spec IS
  the interpreter.
- The live stepper `step_ctx` is evaluation-context-structured:
  `context = CTX | Cunseq | Cwseq | Csseq | Cannot | Cbound`
  (CL/frontend/model/core_run_aux.lem:28), with decomposition
  `get_ctx : expr → list (context × expr)`
  (core_reduction.lem:523; unseq fanout via `get_ctx_unseq_aux`
  :590) and recomposition `apply_ctx` (:605). An ectx-style
  presentation is native to the spec, not an imposition.
- Named reduction rules exist as comments on the live code
  (core_reduction.lem:293-448: PURE, CASE, LET, IF-TRUE/FALSE/UNDEF,
  UNSEQ-RACE, LETW/LETS, SAVE, ND; :1108-1476: THREAD-DONE, RETURN,
  PCALL, RUN, SPAWN, MEMOP …), and a cleaner 7-label alphabet
  `one_step` (TAU_WITH_RUNSTATE | TAU | EVAL | ND | MEMOP |
  UNSEQUENCED_RACE | ILLTYPED, core_reduction.lem:248) sits in the
  file WITH NO CALLERS — an abandoned refactor toward an LTS, and
  the best available naming scheme for a derived relation's labels.
- The race check is join-only: `do_race` (core_reduction.lem:214)
  fires at the unseq join (`one_step_unseq_aux` :258), so race
  detection is schedule-independent ([park] v2 fresh review :74-77,
  re-cited by the engine survey).
- Memory is the SAME ndM at another instantiation
  (`memM`, frontend/model/mem.lem:48), joined by the monad morphism
  `liftND`/`liftMem` (nondeterminism.lem:271, driver.lem:125): one
  ND tree, one resolution point. The Lean CerbMem mirrors this
  (`memM` abbrev, CL/lean_frontend/CerbMem.lean:1394; UB→kill via
  `memFail` :1404-1413). Model of record is PVI, not PNVI
  (docs/2026-08-31_semantics-forward-assessment.md F1.1).
- Fork deltas on these files are target plumbing plus one semantic
  change (symbol-supply threading, Lean-target-only, shimmed back on
  OCaml) — the spec structure above is upstream-faithful
  (core_sequentialise.lem, core_indet.lem, core_run_effect.lem are
  byte-identical to upstream).

### 2.4 The park-branch artifacts [park, design-donor per USER 2026-08-29]

What each actually achieved, its trust status, fit/unfit — assessed
from the sources, not the postmortem's summary alone.

**(i) The per-step language: `KExpr`/`KStep`/`KSteps`**
(park:lean_frontend/relsem/RelSem/PerStep.lean:53,104,138; design
record park:lean_frontend/docs/2026-08-24_arc16-s1-language-instance.md).
Continuation-reified sequencing over the generated ndM:
`KExpr = done (Outcome) | seq (m : ndM α …) (k : α → KExpr)`, with
`denote : KExpr → ndM` (:63) mapping `seq` to the generated
`nd_bind`. `KStep` has 7 arms, each premised on ONE `app` equation of
the leading atom — the same observation discipline as mainline
`RelSem.Machine.Step`, with joints. Lineage: free-monad /
interaction-tree program-logic pattern (named in-file; ITree bind-up-
to-eutt is the exact analog for the observation-level associativity,
PerStepObs.lean header). Derivation theorems PROVED:
- soundness by construction (premises are app equations);
- **steps-of-fuel completeness**: `ksteps_of_runNDFuel` (:431) /
  `ksteps_of_runND` (:533) — every triple the production runner
  enumerates for `denote e` is a `KSteps` endpoint, for
  `F ≤ lemDefaultFuel`. Together: a two-directional characterization
  of the runner at the joint granularity.
- Measured constraint that forced the design: fuel'd `nd_bind` is NOT
  associative as values (misaligns at depth ~10^6); composition holds
  only at the runner-observation level (`runNDFuel_bind_fuel_irrel`
  :362; PerStepObs.lean's congruence/assoc-up-to-observation).
Trust status: built green under the park's in-build axiom audit
(boundary = classical trio + `runEffectful`; no sorry; relsem Audit
sweep, park:relsem/RelSem/Audit.lean). Fit: exactly correction-2
shaped — derived, observation-only, no independent authority. Unfit
part: joints exist only where reification puts them; the expression
is interpreter-run-shaped, not Core-syntax-shaped (see §3.B risks).

**(ii) The Iris language instance** (park:…/PerStepIris.lean:67,75):
`instance Language KDriveExpr driver_state Empty DriveVal` — plain
`Language`, NOT EctxLanguage ([AGENT] decision, S1 record §2.3: ndM
is a function type, no fill/decompose carrier; `seq` plays the
context role by construction). Proved against iris-lean pin
`34390a01` — the SAME rev this repo pins, so zero interface
migration. Thread-pool erasure + `wpk_done = wp_value'` (:138).
UB-kill is a VALUE of the language (spec-excluded, not stuckness).

**(iii) The loop peel** (park:…/PerStepPeel.lean): the generated
driver loops reified as per-round KExpr joints — `dnmsK` (:152, one
scheduler round per joint), `bodyK` (:364 anchor), `callK2` (:509),
with the anchor `runND_callND_eq_callK2` (:595) tying the peel to the
untouched production `callND` at the runner-observation level.
Transcription discipline: every peel atom is a verbatim projection of
the generated loop body; `_unfold` anchors are rfl-grade and break
build-fatally on generated-code drift. This is the mechanism that
recovers per-Core-step granularity from the greedy fast-path (§2.1):
without it, a sequential program is one step.

**(iv) Mechanism C — the per-construct round characterizations**
(park:…/CStep.lean:130,150,170; charter §3.C of
park:docs/reasoning-era/2026-08-28_proof-performance-plan.md).
Lineage precisely named: the derived relational presentation
(introduction lemmas) of a clocked definitional interpreter — the
function→relation direction of functional big-step
(Owens–Myreen–Kumar–Tan, ESOP 2016); Iris precedent HeapLang
`PureExec`. Each `cstep_*` lemma turns one round CLASS of the
interpreter's round function `dnmsRoundM` (PerStepPeel.lean:137) into
an introduction rule quantified over the state fragments, via the
program-blind rebuild family `stateAt` + one generic inversion
`stateAt_inv` (CStep.lean:62,80). Premise structure: a ground
discovery equation
(`find_can_advance (dnmsDiscover tagDefs tid σ) = some (Step_…)`) +
the class's semantic payload (eval verdict). The eval payload layer
IS syntax-facing: `Kit/EvalStep.lean`'s `se_*` laws
(9 laws: `se_sym_hit`, `se_if_bool`, `se_not_bool`, …) are per-
constructor lemmas over the generated one-step pexpr evaluator at
symbolic operands. Probe verdict: **measured GO**
(park:docs/2026-08-29_v3a-loops-mechC.md:18-56 — construct lemmas
fired on rounds they were not generated from, ~0.35-0.6 s per minted
round, within the block-supply cost band). Measured hazards recorded
there: unguarded unfolding runs the fuel loop away (16-48G memory
observed, :98), control images need flattening to beta-normal form
(:107), and probe files carry `maxHeartbeats 2000000` caps
(park:…/CStepProbe.lean) — a banned smell under this repo's rules,
sitting in measurement instruments rather than shipped proofs, but a
real warning about walk cost.

**(v) The decomposed ghost state + WP + adequacy (the "V1 six
components")** (park:…/CerbStateRA.lean, CerbStateWP.lean,
CerbStateStep.lean, CerbStateAdequacy.lean). Components: BYTES
(gen_heap at addr ↦ AbsByte), ALLOCS (ghost_map), ENV (per-cell
local ownership with a LOOKUP-LEVEL coherence invariant `EnvCoh`
(RA:219) — forced because LemLib `Fmap` carries comparator closures,
so no faithful cell-level projection exists), CTL (ghost_var halves
at the control remainder `ctlOf σ`), SUPPLY, MEMREST
(`CerbStInterp`, RA:431). WP rules at component granularity:
lifting skeleton `wpk_seq_res_det` (WP:76), control rounds
`wpk_seq_ctl` (WP:124), env writes (WP:219), case-split-at-symbolic-
discriminant rules with RefinedC `typed_if` lineage
(CerbStateStep.lean:49-…), birth rules against a domain ledger.
Adequacy PROVED: `cerbSt_adequacy` (Adequacy:136), production-runner
face `kAdequateSt_of_wp` (:239), and harness bridges
`kCallHarnessAdequateThrSt_of_wp` (:269) whose CONCLUSIONS are the
engine-only `CallHarnessAdequate` forms (byte-identical defs from
relsemcore Call.lean). Exhibit: `M1Statement`
(park:…/M1Statement.lean) — ∀ x ∈ int range, every outcome of
callND(sgn,[x]) is Specified sgn(x) — labeled PROVED with trio cone,
end-to-end through the Iris WP layer. Fit note: this stratum is the
donor for the port map's stratum (ii)/(v) obligations; the ENV
component may dissolve under RefinedC's locals-as-heap-substitution
(postmortem salvage map row "V1 state decomposition"), an open
design question, not settled here.

**(vi) What the park route did NOT build**: WP lemmas indexed by Core
SYNTAX quantified over all programs. The cstep discovery premises
were discharged per control point by the `seg_discover` kernel-pin
device (Kernel.whnf-computed, kernel-rechecked, no ofReduce* — legal
under this repo's rules but per-program work). The step from
"discovery-equation premise" to "syntactic-redex premise" — a
once-per-construct theorem about `step_ctx`'s dispatch — was the
declared next stratum and is nowhere in the park tree. This is the
main gap every candidate below must price (§3, §4 probe).

### 2.5 Sequentialisation: the brief's premise vs the sources

The brief says the port's referent fragment is SEQUENTIALISED Core.
The sources say, precisely:

- The sequentialise pass exists
  (CL/frontend/model/core_sequentialise.lem:4-69; generated
  CL/lean_frontend/generated/Core_sequentialise.lean:37-40) but is
  (a) **best-effort**: it eliminates `Eunseq` only in
  `Ewseq/Esseq pat (Eunseq es) e2` head position, silently warning
  and leaving other occurrences (core_sequentialise.lem:23-25); (b)
  **a `partial def` in Lean with ZERO callers** — outside the
  totality gate, never validated; (c) **not in either pipeline's
  default path**: OCaml gates it behind `--sequentialise`
  (backend/common/pipeline.ml:533), the lanes run without it
  (CL/scripts/test_exec.sh:18-22 documents dropping the flag), and
  the Lean pipeline (CL/lean_frontend/Main.lean:720-881) has no
  sequentialise wiring at all.
- The engine therefore interprets `Eunseq` LIVE: `get_ctx_unseq_aux`
  produces the interleaving fanout, and the race check is join-only
  (§2.3). One standing exception: pinned libc bodies were dumped from
  an oracle build with `--sequentialise --rewrite`
  (Main.lean:78-100), so libc-mode programs are mixed.
- The park design left the mode-of-record pin as an OPEN OPERATOR
  DECISION, recommending live-unseq
  (park:docs/reasoning-era/2026-08-30_core-logic-paper.md:438-440).

Consequence: "Eunseq excluded from fragment 1" cannot mean "the
engine runs sequentialised Core" — it doesn't. It must be realized
as either (α) a SYNTACTIC SIDE CONDITION (WP/typing rules stated for
unseq-free expressions; programs whose elaboration emits `Eunseq`
outside the handled shape are out of fragment), or (β) wiring +
fuel-totalizing + differentially validating `sequentialise_file` in
the Lean pipeline so the verified object is
`runND (drive tagDefs false (sequentialise_file file) args)` — still
an engine-only statement, but about a transformed file, and the
transform then needs its own validation lane (the oracle supports the
flag, so a differential lane is constructible). This is an operator
decision the language-instance charter needs BEFORE dispatch
(sharpens port-map agenda item 17). Note (γ) — proving an
unseq-elimination correctness theorem — is a research-sized detour
and not required by either realization.

---

## 3. Candidates

Axes per governing rulings: **sanity** (recognizable classical
construction, nameable lineage); **legitimacy** (the derivation
theorem down to the engine: characterization vs one-direction, and
its cost — the engine is the only semantics, the layer is derived);
**end-to-end adequacy statement** (the engine-only theorem a verified
program gets); **scalability** (can the ~55-lemma WP stratum, bind
story, and typing layer be built on it); **effort shape**; **risks**.

### 3.0 [STRUCK] Fresh relational rendering mirrored from the Lem spec

Struck by [USER 2026-08-29] course correction 1; recorded in one
paragraph as required. A hand-written inductive small-step relation
over Core syntax, transcribed from core_reduction.lem's rule
comments, would be a SECOND semantics standing beside the engine:
its fidelity to the engine would be exactly the unpaid debt — every
constructor arm a fresh opportunity for silent divergence from the
artifact the differential lanes validate, with no oracle for the
relation itself ('mirroring' without proof is valueless — governing
ruling 3). Everything such a rendering would buy (syntax-shaped
rules, ectx structure) is obtainable as DERIVED theorems about the
engine (candidates C/D), where disagreement is a build failure
instead of a latent soundness hole. Off target; not evaluated
further.

### 3.B The per-step ndM language, rehabilitated
(park KExpr/KStep + peel + decomposed ghost state, re-hosted on the
pinned mainline)

**What it is.** Re-land §2.4(i,ii,iii,v) over the semantics pin:
`Language KDriveExpr driver_state Empty DriveVal`, joints from the
peel, `stateInterp := CerbStInterp`, WP rules at round granularity.

- **Sanity**: high. Free-monad/ITree program-logic pattern with
  semantic atoms (named lineage in-file); observation-level bind
  algebra = ITree's eutt laws; the peel = the canonical
  big-step↔small-step simulation. All classical, all named.
- **Legitimacy**: the strongest evidenced. Soundness by construction
  (every KStep premise an `app` equation about generated code);
  completeness against the production runner PROVED
  (`ksteps_of_runND`, §2.4(i)) — a genuine two-sided
  characterization at joint granularity, within the default fuel
  budget. The mainline `runND_sound` (§2.2) independently grounds
  the bottom rung. Cost of re-derivation: mostly re-landing proved
  text against the pin (the generated loop shapes are unchanged on
  mainline — verified this session, generated/Driver.lean:346-351).
- **End-to-end adequacy statement**: PROVEN SHAPE, already achieved
  at exemplars: `CallHarnessAdequate prior tagDefs file fname args fs spec`
  = ∀ triples ∈ `CerbND.runND (callND …) (initial state)`, outcome
  is Active ∧ spec (relsemcore Call.lean; concluded from WP by
  park CerbStateAdequacy.lean:269 with byte-identical statement
  defs; exhibit M1). Quantified exclusively over cerberus-lean
  objects. Fully discharges governing ruling 3.
- **Scalability to RefinedC**: the weak axis. The expression type is
  interpreter-run-shaped; Core syntax lives inside `driver_state`
  (thread arena). RefinedC's syntax-indexed judgments
  (`typed_val_expr (e : expr)`) would have to become judgments about
  control images whose arena contains `e` (the `wpk_seq_ctl` shape)
  — a real divergence from the donor's language-based WP, and the
  reflected-syntax/bind story (port map agenda 16) has no direct
  carrier. Worse, the park discharged per-construct step premises by
  per-control-point kernel-pinned discovery (§2.4(vi)); without the
  syntactic-premise stratum, the ~55 WP lemmas cannot even be STATED
  program-generically. wp_bind: `Language.Context` at continuation
  composition (`K e := e` with extended continuation) looks provable
  (the KStep arms are continuation-parametric) but was never done —
  the park chose per-constructor lifting instead.
- **Effort shape**: re-landing = weeks-scale grinding against a
  known surface (the documented strength); the missing syntactic
  stratum is the same open cost as candidate D carries (they
  converge — see E).
- **Risks**: the fuel-non-associativity confines all composition to
  observation level (manageable, proven pattern, but every new loop
  peel pays anchor costs); walk-cost hazards measured (16-48G
  runaway if unfolding is unguarded, §2.4(iv)); the ENV component's
  Fmap coherence workaround; heartbeat-cap smells in the probe tier.

### 3.C Functional big-step characterization consumed directly
(WP over the engine's evaluation, no small-step language)

**What it is.** Take the engine-level big-step judgment —
membership in `runNDFuel`/`Behaviors` (mainline RunND.lean:302) — as
the semantic object, and define a WP for it directly (predicate
transformer over the enumeration: `wp m Φ := ∀ triples ∈ runND m σ,
…`, upgraded to an Iris assertion via the state interpretation), or
via iris-lean's `AbstractWP`/`LawfulAbstractWP` classes
(IRIS/AbstractWeakestPre.lean:24-45) rather than a `Language`
instance.

- **Sanity**: medium-high. Predicate transformers over a fueled
  definitional interpreter is classical (Dijkstra-monad /
  characteristic-formula lineage; OMKT's motivation for functional
  big-step was exactly logics-without-relations).
- **Legitimacy**: maximal by construction — the WP is DEFINED from
  the engine's enumeration; no derivation gap at all at the base.
- **End-to-end adequacy statement**: immediate — the WP's soundness
  IS the engine-only statement.
- **Scalability**: poor, and this kills it as the primary route.
  (1) Iris's invariant/atomicity machinery (masks, later credits,
  `Atomic`, the `typed_read_end/write_end` mask dance the typing
  layer needs — port map agenda 10) is built over per-step
  structure; the `LawfulAbstractWP.wp_atomic` obligation
  (AbstractWeakestPre.lean:44) still needs a `Context`/`Atomic`
  notion, i.e. a step-shaped decomposition re-enters through the
  back door. (2) Big-step WPs sequence at bind, but RefinedC's rule
  library and Lithium dispatch assume small-step-with-bind WP idioms
  throughout (wp_bind tactics, statement-WP over label maps with
  Löb for loops — `wps_block_rec` needs guarded recursion over
  steps). Loops under a pure big-step WP need fuel induction in
  every client proof or a separate fixpoint rule — a structural
  divergence from the donor with no Cerberus forcing fact.
- **Effort/risks**: cheap to stand up, expensive at every consumer;
  the divergence bin would be (c) inherited pseudo-constraint. Keep
  only as a fallback face: the big-step judgment itself
  (`Behaviors`) remains the top-level statement vocabulary for
  adequacy regardless of candidate.

### 3.D The Core-syntax step relation, derived from step_ctx
(the "one level up" relation; new work, engine-characterized)

**What it is.** The relation both surveys independently identify as
the missing native layer: a derived LTS over thread configurations,
`CoreStep : cfg → core_step2 → cfg → Prop`, DEFINED from the engine —
membership in `step_ctx cfg`'s output list plus the effect of
`advance_step`/the memory request on the state (all cerberus-lean
functions; CL/generated/Core_reduction.lean:484,
generated/Driver.lean:335). Package it as an iris-lean language:
Expr = the thread control component (arena+stack+env image — the
park's `ctlOf` decomposition names exactly this split,
park:CerbStateRA header), State = memory + supplies; `primStep` =
the CoreStep graph; labels from the dead-but-clean `one_step`
alphabet (core_reduction.lem:248). The ectx structure is native:
`get_ctx`/`apply_ctx` give `Language.Context` instances over REAL
spec functions, and W-style reflected syntax for the typing layer is
just Core's own constructor set.

- **Sanity**: high. This is OMKT's function→relation move applied at
  the level where the interpreter is already
  successor-set-and-context structured; the relation is the graph of
  spec functions, not an invention.
- **Legitimacy**: two-stage derivation, both stages owed as
  theorems: (α) CoreStep ↔ what one driver-loop round does — the
  round characterization family (mechanism C generalized from
  discovery-equation premises to syntactic-redex premises: for each
  `core_step2` class, "arena decomposes as C[redex] with head
  constructor X ⟹ step_ctx offers exactly these steps" — a
  once-per-construct theorem about `step_ctx`/`get_ctx`, currently
  NOWHERE); (β) rounds ↔ runner enumeration — the peel +
  steps-of-fuel machinery (proved at KStep granularity on the park
  branch, would need re-hosting at CoreStep granularity). Only
  after both does WP-over-CoreStep discharge into the engine-only
  statement. Disagreement anywhere is a defect in this layer by
  ruling 2 — and both stages are build-checked theorems about
  generated functions, so drift IS a build failure.
- **End-to-end adequacy statement**: same engine-only
  `HarnessAdequate`/`CallHarnessAdequate` forms as 3.B — reached
  through (α)+(β). Nothing about CoreStep survives into the final
  statement.
- **Scalability**: the best fit by far. WP lemmas per Core construct
  are STATED over syntax (`wp_pure_op`, `wp_if`, `wp_action_load`,
  `wps_run/save` for the label story — port map agenda 2's
  `save`/`run` ↔ `Goto`/label-map question gets a native carrier:
  `labeled`/`collect_saves` in core_run_state); wp_bind from
  `Context (apply_ctx C ·)`; `Atomic` for action-request steps
  (memory requests are single steps of the driver loop); the
  reflected-syntax obligation (agenda 16) collapses to Core's own
  AST. "Does this let RefinedC's next layer port literally?" — this
  is the only candidate where the answer is structurally yes.
- **Effort shape**: the largest new-proof burden: stage (α) is
  ~a-lemma-per-construct against `step_ctx`'s 12-armed dispatch and
  `get_ctx`'s decomposition (with the sequentialised-fragment
  restriction of §2.5 shrinking the context grammar to
  `Cwseq/Csseq/Cannot/Cbound` — no `Cunseq` — which is what makes
  this tractable: single-redex determinism per round, no
  interleaving fanout); stage (β) is a re-run of proven park
  machinery. Estimated shape: one hard design slice (the cfg split +
  Language instance + 3 exemplar constructs), then grinding.
- **Risks**: (1) the Expr/State split of `driver_state` is a design
  decision with sharp edges (env, supplies, fs — where do they
  live? the park's ctlOf/memRestOf split is the donor answer, but
  it was tuned for ghost decomposition, not for a Language
  instance); (2) stage (α) statements must survive the generated
  code's fuel plumbing (the measured 16-48G unfolding hazard applies
  to any ∀-state computation over these functions); (3) `can_advance`
  panics on `Step_error2` (generated/Driver.lean:310) and
  `bindExhaustive` is a documented upstream stub
  (nondeterminism.lem:104) — edge arms the characterization has to
  treat honestly (fail-noisy, scope them out explicitly); (4) the
  final-value wrinkle (`Driver.hack`, §2.1) sits between "arena
  reached a value" and `dres_core_value` — one extra
  characterization lemma family.

### 3.E Hybrid: the proven ndM spine as the adequacy trunk +
the syntax-facing stratum grown on it (B as chassis, D as interface)

**What it is.** Stage the derivation instead of choosing a level:
keep the mainline Step/runND_sound + rehabilitated KExpr
completeness + peel as the PROVED trunk connecting Iris adequacy to
the engine (all of which exists or existed green), and build D's
stage-(α) syntactic round-characterization lemmas as the WP-LEMMA
LAYER over that trunk — i.e. the ~55 wp lemmas are stated over Core
syntax ("ctl token at a configuration whose redex is X"), proved
from the generalized mechanism-C lemmas, while the Language instance
underneath remains the per-step ndM one. Whether to LATER promote
the syntax layer to its own Language instance (full D) becomes a
refactor decision taken with evidence, not up front.

- **Sanity**: high — it is exactly B's and D's named mechanisms,
  composed; no new species.
- **Legitimacy**: inherits B's proved two-sided runner
  characterization immediately; adds D's stage (α) incrementally,
  construct by construct, each lemma independently grounded (a
  wrong characterization fails against the engine in-build). No
  moment where an unproved layer is load-bearing.
- **End-to-end adequacy statement**: identical to B's — the proven
  `CallHarnessAdequate`/`HarnessAdequate` engine-only forms, from
  day one, at M1-class exemplars first.
- **Scalability**: delivers the WP-lemma stratum in syntax-facing
  form (what the typing layer needs) without betting the adequacy
  spine on the untested cfg-split design. The known cost: judgments
  are configuration-flavored (`ctl`-token premises) rather than
  donor-literal `WP e`; the port ledger must carry this as a
  divergence with the forcing fact "Core's program-in-state
  interpreter structure" — bin (b), a real Cerberus constraint —
  unless/until promotion to D erases it.
- **Effort shape**: smallest distance to a first verified exhibit
  (re-land trunk, then per-construct lemmas in priority order of the
  acceptance ladder's tutorial stem); the D-promotion option is kept
  open because stage-(α) lemmas are exactly what D's primStep
  characterization needs — no thrown-away work on either exit.
- **Risks**: B's walk-cost/fuel-algebra risks carry over; the main
  strategic risk is comfort — settling permanently into
  configuration-flavored judgments if promotion is never forced,
  drifting the typing layer from donor shape (mitigation: the
  ledger rule already prices every such divergence, and the probe
  below tests the promotion question early).

---

## 4. Recommendation

**Recommend 3.E (hybrid), with 3.D as its declared promotion
target, probed FIRST.** Reasoning:

1. Ruling 2 makes legitimacy = derivation-theorem strength, and only
   the B/E trunk has a PROVED two-sided characterization against the
   production runner plus a proved WP→engine-only-adequacy path
   (M1). Starting anywhere else re-derives that spine before any
   exhibit exists.
2. Ruling 3's end-state — adequacy stated exclusively over
   cerberus-lean semantics — is already satisfied by the trunk's
   statement forms (`HarnessAdequate`, relsemcore Cerberus.lean:268);
   no candidate improves on that statement, they differ only in what
   sits between WP and it.
3. The consumer contract's binding constraint is the syntax-facing
   WP-lemma stratum (§1.2 item 2) — the one thing NO existing
   artifact provides. That gap is identical for B, D, and E (it is
   D's stage α). E sequences it so it is built where it is needed,
   over a proved base, with the D-promotion preserved.
4. The struck candidate's lesson applies inside the layer too: every
   syntax-facing lemma must be a theorem about `step_ctx`/the round
   function, never a transcription of the Lem rule comments.

**The cheap falsification probe** (one slice, worktree-scale, no
charter needed beyond this memo's ask):

- Target: stage-(α) exemplars. Prove, over the PINNED mainline
  engine, for an ARBITRARY single-thread configuration whose arena
  decomposes as `C[redex]` with `C` unseq-free:
  (P1) redex = pure `Eif` on a boolean value ⟹
  `step_ctx` offers exactly the corresponding tau/eval step and the
  round function advances the arena to `C[chosen branch]`;
  (P2) redex = a `Paction` load ⟹ the round yields exactly a
  `LoadRequest2`-shaped action request whose continuation plugs the
  loaded value into `C`.
  Statement shape: ∀ configuration fragments (the `stateAt` family
  generalized to arbitrary arena contexts), premises syntactic only
  — NO per-instance discovery equations, no kernel-pinned ground
  side conditions.
- Falsifiers, each cheap to observe: (F1) the lemmas cannot be
  STATED at ∀-context (e.g. `get_ctx`'s recursion or the annotation
  plumbing forces context-shape enumeration) — then the
  syntax-facing stratum as imagined does not exist and D is dead as
  specified; the fallback conversation is about a restricted context
  grammar. (F2) the proofs require unfolding budgets in the measured
  runaway regime (>10 min or >16G on one lemma — the v3a hazard) —
  then representation work (control-image normal forms) must be
  chartered before the stratum, re-pricing E's effort. (F3) the
  proofs go through at sane cost — the recommendation stands and the
  same lemmas seed both E's WP layer and D's promotion.
- Secondary probe (independent, hours-scale): instantiate
  `Language.Context` for KExpr continuation-append over the
  rehabilitated PerStep, to settle whether iris-lean `wp_bind` comes
  for free on the trunk (the park never tried; §3.B).

**Operator decisions this memo surfaces but does not make** (per the
attachment-layer containment rule, scope conversation before any
brief): the §2.5 sequentialised-fragment realization (α syntactic
side condition vs β wired+validated pass); the Expr/State split if D
promotion proceeds; the drive-vs-callND entry point for the
acceptance ladder's adequacy statements; whether the ENV ghost
component survives RefinedC's locals-as-heap porting.

---

## 5. Three facts found that the port map does not record

1. **The engine runs NON-sequentialised Core, and the sequentialise
   pass is dead in Lean** (partial def, zero callers, no pipeline
   wiring; oracle lanes drop the flag too; pinned libc bodies are
   the one pre-sequentialised exception) — §2.5. The port map's
   agenda item 17 asks "which pass, pinned where"; the answer is
   "none is wired anywhere", which converts the item from a pin
   choice into an α/β design decision.
2. **The mainline already carries a proved derived relational spine
   with engine-only adequacy statement forms** (relsemcore:
   `Step`/`Steps`, `runND_sound` against the production runner,
   `HarnessAdequate`/`ExecModel`) — §2.2 — and this repo's iris-lean
   pin (34390a01) is byte-identical to the rev the park's `Language`
   instance and WP/adequacy stack were proved against, so
   rehabilitation has no interface-migration cost.
3. **The final value is computed, not read**: `finalize` runs
   `Driver.hack` (a second fueled evaluator) over the final arena to
   produce `dres_core_value` — every adequacy postcondition about
   results must be characterized through it. Adjacent engine facts
   in the same class: the Lean runner does no constraint pruning
   (both `NDbranch` arms, guards pass — behavior superset, which
   strengthens ∀-behavior adequacy but must be scoped in any
   `CsSem.ofEval`-style claim), and `can_advance` panics on
   `Step_error2` (fail-noisy edge the characterization must scope).

## 6. Open questions (listed, not guessed)

- Does elaboration of the tutorial-stem C programs emit `Eunseq`
  outside the `Ewseq/Esseq`-head shape the pass handles (i.e. how
  restrictive is realization α in practice)? Answerable by running
  the pinned engine over the acceptance-ladder C files and counting
  arena `Eunseq` occurrences — worth doing before the §2.5 decision.
- Is `Language.Context` provable for KExpr continuation-append
  (secondary probe, §4)?
- Can the `Atomic` instances for action-request rounds be stated so
  the typing layer's mask dance (agenda 10) ports — i.e. is one
  driver round genuinely atomic in the iris-lean sense over the
  chosen Expr/State split?
- Which of the park's six ghost components survive contact with
  RefinedC's substitution-everywhere locals story (agenda 7)? The
  salvage map flags ENV as possibly unnecessary; unverified.
- The `runEffectful` axiom's reach into the exec cone consumed by
  the relational layer (the park audit carried it as a boundary
  entry; M1's pin is trio-only, suggesting the callND cone avoids
  it — NOT verified for `drive`'s cone this session).
