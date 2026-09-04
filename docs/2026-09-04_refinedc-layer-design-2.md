# The RefinedC-family layer over cerberus-heaplang — design note 2 (Lane C)

**Status: DRAFT design note for operator discussion, [AGENT 2026-09-04],
read-only.** No build was run; nothing here is built or a ruling. Every
claim about our tree is a `file:line` reading of the worktree
`design-c2` at `0534f9a` (= `main`), of the pinned semantics workspace
`.cerberus-ws/lean_frontend/generated/` (cerberus-lean `f95ef8d9c`,
`scripts/semantics-pin.env`), or of the Cerberus `.lem` sources at
`../cerberus-lean/frontend/model/`; every RefinedC claim cites
`deps/refinedc/theories/<file>.v:line` or `deps/refinedc/frontend/<file>.ml:line`
(RefinedC is BSD; read-only). "DERIVED" marks a tally I computed from
readings; "estimate" marks a sizing guess. Decisions below are [AGENT];
the operator is offline; §7 lists what needs the operator.

Supersedes for planning purposes the Lane C spike
`docs/2026-09-03_refinedc-layer-design-spike.md` (now on branch
`refinedc/dev`, off `main` since `24c2410`), which predates: the calls
arc (procedure specifications, the call rule, recursion through the one
Löb — CLAIMS C9), the fuel-lane restatement F1 (`DriverSafeCtl`/
`DriverDoneCtl` over the genuine driver — ARCHITECTURE §2.4), the 50-row
rule-use manifest (ARCHITECTURE §5), the [USER 2026-09-04] rulings that
close the demo's feature set and move masks and function pointers to
this arc (DECISIONS "THE DEMO'S SCOPE, RESTATED"), the fuel-parameter
design and our review of it (`docs/2026-09-04_review-of-fuel-parameter-design.md`),
and the external audit (`docs/2026-09-04_reynolds-ohearn-separation-logic-audit.md`).
The spike's §1 (types as predicates over the raw assertions), §2 (the
judgment shape), §4 (the executor) and §6 (the port ledger) stand where
this note does not amend them; its §3 and §5 are replaced by §3–§5 here.

Governing rulings applied throughout: ADOPT ONLY THE SLICE OF RefinedC
THAT SERVES AGENT-DRIVEN VERIFICATION AT SCALE ([USER 2026-09-03],
DECISIONS:882); RefinedC's DESIGN IS A TIEBREAKER, NOT A CONSTRAINT
([USER 2026-09-02], DECISIONS:967); THE ROOT PACKAGE'S RAW LOGIC IS A
COPY ([USER 2026-09-03], the Lane B seed pattern); the north star
"boring specs at scale + the most aggressive proof automation ever"
(DECISIONS:52–83); the trust architecture (CLAUDE.md: the engine is the
only semantics; no hand-written definition in an export's statement).

## 0. The six recommendations, one line each

1. **Build on**: `wps`/`wpt` with `Θ : ProcSpec` and the call rules, the
   label-context frame, `DriverSafeCtl`/`DriverDoneCtl` and the closed
   forms, exactly as listed in §1 — in a COPY grown by Lane B, seeded
   only after the re-pin and the fuel restatement land (one rewrite, not
   two); one demo-shape finding: `ProcSpec` cannot state a specification
   whose logical variable is not determined by the argument values (§1.4),
   so RefinedC's `fn_params` shape is the first change the copy makes.
2. **Masks**: the first four slices need no mask generalisation; shared
   READ-ONLY references are fractional/discarded ownership the demo
   already has, not invariants; generalise `wps`/`wpt` over `E` only at
   the slice that introduces the first invariant-backed type (atomics,
   locks), sized in §2 at 3–5 worker-days.
3. **Function pointers**: `Eccall` is processed by the scheduler round
   (`Step_ccall2` is not advanceable by the per-thread loop), so this is
   the slice that lifts adequacy from the per-thread loop to `driver2`
   and makes the outer fuel quantifier do work; state the layer's closed
   forms in the "every outcome in the run's outcome list" shape from
   birth; the mirror's obligation is one `Step.ccall` rule plus a
   persistent `funptrmap` coupling; 2–3 worker-weeks, after the fuel
   restatement (§3).
4. **Annotations**: verify LOCATED Core directly (make `current_loc`
   live state — the mover Soundness.lean names); erasure would put a
   hand-written function between the theorem and the C program, which
   the referent rule forbids; specs are Lean values keyed by function
   symbol, loop invariants keyed by label found through the located
   node; the only C-side annotation is an optional name marker that
   Cerberus already carries to Core as `Aattrs`; no cerberus-lean request
   is required (§4).
5. **The slice**: types as spec vocabulary (`int`, `&own`, `null`,
   `uninit`, `struct`, `array`, `optional`, `∃ₜ`, `value`), the
   syntax-directed judgment shape over `wps`, `fn_params`-shaped
   procedure specs through `procSpecs`, and a Lean 4 goal-directed
   executor implementing Lithium's ALGORITHM (committed choice, atom
   matching, leave-the-side-condition) over our rules; not Caesium, not
   their memory model, frontend, concurrency, `mem_cast`, `Shr`/`Copyable`
   for now; four slices with acceptance tests in §5.5.
6. **Shared library**: yes, for exactly the fragment-INDEPENDENT,
   trust-bearing coupling (≈ 8k lines DERIVED: `Heap`'s ghost carrier +
   `CohG` + `MemWF` + bundles + engine-memory lemmas, `EnvLaws`, the
   machine context, the ND/driver collapse's generic half, the cold
   start) — the demo becomes its regression suite at zero cost, as the
   operator observes — but as an INTERNALS-ONLY extraction slice AFTER
   the demo's v1 tag, never as the first move; (b)/(c) stay copies by the
   standing ruling (§6).

## 1. What the layer builds on, exactly

### 1.1 The judgments and rules it consumes

| Surface | Theorem / definition | Where | What the layer does with it |
|---|---|---|---|
| Partial judgment | `wps M p Ls Θ Ψ e ρ` — guarded fixpoint of `wps.pre` (value / jump / call / step clauses) | `Wps.lean:301`, pre `:217` | `typedStmt` is `wps` at a typed post (spike §2) |
| Label specs | `LabelSpec GF := sym → List value → EnvStack → IProp GF` | `Wps.lean:113` | loop invariants are label preconditions; `typed_block` (programs.v:72–73) maps onto an `Ls` entry |
| Procedure specs | `ProcSpec GF := sym → List value → IProp GF × (value → IProp GF)`; `emptyProcSpec` | `Wps.lean:129`, `:136` | the table `Θ` is a PARAMETER of the judgment; §1.4 finding |
| Call rule | `wps_call` (at `callRedex?`), `wps_call_root` (at `Eproc … (Sym f)`) | `Wps.lean:417`, `:473` | `typed_call` (programs.v:117–118) becomes `wps_call_root` at a typed table entry |
| Procedure rule | `procSpecs M Θ` (abbrev), `procSpecs_intro` — one body proof per declared procedure assuming the table, no Löb | `Wps.lean:3269`, `:3287` | `typed_function` (function.v:59–66) becomes one `hW` obligation |
| Loop rule | `blockSpecs_intro` | `Wps.lean:3195` | the donor's `wps_block_rec` job |
| Frame | `wps_frame`, `wps_frame_labels` (frames the label specs too, via `frameLs`) | `Wps.lean:670`, `:701` | the executor's frame is free by the rule shape (R2) |
| Atomic lifting | `AtomicStep` (mask-generic), `wp_of_atomic`, `wps_of_atomic`, `wpt_of_atomic` | `Rules.lean:194`, `:210`; `Wps.lean:345`; `Wpt.lean:664` | every typed small axiom is a corollary of a `*_plain` rule, itself a corollary of these |
| Memory rules used first | `wps_store_plain`, `wps_load_plain` (posts `AnnotInsensitive`), `wps_store_at`/`wps_load_at` (sub-range), `wps_create`, `wps_kill`, `wps_alloc`, `wps_free` | `Wps.lean:2577`, `:2598`; `AnnotInsensitive` `Wpt.lean:2822`; CLAIMS C10 | `typed_read_end`/`typed_write_end` (programs.v:174–189) |
| Control rules | `wps_seq` (`:1159`), `wps_if` (`:1521`, verdict by `evalPexpr` inside the logic), `wps_save` (`:1677`), `wps_run` (`:381`), `wps_pure` (`:1745`) | `Wps.lean` | the executor's dispatch table |
| Total judgment | `wpt M p Ls Θ k Ψ e ρ`, `LabelSpecT` (variant-indexed), `ProcSpecT` (budget-indexed), `wpt_call`, `procSpecsT_intro` | `Wpt.lean:200`, `:98`, `:108`, `:726`, `:3032` | the total lane, kept for the closed total statements; the layer's first slices are partial |
| Collapses | `wps_sound_cps` (the one Löb), `wps_sound`/`wps_sound_empty`; `wpt_sound_cps` | `Wps.lean:3440`, `:3637`/`:3657`; `Wpt.lean:3173` | consumed only by Iris-level readouts (ARCHITECTURE §2.1 table); the driver lanes run their own inductions |

### 1.2 The adequacy it inherits

| Statement | Where | Shape the layer inherits |
|---|---|---|
| `DriverSafeCtl M₀ th₀ e ρ ctl σ ψ` | `Adequacy.lean:932` | ∀ driver state holding the configuration, ∀ inner fuel `fl`: `runOne (drive_nonmemory_steps_aux2_lemFuel fl …) dst` is the exhaustion kill or PROGRAM-DONE with `ψ v σfin`; nothing else |
| `engine_adequacy` (+ `_alloc`) | `Adequacy.lean:1278` | from `hwp` (the Iris derivation at `⊤`) and the premises of §1.3 to `DriverSafeCtl` |
| `MemTriple` / `project_triple_pure` | `Adequacy.lean:1518`, `:1605` | the Iris-free frame-preserving triple over the loop |
| `DriverDoneCtl … k` / `wpt_driver_done_procs` | `ProdLoop.lean:456`, `:799` | PROGRAM-DONE within `k + 2` iterations, through PCALL/RETURN |
| `prod_run_eqJ_procs` | `ProdEntry.lean:716` | the shipped composite `runND (drive fmapEmpty false (prodFileWith procs e) args) (initial_driver_state …).1 = [(Active dres, [], dst')]`, premise `k + 2 ≤ CerbFuel.driverFuel` |
| `prod_run_safe_procs` | `ProdEntry.lean:768` | the closed PARTIAL form at every `drive_lemFuel fuel`: exactly one execution, exhausted or delivered with `ψ` |

The layer's whole-program theorem is `prod_run_safe_procs` (and its
total twin) at a file whose `main` and procedures come from the C
front end and whose `Θ` is Lean-authored — the shape the spike's §3
`program_adequate` sketched, now with the calls arc's actual names.

### 1.3 The premises every export carries, and what each means for C

From `engine_adequacy` (`Adequacy.lean:1278`–`:1296`) and
`wpt_driver_done_procs` (`ProdLoop.lean:799`–`:809`), read in
ARCHITECTURE §4:

- `htd : M.tagDefs = fmapEmpty`, `hex : M.extern = fmapEmpty` — no
  struct/union TAG DEFINITIONS in any proved configuration (KOI B4).
  For C this is the first wall: every C program with a `struct` type
  has a non-empty tag-definition table (`sizeofCtype`/`offsetsof` read
  it — Heap.lean header, "THE TAG-DEFINITION ENVIRONMENT"). The
  assertions are already indexed by `tds`; the premise is on the
  ADEQUACY lanes (the production driver runs `drive fmapEmpty false …`
  for the synthetic file, ARCHITECTURE §4). Lifting it means the closed
  forms take the file's own `tagDefs` — a Lane B slice ("compiled Core"
  = the first item of the THREE LANES ruling, DECISIONS:873–881).
- `hκ : ctl.κ = []`, `hfrag : Frag e`, `hQf`, `hPf : M.FragProcs`
  (`Adequacy.lean:767`: every declared body in `Frag` within the
  potential bound) — the program and every procedure body must be in
  the fragment.
- `hpot : pot e ≤ lemDefaultFuel`, `hQpot`, `FragProcs.potBound` — the
  static fuel premises (KOI A1); §1.6.
- `hcl : th₀.current_loc = M.currentLoc` — the annotation-free
  invariant (§4).
- `hcoh : Coh …` / `hl : LaunchCoh … B` — the footprint, plus `MemWF`
  and the budget fit for allocating programs (ARCHITECTURE §2.6).
- `hwp` — the Iris derivation, at the top mask (§2).

### 1.4 A demo-shape finding: `ProcSpec` has no logical-variable index

`ProcSpec GF := sym → List value → IProp GF × (value → IProp GF)`
(`Wps.lean:129`–`:130`). The call clause consumes `(Θ f vs).1` and
resumes at `(Θ f vs).2 ret` (`Wps.lean:233`–`:241`; the rule
`wps_call`, `:417`–`:419`); the introduction verifies each body from
`(Θ f vs).1` to `(Θ f vs).2 w.val` (`procSpecs_intro`, `:3287`–`:3297`).
The only data a pre- and postcondition can SHARE is therefore the
argument value list `vs`. A specification of `reverse(p)` — "`list p xs`
before, `list ret (rev xs)` after" — cannot be stated: `xs` is not an
argument value, and `pre := ∃ xs, list p xs` / `post := fun ret => ∃ xs,
list ret (rev xs)` loses the connection. The demo's two call exhibits
never meet this because `fib`/`even`/`odd` are specified by their
integer argument (`FibRecExhibit`, `EvenOddExhibit`; `csSpec` in
`Examples/CallSmoke.lean` is `{0 ≤ x} f(x) {ret = x + 1}`). Labels do
not have the problem: a jump only ESTABLISHES `Ls l vs ρ`, nothing
returns.

RefinedC's shape is `A → fn_params` with `fp_rtype` for the return's
existential (function.v:39–51, the comment "∀ x : A, args ◁ᵥ fp_atys ∗
fp_Pa → ∃ y : fp_rtype, ret ◁ᵥ fr_rty ∗ fr_R"). Two ways to get it:

- (i) **Judgment change in the copy** (recommended, [AGENT]):
  `ProcSpec GF := sym → List value → Σ (A : Type), (A → IProp GF) × (A → value → IProp GF)`
  (universe-polymorphic or `A : Type`), the call clause `∃ x, pre x ∗
  ▷ ∀ ret, post x ret -∗ F …`, the introduction `∀ x, pre x ⊢ wps … (post x) body`.
  The tiebreaker rule says adopt their shape when free; it is the
  classical Hoare rule for procedures with logical variables; `wps_call`,
  `procSpecs_intro`, the collapse's call case and `wpt`'s twins change
  text — a judgment change, so it is a Lane B slice on the COPY, not a
  demo change (the demo's feature set is closed; `emptyProcSpec` and the
  two exhibits survive at `A := Unit`).
- (ii) **Layer-derived** with a ghost variable: iris-lean ships
  `Iris/Instances/Lib/GhostVar.lean` and `SavedProp.lean`; the call
  clause has a `|={⊤}=>` prefix (`Wps.lean:234`) under which a fresh
  `γ` can be allocated, `pre := ∃ x γ, pre x ∗ ghost_var γ ½ x`, the
  caller keeps the other half and recovers `x` by agreement at the post.
  No judgment change, but the layer's ghost functors must extend the
  demo's `SpikeGpreS GF` (`Heap.lean:2402`), and every spec carries
  ghost plumbing the agent sees. Rejected as the default; kept as the
  fallback if (i) is refused.

### 1.5 The fragment boundary and the fifteen NO-RULE variants

`Frag e` (`Soundness.lean:4149`, 23 constructors) is annotation-free
(`:4129`–`:4147`), the plain-symbol binder's head is `BareHead`
(`:3981`), and `Frag.case_value` carries `hbsz` (`:4296`). The 15
NO-RULE variants (ARCHITECTURE §6 table; KOI B14) constrain the C shapes
verifiable today; read against C:

| NO-RULE variant | C shape it excludes | For the layer |
|---|---|---|
| the locking store `Store0 true` | the store that makes an object read-only (the engine flips `isReadonly`, `Frag.store` docstring, `Soundness.lean:4151`–`:4163`) — whether the C elaborator emits it for `const`-qualified objects is NOT measured here (§7 Q7) | a `readonly` stratum rule (`readonlyCell` exists, `Heap.lean:3683`; `load_atomic_readonly` exists, no statement rule) |
| a load at a read-only object | reads of `const` data | same stratum; the natural `&shr`-for-immutables (§2) |
| union-member pointer store/load/kill | C unions | out of scope for the first slices |
| whole-object access at an atomic-typed allocation; `create` of an atomic type | `_Atomic` | out (concurrency) |
| `create` of a zero-size type; of a non-decode-inert type | zero-size objects; types whose unspecified image decodes to something | the `uninit` type former must carry decode-inertness as a side condition |
| static kill of a live region; `free(NULL)`; the colliding `free` (KOI A3) | `free` of automatic storage (UB in C anyway); `free(NULL)` (a legal no-op in C — a rule is a spec addition: `{emp} free(NULL) {emp}`) | `free(NULL)` is the one a C corpus hits; queue it |
| the zero-cost `alloc` | `malloc(0)` | low |
| `PtrEq` at an `SD_Id`-named function pointer vs a concrete pointer | comparing function pointers | with §3 |

The OUT-OF-SCOPE rows (a jump with a non-evaluating surplus argument;
`pure(x)` at a `Proc`-named unbound symbol; the annotated head at the
symbol binder; `PtrEq` across provenances — the engine forks; the `Impl`
call) are the mirror's stated absences, unchanged by this note.

What compiled Core needs beyond `Frag` (spike §5 and §7, still true, by
the fragment-closure record): `Ebound`, `let weak`, `Eunseq`, `Ecase`
truthiness, stdlib pexpr calls (`conv_loaded_int`, `params_length`,
`are_compatible`), member shifts, `kill` of every local. These are Lane
B's fragment-growing slices; the layer's rules are per constructor, so
nothing it builds on hand-written fragment Core is thrown away.

### 1.6 What the fuel-parametric semantics changes for the layer

Per our review (`docs/2026-09-04_review-of-fuel-parameter-design.md` §1,
§5): one ambient `[LemFuel]` class, every fuel'd call starting from the
full ambient, generated `_zero` lemmas, numerals deleted. Consequences
for this layer, [AGENT]:

1. Every statement of the layer that mentions an engine function is
   generic in `[LemFuel]` because the rules it derives from are; the
   layer adds no fuel reasoning of its own. The `≤ lemDefaultFuel`
   premises become `≤ LemFuel.fuel` (the review's §5 count: ~60 sites in
   the demo; the layer inherits them through `FragProcs.potBound` and
   `hpot`).
2. The closed partial form becomes genuinely `∀ [LemFuel]` over BOTH
   loops (KOI A2 closes) — this is exactly what §3 needs: with `Eccall`
   the outer loop is live and its fuel must be quantifiable, which today
   it is not (`new_drive_core_threads` calls the per-thread loop through
   the fixed wrapper, ARCHITECTURE §4).
3. The layer's automation must never mint a `LemFuel` instance (the
   review §1.1 hazard); our gate grep extends to the layer package.
4. Sequencing: the copy the layer builds on must be seeded AFTER the
   re-pin (KOI A6) and the fuel restatement land in the demo, or the
   layer's raw-logic base is rewritten twice (the LANE B PAUSED
   amendment already says "re-seeded from the demo head of that day",
   DECISIONS:1010–1020). Estimated wait per the review §5 and the scout:
   one slice after the LemLib re-pin (2.5–4 worker-days for the re-pin,
   then the restatement).
5. The truth condition (review §2): every fuel'd function reachable
   from `drive` must be (A) data-measure recursion, (B) absorbing typed
   exhaustion, or (C) unreachable. The layer's whole-program `∀ fuel`
   theorem is FALSE at small fuels if any opaque-default exhaustion
   survives on the path; the layer inherits that requirement and adds
   none.

## 2. Masks

### 2.1 What RefinedC's type system uses masks for

Measured in the donor: (a) SHARING — `ty_share l E : ↑shrN ⊆ E →
ty_own Own l ={E}=∗ ty_own Shr l` (type.v:268), with `Shr` ownership of
a location being `inv mtN (∃ q, (l +ₗ i) ↦{q} [b])` per byte (type.v:136)
and `Copyable`'s read protocol requiring `mtE ⊆ E` (type.v:367–373);
`&shr := frac_ptr Shr` (own.v:366). (b) ATOMICS — `typed_read_end`/
`typed_write_end` take `E` and an `atomic` flag with `E' := if atomic
then ∅ else E` (programs.v:174–189). (c) THE FUPD AT RETURN AND IN
SUBSUMPTION — `fn_ret_prop`'s `‖={⊤}=‖` (function.v:53–54), `subsume
P1 M P2 T := P1 -∗ ‖M‖ ∃ x, P2 x ∗ T x` (definitions.v:220). The donor's
own header discusses and rejects a fractional `own_state` for GUARDED
types (type.v:13–60, the comment block); its `Shr` is invariant-based
because Caesium's heap points-to is not fractional at the type level.

### 2.2 What our judgments have

`AtomicStep` is mask-generic (`∀ E₁ E₂, E₂ ⊆ E₁`, `Rules.lean:194`–`:206`)
and `wp_of_atomic` lifts at any `E` (`:210`–`:214`). The statement
judgments fix `⊤`: `wps.pre`'s value/jump/call clauses are under
`|={⊤}=>` and its step clause transitions `={⊤,∅}=∗ … ={∅,⊤}=∗`
(`Wps.lean:224`–`:245`); `wpt.pre` likewise (`Wpt.lean:160`–`:180`);
`wps_of_atomic` instantiates `E₁ := ⊤, E₂ := ∅` (`Wps.lean:359`); the
collapses conclude `WP … @ NotStuck; ⊤` (`Wps.lean:3445`–`:3447`). Count
of `⊤` occurrences: 21 in `Wps.lean`, 26 in `Wpt.lean` (DERIVED,
`grep -c`, docstrings included; ARCHITECTURE §1 reports 19 + 26 code
sites; KOI B11 says 21 + 26).

The demo's ownership is `DFrac` (`pointsToCell tds pv dq ty bs`;
`cellOwn_fractional`, `pointsToView_fractional`; persistence by
`.discard` — Heap.lean header, "THE THREE ALLOCATION FACTS" 1–2) and the
load rules hold at any fraction (`wps_load_at`; CLAIMS C10 "load at any
fraction").

### 2.3 Recommendation: none of it for the first four slices

- **Shared IMMUTABLE references need no invariant here.** RefinedC's
  `&shr ty` in the BSD examples is overwhelmingly read-only sharing of
  data (function-pointer tables, read-only structs). Over our
  assertions, `p ◁ₗ{.discard} ty` — the discarded fraction of the byte
  and metadata cells — is persistent, supports loads by the existing
  rules, and forecloses kills (Heap.lean header, fact 2: "Persisting is
  FINAL"). That is `Shr` for immutable data with no mask, no `shrN`, no
  `▷`. Design consequence: the layer's ownership index is `DFrac` (spike
  ledger 1 stands), with `&own := ◁ₗ{.own 1}` and `&shr := ◁ₗ{.discard}`
  as notations. What this does NOT give: RefinedC's `Shr` on mutable
  shared state (`Lock`, `atomic_bool`, `locked.v`) — those need
  invariants and therefore masks.
- **Atomics are NO-RULE today** (§1.5) and concurrency is outside the
  fragment (KOI B8): the `atomic` flag's `∅` mask has nothing to attach
  to.
- **The fupd at return/subsume is available at `⊤`**: the call clause's
  `|={⊤}=>` prefix (`Wps.lean:234`) already admits a ghost update at the
  call; the typed post can be stated with `|={⊤}=>` inside `Ψ`.

Therefore [AGENT]: the mask generalisation is scheduled at the FIRST
slice that introduces an invariant-backed type former (a lock, an
atomic flag, a shared MUTABLE reference) — none of which is in §5's
first four slices. It is not "possibly forever" (unlike KOI B9): the
Linux-scale north star has spinlocks (`deps/refinedc/examples/spinlock.c`,
`lock.c`, `latch.c` exist in the donor corpus) and the audit's F3 is
correct that top-mask-only judgments cannot nest inside a larger Iris
development.

### 2.4 The minimal generalisation, sized (for when it comes)

- `wps.pre`/`wpt.pre` gain `(E : CoPset)`: the three `|={⊤}=>` become
  `|={E}=>`, the step clause `={E,∅}=∗ … ={∅,E}=∗`; `wps M p Ls Θ` →
  `wpsE E M p Ls Θ` with `wps := wpsE ⊤` an abbreviation (the audit's
  remedy; the classic interface survives textually).
- Rules that need `E`: `wps_of_atomic`/`wpt_of_atomic` (they already
  take a mask-generic `AtomicStep`; instantiate `E₁ := E, E₂ := ∅`); the
  frame and consequence rules (mask-generic by construction); the label
  and procedure specs stay mask-free (they are entered under the
  judgment's own `|={E}=>`); `wps_call`/`wpt_call` unchanged in text
  modulo `E`. The `*_plain` memory rules are corollaries and follow.
- Collapse and adequacy: `wps_sound_cps`'s `WP … @ ⊤` becomes `@ E`;
  `engine_adequacy`'s `hwp` stays at `⊤` (adequacy needs the full mask);
  so the entry points instantiate `E := ⊤` and change no export text.
- A regression test: allocate an invariant in a namespace `N`, prove a
  `wpsE (⊤ \ ↑N)` store, close the invariant (the audit's suggested
  test).
- Size: an internals + statement-shape slice over `Wps.lean` (3700
  lines) and `Wpt.lean` (3411 lines), touching every rule's statement
  by one binder with a default — comparable to the C3 calls slice's
  "judgment indexed by a new parameter" shape (DECISIONS C3 entries).
  Estimate 3–5 worker-days plus its range audit. Because it is a
  statement-shape change it happens in the COPY (Lane B), not the demo.

## 3. Function pointers, and the scheduler that stops being degenerate

### 3.1 The engine facts (pinned tree)

- `Eccall : a → pexpr → pexpr → List pexpr → generic_expr_` (Core.lean:1217).
- `step_ctx`'s arm `Eccall call_annots _ pe pes` (Core_reduction.lean:484,
  the substring beginning `Eccall  call_annots  _  pe  pes =>`): the
  function-type operand is `_` (unread); `pe` must evaluate to
  `Vloaded (LVspecified (OVpointer pv))`; the callee is
  `caseFunsymOpt mem_st pv` (CerbMem.lean:1237–1245: a `PVfunction s` is
  `some s` directly; a `PVconcrete _ addr` is looked up in
  `st.funptrmap`; anything else `none`), `none` being the typed kill
  `UB_CERB003_invalid_function_pointer`; then `call_proc core_extern1
  file1 psym cvals` and the same thread update as `Eproc` — but wrapped
  as **`Step_ccall2 current_tid (…)`**, not `Step_with_runstate2`.
- `core_step2` (Core_reduction.lean:224): `Step_ccall2 : thread_id →
  core_runM thread_state → core_step2` (`:227`).
- The per-thread loop does NOT advance it: `can_advance (Step_ccall2 _ _)
  = false` (Driver.lean:310) and `advance_step`'s arm is `nd_return
  NOWAKEUP` (Driver.lean:336). Like `Step_done2`, it is returned in the
  step map to the scheduler.
- The scheduler processes it: `process_core_step2`'s arm
  `Step_ccall2 tid1 step_m => liftCore_run step_m >>= fun th_st' =>
  nd_update (dr_step_counter + 1; core_state0 := update_thread_state
  tid1 th_st' …) >>= driver21 with_concurrency` (Driver.lean:377) — one
  `driver2` round per C call, then `driver2` re-enters
  `new_drive_core_threads` (Driver.lean:355), whose per-thread loop
  runs from the FIXED budget wrapper (ARCHITECTURE §4, the reason KOI A2
  exists).
- The mirror has `Eccall` outside `Frag` (KOI B8; `callRedex?` answers
  `none` for anything but `Eproc _ (Sym f)`, `Step.lean:703`–`:711`).
- Function pointers as VALUES: `PVfunction sym` (CerbMem.lean:49);
  storing one registers `(addr, (fileDig, name))` in `funptrmap`
  (`memValueToBytes`, CerbMem.lean:621–632, replace-or-insert) and
  loading one looks it up (`reconstructValue`, `:730`–`:737` per the
  spike §1.2). The demo's `StorableAt`/`decIndep` exclude `PVfunction`
  images (spike §1.2; Heap.lean:179, :1501 per the spike).

So: [USER 2026-09-04] "function pointers belong in the refinedc arc" is
also the point where the scheduler loop is on every proved path.

### 3.2 What the closed statements become

Today (ARCHITECTURE §4, the ruled reading [USER 2026-09-03]): the
triple's semantics is the THREAD-level statement `DriverSafeCtl` (inner
loop, ∀ inner fuel); the outer `driver2` runs one round for the
sequential fragment; the closed forms' `fuel` quantifies the outer loop
only and "does no work" (KOI A2); the singleton EQUATION
`runND … = [(st, [], dst')]` is the sequential strengthening of the
intended "for every outcome in the run's outcome list" (KOI B5).

With `Eccall` in the fragment:

1. **The thread-level fact gains a stopping arm.** `DriverSafeCtl`'s
   dichotomy (exhaustion ∨ PROGRAM-DONE) becomes a trichotomy: the
   per-thread loop returns with a `Step_ccall2` singleton at a C call
   site, at a configuration the logic characterises (the callee resolved
   under the spec table, the continuation captured). Call it
   `DriverSafeSeg` (a SEGMENT of the run between scheduler rounds).
2. **A new lane above it: the scheduler induction.** `SchedulerSafe`
   says: at every outer fuel, `driver2` from a state whose single thread
   is in the fragment either exhausts (outer or inner fuel — both are
   the kernel-transparent `fuelExhaustedKill` by the fuel arc's
   `_zero` lemmas, DriverCollapse header "FUEL"), or terminates with
   PROGRAM-DONE and the readout, or — no other outcome. Its proof is an
   induction on the outer fuel, each round being: a `DriverSafeSeg`
   segment (the existing per-thread induction, `drive_safe_aux`,
   `Adequacy.lean:1079`), then either PROGRAM-DONE (`driver2_done`,
   DriverCollapse) or one `Step_ccall2` round (a NEW round lemma
   `ccall_round`, proved by unfolding `process_core_step2`'s arm exactly
   as `loop_step_frag` unfolds the loop — the same discipline, one more
   arm) followed by the induction hypothesis at the callee's
   configuration. The total lane's twin adds the ccall rounds to the
   budget: `1 + m + k' ≤ k` (`Wpt.lean:172`) already has the shape; the
   ccall costs one outer unit and one inner restart.
3. **The outer fuel quantifier does work.** Each `Eccall` spends one
   `driver2` unit, so the outer `∀ fuel` now excludes runs with more C
   calls than fuel — a real exhaustion outcome, admissible in the
   partial form, bounded in the total form (the count of C calls along
   the run, which the spec table's budgets make computable). This is
   precisely why §1.6's item 2 must land first: with the inner loop at a
   fixed wrapper budget the statement "∀ outer fuel" is true but the
   inner exhaustion is not quantifiable, and `prod_run_safe_procs`
   cannot be restated over both loops.
4. **The closed form: the outcome-list shape from birth.** The layer's
   whole-program theorem should be stated as
   `∀ o ∈ CerbND.runND (drive_lemFuel … file args) (initial_driver_state …).1,
    o.1 = Killed _ fuelExhaustedKill ∨ (∃ dres, o.1 = Active dres ∧ ψ …)`
   (plus non-emptiness), NOT as the singleton equation. Sequential
   `Eccall` is still deterministic (the ccall round is `nd_return
   NOWAKEUP`, no fork), so the equation remains PROVABLE as a corollary;
   but the outcome-list form is the one that survives concurrency and
   external C calls ([USER 2026-09-03] "the scheduler … becomes live
   under concurrency or external C calls"). Stating it now costs one
   lemma (`runND_active` gives the singleton list; membership is
   immediate) and saves a restatement later. The demo keeps its
   equations (feature set closed; KOI B5's doc note is its mover).

### 3.3 The mirror's obligation (ours, not cerberus-lean's)

- `Step.ccall`: `Eccall _ _ pe pes` at `PePure` operands, premise
  `evalPexpr … pe = some (Vloaded (LVspecified (OVpointer pv)))`,
  `caseFunsymOpt σ pv = some f` (reads `σ.funptrmap` — a MEMORY read,
  so the rule is action-like, not pure), `lookupProc M.file M.extern f
  = some (params, body)`, arity, then the same successor as `Step.call`
  (`Step.lean:2047`–`:2056`). Its certification is NOT an
  `engine_step_matchU` instance in the current sense (that theorem
  states the engine's step list is a `Step_with_runstate2`/tau/action
  singleton advanced by the loop): it needs a sibling statement
  "the step list is `[Step_ccall2 tid m]` and `liftCore_run m` yields
  the successor thread" — the `ccall_round` of §3.2.
- Completeness (`frag_round_complete`, `Round.lean:5369`): one more
  `complete_ccall` lemma; the refusal `UB_CERB003_invalid_function_pointer`
  is a KILL classification (`ShippedRefusal.killed`), the ill-typed
  first operand is `failwithI` (PANIC family) — both already have
  vocabulary.
- The coupling: a persistent ghost fact `funPtr a f` ("address `a`
  denotes function `f`") coupled to `funptrmap` in `CohG`
  (`Heap.lean:2632`); stable because `funptrmap` is replace-or-insert at
  a symbol's own number (CerbMem.lean:626–630) and is never cleared
  (the only writer found is `memValueToBytes`; `killM` does not touch it
  — to be re-verified at implementation). `StorableAt`/`decIndep` gain
  the `PVfunction` case under that fact. `MemWF` may need a
  `funptrmap` component (keys are function-symbol numbers, not
  allocation addresses — check disjointness from `dynamicAddrs`/live
  ranges is not needed; to measure).
- The logic: NO `fntbl_entry` ghost map (caesium/ghost_state.v:118–125)
  is needed. RefinedC's `function_ptr_type fp f` is `∃ fn, l ↦ f ∗
  fntbl_entry f fn ∗ ▷ typed_function fn fp` (function.v:106–109)
  because Caesium locates functions by address; ours are file symbols
  and `Θ` is a parameter, so the VALUE type is
  `v ◁ᵥ fnptr sp := ∃ f, ⌜v = ptrVal (PVfunction f)⌝ ∗ ⌜Θ f = sp⌝` for a
  symbol-valued pointer, and `∃ f a, ⌜v = concrete a⌝ ∗ funPtr a f ∗
  ⌜Θ f = sp⌝` for a stored-and-reloaded one. The `▷ typed_function`
  under the pointer is our `procSpecs` premise, discharged once at the
  collapse (the one Löb) — spike §3's design point D1, now confirmed by
  the engine reading. The typed call rule is `wps_call`'s shape with
  the resolution premise moved into an atomic-step-like precondition.
- The spec table for a C program is keyed by the C function's symbol;
  `SD_Id name` symbols reconstructed from `funptrmap`
  (CerbMem.lean:1243) compare by `ordCompare` on (digest, number) — the
  `EnvLaws` finding that comparator-equal symbols may differ in
  description (`EnvLaws.lean` header, item 1) applies to `lookupProc`
  through a reconstructed symbol; to measure.

### 3.4 Size and sequence

Mirror + `Frag` + certification + completeness for one constructor
(≈ the C2 slice), the `ccall_round` and the `SchedulerSafe` induction
(a new lane the size of `drive_safe_aux` + `driverDoneCtl_step`), the
`funPtr` coupling (a `CohG` component + preservation through the five
memory operations), the closed forms over both fuels in the
outcome-list shape, the `fnptr` former and its call rule, one exhibit
(a dispatch table: an array of function pointers called in a loop — the
RefinedC `examples/pointers.c`/`scheduler` flavour). Estimate 2–3
worker-weeks, one worker, AFTER the fuel restatement (§1.6 item 2) and
after §1.4's `ProcSpec` change (the call rule is rewritten once). This
slice is the template for concurrency and external calls: the same
scheduler induction, more round shapes.

## 4. The annotation path

### 4.1 What Cerberus keeps

- Every Core node is `Expr : List annot → generic_expr_ → generic_expr`
  (Core.lean:1247). `annot` (Annot.lean:201) has, among others, `Aloc :
  Loc → annot` (`:206`, "C source location"), `Aattrs : attributes →
  annot` (`:216`, "C2X attributes"), `Alabel` (`:221`), `Astmt`/`Aexpr`
  (`:229`/`:231`, "Added for CN, to mark an Ail statement boundary").
- The C elaborator wraps EVERY translated statement as
  `(Caux.add_loc loc -| Caux.add_stmt -| Caux.add_attrs stmt.A.attrs) <$> …`
  (translation.lem:3701); `add_attrs` pushes `Aattrs attrs` onto the
  node's list unless the attribute list is empty (core_aux.lem:2178–2184).
  So a C2X attribute on a C statement — `[[rc::inv_vars(…)]]` on a loop,
  say — reaches Core as `Aattrs` on the outermost node of that
  statement's translation.
- Function-level attributes reach Core through the file:
  `funinfo : Fmap sym (Loc × attributes × ctype × List (Option sym × ctype) × Bool × Bool)`
  (Core.lean:1661; built from `decl_attrs` at translation.lem:4345/4377).
- The engine's ONE use of static annotations on the execution path: in
  `step_ctx`'s general arm, `get_loc e_annots` (Annot.lean:300: the
  first `Aloc`, skipping `Astd`/`Aattrs`/… ) and, unless
  `isLibraryLocation`, `th_st with current_loc := loc1`
  (Core_reduction.lean:484, the substring `let maybe_loc := get_loc
  e_annots; … { th_st with current_loc := loc1 }`). `current_loc` only
  reaches error/UB payloads (`stExceptUndef_undef th_st.current_loc …`,
  the `Eccall` arm above; Step.lean:1450–1455 for the memory actions'
  `loc`). Consequence: `Aattrs`-only annotation lists do not disturb
  `current_loc`; `Aloc` does — and the elaborator always adds `Aloc`.
- Whether the Core rewrite passes (`Core_rewrite`, `Core_sequentialise`,
  anormalisation) PRESERVE `Aattrs` on the nodes they rebuild is not
  measured here (§7 Q7).
- RefinedC's frontend reads its attributes from AIL, not Core
  (`collect_rc_attrs : Annot.attributes → rc_attr list`,
  ail_to_coq.ml:72–92; statement attrs at :1047–1050; function decl
  attrs at :741–744) and emits its own Rocq AST. Its grammar keywords
  (rc_annot.ml:482–510): `parameters, refined_by, typedef, size, exists,
  let, constraints, immovable, field, global, args, requires, returns,
  ensures, annot, asrt, inv_vars, annot_args, tactics, lemmas, trust_me,
  skip, manual_proof, block, full_block, inlined, unfold_order`.

### 4.2 What breaks in the demo on located Core

`Frag` is stated at `Expr []` at every constructor (`Soundness.lean:4129`–
`:4147`); the redex spellings (`storeRedex`, `saveRedex`, …) are at
`Expr []`; `toVal` requires `a.isEmpty && a2.isEmpty && b.isEmpty`
(`Step.lean:250`–`:251`), so a LOCATED VALUE NODE is not a mirror value
although the engine's RETURN/PROGRAM-DONE arms match `Expr e_annots
(Epure (Pexpr _ _ (PEval cval)))` for any `e_annots` (Step.lean:2059
docstring); `ofVal` rebuilds `Expr []` (`:239`); `BareHead` is the
canonical annotation-free shapes (`Soundness.lean:3981`); `MachineCtx.currentLoc`
is immutable (`Step.lean:405`–`:413`) and `engine_step_matchU`'s
successor thread has `current_loc = M.currentLoc`, which every adequacy
export carries as `hcl` (`Adequacy.lean:1296`). The mover is named in
the tree: "make `current_loc` live state, part of the runtime tuple as
`env` is" (`Soundness.lean:4147`).

### 4.3 Options

- **(A) Admit annotated Core into `Frag` with an ERASURE theorem**: the
  layer verifies `erase e` and a theorem transports to `e`. The engine's
  behaviour on `e` and `erase e` differs exactly in `current_loc` and in
  the `Loc` payloads of kills/UB; a transport theorem for SAFE runs (no
  kill) is provable in principle over `step_ctx`. But the exported
  statement would then quantify over `erase file` — a hand-written
  function of ours in the statement of an export, which the referent
  rule forbids ([USER 2026-09-02], CLAUDE.md "The referent of every
  export is the genuine semantics"), or it would be stated about `file`
  with `erase` in the proof only — which is option (C) with an extra
  simulation. No.
- **(B) A cerberus-lean request: an annotation-stripping pass with a
  preservation theorem.** Under their zero-discrepancy rule UB
  locations count as behaviour (their register; our memory
  `cerberus-lean-zero-execution-discrepancies`), so a stripping pass
  can never be "the semantics", only a proof device with a
  safe-run preservation theorem — i.e. (A) owned upstream. It also asks
  them to prove a theorem about `step_ctx` for our convenience. No.
- **(C) Verify LOCATED Core directly** (recommended, [AGENT]): `Ctl`
  gains `curLoc : Loc` (`Step.lean:371`–`:374`: it is already the record
  of "the `thread_state` fields the engine writes"; `current_loc` is
  one more such field); every `Step` rule threads `get_loc a` at its
  redex node through the `isLibraryLocation` test (mechanical, ~24
  rules); `Frag` and the redex spellings generalise `Expr []` to
  `Expr a`; `toVal`/`ofVal` accept any static list (the engine does);
  `BareHead`'s `not_annot` concerns the DYNAMIC `Eannot`, a different
  constructor, and survives; `hcl` disappears from the exports
  (`current_loc` becomes part of the configuration the export names
  through `ctlThread`). The certification re-proves per rule (the
  C1-class re-elaboration of `Soundness.lean` 5297 lines and
  `Step.lean` 3398 lines — the grind tripwire is real; capped,
  per-module). It is a FRAGMENT/MIRROR change, so it is Lane B's first
  fragment slice on the copy, sequenced with "compiled Core" (§1.3,
  §1.5). Estimate 1–2 worker-weeks.

### 4.4 How specifications enter

The ruling stands: RefinedC's annotation language is out of scope;
"specs/proofs authored in Lean natively" ([USER 2026-08-29],
DECISIONS:33–39), now for an AGENT that writes Lean. Therefore:

- **Function specs** are Lean values: a `SpecTable` mapping the C
  function's `sym` (stable: the C name's symbol in `file.funs`) to a
  `fn_params`-shaped entry (§1.4, §5.2). Nothing is read from C.
- **Loop invariants** are `Ls` entries keyed by the `save` label's `sym`
  inside the loop's Core translation. Labels are gensym'd; the agent
  locates the loop by the `Aloc` on the statement node (located Core,
  §4.3) — the same information a human uses — and the layer offers a
  helper that, given a `Loc`, returns the `save` symbols beneath it.
  OPTIONAL, if naming by location proves brittle under edits: ONE
  attribute `[[rc::annot("name")]]` (already in Cerberus's grammar as
  a C2X attribute) as a name marker; it travels to Core as `Aattrs`
  (§4.1) and the layer reads it with `Annot.get_attrs` (Annot.lean:319).
  This is the whole "annotation grammar" recommended: zero keywords
  required, one optional marker.
- **What is NOT recommended**: porting `rc::args/requires/returns/
  ensures/exists/parameters/inv_vars/constraints` as C attributes. For
  an agent the C-side string grammar is an extra parser, an extra
  failure mode and a second copy of every spec; Lean is the single
  source. The tiebreaker does not apply because the choice is not free:
  the frontend ruling decides it.

cerberus-lean requests arising: NONE required for (C). Two OPTIONAL
confirmations for their queue: (i) that `Aattrs` survive the Core
rewrite passes on statement nodes (if the marker is wanted); (ii) that
`funinfo`'s `attributes` are populated for every `Proc` (for a possible
future C-side marker at function level). Neither blocks the layer.

## 5. The slice of RefinedC to adopt

### 5.1 Judgment forms → over our `wps`

| RefinedC (cite) | Ours | Note |
|---|---|---|
| `typed_val_expr e T := ∀ Φ, (∀ v ty, v ◁ᵥ ty -∗ T v ty -∗ Φ v) -∗ WP e {{Φ}}` (programs.v:96–97) | `typedPexpr M ρ pe T := ∃ v ty, ⌜evalPexpr M.tagDefs M.extern ρ pe = some v⌝ ∗ v ◁ᵥ ty ∗ T v ty` — PURE, no WP | Core operands are pure pexprs evaluated big-step; the rules already carry the evaluator verdict (`wps_if`, `Wps.lean:1521`) |
| `typed_stmt s fn ls R Q := ⌜length ls = …⌝ -∗ WPs s {{Q, typed_stmt_post_cond fn ls R}}` (programs.v:68–69) | `typedStmt M p Ls Θ R e ρ := wps M p Ls Θ (fun w ρ' => ∃ ty, w.val ◁ᵥ ty ∗ R w.val ty) e ρ` | `Q : gmap label stmt` is `M.labelsAt p`; the `ls`/`l ↦|ly|` clause (programs.v:66–67) is dropped for LOCALS (Core `kill`s them in-band) but the ARGUMENT SLOTS must be returned in the post (the hostile review's MAJOR-1, `docs/2026-08-30_statement-view-hostile-review.md`) — a spec-shape rule for `fn_params` entries, not a judgment clause |
| `typed_block P b fn ls R Q := wps_block P b Q …` (programs.v:72–73) | an `Ls b` entry + `blockSpecs_intro` (`Wps.lean:3195`) | labels take arguments and are entered by fall-through (spike ledger 7–8) |
| `typed_call v P vl tys T` (programs.v:117–118), `type_call_fnptr` (function.v:131–137) | `wps_call_root` (`Wps.lean:473`) at a `fn_params`-shaped `Θ f` | §1.4 |
| `typed_function fn fp` (function.v:59–66) | one `hW` obligation of `procSpecs_intro` (`Wps.lean:3287`) | persistence is the collapse's `procSpecs` premise |
| `typed_read`/`typed_write` → `typed_read_end`/`typed_write_end` (programs.v:146–189) | typed small axioms as corollaries of `wps_load_plain`/`wps_store_plain` (`Wps.lean:2598`/`:2577`) and `wps_load_at`/`wps_store_at` | `E`/`atomic`/`memcast` dropped (§2; spike ledger 3, 14) |
| `typed_place P l β ty T` (programs.v:324–326) | focus lemmas per composite former | Core has no lvalues; field/index addressing is pure pointer arithmetic (spike ledger 5) |
| `typed_if` (programs.v:51) | `wps_if` + evaluator laws on typed ints | |
| `typed_switch` (programs.v:75–80) | `wps_case_value` (`Frag.case_value`, `Soundness.lean:4296`, carries `hbsz`) | later |
| `typed_assert` (programs.v:84–91) | no counterpart: the C front end INLINES UB checks as `Ecase`/`Eif` over `Specified/Unspecified` and `undef` (statement-view design E2) | this is the dominant automation load on compiled Core: every inlined check is a `wps_if`/`wps_case_value` step with a pure guard the executor must decide |
| `subsume P1 M P2 T := P1 -∗ ‖M‖ ∃ x, P2 x ∗ T x` (definitions.v:220) | `subsume P₁ P₂ T := P₁ -∗ ∃ x, P₂ x ∗ T x` | THE one goal shape the agent sees when the executor stops |
| `typed_annot_expr/stmt`, `typed_macro_expr`, `typed_copy_alloc_id`, `typed_cas` (programs.v:41–48, :122–138) | not ported | annotation conveniences / concurrency |

### 5.2 The minimal type set for "boring specs at scale"

| Former (donor) | Definition to mirror | Over our assertions |
|---|---|---|
| `int it @ n` | `ty_own_val v := ⌜val_to_Z v it = Some n⌝`, `ty_own β l := ∃ v, ⌜val_to_Z v it = Some n⌝ ∗ … ∗ l ↦[β] v` (int.v:10–14) | `valToZ` over the two Core integer spellings (spike §1.2); `ownLoc` via `pointsToCell` at `Basic (Integer ity)`; needs the codec round trip (spike GAP 1) |
| `&own ty` = `frac_ptr Own ty` | `ty_own_val v := ⌜v = val_of_loc l'⌝ ∗ l' ◁ₗ{β} ty`; `ty_own β' l := … l ↦[β'] l' ∗ l' ◁ₗ{own_state_min β' β} ty` (own.v:11–15, :34, :365) | `DFrac`-indexed; `&shr := ◁ₗ{.discard}` (§2.3); needs the pointer round trip (spike GAP 2) |
| `null` | `ty_own_val v := ⌜v = NULL⌝` (own.v:451–455) | indexed by the load's pointee (spike ledger 13) |
| `uninit ly` | `Notation uninit := (bytewise (λ _, True))` (bytes.v:175); `l ◁ₗ uninit ly ≡ l ↦|ly|` (bytes.v:180–181) | the post of `wps_create`: the unspecified image, decode-inert |
| `struct sl tys` | `ty_own β l := ⌜layout⌝ ∗ … ∗ [∗ list] i↦ty ∈ pad_struct …, (l +ₗ offset_of_idx … i) ◁ₗ{β} ty` (struct.v:54–63) | ReadinessSmoke's `twoField` (`Examples/ReadinessSmoke.lean:104`) generalised over a field list via `pointsToView`; needs `memberShiftPtrval` law and the `tagDefs` premise lifted (§1.3) |
| `array ly tys` | `[∗ list] i ↦ ty ∈ tys, (l offset{ly}ₗ i) ◁ₗ{β} ty` (array.v:9–18) | views at `i · sizeof elem`; `pointsToView_split/join` |
| `optional ty optty b` | `⌜b⌝ ∗ l ◁ₗ{β} ty ∨ ⌜¬b⌝ ∗ l ◁ₗ{β} optty` (optional.v:44–48) | the null-terminated list's node type |
| `∃ₜ x. ty x` = `tyexists` | exist.v:18–28 | trivial |
| `own_constrained P ty` / `constrained` | `l ◁ₗ{β} ty ∗ P β` (constrained.v:14–17) | trivial |
| `value ot v`, `place l` | singleton.v:8, :172 | the agent's "I know the exact value/location" escape hatch |
| `fnptr sp` | `function_ptr` (function.v:106–121) — ours without `fntbl_entry` | §3.3 |
| NOT first: `boolean`, `bytes`/`padded`, `intptr`, `tagged_ptr`, `bitfield`, `union`, `locked`, `atomic_bool`, `wand` | | `boolean` when `_Bool`/truthiness needs it; the rest with the arcs that need them |

`fn_params` (function.v:42–51: `fp_atys`, `fp_Pa`, `fp_rtype`, `fp_fr :
fp_rtype → fn_ret{fr_rty, fr_R}`) becomes the layer's `FnSpec A`, lowered
to a `ProcSpec` entry `Θ f vs := ⟨A, fun x => [∗] vs ◁ᵥ atys x ∗ Pa x,
fun x ret => ∃ y, ret ◁ᵥ (fr x y).rty ∗ (fr x y).R⟩` under §1.4 (i); the
argument-slot pointers' return rides in `fr_R`.

### 5.3 How agent-generated specifications enter

A Lean file per C translation unit: `def specs : SpecTable := …` keyed
by function symbol, `def invs : sym → Ls-entry` keyed by label symbol
(located through the loop's `Aloc`/optional marker, §4.4), a `theorem
<unit>_verified` whose statement is `prod_run_safe_procs`'s shape (§3.2
item 4) at the elaborated file and whose proof is the executor plus
the hand-supplied steps. The agent's loop (spike §0): write the table,
run, read the stop, amend. No C-side grammar.

### 5.4 Lithium's algorithm over our judgments

What Lithium IS (measured): a goal LANGUAGE — `li.exhale/inhale/all/
exist/done/false/and/find_in_context/case_if/case_destruct/tactic/
subsume/bind` (syntax.v:11–63) — and an INTERPRETER `liStep`
(interpreter.v:1178–1201) that picks the first applicable of
`liTactic, liExtensible, liSep, liAnd, liWand, liExist, liImpl,
liForall, liSideCond, liFindInContext, liCase, …` with committed choice
(no backtracking), plus the typing dispatch `liRStep :=
liEnsureInvariant; try liRIntroduceLetInGoal; first [liRPopLocationInfo
| liRStmt | liRIntroduceTypedStmt | liRExpr | liRJudgement | liStep]`
(automation.v:257–266), where `liRStmt`/`liRExpr` are `lazymatch` tables
from the statement/expression CONSTRUCTOR to a `type_*` lemma
(automation.v:145–188, :214–247). Side conditions: `liSideCond` tries
`done` and otherwise SHELVES (interpreter.v:458–480); `can_solve_hook
::= solve_goal` (automation.v:45) is the hard solver; `normalize_hook`
(hooks.v; normalize.v) rewrites arithmetic/list normal forms;
extensibility is by typeclass instances (`FindInContext`,
`SimplifyHyp/Goal`, `Subsume`, definitions.v:159–225) — the part the
ruling [USER 2026-09-02] does not take (hand-kept table; revisit past
~100 rules, spike ledger 11).

Over OUR judgments the same algorithm is: (1) `whnfR e` to `Expr a (K …)`
and dispatch on `K` — Core's constructor set is the table's key
(`Esseq/Ewseq/Eif/Esave/Erun/Eaction(Store0/Load0/Create/Kill/Alloc)/
Ememop/Epure/Eproc/Ecase/Eannot`, the 23 `Frag` constructors); (2) apply
the rule (R1–R4 of the spike §2: constructor-headed conclusion, consumed
atoms first, wand continuation, pure side conditions last, `AnnotInsensitive`
posts); (3) `find_in_context` = match the consumed atom `p ◁ₗ _` against
the proof-mode context after pointer normalisation (`cellPtr id (a + off)`
normal form; `envAdd_lookup` for symbols, `EnvLaws.lean`); (4) side
conditions: `rfl`/`decide`/`omega`/`simp [codec]`, unsolved ones LEFT as
goals tagged with the redex's `Aloc` (the agent's feedback — Lithium
shelves for a human who never sees them; we leave them for an agent who
reads them); (5) the leaf is `AtomicStep` through the `*_plain` rules,
never the raw WP; (6) stop at a jump/value/call: emit the `subsume` goal
against `Ls`/the typed post/the table's pre. Reusable: the algorithm,
the rule-statement discipline, the "one goal shape at a stop". Not
reusable: Ltac2 code, the `iProp_to_Prop`/`i2p` instance encoding
(definitions.v:146–152), the evar-sharing machinery (`li_done_evar`,
interpreter.v:596–627) — Lean 4 metavariables and `MetaM` replace them.
Implementation: a `MetaM` tactic composing the existing proof-mode
tactics (the demo's proofs are exactly `iintro/iapply/isplitl/iexact/
imod`), table as `List (Name × Syntax)` per constructor; estimate
400–800 lines for the first fragment (spike §4 stands).

### 5.5 What we deliberately do NOT adopt

Caesium (`caesium/lang.v`, the two-sorted `expr/stmt` grammar, `Ebound`-
free surface) — replaced by Cerberus Core; Caesium's memory model
(`caesium/heap.v`; `heap_mapsto`, `alloc_alive`, `loc_in_bounds`) —
replaced by the engine's `CerbMem` through `CohG`/`MemWF` (our
`allocMeta`/`locInBounds` are the analogues we already have, Heap.lean
header); the C frontend and annotation language (`frontend/`, §4.4);
concurrency (`monStep`, `atomic_bool.v`, `locked.v`) — after masks;
`mem_cast`/`op_type` generality (type.v:283–296) — Cerberus decodes at
the action's ctype; `Shr`/`Copyable` as invariant-based sharing (§2.3);
the subtyping instance families (programs.v:756–922 per the spike) —
until the table needs them; `refinedc_adequacy`'s `fntbl` ghost
(adequacy.v:40–50) — §3.3.

### 5.6 The first four slices, one change each, with acceptance tests

Preconditions (not slices of this layer): the demo's v1 tag; Lane B
re-seeded from that head; the copy's `ProcSpec` change (§1.4 (i)).

| # | Slice (ONE change) | Where | Acceptance test |
|---|---|---|---|
| L1 | The value layer and the scalar formers: `valToZ`, the codec round trips GAP 1/GAP 2 (in the base), `CoreType` (spike §1.1), `int`, `&own`/`&shr`, `null`, `uninit`, `value`, `place`; typed load/store/create/kill as corollaries; `subsume` | layer package over the copy's `API` | `Examples/ReadinessSmoke.lean`'s five `twoField_*` theorems (`:151`–`:276`) re-stated with typed atoms and re-proved through typed rules only; the boundary check (`scripts/boundary_check.sh`) green on the layer's client modules; NORTH-STAR EXHIBIT: a never-seen straight-line C-shaped Core program (hand-written) with an `int`/`&own` spec |
| L2 | The judgment shape: `typedPexpr`, `typedStmt`, typed label entries, `wps_if`/`wps_case_value` with evaluator laws for the eight mirrored binops and comparisons on `int` | layer | `LoopExhibit`'s counter loop and `FibExhibit` re-stated with a typed invariant `Ls l := p ◁ₗ (i @ int ity) ∗ …`, proved by typed rules; statement texts of the demo untouched (it is a copy) |
| L3 | Composite formers: `struct`, `array`, `optional`, `∃ₜ`, `own_constrained`, focus lemmas (`focus_field`/`focus_index`); needs `memberShiftPtrval` and the `tagDefs` lift in the base | layer (+ two base spec-additions) | `ListRevExhibit`'s list as `∃ₜ xs. list xs` via `optional (&own (struct [int; ptr]))` (RefinedC tutorial `list.h` shape), in-place reversal proved by typed rules; `StructExhibit` likewise |
| L4 | The executor `tstep`/`texec` (§5.4) | layer | L1–L3's proofs REPLAYED by `texec` with only the invariants supplied by hand; measured: manual tactic lines per Core statement before/after; a stop report on a program with a deliberately missing invariant naming the `Aloc` |

Then, in order and each its own slice: L5 `FnSpec`/`typed_call` through
`procSpecs` on the changed `ProcSpec` (acceptance: `FibRecExhibit` +
a `reverse` called twice on two lists — the §1.4 counterexample, now
provable); Lane B's located Core (§4.3) and compiled Core (§1.5); L6
the first compiled C exhibit end-to-end (`deps/refinedc/tutorial/t01_basic.c`
or `examples/reverse.c` — the [USER 2026-08-29] acceptance ladder
"their proofs transfer"); §3's function pointers; §2's masks when
`lock.c`/`spinlock.c` come into view.

## 6. A shared coupling library?

### 6.1 The module graph (imports, measured from the `import` lines)

```
Core_aux/Core_run_aux/Core_reduction/CerbMem (engine)
  └─ Step ─┬─ EnvLaws ─┬─ Soundness(+Core_reduction) ─┬─ EvalClass ─┐
           │           │                              ├─ Potential   │
           └─ Heap(+Iris) ─ Lang ─ Rules ─ Wps ─ Wpt   │              │
                 │                    │               │              │
                 │        Adequacy(Rules,Soundness,Potential,DriverCollapse)
                 │                    │               │              │
                 │             TotalAdequacy(Wpt,Adequacy)           │
                 │                    │                              │
                 │      API(Heap,EnvLaws,Rules,Wps,Wpt,Potential,Adequacy,TotalAdequacy)
                 │                                                   │
   DriverCollapse(Soundness,Driver,CerbND) ── Round(Heap,DriverCollapse,EnvLaws,EvalClass)
                 │
   ProdLoop(DriverCollapse,TotalAdequacy) ── ProdEntry(DriverCollapse,Layout,FibExhibit,ProdLoop)
   exhibits(API, Layout, ProdEntry, each other) ── Audit(everything + Round)
```

Line counts (wc, this revision): `Step` 3398, `Heap` 4800, `Lang` 175,
`EnvLaws` 408, `Rules` 1681, `Wps` 3700, `Wpt` 3411, `Soundness` 5297,
`EvalClass` 1094, `Potential` 502, `Round` 5504, `DriverCollapse` 2315,
`Adequacy` 2161, `TotalAdequacy` 94, `API` 119, `ProdLoop` 846,
`ProdEntry` 816, `Audit` 655; exhibits + Examples ≈ 15.9k; total 57,968.
Note `ProdEntry` imports an exhibit (`FibExhibit`) and `Examples.Layout`
(KOI C4's duplication is next door): production-core depends on a
client — a hygiene item that any extraction would have to fix first.

### 6.2 Classification

| Class | Modules / parts | Fragment-independent? | Mask-generic? |
|---|---|---|---|
| (a) SEMANTICS-COUPLING | `Heap` (ghost carrier, `CohG` `:2632`, `MemWF` `:1583`, bundles, engine-memory success lemmas, `MemWF.*` preservation); `EnvLaws`; `MachineCtx`/`Ctl`/`Config`/`Mem` (`Step.lean:167`, `:371`–`:413` — machine embedding, not the relation); `Rules`'s `AtomicStep`/`wp_of_atomic` (`:194`–`:240`); `DriverCollapse`'s ND collapse (`runOne_bind_active`, `runND_active`, `driver2_done`, `loop_step_done`, exhaustion rounds — the header's "ND COLLAPSE"/"READOUT"); `Adequacy`'s `spike_step_adequacy`, `DriverSafeCtl` (`:932`), `MemTriple`/projection; `ProdLoop`'s `DriverDoneCtl` (`:456`); `ProdEntry`'s cold start (`prodMem₀`, `drive_after_setup`, `prod_run_eqJ*`) | YES in content: none of these mentions a `Frag` constructor; `Heap` mentions `MachineCtx` only in a comment (1 hit) and imports `Step` for `Mem`; `AtomicStep` is over `CoreRt`/`primStep`, i.e. over `Step`'s TYPE, not its rules | `AtomicStep`/`wp_of_atomic` yes; `DriverSafeCtl`/`MemTriple` are mask-free (pure) |
| (b) FRAGMENT/MIRROR | `Step` (the relation), `Soundness` (`Frag`, `Decomp`, per-rule step match), `EvalClass`, `Potential`, `Round` (certification + completeness), `DriverCollapse`'s `loop_step_frag` family, `Rules`'s `*_atomic` per construct, `Lang` (the `Language` instance IS `Step`) | no — grows per constructor | n/a |
| (c) STATEMENT LOGIC | `Wps`, `Wpt`, `Rules`'s `wp_store`/`wp_load` faces, `TotalAdequacy`, `ProdLoop`'s inductions, `Adequacy`'s `drive_safe_aux`, the collapses | no — the judgments change shape (§1.4, §2) | NO (`⊤`) — the natural seam the audit named |
| (d) CLIENTS | 16 exhibits, `Examples.*`, `ProdExhibit`/`ProdLoopExhibit`, `Audit` | — | — |

DERIVED rough sizes: (a) ≈ 8–9k lines (Heap 4800 + EnvLaws 408 + ~500 of
Step + ~300 of Rules + ~1100 of DriverCollapse + ~1000 of Adequacy +
ProdEntry 816 + ~450 of ProdLoop); (b) ≈ 16k; (c) ≈ 8k; (d) ≈ 17k
(inexact: the module-internal splits are my reading of the headers).

### 6.3 The earlier ruling, re-read against the classes

[USER 2026-09-03] "reused are the architecture and proof techniques, not
the artifacts — the grown fragment is re-certified anyway"
(DECISIONS:948–966) is exactly right for (b): every `Step` rule,
`Frag` constructor, `complete_*` lemma and `loop_step_frag` case is
re-proved when the fragment grows, and a copy is the honest carrier.
It is right for (c) too: `ProcSpec` (§1.4), masks (§2), the scheduler
lane (§3) change the judgments' text. It does NOT describe (a): `CohG`,
`MemWF` and its five preservation theorems, the byte-map algebra, the
bundles' split/join/fractional laws, `runND_active`, `prodMem₀_memWF`,
`drive_after_setup` are ENGINE facts that no fragment growth touches;
a copy of them is a second copy of the trust-bearing coupling that the
external audit's Note (two bridges) already flags as drift risk in
miniature (KOI B12).

### 6.4 The operator's addendum, weighed

[USER 2026-09-04], verbatim: "There's also a bit of value in factoring
the library in that any updates are then required to keep the demo
working - the demo as regression suite." With a shared package every
change to (a) — a `funptrmap` component in `CohG` (§3.3), a `readonly`
stratum in `MetaCoh`, a live `curLoc` in `Ctl` (§4.3) — must keep the
demo's 402 trio-exact pins and its FULL gate green, at zero extra
authoring cost: 16 exhibits, 9 closed shipped-driver statements, the
manifest, the boundary check. A copy lets the two drift silently. Two
qualifications, [AGENT]:

- The demo exercises (a) only on ITS fragment. A library change adds
  content the demo never runs (the `funptrmap` coupling is inert on
  demo programs); the regression suite proves NON-BREAKAGE of the demo,
  not correctness of the new content — that still needs the layer's own
  exhibits and the audit.
- Some library changes are NOT statement-neutral for the demo: a live
  `curLoc` in `Ctl` deletes `hcl` from every adequacy export
  (§4.3) — the demo's export TEXT changes, its ARCHITECTURE cites move.
  So "pristine" must mean ALWAYS GREEN AND RE-AUDITED, not FROZEN. That
  is a change to the demo's status the operator should rule on
  explicitly (§7 Q3).

Pin/audit boundary: a shared package is its own Lake package
(`cerberus-iris/` beside `cerberus-heaplang/`, same `../.cerberus-ws`
semantics pin, same iris pin, its own `Audit.lean` sweep, `require`d by
path from the demo and the layer). A library change is then a range
under the demo's audit rule ([USER 2026-09-03] "every merge is audited
over the range since the last audit", DECISIONS:901–910) because the
demo's gate runs on it — one audit, not two; the semantics re-pin dance
happens ONCE (today a copy would need two scout records, two re-pins).
Cost: one more package in `test_unit.sh` (gate 2 builds two packages;
the runner already did that before `24c2410` trimmed it), one more
manifest, the demo's `Audit.lean` unchanged if the namespace is kept
(§7 Q3).

### 6.5 Recommendation

[AGENT]: **share (a), copy (b) and (c), never (d)** — but not as the
first move. Order: (1) the demo's v1 tag after the ruled six steps
(re-pin, fuel restatement, statement-shape, hygiene, ARCHITECTURE
re-review); (2) an INTERNALS-ONLY extraction slice on the demo — public
statements frozen and snapshot-checked (`scripts/signature_snapshot.lean`),
module paths move, 402 pins re-baselined by name only — producing
`cerberus-iris/`; (3) Lane B re-seeds the copy of (b)+(c)+(d) from that
head and the layer package `require`s `cerberus-iris` + the copy. The
regression-suite property then holds from the layer's first slice.

**First extraction** (the smallest coherent unit with the highest trust
content): `CerberusIris.Machine` — `Mem`, `MachineCtx`, `Ctl`, `Config`,
`MachineCtx.thread` and the embedding lemmas (from `Step.lean:167`,
`:371`–`:413` and their neighbourhood; NOT the `Step` inductive) — and
`CerberusIris.Heap` = today's `Heap.lean` re-homed (it imports `Step`
only for `Mem`; the one `MachineCtx` mention is a comment), plus
`EnvLaws`. `Step` then imports the library. Estimate 2–4 worker-days
including the snapshot check and its audit; zero statement-text change
if the namespace `CerberusHeapLang` is kept for the moved declarations
(an unusual but legal choice; renaming costs a 402-name re-baseline and
every ARCHITECTURE cite — §7 Q3). Second extraction, later: the ND
collapse half of `DriverCollapse` and `Adequacy`'s definitions
(`DriverSafeCtl`, `MemTriple`) — these mention `ctlThread`/`LabeledProcs`
and so depend on the first extraction, not on `Step`'s rules.

What stays a copy and why: `Lang` (its `primStep := Step …`), `Rules`'s
atomics, `Soundness`, `Round`, `DriverCollapse`'s per-redex rounds,
`Wps`/`Wpt` and the lanes — all of which the layer's base changes.

## 7. Open questions for the operator

1. **`ProcSpec` logical variables (§1.4).** Ratify (i) — the
   `fn_params`-shaped table as the FIRST Lane B slice on the copy — or
   prefer (ii) the layer-derived ghost-variable encoding that leaves
   the copy's judgment unchanged? [AGENT] recommends (i).
2. **Located Core (§4.3).** Accept option (C) (verify located Core;
   `current_loc` live in `Ctl`; `hcl` retired) as Lane B's first
   fragment slice, sequenced with compiled Core? It re-elaborates
   `Soundness`/`Step` wholesale (the C1-class tripwire).
3. **Shared library (§6).** Go/no-go on `cerberus-iris/` as an
   internals-only extraction after the v1 tag; if go: (a) is "pristine"
   allowed to mean "always green and re-audited" rather than "frozen
   text"; (b) keep the `CerberusHeapLang` namespace for moved
   declarations (zero pin churn) or rename; (c) may the layer ALSO
   depend on the demo package's `API`, or only on the library + the
   copy?
4. **Spec entry (§4.4).** Lean-authored specs keyed by symbol and
   label, at most one optional `[[rc::annot("name")]]` marker — confirm
   that no C-side spec grammar is wanted, even for agents that edit the
   C.
5. **Masks (§2).** Accept "wait until the first invariant-backed type"
   — or do the audit's F3 generalisation early as an isolated
   statement-shape slice on the copy while the box is idle (3–5 days)?
6. **Function pointers (§3).** Accept the outcome-list closed form as
   the layer's export shape from birth, and the sequencing after the
   fuel restatement; is the scheduler lane (`SchedulerSafe`) to be
   built as the reusable template for concurrency/external calls, or
   minimally for `Eccall`?
7. **Two measurements** I could not make read-only and would ask a
   worker (or the operator) to run through the OCaml driver
   (`--pp=core --rewrite`, as the hostile review did): does the
   elaborator emit `Store0 true` for `const`-qualified objects (decides
   whether the `readonly` stratum is early or late), and do the Core
   rewrite passes preserve `Aattrs` on statement nodes (decides whether
   the optional marker is viable)?
8. **Acceptance ladder.** [USER 2026-08-29] "RefinedC's own examples/
   tutorial suite" — name the first two: [AGENT] proposes
   `tutorial/t01_basic.c` and `examples/reverse.c`, with
   `examples/spinlock.c` as the first masks-era target.
9. **Sequencing against the box.** Everything here waits on the re-pin
   and the fuel restatement (two build lanes at most); the only Lane C
   work that can proceed meanwhile is design: the `CoreType` record's
   exact laws over the calls-era API and the executor's rule-table
   format. Should that be the next Lane C note?

## 8. Provenance

[AGENT 2026-09-04], the Lane C design agent, read-only in worktree
`design-c2` at `0534f9a`. All [USER] quotations are copied from
`docs/DECISIONS.md` at the lines cited or from the coordinator's relay
of the operator's 2026-09-04 addendum (§6.4, verbatim as relayed).
Tallies marked DERIVED are my `grep -c`/`wc -l` readings at this
revision; module-internal class splits in §6.2 are readings of module
headers, not measurements. Nothing was built; no `.lean` or script was
touched; no register was edited.
