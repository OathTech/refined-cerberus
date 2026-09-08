# What we still need from cerberus-lean — the requests register (demo, and the RefinedC-family layer after it)

Status: DRAFT for the operator [AGENT orchestrator, 2026-09-07], revision 2
after the hostile review `docs/2026-09-07_review-demo-master-plan.md` (its
fixes 3, 10, 11, 15, 17 and Part B5 are applied here); companion to
`docs/2026-09-07_demo-master-plan.md`. Written at refined-cerberus main
`777ca0f`, pin cerberus-lean `89f7e688530c6910884518811d645e4e892e4507`, and
after reading what has landed on the cerberus-lean mainline
(`mdd/cerberus-lean` at `94f339eb4`). Requests to the semantics team travel
as dated notes in `refined-cerberus/docs/` relayed by the operator; nothing
here is filed by being written here. Every claim about the other repository
is from its committed records and `git`, labelled DERIVED where a tally.

2026-09-08 consumer update: R-4's referent is settled for the authorized
whole-file t1 slice, as recorded below. The provider observations and counts
in §1 remain the dated baseline above. No new provider guarantee or reply
is inferred from the consumer's choice of referent.

## 1. What has landed on the cerberus-lean mainline since our pin

30 commits, `89f7e68..94f339eb4` (DERIVED). By content (DERIVED from
`git diff --name-status`, grouped by path):

- **No semantics change.** Nothing changed under `lean_frontend/generated/`,
  the hand-written seams `lean_frontend/*.lean`, `lean_frontend/native/`,
  `frontend/` or `backend/`; the only `.lem` change is a test fixture. Added
  files are all under `tests/`: the failure-reach probe (`FailureReachProbe.lean`,
  `FailureMain.lean`, `FailureReach.lean`, `discarded_failures.lem`,
  `failure_main.ml`, nine `reach/*.c`) and `tests/provider-smoke/ProviderSmoke.lean`.
  Consequence: **our pin is current in substance; no re-pin is forced by
  anything on their mainline today.**
- **Validation foundations** (2026-09-06/07): an independent upstream oracle,
  complete observation capture, a cold provider proof, a failure census, the
  documented test ladder run (Tier A, 11 rows in `scripts/LADDER.md`), release
  hardening, diagnostic-styling pins (`NO_COLOR=1`, `TERM=dumb`), evidence
  reconstructibility rules.
- **The csmith corpus sweep after P0** (6 shards): `mismatch=0` everywhere on
  the whole-line Defined comparison; two rows MATCH → TIMEOUT at the 15 s
  budget (both MATCH at 90 s), registered as pending in their TODO.
- **The risk-map baseline audit** (`2026-09-07_risk-map-baseline.md`, with the
  orchestrator's review §8): six surfaces; §6 is a read of OUR consumer
  surface — it confirms every one of the ten provider change manifests since
  their anchor B is adopted in our sources at the current pin, and lists the
  "actual promised statements" (§2 below quotes the ones that bind us). It
  also notes that our 117 `panic!` figure "is its own dated census, not a
  count certified by this audit" — consistent with the erratum to 119 made at
  the master-plan landing (KOI A5).
- **Pure-failure correspondence**: a reachability census of the 231
  exec-closure pure failure sites, the correspondence design (an `Outcome`
  type, a generated strict twin, a connection theorem), then the design
  **PARKED** with the census outcome "0 discardable sites; option C; flip
  conditions" (`94f339eb4`). Reading: no pure `failwith` in the exec closure
  is discarded, so the kind-1 discrepancy class that motivated the design is
  empty at the pin; the strict-twin route is parked until a flip condition
  makes it live. That design's §4 is also where the provider states that
  fuel MONOTONICITY ("done at n ⇒ done at every m ≥ n", their lem TODO 13) is
  "not statable for `drive`" while eight fuel rows exhaust into opaque
  sentinels — that its shape must be fixed with the operator first is this register's reading of their row, not their words.
- **A Codex charter for fuel-measure cost** (branch `arc/fuel-measure-cost`,
  not mainline): measure and remove the fuel arc's execution cost (build/CPU),
  which touches our build times only.
- **Unmerged: `feature/concurrency`** (S0–S7, 13 commits beyond mainline).
  `lean_frontend/generated/` is UNTRACKED in cerberus-lean (`git ls-files`
  lists no file there), so a diff over the generated Lean is vacuous; against
  the merge-base `31eba718e` the branch changes the `.lem` SOURCES of exactly
  the files the demo mirrors — `frontend/model/driver.lem | 708`,
  `core_run.lem | 50`, `core_reduction.lem | 141`, `core_run_aux.lem | 211`,
  plus `cmm_csem.lem | 45`, `cmm_op.lem | 5`, `mini_pipeline.lem | 2` (7 files,
  966 insertions, 196 deletions; DERIVED). **Its merge is a FORCED re-pin for
  us, with a scout first** (R-9). (Revision 1 said the opposite on a vacuous
  measurement — review F1.)

## 2. What we consume today, and what the provider has promised about it

From the risk-map baseline §6 (their words, "actual promised statements"):

| provider statement | what it means for the demo |
|---|---|
| fuel is a quantified `[LemFuel]` parameter; the zero-fuel and sufficiency lemmas exist at HEAD with the §3 restrictions; "General absorbing propagation/monotonicity is not among the delivered conclusions" | our exports are ∀-fuel above program-derived floors by our own proofs; we need NO monotonicity lemma (master plan §3.3; kill-adequacy note §5) |
| Pmap/Fmap lookup laws exist with comparator/WF hypotheses; EnvLaws supplies them | our 2026-09-03 lem-lean request is CLOSED |
| arbitrary tag environments require `Acyclic`/`AcyclicPair` for the six conditional sufficiency theorems; our fragment uses empty/concrete tag environments | binds V2-3 (structs): lifting `htd : tagDefs = ∅` means discharging acyclicity at the real entry |
| allocation exports narrowed at Z2 (positive alignment, nonnegative size, no requested-address `create`) — visible premise changes | KOI B21; carried honestly; nothing to request |
| kind-1 `panic!` arms: "native fail-stop and in-process default denotation are not yet connected by a faithful outcome theorem"; consumers should NOT mark exports PROVISIONAL merely for pending fuel rows | KOI A5 (119 arms, ten seams); §3 R-2 below |
| provider-native correspondence, strict failures, byte-string parity, broad accepted-domain/completion claims remain open (their master plan steps 2–3, 5); consumer whole-file/library adequacy is separately open (our A7) | A7 is OURS to close (master plan V1-1); §3 R-4 asks the two questions it needs answered |

## 3. Requests and needs for the demo — the register

Status vocabulary: FILED (a dated note exists in `refined-cerberus/docs/`),
ANSWERED (landed at the pin or later), OPEN (no note yet; this register is the
first statement), NONE (we thought about it and need nothing).

| id | need | why | status | ask |
|---|---|---|---|---|
| R-1 | a distinguished, transparent fuel-exhaustion outcome in the driver monad | root of trust: no home-made driver ([USER 2026-09-02]) | FILED `docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md` → **ANSWERED** by the fuel arc: `CerbND.fuelExhaustedKill = Error0 fuelExhaustedLoc fuelExhaustedMsg` (CerbND.lean:98), a `kill_reason` distinct by constructor from `Undef0` | none further |
| R-2 | the 119 `panic!` arms (A5) connected to a faithful outcome | negative claims at an arm are provisional; the covered programs avoid the arms by the rules' premises (ARCHITECTURE §3) | their master plan step; the pure-failure design PARKED 2026-09-07 with flip conditions (that census is about the 231 pure `failwith` sites, not the `panic!` arms) | **keep the arms' reachability characterised and tell us when a flip condition fires**; when a typed-failure outcome lands we adopt it at the next re-pin and re-examine the kill-adequacy terminal (`Undef0` is the channel their design does not move) |
| R-3 | fuel monotonicity | — | NONE for the demo (the WP proofs give ∀-fuel statements directly; §1 records the provider's own view that it is not statable for `drive` today) | none |
| R-4 | **the pipeline's whole file as the statement's referent (A7)**, and WHICH pipeline | criterion 4 of the definition of done; master plan V1-1 and G4.3 | SETTLED FOR t1 under the accepted whole-file charter: the pinned Lean frontend consuming OCaml Cabs, then linking and converting the full file; the theorem runs its quoted data with captured comparators under three checks. This is the option-(b) executable boundary. GENERAL PROVIDER GUARANTEES remain OPEN; no equality with OCaml's printed Core is assumed. | The local in-memory loader supplies the bounded one-TU/no-libc route; no new provider API is needed for t1. The broader questions remain: structural correspondence between frontends, a stable post-link structured dump (R-7), and option (a), the elaborator in the theorem. Record: `docs/2026-09-08_whole-file-t1-implementation.md`. |
| R-5 | a structural size lemma for generated substitution (`esize (subst_sym_expr x v e) = esize e`, and the `subst_sym_pexpr`/label twins) | we carry two `evalDepth`-shaped premises (`hQd`, ProdLoop.lean:380 and :451) and discharge them per program | FILED `docs/2026-09-05_note-cerberus-lean-subst-esize.md` (a duplication-avoidance note; "No action requested") | unchanged: if the lem-lean backend or cerberus-lean ships size lemmas for generated substitution, we consume them and drop the premises |
| R-6 | `mk_conv_int`'s signed non-representable arm vs std.core's `conv_int` (impl-defined `<Integer.conv_nonrepresentable_signed_integer>`) | an upstream Cerberus divergence, invisible for the gcc impl (both wrap) | FILED `docs/2026-09-05_note-cerberus-lean-conv-int-divergence.md` ("Not a request; a latent-divergence note for your register") | none; upstream-tray candidate on their side |
| R-7 | a structured (non-text) emission of the Core file | the corpus whole-text check cannot see what `pp_core.ml` never prints (`Aexpr`, `Astmt`, `Alabel`, `Acerb`, `Ainlined_label`, `Auid`; `Aattrs`/`Avalue` only at debug > 3, `pp_core.ml:577–578`; `Erun`'s annotation; symbol digests; action locations; save passing modes) — KOI C20 | OPEN as a stable provider interface; not a blocker for t1, whose loader captures the pinned Lean frontend's in-memory file directly and compares all retained data | folded into R-4's broader provider questions; the local quoter is not a provider correctness guarantee |
| R-8 | `dynamic_addrs` upstream defect (A3) | outside the logic; our `free` precondition implies the engine's check | provider ISO-fix register R4 DEFERRED upstream | none for the demo |
| R-9 | the sequential scheduler stays the default and stable across the concurrency merge | every export runs `drive fmapEmpty false …` through the shipped scheduler loop with one thread; E6 (calls) builds on the scheduler-round shape; §1 shows the merge rewrites `driver.lem` | OPEN — more than an expectation given §1 | **before `feature/concurrency` merges: notice and a re-pin scout window; confirmation that the sequential model is the default instance and `drive`'s signature is unchanged** |
| R-10 | the S5 "Epar-free agreement" lemma we asked the concurrency team for | E6's scheduler induction would use it | FILED via the S1 interface review (`docs/2026-09-04_response-concurrency-S1-interface-review.md`: "the one-tree agreement lemma (Q4, please prove it …)"); their mainline `2026-09-06_concurrency-integration-charter.md` I3 names it ("deliver provider agreement … under the reviewed `epar_free`/fragment/state/fuel hypotheses"); their branch record `2026-09-05_concurrency-S5-record.md` §4: "NOT done: the agreement lemma — an ACCEPTED Phase-0 obligation, not discharged" | **operator to ask its schedule at the concurrency merge** |
| R-11 | fuel-measure cost (their Codex charter) | our full builds are ~90 s wall for 56 modules | NONE; welcome | none |

Nothing in this table blocks Phase I. R-4/R-7's entry checkpoint is settled
for V1-1a by the bounded frontend choice above; their general guarantees
remain open. R-9/R-10 are the concurrency-merge items; the rest is tracking.

## 4. What the RefinedC-family layer (refined-cerberus) will need semantically

From the Lane C design note (`docs/2026-09-04_refinedc-layer-design-2.md`),
RefinedC's own architecture (the donor at `deps/refinedc/`, read-only:
`theories/caesium/{layout,loc,heap,val,int_type,struct,bitfield,byte}.v`,
`typing/{function,globals,intptr,tagged_ptr,malloc,union,padded}.v`), the
review's Part B5, and what the demo taught us. These are EXPECTED needs,
stated so the semantics team can plan; none is filed. Ordered by when the
layer would hit them.

| id | need | when | what exists at the pin | what would be asked |
|---|---|---|---|---|
| F-1 | **stable located Core with attributes preserved**: RefinedC specifications enter as C attributes (`[[rc::…]]`); the elaborator keeps `Aloc`, `Astd`, `Aattrs`, `Auid`; the demo strips locations (Lane C §4) | first spec-carrying slice | `Aattrs`/`Aloc` exist in the AST; the text printer prints `Aattrs` only at debug > 3 | a guarantee that C attributes reach the Core annotations unchanged, and R-7's structured dump so they can be read |
| F-2 | **function calls as first-class**: `Eproc`/`pcall` rounds, the call protocol, RETURN's control effects (Lane C §3.1) — and, for RefinedC's function pointers, the `funptrmap`/`PtrEq` arm (B8) | E6 (demo V2-4), then the layer's calls | all present in the engine; our mirror does not cover `Eccall` | documented stability of the call/return rounds and the function-pointer map across pins |
| F-3 | **the memory model as a specified interface**: struct/union/array layout (`tagDefs`, offsets, padding, `CerbTagsWf`, acyclicity), pointer arithmetic, **pointer↔integer casts and provenance** (Caesium's `loc = alloc_id × addr` with `alloc_id_alive` is what RefinedC's types are stated over — `intptr.v`, `tagged_ptr.v`), alignment, the byte representation of every scalar (`intToBytes`, `reconstructValue`), and TYPED UB for out-of-bounds, use-after-free, misaligned access | structs (V2-3) and every RefinedC type after `int` | the concrete model behind `drive`; 60 of the 119 `panic!` arms are in `CerbMem.lean` (A5); the "defacto" model is unreachable from `drive` (their TODO F-C2-4); byte-representation producer contracts are on their small-items list | (i) the memory-model seam's contract written down (operations, failures, which model); (ii) UB as `Undef0` outcomes rather than `panic!` in the memory seam — the prerequisite for UB-freedom specifications at scale; (iii) **which model (concrete vs PNVI-ae) is the semantics of record for casts**, and whether `CerbMem`'s provenance is observable through `PtrEq`/`intFromPtr` |
| F-4 | **the UB catalogue**: `Undef0 loc ubs` with the ISO `undefined_behaviour` list, complete for the C fragment the layer covers; and the kill LOCATION `loc` stable and documented (the kill-adequacy design's (c1)/(c2) needs it) | the layer's first UB-freedom claim | the list exists in the generated AST; kills are classified by `EvalFail`; only pure-evaluation kills are characterised in the demo | a statement of which UBs the exec pipeline can raise, per construct — so "UB-free" can be stated as "none of these" |
| F-5 | **integer semantics with the impl map as a parameter**: `conv_int`/wrap/impl-defined arms, `impl0` bound to the pinned gcc map (R-6's divergence lives here). The out-of-range fallback in `EmittedStdCore.convElse2` is a pure `PEcall (Impl …)`, distinct from the manifest's `Eproc _ (Impl _) _` procedure row. Representable t1 conversions take the successful range branch, so retaining the impl map requires no new implementation-procedure rule for t1. | the layer's int types (B15 byte images, B21 allocator contracts); future out-of-range conversion rules | the whole-file t1 certificate retains the linked gcc map; the old wrapper and t4/t5/t6 still have `impl0 = ∅` (A7). The captured-library proofs require explicit representability premises. | R-4 settles the bounded linked-file referent; general pure implementation-call support and stability of the parameterized impl map remain layer work, separately from implementation-procedure calls |
| F-6 | **globals and initialisers**: every current and G2 statement has `globs = []` (G2's own record: "Empty globals, empty tags and parameterless main remain explicit restrictions"); `driver_globals` reads each global through `to_pure`, a pending fuel row on the provider side (FUEL.md §4) | any real C file; RefinedC's `globals.v` | the engine path exists; the `to_pure`/`to_pures` bounds are a provider TODO | **an absorbing or measured `to_pure` on the globals path** (their fuel-parameter C2 follow-up) |
| F-7 | **typed failures**: their master plan steps 2–3 (strict failures, the `Outcome` type) — so that "the run neither panics nor discards a failure" is a theorem | the layer's soundness statement | PARKED (0 discardable sites at the pin) | R-2: notice at the flip |
| F-8 | **the C frontend as a stable pipeline**: `.c` → elaborated Core with a versioned dialect for the constructs the layer covers (arc E's lesson: every C feature is a set of emitted Core shapes, and the shapes move with the elaborator); and ONE referent (R-4's two-pipelines question) | continuously | the emitted corpus and the whole-text check catch drift per program | a dialect note per elaborator change that alters emitted shapes for covered constructs (a changelog, not a theorem) |
| F-9 | **concurrency, later**: the SC-DRF instance behind a parametric model selector (S1), the sequential instance as default | after the demo, when the layer meets threads | `feature/concurrency` S0–S7 unmerged; it rewrites `driver.lem` (§1) | R-9/R-10 first |
| F-10 | **performance of the generated semantics** for proof work: kernel-evaluable layouts (`decide` on concrete `tagDefs`), build time of the generated modules | continuously | their fuel-measure-cost charter; the F-C3-4 eager-measure backlog | none now |
| F-11 | **a kernel-checkable concrete run**, i.e. computing `runND (drive …)` for a small program inside the kernel | negative tests and refutation at the layer (RefinedC has none) | not possible today (the E3 notes: `decide +kernel` does not reduce the driver) | not requested: the kill-adequacy design (option A/B) takes the WP route instead |

## 5. How requests move

A request is a dated note in `refined-cerberus/docs/` (`*_request-*.md` or
`*_note-cerberus-lean-*.md`), written [AGENT] with the ruling it answers
quoted, relayed by the operator, and closed in this register when the
provider's change manifest names it and our adoption is visible in source
(the risk map §6 method). This register is re-issued at each re-pin.

## 6. Provenance

[USER 2026-09-07] (the working session; registered in DECISIONS with the
master plan's revision 2): "a companion document which says exactly what we
still need from cerberus-lean (including what we expect to need semantically
for refined-cerberus). You can take a look at what has landed on main in the
other repo". [AGENT]: §1 (measured on `mdd/cerberus-lean`), §2 (quoted from
their risk-map baseline §6), §3–§4 (our register; the F-items are
expectations from the Lane C note, the RefinedC donor and the review's Part
B5, not rulings). Review: `docs/2026-09-07_review-demo-master-plan.md`.
