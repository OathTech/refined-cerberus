# What we still need from cerberus-lean — the requests register (demo v1, and the RefinedC-family layer after it)

Status: DRAFT for the operator [AGENT orchestrator, 2026-09-07]; companion to
`docs/2026-09-07_demo-master-plan.md`. Written at refined-cerberus main
`777ca0f`, pin cerberus-lean `89f7e688530c6910884518811d645e4e892e4507`, and
after reading what has landed on the cerberus-lean mainline
(`mdd/cerberus-lean` at `94f339eb4`). Requests to the semantics team travel
as dated notes in `refined-cerberus/docs/` relayed by the operator; nothing
here is filed by being written here. Every claim about the other repository
is from its committed records and `git`, labelled where DERIVED.

## 1. What has landed on the cerberus-lean mainline since our pin

30 commits, `89f7e68..94f339eb4` (DERIVED: `git rev-list --count`). By
content (DERIVED from `git diff --stat`, grouped by path):

- **No semantics change.** The generated engine (`lean_frontend/generated/`),
  the hand-written seams and the `.lem` sources are untouched; the only
  Lean/lem additions are a failure-reach probe test (`FailureReachProbe.lean`)
  and its `.lem` fixture under `tests/failure-probes/`. Consequence: **our pin
  is current in substance; no re-pin is forced by anything on their mainline
  today.**
- **Validation foundations** (2026-09-06/07, several commits): an independent
  upstream oracle, complete observation capture, a cold provider proof, a
  failure census, the documented test ladder run (Tier A 13 gates), release
  hardening, diagnostic-styling pins (`NO_COLOR=1`, `TERM=dumb`), evidence
  reconstructibility rules.
- **The csmith corpus sweep after P0** (6 shards): `mismatch=0` everywhere on
  the whole-line Defined comparison; two rows MATCH → TIMEOUT at the 15 s
  budget registered as pending (their TODO).
- **The risk-map baseline audit** (`2026-09-07_risk-map-baseline.md`, with the
  orchestrator's review §8): six surfaces; §6 is a read of OUR consumer
  surface — it confirms every one of the ten provider change manifests since
  their anchor B is adopted in our sources at the current pin, and lists the
  "actual promised statements" (§3 below quotes the ones that bind us).
- **Pure-failure correspondence**: a reachability census of the 231
  exec-closure pure failure sites, the correspondence design (an `Outcome`
  type, a generated strict twin, a connection theorem), then the design
  **PARKED** with the census outcome "0 discardable sites; option C; flip
  conditions" (`94f339eb4`). Reading: no pure `failwith` in the exec closure
  is discarded, so the kind-1 discrepancy class that motivated the design is
  empty at the pin; the strict-twin route is parked until a flip condition
  (their commit message) makes it live.
- **A Codex charter for fuel-measure cost** (branch `arc/fuel-measure-cost`,
  not mainline): measure and remove the fuel arc's execution cost; fuel
  MONOTONICITY was explicitly rejected as that charter's subject ("no
  fuel-kill at n" is not statable for `drive` with pending workers exhausting
  into opaque sentinels; its shape must be fixed with the operator).
- **Unmerged**: `feature/concurrency` (S0–S7, 13 commits beyond mainline; its
  diff against mainline does not touch the four generated driver files the
  demo mirrors — DERIVED, `git diff --stat` on `Driver.lean`, `Core_run.lean`,
  `Nondeterminism.lean`, `Core_reduction.lean` is empty); its merge is a
  re-pin scout event for us regardless (the scheduler's shape is what E6
  builds on).

## 2. What we consume today, and what the provider has promised about it

From the risk-map baseline §6 (their words, "actual promised statements"):

| provider statement | what it means for the demo |
|---|---|
| fuel is a quantified `[LemFuel]` parameter; the zero-fuel and sufficiency lemmas exist at HEAD with the §3 restrictions; "general absorbing propagation/monotonicity is not among the delivered conclusions" | our exports are ∀-fuel above program-derived floors by our own proofs; we need NO monotonicity lemma (master plan §3.3; kill-adequacy note §5) |
| Pmap/Fmap lookup laws exist with comparator/WF hypotheses; EnvLaws supplies them | our 2026-09-03 lem-lean request is CLOSED |
| arbitrary tag environments require `Acyclic`/`AcyclicPair` for the six conditional sufficiency theorems; our fragment uses empty/concrete tag environments | binds V2-3 (structs): lifting `htd : tagDefs = ∅` means discharging acyclicity at the real entry |
| allocation exports narrowed at Z2 (positive alignment, nonnegative size, no requested-address `create`) — visible premise changes | KOI B21; carried honestly; nothing to request |
| kind-1 `panic!` arms: "native fail-stop and in-process default denotation are not yet connected by a faithful outcome theorem"; consumers should NOT mark exports PROVISIONAL merely for pending fuel rows | KOI A5; §3 R-2 below |
| provider-native correspondence, strict failures, byte-string parity, broad accepted-domain/completion claims remain open (their master plan steps 2–3, 5); consumer whole-file/library adequacy is separately open (our A7) | A7 is OURS to close (master plan V1-1); §3 R-4 asks the one question it needs answered |

## 3. Requests and needs for the demo (v1) — the register

Status vocabulary: FILED (a dated note exists in `refined-cerberus/docs/`),
ANSWERED (landed at the pin or later), OPEN (no note yet; this register is the
first statement), NONE (we thought about it and need nothing).

| id | need | why | status | ask |
|---|---|---|---|---|
| R-1 | a distinguished, transparent fuel-exhaustion outcome in the driver monad | root of trust: no home-made driver ([USER 2026-09-02]) | FILED `docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md` → **ANSWERED** by the fuel arc: `CerbND.fuelExhaustedKill = Error0 fuelExhaustedLoc fuelExhaustedMsg`, distinguishable by constructor from `Undef0` | none further |
| R-2 | the 117 `panic!` arms (A5) connected to a faithful outcome | negative claims at an arm are provisional; our covered programs reach none (their census) | their master plan; the pure-failure design PARKED 2026-09-07 with flip conditions | **keep the reachability census maintained and tell us when a flip condition fires**; when a typed-failure outcome lands we adopt it at the next re-pin and re-examine the kill-adequacy terminal (`Undef0` is the channel their design does not move) |
| R-3 | fuel monotonicity ("done at n ⇒ done at every m ≥ n", their TODO 13) | — | NONE for the demo: the WP-style proofs give ∀-fuel statements directly; the kernel cannot evaluate the driver, so a "compute at one fuel and lift" route is not ours | none; their own instrument concern |
| R-4 | **the pipeline's whole file as the statement's referent (A7)**: the linked std.core, the pinned gcc `impl` map, the elaborator's emitted `main` — as ONE artefact we can read into a Lean data term | criterion 4 of the definition of done; master plan V1-1 | OPEN — the G2 work on the parked branch reads the emitted `.annot.core` text with a script; whether the post-`core_linking` file (with `impl0` bound and the whole stdlib) is emitted with a stable printer, and where, is the one question to settle with the provider before V1-1 starts | **a note asking: (i) which command emits the linked file the driver actually runs, (ii) whether its printer is the same `pp_core.ml` the corpus check mirrors, (iii) a stable structured dump (JSON or S-expressions, annotations included) if the text printer is lossy — see R-7** |
| R-5 | a structural size lemma for generated substitution (`esize (subst_sym_expr x v e) = esize e`, and the `subst_sym_pexpr`/label twins) | we carry two `evalDepth`-shaped premises per program in `wpt_driver_done_alloc`'s label hypothesis (`hQd`, ProdLoop.lean, 2 sites) and discharge them per program | FILED `docs/2026-09-05_note-cerberus-lean-subst-esize.md` (a duplication-avoidance note; "no action requested") | unchanged: if the lem-lean backend or cerberus-lean ships size lemmas for generated substitution, we consume them and drop the premises |
| R-6 | `mk_conv_int`'s signed non-representable arm vs std.core's `conv_int` (impl-defined `<Integer.conv_nonrepresentable_signed_integer>`) | an upstream Cerberus divergence, invisible for the gcc impl (both wrap) | FILED `docs/2026-09-05_note-cerberus-lean-conv-int-divergence.md` (register note; not a request) | none; upstream-tray candidate on their side |
| R-7 | a structured (non-text) emission of the Core file | the corpus whole-text check cannot see what `pp_core.ml` never prints (`Aexpr`, `Astmt`, `Alabel`, `Acerb`, `Ainlined_label`, `Auid`, `Aattrs`, `Avalue`; `Erun`'s annotation; symbol digests; action locations; save passing modes) — KOI C20; V1-1's data-term route would read it instead of parsing text | OPEN ("if ever needed" in C20; V1-1 makes it needed) | fold into R-4's note |
| R-8 | `dynamic_addrs` upstream defect (A3) | outside the logic; our `free` precondition implies the engine's check | provider ISO-fix register R4 DEFERRED upstream | none for v1 |
| R-9 | the sequential scheduler stays the default and stable | every export runs `drive fmapEmpty false …` through the shipped scheduler loop with one thread; E6 (calls) builds on the scheduler-round shape | OPEN as an expectation, not a request | **a one-line confirmation, when `feature/concurrency` merges, that the sequential model is the default instance and `drive`'s signature is unchanged; a re-pin scout window for us** |
| R-10 | the S5 "Epar-free agreement" lemma we asked the concurrency team for (their S5 accepted it as a proof obligation, "not discharged") | E6's scheduler induction would use it | FILED via the S1 interface review (`docs/2026-09-04_response-concurrency-S1-interface-review.md`); status not visible in their mainline records | **operator to ask its status at the concurrency merge** |
| R-11 | fuel-measure cost (their Codex charter) | our full builds are ~90 s wall for 56 modules; not a problem today | NONE; welcome | none |

Nothing in this table blocks V1. R-4/R-7 are the one question to settle
before V1-1; everything else is tracking.

## 4. What the RefinedC-family layer (refined-cerberus) will need semantically

From the Lane C design note (`docs/2026-09-04_refinedc-layer-design-2.md`),
RefinedC's own architecture (the donor at `deps/refinedc/`, read-only), and
what the demo taught us. These are EXPECTED needs, stated so the semantics
team can plan; none is filed. Ordered by when the layer would hit them.

| id | need | when | what exists at the pin | what would be asked |
|---|---|---|---|---|
| F-1 | **stable located Core with attributes preserved**: RefinedC specifications enter as C attributes (`[[rc::…]]`); the elaborator keeps `Aloc`, `Astd`, `Aattrs`, `Auid`; the demo strips locations (Lane C §4) | first spec-carrying slice | `Aattrs`/`Aloc` exist in the AST; the text printer prints `Aattrs` only at debug > 3 | a guarantee that C attributes reach the Core annotations unchanged, and R-7's structured dump so they can be read |
| F-2 | **function calls as first-class**: `Eproc`/`pcall` rounds, the call protocol, RETURN's control effects (Lane C §3.1) — and, for RefinedC's function pointers, the `funptrmap`/`PtrEq` arm (B8) | E6 (demo V2-4), then the layer's calls | all present in the engine; our mirror does not cover `Eccall` | documented stability of the call/return rounds and the function-pointer map across pins |
| F-3 | **the memory model as a specified interface**: struct/union/array layout (`tagDefs`, offsets, padding, `CerbTagsWf`, acyclicity), pointer arithmetic and provenance, alignment, the byte representation of every scalar (`intToBytes`, `reconstructValue`), and TYPED UB for out-of-bounds, use-after-free, misaligned access | structs (V2-3) and every RefinedC type after `int` | the concrete model behind `drive`; 60 of the 117 `panic!` arms are in `CerbMem.lean` (A5); the "defacto" model is unreachable from `drive` (their F-C2-4); byte-representation producer contracts are on their small-items list | (i) the memory-model seam's contract written down (which operations, which failures, which model); (ii) UB as `Undef0` outcomes rather than `panic!` in the memory seam — the prerequisite for UB-freedom specifications at scale; (iii) which model is the semantics of record for C verification (concrete vs provenance-aware) |
| F-4 | **the UB catalogue**: `Undef0 loc ubs` with the ISO `undefined_behaviour` list, complete for the C fragment the layer covers | the layer's first UB-freedom claim | the list exists in the generated AST; kills are classified by `EvalFail`; only pure-evaluation kills are characterised in the demo | a statement of which UBs the exec pipeline can raise, per construct — so "UB-free" can be stated as "none of these" |
| F-5 | **integer semantics with the impl map as a parameter**: `conv_int`/wrap/impl-defined arms, `impl0` bound to the pinned gcc map (R-6's divergence lives here) | the layer's int types (B15 byte images, B21 allocator contracts) | present; `impl0 = ∅` in our hand-built file (A7) | R-4 (the linked file) settles it for the demo; for the layer, the impl map as an explicit parameter of statements |
| F-6 | **typed failures**: their master plan steps 2–3 (strict failures, the `Outcome` type) — so that "the run neither panics nor discards a failure" is a theorem | the layer's soundness statement | PARKED (0 discardable sites at the pin) | R-2: notice at the flip |
| F-7 | **the C frontend as a stable pipeline**: `.c` → elaborated Core with a versioned dialect for the constructs the layer covers (arc E's lesson: every C feature is a set of emitted Core shapes, and the shapes move with the elaborator) | continuously | the emitted corpus and the whole-text check catch drift per program | a dialect note per elaborator change that alters emitted shapes for covered constructs (a changelog, not a theorem) |
| F-8 | **concurrency, later**: the SC-DRF instance behind a parametric model selector (S1), the sequential instance as default | after the demo, when the layer meets threads | `feature/concurrency` S0–S7 unmerged | R-9/R-10 first |
| F-9 | **performance of the generated semantics** for proof work: kernel-evaluable layouts (`decide` on concrete `tagDefs`), build time of the generated modules | continuously | their fuel-measure-cost charter | none now; the F-C3-4 eager-measure backlog is the item to watch |
| F-10 | **a kernel-checkable concrete run**, i.e. computing `runND (drive …)` for a small program inside the kernel | negative tests and refutation at the layer (RefinedC has none; a refutation lane would be new) | not possible today (the E3 notes: `decide +kernel` does not reduce the driver) | not requested: the kill-adequacy design (option A/B) takes the WP route instead |

## 5. How requests move

A request is a dated note in `refined-cerberus/docs/` (`*_request-*.md` or
`*_note-cerberus-lean-*.md`), written [AGENT] with the ruling it answers
quoted, relayed by the operator, and closed in this register when the
provider's change manifest names it and our adoption is visible in source
(the risk map §6 method). This register is re-issued at each re-pin.

## 6. Provenance

[USER 2026-09-07]: "a companion document which says exactly what we still
need from cerberus-lean (including what we expect to need semantically for
refined-cerberus). You can take a look at what has landed on main in the
other repo". [AGENT]: §1 (measured on `mdd/cerberus-lean`), §2 (quoted from
their risk-map baseline §6), §3–§4 (our register; the F-items are
expectations from the Lane C note and the RefinedC donor, not rulings).
