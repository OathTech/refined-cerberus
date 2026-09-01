# Fresh foundational re-audit of `cerberus-heaplang` (arc exit gate)

Date: 2026-09-01
Auditor: FRESH re-auditor (new agent; did not author any of the arc;
terms of reference = the 2026-08-31 foundational audit's brief +
its acceptance suite, per the arc plan).
Tree audited: branch `heaplang-foundations` @ `4dc79a3`, clean at
audit start and end (all plants reverted; `git status` empty).
Method: every claim re-derived against the TREE — sources read, the
full gate suite re-run independently, probes via
`lake env lean --stdin`, two mutation plants executed end-to-end
and reverted, one perturbation executed end-to-end and reverted.
Quoted outputs are verbatim; derived tallies are labeled.

## Verdict

**ZERO High findings. The arc's exit criterion is met: the arc is
DONE by its own terms.** Three Low findings (documentation/instrument
precision, none touching a theorem, a cone, or a gate's soundness)
and a short observations list are recorded below with suggested
one-line fixes. Every one of F-01..F-10 re-verified as disposed
exactly as the arc summary claims; the acceptance suite's evidence
reproduced wherever I re-ran it, byte-for-byte where transcripts
were quoted.

## Independent gate baseline (this audit, this tree)

`./scripts/test_unit.sh` re-run start-of-audit: exit 0, ALL GATES
GREEN. The two sweep lines, verbatim, matching the README /
walkthrough / acceptance-record quoted tails exactly:

```
info: CerberusHeapLang/Audit.lean:624:0: CerberusHeapLang axiom sweep: 1123 theorems BOUNDED by the declared upper bounds (71 in the production-entry boundary modules, of which 13 carry the boundary axiom — each STATEMENT-BORNE, origin-checked, so every boundary cone is exact-by-construction: trio + runEffectful iff the statement carries it; all other theorems bounded by the trio; headline cones additionally pinned above)
info: CerberusHeapLang/Audit.lean:624:0: CerberusHeapLang banned-axiom sweep: 2075 constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
```

Gates 4 and 5 are genuinely wired in `scripts/test_unit.sh` (code
read: gate 4 regenerates the manifest, diffs against the committed
copy, fail-closed on a red generator, and ties the README
MANIFEST-SCOPE token block to the ADEQUACY-EXPORTABLE line; gate 5
regenerates the census and diffs against
`docs/STATEMENT_CENSUS.txt`, fail-closed on missing file / red
generator / drift). Both ran green in my baseline.

## F-01..F-10 re-verification

| F | Original defect | Re-verified state on this tree | Verdict |
|---|---|---|---|
| F-01 (High) | `Ecase` advertised but outside the adequacy cone; `wps_case_value` consumerless | `Frag.case_value` is IN the one cone (Soundness.lean:3578 cone, with explicit branch-closure + branch-size premises); two-sided pair `engine_complete_caseU` (Soundness.lean:4905) exists; **`case_certified` (CaseExhibit.lean:136) read in full: a genuine adequacy consumer** — a BINDER-pattern case program (the substitution tau genuinely fires, `caseProg_select` is `rfl`), concluded in engine vocabulary (`drive … ≠ .killed/.stuck`, delivered value = scrutinee) through `wps_case_value → wps_sound → spike_engine_adequacy`; manifest row `case-value` FULL-ROW; cone pinned exactly trio (probe re-run) | CLOSED |
| F-02 (High) | Totality an operational side proof; `blockSpecs_intro_variant` consumerless, decrease optional | `blockSpecs_intro_variant` exists **nowhere as code** (grep: comments only). `wpt` (Wpt.lean) read in full at the definition: structural recursion on the budget, the decrease `⌜1 + m ≤ k⌝` is a conjunct **inside the definitional jump clause** (wpt.pre:126) — not a hypothesis; `blockSpecsT` verifies every label body at its own claimed variant `m`, so back edges strictly decrease; escape-hatch hunt over ALL `wpt` rules (full `^theorem wpt` enumeration): only `wpt_run` concludes at a jump redex and it demands `1 + m ≤ k`; the only budget-relaxing rule is upward weakening (`wpt_mono_k`), sound for an upper bound. `wpt_sound` collapses into pinned Iris `TotalWeakestPre`; both adequacy halves separated as ordered (`wpt_strongly_normalizing` via `twp_total` as-is; `wpt_engine_boundU/J` the generic measure→drive-fuel simulation, statements read). Exhibit grep re-run: **zero** `Step.*`/`driveJ_step` code occurrences in the five loop exhibits (six hits, all doc lines, each read). fib total proof verified riding `fib_body_wpt`/`wpt_run` at variant `2·(n−i)+3`. The actual decrease-deletion plant re-run (below) breaks `wpt_sound`/`wpt_run` exactly as recorded | CLOSED |
| F-03 (High) | Hand-duplicated frozen projection; six parallel cones; frozen profiles | Parallel-cone hunt: `inductive` grep finds exactly `Redex`/`Decomp` (the one redex grammar + one decomposition), `Frag` (the ONE cone), and `StraightFrag` — the last documented in-source (Soundness.lean:353, :1682) as a per-theorem completeness DOMAIN (with `StraightFrag.toFrag`), not a coverage authority; `FragP`/`FragJ`/`RedexJ`/`DecompJ` survive only in retirement comments. `MachineCtx` (Step.lean:326) carries exactly the 11 fields of the design-record table; the label map is DERIVED (`MachineCtx.labels`, matching step_ctx's Erun read); live state is the relational triple. Iris `primStep` IS `Step` (Lang.lean instance read: definitional). `engine_step_matchU` (Soundness.lean:~4396) is at ANY `MachineCtx` over the full cone. Manifest row set derived from `Frag` in the environment; mirror coverage exactly `Step`'s constructor list (generator code read; fail-closed plant re-run below) | CLOSED |
| F-04 (High) | Exhibits defined their own WP-lifting rules | Hunt across all exhibit modules for WP-rule definitions: every `wps_*`/`wpt_*` theorem in ArrayExhibit / StructExhibit / ListRevExhibit / TreeRotExhibit is a **term-mode one-liner instance** of the core generic rules `wps_load_cell_at`/`wps_store_cell_at`/`wpt_*_cell_at` (Wps.lean:1956/2049, Wpt.lean:1517/1607) — read at source; no `wps.pre`/step-level reasoning in any exhibit. The generic layer (views, `wps_load_at`/`wps_store_at`, `wps_create`) lives in core modules | CLOSED |
| F-05 (Medium) | "production" name on a driveJ theorem | The rename is real: `counter_loop_certified_registration` (ProdEntry.lean:~440, driveJ lane, honestly labeled). The three `*_production` theorems (ProdLoopExhibit.lean:97/222/684) read in full: each statement's execution function is `CerbND.runND (_root_.drive fmapEmpty false (prodFile …) args) (initial_driver_state (prodFile …) fs)` — and I verified in the pinned generated source that `drive` (Driver.lean:500) and `initial_driver_state` (Driver.lean:435) are the shipped pipeline. No package `drive`/`driveJ` in any of the three statements; `prodFile`/program terms are data; conclusions use the documented spec idioms (`CellCoh`, `SeedChain`, `Sat`). The only remaining `*_production` names in ProdEntry are the `LabeledAt` registration ties (statements about the shipped registration — not misnomers) | CLOSED |
| F-06 (Medium) | List spec weaker than in-place reversal | `list_reverse_certified_total` statement read in full (ListRevExhibit.lean:1963): identity-indexed `ns : List (Int × Int)` (allocation id × value), `SeedChain Q p' ns.reverse` (same ids, exactly reversed order, own values), literal footprint equality `∀ k, (get? Q k).isSome ↔ (get? m₀ k).isSome`, arbitrary disjoint frame `R` returned verbatim (`Q ##ₘ R ∧ Sat σ' (Q ∪ R)`), unconditional `driveJ` equation at the derived bound `13·|ns|+7` — no fuel hypothesis, no GF binder. Second client `tree_rotate_certified{,_total}` present (own layout, branching predicates, 3-file commit verified below) | CLOSED |
| F-07 (Medium) | Upper-bound audit called exact | Sweep code read line-by-line (Audit.lean:596-706): exhaustive theorem sweep by module-of-origin (not namespace), unresolvable-module constants held to the trio, `isInternalDetail` only skip; **origin discipline real**: boundary theorems carrying `runEffectful` must reach it through the STATEMENT's constants (`carriesAx` closure over types AND bodies), else `throwError` → build failure; boundary = exactly the three statement-carrying modules; pass 2 checks banned axioms on every constant kind. Public wording now "BOUNDED … exact-by-construction", accurate. Pins: 63 `#guard_msgs` blocks / 62 distinct theorems (`wps_sound` pinned twice — derived tally), covering the README verify-me list, all exhibit-table exports except the interior `wp_store`/`wp_load` row (see finding L3). 13 probe re-runs all exact | CLOSED (fallback form; see L3/L4) |
| F-08 (Known blocker) | `runEffectful` boundary | Still open, honestly: I verified LemLib.lean:54 still carries the axiom in BOTH the vendored `.lake` copy and the lem-lean mainline checkout — the record's "retirement NOT landed" status is true, the fallback (minimal 3-module boundary + origin discipline + statement-borne-only, 13 carriers) is in force and reproduced in my sweep run; mover registered in the Audit.lean header with [USER] provenance | HELD (fallback as documented) |
| F-09 (Medium) | Doc contradictions; no coverage matrix | Fresh contradictions hunt: the old specific contradictions are gone (README Lang.lean row now records the deliberate ABSENCE of `Language.Context` with the falsification reason; Ecase claimed at exactly its manifest level; "wrong mirror only unprovable" slogan carries the F-09 caveat verbatim; expected-tail blocks match my own build's output byte-for-byte). The manifest is the authoritative matrix and is gate-enforced. New (small) claims-vs-tree gaps found: L1-L3 below | CLOSED (new Low residue) |
| F-10 (Known limitation) | Whole-alloc ownership; no alloc rule | Ownership split read at source (Heap.lean): per-byte `bytesOwn` (split/join at real ∗, `bytesOwn_append` both directions), fractional `metaOwn` (via the GenHeap `Fractional` instance; `metaOwn_agree`), typed views with `pointsToView_split`/`pointsToView_join` — **fraction arithmetic checked**: split consumes `.own (q₁+q₂)` into `.own q₁ ∗ .own q₂` with the byte range split at the list decomposition (byte fraction rides whole on disjoint addresses — sound); join re-derives the bounds facts; no duplication law exists. `wps_create` (Wps.lean:2192) allocates through the owned cursor; the OOM arm is the pure `freshBase … ≠ 0` premise computed on OWNED state (not assumed away); consumer `struct_create_store_wps` | CLOSED |

## Acceptance-suite re-run (what I ran vs spot-checked)

| # | Test | My action | Result |
|---|---|---|---|
| 1 | Rule-consumption | RE-RAN gate 4 (full suite); read the generator (all 622 lines): row set enumerated from `Frag` in the environment, mirror claims must be exactly `Step`'s constructor list, `OK` cells name-and-kind checked, DECLARED granularity honestly stated in the output itself; PLUS an adversarial fail-closed plant (below) | PASS — committed manifest drift-free; machine tail: 18 rows + evaluator row, all ADEQUACY-EXPORTABLE and FULL-ROW, LOCAL-RULE-ONLY empty |
| 2 | Fresh-client | Spot-checked the commit-diff evidence myself: `git show --stat 2f15f98` (StructExhibit: 6 files — exhibit, lib root, Audit pins, README, manifest generator+regen; NO core module) and `4e86c08` (TreeRot: exactly 3 files). Read both exhibits' rules: all one-line clients | PASS |
| 3 | Perturbation | **RE-RAN end-to-end myself**: `fieldY 8 → 12` (single-constant diff confirmed), full package rebuild → `Build completed successfully (443 jobs)` with the audit sweeps green, ZERO further edits; reverted; green. Grep re-confirmed `fieldX`/`fieldY` appear only in StructExhibit.lean | PASS (reproduced) |
| 4 | Totality | RE-RAN the grep (verbatim-identical six doc-line hits, each line read); verified at source that the total exports ride `wpt`→`wpt_engine_boundJ` and that `TotalWeakestPre`/`twp_total` are genuinely consumed; `diverge_total_unprovable` read in full (the self-step, non-normalization, and the False conclusion are all real) | PASS (reproduced) |
| 5 | State-read census | Spot-verified against the tree: `MachineCtx` = exactly the 11 design-record fields; labels DERIVED from proc/extern/runState.labeled; `Step` over the live triple; `engine_step_matchU` at arbitrary `MachineCtx` | PASS |
| 6 | Production | Read all three statements at source; verified `_root_.drive`/`initial_driver_state` in the pinned generated Driver.lean (:500/:435) are the shipped composite; no package execution function in any statement; probed all three cones: exactly trio + `runEffectful` | PASS |
| 7 | Axiom | RE-RAN the full suite (sweep lines verbatim, 1123/71/13, 2075); probed 13 headline cones via `--stdin` (all exact as pinned); verified upstream axiom still present (fallback honest); verified pin count (62 distinct) | PASS (fallback form, as documented) |
| 8 | Mutation gates | **(d) RE-RAN end-to-end**: deleted `⌜1 + m ≤ k⌝ ∗` from `wpt.pre`'s jump clause + `wpt_jump_eq` (the consistent mutation); build exit 1 with EXACTLY the six recorded error lines (Wpt.lean:209/239/354/766/838/1863 — `wpt_run` and `wpt_sound`'s collapse break); reverted; green. **(a) RE-RAN the gate-4 channel**: unclaimed `Step.wseq_ctx` in a temp copy of the generator → exit 1, verbatim the recorded "mirror constructor … has NO manifest row" error. (b)/(c) spot-checked against the tree: the target lines exist as recorded (`engine_step_matchU`'s load arm ~:4424; `CellCoh.bytes` ~:255 consumed at the load rule's readout ~:343 — genuinely load-bearing premises, so the structural-forcing argument holds). Gate-5 plants: record transcripts consistent with the gate code I read (drift/red-generator/missing-file all fail) | PASS (both re-run plants reproduced byte-for-byte) |

## New findings (fresh-eyes pass over the arc's new surface)

No High. No Medium. Three Low:

**L1 (Low, doc accuracy)** — Walkthrough §5.4 item 2 lists
`counter_loop_certified_production` among the statements the census
surfaces, but the census's pinned list
(`scripts/statement_census.lean:50`, and hence the committed
`docs/STATEMENT_CENSUS.txt`, which I confirmed contains exactly 12
theorems) does not include it. The sentence's substance (finite-map
vocabulary in that statement) may be true but is not
census-witnessed. Fix: reword, or better, L2.

**L2 (Low, instrument scope)** — The census freeze-gate (gate 5)
covers the 12 verify-me theorems only; the three Phase-5 production
exports (`fib/counter_loop/list_reverse_certified_production`) —
the arc's headline new statements — are axiom-PINNED but not
census-FROZEN, so the acceptance record's test-8(c) protection
("statement-vocabulary weakening is caught by gate 5") does not
extend to them. All in-scope claims surfaces state the census scope
accurately, which is why this is Low, not Medium. Fix: add the
three names to `pinned` and re-baseline the census in one commit.

**L3 (Low, claim inexactness in the acceptance record)** — Test 7's
"the curated pin list … now covers every theorem in the README's
exhibit table": the exhibit table's first row (`wp_store`,
`wp_load`, explicitly interior) has no curated pins — they are
sweep-BOUNDED only. Every export-lane theorem in the table IS
pinned. Fix: two pins or one clause ("every exported theorem").

**Observations (no action required; recorded so the next reader
does not rediscover them):**

- The origin discipline proves cone-exactness ("trio +
  `runEffectful` iff the statement carries it" — correct, and I
  verified the iff argument: statement-carriage forces cone
  membership via `collectAxioms` over the type). The finer README
  phrase "fails the build on any proof-borne occurrence" is exact
  only for theorems whose statements do NOT carry the axiom — for
  the 13 statement-borne carriers, additional proof-side use would
  be cone-invisible in principle. The semantic backstop (the
  trio-only DriverCollapse layer concludes at arbitrary run states)
  is what carries the "holds for every seam value" argument, and it
  is in place.
- `wps_sound` is pinned twice in Audit.lean (63 blocks, 62 distinct
  — the record's "62 pins" counts distinct). Cosmetic.
- `StraightFrag` (Soundness.lean:1739) is a second grammar, but
  documented in-source as a completeness DOMAIN with an injection
  into the one cone, not a coverage authority; the general
  straight-line production entry (`prod_run_eq`/`sem_triple_prod`)
  is scoped by it. Watch it if the straight-line lane grows.
- Registered items 1-10 of the arc summary each check out as real
  and honestly labeled where I touched them (`hfuel2` present on
  exactly the three partial driveJ loop exports; GF binder only on
  `semantic_triple_sound`, load-bearing; Ecase EVAL arm / Ewseq
  binder patterns registered in README + Step.lean).

## State of the demo (closing assessment)

Yes — on this tree, without qualification games, this is a
legitimate Reynolds/O'Hearn separation logic over the Cerberus Core
engine with honest claims. The separating conjunction is Iris BI
over real ghost ownership of engine memory; the small axioms,
frame, fractional reads/full-ownership writes, structurally
recursive representation predicates, and textbook loop invariants
are all genuinely present and genuinely consumed; allocation is in
the logic through an allocator resource; interior access is one
generic typed-subrange rule pair with exhibits as verbatim
one-line clients (demonstrated by an actual layout perturbation
rebuilding green). Total correctness is now a logic result — a
budgeted total judgment with a definitionally mandatory back-edge
decrease, collapsing into pinned Iris TotalWeakestPre, with a
semantic negative test and a plant-verified structural tripwire —
and the flagship theorems say the strong thing (same-footprint,
in-place, framed, terminating) while three loop theorems conclude
about the literally shipped `runND ∘ Driver.drive ∘
initial_driver_state` composite from a cold start. The trust story
is stated at exactly its strength: one declared temporal boundary
axiom, statement-borne and mechanically origin-checked, with a
live upstream mover; an upper-bound sweep that says "bounded" plus
curated exact pins; a cone-derived, gate-enforced capability
manifest as the single scope authority; and the residual scope
limits (fragment size, fuel side conditions, one-sided match lanes,
whole-cell exhibits' seeded pre-states) written on the claims
surfaces themselves. The three Low findings are documentation and
instrument-scope trims, not cracks. The foundations arc is done;
the port is unblocked from this side.
