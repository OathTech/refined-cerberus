# cerberus-heaplang

A demonstration separation logic for the Cerberus Core engine — the
HeapLang-analog of the cerberus-lean semantics. A small Iris program
logic (points-to, the store/load small axioms, frame, sequencing,
consequence) is built over a tight fragment of the Core AST and then
**certified against the production cerberus-lean pipeline from cold
start**: the exported theorems quantify over the shipped
`initial_driver_state` and conclude equations about the very
`CerbND.runND (Driver.drive …)` composite that the cerberus-lean
executable runs.

**What this is NOT**: the RefinedC port. That development — the
Lean-native RefinedC-architecture verifier — lives alongside, in
this repository's root `RefinedCerberus` package, and is the actual
product; this package is a self-contained demo that the attachment
pattern (mirror step relation → Iris logic → per-rule engine
certification → production-entry export) works end-to-end.

## The trust story

The only trusted semantics is the cerberus-lean operational
semantics (the Lean port of Cerberus Core, pinned by commit in
`../scripts/semantics-pin.env` and differentially validated upstream
against the OCaml oracle); everything in this package is derived and
proved down into that engine. Every theorem is kernel-checked with
its exact axiom cone asserted in-build (`CerberusHeapLang/Audit.lean`,
the last import of the library root): all cones are exactly the
classical trio (`propext`, `Classical.choice`, `Quot.sound`), except
in the two production-entry modules (`ProdEntry`, `ProdExhibit`)
whose statements mention the shipped initial driver state and
therefore additionally carry the semantics repo's one residual axiom
`runEffectful` — a declared TEMPORAL boundary, entering through the
statements only, whose upstream retirement is planned (after which
this boundary vanishes at a pin bump with no restatement here).
Non-kernel proof methods (`native_decide`, `bv_decide`, `ofReduce*`)
are banned by a grep gate and would in any case enter a cone and
fail the audit — a build that weakens any of this fails.

## How to build

From the repository root (offline; deps resolve through the
container's git redirects, which `scripts/capped` self-loads):

```bash
scripts/setup-cerberus-dep.sh        # once: the pinned semantics workspace
cd cerberus-heaplang
../scripts/capped ~/.elan/bin/lake build
```

A green build IS the verification run: it elaborates every proof
through the Lean kernel and then `Audit.lean`, which sweeps the
transitive axiom cone of every theorem in the package and pins the
headline theorems' exact cones. Expected tail:

```
info: CerberusHeapLang/Audit.lean:201:0: CerberusHeapLang axiom sweep: 285 theorems within the declared boundary (34 in the production-entry boundary modules, trio + runEffectful; all others trio-exact)
Build completed successfully (424 jobs).
```

Or run both packages plus the grep gate: `scripts/test_unit.sh` from
the repository root.

## How to verify me

Spot-check the headline cones yourself (from `cerberus-heaplang/`):

```bash
../scripts/capped ~/.elan/bin/lake env lean --stdin <<'EOF'
import CerberusHeapLang
#print axioms CerberusHeapLang.semantic_triple_sound
#print axioms CerberusHeapLang.semantic_frame
#print axioms CerberusHeapLang.engine_complete
#print axioms CerberusHeapLang.exhibitA_prod
EOF
```

Observed output (2026-08-31, this checkout):

```
'CerberusHeapLang.semantic_triple_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.semantic_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.engine_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.exhibitA_prod' depends on axioms: [propext, runEffectful, Classical.choice, Quot.sound]
```

Expected: the first three report exactly
`[propext, Classical.choice, Quot.sound]`; `exhibitA_prod` reports
`[propext, runEffectful, Classical.choice, Quot.sound]` (the one
declared temporal boundary, above). `sorryAx` appearing anywhere is
a failure.

## Worked tour (the modules, in build order)

| Module | Contents | Headline |
|--------|----------|----------|
| `Step.lean` | The fragment's mirror small-step over the ENGINE's generated AST/state types (values, `store`/`load`/`create`, strong sequencing, the annotation residue) — hand-written, zero authority until certified | `Step` |
| `Heap.lean` | Points-to over the engine's memory state via iris-lean GenHeap (allocation-rooted byte-list cells); the memM-level store/load facts | `pointsToCell` (`↦c`), `storeM_success`, `loadM_success` |
| `Lang.lean` | The iris-lean `Language` instance over Step (evaluation contexts, wp_bind for real `Esseq`) | `instance : Language CoreExpr Mem Empty SpikeVal` |
| `Rules.lean` | The logic: small axioms, sequencing, frame, consequence, wand — plus the compositional exhibit-C triple | `wp_store`, `wp_load`, `wp_sseq`, `triple_frame`, `triple_seq`, `triple_conseq` |
| `Soundness.lean` | Per-construct certification of Step against the engine's own `step_ctx` + request discharge (context-undisturbed shape; refusals classified) | `engine_complete` |
| `Adequacy.lean` | The exported semantic face over engine configurations: triples with an arbitrary framed rest, driven by the engine's step function | `semantic_triple_sound`, `semantic_frame`, `spike_engine_adequacy` |
| `Exhibit.lean` | End-to-end exhibits at the engine level: store-then-load returns 7; the frame exhibit; termination of the probe as a theorem | `exhibitA_engine`, `exhibitB_engine`, `exhibitC_engine`, `exhibitA_terminates` |
| `DriverCollapse.lean` | The production scheduler/ND/readout collapsed onto the demo's drive loop — proved from the driver's OWN round functions; entirely trio-exact | `prod_loop_done`, `driver2_done`, `finalize_done` |
| `ProdEntry.lean` | Cold start from the SHIPPED `initial_driver_state` (errno allocated by the real allocator) + the production-entry theorem: the production run IS the singleton Active execution satisfying the postcondition | `sem_triple_prod`, `prod_run_eq` |
| `ProdExhibit.lean` | The demonstration: a self-contained program (create/store/load) run through the production pipeline delivers 7 with the exact final bytes | `exhibitA_prod` |
| `Audit.lean` | The in-build axiom gate: curated exact-cone pins + the exhaustive sweep with the module-scoped `runEffectful` boundary (plant-tested both directions — see `docs/2026-08-31_restructure-notes.md`) | the sweep |

History and design findings: the spike records in `docs/`
(`2026-08-30_spike-report.md` is the closing report; plan, recon and
slice notes alongside).

---

Built by AI agents (Claude, Anthropic) under the direction and
review of Mike Dodds.
