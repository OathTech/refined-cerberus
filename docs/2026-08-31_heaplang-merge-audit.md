# cerberus-heaplang merge audit (branch `spike-minilog`)

[AGENT 2026-08-31] Skeptical pre-merge audit, dispatched on operator
order: poke holes with respect to the goal of a legitimate,
NO-QUALIFIERS "heaplang-on-cerberus" — acceptable qualifiers are
clear, known divergences with retirement paths; anything less
explicit is a finding. The auditor built none of this; everything
below was re-derived in this session (engine sources re-read at the
pin, gates re-run, plants re-planted, cones re-probed).

## VERDICT: FIX-FIRST (docs only), then merge

No proof-content defect was found. The theorem chain is legitimate:
the production-entry statements are about the shipped
`CerbND.runND ∘ Driver.drive ∘ initial_driver_state` composite
(traced into `generated/Driver.lean` / `Main.lean` at pin
07a7fca29, no lookalikes), the collapse lemmas unfold the driver's
real round functions, all 14 probed cones are exact, the boundary
gate fires in both planted directions, both packages build green,
the root package carries no boundary, the tree is clean.

The fix list is documentation, ~an hour, no Lean changes:

1. (F1) One scope paragraph in `cerberus-heaplang/README.md`
   stating the qualifier set of the exported theorems (partial
   correctness; in-budget-termination hypothesis at the production
   entry; the ~10^6-step fuel budget; single-threaded; the
   four-construct fragment; no `wp_create` in the logic) — or an
   explicit pointer to where each is registered.
2. (F2) One register line (ProdEntry header or the spike report)
   for the CerbTags/tagDefs-argument seam (finding 2).
3. (F3 — optional, may be deferred as a registered gap) Close or
   register the def-level-sorry gate gap (finding 3).

With F1+F2 landed, the honest verdict becomes
findings-registered-merge acceptable.

## What was re-derived (evidence base)

- **Pin**: `.cerberus-ws` HEAD = `07a7fca29c30…` =
  `scripts/semantics-pin.env`. Verified.
- **The shipped composite**: `Main.lean:855-885` runs
  `CerbND.runND (drive (CerbTags.tagDefs ()) false runFile
  ("cmdname" :: progArgs)) (initial_driver_state runFile fsState)`.
  `_root_.drive` in `prod_run_eq`'s statement is
  `generated/Driver.lean:500` (signature and body verified: globals
  → main lookup → Proc arm → no-params skip → errno
  allocate-and-zero with the real `allocateObject`/`storeM` →
  park-arena literal matching `prodThread` field-for-field →
  `driver2` → `finalize`). `initial_driver_state` is
  `generated/Driver.lean` (~:429), `initial_core_run_state`
  (`Core_run_aux.lean:395`) draws `sym_supply` through
  `runEffectful (fun () => CerberusFresh.freshIntIO ())` —
  exactly as the boundary provenance states. `runEffectful` is an
  axiom (`LemLib.lean:54`, `@[implemented_by]`), confirmed.
- **prodFile honesty**: `mainDecl e = Proc … [] e` — the Proc arm
  of `drive` parks `e` verbatim; the no-params arm skips argc/argv;
  `(prodFile e).tagDefs = fmapEmpty` proved by `rfl` in-session.
  No wrapper beyond the synthetic file constructor.
- **Collapse lemmas vs the driver's real code** (spot-checked 6):
  `loop_step_tau`/`loop_step_action` vs `advance_step`
  (Driver.lean:335) + `drive_nonmemory_steps_aux2_lemFuel`
  (Driver.lean:346-348); `ars_store_active` vs
  `action_request_sequential2` (Driver.lean:273) and
  `perform_action_request2` (Driver.lean:277, the
  `fresh_action_id'` draw); `driver2_done` vs `driver2_lemFuel`
  (Driver.lean:381-386, both scheduler branches of the opaque
  `CerbGlobal.current_execution_mode` read); `finalize_done` /
  `hack_value` vs `finalize` (Driver.lean:423-424) and
  `hack_lemFuel` (:390-395). All match; `is_irreducible`
  (Core_reduction.lean:293) matches `SpikeVal` exactly, including
  the double-annot force-reduction.
- **Gates**: `scripts/test_unit.sh` → `ALL GATES GREEN`; demo sweep
  verbatim: `CerberusHeapLang axiom sweep: 285 theorems within the
  declared boundary (34 in the production-entry boundary modules,
  trio + runEffectful; all others trio-exact)`; root sweep:
  `RefinedCerberus axiom sweep: 2 theorems, all cones within the
  classical trio` (no boundary). Both match the READMEs.
- **Cone probes** (`lake env lean --stdin`, this session, 14
  theorems): `semantic_triple_sound`, `semantic_frame`,
  `engine_complete`, `spike_engine_adequacy`,
  `exhibitA_terminates`, `exhibitC_engine`, `prod_loop_done`,
  `driver2_done`, `finalize_done`, `wp_store`, `exhibit` — exactly
  `[propext, Classical.choice, Quot.sound]`; `prod_run_eq`,
  `sem_triple_prod`, `exhibitA_prod` — exactly
  `[propext, runEffectful, Classical.choice, Quot.sound]`.
- **Plant tests, re-run by the auditor** (all reverted; post-revert
  tree clean, build green):
  - Direction 1 (runEffectful outside boundary, planted TOP-LEVEL
    to also test the module-of-origin filter): build FAILS with the
    sweep message. Fires.
  - Direction 2 (sorry inside a boundary module): build FAILS
    (`carries axiom sorryAx, outside the declared boundary
    [propext, … runEffectful]`). Fires.
  - Direction 3 (auditor's own: `def … : Nat := sorry` in
    Exhibit.lean): build GREEN, sweep count unchanged → finding 3.
- **Merge hygiene**: `git status` clean; `main..HEAD` = 13 coherent
  commits (plan → recon → slices A/B → exhibit C → extension D →
  pin bump → restructure); doc moves intact (stub at
  `docs/2026-08-30_spike-minilog-plan.md` points into the package);
  DECISIONS.md carries the [USER 2026-08-31] restructure ruling;
  worktree CLAUDE.md layout row present; `.cerberus-ws`/`.lake`
  gitignored.

## Findings

### MAJOR

**1. The README's production-entry claim carries none of the
theorems' qualifiers.** README (cerberus-heaplang/README.md:6-11):

> "**certified against the production cerberus-lean pipeline from
> cold start**: the exported theorems quantify over the shipped
> `initial_driver_state` and conclude equations about the very
> `CerbND.runND (Driver.drive …)` composite that the cerberus-lean
> executable runs."

and the module table (README.md:105): "the production-entry
theorem: the production run IS the singleton Active execution
satisfying the postcondition". What the theorems actually say:
`sem_triple_prod` (ProdEntry.lean:303-331) and `prod_run_eq`
(ProdEntry.lean:265-279) conclude the runND equation only under
`hterm : ∀ aids, drive aids k … = .done v σfin` (proved in-budget
termination), `hpre` (a proved setup-prefix alignment equation),
and `hfuel`/`hfuelc` (`esize … ≤ lemDefaultFuel = 10^6`);
`SemTriple` (Adequacy.lean:348-356) is partial correctness (`.more`
unconstrained) with the same fuel cap; everything is
single-threaded and fragment-only. Every one of these qualifiers IS
honestly registered — but in module headers and
`docs/2026-08-30_spike-report.md` ("What remains", FUEL HONESTY),
not in the README, which also says "A green build IS the
verification run" (README.md:51). Under the no-qualifiers bar, the
claims surface must carry the scope. Mitigating fact, verified: the
demonstration theorem `exhibitA_prod` (ProdExhibit.lean:370-377) is
genuinely hypothesis-free (only `fs`/`args` quantified — every
hypothesis discharged concretely), so the headline demonstration
stands unconditionally; the GENERAL production-entry theorems are
the conditioned ones. **Fix: the F1 scope paragraph.**

### MINOR

**2. Unregistered divergence: the tagDefs argument / CerbTags
effectful-global seam.** The theorems' subject is
`CerbND.runND (_root_.drive fmapEmpty false (prodFile e) args) …`
(ProdEntry.lean:272-273); the executable's invocation is
`drive (CerbTags.tagDefs ()) false runFile …` after
`CerbTags.setTagDefsIO runFile.tagDefs` (Main.lean:855,871).
`(prodFile e).tagDefs = fmapEmpty` holds by `rfl` (probed
in-session), so the identification is semantically forced for the
synthetic file — but it factors through an extra-logical
set-then-read of an effectful global (and CerbMem layout functions
read that global for struct/union types; scalar paths provably do
not, as the `rfl`-proved allocation/store equations demonstrate).
Nothing on the register mentions this seam; the report
(spike-report.md, Extension D) says "the exact composite
Main.lean:857-885 runs", which quietly elides it. **Fix: one
register line naming the seam and why it is inert for tagless
synthetic files.**

**3. Gate gap: a def-level `sorry` passes every gate green.**
Planted `def plant_def_sorry_audit : Nat := sorry` at the end of
Exhibit.lean: `lake build` completes successfully, sweep reports
285 unchanged, the grep gate does not cover `sorry`. Bounded
impact, verified mechanism: `collectAxioms` traverses statement
cones (that is exactly how `runEffectful` enters the boundary
theorems), so a sorry-carrying def REFERENCED by any swept theorem
— in statement or proof — is caught; only defs referenced by no
theorem escape. But the demo's claim surface includes bare
definitions (`drive`, `prodFile`, `prodMem₀` are defs), so a hole
in an unreferenced definitional artifact would ride a green build.
**Fix options: sweep defs too, or add a project-source
`sorry`-warning check to test_unit.sh; acceptable to register as a
known gap instead.**

**4. Naming: "the HeapLang-analog" is scoped only implicitly.**
README:3-5 ("A demonstration separation logic… the HeapLang-analog
of the cerberus-lean semantics. A small Iris program logic… over a
tight fragment") does scope downward, but never states the contrast
a HeapLang-conditioned reader will assume: Iris HeapLang has a full
expression language, concurrency (fork/CmpXchg/FAA), prophecy
variables, allocation/free rules, and a standard lemma/tactic
suite; this package has three memory actions + strong sequencing +
the annotation residue, sequential single-threaded only
(`Observation = Empty`, trivial forkPost — Lang.lean:136-139), no
allocation rule in the logic (registered: ProdEntry.lean:42-53),
partial correctness. **Fix: one contrast sentence in the README
(folds naturally into F1).**

### NOTES (no action required for merge; recorded for the register)

**5. The pinned engine itself contains a data-level `sorry`**:
`generated/Cmm_op.lean:283` — `(sorry : String)` inside a
concurrency-model debug-log message (`auxAddToRfLoad`), in the
parked cmm instantiation (engine TODO.md:10). Proven outside every
demo theorem cone (the sweep and all probes are trio-exact). An
engine-repo concern surfaced here only because the README's trust
story describes the engine without noting parked-code holes;
informational.

**6. Memory orders are accepted arbitrarily and this is
mirror-true**: `Step.store`/`wp_store` hold at ANY `memory_order`
because the sequential driver's discharge drops `mo`
(`action_request_sequential2`, Driver.lean:273: `StoreRequest2 mo1
… => liftMem (CerbMem.storeM …)` — `mo1` unused). Faithful to the
pinned engine, but a reader expecting NA-only side conditions
should find this named; candidate register line.

**7. exhibitC_semantic has no value clause** — deliberately, with
in-code rationale (Exhibit.lean:649-653: "The postcondition carries
NO value clause: `triple_seq`'s assertion-postcondition form …
discards the delivered value"). Adequately registered.

**8. Untracked-memory non-preservation** of `SemTriple` (cells
outside P ⊎ R unconstrained in the conclusion) is registered in the
report ("Untracked-preservation export … unclaimed") but nowhere
nearer the claims; folds into F1.

**9. Divergence register, checked item by item**: runEffectful
boundary (explicit, module-scoped, plant-tested, [USER 2026-08-31]
retirement note — OK); byte-splitting growth step (Heap.lean
header + report R2 — OK); Ewseq/Eif absent (Step.lean header +
report "Honestly open" — OK, mechanical-extension path named);
fuel parametricity pending (report "What remains" + ProdEntry
header — OK); allocator-cursor resource pending (ProdEntry header
+ report D26 — OK); D1 REMOVE-ANNOT value protocol and D3
canonical-annotation subrelation (Step.lean header, slice notes —
OK, and `is_irreducible` re-read confirms the mirror claim). The
only divergences found OFF the register are findings 2 and 6.

## Qualifier inventory (theorem hypothesis → README treatment → verdict)

| Qualifier / hypothesis | Where it lives | README treatment | Verdict |
|---|---|---|---|
| `runEffectful` in production-entry cones (statement-only, temporal) | Audit.lean header; README trust story | Stated, with retirement plan | **OK** |
| `hterm`: in-budget termination, ∀ aids (`sem_triple_prod`, `prod_run_eq`) | ProdEntry.lean:33-40, report "What remains" | Absent | **GAP → F1** |
| `hpre`: setup-prefix alignment (`sem_triple_prod`) | ProdEntry.lean:311-315 | Absent | **GAP → F1** |
| `hfuel`/`hfuelc`, SemTriple's `esize e + n ≤ 10^6` | Soundness.lean FUEL HONESTY; report D19 | Absent | **GAP → F1** |
| Partial correctness (`.more` unconstrained) | Adequacy.lean:36-39; report | Absent | **GAP → F1** |
| Single-threaded, no concurrency | Lang.lean; report scope honesty | Implicit ("small", "tight") | **GAP → F1/F4** |
| Fragment = store/load/create/sseq/annot only; no Ewseq/Eif | Step.lean header; report | "tight fragment" + module table | **PARTIAL** |
| No `wp_create` in the logic (allocator-cursor pending) | ProdEntry.lean:42-53; report D26 | Absent | **PARTIAL (registered off-README)** |
| Sat/Coh commitments (whole-allocation cells, writable, non-atomic, exact bytes, side-table inertness) | Heap.lean header | "allocation-rooted byte-list cells" | **OK for a demo README** |
| `StorableAt` / `cellLoadTrap` premises on the small axioms | Rules.lean headers | Not claimed in README | **OK (interior)** |
| tagDefs arg = `fmapEmpty` vs Main's `CerbTags.tagDefs ()` | nowhere | Absent | **GAP → F2 (finding 2)** |
| `memory_order` arbitrary (engine drops it sequentially) | nowhere | Absent | **NOTE (mirror-true) → register line** |
| exhibitC: no value clause | Exhibit.lean:649-653 | Not claimed | **OK** |
| Untracked-memory non-preservation | report "What remains" | Absent | **PARTIAL → F1** |
| D1/D3 value protocol, canonical-annots subrelation | Step.lean header, slice notes | Not claimed | **OK (registered)** |

## Bottom line

The mechanism is real: nothing in the chain from `wp_store` to
`exhibitA_prod` rests on anything but the pinned engine's own
definitions plus the declared, retirement-planned `runEffectful`
statement seam, and the audit gate demonstrably fails builds that
would weaken that position (in the two directions it was designed
for). The holes found are claims-hygiene holes, concentrated in the
README's silence about the exported theorems' qualifier set, plus
one unregistered (semantically inert) seam and one bounded gate
gap. Fix F1+F2 (docs only), decide F3's disposition, then this is
merge-ready.
