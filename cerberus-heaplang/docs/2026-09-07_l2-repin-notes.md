# L2 — the re-pin landing: cerberus-lean `89f7e6885`, fuel quantified, the fragment kept syntactic

[AGENT 2026-09-07] Landing record of `land/repin-89f7e68` — the L2 slice of
`../../docs/2026-09-07_landing-charter.md` §2, re-cut from the other agent's
re-pin code commit `ce4d7de` (branch `demo-repin`; its thirteen red-frontier
documents, seventeen progress records and `docs/evidence/*` are NOT taken and
stay on `parked/demo-expansion-2026-09-07`). Rulings applied: R1 — the pin IS
`89f7e688530c6910884518811d645e4e892e4507` ([USER 2026-09-07]); R2 — the
fragment stays SYNTACTIC, the fuel premise is a hypothesis on the adequacy
theorems ([USER 2026-09-07], "match refinedC"). Base: main `f1f2573` (L1 with
the E5 full-range audit's fixes, `46c28dc`, plus the docs-only Codex-charter
commit `f1f2573` that landed during the slice; rebased onto each in turn). Every tally marked DERIVED is computed from
the artefacts named; quoted outputs are verbatim.

**Provenance of the pin and the oracle.** `git -C cerberus-lean log -1` at
the sibling `/home/dev/projects/cerberus-lean-proj/cerberus-lean` (read-only)
at the start of the slice:
`89f7e688530c6910884518811d645e4e892e4507 2026-09-05 22:34:29 +0000 docs: orchestrator handoff (2026-09-05 evening) — …`,
branch `mdd/cerberus-lean`. The oracle binary
`_build/default/backend/driver/main.exe` has mtime `2026-09-05 19:47:06 +0000`
— built before the docs-only handoff commit; caveat: the binary predates the
pin commit by about three hours and the commits between are docs/instruments,
not semantics. During the slice the sibling's HEAD moved on (at the record's
writing `a3b5d169d … 2026-09-07 03:04:17 +0000 record: orchestrator boundary
battery …`); the pin and the workspace `.cerberus-ws` are unaffected (the
workspace is primed from the pin commit, `scripts/setup-cerberus-dep.sh
--check`: 37 seams). The sibling was neither built nor modified.

## 1. The three change classes at the pin, and what landed

| Class | Engine change (cerberus-lean) | Consumer effect | Where |
|---|---|---|---|
| **Fuel** | the fuel-parameter arc C1–C4 (`lean_frontend/docs/2026-09-05_fuel-parameter-C{3,4}-change-manifest.md`): every fuelled function reads the ambient `[LemFuel]`; `lemDefaultFuel`, `CerbFuel.driverFuel`, `CerbND.drive_lemFuel` gone; `get_ctx`/`subst_sym_*`/`update_env_aux`/the CerbMem layout MEASURED; the eight (D) rows of `scripts/fuel_forms_pending.txt` | every export `[LemFuel]`; hypotheses `2 ≤ LemFuel.fuel`, `evalDepth … ≤ LemFuel.fuel` (R2), `N ≤ LemFuel.fuel`; the `pot` premises gone; the thirteen `*_shipped` corollaries | §3, §4, §5; `FUEL.md` |
| **`killM` re-mirroring (Z1)** | `lean_frontend/docs/2026-09-03_zero-discrepancy-Z1-change-manifest.md` §2: the kill rows of `killM` re-mirrored (function pointer, missing provenance, `Prov_symbolic`, `UB009_outside_lifetime`); the dead-static-kill arm is a `panic!` (`CerbMem.lean:2216`) | `killM_killed_inv` seven rows (was three); `killM_success`/`_dynamic`, `allocateRegion_killed_inv`, the two `drive_after_setup_*_killed` restated | §6 |
| **Allocator / memory contract (Z2)** | `lean_frontend/docs/2026-09-04_zero-discrepancy-Z2-change-manifest.md`: signed sizes (`allocateRegion` at `Int`), the requested-address `allocateObject` arm a fail-stop, `PrefMalloc` recorded regardless of the caller's prefix, retained bytes (no `writeBytesTo` of undef on `alloc`), `lastUsed := some id`, `UnallocatedBytes`, `intToBytes signed` | new rule premises `0 < alignN`, `0 ≤ sizeN`, `get_with_address a = none`; `allocateRegion_success`/`allocateObject_success` new shapes; `LaunchCoh.unallocated`; value-range premises on the storable lemmas | §6; KOI B21 |

Commits of the landing (on `f1f2573`): `3c59325` the cherry-pick of `ce4d7de`
(70 files; conflict resolutions §2); `1813fa1` R2 (§3); `02580bd` the shipped
corollaries and gate 1b (§4); `2deabc5` the rebase onto `46c28dc`, header
reflow, the two not-taken files removed; `cc4fe8f` the documentation (§9; the
FULL gate's commit, §11); then this record (docs-only). The hashes before the
second rebase (onto `f1f2573`, docs-only, no conflicts) were `a6e3378`,
`5db6f49`, `743b13c`, `e7b81be`, `dfcb2bf`. `scripts/semantics-pin.env` reads
`CERBERUS_LEAN_COMMIT="89f7e688530c6910884518811d645e4e892e4507"`;
`cerberus-heaplang/lake-manifest.json` pins LemLib at
`f6542f8e6860d12d4655e6648bc4c45dabd1d798`.

## 2. Conflict resolutions

The cherry-pick of `ce4d7de` onto `093b02b` (eight conflicts):

| File | Resolution |
|---|---|
| `CorpusT4Exhibit.lean`, `CorpusT5Exhibit.lean`, `CorpusT6Exhibit.lean` | the re-pin's content (`[LemFuel] (hfuel : 917/90/80 ≤ LemFuel.fuel)` headers, the fuel sentences); L1's hygiene re-applied (no client imports, no aliases, the supply-floor docstring sentence) |
| `Examples/EmittedInt.lean` | the re-pin's content; `[LemFuel]` added to `specInt_eval`, `t1ConvLoadedInt_eval`, `t1sym_eval`, `t5CmpBranch_eval`, `t5Tuple_eval` (the evaluator is `[LemFuel]` at the pin) |
| `docs/CLAIMS.md` | BOTH rows: L1's C13–C17 text with the re-pin's fuel sentences ("ambient fuel at least fifty/ninety/eighty/917 (`N ≤ LemFuel.fuel`)"); `t6Q_pot`/`t4Q_pot` dropped from the theorem cells (deleted at the pin) |
| `docs/DECISIONS.md` | HEAD's file exactly (orchestrator-owned) |
| `docs/KNOWN-OPEN-ITEMS.md` | HEAD's file, then item 7 (§9) |
| `docs/2026-09-07_demo-completion-charter.md` | stays DELETED |

The rebase onto `46c28dc` (main after L1's audit fixes), replaying the three
L2 commits — seven conflicts:

| Commit / file | Resolution |
|---|---|
| the cherry-pick (`3c59325`) / `CorpusT4/T5/T6Exhibit.lean` | main's D-2 "not vacuous" docstring sentence kept; the re-pin's `[LemFuel]`/`hfuel` header and fuel sentence layered on top |
| the cherry-pick / `Potential.lean` header | main's D-1 leaf weights (the negative leaf is 10, `pot_negRewrite_le`) kept; the false premise "`get_ctx` is fuel-bounded" replaced by the truth at the pin (`get_ctx` MEASURED; `evalDepth` the one fuel hypothesis) |
| the cherry-pick / `docs/CAPABILITY_MANIFEST.md` | main's counts (78 rows / 7 OUT-OF-SCOPE, the `Frag.neg_store` row); regenerated in the documentation commit |
| R2 (`1813fa1`) / `Potential.lean` | both hunks main's text (the module header as resolved above; the negative-leaf docstring: 10, `pot_negRewrite_le`) |

## 3. R2 — the fragment is syntactic again

The re-pin's `Frag [LemFuel]` (Soundness.lean, `ce4d7de`) carried
`peDepth pe ≤ LemFuel.fuel` FIELDS on every operand-evaluating constructor,
so `Frag e` depended on the ambient instance. Design decision ([AGENT], Option
F of the analysis): keep that inductive as the PROOF DEVICE `FragFuel`
(`Soundness.lean:9297`; the mirror-certification, round-classification and
driver-collapse proofs are written over it), define the public SYNTACTIC
`Frag` (`Fragment.lean:491`, 35 constructors, no fuel field) and the measure
`evalDepth` (`Fragment.lean:86`), bridge both ways (`Frag.toFuel`
`Fragment.lean:753`, `FragFuel.toFrag`, `fragFuel_iff` `:950`), and restate
every export as a WRAPPER over `Frag e` + `hdep : evalDepth e ≤ LemFuel.fuel`
(and `hQd`/`hPd : M.ProcsDepth LemFuel.fuel` for label and procedure bodies,
`Adequacy.lean:728`) whose proof is the device form (`X_fuel`, unpinned).
Why not re-prove: `Redex`/`Decomp` are already syntactic; the depth fields
are consumed only in `Frag.step`/`Frag.decomp`/the round completeness; the
bridge costs nothing at the kernel and no ten-thousand-line proof moves.

**Deviation from the design note's letter** ([AGENT]; a premise falsified by
measurement): the brief and `docs/2026-09-04_fuel-restatement-design.md` §3
name the hypothesis `pot e ≤ LemFuel.fuel`. The additive potential `pot` never
bounded operand depth — it bounded `esize` for the former `get_ctx` ceiling,
which the pin's MEASURED `get_ctx` retired (cerberus-lean C3 manifest §1); the
operand bound was always the per-operand `peDepth` field the fragment carried
at the fixed `lemDefaultFuel`. The honest hypothesis is `evalDepth e ≤
LemFuel.fuel` (the max `peDepth` over the operands the run can evaluate,
values cost one). Stability under the engine's substitution is proved
(`peDepth_subst`, `evalDepth_subst`, `evalDepth_subst_fold`, at the pin's
MEASURED `subst_sym_*`), which is what lets `Frag`'s `case` nodes carry no
fuel field.

**Every changed statement** (the twenty-three exports restated; before =
the re-pin form at `a6e3378`, over the fuel-relative `Frag`; after = the
export at the landing head, over the syntactic `Frag`; the re-pin form is
readable at `3c59325`):

| Export (file) | Before (re-pin `ce4d7de`) | After (R2) |
|---|---|---|
| `engine_adequacy`, `engine_adequacy_alloc` (Adequacy) | `(hfuel : 2 ≤ LemFuel.fuel) … (hQf : … → Frag cont) (hPf : M.FragProcs) … (hfrag : Frag e₀)` with `Frag` fuel-relative | `(hfuel : 2 ≤ LemFuel.fuel) … (hQf : … → Frag cont) (hQd : … → evalDepth cont ≤ LemFuel.fuel) (hPf : M.FragProcs) (hPd : M.ProcsDepth LemFuel.fuel) … (hfrag : Frag e₀) (hdep : evalDepth e₀ ≤ LemFuel.fuel)` |
| `project_triple`, `project_triple_pure`, `project_triple_alloc`, `project_triple_pure_alloc`, `semantic_triple_sound`, `semantic_frame` (Adequacy) | same pattern (`hQf`, `hPf`, `hfrag : Frag e`) | same pattern plus `hQd`, `hPd`, `hdep : evalDepth e ≤ LemFuel.fuel` |
| `engine_step_matchU`, `step_iff_cerberusRound` (Round) | `(hfuel : 2 ≤ LemFuel.fuel) … (hf : Frag e)` | `… (hf : Frag e) (hdep : evalDepth e ≤ LemFuel.fuel)` |
| `frag_round_complete`, `cerberusRound_classify` (Round) | `(hfuel : 4 ≤ LemFuel.fuel) … (hf : Frag e)` | `… (hf : Frag e) (hdep : evalDepth e ≤ LemFuel.fuel)` |
| `loop_step_frag`, `loop_step_frag'`, `loop_step_frag_same`, `loop_step_frag_same'` (DriverCollapse) | `(hfuel : 2 ≤ LemFuel.fuel) … (hf : Frag e)`; `loop_step_frag'`'s jump tie `hjmp` delivered `Frag`-membership of the label bodies | `… (hf : Frag e) (hdep : evalDepth e ≤ LemFuel.fuel)`; `hjmp` delivers `Frag cont` and `evalDepth cont ≤ LemFuel.fuel` |
| `wpt_driver_done`, `wpt_driver_done_alloc` (ProdLoop) | `(hfuel : 2 ≤ LemFuel.fuel) (hQf : … → Frag cont) … (hfrag : Frag e₀)` | plus `hQd`, `hdep` |
| `driverDoneCtl_step` (ProdLoop) | `(hfuel : 2 ≤ LemFuel.fuel) … (hf : Frag e)` | plus `hdep` |
| `wpt_driver_done_procs`, `wpt_driver_cps` (ProdLoop) | `(hfuel : 2 ≤ LemFuel.fuel) (hPf : M₀.FragProcs) … (hfrag : Frag e₀)` / `… → Frag e → …` | plus `hPd : M₀.ProcsDepth LemFuel.fuel`, `hdep` / `… → Frag e → evalDepth e ≤ LemFuel.fuel → …` |

`MachineCtx.FragProcs` is now syntactic (`Adequacy.lean:719`; the re-pin's
fuel-relative form is `FragProcsFuel`, `:709`, a device); the depth twin is
`MachineCtx.ProcsDepth n` (`:728`) with witnesses `spikeCtx_procsDepth`,
`procCtx_procsDepth`, `eoCtx_procsDepth`, `frCtx_procsDepth`. `Frag`'s
syntactic twins of the device lemmas (`Frag.ccallFree`, `Frag.decomp`,
`Frag.replug`, `Frag.of_negRedex`, `Frag.excluded_of_neg`,
`Frag.negRewrite_frag`, `Frag.of_pePure`, `Frag.substFold_pure`,
`frag_ofValA`/`frag_ofVal`, `Frag.pure_sym`, the inversions) are proved by
instantiating the device at `letI : LemFuel := ⟨evalDepth e⟩`. Clients
discharge `hdep` by `Nat.le_of_ble_eq_true rfl` on the transcribed program's
depth (t1/t4/t5/t6 at most 40, the emitted A/B/C programs 9–26, the authored
programs 1–2) then `omega` against `hfuel`; the depth helpers of the re-pin
(`CorpusE0.depLe`, `depLe40`, `depLeB`, `depLeC`) and the `*_pot` witnesses
are deleted. Verified at R2's commit: FAST-GATE GREEN, 886 trio-exact pins.

**Erratum [AGENT 2026-09-07, the L2 range audit's R-2].** "The twenty-three
exports restated" above is a miscount: the table lists TWENTY-ONE names,
all twenty-one carry the depth hypothesis (`evalDepth … ≤ LemFuel.fuel` /
`ProcsDepth LemFuel.fuel`) in `2026-09-07_l2-signatures-post.txt`, TWENTY
are pinned in `Audit.lean`, and `wpt_driver_done_alloc` is restated but
UNPINNED (it never was pinned) — measured over the snapshot and the
`trioExports` list at the fixes. The census row "the `*_fuel` device forms
(23 …)" in §7 is likewise 22 by name in `2026-09-07_l2-signature-census.txt`
(`spikeCtx_fragProcs_fuel`, `procCtx_fragProcs_fuel`,
`spikeCtx_labels_frag_fuel` among them, which wrap no export). The original
text stands as written; this paragraph governs.

## 4. The shipped-constant corollaries and gate 1b

`CerberusHeapLang/Shipped.lean` (class `production-wrapper`): for each of
the thirteen closed statements a theorem `X_shipped` whose STATEMENT fixes
`letI : LemFuel := ⟨100000000⟩` (the binary's `--fuel` default) and whose
side condition is discharged by `show _ ≤ 100000000; omega` — never `decide`
on the numeral. The six parametric programs get closed-form parameter bounds
(`n.toNat ≤ 49999997` fib, `≤ 16666665` counter, `≤ 14285713` region,
`≤ 3999999` malloc, `≤ 33` recursive fib via `fibRounds_33`/`fibRounds_mono`,
`≤ 33333331` even/odd); `fibSpec_34`/`fibRounds_33` are closed by `decide` on
the LINEAR `fibPair`, never on the doubly recursive `fibSpec`/`fibRounds` or
on the fuel numeral. All thirteen pinned trio-exact (§7). The numeral appears
in no other `.lean` file: gate 1b `scripts/fuel_numeral_check.sh` (wired into
`scripts/test_unit.sh`) reds `100000000`/`1000000`/`999999` outside a
`theorem *_shipped` and the retired `lemDefaultFuel`/`CerbFuel.driverFuel`/
`ndDefaultFuel` anywhere, comments stripped; `--selftest` plants five cases
(verbatim: `fuel_numeral_check: SELFTEST OK (5 plants: 3 red as required, 2
positive controls green)`). Tree run (verbatim): `ok: no fuel numeral
(100000000/1000000/999999) outside a *_shipped corollary and no retired fuel
constant (60 files scanned, comments stripped)`.

## 5. Exhaustion on the fragment's execution path

The classification table is `FUEL.md` §4 (this directory), summarised in
ARCHITECTURE §4 "Exhaustion on the proved path". Result: every fuelled
function reachable from `drive` on the fragment's path is (A) MEASURED
(`get_ctx`, `subst_sym_*`, `update_env_aux`, `step_eval_pexpr`,
`memValueFromValue`, the layout rows) or (B) ABSORBING (the driver family
`driver2`/`drive_nonmemory_steps_aux2`/`nd_bind`/`runND`, exhaustion =
`CerbND.fuelExhaustedKill`; the evaluator's pass loop `eval_pexpr_aux2`/
`full_eval_pexpr`, exhaustion = the absorbing `Result (Error
fuelExhaustedLoc fuelExhaustedMsg)`, excluded on the path by the depth
hypothesis). Of the auditor's eight registered (D) rows, two ARE on the path
— `hack` and `to_pure`, called once by `finalize` (generated `Driver.lean:469`)
on the value arena at PROGRAM-DONE, fuel-0 values the opaque sentinels
`fuelExhausted Vunit`/`fuelExhausted none` — and are excluded by
`0 < LemFuel.fuel` (`hack_value` `DriverCollapse.lean:660`, `finalize_done`
`:677`, implied by `hfuel`); the other six (`to_pures`, `many`, `many1`, the
`are_compatible_aux` trio) are (C) for the fragment (the rewriter and
`core_thread_step2`, which the driver does not call; the `printf` format
parser; struct/union stores — the fragment's memory values are integers and
pointers, `grep OVstruct` over Step/Rules/Heap/StructExhibit: none). Hence
no (D) row's exhaustion arm is evaluated on the proved path, the closed
PARTIAL forms (`prod_run_safe_procs`, `fib_rec_certified`,
`even_odd_certified`) are theorems at every ambient budget with no fuel
hypothesis, and KOI A2 closes (the ambient instance is the budget of BOTH
loops: `new_drive_core_threads`, `Driver.lean:399`). KOI A1 closes for this
package's exports; its residual is cerberus-lean's eight-row register.

## 6. The unplanned third class — the memory contract

Public statements whose TEXT changed for a memory-contract reason (DERIVED
from the census, §7; causes `Z1-kill`, `Z2-alloc`, `Z2-mem-repr`):

- **Z1 (`killM` re-mirroring; six statements)**: `killM_killed_inv` — before
  three refusal rows (`UB179a_non_matching_allocation_free`,
  `UB179b_dead_allocation_free`, `MerrUndefinedFree Free_out_of_bound`),
  after seven (plus `Undef0 loc [UB009_outside_lifetime]`, `MerrOther
  "attempted to kill with a function pointer"`, `MerrOther "attempted to kill
  with a pointer lacking a provenance"`, `MerrOther "killM: Prov_symbolic in
  concrete model"`); `killM_success`, `killM_success_dynamic`,
  `allocateRegion_killed_inv`, `drive_after_setup_lib_killed`,
  `drive_after_setup_with_killed`.
- **Z2 allocator (47 statements)** — new premises `0 < alignN` (and `0 ≤
  sizeN` for `alloc`), `get_with_address a = none` (`create`), and
  `0 < LemFuel.fuel` where the engine evaluates: `wps_create`, `wpt_create`,
  `wps_create_of_plan`, `wpt_create_of_plan`, `wps_alloc`, `wpt_alloc`,
  `create_atomic`, `alloc_atomic`, `allocateObject_success`,
  `allocateObject_arg_irrel`, `allocateRegion_success` (also its SHAPE: the
  result memory is the record with `size := sizeN`, `prefix_ := PrefMalloc`,
  `lastUsed := some σ.nextAllocId`, no `writeBytesTo` of undef bytes — the
  allocator retains the bytes), `MemWF.allocateObject`, `MemWF.allocateRegion`,
  `MemWF.kill`, `CohG.alloc`/`create`/`kill`/`mk`, `MetaCoh.kill_other`,
  `Step.create`/`create_canonical`/`create_inv`, `LaunchCoh.mk`/`empty` (the
  new field `unallocated : UnallocatedBytes σ`), the `loadM_*`/`storeM_*` seams,
  the region-loop and malloc-list families (`rl_*`, `ml_*`,
  `alloc_*_wps`/`wpt`, `struct_create_store_wps`,
  `ReadinessSmoke.twoField_create`), and the two production statements
  `region_loop_certified_production` (`hal : 0 < al`, `hsz : 0 ≤ sz` added)
  and `malloc_list_certified_production` (`hal : 0 < al`).
- **Z2 memory representation (24 statements)** — `intToBytes` takes a
  `signed` flag and the storable lemmas carry the value range:
  `emittedInt_storable` (`-2147483648 ≤ n`, `n ≤ 2147483647` — now covers
  every `int`, the re-pin's extension), `longMval_storable`,
  `longMval_img_length`, `mlBuilt_*`, `lrBuilt1_*`, `ptrImg_cell*`,
  `intToBytes_length`/`_nonneg`, `bytesToInt_of_all_some`,
  `splitBytesProv_ptrImg_cell_fst`, `trPtrImg_cell_length`, the `ml_*` rules.

Engine cites: Z2 manifest rows for `allocateRegion`/`allocateObject`
(`lean_frontend/docs/2026-09-04_zero-discrepancy-Z2-change-manifest.md`), Z1
manifest §2 for `killM`. Registered: KOI A6 (the class), KOI B21 (the rule
premises as disclosed limitations: a requested-address `create` and a
negative-size `alloc` have no rule). The full per-name lists:
`2026-09-07_l2-signature-census.txt`.

## 7. Census

Pre = `2026-09-07_l1-signatures-post.txt` (L1 head `093b02b`); post =
`2026-09-07_l2-signatures-post.txt` (this head; `scripts/signature_snapshot.lean`,
52222 lines; re-run at the final tree and byte-identical to the run after
the shipped-corollaries commit — the documentation and API-header commit
changes no statement).
Classifier: `scripts/signature_census.py` (heuristic, DERIVED); output
`2026-09-07_l2-signature-census.txt`.

| | count |
|---|---|
| constants pre / post | 4950 / 5212 |
| ADDED | 283 — the `Fragment.lean` declarations (`Frag`, `evalDepth`, the bridges and twins), `Shipped.lean` (19), the `*_fuel` device forms (23 + their `FragFuel` helpers), `MachineCtx.ProcsDepth` and its witnesses, `MachineCtx.FragProcsFuel`, the E5/re-pin evaluator lemmas, generated `.eq_def`s of the pin's new workers |
| REMOVED | 21 — `CorpusE0.depLe/depLe40`, `depLeB/depLeC`, `Decomp.frag_plug_call'`, `Frag.esize_le_pot`/`pot_step_bound`/`step` (→ `FragFuel.*`), `MachineCtx.FragProcs.potBound`, `drive_after_setup_{lib,with}_lemFuel` (the pin has no `_lemFuel` drive), `instLanguageCoreRtMemEmptyCoreRVal` (renamed instance), `t1Main_pot`/`t4Main_pot`/`t4Q_pot`/`t5Main_pot`/`t6Main_pot`/`t6Q_pot`, `treeMap_get?_insert_empty` (A4: the upstream law replaces it), `subst_sym_pexpr_lemFuel.eq_def`/`update_env_aux_lemFuel.eq_def` (MEASURED at the pin) |
| CHANGED | 1483 |
| — binder-only | 1340 (`[LemFuel]` inserted; `hfuel`/`hdep`/`hQd`/`hPd` inserted; `pot`/`peDepth ≤ lemDefaultFuel` premises dropped; `[inst]`→`[inst_1]` renames; section-variable reordering) |
| — premise-text | 82: Z2-alloc 32, Z2-mem-repr 21, printing (`⋯` elision / `expr` abbreviation) 23, R2-fragment 4 (depth witnesses), unexplained 2 (`stExpect_mapM_cons` — a type-variable rename `s`→`st`; `tree_rotate_certified` — `sbty` binder moved into the section) |
| — shape | 61: R2-fragment 18 (the `Frag` constructors' fields, the `_depth`/`_pot` helper conclusions, `wps_bound_aux`'s dropped `pot` conjunct), Z2-alloc 15, Z1-kill 6, engine-wrapper 7 (`drive_lemFuel`→`drive` in the closed partial forms, `.eq_def`s of the pin's wrappers), LemLib-map 6 (the canonical `symAdd` order of computed registration maps: `collect_new_eo`, `t4Q_eq`/`_lookup`, `t6Q_eq`/`_lookup`, `fmapLookupBy_addBy_empty` — A4), Z2-mem-repr 3, fuel-token-only 3, printing 2, unexplained 1 (`struct_wp_readout` — its WP post's printed form) |

Auditor's reference for the other agent's re-pin (860 added / 35 removed /
1599 changed; 565 binder-only, 1034 real) is not comparable: R2 restates the
exports and the classifier flattens the binder telescopes (a leading
`[LemFuel] → 2 ≤ LemFuel.fuel →` insertion is binder-only here).

**Pins.** `Audit.lean`: 893 → 901 trio-exact (the thirteen `*_shipped`,
`peDepth_subst`, `evalDepth_subst`; the L1 count 893 kept — every re-pinned
export stays trio-exact, `Audit.lean` header "L2 RE-PIN"); the six
axiom-free-exact pins unchanged (the class is kept because exactness is
preserved: the six statements have EMPTY axiom sets at the pin as before —
the Audit header paragraph explains). The `*_fuel` device forms are unpinned
(proof devices, the 2026-09-03 standards-audit rule).

**Erratum [AGENT 2026-09-07, the L2 range audit's R-1].** The pin
derivation above is wrong (893 + 15 ≠ 901) and "the six axiom-free-exact
pins unchanged" is wrong (the class did not exist at L1: the L1 gate line
is `export pins: 893 trio-exact`). Re-derived at the fixes from
`Audit.lean` at `46c28dc` against this head, by name (893 distinct at
`46c28dc`, 901 + 6 distinct here): 893 − 4 REMOVED
(`drive_after_setup_lib_lemFuel`, `drive_after_setup_with_lemFuel`,
`t4Q_pot`, `t6Q_pot`) − 6 MOVED from `trioExports` to the NEW list
`axiomFreeExports` (`procCtxF_runState_labeled`, `procCtxF_sym_supply`,
`procCtx_runState_labeled`, `procCtx_sym_supply`, `prodThread_eq_ctlThread`,
`prodCtx_extern`; the class arrives with the cherry-pick of `ce4d7de`) + 18
ADDED (the thirteen `*_shipped`, `peDepth_subst`, `evalDepth_subst`,
`drive_after_setup_lib_one`, `drive_after_setup_with_one`, `errno_init_eq`)
= 901 trio-exact, plus the 6 axiom-free-exact. Trust impact none (the
auditor's independent sweep: 901/901, 6/6). The original text stands as
written; this paragraph governs; ARCHITECTURE §3 carries the same
derivation.

**The thirteen closed statements and three closed partial forms, before
(L1, pin `f95ef8d9c`) → after (this head).** Every one gains `[LemFuel]`;
the total ones exchange `≤ CerbFuel.driverFuel` for `≤ LemFuel.fuel` or gain
the constant bound: `exhibitA_prod` (+`hfuel : 12 ≤ LemFuel.fuel`),
`fib_certified_production` (`2 * n.toNat + 6 ≤ …`),
`counter_loop_certified_production` (`6 * n.toNat + 8 ≤ …`),
`list_reverse_certified_production` (+`56 ≤ …`),
`dispose_list_certified_production` (+`53 ≤ …`),
`region_loop_certified_production` (`7 * n.toNat + 5 ≤ …`; +`0 < al`, `0 ≤
sz`), `malloc_list_certified_production` (`25 * n.toNat + 9 ≤ …`; +`0 < al`),
`fib_rec_certified_production` (`fibRounds n.toNat + 4 ≤ …`),
`even_odd_certified_production` (`3 * n.toNat + 6 ≤ …`),
`t1_certified_production` (+`50 ≤ …`), `t4_certified_production` (+`917 ≤
…`), `t5_certified_production` (+`90 ≤ …`), `t6_certified_production` (+`80 ≤
…`); the partial `prod_run_safe_procs`, `fib_rec_certified`,
`even_odd_certified` lose the `(fuel : Nat)` binder and `CerbND.drive_lemFuel
fuel` for the shipped `drive` at the ambient `[LemFuel]`
(`prod_run_safe_procs`'s `DriverSafeCtl` premise now under `2 ≤ LemFuel.fuel
→`). Full texts: the two snapshots.

## 8. Oracle cross-checks (verbatim; the caveat of the header applies)

`cd /home/dev/projects/cerberus-lean-proj && scripts/ce cerberus-lean/_build/default/backend/driver/main.exe --nolibc --exec --batch refined-cerberus/docs/corpus-e0/<f>.c`:

```
== t1
Defined {value: "Specified(4)", stdout: "", stderr: "", blocked: "false"}
== t4_while
Defined {value: "Specified(10)", stdout: "", stderr: "", blocked: "false"}
== t5_ifelse
Defined {value: "Specified(1)", stdout: "", stderr: "", blocked: "false"}
== t6_switch
Defined {value: "Specified(20)", stdout: "", stderr: "", blocked: "false"}
== t2
Defined {value: "Specified(3)", stdout: "", stderr: "", blocked: "false"}
== t3_ptrarg
Defined {value: "Specified(4)", stdout: "", stderr: "", blocked: "false"}
== t10_evenodd
Defined {value: "Specified(1)", stdout: "", stderr: "", blocked: "false"}
```

The certified values agree: `t1_certified_production` delivers `lint 4`,
t4 `10`, t5 `1`, t6 `20`. (The `exit=` capture in the run loop printed empty
because the shell was zsh — `PIPESTATUS` is `pipestatus` there; the outputs
above are the oracle's stdout verbatim, "Time spent" lines omitted.)

## 9. Documentation changed (shop-window: the system as it IS)

- `docs/FUEL.md` (NEW, replaces the other agent's file, not taken): the
  parameter, the budgets, the hypotheses, the exhaustion classification
  table (§5 above), what is not claimed.
- `ARCHITECTURE.md`: the M2 banner removed; glossary (`Frag` syntactic,
  `evalDepth`, the ambient fuel, `Step [LemFuel]`); §1 fragment cites →
  Fragment.lean; §2.2 `engine_step_matchU` re-printed verbatim; §2.4 the
  loop at the ambient budget, the premises `FragProcs`/`ProcsDepth`, the
  closed forms over `drive` at `[LemFuel]`; §2.5 the `hfuel` bounds of all
  thirteen + the `*_shipped` corollaries (table re-cited); §3 the pin,
  901 pins, the `panic!` count re-measured (127 non-comment lines in the
  twelve hand-written seams, 61 in `CerbMem.lean`; DERIVED, method stated),
  LemLib cites; §4 `fib_certified_production` and `counter_loop_certified`
  re-printed verbatim, the premises list (`hfuel`, `hdep`/`hQd`/`hPd`
  replacing the `hpot` bullet, with the measured-vs-design note), the
  exhaustion paragraph, the ruled reading's consequences (A2 closed); §6
  fuel bullet, A5 bullet (the arm IS a `panic!` at the pin, `CerbMem.lean:2216`),
  `hbsz` cites; §7 goal 1. `scripts/cite_check.sh`: 301 cites, EXACT 106 at
  the start of the pass → 233 after `--fix` (71) and the hand-check of the
  whole queue (verbatim final line: `cite-check: ARCHITECTURE.md — 301 cites;
  EXACT 233; DECL 16 (fixed 0; ranges among them counted in RANGE); USE 14;
  HAND 22; PIN 16; NOFILE 0; RANGE 16 (never rewritten)`; the residue is
  ranges whose end line the tool attributes to the range's start
  declaration, hypothesis-name and use-site cites, and file-header cites —
  each checked by hand; the commit message of `cc4fe8f` says 230, written
  before the last four fixes).
- `README.md` (by a fork of this worker, its edit list in §10): banner
  removed; every fuel passage; the exhibit table's hypotheses re-read from
  the snapshot; the divergences table (Fuel, `FragProcs`, `hbsz` rows); the
  trust diagram; module rows for `Fragment.lean`/`Shipped.lean`; the
  admissions and `panic!` bullets re-measured (the fork's count: 119
  non-comment `panic!` over the 37 manifest seams, comments stripped at the
  block level — a different method from ARCHITECTURE's 127 over the twelve
  `lean_frontend/*.lean` files; both DERIVED, both stated with their method).
- `docs/WALKTHROUGH.md` (by a fork): banner removed; `project_triple_pure`,
  `engine_step_matchU`, `frag_round_complete`, `Frag.if_`, `Frag.store_op`
  re-printed verbatim; §1.3 rewritten; "Why the fuel hypotheses exist"
  replaces the two fuel-premise sections; the `hbsz` story corrected; §7
  "A fuel-free semantics"; the two-arm → three-arm residual (main's D-1 truth
  the walkthrough had missed).
- `CerberusHeapLang/API.lean` header: the partial-lane sentence, the `Frag`
  row (Fragment), "The evaluator-depth hypothesis" row replacing "The static
  fuel bound", the Soundness row (`FragFuel` the device); explicit
  `import CerberusHeapLang.Fragment`.
- `docs/CLAIMS.md` C3: the shipped-constant instances named.
- `scripts/capability_manifest.lean` two shape strings (`Frag.save`,
  `Frag.bound`); `docs/CAPABILITY_MANIFEST.md` regenerated (78 rows / 7
  OUT-OF-SCOPE; module rows `Fragment`, `Shipped`; 59 modules classified).
- `scripts/module_classes.tsv`: rows `Fragment` (core), `Shipped`
  (production-wrapper); Soundness reworded.
- `docs/KNOWN-OPEN-ITEMS.md` (only the permitted rows): state line; A1
  (CLOSED for the exports, residual upstream), A2 (CLOSED), A4 (CLOSED at
  the re-pin, the LemLib-map statement effect), A6 (LANDED); new B21 (the
  allocator premises); §E pin sentence, the scout worktree superseded, the
  expected FULL tail (§11).
- `scripts/semantics-pin.env`: the L2 paragraph replaces the other agent's
  (109 commits; code-bearing delta `69 files changed, 8184 insertions(+),
  1619 deletions(-)`, measured read-only on the sibling; 37 seams).
- `Potential.lean` header (the rebase resolution, §2).

## 10. Deviations and decision points ([AGENT] unless marked)

1. **`evalDepth`, not `pot`** (§3): the brief's `pot e ≤ LemFuel.fuel` named
   a measure that never bounded the evaluator; recorded as a design-note
   premise falsified by measurement. Decision point for the operator only if
   the letter of the design is preferred over the measured truth.
2. **The device kept** (Option F): the re-pin's fuel-relative inductive lives
   on as `FragFuel` (unpinned, proof device) instead of being re-proved
   syntactically. Everything exported is over `Frag`; `FragFuel` appears in
   no export statement.
3. **Rebase mid-slice**: onto `46c28dc` before the documentation pass (the
   brief says before the FINAL gate; doing it first let the prose land on
   main's D-1/D-2 truths instead of conflicting with them later). Main moved
   once more before the final gate (`f1f2573`, docs-only); the five commits
   were rebased again without conflict and the FULL gate ran on the rebased
   head `cc4fe8f`.
4. **Header reflow** (cosmetic, `e7b81be`): 43 generated wrapper headers
   reflowed at binder boundaries; ~40 continuation and proof-term lines of
   those wrappers remain over 140 characters — left, because a second pass
   would shift the line numbers every document cites.
5. **Forks**: README.md and WALKTHROUGH.md were edited by two forks of this
   worker (full context, no build, one file each); their edit lists are §9;
   what they flagged and I did not change: README's "Scope" manifest counts
   are stale from L1 (28 constructors/58 rows … vs the manifest's 35/78) —
   outside this slice's items, for the orchestrator; `csCtx_procsDepth`
   does not exist (only `spikeCtx_`, `procCtx_`, `frCtx_`, `eoCtx_`).
6. **KOI rows not mine but now imprecise** (flagged, not edited): A5 says
   "at the PIN `f95ef8d9c` … the next pin brings it" — the pin has landed and
   the arm IS the `panic!`; B7 says `esize_subst` is "proved at the engine's
   fuel" — at the pin `subst_sym_expr` is MEASURED (fuel-free).
7. **Shipped side conditions**: `omega` cannot see `(⟨100000000⟩ :
   LemFuel).fuel` as the literal; `show _ ≤ 100000000; omega` first (the
   projection reduces by `whnf`). Not `decide`.
8. **The zsh `PIPESTATUS`** slip in the oracle run loop (§8): outputs
   verbatim, exit codes not captured; the values are the ones certified.
9. **Not taken**: `docs/2026-09-06_repin-t4-malloclist-and-full-gate.md` and
   `docs/evidence/2026-09-06_repin-t4-malloclist-axioms.lean` came with the
   cherry-pick and were removed at `e7b81be` (they stay on the parked branch).
10. **Scratch** `.l2-scratch/` (worktree root, ephemeral) is deleted at the
    end of the slice; nothing in it is needed — the snapshots, census output
    and classifier are committed.

## 11. Build cost and the gates

Under `CERB_MEM_MAX=40G scripts/capped` throughout (no uncapped `lean`).
Full rebuilds of the package after the cherry-pick / R2 / the shipped
corollaries / the rebase / the API-header edit: 481–483 jobs each; the
longest single pass stayed well under the one-hour tripwire (the R2 pass was
the largest: Soundness → Round → DriverCollapse → Adequacy → all clients).
Snapshot runs: 32–34 s each. Gate 1b self-test: sub-second. The manifest
regeneration: ~12 s.

FAST-GATE verdicts (verbatim `info:` line each time):
`CerberusHeapLang/Audit.lean:1116:0: CerberusHeapLang export pins: 901 trio-exact, 6 axiom-free-exact`
at the shipped-corollaries commit, the reflow commit and the documentation
head (before and after the second rebase).

**FULL gate** at commit `cc4fe8f` (`CERB_MEM_MAX=40G scripts/test_unit.sh`),
the tail verbatim (lines `^==|^ok:|^info: CerberusHeapLang|^ALL GATES|^GATE-EXIT|^Build completed|^BOUNDARY|^ALLOWLISTED|^FAIL`):

```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 1b: fuel-numeral grep (scripts/fuel_numeral_check.sh; a numeral outside a *_shipped corollary is red) ==
ok: no fuel numeral (100000000/1000000/999999) outside a *_shipped corollary and no retired fuel constant (60 files scanned, comments stripped)
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:1116:0: CerberusHeapLang export pins: 901 trio-exact, 6 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1116:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (6450 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1116:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (9664 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (483 jobs).
ok: cerberus-heaplang build green
== speedbump: rule-use and classification manifest (regenerate; red on a red row or drift) ==
ok: capability manifest regenerated, no drift
== speedbump: corpus skeleton (hand-transcribed emitted Core vs docs/corpus-e0; scripts/corpus_skeleton.lean) ==
ok: corpus skeleton — every transcription matches its emitted text, every plant mismatches
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — 19 core modules, none imports an exhibit/example/production module
== speedbump: client boundary (positive clients mention no logic internals; scripts/boundary_check.sh) ==
ok:   Exhibit — 0 internals mentions
ok:   LoopExhibit — 0 internals mentions
ok:   FibExhibit — 0 internals mentions
ok:   ArrayExhibit — 0 internals mentions
ok:   ListRevExhibit — 0 internals mentions
ok:   TreeRotExhibit — 0 internals mentions
ok:   CaseExhibit — 0 internals mentions
ok:   WseqExhibit — 0 internals mentions
ok:   StructExhibit — 0 internals mentions
ok:   AllocExhibit — 0 internals mentions
ok:   DisposeExhibit — 0 internals mentions
ok:   RegionLoopExhibit — 0 internals mentions
ok:   MallocListExhibit — 0 internals mentions
ok:   FibRecExhibit — 0 internals mentions
ok:   TwoLabelExhibit — 0 internals mentions
ok:   EvenOddExhibit — 0 internals mentions
ok:   EmittedAExhibit — 0 internals mentions
ok:   EmittedBExhibit — 0 internals mentions
ok:   EmittedCExhibit — 0 internals mentions
ok:   CorpusT1Exhibit — 0 internals mentions
ok:   CorpusT5Exhibit — 0 internals mentions
ok:   CorpusT6Exhibit — 0 internals mentions
ok:   Examples.CallSmoke — 0 internals mentions
ok:   Examples.ReadinessSmoke — 0 internals mentions
ok:   Examples.Layout — 0 internals mentions
ok:   Examples.CorpusE0 — 0 internals mentions
ok:   Examples.CorpusE5 — 0 internals mentions
ok:   Examples.EmittedInt — 0 internals mentions
ok:   CorpusT4Exhibit — 0 internals mentions
BOUNDARY: 29 modules checked, 0 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
GATE-EXIT=0
```

## 12. L2 range audit fixes

[AGENT 2026-09-07] The range audit `f1f2573..d8ebad9`
(`2026-09-07_audit-l2-range.md`, committed verbatim at `d2ded73`; verdict PASS
WITH FIXES REQUIRED, no T-/C- finding) named R-1, R-2, D-1..D-6, H-1 and the
Note-level H-2. Every item is applied in commit `317dd29` on
`land/repin-89f7e68`; this section (docs-only, the third commit) is the record.
Worked in `worktrees/land-repin` only; every lake/lean invocation through
`scripts/capped` at `CERB_MEM_MAX=40G` (another agent's builds were running on
the box; no `UNCAPPED` line in any log). Every audit premise was re-measured
before its remedy was applied ("audit findings are claims"); two premises did
not survive (D-6(a)'s `hack` half; the audit's own per-file `panic!` breakdown)
and are recorded as such below. Quoted outputs are verbatim; tallies marked
DERIVED are mine.

### 12.1 Disposition

| id | done | where | verified against |
|---|---|---|---|
| R-1 | yes | ARCHITECTURE §3 "What the build checks" (the derivation) and the glossary's *pinned*; the erratum appended to §7 above; DECISIONS text §12.7 | `Audit.lean` at `46c28dc` vs this head, by ``-name (§12.2): `trioExports` 893 distinct → 901 distinct; `axiomFreeExports` absent → 6; REMOVED 4, MOVED 6, ADDED 18; 893 − 4 − 6 + 18 = 901 |
| R-2 | yes | the erratum appended to §3 above; DECISIONS text §12.7 | the 21 names of the §3 table: all 21 entries of `2026-09-07_l2-signatures-post.txt` carry `evalDepth … ≤ LemFuel.fuel`/`ProcsDepth LemFuel.fuel`; 20 are in `trioExports`; `wpt_driver_done_alloc` is not (and is not in `46c28dc`'s list either) |
| D-1 | yes | README, divergences table, Fuel row | generated `Driver.lean:469` (`finalize`: `hack … (match to_pure th_st.arena with …)`); the caller greps §12.3 |
| D-2 | yes | ARCHITECTURE §2.5 rows for `region_loop_certified_production`/`malloc_list_certified_production` ("NARROWED at the L2 re-pin"); KOI B21 names both; DECISIONS text §12.7 | `RegionLoopExhibit.lean:612` — `(halign : 0 < al) (hsize : 0 ≤ sz)`; `MallocListExhibit.lean:1672` — `(halign : 0 < al)`. The premise names are `halign`/`hsize`, not the audit's `hal`/`hsz` (nor §6's above — erratum, §12.8) |
| D-3 | yes | ARCHITECTURE §3 "The `panic!` arms"; README "What you are asked to take on faith"; KOI A5 | ONE measurement, ONE method (§12.2): 117, in nine seams; "twelve seams" → the manifest's 37 |
| D-4 | yes | KOI B7 | `Soundness.lean:1228` (`theorem esize_subst {e : CoreExpr} (x : sym) (v : value) : esize (subst_sym_expr x v e) = esize e`, no premise), `:1141` (`esize_subst_lemFuel`), `:1244`, `:1353`, `:1667`, `:1387` (unconditional); `Potential.lean:508`; generated `Core_aux.lean:531` (`subst_sym_expr … := subst_sym_expr_lemFuel (generic_expr.lemSize g) …`) |
| D-5 | yes | README "Scope, exactly" (the class list gains RULE-PARTIAL-UNDEMONSTRATED; the counts) | `docs/CAPABILITY_MANIFEST.md:182`: `MANIFEST: 35 constructors, 78 variant rows (40 RULE, 0 RULE-TOTAL-UNDEMONSTRATED, 7 RULE-PARTIAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 24 NO-RULE, 7 OUT-OF-SCOPE), 0 red, 25 consumer modules` |
| D-6 | yes — (a) for `to_pure` only: the `hack` half of the premise is FALSE | FUEL.md §1 (the `NDnd` qualification), §3 (the reason for four), §4 (`hack` and `to_pure` rows, reading (iii)) | generated `Driver.lean:518`–`:527`: `to_pure th_st.arena` at `:526`, no `hack` (§12.3); `ProdEntry.lean:82` (`globs := []`), `:370`/`:680` (`{ prodFile e with … }`, `{ prodFileWith … with … }`); `Nondeterminism.lean:212` (the `Nat.succ` arm's `NDnd` case re-binds at `lemFuel`, i.e. the caller's minus one); `Round.lean:6827` (`runOne_bind_nd`), `:6961`–`:7005` (`memop_fork`: `hfuel : 4 ≤`, `hF : LemFuel.fuel = fuel + 4` at `:6970`, `runOne_bind_active` at `:6985`, `runOne_bind_nd` at `:6987`/`:6990`/`:7001`) |
| H-1 | yes — TWELVE, not eleven | `Adequacy.lean` (8 sites), `Examples/CallSmoke.lean` (4 sites) | gate-log warnings 44 → 33, `section variable` warnings 11 → 0 (§12.5); the snapshot diff is exactly the twelve statements (§12.6) |
| H-2 | yes | `scripts/fuel_numeral_check.sh` | the self-test's 11 plants (§12.4); the tree run green; the gate's 1b ok-line byte-identical to before |

### 12.2 D-3 and R-1: the measurements (command and output verbatim)

The `panic!` count. Method: code occurrences of `panic!` in the 37 seams of
the pin's `handwritten_copy.manifest`, block comments (nested) and line
comments blanked, string literals kept — the stripper of gate 1b. Run from
the worktree root against the primed workspace:

```
$ cat > .l2fix-scratch/panic_count.py <<'PY'
# panic_count.py — count `panic!` arms in the 37 hand-written seams at the pin,
# comments stripped (nested block comments /- -/ and line comments --; string
# literals kept). Same stripping method as scripts/fuel_numeral_check.sh.
import re, sys, os
ws = '.cerberus-ws/lean_frontend'
man = [l.strip() for l in open(f'{ws}/handwritten_copy.manifest') if l.strip() and not l.startswith('#')]
def strip(src):
    out=[]; i=0; depth=0
    while i < len(src):
        if src.startswith('/-', i): depth+=1; i+=2; out.append('  '); continue
        if depth>0 and src.startswith('-/', i): depth-=1; i+=2; out.append('  '); continue
        c=src[i]; out.append(c if (depth==0 or c=='\n') else ' '); i+=1
    lines=''.join(out).split('\n')
    return [re.sub(r'--.*$','',l) for l in lines]
total=0; per={}
for f in man:
    p=f'{ws}/{f}'
    src=open(p,encoding='utf-8').read()
    n=sum(l.count('panic!') for l in strip(src))
    if n: per[f]=n
    total+=n
print(f"seams in manifest: {len(man)}")
for f,n in sorted(per.items(), key=lambda kv:-kv[1]): print(f"  {f}: {n}")
print(f"files carrying a panic!: {len(per)}")
print(f"TOTAL panic! arms (comment-stripped code, 37 seams): {total}")
PY
$ python3 .l2fix-scratch/panic_count.py
seams in manifest: 37
  CerbMem.lean: 60
  CerbFS.lean: 36
  CerbDecode.lean: 7
  CerberusImpl.lean: 4
  CerbUtils.lean: 4
  CerbLocation.lean: 2
  Main.lean: 2
  CerbTags.lean: 1
  CoreParser.lean: 1
files carrying a panic!: 9
TOTAL panic! arms (comment-stripped code, 37 seams): 117
```

In the same run: every `lean_frontend/<seam>.lean` is `cmp`-identical to its
`generated/<seam>.lean` copy (`seam-identity bad=0`); no lem-generated
(non-seam) file under `generated/` contains `panic!`; the raw
`grep -c 'panic!'` less line-comment LINES over the same 37 files gives 128
(DERIVED — a different method, quoted only to show why one method had to be
fixed; the audit got 126 by its own variant of it). The audit's per-file list
(eleven files, `CerbFloat.lean` 5 and `CerbND.lean` 1 among them) sums to
123, not to its stated 117: those two files mention `panic!` in comments
only, and the comment-stripped method excludes them — 117 in nine files is
the number on every surface now. The 54/7 mirror-vs-guard split was measured
at pin `f95ef8d9c` over 61 arms; it is NOT re-derived here and every surface
says so.

The pin accounting (the ``-names of `trioExports`/`axiomFreeExports`, line
comments stripped, at `46c28dc` — `git show 46c28dc:cerberus-heaplang/
CerberusHeapLang/Audit.lean` — and at this head):

```
46c28dc trioExports: 893 distinct 893
46c28dc axiomFreeExports: []
HEAD trioExports: 901 distinct 901
HEAD axiomFreeExports: 6 ['CerberusHeapLang.procCtxF_runState_labeled', 'CerberusHeapLang.procCtxF_sym_supply', 'CerberusHeapLang.procCtx_runState_labeled', 'CerberusHeapLang.procCtx_sym_supply', 'CerberusHeapLang.prodThread_eq_ctlThread', 'CerberusHeapLang.prodCtx_extern']
REMOVED (in old trio, in neither HEAD list): 4 ['CerberusHeapLang.drive_after_setup_lib_lemFuel', 'CerberusHeapLang.drive_after_setup_with_lemFuel', 'CerberusHeapLang.t4Q_pot', 'CerberusHeapLang.t6Q_pot']
MOVED (old trio -> HEAD axiomFree): 6 ['CerberusHeapLang.procCtxF_runState_labeled', 'CerberusHeapLang.procCtxF_sym_supply', 'CerberusHeapLang.procCtx_runState_labeled', 'CerberusHeapLang.procCtx_sym_supply', 'CerberusHeapLang.prodCtx_extern', 'CerberusHeapLang.prodThread_eq_ctlThread']
ADDED (HEAD trio, not in old): 18 ['CerberusHeapLang.counter_loop_certified_production_shipped', 'CerberusHeapLang.dispose_list_certified_production_shipped', 'CerberusHeapLang.drive_after_setup_lib_one', 'CerberusHeapLang.drive_after_setup_with_one', 'CerberusHeapLang.errno_init_eq', 'CerberusHeapLang.evalDepth_subst', 'CerberusHeapLang.even_odd_certified_production_shipped', 'CerberusHeapLang.exhibitA_prod_shipped', 'CerberusHeapLang.fib_certified_production_shipped', 'CerberusHeapLang.fib_rec_certified_production_shipped', 'CerberusHeapLang.list_reverse_certified_production_shipped', 'CerberusHeapLang.malloc_list_certified_production_shipped', 'CerberusHeapLang.peDepth_subst', 'CerberusHeapLang.region_loop_certified_production_shipped', 'CerberusHeapLang.t1_certified_production_shipped', 'CerberusHeapLang.t4_certified_production_shipped', 'CerberusHeapLang.t5_certified_production_shipped', 'CerberusHeapLang.t6_certified_production_shipped']
check: 893 - 4 - 6 + 18 = 901
R2 names listed in the record table: 21
pinned: 20
NOT pinned: ['wpt_driver_done_alloc']
```

### 12.3 D-1 and D-6: the caller greps over the pinned `generated/` (verbatim, lines cut at 90 columns)

```
$ grep -n "\bhack\b" Driver.lean | cut -c1-90
425:  match  CerbDebug.print_debug_pure (  2)  []  (fun (u : Unit) =>  match u with |  ()
436:  match  CerbDebug.print_debug_pure (  2)  []  (fun (u : Unit) =>  match u with |  ()
438:def hack [LemFuel] : (Fmap (sym) ((CerbLocation.Loc ×tag_definition))) -> Fmap (sym)
469:  match  dr_st.core_state0.thread_states with  |  [(tid1,  (_,  th_st))] => (
$ grep -n "\bto_pure\b" *.lean | grep -v "to_pure_lemFuel\|def to_pure\|to_pures" | cut -c1-90
Core_rewrite.lean:185: partial def  remove_unseqs  {a : Type} [LemFuel]  (g : generic_expr
Core_rewrite.lean:233:        match to_pure e2' with
Core_rewrite.lean:242:        match (to_pure e2', to_pure e3') with
Core_rewrite.lean:263:        match to_pure e1' with
Core_rewrite.lean:271:        match to_pure e1' with
Driver.lean:469:  match  dr_st.core_state0.thread_states with  |  [(tid1,  (_,  th_st))] =
Driver.lean:526:  let  glob_defs  := List.reverse  (List.foldl  (fun (acc : List ((sym ×c
$ grep -n "\bto_pures\b" *.lean | grep -v "to_pures_lemFuel\|def  to_pures\|theorem to_pures\|lemMeasureProofs" | cut -c1-90
Core_rewrite.lean:255:        match to_pures es' with
Core_rewrite.lean:296: partial def  pure_propagation2  {a : Type} [LemFuel]  (g : generic_
Core_run.lean:424:def  core_thread_step2 [LemFuel] (_lemReader_tagDefs : Fmap (sym) ((Cerb
```

Reading: `hack`'s code occurrences in `Driver.lean` are its definition
(`:436`/`:438`), a comment word at `:425` ("hackish", inside `driver2`) and the
ONE call at `:469` (`finalize`); the other ten files listed by
`grep -l "\bhack\b" *.lean` contain the word in comments only (`TODO: hack`).
`to_pure` is called at `finalize` (`:469`), at `driver_globals` (`:526`, the
`match to_pure th_st.arena with | some pe => (match valueFromPexpr pe …)`
inside the `nd_mapM_` over `glob_defs`) and in the rewriter
(`Core_rewrite.lean:233`/`:242`/`:263`/`:271`). `to_pures` is called at
`Core_rewrite.lean:255` and `Core_run.lean:424` (`core_thread_step2`). So the
audit's D-6(a) is right about `to_pure` and wrong about `hack`; FUEL.md §4 now
says both. The README's former "`to_pure`/`to_pures` only from the Core
rewriter … none from a `Frag` program's run" (D-1) was false for `to_pure`.

### 12.4 H-2: the self-test (verbatim) and the tree run

Tree run (`scripts/fuel_numeral_check.sh`, exit 0):
`ok: no fuel numeral (100000000/1000000/999999) outside a *_shipped corollary and no retired fuel constant (60 files scanned, comments stripped)`
— byte-identical to the line before the change, so the expected gate tail
(KOI §E, the DECISIONS L2 entry) is unchanged. `--selftest` (exit 0):

```
PLANT A (numeral in an ordinary theorem):
  PLANT OK: 2 hit(s)
PLANT B (retired constant):
  PLANT OK: 1 hit(s)
PLANT C (numeral in comments only, positive control):
  PLANT OK: green
PLANT D (numeral inside a *_shipped corollary, positive control):
  PLANT OK: green
PLANT E (numeral in the declaration after a *_shipped one):
  PLANT OK: 2 hit(s)
PLANT F (numeral in a non-declaration command after a *_shipped one):
  PLANT OK: 1 hit(s)
PLANT G (the numeral spelled 10^8):
  PLANT OK: 2 hit(s)
PLANT H (the numeral spelled 100_000_000):
  PLANT OK: 2 hit(s)
PLANT I (numeral after a "--" string literal on the same line):
  PLANT OK: 2 hit(s)
PLANT K (numeral after a comment containing a lone "):
  PLANT OK: 2 hit(s)
PLANT L (char literal '"' before a *_shipped corollary, positive control):
  PLANT OK: green
fuel_numeral_check: SELFTEST OK (11 plants: 8 red as required, 3 positive controls green)
```

Plants F, G, H and I are the audit's four leaks (all GREEN before, all RED
now); K and L exercise the two directions of the new literal-aware stripper
(a `"` in a comment must not hide code; a `'"'` char literal must not open a
string). The mechanism: one tokenizer pass tracks `code | string | line-
comment | block-comment(depth)`; a `--`/`/-` inside a literal is literal text,
a `"` inside a comment is comment text; an unterminated literal or block
comment at end of file is RED (the file could not be classified); the
`*_shipped` allowance is reset at every column-0 line that is not a
declaration header (the header regex is unchanged); `NUMERALS` gains
`100_000_000|10\s*\^\s*8` and, for the same values already listed,
`1_000_000|10\s*\^\s*6|999_999`. The package's one `"--"` string literal
(`Examples/CorpusE0.lean:481`, `startsWith cs "--"`) is now scanned past
instead of being cut at the quote.

### 12.5 H-1: the warnings

Baseline (a cached replay of `lake build` at `d8ebad9`, before any edit):
44 `warning: CerberusHeapLang/*` lines — `Potential.lean` 31, `Heap.lean` 2,
`Adequacy.lean` 8, `Examples/CallSmoke.lean` 3; the eleven
`automatically included section variable(s) unused in theorem …` at exactly
the audit's lines (`Adequacy.lean:735`, `:756`, `:760`, `:764`, `:768`, `:852`,
`:1403`, `:1407`; `CallSmoke.lean:168`, `:176`, `:196`). After the eleven
fixes the FULL gate reported 34: `CallSmoke.lean:185:0: automatically
included section variable(s) unused in theorem CerberusHeapLang.csCtx_fragProcs`
— a CASCADE: `csCtx_fragProcs` (PINNED, `Audit.lean:617`) used its instance
only to pass it to `csFBody_frag`/`csMainBody_frag`, which no longer take one;
a twelfth vacuous binder, fixed the same way. Final: **33** (`Potential.lean`
31, `Heap.lean` 2 — `Heap.lean:1396:5`/`:2379:5` "Variable name … is not
explicitly referenced"), zero `section variable` warnings. Each `omit
[LemFuel] in` sits on the blank separator line above its theorem (or its
docstring), so NO line of `Adequacy.lean`/`CallSmoke.lean` moved (the files
are 2358/460 lines before and after); the two double binders lost their
explicit `[LemFuel]` on the same line.

### 12.6 The snapshot: `2026-09-07_l2-signatures-post.txt` → `2026-09-07_l2b-signatures-post.txt` (verbatim `diff`)

Regenerated at the built tree of `317dd29` (`scripts/signature_snapshot.lean`,
52222 → 52221 lines); the diff is exactly the twelve statements, each losing
its vacuous `[LemFuel]` binder (a strengthening: the statement no longer
quantifies over an instance it does not read):

```
2996,2997c2996,2997
< ∀ [LemFuel] {e : CerberusHeapLang.CoreExpr} {ctx : context} {an : List annot}
<   {ra : core_run_annotation} {f : sym} {pes : List (generic_pexpr Unit sym)},
---
> ∀ {e : CerberusHeapLang.CoreExpr} {ctx : context} {an : List annot} {ra : core_run_annotation}
>   {f : sym} {pes : List (generic_pexpr Unit sym)},
10016c10016
< ∀ [LemFuel] [inst : LemFuel] {M : CerberusHeapLang.MachineCtx},
---
> ∀ [inst : LemFuel] {M : CerberusHeapLang.MachineCtx},
25011c25011
< ∀ [LemFuel] (ra : core_run_annotation) (bty ybty : core_base_type),
---
> ∀ (ra : core_run_annotation) (bty ybty : core_base_type),
25033c25033
< ∀ [LemFuel] [inst : LemFuel],
---
> ∀ [inst : LemFuel],
25045c25045
< ∀ [LemFuel] (bty ybty : core_base_type), CerberusHeapLang.Frag (CerberusHeapLang.csFBody bty ybty)
---
> ∀ (bty ybty : core_base_type), CerberusHeapLang.Frag (CerberusHeapLang.csFBody bty ybty)
25125c25125
< ∀ [LemFuel] (ra : core_run_annotation), CerberusHeapLang.Frag (CerberusHeapLang.csMainBody ra)
---
> ∀ (ra : core_run_annotation), CerberusHeapLang.Frag (CerberusHeapLang.csMainBody ra)
36425c36425
< ∀ [LemFuel] (rs : core_run_state), (CerberusHeapLang.procCtx rs).FragProcs
---
> ∀ (rs : core_run_state), (CerberusHeapLang.procCtx rs).FragProcs
36436c36436
< ∀ [LemFuel] (rs : core_run_state) (n : Nat), (CerberusHeapLang.procCtx rs).ProcsDepth n
---
> ∀ (rs : core_run_state) (n : Nat), (CerberusHeapLang.procCtx rs).ProcsDepth n
39284c39284
< ∀ [LemFuel], CerberusHeapLang.spikeCtx.FragProcs
---
> CerberusHeapLang.spikeCtx.FragProcs
39293,39294c39293
< ∀ [LemFuel] (bound : Nat) (l : sym) (params : List (sym × core_base_type))
<   (cont : CerberusHeapLang.CoreExpr),
---
> ∀ (bound : Nat) (l : sym) (params : List (sym × core_base_type)) (cont : CerberusHeapLang.CoreExpr),
39301c39300
< ∀ [LemFuel] (l : sym) (params : List (sym × core_base_type)) (cont : CerberusHeapLang.CoreExpr),
---
> ∀ (l : sym) (params : List (sym × core_base_type)) (cont : CerberusHeapLang.CoreExpr),
39330c39329
< ∀ [LemFuel] (n : Nat), CerberusHeapLang.spikeCtx.ProcsDepth n
---
> ∀ (n : Nat), CerberusHeapLang.spikeCtx.ProcsDepth n
```

The twelve, in hunk order: `Decomp.frag_plug_call` (PINNED),
`MachineCtx.FragProcs.toFuel` (the double binder → one), `csCtx_fragProcs`
(PINNED; the cascade), `csCtx_procsDepth` (the double binder → one),
`csFBody_frag`, `csMainBody_frag`, `procCtx_fragProcs`, `procCtx_procsDepth`,
`spikeCtx_fragProcs` (PINNED), `spikeCtx_labels_depth`, `spikeCtx_labels_frag`,
`spikeCtx_procsDepth`. The three pinned statements before → after:
`spikeCtx_fragProcs : ∀ [LemFuel], spikeCtx.FragProcs` →
`spikeCtx.FragProcs`; `Decomp.frag_plug_call : ∀ [LemFuel] {e ctx an ra f pes}, Decomp e ctx (callRedex an ra f pes) → Frag e → ∀ (a : List annot) (v : value), Frag (apply_ctx ctx (ofValA (.pure a [] v)))` →
the same without `[LemFuel]`; `csCtx_fragProcs : ∀ [LemFuel] (ra : core_run_annotation) (bty ybty : core_base_type), (csCtx ra bty ybty).FragProcs` →
the same without `[LemFuel]`. Their pin entries are unchanged and the axiom
sets are unchanged (the gate line below). Nothing else in the 52221 lines moved.

### 12.7 For the orchestrator — DECISIONS replacement texts and the KOI row not edited

The DECISIONS L2 entry (2026-09-07 [AGENT] "L2 LANDED ON `land/repin-89f7e68`")
is orchestrator-owned; the errata, in the register's "later governs" form:

- **R-1** — for "Pins 893 → 901 trio-exact + 6 axiom-free-exact." read:
  "Pins 893 → 901 trio-exact + 6 axiom-free-exact, derived (L2 range audit
  R-1, re-measured at the fixes): 893 − 4 REMOVED
  (`drive_after_setup_{lib,with}_lemFuel`, `t4Q_pot`, `t6Q_pot`) − 6 MOVED
  from `trioExports` to the NEW class `axiomFreeExports`
  (`procCtxF_runState_labeled`, `procCtxF_sym_supply`,
  `procCtx_runState_labeled`, `procCtx_sym_supply`, `prodThread_eq_ctlThread`,
  `prodCtx_extern`; the class did not exist at L1 — the L1 gate line is
  `export pins: 893 trio-exact`) + 18 ADDED (the thirteen `*_shipped`,
  `peDepth_subst`, `evalDepth_subst`, `drive_after_setup_{lib,with}_one`,
  `errno_init_eq`) = 901."
- **R-2** — for "23 exports restated over `Frag e` + a depth hypothesis" read:
  "21 exports restated over `Frag e` + a depth hypothesis (20 pinned;
  `wpt_driver_done_alloc` restated but unpinned, as it always was)."
- **D-2** — for "`region_loop`/`malloc_list` production statements gained
  `0 < al`" read: "`region_loop_certified_production` gained `halign : 0 < al`
  and `hsize : 0 ≤ sz`, `malloc_list_certified_production` gained
  `halign : 0 < al` — the two statements are NARROWED at the re-pin (the
  coverage of `al ≤ 0` / `sz < 0` that pin `f95ef8d9c`'s clamping allocator
  gave is gone), forced by the pin's unclamped `allocator`
  (`CerbMem.lean:2089`–`:2103`, `panic!` at `align == 0`)."

KOI **C5** was NOT edited (the brief names A5/B7/B21 only). Proposed text for
the orchestrator: append to C5's Item cell "→ 44 at the L2 landing (Potential
31, Heap 2, Adequacy 8, CallSmoke 3 — the eleven new ones vacuous `[LemFuel]`
binders, L2 range audit H-1) → 33 at the L2 audit fixes (`317dd29`; Potential
31, Heap 2; zero `section variable` warnings)" and set Status to "Hold at ≤ 33;
each slice fixes what it introduces."

### 12.8 [AGENT] decisions and deviations

1. **`omit [LemFuel] in` on the blank separator lines**, not on new lines:
   §10 item 4 above declined a reflow because it would move cited line
   numbers; the same rule here — no line of either file moved, so no cite
   in ARCHITECTURE/README/FUEL/WALKTHROUGH/API changed, and `cite_check`
   reproduces its earlier classes (§12.9).
2. **The twelfth binder** (`csCtx_fragProcs`, pinned) is a cascade the audit
   could not have seen at HEAD; fixed in the same commit, recorded here.
3. **D-6(a)'s `hack` half is false** (§12.3): `driver_globals` calls
   `to_pure`, never `hack`; FUEL.md states `hack`'s single caller and
   `to_pure`'s second site. The audit's `Nondeterminism.lean:213` for the
   `NDnd` arm is `:212` at the pin (the `Nat.succ` arm is one line); cited so.
4. **The audit's per-file `panic!` breakdown summed to 123 against its
   stated 117** (§12.2); the one method here gives 117 in nine files
   (`CerbFloat.lean`/`CerbND.lean` comment-only). The 54/7 split is stated
   as the previous pin's measurement on every surface, not re-derived.
5. **Two sentences false at HEAD that the audit did not list**, fixed in
   the same class as D-*: ARCHITECTURE's header (`:7`) and §3 (`:585`) named
   the pin as `f95ef8d9c` → `89f7e6885` (§3 read "the pinned semantics
   (`f95ef8d9c`) … It is the pin `89f7e6885`"); README "eighteen modules
   classified `positive-client`/`declared-smoke`" and ARCHITECTURE §5 "22
   modules: the twenty program exhibits" → 25 (`scripts/module_classes.tsv`:
   23 `positive-client` + 2 `declared-smoke`; the manifest's "25 consumer
   modules"). README's class list also gains RULE-PARTIAL-UNDEMONSTRATED,
   which the manifest has reported since E5 and the sentence omitted.
6. **Numeral spellings**: the audit asked for `10^8`/`100_000_000`; the same
   values' other listed numerals get their twins (`1_000_000`, `10^6`,
   `999_999`). A hex spelling is not covered and the header says so (the
   gate is a speedbump against honest drift; the trust base is the build).
   The gate's ok-line was kept byte-identical (the expected tails stand).
7. **`csCtx_fragProcs`'s docstring** said "with sufficient operand fuel" —
   false since R2 (the depth is `csCtx_procsDepth`); one clause corrected
   while editing the line above it.
8. **Errata to this record** (text above left as written): §3
   "twenty-three" (R-2 erratum appended there); §7 "893 → 901 … the six
   axiom-free-exact pins unchanged" (R-1 erratum appended there); §6 names
   the new premises `hal`/`hsz` — the theorems' names are `halign`/`hsize`
   (`RegionLoopExhibit.lean:613`, `MallocListExhibit.lean:1672`); §7's ADDED
   row counts "23" `*_fuel` device forms — 22 by name in the census file.
9. **Build cost.** The one real rebuild (after the `Adequacy.lean` edit:
   Adequacy → every client) finished, as a FULL gate, 181 s after the edit
   (mtime of the gate log minus mtime of the file — an upper bound);
   the final FULL gate and the two snapshot runs (34 s each) were cached
   replays plus `CallSmoke`. No pass approached the tripwire.
10. **Scratch** `.l2fix-scratch/` (worktree root, untracked: the gate logs,
    the census/pin scripts, the cite TSVs) is deleted at the end of the
    slice; everything it produced is quoted above.

### 12.9 `cite_check.sh` on ARCHITECTURE.md — the last step of the docs pass (verbatim final line)

`cite-check: ARCHITECTURE.md — 301 cites; EXACT 235; DECL 16 (fixed 0; ranges among them counted in RANGE); USE 15; HAND 22; PIN 13; NOFILE 0; RANGE 18 (never rewritten)`

Against the audit's `EXACT 233 … USE 14; PIN 16; RANGE 16`: the four cite
tokens I removed (`CerbFS.lean:47`, `CoreParser.lean:2097`,
`CerbMem.lean:1127`–`:1132` — all stale at the pin: a table comment, a parser
line, a `.MVunion` arm) are replaced by four (`CoreParser.lean:2413` — the
parser's `panic!`; `CerbMem.lean:1261`–`:1262` — the `panicWithPosWithDecl … =
default := … rfl` fact; `docs/CAPABILITY_MANIFEST.md:182` — the manifest's
tail line, which the tool files as USE because it attributes the cite to the
nearest backticked name, `Examples.ReadinessSmoke`); every other non-EXACT
line is one the audit hand-checked or a HAND/PIN/RANGE the tool never judges.
Run twice, before and after the `.lean` edits: byte-identical output.

### 12.10 The FULL gate at `317dd29`, verbatim

`CERB_MEM_MAX=40G scripts/test_unit.sh` on the tracked tree of `317dd29`
(run immediately before the commit; the only uncommitted file was this
record, which no gate reads); matching lines
`^==|^ok:|^info: CerberusHeapLang|^ALL GATES|^GATE-EXIT|^Build completed|^BOUNDARY|^ALLOWLISTED|^FAIL`, unmodified:

```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 1b: fuel-numeral grep (scripts/fuel_numeral_check.sh; a numeral outside a *_shipped corollary is red) ==
ok: no fuel numeral (100000000/1000000/999999) outside a *_shipped corollary and no retired fuel constant (60 files scanned, comments stripped)
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:1116:0: CerberusHeapLang export pins: 901 trio-exact, 6 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1116:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (6450 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1116:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (9664 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (483 jobs).
ok: cerberus-heaplang build green
== speedbump: rule-use and classification manifest (regenerate; red on a red row or drift) ==
ok: capability manifest regenerated, no drift
== speedbump: corpus skeleton (hand-transcribed emitted Core vs docs/corpus-e0; scripts/corpus_skeleton.lean) ==
ok: corpus skeleton — every transcription matches its emitted text, every plant mismatches
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — 19 core modules, none imports an exhibit/example/production module
== speedbump: client boundary (positive clients mention no logic internals; scripts/boundary_check.sh) ==
ok:   Exhibit — 0 internals mentions
ok:   LoopExhibit — 0 internals mentions
ok:   FibExhibit — 0 internals mentions
ok:   ArrayExhibit — 0 internals mentions
ok:   ListRevExhibit — 0 internals mentions
ok:   TreeRotExhibit — 0 internals mentions
ok:   CaseExhibit — 0 internals mentions
ok:   WseqExhibit — 0 internals mentions
ok:   StructExhibit — 0 internals mentions
ok:   AllocExhibit — 0 internals mentions
ok:   DisposeExhibit — 0 internals mentions
ok:   RegionLoopExhibit — 0 internals mentions
ok:   MallocListExhibit — 0 internals mentions
ok:   FibRecExhibit — 0 internals mentions
ok:   TwoLabelExhibit — 0 internals mentions
ok:   EvenOddExhibit — 0 internals mentions
ok:   EmittedAExhibit — 0 internals mentions
ok:   EmittedBExhibit — 0 internals mentions
ok:   EmittedCExhibit — 0 internals mentions
ok:   CorpusT1Exhibit — 0 internals mentions
ok:   CorpusT5Exhibit — 0 internals mentions
ok:   CorpusT6Exhibit — 0 internals mentions
ok:   Examples.CallSmoke — 0 internals mentions
ok:   Examples.ReadinessSmoke — 0 internals mentions
ok:   Examples.Layout — 0 internals mentions
ok:   Examples.CorpusE0 — 0 internals mentions
ok:   Examples.CorpusE5 — 0 internals mentions
ok:   Examples.EmittedInt — 0 internals mentions
ok:   CorpusT4Exhibit — 0 internals mentions
BOUNDARY: 29 modules checked, 0 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
GATE-EXIT=0
```

Line for line the tail of §11 (at `cc4fe8f`) and of the DECISIONS L2 entry;
33 `warning: CerberusHeapLang/*` lines in the full log (§12.5); no `UNCAPPED`
line.
