# 2026-09-03 — RE-PIN SCOUT 2: dry run of cerberus-heaplang onto cerberus-lean `de2fbf1bd` (pin-bump 3c88f0d + zero-discrepancy Z1)

Scout record (worker, branch `repin-scout2`, worktree
`worktrees/repin-scout2`, base `2bbfd70` = the F1 head). Scope: MEASURE,
do not fix — every Lean touch made to see past a frontier is labelled
SCOUT-ONLY below and was REVERTED before the commit (`git status` at
commit time: `scripts/semantics-pin.env` + this record only). Provenance:
the operator's scout-2 brief (2026-09-03); the `docs/DECISIONS.md` entry
"CERBERUS-LEAN MOVED" (scout priorities (1)–(4), dynamic_addrs outcome);
the previous scout `docs/2026-09-03_repin-scout.md` and the re-pin record
`cerberus-heaplang/docs/2026-09-03_repin-fuel-notes.md` (the method).
Quoted outputs are verbatim; tallies marked DERIVED are grep/diff-derived;
§6 is an ESTIMATE. The user was offline; every decision here is [AGENT].

Old pin: `f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf`. Target (this dry
run): `de2fbf1bd3001491c741f6a1b0b7d36412db3be5` = cerberus-lean mainline
`mdd/cerberus-lean` HEAD at scout time (`git -C cerberus-lean rev-parse
mdd/cerberus-lean` = `git rev-parse HEAD` = `de2fbf1bd…`; the primary
checkout is built at it; 34 commits in the range, DERIVED via `git
rev-list --count`). The operator says cerberus-lean will likely move again
before the re-pin proper ("the remaining things are lighter fixes"); this
record sizes the work against `de2fbf1bd` so the re-pin brief can be
precise, and names what to re-measure if the head moves.

The consumer manifests on their side (read in full, verified against the
tree here where cited): `lean_frontend/docs/2026-09-03_pin-bump-change-manifest.md`
(LemLib 045dcb0 → 3c88f0d), `…_zero-discrepancy-Z1-change-manifest.md`
(killM, copyAllocId, device ranges, casePtrval, IvMaxAlignment, CerbFS),
`…_dynamic-addrs-investigation.md` (§0, §5, §6).

## 0. Headline

| | |
|---|---|
| Build at the new pin, demo manifest untouched | FAILS in the DEPENDENCY cone (`Enum`, `Float`, `Utils`: unknown `lemNatFromNatural`/`lemIntFromInteger`/`lemListFoldr`/`Pset`) — the demo's `lake-manifest.json` pins LemLib at `045dcb0`; **it MUST move to `3c88f0d`** (§2) |
| After `lake update LemLib` (offline, via the container redirect) | dependency cone green (Cabs 98 s); the demo's first module `Step` fails |
| Modules elaborated end to end with SCOUT-ONLY stubs | 38 of 39 (all but `Audit`, which fails on `sorryAx` — the stubs — as designed) |
| Failing declarations at the frontier (measured, cumulative) | **41 sites in 12 files**, of **five classes** (§4); everything else green untouched |
| Exported statements whose TEXT must change | **1**: `killM_killed_inv` (Audit pin; new refusal rows) — plus **1 definition** in a pinned premise: `SymMap` (EnvLaws; the `Fmap` representation) — §5 |
| The nine production statements | textually UNCHANGED (their modules elaborate; their proofs depend on the registration `rfl`s, which are the largest class) |
| Biggest single item | the LemLib `Fmap`/`Pmap` representation: EnvLaws' lookup law needs a BST invariant + `Pmap.find?/add` theorem (L), and the WF-recursive `Pmap.join` blocks every registration/`collect_saves` `rfl` (14 sites, M) — §4(a)/(a′) |
| What did NOT change for us | `CerbND.drive`/`drive_lemFuel`/`drive_wrapper_defeq`/`fuelExhaustedKill`/`CerbFuel.driverFuel`/`initial_driver_state`: byte-identical (§7) |

## 1. What was done (verbatim commands and key outputs)

### 1.1 The pin

`scripts/semantics-pin.env`: `CERBERUS_LEAN_COMMIT` `f95ef8d9c…` →
`de2fbf1bd3001491c741f6a1b0b7d36412db3be5` (this worktree; `.cerberus-ws`
did not exist). `scripts/setup-cerberus-dep.sh`, verbatim (rc 0, 2.0 s):

```
== setup-cerberus-dep: A: cloning /home/dev/projects/cerberus-lean-proj/cerberus-lean -> /home/dev/projects/cerberus-lean-proj/refined-cerberus/worktrees/repin-scout2/.cerberus-ws @ de2fbf1bd3001491c741f6a1b0b7d36412db3be5
Cloning into '/home/dev/projects/cerberus-lean-proj/refined-cerberus/worktrees/repin-scout2/.cerberus-ws'...
done.
HEAD is now at de2fbf1bd zero-discrepancy Z1: pre-merge audit of arc/zero-discrepancy @ e6f86bdcb — MERGE-WITH-FIXES
== setup-cerberus-dep: B: priming lean_frontend/generated
== setup-cerberus-dep: B: priming lean_frontend/native
== setup-cerberus-dep: B: priming lean_frontend/.lake
check_lem_sync: lean OK (src 4f2e089b39d5b371973513b3350f81d1b89871976f77df9ba4a25da3421d0c54, gen 41781645302ba346ab11977956c6eb2e82f5de95678bc3d1091b1ae9e9eab3f8)
== setup-cerberus-dep: C ok: 23 hand-written seams byte-identical to the pin
== setup-cerberus-dep: DONE. Lake consumes /home/dev/projects/cerberus-lean-proj/refined-cerberus/worktrees/repin-scout2/.cerberus-ws/lean_frontend as a path dependency.
```

The primary checkout IS at the pin, so section B took the equal-commit
path (the content guard's diff branch did not run); section C read the
pin's `handwritten_copy.manifest` (23 seams, unchanged in the range — the
manifest file has no diff in `f95ef8d..de2fbf1`). `.primed-from`:
`de2fbf1bd3001491c741f6a1b0b7d36412db3be5 2026-09-03T23:07:26Z`. Note the
`src` stamp hash is unchanged from the previous pin (`4f2e089b…`: no `.lem`
changed — `git diff --stat f95ef8d..de2fbf1 -- frontend` is EMPTY) while
the `gen` hash moved (`49ad8b2c…` → `41781645…`): the whole generated
delta is the lem BACKEND (LemLib 3c88f0d), not the model. DERIVED: 58 of
the generated `.lean` files differ between the two primed workspaces
(`diff -rq` of `.cerberus-ws/lean_frontend/generated` at `f95ef8d`, the
primary refined-cerberus checkout's, read-only, vs this worktree's).

### 1.2 The semantics delta on the code-bearing paths (verbatim `git diff --stat f95ef8d9c… de2fbf1bd… -- …`)

```
 lean_frontend/CerbCall.lean                        |   6 +-
 lean_frontend/CerbDecode.lean                      |  36 +-
 lean_frontend/CerbFS.lean                          | 444 ++++++++++++++-------
 lean_frontend/CerbFunMapInstances.lean             |  27 +-
 lean_frontend/CerbLocation.lean                    |  70 +++-
 lean_frontend/CerbMem.lean                         | 185 ++++++---
 lean_frontend/CerbUtils.lean                       |   7 -
 lean_frontend/CoreParser.lean                      | 185 ++++++++-
 lean_frontend/Main.lean                            | 166 ++++++--
 .../lean4/repro/OverflowInMalloc.lean              |  28 ++
 .../upstream-tray/lean4/repro/PlainRecursion.lean  |  17 +
 .../docs/upstream-tray/lean4/repro/Variants.lean   |  63 +++
 lean_frontend/lake-manifest.json                   |   4 +-
 lean_frontend/lakefile.toml                        |   6 +-
 lean_frontend/speclab/SpecLab/ListAppendCore.lean  |   2 +-
 lean_frontend/test/Unit/FuelExemplar.lean          |  10 +-
 16 files changed, 989 insertions(+), 267 deletions(-)
```

Paths with NO diff in the range (checked): `frontend/` (the `.lem`
model), `lean_frontend/native`, `lean_frontend/handwritten_copy.manifest`,
`lean_frontend/Makefile`, `Makefile`, `lean_frontend/CerbND.lean`,
`lean_frontend/CerbFuel.lean`. `CerbMem.lean`'s diff is exactly the Z1
manifest §1 (read in full): `import Std.Data.TreeMap` added; `casePtrval`
gains `[Inhabited α]` and its fallback is `panic! "case_ptrval"`; `killM`
re-mirrored arm for arm (:1912–1968); `deviceRanges`/`isWithinDevice` new,
device arms in `loadM`/`storeM`/`ptrfromint`; `intfromptr` carries the loc;
`copyAllocId` real. Top-level declaration names in the generated tree
(DERIVED, `def|theorem|…` grep, old vs new): removed `set_fold`,
`update0`; added `update`, `deviceRanges`, `isWithinDevice`, `anyFdOn`,
`countOf`, `dirname`, `fdOf`, `isStdFd`, `libLoc`, `libraryDirs`, `mover*`
(7), `parseLibraryFile`, `refusal`, `refuseFlag`, `reloc*` (8),
`simpleLocation`, `stampLibraryFile`, `libcMapFromAssoc`, and the
`*.beq_deriv_aux*`/`*.cmp_deriv_aux*`/`*.ctor_rank_ocaml`/`*.beq_derived`/
`*.compare_derived` families. Also one record FIELD rename in the generated
`Nondeterminism.lean`: `Constraints.concat0` → `concat` (0 demo references).
None of the removed names is cited by the demo.

### 1.3 Builds (all through `scripts/capped`, `CERB_MEM_MAX=40G`; no UNCAPPED warning in any log; an auditor built concurrently)

Twelve `lake build` cycles, 23:08 → 23:33 UTC (the dep cone once, 2.3 min,
`Cabs (98s)`; every later cycle 5–20 s of elaboration + the failing module).
Cycle 1 is the manifest measurement (§2); cycles 2–12 each advanced the
frontier by one SCOUT-ONLY touch set (§3). Final state (cycle 12): every
module but `Audit` built; `Audit` fails exactly as it must with `sorry` in
a pinned cone, verbatim:

```
error: CerberusHeapLang/Audit.lean:567:0: CerberusHeapLang export pin FAILED: CerberusHeapLang.exhibitA_engine depends on axioms [Classical.choice,
 Quot.sound,
 propext,
 sorryAx], expected EXACTLY [Classical.choice, Quot.sound, propext]
```

Modules built green at the new pin WITHOUT any touch (DERIVED, union of
the `Built CerberusHeapLang.*` lines over the cycles minus the touched
files): `Lang`, `Rules`, `Wps`, `Wpt`, `Potential`, `Adequacy`,
`TotalAdequacy`, `API`, `ProdLoop`, `Exhibit`, `LoopExhibit`, `FibExhibit`,
`DivergeExhibit`, `ArrayExhibit`, `ListRevExhibit`, `TreeRotExhibit`,
`CaseExhibit`, `WseqExhibit`, `StructExhibit`, `AllocExhibit`,
`Examples.Layout`, `Examples.ReadinessSmoke`, `Examples.MirrorCoverage`,
`Examples.CallSmoke` (24 of 39). Touched and then green: `Step`, `EnvLaws`,
`Heap`, `Soundness`, `DriverCollapse`, `EvalClass`, `Round`, `ProdEntry`,
`ProdExhibit`, `ProdLoopExhibit`, `RegionLoopExhibit`, `FibRecExhibit`,
`DisposeExhibit`, `MallocListExhibit` (14). Not green: `Audit` (1).

## 2. The Lake / LemLib pin situation (measured)

- cerberus-lean at `de2fbf1bd` pins LemLib at
  `3c88f0d7e5556491d733932c503c1637ae186f54` (`lean_frontend/lakefile.toml`
  + `lake-manifest.json`, URL `https://github.com/OathTech/lem-lean`). The
  primed workspace's own `.lake/packages/LemLib` is at `3c88f0d` (verified
  by `git rev-parse HEAD` in it).
- The DEMO's `cerberus-heaplang/lake-manifest.json` carries the INHERITED
  entry `LemLib` at `045dcb0d57a171eb4fb3a6eb5abe288c227270ce`, URL
  `https://github.com/septract/lem-lean`, and Lake HONOURS THE ROOT
  MANIFEST: cycle 1 (`lake build` with the manifest untouched) resolved
  LemLib at `045dcb0` (the demo's `.lake/packages/LemLib` stayed at
  `045dcb0`; no "manifest out of date" message was printed) and the
  generated tree failed against the OLD library, verbatim:

  ```
  error: generated/Enum.lean:58:19: Unknown identifier `lemNatFromNatural`
  error: generated/Float.lean:102:59: Unknown identifier `lemIntFromInteger`
  error: generated/Utils.lean:90:2: Unknown identifier `lemListFoldr`
  error: generated/Utils.lean:116:74: Unknown identifier `Pset`
  ```
  (`Some required targets logged failures: - Enum - Float - Utils`.) So
  the re-pin MUST move the demo's manifest — this is the first re-pin
  where that is true (the fuel re-pin left it at `045dcb0` because the rev
  had not moved).
- Availability offline: `3c88f0d` is in the local `lem-lean` checkout
  (`git -C lem-lean rev-parse 3c88f0d…` resolves; `mdd/lean-backend` is
  two DOCS-ONLY commits ahead at `0890229`, `git diff --stat 3c88f0d
  mdd/lean-backend -- lean-lib` EMPTY). There is NO `deps/mirrors/*lem*`
  bare mirror; `deps/gitconfig` redirects BOTH URL spellings
  (`septract/lem-lean`, `OathTech/lem-lean`) to the live checkout, and
  `scripts/capped` self-loads the container env, so the move works
  in-sandbox. Verbatim (`../scripts/capped ~/.elan/bin/lake update LemLib`
  in `cerberus-heaplang/`, 0.6 s, rc 0):

  ```
  info: toolchain not updated; already up-to-date
  info: LemLib: URL has changed; deleting '/home/dev/projects/cerberus-lean-proj/refined-cerberus/worktrees/repin-scout2/cerberus-heaplang/.lake/packages/LemLib' and cloning again
  info: LemLib: cloning https://github.com/OathTech/lem-lean
  info: LemLib: checking out revision '3c88f0d7e5556491d733932c503c1637ae186f54'
  ```
  Resulting manifest diff: the `LemLib` entry only — `url` septract →
  OathTech, `rev`/`inputRev` `045dcb0…` → `3c88f0d…`; `iris`, `Qq`,
  `batteries` untouched (verified by `git diff cerberus-heaplang/lake-manifest.json`).
  The manifest change was REVERTED with the other scout touches (this
  branch is a record); the re-pin slice re-runs the same command.
- `LemLibTheorems` (the kernel-checked `lem*_eq` equations, lem-lean
  `lean-lib/LemLibTheorems.lean`, a `@[default_target] lean_lib` of the
  LemLib package at `3c88f0d`) is REACHABLE from the demo by `import
  LemLibTheorems` — measured: the SCOUT-ONLY `import LemLibTheorems` in
  `Step.lean` built the module and the demo's cycles printed its
  `#print axioms` lines (e.g. verbatim `info: LemLibTheorems.lean:255:0:
  'LemLibTheorems.lemListFoldr_eq' depends on axioms: [propext,
  Quot.sound]`). All within the trio; `lemListZipSameLength_eq` uses
  `Classical.choice` (fine). NOTHING in LemLib or LemLibTheorems states a
  `Pmap`/`Pset` LAW (lookup-after-add, union equations): `LemLibTest.lean`
  is `#guard`-only bounded testing (`Pmap.wellFormed`, `strictlyAscending`
  over 5832 sequences) — tests, never theorems. See §4(a).

## 3. The SCOUT-ONLY touches (all reverted) and the frontier they opened

Cumulative, in the order the frontier moved (cycle → touch → what became
visible). 43 marker lines in 14 files (DERIVED, `grep -c SCOUT-ONLY` after cycle
12): 30 `sorry` stubs (statement kept, proof removed), 5 `show … from
sorry` inside proofs, 8 definitional/import stand-in lines in
`EnvLaws`/`Step`.

| cycle | module | touch | why (the measured error) |
|---|---|---|---|
| 2 | dep cone | (none — after `lake update LemLib`) | dep cone green; `Step` fails |
| 3–4 | `Step` | `import LemLibTheorems`; `simp only [LemLibTheorems.lemListFoldr_eq, List.foldr_cons(, List.foldr_nil)]` at `valueFromPexprs_cons` :1182 and `valueFromPexprs_pair` :1196 (a bare `rw` rewrote only the head instance — the RHS's `valueFromPexprs pes` unfolds to a second `lemListFoldr` — so `simp only` is the idiom) | `` `simp` made no progress `` on `List.foldr_cons`: `valueFromPexprs` (Core_aux.lean:477) now folds with `lemListFoldr` |
| 5 | `EnvLaws` | local `def lemCmpToOrd`; `symAdd`/`envAdd` without the `[BEq]` instance argument; `SymMap` redefined over `Fmap.mk symCmpK (p : Pmap sym β)`; `fmapLookupBy_addBy_empty` and `symAdd_lookup` proofs → `sorry` | 14 errors: `Unknown identifier lemCmpToOrd` (removed from LemLib); `fmapAddBy instBEqOfMapKeyType` type mismatch (`fmapAddBy` lost its `[BEq α]` binder); `SymMap`'s `∃ bk bs n, m = Fmap.mk symOrd bk bs n` against the new 2-constructor `Fmap`; every `Std.TreeMap.*` rewrite dead; `procEnv_single`/`update_env_aux_sym`/`update_env_aux_spec` `rfl`s failed only through the ill-typed `envAdd` (they passed once `envAdd` was re-typed) |
| 5 | `Heap` | `killM_success` :1320, `killM_success_dynamic` :1339: `sorry` after the `simp only`; `MemWF.killM` :2010: `all_goals sorry` after the case split | unsolved goals: the `simp only` set (`bne`, `Bool.not_true`, `Bool.false_and`) matched the OLD arm shape; the new success arm sits under `if addr == alloc.base … if has_switch .zap_dead_pointers …`; `MemWF.killM`'s residual goal is verbatim `⊢ MemWF default` (the `panic!` arm — §4(c)) |
| 6 | `Soundness` | `step_ctx_save`, `stepDischarge_run`, `mapM1_id_defined`, `mapM_save_bridge`, `mapM_full_eval_bridge` → `sorry` | `rfl` failed at :2551 (`lemListZip ps cvals` in the Esave arm — Core_reduction's `List.zip`); `rewrite` pattern `stExceptUndef_foldM ?m th.env (params.zip pes) rs` not found — the call-arg fold is over `lemListZip params pes` (:3033/:3044); `'show' … not definitionally equal` at :3330/:3400/:3454 — `mapM1`/`stExpect_mapM` fold with `lemListFoldr` |
| 7 | `DriverCollapse` | `finalize_done`, `driver2_done`, `step_ctx_run_ws` → `sorry` | `finalize_done` :637 `rfl`: the engine's `dres_stdout := lemListFoldr String.append "" …` vs the statement's `List.foldr String.append ""`; `driver2_done` :701: after `unfold nd_mapM` the `dsimp only [List.map, List.foldr]` no longer exposes the binds (goal shows `runOne (lemListFoldr (fun m m' => nd_bind …) (nd_return []) [ … ]) dstF`); `step_ctx_run_ws` :1076/:1087: the `params.zip pes` pattern again |
| 7 | `EvalClass` | two `show stExpect_mapM f (pe :: pes) = stExpect_bind … from rfl` → `from sorry` (:861, :951) | `Type mismatch rfl` — `stExpect_mapM` folds with `lemListFoldr` |
| 8 | `ProdEntry` | `collect_saves_fib`, `collect_new_fib`, `collect_saves_loop` (`:= rfl` → `sorry`), `loop_labeledAt_production` → `sorry` | `Type mismatch rfl` on `collect_saves (fibProg …) = fibQ …` and on `collect_labeled_continuations_NEW (prodFile …) = fmapAddBy … mainSym … fmapEmpty` — cause §4(a′) (NOT `lemListFoldr`: measured, §4(b) probe) |
| 8 | `Round` | `killM_killed_inv` → `sorry`; `stExpect_mapM_full_eval_kill`'s `from rfl` → `sorry`; `step_ctx_run_kill` → `sorry` (a first attempt stubbed the neighbouring `step_ctx_save_eval_kill` by a line-offset slip; restored from `HEAD` in cycle 9 and it built green untouched) | :789 ×12 `Application type mismatch … Or.inr rfl`: e.g. verbatim `CerbMem.failReason MerrFreeNullPtr loc = Other (MerrUndefinedFree Free_out_of_bound)` and `CerbMem.failReason (MerrOther "attempted to kill with a function pointer") loc = …` — the three-row disjunction is STALE; :5182 `stExpect_mapM` show-rfl; :3521/:3530 the `params.zip pes` pattern |
| 9 | `FibRecExhibit` | `collect_saves_frBody` :180, `collect_new_fr` :189 (`:= rfl` → `sorry`) | `Type mismatch rfl` — §4(a′) |
| 9 | `ProdExhibit` | :251 `show collect_labeled_continuations_NEW (prodFile progAProd) = … from rfl` → `from sorry` | same |
| 9 | `RegionLoopExhibit` | `collect_new_rl` :607 (`:= rfl` → `sorry`) | same |
| 10–11 | `ProdLoopExhibit` | `collect_new_ctr` :591, `col_lrProg` :1347, `col_lrProdSave` :1358 (`:= rfl` → `sorry`); in `collect_new_lrProd`: the `show … from rfl` (:1376) and the closing `rfl` of the "union tower" (:1395) → `sorry` | same; :1395 verbatim `Tactic rfl failed: The left-hand side have st := union_saves { tmp_acc := fmapEmpty, closed_acc := fmapEmpty } (union_saves …` |
| 12 | `DisposeExhibit` | `col_dlProdSave` :1460 (`:= rfl`), the `show … from rfl` :1475, the tower `rfl` → `sorry` | same |
| 12 | `MallocListExhibit` | `collect_new_ml` :1633 (`:= rfl` → `sorry`) | same |

Everything else in those 14 files elaborated unchanged; in particular the
register-order `rfl`s that do NOT go through `collect_saves`
(`prodFile_funs_lookup`, `frFile_funs`, `prodFile_eq_with`,
`prodThread_eq_ctlThread`, `prodRS_labeled`, `procEnv_single`,
`update_env_aux_*`) all still hold by `rfl`.

## 4. Classification of every breakage (the manifests' categories)

Counts are failing DECLARATIONS at the frontier (a declaration with several
error lines counts once); "exported" = the name is an `Audit.lean` pin
(`grep` over the pin list).

| class | failing decls | files | exported statement text must change? | fix size | reason |
|---|---|---|---|---|---|
| (a) `Fmap` representation (LemLib `Std.TreeMap` → inductive `Pmap`) | 3 decls + 3 defs in `EnvLaws` (`fmapLookupBy_addBy_empty`, `symAdd_lookup`, `SymMap`/`symAdd`/`envAdd` + the dead `treeMap_get?_insert_empty`); `symOrd := lemCmpToOrd symCmpK` (removed name) | 1 (`EnvLaws`; 345 consumer references across 19 files unaffected if the API names survive — `lookup_env_head` 79, `envAdd_lookup` 75, `update_env_aux_sym` 39, `fmapLookupBy_addBy_empty` 35, `symFrame_empty` 30, `symAdd_lookup_two` 11, `symAdd_lookup` 8 …) | `SymMap` (a def in the PREMISE of the pinned `symAdd_lookup`/`symAdd_lookup_two`) must be REDEFINED; the lemma statements keep their text | **L** (0.5–1.5 days) | THE LOOKUP LAW `symAdd_lookup` is `Pmap.find? c k (Pmap.add c k' v m) = if … then some v else Pmap.find? c k m` — true only for a BST under a lawful comparator; `Pmap.add` rebalances (`bal`), so the proof needs (i) a BST/ordering invariant on `Pmap` (the new `SymMap`), (ii) `find?`-after-`bal`/`create` preservation, (iii) `add` preserves the invariant, (iv) the comparator lawfulness already proved (`symOrd_eq_compareOn`, `Std.TransCmp` — reusable via the local `lemCmpToOrd`). LemLib ships NO such law (§2). Alternative: REQUEST `Pmap.find?_add`/`Pmap.WF` from lem-lean (they own pmap.ml's port) — a dated request note, and the demo consumes it; the demo can carry its own proof meanwhile |
| (a′) WF-recursive `Pmap.join` blocks definitional computation (NOT in either manifest — NEW FINDING) | 14 registration/`collect_saves` `rfl`s: ProdEntry 4, ProdLoopExhibit 5, DisposeExhibit 3, FibRecExhibit 2 (+ ProdExhibit 1, RegionLoopExhibit 1, MallocListExhibit 1 = **17 sites**, of which 14 are `:= rfl`/`from rfl` and 3 are the closing `rfl` of a union tower) | 7 | NO (all are collapse lemmas/exhibit-local computations; `fib_labeledAt_production`, `*_labeledAt` are pins whose PROOFS `rw` through them — text unchanged) | **M** (1 day) | `collect_saves = fmapUnionBy cmp st.tmp_acc st.closed_acc` (Core_aux.lean:778) and every `Esave` arm union; `fmapUnionBy` → `Pmap.union` → `merge` → `mergeGo` (height-fuelled, structural) → `concatOrJoin` → `Pmap.join`, which is `termination_by sizeOf l + sizeOf r` (LemLib.lean:916–925) — WELL-FOUNDED, so `whnf`/`rfl` cannot unfold it. MEASURED (probe `UnionProbe.lean`): `fmapUnionBy c fmapEmpty fmapEmpty = fmapEmpty := rfl` PASSES (structural arm); `fmapUnionBy c (fmapAddBy c 1 1 fmapEmpty) fmapEmpty = fmapAddBy c 1 1 fmapEmpty := rfl` FAILS; the same by `unfold fmapUnionBy fmapAddBy fmapEmpty Fmap.rep Pmap.union Pmap.merge; simp only [Pmap.height, Pmap.add]; rw [Pmap.mergeGo]; simp [Pmap.height, Pmap.split, Pmap.concatOrJoin, Pmap.join, Pmap.add]` SUCCEEDS — the equation-lemma idiom. Each site becomes a short rewrite script (or a shared `collect_saves` simp set); the towers (6 layers of `col_aux_*` then `rfl`) need the same at the end. Structural alternative: REQUEST lem-lean make `join` height-fuelled like `mergeGo` (then `rfl` returns everywhere) — the cheapest fix if granted; both routes recorded |
| (a″) `fmapElements` order (scout priority (1)) | **0** | — | — | — | MEASURED (probes `OrderProbe.lean`, `ShapeProbe.lean`, `FoldrProbe.lean`): `fmapElements` is ASCENDING under the captured comparator regardless of insertion order (`[(0, 1), (701, 2)]` for both orders of `mainSym = Symbol "" 0 SD_None` / `frSym = Symbol "" 701 SD_None`; `symCmpK mainSym frSym = LemOrdering.LT`); the two insertion orders give DIFFERENT `Pmap` shapes (`N(N(E,0:1,E,h1),701:2,E,h2)` vs `N(E,0:1,N(E,701:2,E,h1),h2)`; `example : m1 = m2 := by rfl` FAILS) so a shape-`rfl` IS order-sensitive; but the registration `Lem_Map_extra.fold` (now `setFold … (fmapToSetBy …)` — Pset in-order, ascending) visits `main` (0) BEFORE `fib` (701), i.e. adds main first, which is exactly the shape `symAdd frSym (frQ) (symAdd mainSym ∅ ∅)` that `collect_new_fr` states — the OLD rep's newest-insert-first enumeration happened to give the same order. The C4 `rfl` is therefore stale for the (a′) reason, not for order; `fmapElements (fmapAddBy defaultCompare (0 : Nat) [Step_done2 v] fmapEmpty) = [(0, [Step_done2 v])] := rfl` (DriverCollapse:697's rewrite) PASSES |
| (b) `lemListFoldr`/`lemListZip` non-reduction | **13**: Step 2 (`valueFromPexprs_cons/_pair`), Soundness 5 (`step_ctx_save` [zip], `stepDischarge_run` [zip], `mapM1_id_defined`, `mapM_save_bridge`, `mapM_full_eval_bridge`), DriverCollapse 3 (`finalize_done`, `driver2_done`, `step_ctx_run_ws` [zip]), EvalClass 2 (`stExpect_mapM` show-rfls), Round 2 (`step_ctx_run_kill` [zip], `stExpect_mapM_full_eval_kill`) | 5 | NO — `finalize_done`/`driver2_done` are pins; their text (`List.foldr String.append ""`) can stay: `LemLibTheorems.lemListFoldr_eq` is propositional and the proof rewrites through it | **S** (half a day) | MEASURED: `lemListFoldr` DOES reduce by `rfl` on a concrete spine even with symbolic elements (`lemListFoldr (·+·) 0 [n, 2] = n + 2 := rfl` passes) — the breakage is in `show`/`dsimp`-shaped proofs that expect the `List.foldr`/`List.zip` CONSTANT (the `foldM_args_bridge` pattern `params.zip pes`, the `stExpect_mapM` bind shape, `dsimp only [List.foldr]`), which now see `lemListFoldr`/`lemListZip`. Fix: `simp only [LemLibTheorems.lemListFoldr_eq, LemLibTheorems.lemListZip_eq]` before the old step (the `Step` touch is the working idiom); `foldM_args_bridge` and friends restated over `lemListZip` or applied after the rewrite. `LemLibTheorems` is importable (§2) |
| (c) `killM` re-mirroring (scout priority (3)) | **4**: Heap 3 (`killM_success`, `killM_success_dynamic`, `MemWF.killM`), Round 1 (`killM_killed_inv`) | 2 | **YES, 1**: `killM_killed_inv` (pin) — its three-row disjunction `UB179a ∨ UB179b ∨ Other (MerrUndefinedFree Free_out_of_bound)` is FALSE at the new arms: `failReason MerrFreeNullPtr loc` (UB_CERB005, under `has_switch .forbid_nullptr_free`), `Other (MerrOther "attempted to kill with a function pointer")`, `Other (MerrOther "attempted to kill with a pointer lacking a provenance")`, `failReason (MerrOutsideLifetime …)` (UB009, no record at the id), `Other (MerrOther "killM: Prov_symbolic …")`, `Other (MerrOther "killM: SW_zap_dead_pointers …")`. `killM_success`, `killM_success_dynamic`, `MemWF.killM`, `MemWF.kill`: statements SURVIVE (their premises — live cell, present record at the base — select the one active arm); proofs re-cut. The rules `kill_atomic`/`free_atomic` (Rules) and `Step.kill` built GREEN untouched: the RULE statements survive verbatim | **S–M** (half a day; the new rows) | The arms and their ORDER now mirror impl_mem.ml:1464–1550: `isDynamic && !dynamicAddrs.contains addr` (the POINTER's address) → dead (dynamic: UB179b; static: `panic!`) → `get? allocId` (`none` → `MerrOutsideLifetime`) → `addr == alloc.base` (→ `zap_dead_pointers` switch → active) else `Free_out_of_bound`. **Semantic note for the proofs (NEW):** the static-kill-of-a-dead-id arm is `panic! "Concrete: FREE was called on a dead allocation"` at type `nd_outcome × MemState`; in the kernel `panic!` IS `default`, so that arm is an ACTIVE outcome `(NDactive (), default)` — `MemWF.killM`'s residual goal is verbatim `⊢ MemWF default`. It is PROVABLE (`default : MemState` has `lastAddress := 0xFFFFFFFFFFFF`, `nextAllocId := 0`, empty maps/lists — every `MemWF` clause holds), so the statement can stay, but the proof must add a `MemWF default` lemma; and `killM_killed_inv`'s "every killed outcome" remains true (the panic arm is not a kill). Consumers never reach that arm (`pointsToCell` implies live), so no rule is affected; this is exactly the Z1 manifest §2 "panic denotes the Inhabited default" caveat, now visible in our proofs. The K3 `free` precondition stands (DECISIONS: the dynamic_addrs outcome) — `killM_success_dynamic`'s `mem_contains_int` bridge now applies at the POINTER address `mc.addr`, which the cell equates with `alloc.base` anyway |
| (d) `casePtrval` `[Inhabited α]` | **0** | — | — | — | 0 demo references to `casePtrval` (grep) |
| (e) `IvMaxAlignment` 16 → 8 (scout priority (4)) | **0** | — | — | — | 0 demo references to `IvMaxAlignment`/std.core/`malloc_proxy`; every concrete address in the demo (`xAddr = 281474976710648`, `errnoAddr = 0xFFFFFFFFFFF8`, MallocList's `281474976710647`) comes from `allocateObject`/`allocateRegion` at the PROGRAM's own alignment, not from the std.core constant. MEASURED: `Exhibit` (`xPtr_eq : xPtr = cellPtr 0 xAddr := rfl`), `ProdEntry`'s `prodMem₀_*` `rfl`s, `MallocListExhibit`'s `ml_budget_bridge` all built green |
| (f) derived `Ord`/`BEq` (55 types → `compare_derived`/`beq_derived`) | **0** | — | — | — | the demo's comparator laws (`EnvLaws.symCmpK_eq`, `lemNatBeq_iff`, `Heap.int_beq_*`, `provenance_beq_refl`) bottom out in `symbol_compare`/`defaultCompare` on `Nat`/`Int`/`String` and CerbMem's own `deriving BEq` on `Provenance` — the `sym` instance lines are byte-identical between the two generated `Symbol.lean` (checked); `decide +kernel` on `symOrd g mainSym = .eq` still discharges |
| (g) `copyAllocId`, device ranges, CerbFS refusals | **0** | — | — | — | 0 demo references to `copyAllocId`/`deviceRanges`/`isWithinDevice`/`fs_*`; `CerbFS.FsState` appears only as a quantified parameter of the production statements; no demo program touches a device address (`loadM`/`storeM` device arms are new `Prov_device` cases — `Heap`'s `provenance_beq_refl` `Prov_device => rfl` still holds; `Rules`/`Soundness` load/store proofs built green) |
| (h) anything else | **0** measured | — | — | — | No renamed constant the demo cites; `CerbMem` `import Std.Data.TreeMap` keeps the demo's `Std.TreeMap` proofs over `MemState.allocations`/`bytemap` valid (Heap 8 sites, Exhibit 1, ProdEntry 1 — all green); the `Constraints.concat0 → concat` field rename has 0 demo hits; `update_env_aux_spec`'s fuel-arm `rfl` and every `pot`/`esize` bound untouched |

Totals (DERIVED from the touch table): 41 failing declarations
(a: 3 + 3 defs; a′: 17; b: 13; c: 4; +1 slip corrected) in 12 files.
Exported-statement TEXT changes required: 1 (`killM_killed_inv`), plus the
`SymMap` definition change (a pinned premise's referent). The other 33
touched declarations keep their statements.

## 5. Exported-statement impact list

Against `docs/2026-09-03_f1-signatures-post.txt` (the F1 snapshot; pins by
name in `Audit.lean`):

| statement | pin? | text | proof |
|---|---|---|---|
| `killM_killed_inv` (Round) | yes | **MUST CHANGE**: add the new refusal rows (or restate as "killed ⇒ state untouched ∧ reason ∈ the engine's kill-reason set", enumerated) | re-cut over the new arms |
| `SymMap` (EnvLaws, `def`) — premise of the pinned `symAdd_lookup`, `symAdd_lookup_two`, `procDecls_symMap`, `symMap_empty`, `SymMap.add` | (referent of a pin) | **MUST CHANGE** (representation): `∃ p : Pmap sym β, m = Fmap.mk symCmpK p ∧ <BST invariant>` — the lemma texts keep their spelling | THE LOOKUP LAW re-proved (§4(a)) |
| `symAdd`, `envAdd` (EnvLaws, `abbrev`) | (appear in pinned statements) | body loses the `instBEqOfMapKeyType` argument (`fmapAddBy` has no `[BEq]` binder now); spelling in statements unchanged | — |
| `MemWF.killM`, `killM_success`, `killM_success_dynamic`, `MemWF.kill` (Heap) | yes | UNCHANGED | re-cut; `MemWF default` lemma for the panic arm |
| `finalize_done`, `driver2_done` (DriverCollapse) | yes | UNCHANGED (keep `List.foldr String.append ""`; equal via `lemListFoldr_eq`) | rewrite through `LemLibTheorems.*` |
| `kill_atomic`, `free_atomic`, `wps_kill*`, `wpt_kill*`, `Step.kill*`, `alloc_create_kill_wps`, `complete_kill_op`, `step_ctx_kill_*` | yes | UNCHANGED — built GREEN untouched | — |
| the nine production statements (`exhibitA_prod`, `fib_labeledAt_production`, `fib_certified_production`, `counter_loop_certified_production`, `list_reverse_certified_production`, `dispose_list_certified_production`, `region_loop_certified_production`, `malloc_list_certified_production`, `fib_rec_certified_production`) + `prod_run_eqJ`, `fib_rec_certified` | yes | UNCHANGED (their modules elaborated with the stubs beneath them; nothing in their text names a changed shape) | depend on the (a′) registration lemmas and (a) lookup law |
| every rule and collapse not named above (Rules, Wps, Wpt, Soundness minus the 5, Round minus the 3, Adequacy, TotalAdequacy, API) | yes | UNCHANGED — built green untouched | — |

## 6. Recommended slice plan (ESTIMATE; one change at a time)

The re-pin is ONE forced-semantics-change slice, but its internals split
into commits that can be fast-gated separately, in dependency order (each
commit builds green — no `sorry` ever lands):

1. **Pin + manifest (mechanical, minutes).** `semantics-pin.env` →
   the target; `rm -rf .cerberus-ws`; `setup-cerberus-dep.sh`; in
   `cerberus-heaplang/`: `capped lake update LemLib` (moves ONLY the
   LemLib entry; verify the manifest diff is those 3 lines). Cannot be a
   green commit on its own (Step fails) — lands with 2–3 below, or as the
   first of a stacked series that is merged together.
2. **Class (b) — the `lem*` rewrites (S; same commit as 1 or next).**
   `import LemLibTheorems` where needed; `simp only [LemLibTheorems.
   lemListFoldr_eq, LemLibTheorems.lemListZip_eq]` at the 13 sites (Step 2,
   Soundness 5, DriverCollapse 3, EvalClass 2, Round 2); restate/re-apply
   `foldM_args_bridge` over `lemListZip` (or rewrite before applying).
   Statements unchanged. Note the two-instance gotcha (`rw` only rewrites
   the head instantiation; `simp only` is the idiom).
3. **Class (c) — killM (S–M; separate commit).** `MemWF default` lemma;
   re-cut `killM_success`/`_dynamic`/`MemWF.killM`; RESTATE
   `killM_killed_inv` with the new rows (the one exported-text change —
   name it in the commit message and in the signature snapshot delta);
   header prose in Heap/Rules/Step/Round citing `CerbMem.lean:1555-1580`
   and "three engine reasons" updated (the cites are stale: killM is now
   :1912–1968). Independent of 4–5 (Heap does not import EnvLaws).
4. **Class (a) — the lookup law (L; separate commit, the risk item).**
   Redefine `SymMap` with a BST invariant; prove `Pmap.find?` after
   `create`/`bal`/`add`; `SymMap.add`; `symAdd_lookup`; `fmapLookupBy_addBy_empty`
   (a one-node tree: direct). Delete `treeMap_get?_insert_empty`, the
   `Std.TreeMap` prose; keep `symOrd_eq_compareOn`/`TransCmp` (transport
   through a local `lemCmpToOrd`). Everything downstream (345 references)
   should elaborate unchanged if the API names survive — measured: with
   the law `sorry`-stubbed and the API kept, all 19 consumer files built.
   **Decision point for the orchestrator:** carry our own `Pmap` law, or
   REQUEST it from lem-lean (a dated request note; they own pmap.ml's
   port and its `LemLibTest` invariants are already the right shape) —
   recommendation: request AND carry a local proof now (the request is
   the durable home; the local proof unblocks the re-pin and is deleted
   when theirs lands).
5. **Class (a′) — the registration computations (M; separate commit).**
   Either (i) a shared `simp` set / `collect_saves_*` equation lemmas
   through `Pmap.join`'s equation lemmas (the probe's idiom) at the 17
   sites, or (ii) request lem-lean make `Pmap.join` height-fuelled like
   `mergeGo` (mirrors pmap.ml equally; restores `rfl` everywhere; also
   `Pset.join`, LemLib.lean:382–391). Recommendation: request (ii) as the
   structural fix; do (i) only if the re-pin cannot wait. Depends on 4
   only through `fmapLookupBy_addBy_empty` (used right after each
   registration `rfl`).
6. **Snapshot + docs (same commit as the last code commit).** Signature
   snapshot pre/post; the delta must be exactly: `killM_killed_inv`'s
   type, `SymMap`'s type (and any `.eq_def` auxiliaries showing the pin
   through); shop-window prose (README "pin" line, ARCHITECTURE cites,
   DriverCollapse/Heap headers); `cerberus-heaplang/docs/2026-09-03_repin-<name>-notes.md`
   per the fuel re-pin's template; `semantics-pin.env` history paragraph.
7. **FULL gate** (`scripts/test_unit.sh`), then the unconditional
   pre-merge audit ask (the trust base moved: new semantics tree, new
   LemLib, one exported statement restated).

Sizing (ESTIMATE): 1–3 half a day; 4 one to one-and-a-half days (the only
place a grind could start — if `Pmap.find?_add` resists, STOP and file the
lem-lean request rather than brute-force the AVL cases); 5 one day by
route (i), an hour by route (ii) once granted; 6–7 half a day. Total 2.5–4
days of worker time.

## 7. What did NOT change for us (confirmed from the tree and the range)

- `lean_frontend/CerbND.lean`, `lean_frontend/CerbFuel.lean`: NO diff in
  `f95ef8d..de2fbf1`. At the pin: `def fuelExhaustedKill` (CerbND.lean:80),
  `def ndDefaultFuel : Nat := CerbFuel.driverFuel` (:85), `def drive_lemFuel`
  (:450), `theorem drive_wrapper_defeq : drive = drive_lemFuel
  CerbFuel.driverFuel := rfl` (:467), `def driverFuel : Nat := 100000000`
  (CerbFuel.lean:71) — all verbatim as at the fuel re-pin.
- `frontend/model/driver.lem`, `nondeterminism.lem`, `core_run.lem`,
  `core_run_aux.lem`: NO diff (no `.lem` changed at all). In the generated
  `Driver.lean`, the lines defining `initial_driver_state` (:483, `(_lemSupply_fresh_int
  : Nat) (file1 …) (fs_state2 : CerbFS.FsState) : ((driver_state) × Nat)`),
  `drive` (:555), `driver2`, `drive_nonmemory_steps_aux2` and their
  `_lemFuel` workers are UNCHANGED (`diff` of the two generated `Driver.lean`
  has 0 lines mentioning them; its 77 changed lines are the `step_kind`
  derived instances, `Pset` types in the fs-op lets, and one local `let`
  rename `update2 → update1`). `Nondeterminism.lean`'s diff is `nd_mapM`/
  `nd_sequence_` → `lemListFoldr` and the `Constraints.concat0 → concat`
  field; the `nd_bind`/`liftND`/`liftAction` fuel arms are untouched.
- `scripts/setup-cerberus-dep.sh --check` on the new tree, verbatim (rc 0):

  ```
  == setup-cerberus-dep: A ok: workspace at pinned commit
  == setup-cerberus-dep: B ok: primed (de2fbf1bd3001491c741f6a1b0b7d36412db3be5 2026-09-03T23:07:26Z)
  check_lem_sync: lean OK (src 4f2e089b39d5b371973513b3350f81d1b89871976f77df9ba4a25da3421d0c54, gen 41781645302ba346ab11977956c6eb2e82f5de95678bc3d1091b1ae9e9eab3f8)
  == setup-cerberus-dep: B ok: Lean lem-sync stamp verified in the workspace
  == setup-cerberus-dep: C ok: 23 hand-written seams byte-identical to the pin
  == setup-cerberus-dep: DONE. Lake consumes /home/dev/projects/cerberus-lean-proj/refined-cerberus/worktrees/repin-scout2/.cerberus-ws/lean_frontend as a path dependency.
  ```
  The content guard (section B's diff branch) was NOT exercised (source ==
  pin); section C ran in both modes and passed.

## 8. Risks

- (α) The `Pmap` lookup law (class a) is the one item that could grind:
  AVL rebalancing proofs are classical but case-heavy. Guard: state the
  invariant as "sorted `bindings` under the comparator" and prove
  `find?` through `bindings` membership, or hand it to lem-lean. Never
  bulk `decide` over trees.
- (β) `Pmap.join`'s WF recursion also sits under `fmapDeleteBy`/`remove`,
  `fmapUnionBy`, `Pset.union/remove` — any FUTURE demo proof that computes
  an engine map through them by `rfl` will hit (a′); the structural
  lem-lean fix (height fuel) removes the class for good. Say so in the
  request.
- (γ) The `panic!`-is-`default` reading of `killM`'s dead-static arm is
  a kernel-level fact about the mirror: a hypothetical exported statement
  quantifying over ALL kills would have to carry it. Today none does
  (every kill/free rule presupposes a live cell); the typed-failure
  outcomes pass scheduled on their side (Z1 manifest §2) will remove the
  arm's `Inhabited` semantics — re-check `MemWF.killM` at that re-pin.
- (δ) If cerberus-lean moves again before the re-pin ("lighter fixes"),
  re-measure ONLY: the seam list (`handwritten_copy.manifest`), the
  `killM` arm text (class c is a text-shape dependency), `Core_aux`'s
  `collect_saves`, and the LemLib rev (if lem-lean lands the `join`
  request, class a′ evaporates). The class (b) idiom and the class (a)
  law are pin-independent.
- (ε) The demo's manifest URL for LemLib flips to `OathTech` — both
  spellings are redirected; no network implication in-sandbox.

## 9. What was NOT measured / not done

- No fix was attempted (every touch reverted); the (a) law and the (a′)
  rewrite scripts were NOT written — their sizes are estimates informed
  by the two probes (`UnionProbe.lean`: the equation-lemma route closes a
  one-element union; `ShapeProbe.lean`: insertion order changes the tree).
- `Audit.lean` itself was not run to a verdict at the new pin (it cannot
  be, with stubs beneath it); the pin COUNT and the sweep totals after the
  re-pin are the re-pin slice's to record.
- The `.repin-logs/` scratch (12 build logs, 4 probe files, the check
  transcript) is EPHEMERAL per the container rule and is deleted at slice
  end; every line quoted above is in this record. The worktree's
  `.cerberus-ws` (primed at `de2fbf1bd`) and the demo's `.lake` (dep cone
  built at LemLib `3c88f0d`) are left in place for the re-pin worker —
  note the `.lake/packages/LemLib` is at `3c88f0d` while the committed
  manifest still says `045dcb0`: the worker's first `lake update LemLib`
  re-aligns them (or Lake re-clones; either way 1 s).
- `scripts/test_unit.sh` was not run (the build is red by design).
- No `sorry`/`native_decide` grep of the new generated tree beyond the
  scout's own touches; the fuel re-pin's admissions census (`grep -rn
  sorry generated/`: comment text only) was not repeated.
