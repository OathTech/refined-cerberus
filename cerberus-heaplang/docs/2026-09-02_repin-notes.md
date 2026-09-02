# 2026-09-02 — THE RETIREMENT RE-PIN (alloc arc P7 / restart Slice 1)

Worker record. Provenance: [USER 2026-09-02] (resume note, Slice 1:
re-pin to the cerberus-lean effect-retirement head and delete the
`runEffectful` boundary); [AGENT 2026-09-02] coordinator adjudication
of the C1 tag-environment change (option (a), verbatim in
`docs/DECISIONS.md`, same date). Quoted outputs are verbatim; tallies
marked DERIVED are grep/diff-derived.

## 1. The pin move

`scripts/semantics-pin.env`: `58ec50779f036da1794c440d215d41a755027382`
→ `ddcfc919972a31bc43a0454e6b2e76a19e6c4594` (cerberus-lean mainline
`mdd/cerberus-lean` head; `git rev-list --count` = 38 commits). The
delta on the primed code-bearing paths, verbatim
(`git -C cerberus-lean diff --stat 58ec507..ddcfc91 -- frontend
lean_frontend/generated lean_frontend/native lean_frontend/lakefile.toml`):

```
 frontend/model/cabs_to_ail.lem        |  22 +++++--
 frontend/model/cabs_to_ail_effect.lem |  32 ++++++++--
 frontend/model/core_run_aux.lem       |  17 +++--
 frontend/model/ctype_aux.lem          |  28 ++++----
 frontend/model/driver.lem             |  20 +++++-
 frontend/model/mem.lem                |  27 ++++++++
 frontend/model/mini_pipeline.lem      |  50 +++++++++------
 frontend/model/symbol.lem             |  26 ++++++--
 frontend/model/translation.lem        | 116 ++++++++++++++++++++++++----------
 frontend/model/translation_effect.lem |  83 +++++++++++++++++++-----
 lean_frontend/lakefile.toml           |  20 +++---
 lean_frontend/native/debug.c          |  19 ------
 lean_frontend/native/fresh_int.c      |  45 -------------
 lean_frontend/native/tags.c           |  80 -----------------------
 14 files changed, 330 insertions(+), 255 deletions(-)
```

(`generated/` is gitignored upstream: its delta shows through the
workspace re-prime, not git. File-level: 27 generated modules differ
between the old and new primed trees, two (`Core_unstruct*.lean`) are
gone; most differences are the new lem emitter's re-emission — the
signature-bearing ones are listed in §3.)

The 38 commits: the effect-retirement arc (design note R1–R3.1, S0
scan, C1 adoption `0780445a6` + rebaseline, C2 deletion `895f9ada6`
lem pin → LemLib `045dcb0d57a171eb4fb3a6eb5abe288c227270ce`, the C2
ratchet), the trust-basket slice (CerbFS fail-closed, driver
freshness stamps, `--cabs-json` parse-only), the gcc second-oracle
lane baselines, and `capped` cgroup-direct mode. Records upstream:
`lean_frontend/docs/2026-08-31_effect-retirement-design.md`,
`2026-08-31_C1-change-manifest.md`, `2026-09-01_C1-adoption-record.md`,
`2026-09-01_C2-ratchet-record.md`.

LemLib moved in both Lake manifests (`lake-manifest.json`,
`cerberus-heaplang/lake-manifest.json`) from `861ed814f178a40a…` to
`045dcb0d57a171eb…` via `scripts/capped lake update LemLib` — the
dependency's own manifest pins it there; the diff is rev/inputRev only.

## 2. The re-prime (transcript tail, verbatim)

`rm -rf .cerberus-ws` (this worktree's own) then
`scripts/setup-cerberus-dep.sh` — the source checkout sits exactly at
the pin, so the content guard was not consulted:

```
== setup-cerberus-dep: A: cloning /home/dev/projects/cerberus-lean-proj/cerberus-lean -> …/heaplang-alloc-arc/.cerberus-ws @ ddcfc919972a31bc43a0454e6b2e76a19e6c4594
…
== setup-cerberus-dep: B: priming lean_frontend/generated
== setup-cerberus-dep: B: priming lean_frontend/native
== setup-cerberus-dep: B: priming lean_frontend/.lake
check_lem_sync: lean OK (src f4c0096697fb68c508acbe35423ed0fce77c6988ceafcaffe772924358e8a624, gen 6c2ae2041cceb0aed61cae04917144131fe96940e2aec6213d43b13b9d8fd5e7)
== setup-cerberus-dep: DONE. Lake consumes …/.cerberus-ws/lean_frontend as a path dependency.
```

`--check`: `A ok: workspace at pinned commit` / `B ok: primed
(ddcfc919972a31bc43a0454e6b2e76a19e6c4594 2026-09-02T01:54:34Z)`.
`grep -rn runEffectful .cerberus-ws/lean_frontend/generated
.cerberus-ws/lean_frontend/native` → empty (rc 1). LemLib at the pin
mentions the name only in two comments.

## 3. What changed shape in the semantics (measured old vs new tree)

The entry constructors (Driver.lean:446 / Core_run_aux.lean:400-409):

| Constant | old | new |
|---|---|---|
| `initial_driver_state` | `file → fs_state → driver_state` | `(sup : Nat) → file → fs_state → driver_state × Nat` |
| `initial_core_run_state` | `xs → core_run_state` | `(sup : Nat) → xs → core_run_state × Nat` (`.1` has `sym_supply := sup`, `.2 = sup + 1`) |
| `initial_driver_state_with`, `initial_driver_state_given`, `initial_core_run_state_given` | — | NEW pure builders (not used here: the statements quantify over the shipped entry) |

The CerbMem memory functions used by this package (C1 reader_consumer
threading — an explicit leading tag-definition argument), verbatim
signature lines old → new:

```
alignofIval (ty : ctype) : IntegerValue
alignofIval (tagDefs : TagDefs) (ty : ctype) : IntegerValue
allocateObject (_ : Nat) (pref : prefix0) (alignIv : IntegerValue) …
allocateObject (tagDefs : TagDefs) (_ : Nat) (pref : prefix0) (alignIv : IntegerValue) …
arrayShiftPtrval (pv : PointerValue) (elemTy : ctype) (iv : IntegerValue) : PointerValue
arrayShiftPtrval (tagDefs : TagDefs) (pv : PointerValue) (elemTy : ctype) (iv : IntegerValue) : PointerValue
isAtomicMemberAccess (alloc : Allocation) (lvalueTy : ctype) (addr : Int) : Bool
isAtomicMemberAccess (tagDefs : TagDefs) (alloc : Allocation) (lvalueTy : ctype) (addr : Int) : Bool
loadM (loc : CerbLocation.Loc) (ty : ctype) (pv : PointerValue) : memM (Footprint × MemValue)
loadM (tagDefs : TagDefs) (loc : CerbLocation.Loc) (ty : ctype) (pv : PointerValue) : memM (Footprint × MemValue)
memValueToBytes (funptrmap : Funptrmap) (val_ : MemValue) : …
memValueToBytes (ambient : TagDefs) (funptrmap : Funptrmap) (val_ : MemValue) : …
reconstructValue (unionmap : List (Int × identifier)) …
reconstructValue (ambient : TagDefs) (unionmap : List (Int × identifier)) …
reconstructValue_lemFuel (lemFuel : Nat) …
reconstructValue_lemFuel (lemFuel : Nat) (ambient : TagDefs) …
sizeofCtype (cty : ctype) : Nat
sizeofCtype (ambient : TagDefs) (cty : ctype) : Nat
storeM (loc : CerbLocation.Loc) (ty : ctype) (isLocking : Bool) (pv : PointerValue) (mv : MemValue) : memM Footprint
storeM (tagDefs : TagDefs) (loc : CerbLocation.Loc) (ty : ctype) (isLocking : Bool) (pv : PointerValue) (mv : MemValue) : memM Footprint
```

(`TagDefs` is CerbMem's private abbreviation of `CerbTags.TagDefsMap =
Fmap sym (CerbLocation.Loc × tag_definition)`; this package writes
`CerbTags.TagDefsMap`.) In Driver.lean, `action_request_sequential2`,
`perform_action_request2` and `prepare_main_args` gained the
`_lemReader_tagDefs` reader binder; `drive`/`driver2`/`step_ctx`/
`finalize` are unchanged. CerbTags' globals (`tagDefs ()`,
`set_tagDefs`, `with_tagDefs`) are gone (never referenced here).
DERIVED census before the fix: 761 lines in `CerberusHeapLang/*.lean`
referenced one of these names (Heap 204, Wps 134, Wpt 121, ListRev 54,
TreeRot 48, Soundness 30, Exhibit 26, Rules 25, ProdLoopExhibit 21,
DriverCollapse 20, Step 20, ArrayExhibit 18, ProdEntry 14, Struct 11,
ProdExhibit 4, Round 4, Alloc 3, Adequacy 2, LoopExhibit 2).

## 4. The first build (the stop-and-report point)

At the new pin, `CerberusHeapLang.Step` failed with ten errors of one
class — e.g.

```
error: CerberusHeapLang/Step.lean:834:40: Application type mismatch: The argument
  loc
has type
  CerbLocation.Loc
but is expected to have type
  CerbMem.TagDefs✝
in the application
  CerbMem.storeM loc
```

— the reader_consumer change, not a rename: a design choice about how
the logic threads the tag environment. Reported; adjudicated as
option (a) (DECISIONS.md, [AGENT 2026-09-02]); resumed.

## 5. Option (a) as implemented — the tag environment threaded

- **Mirror (Step.lean).** `Step.store/load/create` discharge against
  `CerbMem.storeM M.tagDefs …` / `loadM M.tagDefs` /
  `allocateObject M.tagDefs 0 …` — the engine's reader binder
  (`action_request_sequential2 _lemReader_tagDefs`, Driver.lean:273)
  mirrored by the context field. The pure evaluator gains the
  environment as its first argument (`evalPexpr tds ext ρ`,
  `evalPexprs`, `evalArrayShift tds ty` ↔ `(CerbMem.arrayShiftPtrval
  _lemReader_tagDefs)`, Core_eval.lean:145); the rules use `M.tagDefs`.
- **Heap layer (Heap.lean).** Explicit `(tds : CerbTags.TagDefsMap)`,
  first explicit parameter (after the instance binder), on every
  layout-dependent predicate and engine-seam lemma: `decodeCell`,
  `cellLoadTrap`, `StorableAt`, `CellCoh`, `cellsDisjoint`, `Coh`,
  `storeM_success`, `loadM_success`, `Coh.store`, `Coh.store_interior`,
  `metaOf`, `CellCoh.toMetaCoh/ofParts`, `loadM_at`, `storeM_at`,
  `freshBase_*`, `allocateObject_success`, `advanceCursor`, `PlanFits`
  (+ lemmas), `decIndep`, `pointsToView`, `cellOwn`, `pointsToCell`
  (+ `_iff`s, split/join/view laws), `allocCap` (+ intro/weaken),
  `cellOwn_cellCoh`, `CohG.create`, `isAtomicMemberAccess_false(')`.
  Representative before/after:
  ```
  def pointsToCell [SpikeGS hlc GF] (pv : CerbMem.PointerValue) (dq : DFrac)
      (ty : ctype) (bs : List CerbMem.AbsByte) : IProp GF
  def pointsToCell [SpikeGS hlc GF] (tds : CerbTags.TagDefsMap) (pv : CerbMem.PointerValue) (dq : DFrac)
      (ty : ctype) (bs : List CerbMem.AbsByte) : IProp GF
  ```
  Notation: `pv ↦c[tds]{dq} ty ; bs`, `pv ↦c[tds] ty ; bs`.
- **The state interpretation computes no layout** (the worker's
  implementation refinement, recorded in the DECISIONS entry): `Iris`
  synthesizes `StateInterp Mem Empty GF` by type class, so it cannot
  take `tds` as an explicit argument. `MetaCell` therefore records the
  allocation's `size : Nat` as ghost data (the engine's own
  `Allocation.size`, registered by `allocateObject`; Caesium's
  `allocation` start/len shape), `MetaCoh` pins `al.size = mc.size`,
  `metaDisjoint` is size-based, and the assertions pin `size =
  sizeofCtype tds ty` (`metaOf tds c := ⟨c.addr, c.ty, sizeofCtype tds
  c.ty⟩`). `CohG`, `SpikeState`, `instIrisGS` are unchanged in shape.
- **Rules generic in `M`** (Rules/Wps/Wpt): `M.tagDefs` everywhere;
  representative:
  ```
      (hst : StorableAt ty mv) :
      pointsToCell (GF := GF) pv (.own 1) ty bs ⊢
        WP … {{ w, ∃ fp, ⌜…⌝ ∗ pointsToCell pv (.own 1) ty (CerbMem.memValueToBytes [] mv).2 }}
      (hst : StorableAt M.tagDefs ty mv) :
      pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ⊢
        WP … {{ w, ∃ fp, ⌜…⌝ ∗ pointsToCell M.tagDefs pv (.own 1) ty (CerbMem.memValueToBytes M.tagDefs [] mv).2 }}
  ```
  (`wp_store`, Rules.lean:177). Heap-level lemmas in Rules/Adequacy
  that have no context (`pointsToCell_iff`, `loadedVal`, `Sat`,
  `MetaByteOf`, `LaunchCoh`, `spikeCells_alloc`, `launchResources`,
  `spike_step_adequacy(_alloc)`, `cellsOwn_*`, `cells_readout`,
  `bigSepM_own_disjoint`) take `(tds)` explicitly; `Sat.mono`,
  `Sat.union_left`, `MetaByteOf.cohG`, `LaunchCoh.cohG` take it
  implicitly (determined by their hypotheses).
- **Soundness/DriverCollapse.** `dischargeStep (tds) aid rs σ` — the
  driver's reader; `outcomesU M …` passes `M.tagDefs`, the frozen
  `engineOutcomes` passes `spikeCtx.tagDefs`, `engineOutcomesP p rs`
  passes `(procCtx p rs).tagDefs`, `driveJ` passes `(rsCtx rs).tagDefs`.
  The `step_ctx`-level theorems quantified over `tds` already; the
  evaluator bridges (`step_eval_bridge`, `aux2_bridge`,
  `full_eval_bridge`, `eval1_bridge`) had `tds` bound AFTER the
  evaluator hypothesis — it now must come before it (`evalPexpr tds …`),
  so it is a leading implicit `{tds}` and the trailing explicit
  argument is gone (call sites drop it; the ∀-quantified conclusions
  lose the inner `∀ tds`). The `ars_*_active` driver-discharge lemmas
  take `{tds}`; `prod_loop_done`'s statement keeps the driver at
  `fmapEmpty` as before.
- **Adequacy.** `Sat (tds) σ m := Coh tds σ m`; `SemTriple`,
  `ProvenTriple`, `semantic_triple_sound`, `semantic_frame` are
  UNCHANGED in statement (they are at the fixed `spikeCtx` profile and
  use `spikeCtx.tagDefs` internally); `engine_adequacyU(_alloc)` at
  `M.tagDefs`, `spike_engine_adequacy(_alloc)` at `spikeCtx.tagDefs`,
  `engine_adequacyJ` at `(procCtx p rs).tagDefs`; `drive`/`driveJ`/
  `driveU` unchanged.
- **Clients (the exhibits and production modules).** Footprints are
  stated at the program's environment `fmapEmpty` (what the shipped
  `drive fmapEmpty` passes) or, where a statement is literally at a
  profile context, at that context's `.tagDefs`. To make the clients'
  `fmapEmpty` meet the rules' `M.tagDefs` inside the proof mode,
  `spikeCtx`/`procCtx`/`rsCtx` are `@[reducible]` (their `.tagDefs`
  projections unfold to `fmapEmpty` under reducible-transparency
  matching). Client-level lemmas generic in `M` (the node/tree/struct
  field clients, `wps_arr_elem_load`, `progA_wpt`, `progAProd_wpt`,
  the Alloc clients) are at `M.tagDefs`; their pure layout facts
  (`structTy_size`, `nodeTy_size`, `treeTy_dec_indep`, `node_store_kit`,
  `seven_reconstruct`, …) are generalized over an implicit `{tds}`
  (all still `rfl`/`decide` — the integer/array/pointer arms never read
  the environment). Byte-image constants gained the environment
  (`sevenBytes/fiveBytes/sixBytes (tds)` in Rules; `imgOf`,
  `nodeValDec`, `nodeNextDec`, `treePtrDec`, `intUndefBytes`, `ψX`,
  `ψA`); the production-image facts of ProdLoopExhibit
  (`lrBuilt*`, `nodeUndefBytes`, `nodeTy_decIndep_undef`) stay at
  `fmapEmpty`. Rules' example constants: `seven_encodes` was already
  stated at `fmapEmpty`; `sevenBytes fmapEmpty` etc. are the demo's
  instantiation (R-07 movers).
- **`DriverDoneAt`, `wpt_driver_done(_alloc)`** are unchanged (their
  statements fix the driver's table).

Statement-shape summary (DERIVED): 120 declarations carry a `tds`
binder (`grep -c` over `(tds : CerbTags.TagDefsMap)` /
`{tds : CerbTags.TagDefsMap}` at declaration heads: Heap 48, Adequacy
16, ListRev 17, Soundness 12, Step 10, ProdEntry 10, TreeRot 9, Rules
8, Struct 5, ProdLoopExhibit 5, Exhibit 4, Alloc 3, ProdExhibit 3,
Array 2, Audit 1 — the last is the export list's file, counted by the
same grep); 16 production-entry declarations carry `(sup : Nat)`.
Changed lines per module (part-1 commit `0f1558a`, `git diff --stat
HEAD~1 HEAD -- cerberus-heaplang/CerberusHeapLang`, DERIVED): Heap 612,
Wps 432, Wpt 358, Soundness 253, ListRev 240, TreeRot 232,
ProdLoopExhibit 221, Adequacy 196, ProdEntry 167, Rules 165, Struct
164, Step 161, Exhibit 156, DriverCollapse 92, Audit 91, Array 90,
LoopExhibit 88, ProdExhibit 58, TotalAdequacy 38, Alloc 28, Fib 24,
ProdLoop 14, Round 10 — 23 files, 1967 insertions, 1923 deletions.

No statement was weakened; no axiom, `sorry`, or non-kernel method was
introduced (the in-build sweeps below are the evidence).

## 6. The production entry restated ([USER]: quantify over the shipped entry)

Sixteen declarations gain `(sup : Nat)` as their first explicit
parameter and are stated over the shipped constructor's `.1`
projection: ProdEntry `prodPostGlobals`, `prodEntryState`,
`drive_after_setup`, `prod_run_eq`, `sem_triple_prod`, `prod_run_eqJ`,
`fib_labeledAt_production`, `loop_labeledAt_production`,
`counter_loop_certified_registration`; ProdExhibit
`progAProd_labeledAt`, `exhibitA_prod`; ProdLoopExhibit
`fib_certified_production`, `ctrProd_labeledAt`,
`counter_loop_certified_production`, `lrProd_labeledAt`,
`list_reverse_certified_production`. Representative before/after
(`exhibitA_prod`, ProdExhibit.lean:244):

```
theorem exhibitA_prod (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFile progAProd) args)
          (initial_driver_state (prodFile progAProd) fs) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = sevenVal ∧
      (∃ i a : Int, CellCoh dst'.layout_state i ⟨a, intTy, sevenBytes⟩) ∧ …
theorem exhibitA_prod (sup : Nat) (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFile progAProd) args)
          ((initial_driver_state sup (prodFile progAProd) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = sevenVal ∧
      (∃ i a : Int, CellCoh fmapEmpty dst'.layout_state i ⟨a, intTy, (sevenBytes fmapEmpty)⟩) ∧ …
```

The `LabeledAt` ties are stated at `(initial_core_run_state sup
(collect_labeled_continuations_NEW (prodFile …))).1` and their
`.labeled = collect …` steps stay `rfl` (`LemLib.supplySplit s = (s,
s+1)` reduces, so `.1` computes to `initial_core_run_state_given sup
…`). The setup-collapse `rfl`s (`drive_after_setup`) went through
unchanged. `sup` is never read by any proof.

## 7. Audit.lean

`boundaryAxioms`, `boundaryModules`, `boundaryExports` deleted; the
nine former boundary exports moved into `trioExports`; the exhaustive
sweep bounds every theorem of every module by the trio; the
banned-axiom sweep is unchanged; header rewritten (the retirement, the
pin commit, Driver.lean:446 / Core_run_aux.lean:406). Summary lines
at the full gate, verbatim:

```
info: CerberusHeapLang/Audit.lean:122:0: CerberusHeapLang export pins: 62 trio-exact
info: CerberusHeapLang/Audit.lean:122:0: CerberusHeapLang axiom sweep: 1115 theorems bounded by the trio
info: CerberusHeapLang/Audit.lean:122:0: CerberusHeapLang banned-axiom sweep: 1948 constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
```

(Before: 62 pins as 53 trio-exact + 9 trio+runEffectful-exact; the
theorem/constant counts moved with P3.5 and this slice's helper
reshaping — both sweeps are exhaustive by construction, not
enumerated.)

## 8. Docs touched

`cerberus-heaplang/README.md` (trust story, take-on-faith, divergence
register, expected tail, census, module table),
`cerberus-heaplang/docs/WALKTHROUGH.md` (§4 tier 1, §5 production
statement, §7 build/census), `docs/2026-09-01_alloc-arc-plan.md` (R-11
CLOSED), `docs/DECISIONS.md` (the two [AGENT] entries),
`RefinedCerberus/Audit.lean` header, `scripts/semantics-pin.env`.
Dated records elsewhere untouched. `grep -rn runEffectful` over the
worktree (excluding `.cerberus-ws`, `.lake`, dated docs) leaves only
historical mentions ("former", "retired") in Audit/ProdEntry/
ProdLoopExhibit headers, README, WALKTHROUGH, DECISIONS and the pin
file's comment — no live reference.

## 9. Borderline observations (recorded, not investigated)

1. **Primed oleans did not replay.** After the re-prime, the root
   build rebuilt the semantics cone reachable from `CerbMem` (~60
   modules, 2:20) and the cerberus-heaplang build rebuilt the rest,
   instead of replaying the primed `.lake` — a trace mismatch between
   the primary checkout's build and this workspace (cause not
   investigated; cheap here).
2. **`native/native/` nesting in `setup-cerberus-dep.sh`** (pre-existing):
   `cp -a "$SRC/$p" "$WS/$p"` onto the clone's existing `native/`
   (tracked `md5.c`) nested the primed objects one level down. Inert
   for the library build (only the `lean_exe`s link `native/md5.o`).
   FIXED (two lines: `mkdir -p "$WS/$p"` + `cp -a "$SRC/$p/." "$WS/$p"`),
   verified on a scratch workspace (native/ flat: `debug.o fresh_int.o
   md5.c md5.o tags.o`; generated/ listing identical to the live
   workspace). The live `.cerberus-ws` was primed by the old form and
   left as is (its `native/native/` is inert; `--check` green).
3. The primary checkout's `native/` still carries stale `debug.o`,
   `fresh_int.o`, `tags.o` for sources deleted upstream (they ride
   into the prime; inert).
4. The one `fmapEmpty` inside logic modules: Rules' example constants
   (`sevenBytes fmapEmpty` in the `exhibit`/`exhibitC_triple` examples,
   next to the pre-existing `seven_encodes` at `fmapEmpty`), Adequacy's
   pre-existing `step_ctx fmapEmpty … spikeFile fmapEmpty` spellings of
   the frozen profile, and DriverCollapse's driver at `fmapEmpty` — all
   pre-existing profile facts, none new.

## 10. Ephemeral material

The worker's scratch (`.repin-scratch/`: transcripts, build logs,
copies of the OLD pin's generated `CerbMem/Core_run/Core_run_aux/
Driver/CerbTags/Ctype_aux/Core_aux.lean`) is deleted at slice end per
the container rule. The old generated tree is not worth keeping: it is
reproducible from cerberus-lean at `58ec50779` + `make
lean-prelude-src`.

## 11. Gates

Intermediate commit `0f1558a` on `scripts/test_unit.sh --fast`
(fast-gate). Final commit on the FULL gate; tail verbatim in the
commit message and here:

```
ok: cerberus-heaplang build green
== speedbump: capability manifest (regenerate; red on a red row or drift) ==
ok: capability manifest regenerated, no drift
ALL GATES GREEN
```
