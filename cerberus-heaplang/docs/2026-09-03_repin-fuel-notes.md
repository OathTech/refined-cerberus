# 2026-09-03 — THE FUEL-ARC RE-PIN (cerberus-lean `ddcfc9199` → `f95ef8d9c`)

Worker record (branch `repin-fuel`, worktree `worktrees/repin-fuel`).
Provenance: [USER 2026-09-03] OVERNIGHT AUTONOMY ruling (2) in
`docs/DECISIONS.md` (the fuel fix landed; re-pin after K4/K5, before calls;
the fuel-lane restatement after calls); the [USER 2026-09-02] genuine-driver
rule; the scout record `docs/2026-09-03_repin-scout.md` (branch
`repin-scout`); the cerberus-lean change manifest
`lean_frontend/docs/2026-09-03_fuel-arc-change-manifest.md`. This is a
FORCED SEMANTICS-CHANGE slice, one change at a time: the pin plus the
mechanical fixes it forces, and nothing else — no fuel-lane restatement
(`driveU` and every PROVISIONAL export are untouched). Quoted outputs are
verbatim; tallies marked DERIVED are grep/diff-derived.

Rebased base: `367af77` (`kill-free-k2` head at gate time: the K5 range
audit record + its DECISIONS entry; K5.1 not yet landed). Commits: `ee02961`
(1/2, the code slice; fast-gate) and the record commit (2/2, this file +
shop-window docs + two Lean header comments; FULL gate, §8).

## 1. The pin move

`scripts/semantics-pin.env`: `CERBERUS_LEAN_COMMIT`
`ddcfc919972a31bc43a0454e6b2e76a19e6c4594` →
`f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf` (`git -C cerberus-lean rev-parse
f95ef8d9c`; = mainline `mdd/cerberus-lean` HEAD; 35 commits, `git rev-list
--count`). The delta on the code-bearing paths, verbatim
(`git -C cerberus-lean diff --stat ddcfc919… f95ef8d9c… -- frontend
lean_frontend/generated lean_frontend/native lean_frontend/lakefile.toml
lean_frontend/handwritten_copy.manifest 'lean_frontend/*.lean' Makefile
lean_frontend/Makefile`):

```
 Makefile                                           |  44 +-
 frontend/concurrency/cmm_op.lem                    |  13 +-
 frontend/model/annot.lem                           |   6 +-
 frontend/model/core.lem                            |   3 +-
 frontend/model/core_run_aux.lem                    |  24 -
 frontend/model/ctype.lem                           |   3 +-
 frontend/model/defacto_memory.lem                  |  11 +-
 frontend/model/driver.lem                          |  29 +-
 frontend/model/nondeterminism.lem                  |  33 +-
 frontend/model/state_exception_undefined.lem       |   3 +-
 frontend/model/utils.lem                           |   5 +-
 .../{relsemcore/RelSem/Call.lean => CerbCall.lean} | 137 ++---
 lean_frontend/CerbFuel.lean                        |  73 +++
 lean_frontend/CerbFunMapInstances.lean             |  11 +-
 lean_frontend/CerbMem.lean                         | 388 ++++++++++++-
 lean_frontend/CerbND.lean                          | 310 +++++++++--
 lean_frontend/CerberusFresh.lean                   |   6 +-
 lean_frontend/Main.lean                            |  28 +-
 lean_frontend/handwritten_copy.manifest            |  45 ++
 lean_frontend/lakefile.toml                        |  29 +-
 lean_frontend/relsemcore/RelSem/Cerberus.lean      | 456 ----------------
 lean_frontend/relsemcore/RelSem/ExecModel.lean     |  95 ----
 lean_frontend/relsemcore/RelSem/Machine.lean       | 602 ---------------------
 lean_frontend/relsemcore/RelSem/RunND.lean         | 356 ------------
 lean_frontend/speclab/SpecLab/ByteArrHarness.lean  |   7 +-
 lean_frontend/speclab/SpecLab/CnSeed.lean          |   2 +-
 lean_frontend/speclab/SpecLab/Codec.lean           |   3 +-
 lean_frontend/speclab/SpecLab/DivModFiles.lean     |   7 +-
 lean_frontend/speclab/SpecLab/DivModHarness.lean   |  11 +-
 lean_frontend/speclab/SpecLab/ListAppendFiles.lean |   6 +-
 lean_frontend/speclab/SpecLab/MkHarness.lean       |   8 +-
 .../speclab/test/SLUnit/ByteArrGateTest.lean       |   8 +-
 .../speclab/test/SLUnit/CoreGateTest.lean          |  15 +-
 lean_frontend/speclab/test/SLUnit/EmitCore.lean    |  12 +-
 lean_frontend/speclab/test/SLUnit/ListGateTest.lean |   8 +-
 lean_frontend/speclab/test/SLUnit/SeedGateTest.lean |   9 +-
 lean_frontend/speclab/test/SLUnit/TreeGateTest.lean |   8 +-
 lean_frontend/test/Unit/FuelExemplar.lean          | 449 +++++++++++++++
 lean_frontend/test/Unit/TotalityProofTest.lean     |  17 +-
 39 files changed, 1469 insertions(+), 1811 deletions(-)
```

(`generated/` is gitignored upstream: its delta shows through the
workspace re-prime, as at every re-pin.) What the delta is, per the scout's
verified account (§1–2 there): the FUEL arc — `CerbFuel.lean` (new seam:
`fuelExhaustedLoc` opaque-with-value, `fuelExhaustedMsg`, `driverFuel :=
100000000`), `CerbND.lean` (`fuelExhaustedKill`, `ndDefaultFuel :=
driverFuel`, the `FuelContract` section: nine ND-typed `_lemFuel_zero`
lemmas, three runner leaves, `driverFuel_eq`, the wrapper `rfl`s
`driver2_wrapper_defeq`/`nd_bind_wrapper_defeq`/`runND_eq`/…, and the
`DriveMirror` section: `drive_lemFuel` with `drive_wrapper_defeq`), the six
L1 budget declares in `driver.lem`/`nondeterminism.lem` that emit `10^8`
into the drive cone's generated wrappers; the mem-scale C1/C3 body changes
in `CerbMem.lean` (`reconstructValue_lemFuel` array arm,
`memValueToBytes_lemFuel` struct arm; signatures unchanged; the pre-change
forms kept as kernel-checked equalities); the RelSem prune (four modules
deleted, `Call.lean` → `CerbCall.lean`); `cmm_op.lem`'s `sorry` target_rep
replaced by `CerbMem.stringFromMemValue`; and `handwritten_copy.manifest`
(NEW — the authoritative 23-seam list, which section C of
`setup-cerberus-dep.sh` now reads).

LemLib: rev UNCHANGED (`045dcb0d57a171eb4fb3a6eb5abe288c227270ce` in both
`lake-manifest.json` and `cerberus-heaplang/lake-manifest.json`, verified
by grep); no `lake update` was run; the manifests are untouched (Lake
accepted them silently in every build — `git status` never showed them).

## 2. The workspace (`--check` transcript, verbatim, rc 0)

The worktree's `.cerberus-ws` was primed and built at the new pin by the
scout (`.primed-from`: `f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf
2026-09-03T05:52:15Z`; `git -C .cerberus-ws rev-parse HEAD` =
`f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf`). After the pin edit:

```
== setup-cerberus-dep: A ok: workspace at pinned commit
== setup-cerberus-dep: B ok: primed (f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf 2026-09-03T05:52:15Z)
check_lem_sync: lean OK (src 4f2e089b39d5b371973513b3350f81d1b89871976f77df9ba4a25da3421d0c54, gen 49ad8b2c359cb0b36ed12913eb0bb3a4986c0ee582fe8e735e700297d38eee00)
== setup-cerberus-dep: B ok: Lean lem-sync stamp verified in the workspace
== setup-cerberus-dep: C ok: 23 hand-written seams byte-identical to the pin
== setup-cerberus-dep: DONE. Lake consumes /home/dev/projects/cerberus-lean-proj/refined-cerberus/worktrees/repin-fuel/.cerberus-ws/lean_frontend as a path dependency.
```

Admissions at the new pin (measured): `grep -rn sorry
.cerberus-ws/lean_frontend/generated/` hits eight files, every hit comment
text (the arc-4 history notes in `CerbStepInstances.lean`,
`CerbFunMapInstances.lean`, `Core_reduction.lean`, …); no `sorry` term;
neither build log contains `declaration uses sorry` (`grep -c` = 0 in the
census build and in the FULL gate). The README's "one known admission"
paragraph (the `Cmm_op.lean` `(sorry : String)` pair) is therefore stale
and is rewritten in this slice (§7).

## 3. The error census — measured, three build cycles, ONE cause

All builds through `scripts/capped` with `CERB_MEM_MAX=48G`; no UNCAPPED
warning in any log (`grep -ci uncapped` = 0). Root package first: rc 0,
10:55:58 → 10:56:00 (everything replayed against the dep cone the scout
had built in `.cerberus-ws/lean_frontend/.lake`; Audit output verbatim:
`RefinedCerberus axiom sweep: 2 theorems, all cones within the classical
trio` / `RefinedCerberus banned-axiom sweep: 3 constants of every kind
checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones`).

The one cause, everywhere: the drive cone's wrappers (`nd_bind`,
`driver2`, `drive_nonmemory_steps_aux2`, `runND`/`ndDefaultFuel`) now
unfold to `100000000`; our proofs equated them with `lemDefaultFuel` /
`Nat.succ 999999` / the `999999`-family numerals. A `show` that forces the
10^8-vs-10^6 numeral defeq hits `maximum recursion depth`; a `rfl` stating
`ndDefaultFuel = Nat.succ 999999` is a type mismatch; a hypothesis stated
at `driver2_lemFuel lemDefaultFuel` no longer matches the wrapper.

### Cycle 1 (the frontier; heaplang rc 1, 10:56:00 → 10:58:27)

```
error: CerberusHeapLang/DriverCollapse.lean:123:2: maximum recursion depth has been reached
error: CerberusHeapLang/DriverCollapse.lean:140:2: maximum recursion depth has been reached
error: CerberusHeapLang/DriverCollapse.lean:221:55: Type mismatch
  rfl
has type
  ?m.61 = ?m.61
but is expected to have type
  CerbND.ndDefaultFuel = Nat.succ 999999
error: CerberusHeapLang/DriverCollapse.lean:602:11: maximum recursion depth has been reached
```

Tail: `Some required targets logged failures:` / `- CerberusHeapLang.DriverCollapse` / `error: build failed`.
Twenty-five modules built green ahead of the frontier (the scout's list;
`Heap`, `Rules`, `Soundness`, `Examples.Layout`, `LoopExhibit`,
`ListRevExhibit`, `TreeRotExhibit` among them — the C1/C3 clients).

### Cycle 2 (after the DriverCollapse fixes; rc 1, 11:02:12 → 11:02:35)

```
error: CerberusHeapLang/ProdEntry.lean:361:10: maximum recursion depth has been reached
error: CerberusHeapLang/ProdEntry.lean:399:10: maximum recursion depth has been reached
error: CerberusHeapLang/Round.lean:4736:4: maximum recursion depth has been reached
error: CerberusHeapLang/Round.lean:4917:55: Type mismatch
  rfl
has type
  ?m.636 = ?m.636
but is expected to have type
  CerbND.ndDefaultFuel = Nat.succ 999999
```

### Cycle 3 (after the Round/ProdEntry fixes; rc 1, 11:03:31 → 11:03:50)

```
error: CerberusHeapLang/ProdExhibit.lean:308:14: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  lemDefaultFuel
in the target expression
  10 + 2 ≤ CerbFuel.driverFuel
error: CerberusHeapLang/RegionLoopExhibit.lean:745:25: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  …
 d := ↑lemDefaultFuel
 e := ↑CerbFuel.driverFuel
```

`Round`, `ProdEntry`, `ProdLoop`, `StructExhibit`, `AllocExhibit` built
GREEN in this cycle (StructExhibit is the one struct-typed
`memValueToBytes` client the scout could not reach: C3 broke nothing —
measured). `ProdLoopExhibit`, `DisposeExhibit`, `MallocListExhibit`,
`Audit` were not reached (import order); their sites are of the identical
shape (the `hfl` discharge fed to `prod_run_eqJ`) and were fixed in the
same edit as the two measured ones.

### Cycle 4 (after the exhibit fixes; rc 0, 11:04:32 → 11:04:47)

```
info: CerberusHeapLang/Audit.lean:396:0: CerberusHeapLang export pins: 294 trio-exact
info: CerberusHeapLang/Audit.lean:396:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (3046 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:396:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (4691 constants of every kind swept, internal details included — count informational, environment-dependent)
```

### Census vs the scout's prediction

| module | measured errors | site (today's lines) | scout §3.3 |
|---|---|---|---|
| DriverCollapse | 4 | :123 `runOne_bind_active`, :140 `runOne_bind_killed` (nd_bind `show`), :221 `runND_active` (`ndDefaultFuel` rfl), :602 `driver2_done` (`hloop` at `lemDefaultFuel`) | 4 MEASURED at :123/:140/:221/:548 (K5 shifted the last) — exact |
| Round | 2 (cascade hides the rest of `memop_fork`) | :4736 `runOne_bind_nd` (`show`), :4917 `memop_fork` (`ndDefaultFuel` rfl); the same theorem's `bind_branch_active 999998` ×3, `runNDFuel_nd 999999`, `runNDFuel 999999`, `runNDFuel_active 999998` fixed with it | PREDICTED :3760–3767/:3937/:3946–3954 — the same three sites |
| ProdEntry | 2 | :361 `drive_after_setup` (`exact hdrv2` — its `hdrv2` binder at `lemDefaultFuel`), :399 `prod_run_eqJ` (`driver2_done 999999`) | PREDICTED :327/:393 — exact |
| ProdExhibit | 1 | :308 `exhibitA_prod`'s `hfl` discharge (`rw [show lemDefaultFuel = …]` on a `driverFuel` goal) | PREDICTED ("follows the ProdEntry restatement") |
| RegionLoopExhibit | 1 | :745 `region_loop_certified_production`'s `hfl` discharge (`omega` with `hfuel` in `lemDefaultFuel`) | PREDICTED (same class) |
| ProdLoopExhibit, DisposeExhibit, MallocListExhibit | not reached; same shape fixed | fib :~112 `(by omega)`, counter :679, list-reverse :1495–1497; dispose :1655–1657; malloc-list `(by unfold mlCost; omega)` | PREDICTED |
| StructExhibit, AllocExhibit | 0 (built green untouched) | — | listed as "if `prod_run_eqJ`'s premise moves"; they do not consume `prod_run_eqJ` (`pot`-bound `show lemDefaultFuel = 999999 + 1` sites only, which stay valid) |
| Audit | 0 | 294 pins unchanged (no name moved) | "mechanical re-pin of the signature file" — not needed: pins are by name and axiom cone, not signature |

Renamed constants: 0. Changed signatures: 0. CerbMem C1/C3 body-change
breakage: 0 (every client module built green untouched). Nothing was
stopped; every error was of the budget class.

## 4. Every fix, before → after

The idiom (the exemplar's, cerberus-lean `test/Unit/FuelExemplar.lean:198`):
unfold the budget ONLY through a `_succ` lemma — never a `show`-forced
numeral defeq.

DriverCollapse.lean
- NEW beside `lemDefaultFuel_succ` (kept for `liftND`): `private theorem
  driverFuel_succ : CerbFuel.driverFuel = Nat.succ 99999999 := rfl`.
- `runOne_bind_active`, `runOne_bind_killed`: `show runOne (nd_bind_lemFuel
  lemDefaultFuel (ND g) f) s = _; rw [lemDefaultFuel_succ]` → `show runOne
  (nd_bind_lemFuel CerbFuel.driverFuel (ND g) f) s = _; rw [driverFuel_succ]`.
- `runOne_liftMem_active`: UNCHANGED (`liftND_lemFuel lemDefaultFuel` — the
  lift stays at 10^6, the L1 opt-in guarantee).
- `runND_active`: `show CerbND.runNDFuel CerbND.ndDefaultFuel (ND g) s = _;
  rw [show CerbND.ndDefaultFuel = Nat.succ 999999 from rfl]` → `show
  CerbND.runNDFuel CerbFuel.driverFuel (ND g) s = _; rw [driverFuel_succ]`.
- `driver2_done` (STATEMENT): `(hloop : runOne
  (drive_nonmemory_steps_aux2_lemFuel lemDefaultFuel tds fmapEmpty [0]) dst
  = …)` → `… drive_nonmemory_steps_aux2_lemFuel CerbFuel.driverFuel …`.
- Header FUEL paragraph rewritten (the drive cone at `driverFuel`, the
  transparent kill, the `_succ` discipline).

Round.lean
- `runOne_bind_nd` (STATEMENT + proof): `p'.2 = nd_bind_lemFuel 999999 p.2
  f` → `… 99999999 …` (twice); `show runOne (nd_bind_lemFuel lemDefaultFuel
  (ND g) f) s = _; rw [show lemDefaultFuel = Nat.succ 999999 from rfl]` →
  `… CerbFuel.driverFuel …; rw [show CerbFuel.driverFuel = Nat.succ 99999999
  from rfl]`; docstring names the budget.
- `memop_fork` (proof only): `bind_branch_active 999998` ×3 →
  `bind_branch_active 99999998` ×3; `show 2 ≤ (CerbND.runNDFuel
  CerbND.ndDefaultFuel _ dst).length; rw [show CerbND.ndDefaultFuel =
  Nat.succ 999999 from rfl, runNDFuel_nd 999999 hD',
  foldl_append_singletons_length (fun p => CerbND.runNDFuel 999999 …` →
  `… CerbFuel.driverFuel …; rw [show CerbFuel.driverFuel = Nat.succ 99999999
  from rfl, runNDFuel_nd 99999999 hD', … CerbND.runNDFuel 99999999 …`;
  `runNDFuel_active 999998` → `runNDFuel_active 99999998`. The
  `runOne_liftNDF_nd 999998` / `runOne_liftNDF_active 999996` layers
  (liftMem = liftND at `lemDefaultFuel`) are UNCHANGED.
- `runOne_liftMem_killed`, `update_env_aux_spec_mismatch`, every `pot`/
  `esize`/`peDepth` site, every `unfold lemDefaultFuel`: UNCHANGED (10^6
  workers).

ProdEntry.lean
- `drive_after_setup` (STATEMENT): `(hdrv2 : runOne (driver2_lemFuel
  lemDefaultFuel fmapEmpty false) (prodEntryState sup e fs) = …)` → `…
  driver2_lemFuel CerbFuel.driverFuel …`.
- `prod_run_eqJ` (STATEMENT): `(hfl : k + 2 ≤ lemDefaultFuel)` → `(hfl : k
  + 2 ≤ CerbFuel.driverFuel)`; proof: `hdd (prodEntryState sup e fs)
  fmapEmpty lemDefaultFuel rfl rfl rfl hQe hfl` → `… CerbFuel.driverFuel
  …`; `driver2_done 999999 …` → `driver2_done 99999999 …`.
- Header: the in-budget-bound paragraph rewritten (the bound against the
  name the semantics exports; the transparent kill below it).

ProdLoop.lean — header sentence only (`k + 2 ≤ CerbFuel.driverFuel`; `fl`
instantiated at it by `prod_run_eqJ`). `DriverDoneAt` is fuel-generic and
UNCHANGED.

ProdExhibit.lean — `exhibitA_prod`'s `hfl`: `(by rw [show lemDefaultFuel =
999999 + 1 from rfl]; omega)` → `(by rw [show CerbFuel.driverFuel =
99999999 + 1 from rfl]; omega)`.

ProdLoopExhibit.lean
- `fib_certified_production` (STATEMENT): `(hfuel : 2 * n.toNat + 6 ≤
  lemDefaultFuel)` → `… ≤ CerbFuel.driverFuel`; its `hfl` `(by omega)`
  unchanged (omega on the shared atom); docstring's "`lemDefaultFuel =
  10^6`" → "`CerbFuel.driverFuel = 10^8`".
- `counter_loop_certified_production` (STATEMENT): `(hfuel : 6 * n.toNat +
  8 ≤ lemDefaultFuel)` → `… ≤ CerbFuel.driverFuel`; its `hfl`: `(by rw
  [show lemDefaultFuel = 999999 + 1 from rfl] at hfuel ⊢; rw [ctrCost_eq,
  …]; omega)` → `(by rw [ctrCost_eq, …]; omega)` (the numeral rewrite is
  unnecessary on the shared atom).
- `list_reverse_certified_production`'s `hfl`: `show lemDefaultFuel =
  999999 + 1 from rfl` → `show CerbFuel.driverFuel = 99999999 + 1 from rfl`
  (statement has no `hfuel`: constant step count).

DisposeExhibit.lean — `dispose_list_certified_production`'s `hfl`: the same
numeral rewrite → `CerbFuel.driverFuel = 99999999 + 1`.

RegionLoopExhibit.lean — `region_loop_certified_production` (STATEMENT):
`(hfuel : 7 * n.toNat + 5 ≤ lemDefaultFuel)` → `… ≤ CerbFuel.driverFuel`;
its `hfl` `(by unfold rlCost; omega)` unchanged.

MallocListExhibit.lean — `malloc_list_certified_production` (STATEMENT):
`(hfuel : 25 * n.toNat + 9 ≤ lemDefaultFuel)` → `… ≤ CerbFuel.driverFuel`;
its `hfl` `(by unfold mlCost; omega)` unchanged; header sentence.

Unchanged and deliberately so: every `pot e ≤ lemDefaultFuel` / `esize e ≤
lemDefaultFuel` / `peDepth pe ≤ lemDefaultFuel` premise (the evaluator and
`get_ctx` stay at 10^6), every `liftND`/`liftAction`/`update_env_aux`/
`collect_saves`/`step_eval_pexpr` site, every `show lemDefaultFuel = 999999
+ 1 from rfl` under a `pot` bound. `driveU`, `MemTripleU`, the projection
theorems, `wpt_engine_boundU*` and every PROVISIONAL export: untouched.

## 5. The restated side conditions — the operator-facing decision

Scout §4.3 design point (i): the exported premise `k + 2 ≤ lemDefaultFuel`
on `prod_run_eqJ` and the `*_certified_production` statements was still
TRUE and provable at 10^8 (the old bound implies the new one), so it could
have been kept verbatim. Per the brief, it is RESTATED as `k + 2 ≤
CerbFuel.driverFuel`, because (a) the shipped wrappers now run at
`driverFuel` and the change manifest §4 names `CerbFuel.driverFuel` as the
citable side-condition name ("the premise shape is `k + 2 ≤
CerbFuel.driverFuel`"); (b) `lemDefaultFuel` would have been a bound about
a DIFFERENT budget than the one the statement's driver consumes — true by
accident of 10^6 ≤ 10^8, not by meaning; (c) every affected statement's
premise WEAKENS (`lemDefaultFuel ≤ driverFuel`, i.e. 10^6 ≤ 10^8), so each
restatement is a strict generalization of the K5-head theorem.

| statement | old premise | new premise |
|---|---|---|
| `prod_run_eqJ` | `hfl : k + 2 ≤ lemDefaultFuel` | `hfl : k + 2 ≤ CerbFuel.driverFuel` |
| `fib_certified_production` | `hfuel : 2 * n.toNat + 6 ≤ lemDefaultFuel` | `… ≤ CerbFuel.driverFuel` |
| `counter_loop_certified_production` | `hfuel : 6 * n.toNat + 8 ≤ lemDefaultFuel` | `… ≤ CerbFuel.driverFuel` |
| `region_loop_certified_production` | `hfuel : 7 * n.toNat + 5 ≤ lemDefaultFuel` | `… ≤ CerbFuel.driverFuel` |
| `malloc_list_certified_production` | `hfuel : 25 * n.toNat + 9 ≤ lemDefaultFuel` | `… ≤ CerbFuel.driverFuel` |
| `drive_after_setup` (collapse machinery) | `hdrv2 : runOne (driver2_lemFuel lemDefaultFuel …) …` | `… driver2_lemFuel CerbFuel.driverFuel …` |
| `driver2_done` (collapse machinery) | `hloop : runOne (drive_nonmemory_steps_aux2_lemFuel lemDefaultFuel …) …` | `… CerbFuel.driverFuel …` |
| `runOne_bind_nd` (ND-collapse lemma) | `p'.2 = nd_bind_lemFuel 999999 p.2 f` | `… 99999999 …` |

`exhibitA_prod`, `list_reverse_certified_production`,
`dispose_list_certified_production` have constant certified step counts
and no fuel premise; their statements are byte-identical (snapshot §6).
The last three rows are not side conditions but statements about the
wrappers' fuel at the concrete budget; they follow the wrappers.

## 6. Snapshot pre → post, classified

`docs/2026-09-03_k5-signatures-post.txt (byte-identical to the former 2026-09-03_repin-fuel-signatures-pre.txt, deduplicated 2026-09-03)` is a copy of
`2026-09-03_k5-signatures-post.txt` (the tree at `a0449d7` is the K5 head
unchanged; the old-pin build state is no longer available in this worktree
to regenerate it). `…-post.txt` was generated by
`scripts/signature_snapshot.lean` after cycle 4 (2665 → 2664 entries).
Compared BY ENTRY (kind + name + printed type; DERIVED):

- ADDED: 0.
- REMOVED: 1 — `CerbMem.reconstructValue_lemFuel.eq_def`. A DEPENDENCY
  equation lemma, not a package statement: at the old pin it was realized
  on demand inside `ListRevExhibit`/`TreeRotExhibit` (their `unfold
  CerbMem.reconstructValue_lemFuel`, :263/:144) and so carried our
  module-of-origin; at the new pin `CerbMem.lean:1125` (`unfold
  reconstructValue_lemFuel …` inside `reconstructValue_lemFuel_eq_indexed`)
  realizes it upstream, so it is no longer ours. Exactly the
  environment-dependent auxiliary class the Audit header documents.
- CHANGED: 14.
  - 8 package statements — exactly the §5 table: `prod_run_eqJ`,
    `fib_certified_production`, `counter_loop_certified_production`,
    `region_loop_certified_production`, `malloc_list_certified_production`
    (`≤ lemDefaultFuel` → `≤ CerbFuel.driverFuel`), `drive_after_setup`,
    `driver2_done` (`lemDefaultFuel` → `CerbFuel.driverFuel` in the wrapper
    argument), `runOne_bind_nd` (`999999` → `99999999`).
  - 6 dependency `.eq_def` auxiliaries whose printed type is the
    semantics' own definition — the pin delta showing through, no package
    change: `CerbND.runNDFuel.eq_def` (fuel-0 leaf `panicWithPosWithDecl
    "CerbND" "CerbND.runNDFuel" …` → `[(Killed st0 CerbND.fuelExhaustedKill,
    [], st0)]`), `driver2_lemFuel.eq_def`, `nd_bind_lemFuel.eq_def`,
    `liftND_lemFuel.eq_def`, `drive_nonmemory_steps_aux2_lemFuel.eq_def`,
    `liftAction_lemFuel.eq_def` (each fuel-0 arm `fuelExhausted (… NDkilled
    (Undef0 CerbLocation.Loc.unknown []) …)` → `… NDkilled (Error0
    CerbFuel.fuelExhaustedLoc CerbFuel.fuelExhaustedMsg) …`).
- Every other entry (2650) byte-identical. Nothing else changed shape:
  the expected changes are exactly the side conditions, and the rest is
  the dependency showing through.

## 7. Shop-window docs and in-code prose

README (pin line already points at `../scripts/semantics-pin.env`): the
exhibits table's four `hfuel` cells → `CerbFuel.driverFuel`; "The claim"
and "The trust story" PROVISIONAL paragraphs: the obstacle sentence
(kernel-opaque `fuelExhaustedWith`) restated in the past tense with the
landing named — the shipped driver's fuel exhaustion is now the
kernel-transparent kill `CerbND.fuelExhaustedKill`, `CerbND.drive_lemFuel`
is pinned to `drive` by `drive_wrapper_defeq`, the partial lane's
restatement over `drive_lemFuel` is the next slice (after calls), the
PROVISIONAL labels remain until then; the "one known admission" paragraph
→ "none (measured 2026-09-03)" with the measurement (§2); the
divergences table's Fuel row; the trust diagram's `[labels; k + 2 ≤
CerbFuel.driverFuel]`; the diagram's "what it does not contain" note.
ARCHITECTURE §6: the `hfuel`/`k + 2` clauses, the PROVISIONAL-lane
obstacle paragraph (lifted at the pin, restatement sequenced after calls),
§7 goal 1 ("HAS LANDED AND IS PINNED", re-pin done). WALKTHROUGH §1.1/§1.3/
§4/§5/§7: the same sentences at their five sites plus the two exhibit
`hfuel` mentions. In-code: `Adequacy.lean` header (the PROVISIONAL
definition's obstacle sentence, same rewording), `Audit.lean` header (the
re-pin noted; pin list unchanged at 294), and the DriverCollapse/ProdEntry/
ProdLoop/ProdLoopExhibit/MallocListExhibit sentences listed in §4. Every
statement that the evaluator/`get_ctx` run at `lemDefaultFuel = 10^6` with
an opaque leaf (README "The fragment", WALKTHROUGH §5, Soundness FUEL
HONESTY) is UNCHANGED — still true: only the ND-typed workers' arms became
transparent; the pure-return arms (`get_ctx`, `hack`, `mkUnspec`, …) keep
the opaque sentinel (scout §1.2). PROVISIONAL label count: README 31 → 32
(the one new mention is this slice's "the PROVISIONAL labels remain until
then" sentence), ARCHITECTURE 5, WALKTHROUGH 12 — no label removed, none
added to a theorem (DERIVED `grep -c`).
`docs/DECISIONS.md` not edited (orchestrator's).

## 8. The FULL gate (rebased tree; verbatim tail)

`CERB_MEM_MAX=48G scripts/test_unit.sh` on the rebased tree (commit 1 =
`ee02961` on `367af77`, plus the working-tree docs and the two Lean header
comments that commit 2 adds), 11:12:21 → 11:16:25 UTC; `grep -c 'uses
sorry'` = 0 and `grep -ci uncapped` = 0 over the whole log. Gate 1 `ok: no
banned proof-method references`; gate 2 `ok: root build green`; gate 3 and
the speedbumps, verbatim tail (the preceding lines are the pre-existing
unused-simp-arg linter note at Round.lean:4913):

```
  List.mem_singleton

Hint: Omit it from the simp argument list.
  simp only [List.mem_cons, L̵i̵s̵t̵.̵m̵e̵m̵_̵s̵i̵n̵g̵l̵e̵t̵o̵n̵,̵ ̵List.not_mem_nil, or_false] at hp0

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
ℹ [452/454] Built CerberusHeapLang.Audit (1.2s)
info: CerberusHeapLang/Audit.lean:403:0: CerberusHeapLang export pins: 294 trio-exact
info: CerberusHeapLang/Audit.lean:403:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (3046 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:403:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (4691 constants of every kind swept, internal details included — count informational, environment-dependent)
✔ [453/454] Built CerberusHeapLang (693ms)
Build completed successfully (454 jobs).
ok: cerberus-heaplang build green
== speedbump: capability manifest (regenerate; red on a red row or drift) ==
cerberus-lean-proj env: switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_opam, git redirects active
ok: capability manifest regenerated, no drift
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — no core module imports an exhibit/example/production module
ALL GATES GREEN
gate rc=0
2026-09-03T11:16:25Z
```

Exit code 0.

## 9. What was not done / borderline

- Nothing stopped: no non-budget-class error appeared in any cycle.
- The scout's suggested deletion of the "opaque `fuelExhausted`" prose at
  Soundness.lean:56 was NOT applied: that sentence is about `get_ctx`, whose
  arm is a pure-return sentinel and stays opaque at the new pin (scout §1.2:
  "the pure-return arms keep the opaque sentinel"). The Adequacy/ProdEntry/
  DriverCollapse instances (about the driver) were rewritten.
- The pre-snapshot is a copy of the K5 post-snapshot, not a regeneration
  (the old-pin build state is gone from this worktree); the tree at
  `a0449d7` is the K5 head unchanged, so the copy IS the old-pin
  snapshot of this tree.
- The scout's §3.4 observation (the two consumers rebuild the shared dep
  cone on alternation) recurred once here: the fast gate's root build
  rebuilt the cone (~3 min) after the heaplang cycles; cycles 2–4 of the
  heaplang build alone took 15–25 s each.
- K5.1 (`kill-free-k2` follow-up) had not landed at gate time; the branch
  sits on `367af77` (the K5 audit record + DECISIONS entry, docs only — no
  conflicts). If K5.1 lands, the orchestrator rebases (coordinator's
  sequencing note).

## Addendum (orchestrator, 2026-09-03): the FULL gate at the COMBINED head

The record above describes the pre-rebase tree (294 pins). After the rebase over K5.1 and the audit's N-1 comment fix (head cf40966), the orchestrator ran `scripts/test_unit.sh` at that head. Verbatim verdict lines:

```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 2: capped build, root package (elaborates its axiom audit) ==
RefinedCerberus axiom sweep: 2 theorems, all cones within the classical trio
RefinedCerberus banned-axiom sweep: 3 constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
ok: root build green
== gate 3: capped build, cerberus-heaplang (elaborates its axiom audit) ==
CerberusHeapLang export pins: 296 trio-exact
CerberusHeapLang axiom sweep: every theorem bounded by the trio (3050 swept, internal details included — count informational, environment-dependent)
CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (4701 constants of every kind swept, internal details included — count informational, environment-dependent)
ok: cerberus-heaplang build green
== speedbump: capability manifest (regenerate; red on a red row or drift) ==
ok: capability manifest regenerated, no drift
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — no core module imports an exhibit/example/production module
ALL GATES GREEN
GATE-EXIT=0
```

This answers the combined audit's M-1 (no recorded gate at the combined head) and N-3/N-4 (the 294 in the record and commit message are the pre-rebase count; the merged content has 296 pins).
