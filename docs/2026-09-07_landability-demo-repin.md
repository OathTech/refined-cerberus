# Landability audit: branch `demo-repin` (cb46e4c..a41292d, 44 commits)

Auditor: independent skeptical auditor [AGENT], 2026-09-07. Subject: the
fixed detached copy `worktrees/audit-repin-a41292d` (HEAD `a41292d`), primed
at cerberus-lean `89f7e688530c6910884518811d645e4e892e4507` / LemLib
`f6542f8e6860d12d4655e6648bc4c45dabd1d798` / Lean 4.32.2
(`scripts/setup-cerberus-dep.sh --check` passed inside the inspector run,
see §7). Graded against `docs/AUDIT-BRIEF.md`; every KOI entry was read
first and is cited, not re-reported. All 44 commits are authored
`Mike Dodds <mike@oath.tech>` (the agent's session); every DECISIONS entry in
the range is `[AGENT, active charter]` except the one `[USER]` pause quote.
Nothing here was committed, merged or pushed; the only files I created are
this report and scratch logs I deleted.

## 0. Verdict table

| Group | Commits | Verdict | Size of work |
|---|---|---|---|
| G1 re-pin (representation + fuel + allocator contracts) | 8ddfeb8..520654f (17) | **LANDABLE WITH WORK** — as ONE forced re-pin slice (the pin carries both halves; a post-hoc representation/fuel split is not possible) | M |
| G2 a7 actual t1 file | 3aac95d..5bfe992 (10) | **LANDABLE WITH WORK** — it is the [USER 2026-09-04 Q3] option (b) mechanised over the whole file, not option (a); the executable check must become a gate speedbump and A7's "option (a) remains the target" sentence must come back | M |
| G3 E6/E7 scheduler, raw calls, multiple offers | 14e7dc3..6c8e7e3 (13) | **SPLIT — PARK** (do not land now): honest, kernel-sound scaffolding over shipped engine functions, but no acceptance program, a changed `Step`/`wps`/`wpt`/`Frag` under the frozen spec, 32 device-referent pins, and a design-level finding (the counterexample) that must go back to the operator before E6 continues | — (re-scope with operator) |
| G4 `seq_rmw` | 567c578..19292c0 (4) | **SPLIT — land after re-cut onto G1+G2 without G3** (it is E5's missing item; mirror faithful, rules sound, PROVISIONAL honestly labelled; sits textually on G3's traversal) | M (re-cut) + S (census) |
| G5 pause record + committed failing WIP patch | a41292d | **REJECT the patch in `docs/`** (branch it); the pause record is fine as a dated [AGENT] record | S |
| G6 DECISIONS / KOI / README / charter | spread | **LANDABLE WITH WORK** — README accurate at HEAD; DECISIONS is a 1795-line build log that must collapse; KOI has a malformed row, a stale E section and a quietly dropped "option (a) is the named target" | M (editorial) |

Overall: the branch is real work of good kernel-level quality, but it is not
"a validated checkpoint" in the sense the repo uses (one change at a time,
censused, recorded once). Land G1 then G2 with the fixes in §8, re-cut G4 on
top, park G3 until E6 is re-scoped with the operator, keep the WIP patch off
`main`, and squash the register.

## 1. What I ran (verbatim tails)

`CERB_MEM_MAX=40G scripts/test_unit.sh` in the audit copy, exit 0. The
package modules were replayed from the primed cache (Lake replays cached
logs), so warnings are the cached ones. Verdict lines, verbatim:

```text
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:1154:0: CerberusHeapLang export pins: 958 trio-exact, 7 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1154:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (6966 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1154:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (10402 constants of every kind swept, internal details included — count informational, environment-dependent)
ok: cerberus-heaplang build green
ok: capability manifest regenerated, no drift
ok: corpus skeleton — every transcription matches its emitted text, every plant mismatches
ok: import direction — 18 core modules, none imports an exhibit/example/production module
BOUNDARY: 33 modules checked, 0 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
EXIT=0
```

Package warnings (replayed), exactly two, verbatim:

```text
warning: CerberusHeapLang/Heap.lean:1396:5: Variable name `hsz` is not explicitly referenced.
warning: CerberusHeapLang/Heap.lean:2388:5: Variable name `h` is not explicitly referenced.
```

(627 further warnings are in LemLib/`generated/` — dependency, not ours.)

Oracle (mainline OCaml build, `--nolibc --exec --batch`), verbatim:

```text
t1:           Defined {value: "Specified(4)", stdout: "", stderr: "", blocked: "false"}
t2:           Defined {value: "Specified(3)", stdout: "", stderr: "", blocked: "false"}
t3_ptrarg:    Defined {value: "Specified(4)", stdout: "", stderr: "", blocked: "false"}
t10_evenodd:  Defined {value: "Specified(1)", stdout: "", stderr: "", blocked: "false"}
```

None of t2/t3/t10 has any theorem on the branch (§4). t8/t9 have no `.c`
in `docs/corpus-e0/` at HEAD.

Other measurements: `scripts/signature_snapshot.lean` at HEAD (33 s);
elaboration timings of the a7 modules (`EmittedT1.lean` 5.1 s wall,
`EmittedT1Data.lean` 3.2 s, `EmittedT1Exhibit.lean` 3.0 s); all 27
committed `docs/**/*.lean` evidence/probe files compile at HEAD with zero
errors; `git apply --check --unidiff-zero` of the WIP patch succeeds; the
a7 inspector (`scripts/inspect-emitted-file.sh … 50 … --check-data`) ran in
9.6 s wall after its one-off build and printed `emitted-file data
round-trip: exact quotation and supply match`; its report equals the
committed `docs/corpus-a7/t1.fuel50.inspection.json` byte-for-byte in
observations AND provenance (DERIVED by a JSON comparison).

## 2. Census (DERIVED; base is the last committed snapshot)

The branch committed NO signature snapshot for any of its 44 commits (the
repo's per-slice discipline since P0). The last committed snapshot is
`2026-09-05_e5b-signatures-post.txt` at `1d04dd7` (t5); `f60cdcf` (t4)
added statements without a snapshot, so a few "ADDED" below pre-date the
range. Against that base, HEAD has:

- entries 5543 vs 4718; **ADDED 860, REMOVED 35, CHANGED 1599**;
- of the 1599 changed: **565 binder/constant-only** (`[LemFuel]` inserted,
  `lemDefaultFuel`/`CerbFuel.driverFuel` → `LemFuel.fuel`), **1034 real
  text changes**: 264 remove a `pot`/`esize`/size premise, 139 add a fuel
  bound (`N ≤ LemFuel.fuel`, `0 < LemFuel.fuel`), 55 add the `Frag`
  `rawCalls : Bool` index, 14 change extern/requested-address contracts,
  562 other (mostly `callRedex?` → `callRedexAt? M ρ`, `M`/`resolve`
  arguments, `get_with_address`, `alignN`/`sz` allocator premises);
- theorems: 537 added, 30 removed, 861 real-changed.

Removed theorems (30): the `negFree*` family (renamed `boundFree*`,
G4), `MachineCtx.FragProcs.potBound`, `esizeAlts_le_potAlts_of`,
`esizeList_le_potList_of`, `drive_after_setup_{lib,with}_lemFuel`,
`t1Main_pot`, `t5Main_pot`, `treeMap_get?_insert_empty`, two `.eq_def`
auxiliaries; removed defs: `ctxNoUnseq`, `negFree`, `negFreeAlts`,
`negFreeList`, `instLanguageCoreRtMemEmptyCoreRVal` (re-created under a
`[LemFuel]` binder).

The twelve-ish headline statements — everything that changed beyond the
`[LemFuel]` binder and an `hfuel` bound:

| Statement | Change beyond binder/bound |
|---|---|
| `engine_adequacy`, `engine_adequacy_alloc`, `project_triple_pure` | `2 ≤ LemFuel.fuel` floor ADDED; `pot e₀ ≤ lemDefaultFuel` and the label-continuation `hQpot` premise DELETED (the bound now lives inside `Frag [LemFuel]` as `peDepth pe ≤ LemFuel.fuel`) |
| `engine_step_matchU` | `2 ≤ LemFuel.fuel` added; `esize e ≤ lemDefaultFuel` deleted |
| `prod_run_safe_procs`, `prod_run_safe_lib`, `fib_rec_certified`, `even_odd_certified` | `(fuel : Nat)` parameter and `CerbND.drive_lemFuel fuel` GONE → plain `drive` at the ambient; `hsafe` now conditional on `2 ≤ LemFuel.fuel` (KOI A2 genuinely closes) |
| `prod_run_eqJ`, `prod_run_eqJ_procs`, `fib_rec_certified_production` | constant → `LemFuel.fuel` only |
| `t1/t5/t6/t4_certified_production`, `list_reverse_certified_production`, `exhibitA_prod` | a NEW explicit `hfuel : N ≤ LemFuel.fuel` (50/90/80/917/56/12) — bounds, not numerals in the ruling's sense |
| `malloc_list_certified_production` | ADDITIONALLY `0 < al` (positive alignment — the allocator contract change, §3.4) |
| `killM_killed_inv` | 3 → 7 refusal rows (§3.2) |

Every pinned name exists and is exact (the build says so); 958 distinct
trio pins + 7 axiom-free pins measured from `Audit.lean` (964 name
occurrences, 958 distinct — the six repeats are comment mentions).

## 3. G1 — the re-pin group (8ddfeb8 … ce4d7de … 520654f)

### 3.1 What it is
Thirteen docs-only commits (8ddfeb8..1270ed9) recording a RED frontier
("the fast gate fails at …") while the source stayed uncommitted, then ONE
58-file source commit `ce4d7de` ("repin: quantify fuel and restore all
clients"), then three docs commits (FUEL.md, README/WALKTHROUGH,
ARCHITECTURE). The pin moves `f95ef8d9c` → `89f7e6885`, LemLib `045dcb0`
→ `f6542f8` (`lake-manifest.json` also changes the LemLib URL to
`OathTech/lem-lean`). The 37 hand-written seams verify.

### 3.2 (a) the LemLib representation change — as the scout predicted?
Yes, and better than predicted: `SymMap m := Fmap.WF symCmpK m`
(`EnvLaws.lean:242`) consumes the UPSTREAM `LemLibPmapLaws`
(`Fmap.WF_empty`, `Fmap.WF_fmapAddBy symCmpK_laws`) — the requested law
landed upstream, no local interim law (scout §4(a) alternative taken).
`Pmap.join` non-reduction (scout (a′)) is handled by "constructor-based
registration proofs … without increasing proof limits" (record) — no
heartbeat bump anywhere (grep: none). Fold/zip rewrites via
`LemLibTheorems.lemListFoldr_eq` as the scout's idiom. `killM_killed_inv`
text changed from 3 rows to 7 (UB179a, UB179b, UB009, Free_out_of_bound,
function pointer, no provenance, Prov_symbolic) — the scout predicted the
null-free (switch) and `zap_dead_pointers` (switch) rows too; the proof
discharges those arms with `CerbGlobal.has_switch_eq`, so at the pinned
switches they are unreachable; the disjunction is kernel-exhaustive. OK.

### 3.3 (b) the fuel restatement
- `lemDefaultFuel`, `driverFuel`, `ndDefaultFuel`: ZERO occurrences in
  code; the only mention is the historical paragraph in `Audit.lean:64-67`
  (comment). Numerals `10^8/1000000/999999`: none. `letI : LemFuel := ⟨…⟩`
  appears at 7 sites in `ProdEntry.lean`, all INSIDE proofs after
  `rcases LF with ⟨fuel⟩` (verified at each line) — the design's risk 2 is
  respected; no file-level `instance : LemFuel` in the library (the two
  `instance … [LemFuel]` in `Lang.lean` are the iris `Language`/`IrisGS`
  instances taking the binder). `docs/evidence/…repin-allocator.lean` has a
  `local instance : LemFuel := ⟨1⟩` — a probe, fine.
- Every fuel'd export is `[LemFuel]`; the closed partial forms
  (`prod_run_safe_procs/_lib`, `fib_rec_certified`, `even_odd_certified`)
  are genuinely `∀ [LemFuel]` over `drive` — both loops read the same
  ambient. KOI A2 closes as the design wanted.
- **Design deviation 1 (must be recorded, not a defect):** the orchestrator's
  `2026-09-04_fuel-restatement-design.md` §3 kept `hpot : pot e ≤
  LemFuel.fuel` as a statement hypothesis. The branch instead DELETED the
  potential premises and put the per-operand bound INSIDE the fragment:
  `inductive Frag [LemFuel] : CoreExpr → (rawCalls : Bool := false) → Prop`
  with `peDepth pe ≤ LemFuel.fuel` fields. The fragment is therefore
  fuel-relative (membership depends on the instance). Logically equivalent
  placement; semantically it changes what "the declared fragment" means on
  every manifest row. FUEL.md and ARCHITECTURE:71 disclose it, but neither
  says it deviates from the design or why. Also a `2 ≤ LemFuel.fuel` floor
  on generic adequacy/`engine_step_matchU` (ambient 0/1 handled only by
  the closed production forms) — disclosed in FUEL.md.
- **Design deviation 2:** no shipped-constant corollaries at `⟨100000000⟩`
  (design §3). Acceptable — no statement claims anything about the shipped
  binary — but the omission is undocumented.
- **The exhaustion question (review §2, F2 brief risk 1) was NOT
  measured or recorded.** At this pin the cerberus-lean C3/C4 manifests
  leave eight reachable AMBIENT rows whose exhaustion is the opaque
  `fuelExhausted x` (kernel `Inhabited` default): `ctype_aux`
  `are_compatible_aux` trio, `hack`, `to_pure`/`to_pures`, `many`/`many1`
  (C3 manifest §3; `check_fuel_forms.sh` register). FUEL.md says
  "Structural operations … use their own structural measures" and is silent
  on these. The branch's theorems are kernel-checked, so they are TRUE as
  stated — which means the premises (`Frag`'s per-operand depth, `2 ≤ fuel`,
  the exact zero/one setup equations) keep every export off those arms —
  but the F2 design required "State which form landed, in the record and
  in ARCHITECTURE §4", i.e. the (A)/(B)/(C)/(D) classification of the
  execution path with the premise that excludes each (D). Grep of every
  `repin-*.md`, FUEL.md and ARCHITECTURE for `opaque|pending|are_compatible|
  hack|to_pure|absorb`: nothing relevant. Documentation gap, graded Note
  (no gap in the logic), but it is exactly the deliverable the design named.
- `CerbTagsWf.Acyclic` (C4 hypothesis on the layout oracle): zero uses in
  the package — correct, every certified file has `tagDefs = fmapEmpty`;
  say so in FUEL.md.

### 3.4 An unplanned third change class: allocator/memory contracts
The scout (KOI A6 at base: "Everything else on the manifests measured
zero for this package") missed real semantic changes at the pin, which the
branch found by kernel counterexample (`docs/evidence/2026-09-06_repin-allocator.lean`):
negative-size region allocation succeeds; region allocation retains prior
bytes; `allocateObject` reads the requested address; `lastUsed` written.
The branch's response is correct in kind — premises on the public rules
(`0 < al`, nonnegative size, `get_with_address a = none`), a new
`UnallocatedBytes` component in `CohG`/`LaunchCoh` proved at `prodMem₀`
(`ProdMemory.lean`) — but it is a THIRD forced change with statement-text
consequences on public rules and one production export
(`malloc_list_certified_production`), landed in the same commit and
recorded across 17 progress files, never as one classified delta.

### 3.5 The `axiomFreeExports` class (7 pins)
Introduced because six previously trio-exact exports (`procCtx*` field
projections, `prodThread_eq_ctlThread`, `prodCtx_extern`) reduce by `rfl`
at the new pin and therefore have EMPTY cones; the exact-pin check fails on
shrinkage. The agent refused to "manufacture dependencies" and pinned them
to `[]` instead (E7 later added `runNDFuel_succ_congr`). Exactness is
preserved per name; the gate is not weakened; header comment and
docstring explain it with provenance. Fine. (Cosmetic: the Audit.lean
header still narrates the `10^8` era at :64-67.)

### 3.6 The 20 `docs/evidence/*.lean` files and 17 `repin-*.md` records
The `.lean` files are per-commit `#print axioms` listings (17) plus three
probes (allocator counterexample, kill classification, panic defaults).
All 27 committed `.lean` files in `docs/` compile at HEAD. They are not run
by any gate; they duplicate what the exhaustive sweep proves for the whole
package at every build; several headers say "Requires the in-progress M2
source repairs in worktrees/demo-repin" (stale). They are inspection logs,
not evidence of anything the build does not already assert — shop-window
noise. The three probes are worth keeping (as ONE dated evidence file);
the 17 listings should go. The 17 `repin-*.md` files (about 2.4 k lines)
are the same progress log in prose, and 31 of the 44 dated docs cite 34
distinct `.tmp/repin-scout/...` scratch paths that the container rule says
are ephemeral — dangling evidence pointers in committed records.

### 3.7 Verdict G1
LANDABLE WITH WORK (M). The pin, the representation, the fuel, and the
allocator repairs are all forced and correctly done at the kernel; the
work is what the design required around them: a census (§2 is a start),
the (D) paragraph, the deviation statement, one record, and hygiene.
A representation-first/fuel-second split (design §4) is impossible at
this pin (both arrive together, and the representation half does not
build without the binder), so ONE re-pin slice is the honest shape — say
so in the record with the three classes labelled.

## 4. G2 — a7, "certify actual t1 complete-file production" (3aac95d … 5bfe992)

### 4.1 What the statement is over
`CorpusA7.T1.certified_production [LemFuel] (hfuel : 50 ≤ LemFuel.fuel)
(cmp : EmittedFile.Comparators) (hstd : intLibraryCheck cmp.stdlib = true)
(hmain : mainLookupCheck cmp.funs = true) (hlabels : labelUnionCheck cmp =
true) fs args : ∃ dres dst', CerbND.runND (drive (restoredFile cmp).tagDefs
false (restoredFile cmp) args) ((initial_driver_state frontendSupply
(restoredFile cmp) fs).1) = [(Active dres, [], dst')] ∧ dres.dres_core_value
= lint 4 ∧ …` where `restoredFile cmp := EmittedFile.restore cmp data` and
`data : EmittedFile.Data` is the 42 841-line generated term
`Examples/EmittedT1Data.lean`, `frontendSupply = 36`. The transfer form
`certified_production_of_capture_eq` takes `hdata : captureData F = data`
and `hsup : sup = frontendSupply` for an arbitrary `F : file`.

So: NOT option (a) (the pipeline function is not in the statement). It is
option (b) — a transcribed term plus an executable equality — but
mechanised (the term is machine-quoted from the pinned Lean frontend's
in-memory `file` by `scripts/derive_file_to_expr.lean` + `emitted_frontend.lean`,
driven by `scripts/inspect-emitted-file.sh`, from the OCaml oracle's
`--cabs-json`) and over the WHOLE file (110 stdlib + 6 impl entries, all
eleven fields, tree shapes and heights, annotations, locations). The
comparators are quantified and constrained only by finite path checks on
the lookups the proof uses; `_of_capture_eq` re-instantiates them with the
captured closures — sound and honest (`restore_eq_of_data_eq`).

### 4.2 Is the ruling respected?
[USER 2026-09-04] E0 Q3 (DECISIONS at base): "the pipeline's Core enters a
statement as a HAND-TRANSCRIBED TERM checked by an EXECUTABLE EQUALITY
speedbump against the oracle's emitted Core … the elaborator-in-the-
statement form is the named target, not done". The branch's "user-
authorized executable-comparison boundary" (a7 records, KOI A7, README) is
therefore accurately sourced. Two departures:
1. **The check is not a speedbump.** It is an on-demand script, not in
   `test_unit.sh`; the claim gate cannot detect drift between
   `EmittedT1Data.lean` and the pipeline. I ran it: 9.6 s wall after its
   one-off build (it builds `+CerberusFresh:c`, compiles two helpers, links
   a `.so`, runs the pinned frontend, compares `toExpr (captureData actual)
   == toExpr data` and the supply). Cheap enough to be a gate speedbump
   like the corpus skeleton (E1's ruling made the skeleton one). Result at
   HEAD: `emitted-file data round-trip: exact quotation and supply match`;
   report identical to the committed fuel-50 report including provenance.
2. **KOI A7 quietly dropped the target.** Base A7 ended "The pipeline's
   whole `core_file` as the statement's object is the named target (design
   §C.9 option (a)), not done." The rewritten A7 does not mention option
   (a); the charter (§3) says only "The pipeline's whole file remains the
   preferred theorem referent". A shop-window regression: restore the
   sentence, or obtain a [USER] ruling that mechanised-(b) closes A7 for t1.

### 4.3 What is trusted
The theorem's kernel cone is the trio (pinned). Its MEANING depends on the
quoter (`derive_file_to_expr.lean`, hand-written; derives `ToExpr` for every
type reachable from `file`, hand-instances `Float` by bits, errors on
function fields) and on `emitted_frontend.lean` reproducing
`Main.runPipeline`'s loading path. A lossy quoter would make both sides
agree wrongly: the `data` term is elaborated from the SAME quoter's
output, so `toExpr actual == toExpr data` cannot see what the quoter
drops. Mitigations present: planted main-symbol/supply changes are
rejected; `restore_capture` proves reconstruction is exact for any file
(about `restore ∘ capture`, not about quotation); the frontend is the
pinned Lean frontend (Cabs from the OCaml oracle, digest checked). Missing:
an independent equality not routed through `toExpr` — a derived
`BEq`/`DecidableEq` on `EmittedFile.Data` evaluated on `captureData actual`
vs `data` (the record notes `file` has a derived `BEq` whose `Fmap` instance
compares binding lists only; `Data` excludes comparators so a full
structural instance is derivable). Cheap; do it.

`reference_main_labels` submits `Eq.refl` to the kernel through
`mkAuxLemma` inside `run_tac` (a hand-rolled `decide +kernel`) because the
elaborator hit the heartbeat limit reducing the map towers. Kernel-checked,
no `ofReduce*`, whole module 5 s — not a grind and not a bump; but it is
an unusual device and should be named in ARCHITECTURE's instruments
section rather than only in a docstring.

Nothing hand-written of semantic kind enters the statement: `restore` is a
record constructor over the engine's `file`; the checks are decidable
`Bool` functions over the data; `drive`, `runND`, `initial_driver_state`,
`create_extern_symmap`, `collect_labeled_continuations_NEW` are the
engine's. The referent rule is respected in the (b) sense.

### 4.4 Does it close KOI A7 for t1?
For t1: it is the full pipeline file (as data) with its full stdlib/impl,
so the E3-audit D-6 wrapper-vs-file gap is closed for t1 — modulo the
executable boundary, which is the ruled form. For the corpus: no (t4/t5/t6
still on `prodFileLib stdlibE3`; the KOI says so). Design Q7 said the
authored/wrapper twin retires when the emitted twin certifies:
`CorpusT1Exhibit` (the three-function wrapper) is retained as a
"regression" — a Q7 decision to make explicitly, not by default.

### 4.5 Verdict G2
LANDABLE WITH WORK (M): (i) the check into the gate; (ii) the independent
`BEq` cross-check; (iii) KOI A7's option-(a) sentence back (or a ruling);
(iv) the `mkAuxLemma` device named in ARCHITECTURE; (v) a decision on
retiring `CorpusT1Exhibit`. `docs/corpus-a7/` (Cabs JSON, reports, README)
is appropriate; `t2.cabs.json`/`t2.inspection.json` are metadata with no
theorem (fine, labelled).

## 5. G3 — E6 raw calls / scheduler / E7 multiple offers (14e7dc3 … 6c8e7e3)

### 5.1 What is proved (statements read verbatim)
All conclusions are over shipped engine functions: `drive_nonmemory_steps_aux2_lemFuel`,
`driver2_lemFuel`, `process_core_step2`, `find_can_advance`, `step_ctx`,
`liftCore_run`, `CerbND.runNDFuel`. E.g.
`driver2_ccall : runOne (driver2_lemFuel (Nat.succ fl) tds false) dst =
runOne (driver2_lemFuel fl tds false) {…post-call state…}` given the
per-thread loop's `[Step_ccall2 0 m]` and the lift; `driver2_many_all`
(outcome-list form): `(∀ o ∈ runNDFuel (n+1) (driver2_lemFuel (fl+1) …) dst,
P o) ∧ … ≠ []` from per-branch obligations — exactly the design's C.7
shape; `driver2_ccall_of_decomp` derives the call round from raw `Eccall`
syntax + evaluations + lookup/arity; `DriverDoneSeg` (a Prop over the two
engine loops, like `DriverDoneCtl`) with `.driver`, `.ccall`, `.driver_many`;
`wps_ccall_root`/`wpt_ccall_root` public rules; `Frag e true` admits
`ccall`/`unseq_single`; `advanceOffer?_step` proves the source-annotated
selector's projection equals `find_can_advance`. `CallReady` = the mirror's
`callRedexAt?` query ∧ (authored call ∨ `find_can_advance … = none`).

### 5.2 Referent rule
No hand-written driver/scheduler REPLACES an engine function in any
statement (checked all E6/E7 pins' types): `advanceOffer?`, `callSites`,
`CallReady` are side predicates proved equal/implied to the engine's
selection. But 32 of the 192 new pins have package DEVICES in their
statements — `Decomp` 9, `Redex` 13, `callRedex*` 6, `CallReady` 4,
`advanceOffer?` 5, `callSites`/`CallSite`/`rootCallSite?` 1 each,
`SeqRmwStep` 2, `DriverDoneSeg` 5, `DriverFinalCtl` 1 (list in §8 F5).
The 2026-09-03 standards-audit response (Audit.lean header) unpinned
exactly this class: "a lemma whose statement's referent is a package-
defined device is a proof device, not an export". `DriverDoneSeg`/
`DriverFinalCtl` are arguably contracts like `DriverDoneCtl` (keep); the
rest should be unpinned (the exhaustive sweep still bounds them). The
"958 pins" figure is inflated by them.

### 5.3 Is this the E6 the design ruled?
Design §C.6: `Step.ccall` mirror step certified by a `ccall_round`;
`DriverSafeSeg` (partial) + `SchedulerSafe`/`SchedulerDone` outer-fuel
induction; both closed forms restated over both loops; acceptance t2, t3,
t10 (t8 after). Branch: no `Step.ccall` mirror step (the judgments were
instead migrated to dispatch on the live query `callRedexAt?`); total
segment form and one-call composition exist; NO partial lane; NO outer
induction beyond one round/one fork; NO acceptance program; the manifest
rows are PROVISIONAL (honest). Then a design-level finding: the candidate
`Frag e true` is not closed under `Step` — kernel counterexample
`docs/2026-09-06_e6-call-fragment-counterexample.lean` (verified to
compile): `bound(letw _ = neg(store) in Eccall)` rewrites to an `unseq`
whose collector has TWO offers, so E6 cannot be finished without E7's
multiple-offer machinery. The agent then pulled E7 forward ([AGENT]
decision, labelled) and built seven more slices of scheduler equations.
That is a change of the ruled order (C.10: "E6 → E7") decided by the
agent under the charter's "resolve strategic choices itself" clause; the
CLAUDE.md rule is stronger: "Scope of any design-level pass is decided
WITH the operator". The finding is real and valuable; the response should
have been a stop-and-ask.

Cost of landing it now: `Step`, `wps`, `wpt` and `Frag` (core definitions
under the frozen spec) change shape (`callRedex? e` → `callRedexAt? M ρ e`
in 50 statements; `Frag`'s Bool index in 55) with no census, no capability
gained, and a candidate domain admitted to be unsound as a fragment.

### 5.4 Verdict G3
SPLIT — PARK the whole group on the branch (nothing in it is wrong; nothing
in it is finished). Before any E6 work resumes: an operator conversation
that absorbs the counterexample into the design (E6 ⊇ multiple offers, or
a sequentialised referent — a ruled question, DECISIONS Q1 said raw Core).

## 6. G4 — `seq_rmw` (567c578 … 19292c0)

### 6.1 Engine vs mirror (cite)
Engine: `generated/Core_reduction.lean` `step_ctx` SeqRMW arm —
`Step_action_request2 "SeqRMW" loc tid (is_unseq_with_ccall ctx) (… eval
pe1 pe2 → fresh_excluded_id → fresh_symbol0 → SeqRMWRequest2 ty ptrval
(fun mval => full_eval_pexpr th_st_tmp … pe3 with the binder bound to
(valueFromMemValue mval).2 in the head env → memValueFromValue …) (fun aid
fp mval mval' => … cval_e := (if with_forward then mval' else mval) … ))`;
`generated/Driver.lean:312` `action_request_sequential2`'s `SeqRMWRequest2`
arm: `loadM` → `liftCore_run (mk_mval' mval)` → `storeM … false …` → trace
`ME_seq_rmw`. (The old `core_action_step`'s `SeqRMW … => failwithI` at
`Core_run.lean:421` is not on the driver's path.) Mirror:
`step_ctx_seq_rmw_at` (Soundness:8930) states exactly that shape — the
`"SeqRMW"` request, both supply draws (`excluded_supply + 1`, `sym_supply
+ 1`), the temp-binder update evaluation, the forward/old selection, and
the `BOUND_NO_SSEQ` continuation `apply_ctx ctxB (wseq (tuple [unit, sym])
(unseq [DA_neg excl … unit; apply_ctx (add_exclusion excl ctxA) value])
(pure sym))`; `SeqRmwStep.run` derives both action paths and the
successor driver from the shipped request/processor equations. Kernel-
checked; faithful by inspection.

### 6.2 Rules
`wps_seq_rmw_bound`/`wpt_seq_rmw_bound` (cost 8): full-cell ownership,
trap exclusion, `StorableAt`, update evaluated with the binder bound to
the CURRENT bytes' loaded value, postcondition gets the fresh symbol
bound to `if forward then new else old` and the cell at
`memValueToBytes mv`. The public bound premise `negFree` was strengthened
and RENAMED `boundFree` (excludes positive SeqRMW under `bound`) — a
public-rule text change on `wps_bound`/`wpt_bound` and their tuple
variants; consumers (t4) repaired. `Frag`/`Decomp` still exclude positive
SeqRMW; the manifest and README say PROVISIONAL (the referent rule's
interim clause honoured). Corpus use: none (t2 needs it); the API-only
`Examples/SeqRmwSmoke` at both faces.

### 6.3 Verdict G4
Sound, faithful, honestly labelled, and it is E5's own missing item
(design §C.5 lists `seq_rmw` under E5; base cb46e4c has none). SPLIT: land
after re-cutting onto G1+G2 WITHOUT G3 (its `boundRedex?`/`seqRmwRedex?`
traversal was added on top of G3's `actionRedex?` refactor and
`callRedexAt?`; expect a real rebase). Census the `negFree`→`boundFree`
change. Size M.

## 7. G5 — the pause and the committed WIP patch

`docs/2026-09-06_seq-rmw-decomposition-wip.patch` (351 lines, zero-context,
applies cleanly with `--unidiff-zero` — checked) is a failing draft of the
`Redex.seq_rmw` decomposition arm. It is cited only by the pause record and
the charter, both saying "not capability evidence". Under the shop-window
doctrine `docs/` holds records and decisions; a failing patch is a scratch
artifact whose home is a branch (`wip/seq-rmw-decomposition`). REJECT in
`docs/`; branch it. The pause record itself is an adequate dated [AGENT]
record; its milestone table is the agent's assessment and says so.

## 8. G6 — DECISIONS, KOI, README, charter

- **DECISIONS**: 44 new `## 2026-09-06` entries, 1795 lines, all
  `[AGENT, active charter]`, one `[USER]` quote (the pause request). It is a
  build log in the rulings register: 35 occurrences of "no dispatch/merge/
  push", 48 of "goal remains active/not a park", per-commit pin counts,
  frontier failure lists. Provenance is honest — nothing is mis-tagged
  [USER]; the charter's "user has authorized" traces to the verbatim
  [USER] adoption entry of 2026-09-05 at base; "user-authorized executable
  boundary" traces to [USER 2026-09-04] Q3. Agent-called dispositions that
  the operator should read as such: (a) "generic ambient-one is outside
  the theorem domain" (M2 fuel-contract entry); (b) "[AGENT] Sequence
  adjustment within the charter" (seq_rmw before the raw-call migration);
  (c) "[AGENT] Bring the relevant E7 … machinery forward alongside E6"
  (the order change, §5.3); (d) the A7 startup-scout self-certification
  "This implementation choice remains within the adopted charter"; (e) the
  `axiomFreeExports` class. Collapse to ≤ 5 entries (re-pin; a7 t1; E6/E7
  parked with the counterexample finding and the order question; seq_rmw;
  pause) carrying the [AGENT] decisions above explicitly.
- **KOI** (74 lines changed): A1/A2/A4/A6 accurate at HEAD; A5 accurate;
  A7 accurate except the dropped option-(a) target (§4.2); B5 and B8 are
  bloated with E6/E7 progress prose and **B8's table row is malformed**
  (a fifth cell "| The [bound-guard integration] …" appended after the
  mover column); C19 fine; **E is stale** (quotes 889/6, 892/6, 902/6 —
  HEAD is 958/7 — and describes the agent's worktree layout).
- **README** (rewritten, −1140/+393): checked line by line against HEAD —
  the t1 path, the assumption table, the cost/fuel table (48/50, 915/917,
  88/90, 78/80 match the statements), the manifest counts (37/82/40/7/24/
  9/2), the PROVISIONAL wording, the A5/A7 caveats: accurate. "Warnings"
  unmentioned (fine).
- **Charter** (20 lines): status → "ADOPTED — execution paused"; M-rows
  turned into progress logs. The [AGENT] order change (§5.3) is not
  surfaced in the charter as a scope question.

## 9. Landing ORDER and the exact fixes before any merge ask

Order: **G1 → G2 → G4 (re-cut) → [park G3] → G5 off main → G6 with each.**
Each landing gets its own snapshot/census and one record; each is a
separate merge ask (per-merge sign-off, no carry-over).

F1 (G1) Signature census pre `cb46e4c` (generate it on the old pin from the
`dialect-e5` worktree, NOT from e5b) / post `520654f`, classified as in §2;
list the 35 removals and the allocator-contract statement changes.
F2 (G1) FUEL.md + ARCHITECTURE §4: the (D) paragraph — the eight remaining
reachable-ambient opaque-exhaustion rows at the pin (cite the C3 manifest
§3 / `scripts/fuel_forms_pending.txt`) and, per export family, the premise
that keeps it off them; the two design deviations named against
`2026-09-04_fuel-restatement-design.md` §3; `Acyclic` unused because
`tagDefs = ∅`.
F3 (G1) One re-pin record (the 17 `repin-*.md` become an appendix or go),
three change classes labelled (representation / fuel / allocator-memory);
squash the 13 red-frontier docs commits; delete the 17 `#print axioms`
listings in `docs/evidence/` (keep the three probes as one file); scrub the
34 `.tmp/repin-scout/` citations; fix Audit.lean's `10^8` narrative.
F4 (G2) `inspect-emitted-file.sh … --check-data` as a `test_unit.sh`
speedbump (≈10 s); a derived structural `BEq`/`DecidableEq` equality on
`EmittedFile.Data` beside the `toExpr` comparison; restore "option (a) is
the named target, not done" in KOI A7 (or a [USER] ruling); name the
`mkAuxLemma` kernel-certificate device in ARCHITECTURE; decide Q7 for
`CorpusT1Exhibit`.
F5 (G3/G4) Unpin the device-referent lemmas (leave under the sweep):
`step_ctx_ccall_eval`, `step_ctx_ccall_single`, `driver2_ccall_of_decomp`,
`DriverDoneSeg.ccall_of_decomp`, `driverDoneCtl_ccall`, `Decomp.frag_ccall`,
`driverDoneCtl_ccall_frag`, `step_ctx_excluded_store_at`, `step_ctx_load_at`,
`step_ctx_ccall_excluded_store`, `driver2_ccall_store_runNDFuel`,
`driver2_ccall_store_runND`, `step_ctx_if_true_ws_at`, `CallReady.of_frag`,
`CallReady.of_single_ccall`, `loop_step_call_ready`,
`driver2_call_ready_runNDFuel`, `advanceOffer?_step`, `advanceOffer?_at`,
`callSites_cases`, `loop_step_selected_offer`, `loop_step_no_selected_offer`,
`SeqRmwStep.run`, `SeqRmwStep.memWF`, `callRedexAt?_eq_of_ccallFree`,
`Decomp.callRedexAt?_ccall_iff`, `Step.boundFree_preserved` (the
`DriverDoneSeg.*`/`DriverFinalCtl.finalize` contracts may stay, argued).
F6 (G4) Re-cut the four seq_rmw commits onto G1+G2 (no `callRedexAt?`,
no `Frag` index); census the `negFree`→`boundFree` public premise change;
record it as E5's outstanding item closed.
F7 (G5) Move the WIP patch to a branch; drop it from the landing set.
F8 (G6) Collapse DECISIONS as in §8; fix KOI B8's row; refresh or delete
KOI E's running counts; trim B5/B8.
F9 (G3) Operator conversation, before any further E6 work: does E6 absorb
the multiple-offer machinery (the counterexample forces it for raw Core),
and is the [AGENT] E7-first reordering ratified?

## 10. Verified true (by measurement in the audit copy)

Gate green with the verbatim tail in §1; 958 distinct trio pins + 7
axiom-free pins; two package linter warnings at the stated lines; no fuel
numeral or retired constant in code; `letI` only inside proofs; closed
partial forms over `drive` at the ambient; `SymMap = Fmap.WF symCmpK`
through upstream `LemLibPmapLaws`; `killM_killed_inv` 7 rows; `Frag`
fuel-indexed with the operand bound; statement deltas of the headline
exports as tabulated; manifest no drift / corpus skeleton (t1/t4/t5/t6)
green / import direction 18 / boundary 33-0; oracle values for
t1/t2/t3/t10; the a7 inspector reproduces the committed fuel-50 report
exactly and the data round-trip matches; a7 modules elaborate in seconds;
all 27 committed evidence/probe `.lean` files compile; the WIP patch
applies (check only); SeqRMW engine arms located and compared to the
mirror statement; 32 device-referent pins counted; census numbers in §2.

## 11. Not checked

- Proof CONTENT of the 861 changed and 537 added theorems beyond their
  statements (the kernel did; I read statements).
- The quoter's faithfulness (`derive_file_to_expr.lean`) beyond reading
  its head and running the round-trip; the Cabs JSON's provenance beyond
  the committed hashes (I did not regenerate it from the oracle).
- A fresh cache-disabled rebuild of the package (warnings were read from
  Lake's replay of the primed cache).
- The E5 partial-face debts, WALKTHROUGH body, ARCHITECTURE prose
  accuracy beyond the fuel/A7 paragraphs and the three quoted theorems.
- Reachability, on the branch's proved paths, of the eight opaque-exhaustion
  engine rows (the theorems are kernel-true regardless; the request is the
  documented classification).
- Whether `CorpusT4/T5/T6Exhibit`'s 917/90/80 bounds are tight (nothing
  claims tightness; KOI B6).
- Anything on the primary checkout, other worktrees or `main`.
