# Range audit 5d08237..ebf9423 (AR5: readout + manifest) — 2026-09-04

**VERDICT: PASS WITH FIXES REQUIRED — grade A-.** The Lean change is exact
(three trio-exact lemmas, `DeadAt` moved verbatim, census ADDED 3 / REMOVED 3 /
CHANGED 0 re-derived, HEAD snapshot byte-identical, both production statements
unchanged, zero exhibit code names an internal). The manifest now says what it
checks and every plant in the brief went red as claimed. The fixes required are
all cheap and none touches a proof or the truth of a claim: two fail-open paths
in `scripts/boundary_check.sh`'s TSV reading (a malformed row becomes a silent
allowance; a missing trailing newline silently drops the last row — the second
is caught by no other gate), a DECISIONS gate quote labelled verbatim that is
truncated and elided, two stale prose sentences (README "at this writing" three
allowances; ARCHITECTURE "ten stale seeds"), and two engine-success shapes the
variant table does not classify (kill/free through a union-member pointer;
whole-object access at an atomic allocation). Fix list: C-1, C-2, R-1, R-2, R-3
required; C-3, C-4 required as table rows (data edit + regenerate); H-* optional.

Auditor: fresh, independent; standard `docs/AUDIT-BRIEF.md`. Copy:
`worktrees/audit-ar5-ebf9423` at `ebf9423` (detached), working tree clean at
start and at end (`git status --short` = only this report). Every lake/lean
invocation through `scripts/capped` (`grep -c uncapped` = 0 in every log). No
pass exceeded 2 minutes wall; the longest was the on-demand inventory (1m37s).
Quoted outputs are verbatim unless marked DERIVED. Provenance: every judgement
below is [AGENT] (this auditor).

## 0. What was audited, by measurement

- Range: `git log --oneline 5d08237..ebf9423` = the eight commits named in
  the brief (e9111d0, a40ba88, 5362dec, 5c2813b, fc7f071, 5355b15, 5e39386,
  ebf9423). Full diff read (`--stat`: 20 files, +31667/−409; the Lean diff is
  API.lean, Adequacy.lean, Audit.lean, DisposeExhibit.lean,
  MallocListExhibit.lean only).
- Documents read in full: AUDIT-BRIEF, KNOWN-OPEN-ITEMS, CLAUDE.md, the
  external audit, DECISIONS tail (~130 lines), both AR5 records, the
  generator, the inventory, the TSV, CAPABILITY_MANIFEST.md, CLAIMS.md,
  boundary_check.sh, test_unit.sh, the ARCHITECTURE/README/KOI diffs.
- Engine arms read at the pin (`.cerberus-ws/lean_frontend/generated/CerbMem.lean`):
  `allocateObject` :1844, `allocateRegion` :1873, `killM` :1895, `loadM`
  :1961, `storeM` :2007, `eqPtrval` :2106, `readonlyStatusForAlloc` :1830,
  `isAtomicMemberAccess` :1949. Mirror: `Frag` (Soundness.lean:4149–4320),
  `Step.store/load/create/alloc/kill/memop_ptreq` (Step.lean:1468–1600,
  1898–1917). Rules: all eleven `*_atomic` statements (Rules.lean:264–1508),
  `wps_memop_ptreq` (Wps.lean:2273). Bundles: `pointsToView` (Heap.lean:2714),
  `typedRegionView` :3481, `readonlyCell` :3683, `pointsToCell` :2749,
  `CellCoh` :358, `MetaCoh` :987, `allocCost` :2255, `regionCost` :2322.

## 1. Findings, ranked

Severity scale: High = a gap in the logic or its coverage; Medium = an
instrument that does not do what its header says, or a record/shop-window
statement that is false; Low = precision; Note = process/hardening.
No T- (trust/logic) finding.

### C-1 (Medium) `boundary_check.sh` is fail-OPEN on a malformed TSV row: a missing `internals-allow` cell is read as an ALLOWANCE

Premise verified by measurement: YES (plant, §3 P4).

Evidence. `scripts/boundary_check.sh:55` reads
`while IFS=$'\t' read -r module cls allow note; do`; with a 2-cell row `allow`
is the empty string, and `:72`/`:77` test `[[ "$allow" != "-" ]]` — the empty
string is "not `-`", so the module is allowlisted with an empty reason. Planted
(`LoopExhibit` row cut to two cells + a `CohG` mention in LoopExhibit.lean):

```
ALLOWLISTED: LoopExhibit — 1 internals mention(s): 
      LoopExhibit:550:  have := @CohG
ok:   RegionLoopExhibit — 0 internals mentions
BOUNDARY: 17 modules checked, 2 internals mention(s) in total, exit=0
```

The script's own header (`:34–37`) promises "EXIT: … 1 = … a malformed TSV".
In the FULL gate the manifest generator (which runs first and rejects
`cells.length != 4`, `capability_manifest.lean:294`) would go red, so the
gate as a whole is not fooled; standalone, and for anyone reading the
header, the check is fail-open. Under CLAUDE.md "fail-closed, fail-noisy"
this is a defect regardless of tier.

Fix (one line): after the `read`, `[[ -n "$cls" && -n "$allow" && -n "$note" ]] || { echo "boundary FAIL: $tsv: malformed row for $module (expected 4 TAB-separated cells)" >&2; fail=1; continue; }`
— or require the cell to be `-` or non-empty explicitly. Same pattern in
`scripts/test_unit.sh:71` (harmless there: a malformed core row only drops a
protected file; make it loud too).

### C-2 (Medium) `boundary_check.sh` and `test_unit.sh` silently drop the LAST TSV row when the file lacks a trailing newline — caught by no other instrument

Premise verified by measurement: YES (plant, §3 P5).

Evidence. Both scripts use `while IFS=$'\t' read -r …; done < "$tsv"`; bash's
`read` returns non-zero on the final unterminated line, so the loop body never
runs for it. Planted (LoopExhibit moved to the last row without `\n`, plus a
`CohG` mention in LoopExhibit.lean):

```
ok:   RegionLoopExhibit — 0 internals mentions
BOUNDARY: 16 modules checked, 1 internals mention(s) in total, exit=0
```

(17 → 16 modules; the planted hit is invisible; exit 0.) The Lean readers
(`splitOn "\n"`) parse the same file completely, so the manifest generator's
"complete and exact" check passes and NOTHING in the gate notices. Today the
file ends in `\n` (`tail -c1 | xxd` = `0a`) and the last row is
`DivergeExhibit` (exempt), so there is no present gap — but one careless edit
away, an exhibit disappears from the boundary check (and, in test_unit.sh, a
core module from the import-direction protected set) with a green gate.

Fix (one token each): `while IFS=$'\t' read -r module cls allow note || [[ -n "$module" ]]; do`
in both scripts.

### R-1 (Medium) The DECISIONS AR5-manifest entry's FULL-gate quote is labelled "verbatim" and is not

Premise verified by measurement: YES (diff of the register block against my
own gate log, §3 G1).

Evidence. `docs/DECISIONS.md:1937` "Orchestrator FULL gate at 5e39386 (64G
cap), verbatim". Against the runner's actual output at ebf9423 (which is
byte-for-byte the same tail as the register describes for 5e39386 — same
pins, same counts):

1. two lines are TRUNCATED mid-word with no ellipsis — `:1946` ends
   `… environment-depend` (the real line ends `environment-dependent)`),
   `:1954` ends `… found by this check at ar5-m` (the real line runs to
   `… removes the entry`);
2. the `info: CerberusHeapLang/Audit.lean:576:0: ` prefixes of the three
   sweep lines are stripped;
3. the two `cerberus-lean-proj env: …` lines the runner prints are elided;
4. the ALLOWLISTED hit line `      Exhibit:585:  icases (stateInterp_iff σ2 ns κs nt).mp $$ Hσ`
   is elided.

The AR5-readout entry (`:1899`) has (2) and (3) as well; the readout
record's own §8 quote keeps the prefixes and the env line. Under "Record
integrity. Quoted outputs are verbatim" (CLAUDE.md; memory: gate tails are
recorded verbatim), an edited quote labelled verbatim is a record defect even
when every fact in it is true — the truncations here look like a 200-column
terminal capture, which is exactly the failure mode the rule exists to catch.

Fix: re-paste both blocks from the log (or keep the edits and label them:
"prefixes/env lines elided; lines wrapped"). The verbatim tail at ebf9423 is
in §3 G1 below.

### R-2 (Medium) ARCHITECTURE §7 states "the ten stale seeds" — the measured count is SIX, corrected in this very range

Premise verified by measurement: YES.

Evidence. `cerberus-heaplang/ARCHITECTURE.md:665` "the ten stale seeds of the
F1 renaming are refreshed"; the manifest record §1 (fixed at fc7f071) says
"corrected here to SIX ([AGENT], measured as stated)", KOI §D registers the
erratum "10 → 6", and DECISIONS records the orchestrator's 10 as WRONG. The
shop-window core document carries the falsified number.

Fix: "the six stale seeds".

### R-3 (Medium) README describes allowances that no longer exist, in present tense

Premise verified by measurement: YES (`git log 5355b15..ebf9423 -- README.md ARCHITECTURE.md` is empty; the TSV has one non-`-` cell).

Evidence. `cerberus-heaplang/README.md:823–825` "at this writing the
dead-object readout helpers of `DisposeExhibit`/`MallocListExhibit`, being
relocated, and `progA_wpt` in `Exhibit`". At HEAD the helpers are deleted
(e9111d0), the two allowances dropped (5355b15), and the gate prints ONE
ALLOWLISTED line. `ARCHITECTURE.md:646` "at the landing three: …" is framed
historically but the landing tree (this range's head) has one; a reader of
the core document is told the wrong number.

Fix: README — "at this writing one: `progA_wpt` in `Exhibit` (KOI C8)";
ARCHITECTURE — "at the manifest slice's landing three …; after the readout
slice landed, one".

### C-3 (Medium, coverage of the instrument) Two engine-admitted SUCCESS shapes have no row

Premise verified by measurement: YES (engine arms and bundles read; rows
enumerated). Both are exactly the class the external audit's Finding 1
complained about; the header's "not exhaustive" disclaimer covers them but a
table that claims to be "the engine-SUCCESS shapes of every `Frag`
constructor, read off … `killM` … arms" should have them.

(a) **Kill/free through a union-member pointer.** `killM` (CerbMem.lean:1905)
matches `.PV (.Prov_some allocId) (.PVconcrete _ addr)` — the member is
ignored — so `kill(static, p)` / `free(p)` at `PVconcrete (some membr) base`
succeeds exactly as at `none`. `Frag.kill` (Soundness.lean:4187) admits any
`pv`; `Step.kill` (Step.lean:1578) is generic in `pv`. `kill_atomic`
(Rules.lean:1204) consumes `pointsToCell pv …` whose body forces
`pv = cellPtr id a = PV (Prov_some id) (PVconcrete none a)` (Heap.lean:2749,
:166); `free_atomic` (:1502) is stated at `cellPtr id a`. So: engine success,
in the fragment, mirrored, NO rule — and no row. The slice added the
union-member rows for `store` and `load` (manifest rows at
CAPABILITY_MANIFEST.md:87, :93) and stopped one constructor short.

(b) **Whole-object load/store at an ATOMIC allocation.** `isAtomicMemberAccess`
(CerbMem.lean:1949) is `false` when the access is the whole object with the
allocation's own type, so `loadM`/`storeM` at an atomic-typed allocation
succeed in that case. No bundle can describe such an allocation
(`CellCoh.nonAtomic`, Heap.lean:363; `MetaCoh.nonAtomic`, :991), and the
`create` of an atomic type is a NO-RULE row — but the ACCESS is a separate
engine-success shape of `Frag.load`/`Frag.store` (reachable from a seeded
memory or an authored pointer literal) that the load/store rows do not
classify. Two NO-RULE rows (or one sentence in the atomic-`create` row's
reason: "and the whole-object accesses to such an allocation, `loadM`/`storeM`
at `isAtomicMemberAccess = false`, have no rule either").

Checked and found CORRECT (for the record, so nobody re-derives it): type
punning at an in-bounds offset is covered by the sub-range rows
(`pointsToView` admits any `off`, `vty` with `off + sizeof vty ≤ sizeof aty`,
Heap.lean:2717); non-positive alignment at `create` is covered
(`allocCost … al.toNat.max 1` mirrors `allocateObject`'s `alignN.toNat.max 1`);
`readonlyStatusForAlloc pref none = IsWritable` (CerbMem.lean:1841), so no
prefix makes a `Frag.create` cell read-only; the zero-cost `alloc` row's
`n ≤ 0 ∧ al ≤ 1` is exactly `regionCost = 0` (Heap.lean:2322); store at a dead
allocation is a kill (`killM` erases the record, `storeM` :1992 `none →
fail`); `Frag.memop_vals` at non-pointer values is a kill.

### C-4 (Low, precision) The function-vs-concrete `PtrEq` NO-RULE row over-claims the absence; the RULE row's enumeration is incomplete

Premise verified by measurement: YES (`eqPtrval`, CerbMem.lean:2106–2131).

Only `PVfunction (Symbol _ _ (SD_Id _))` against a concrete pointer reads
`funptrmap` (:2113–2119). A function pointer whose symbol description is not
`SD_Id`, against a concrete pointer, is the state-independent `false` arm
(:2120) and IS covered by `wps_memop_ptreq`'s `∀ σ` premise; `null` against a
function pointer is `false` (:2109), also covered, and not in the RULE row's
list ("null/null, null/concrete, function/function, same-provenance
concrete pair", CAPABILITY_MANIFEST.md:115). Conservative direction (a covered
shape labelled NO-RULE), so Low. Fix: RULE row shape "… null/any,
function/function, function(non-`SD_Id`)/concrete, same-provenance concrete
pair"; NO-RULE row "`PtrEq` at an `SD_Id`-named FUNCTION pointer against a
CONCRETE pointer (reads `funptrmap`)". KOI B14's seventh variant is
confirmed with this sharpening; the other six are confirmed exactly (§2.2).

### H-1 (Note) Comment stripping is not string-literal-aware

Premise verified by measurement: YES (plant §3 P3: a `"--"` literal hid a
`CohG` on the same line; a `"/-"` literal swallowed the following lines up to
a `"-/"` literal; `LoopExhibit — 0 internals mentions`, exit 0). No subject
module contains a string literal with `--`, `/-` or `-/` today (grep over the
17 subject files: zero hits), so nothing in the tree is hidden. Adversarial
shape; the header already says TEXT-BASED. Optional: strip `"…"` literals
before comments, or add the limitation to the header sentence.

### H-2 (Note) The allowance is per-module, so a SECOND hit in `Exhibit` would print under ALLOWLISTED without turning red

Acceptable under the speedbumps ruling and disclosed in the header ("CURRENT
hits tolerated"). Cheap tightening if wanted: an optional expected count in
the cell (`1: reason`) — red when the count grows.

### H-3 (Note) The class vocabulary's definition of `production-wrapper` is not the criterion that separates the modules

`module_classes.tsv:24` defines it as "closed statements over the shipped
pipeline (root-of-trust lane)"; but `DisposeExhibit`, `RegionLoopExhibit`,
`MallocListExhibit`, `FibRecExhibit` carry such statements
(`*_certified_production`, CLAIMS C3) and are `positive-client`. The
operative criterion — "its rule use is entirely through the positive clients
it imports" — is in the parenthesis; make it the definition. Classification
itself is exact (39 files = 39 rows, measured).

### H-4 (Note) `Audit.lean` pins `deadObj_dead`/`deadRegion_dead` (:325, :390) while API.lean now lists them below the line

The readout record flagged it (§9); KOI C10 owns it. Consistent with their
actual role: the only remaining consumers are the two public faces
(`grep` over the package: no exhibit names them in code; one prose mention
DisposeExhibit.lean:938). Pins track exports, the API line tracks clients —
say which the pin list means, or unpin.

### H-5 (Note) Record hygiene, minor

The manifest record §4 quotes `keep_pure` as having "eight consumers in
MallocListExhibit" — 10 textual mentions (DERIVED, `grep -c`); trivia. The
record's branch hashes `3f21303`, `56e1fed` are reachable objects in this
repository (checked) — fine.

## 2. What was verified and held (the positive record)

### 2.1 The Lean change

- `#print axioms` at HEAD (capped `lake env lean`, 1.2 s), verbatim:
  ```
  'CerberusHeapLang.deadObj_consequence' depends on axioms: [propext, Classical.choice, Quot.sound]
  'CerberusHeapLang.deadRegion_consequence' depends on axioms: [propext, Classical.choice, Quot.sound]
  'CerberusHeapLang.bigSepL_consequence' depends on axioms: [propext, Classical.choice, Quot.sound]
  'CerberusHeapLang.deadObj_dead' depends on axioms: [propext, Classical.choice, Quot.sound]
  'CerberusHeapLang.deadRegion_dead' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```
  All three pinned in `Audit.lean:565–566`; gate prints `376 trio-exact`.
- Statements sensible: `bigSepL_consequence` is the right generic fold
  (pure conclusions duplicate under `∗`; induction on the list through
  `sep_consequence`); the two token faces are `deadObj_dead`/`deadRegion_dead`
  re-shaped to the projection obligation `Φ ∗ metaInterp ∗ byteInterp ⊢ ⌜…⌝`
  under `CohG`, dropping the unused byte interpretation — the same shape as
  `cellOwn_consequence`. Nothing is weaker than what the exhibits had.
- `DeadAt`: `git show 5d08237:…DisposeExhibit.lean` :909–910 vs
  Adequacy.lean:1900–1901 — identical name, binder names, type, body
  (`#print` at HEAD: `fun σ id => σ.deadAllocations.contains id = true ∧ σ.allocations.get? id = none`).
- Census re-derived independently (entries split on `----`, sorted, diffed by
  whole entry): pre 2971 entries, post 2971 entries; exactly 3 `>` lines
  (`bigSepL_consequence`, `deadObj_consequence`, `deadRegion_consequence`)
  and 3 `<` lines (`deadNodes_dead`, `deadObj_dead_keep`, `deadRegions_dead`);
  hence CHANGED 0 and `dispose_list_certified_production` /
  `malloc_list_certified_production` byte-identical (DERIVED from the diff).
- HEAD snapshot regenerated (`signature_snapshot.lean`, 13.9 s):
  `cmp` → `SNAPSHOT-BYTE-IDENTICAL`, sha1 `71f51e04f3bc13f35d66301d7021bef84c095e97` both files.
- Exhibits through public lemmas only: the two readouts bind `hG` and pass it
  to `deadObj_consequence`/`deadRegion_consequence`/`cellsOwn_consequence`;
  no `CohG`/`metaInterp`/`byteInterp` text remains in any positive client
  (boundary check 0 hits ×16; inventory `Ghost-direct` in every client is
  exactly the `*_readout` theorem whose STATEMENT carries the projection's
  `hpost` type — the documented exception). `progA_wpt` (Exhibit.lean:585,
  `stateInterp_iff`) is the one genuine crossing, consumerless, allowlisted,
  KOI C8 — correctly recorded.
- Reclassification of `deadObj_dead`/`deadRegion_dead` below the line:
  consistent with their role (H-4).
- No new linter warnings: the gate log's 62 package warnings are in files
  this range did not touch; zero in Adequacy/DisposeExhibit/MallocListExhibit/
  Audit/API.

### 2.2 The manifest as a coverage instrument

- Header paragraph "WHAT GREEN ESTABLISHES / DOES NOT ESTABLISH": each of the
  five numbered claims corresponds to a check in the generator (constructor
  cover :426–433; theorem existence :472–488; consumer cone :465–470 and
  :495–513; module classification :409–420; claims names :527–547), and each
  disclaimer is true. No over-claim found; the one under-claim is that it does
  not mention the plant-confirmed "RULE-TOTAL-UNDEMONSTRATED turns red when a
  consumer appears" property (it is in the class description; fine).
- 47 rows, 23 constructors (counted against `Frag`'s constructor list: 23).
  RULE rows traced (5 + the total-rule cone): `Frag.alloc_op`
  (`wps_alloc_eval`/`wpt_alloc_eval` — AllocExhibit), `Frag.call` root/context
  (CallSmoke, FibRecExhibit), `Frag.store` region (`wps/wpt_store_region_at`
  — MallocListExhibit), `Frag.kill` static (`wps_kill` — AllocExhibit,
  DisposeExhibit; `wpt_kill` — DisposeExhibit), `Frag.if_` true/false; each
  named theorem exists (the generator resolves all; my plants confirm the
  resolver is live), and the consumer lists are the cones' output.
- NO-RULE rows against the engine and the rules' hypotheses: locking store
  (`storeExpr` = `Store0 false`, Rules.lean:67; `storeM` `isLocking` arm
  :2032), union-member store/load (bundles fix `cellPtr`, `storeM`/`loadM`
  admit `PVconcrete unionMem`), read-only load (`load_atomic_readonly` exists,
  no `wps_`/`wpt_` face: grep of Wps/Wpt for `readonly` = 0), zero-size create
  (`.max 1`, `hsz`), atomic create (`hatom`; `allocateObject` does not check),
  non-inert create (`hinert`, a rule premise — stated as such), static kill
  of a region (`killM` short-circuits `dynamicAddrs` at `isDynamic = false`),
  `free(NULL)` (`PVnull` arm), colliding `free` (KOI A3), zero-cost alloc,
  function-vs-concrete `PtrEq` (C-4 sharpening). B14's seven: six exact, one
  sharpened.
- OUT-OF-SCOPE rows: each cites an existing record (`fragment-closure-notes`,
  `c2-notes`) and a real residual/absence (`OpenRound.run_surplus`,
  `OpenRound.eval_uncovered`, `BareHead`, `memop_fork`, `callRedex?`).
- Missed shapes: C-3 (two). Everything else I could construct from the arms
  is classified (§C-3 "checked and found CORRECT").
- Hand-maintained data in one place: `variants` (generator :101–271) and
  `module_classes.tsv`; unclassified constructor → red (plant P-e2).

### 2.3 Fail-closedness (plants: §3)

(a) red; (b) hard failure, no measurement printed; (c) red; (d) red;
(e) red; (f) comment-only ignored, exit 0; (f′) string-literal hazard — H-1;
malformed row — C-1; missing trailing newline — C-2; unknown class — red.

### 2.4 Module classification and the consumer set

39 `.lean` files under `CerberusHeapLang/` = 39 TSV rows (set-identical,
measured); every row 4 cells. 18 → 16: from `git show 5d08237:…CAPABILITY_MANIFEST.md`
the only row naming a dropped module was `wps_store_eval` (ProdExhibit)
and it keeps four other consumers; the old manifest tracked partial rules
only, so I probed the totals directly (§3 P-d′): with ProdExhibit,
ProdLoopExhibit and DivergeExhibit re-added as consumers (19), the three
RULE-TOTAL-UNDEMONSTRATED rows are still "consumed by NO consumer module" and
`0 red` — no rule, partial or total, lost its only consumer.

### 2.5 CLAIMS.md

86 names checked by the generator (plant P-e3 confirms the check is live).
Kinds against the snapshot: C3 "total — closed equation" ✔
(`dispose_list_certified_production`: `runND … = [(Active dres, [], dst')] ∧ …`,
no fuel hypothesis); C4 partial closed form ✔ (`fib_rec_certified`:
`Killed dst' fuelExhaustedKill ∨ ∃ dres, …` at every `fuel`;
`prod_run_safe_procs` likewise); C5 semantic negative ✔
(`diverge_total_unprovable : … → False`; `dg_loop_exhausts` an engine fact);
C2 projected ✔ (`semantic_frame`'s conclusion `SemTriple` is Iris-free);
C7 ✔ (`MemWF.storeM` has `lk : Bool` free; `MemWF.killM` `isDyn` free;
`MemWF.allocateObject` `initOpt` free — "either locking mode / both kill
arms / any initializer" are literally true); C8 `semantic_frame` consumed by
Exhibit ✔ (Exhibit.lean:398). Exclusions point at KOI entries that exist
(A1–A3, A5, A6, B1–B8). Eight closed statements in C3: counted 8 ✔.

### 2.6 Prose and records

- `grep -rn '0 red' --include='*.md' --include='*.lean'`: outside dated
  records and DECISIONS quotes, the phrase survives only as "the former …
  reading is withdrawn" (ARCHITECTURE.md:616, README.md:125,
  capability_manifest.lean:8) and as the machine line's red-count
  (CAPABILITY_MANIFEST.md:126, correct usage). No stale coverage reading.
- KOI B11 (21 + 26 `⊤` sites): `grep -c '⊤'` = Wps 21, Wpt 26 ✔. B12, B13,
  B14 (see C-4), C8, C9 (API.lean:18–20 still names the inventory as the
  instrument ✔), C10 accurate; §E's expected tail matches §3 G1.
- DECISIONS chronological (the range appends 2026-09-04 entries after
  2026-09-03) ✔; counts in the two records (pins 373 → 376; 15 code hits →
  0; 47/27/3/0/12/5; 16 consumers; 17 modules checked; 39 rows; 132 rule
  theorems / 24 seeds / 16 clients) all re-measured ✔.
- The external audit is claimed "committed verbatim, `cmp`-identical" against
  an untracked file in the primary checkout — NOT verified here (out of this
  copy).

## 3. The plant log (verbatim; each plant reverted with `git checkout --`, `git status --short` clean of tracked changes after every plant; the FULL gate re-run on the reverted tree at the end — G2)

P1 — `CohG` injected into `LoopExhibit.lean` (positive-client, no allowance):
```
FAIL: LoopExhibit — 1 internals mention(s) in a positive-client module (no allowance):
      LoopExhibit:550:  have := @CohG
ok:   RegionLoopExhibit — 0 internals mentions
BOUNDARY: 17 modules checked, 2 internals mention(s) in total, exit=1
```
P2 — the same names in a block comment, a `--` comment and a docstring only:
```
ok:   LoopExhibit — 0 internals mentions
ok:   RegionLoopExhibit — 0 internals mentions
BOUNDARY: 17 modules checked, 1 internals mention(s) in total, exit=0
```
P3 — appended `def plantStr_audit : String := "--" ; theorem plant_hidden_audit : True := by have := @CohG; trivial`, then `def plantStr2_audit : String := "/-"`, `theorem plant_hidden2_audit : True := by have := @metaInterp; trivial`, `def plantStr3_audit : String := "-/"` (H-1):
```
ok:   LoopExhibit — 0 internals mentions
ok:   RegionLoopExhibit — 0 internals mentions
BOUNDARY: 17 modules checked, 1 internals mention(s) in total, exit=0
```
P4 — LoopExhibit's TSV row cut to `CerberusHeapLang.LoopExhibit\tpositive-client` + the P1 mention (C-1):
```
ALLOWLISTED: LoopExhibit — 1 internals mention(s): 
      LoopExhibit:550:  have := @CohG
ok:   RegionLoopExhibit — 0 internals mentions
BOUNDARY: 17 modules checked, 2 internals mention(s) in total, exit=0
```
P5 — LoopExhibit's row moved to the end of the TSV with no trailing newline + the P1 mention (C-2):
```
ok:   RegionLoopExhibit — 0 internals mentions
BOUNDARY: 16 modules checked, 1 internals mention(s) in total, exit=0
```
P6 — class misspelt `positive-clint`:
```
boundary FAIL: cerberus-heaplang/scripts/module_classes.tsv: module CerberusHeapLang.LoopExhibit has unknown class 'positive-clint'
ok:   RegionLoopExhibit — 0 internals mentions
BOUNDARY: 16 modules checked, 1 internals mention(s) in total, exit=1
```
P-c — RULE row total `wpt_alloc_eval` → `wpt_alloc_eval_plant` (generator, capped `lake env lean`, ~8 s):
```
generator exit=1
| `Frag.alloc_op` | `Alloc0` at `PePure` operands (not all values) evaluating to INTEGERS (the ACTION_EVAL round) | RULE | `wps_alloc_eval` — AllocExhibit | `wpt_alloc_eval_plant` — **RED: not in the environment** | |
MANIFEST: 23 constructors, 47 variant rows (27 RULE, 3 RULE-TOTAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 12 NO-RULE, 5 OUT-OF-SCOPE), 1 red, 16 consumer modules
scripts/capability_manifest.lean:402:0: error: capability manifest: 1 red finding(s) — see the table and PROBLEMS above
```
P-d — `wpt_case_value` row reclassified `.rule`:
```
generator exit=1
| `Frag.case_value` | `case v of pats` at a VALUE scrutinee with a matching pattern (the substitution TAU) | RULE | `wps_case_value` — CaseExhibit | `wpt_case_value` — **RED: consumed by no consumer module** | |
MANIFEST: 23 constructors, 47 variant rows (28 RULE, 2 RULE-TOTAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 12 NO-RULE, 5 OUT-OF-SCOPE), 1 red, 16 consumer modules
scripts/capability_manifest.lean:401:0: error: capability manifest: 1 red finding(s) — see the table and PROBLEMS above
```
P-e — `TreeRotExhibit` row deleted from the TSV:
```
generator exit=1
MODULES: 38 classified, 15 consumer modules (…)
MANIFEST: 23 constructors, 47 variant rows (27 RULE, 3 RULE-TOTAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 12 NO-RULE, 5 OUT-OF-SCOPE), 1 red, 15 consumer modules
- **RED**: module `TreeRotExhibit` is in the environment but NOT classified in scripts/module_classes.tsv
scripts/capability_manifest.lean:402:0: error: capability manifest: 1 red finding(s) — see the table and PROBLEMS above
```
P-e2 — row constructor `Frag.wseq` → `Frag.wseq_plant`:
```
generator exit=1
MANIFEST: 23 constructors, 47 variant rows (27 RULE, 3 RULE-TOTAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 12 NO-RULE, 5 OUT-OF-SCOPE), 2 red, 16 consumer modules
- **RED**: constructor `Frag.wseq` has NO variant row (MISSING — classify it)
- **RED**: variant row names `Frag.wseq_plant`, not a constructor of `Frag` (stale row)
scripts/capability_manifest.lean:402:0: error: capability manifest: 2 red finding(s) — see the table and PROBLEMS above
```
P-e3 — CLAIMS.md C2 `project_triple_pure` → `project_triple_pure_plant`:
```
generator exit=1
CLAIMS: 11 claim rows, 86 declaration names checked
- **RED**: docs/CLAIMS.md C2: `project_triple_pure_plant` is not in the environment
scripts/capability_manifest.lean:402:0: error: capability manifest: 1 red finding(s) — see the table and PROBLEMS above
```
P-d′ (probe, not a plant) — ProdExhibit, ProdLoopExhibit, DivergeExhibit reclassified `positive-client`:
```
generator exit=0
| `Frag.load` | … | RULE-TOTAL-UNDEMONSTRATED | `wps_load` — Exhibit, StructExhibit | `wpt_load` — exists, proved, consumed by NO consumer module | …
| `Frag.case_value` | … | RULE-TOTAL-UNDEMONSTRATED | `wps_case_value` — CaseExhibit | `wpt_case_value` — exists, proved, consumed by NO consumer module | …
| `Frag.wseq` | … | RULE-TOTAL-UNDEMONSTRATED | `wps_wseq` — WseqExhibit | `wpt_wseq` — exists, proved, consumed by NO consumer module | …
MANIFEST: 23 constructors, 47 variant rows (27 RULE, 3 RULE-TOTAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 12 NO-RULE, 5 OUT-OF-SCOPE), 0 red, 19 consumer modules
```
P-b — stale seed `CerberusHeapLang.engine_adequacyU` appended to `exportSeeds` (1.85 s wall; the whole output):
```
cerberus-lean-proj env: switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_opam, git redirects active
scripts/parametric_inventory.lean:274:0: error: parametric_inventory FAIL: export seed `CerberusHeapLang.engine_adequacyU` is not a declaration of the built environment (stale configuration — refresh it)
inventory plant exit=1
```
Inventory at HEAD, unplanted (1m37s wall; last line, and the client lines
matched the record's sample exactly):
```
INVENTORY: 132 rule theorems, 24 export seeds (all resolved), 16 client modules
```

G1 — FULL gate at ebf9423, first run (18 s wall, replay build; `grep -c uncapped` = 0, `grep -c 'uses sorry'` = 0), the runner's own lines verbatim (the ~3060 replayed warning lines between the gate-2 header and the sweep are elided here, said so):
```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
cerberus-lean-proj env: switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_opam, git redirects active
info: CerberusHeapLang/Audit.lean:576:0: CerberusHeapLang export pins: 376 trio-exact
info: CerberusHeapLang/Audit.lean:576:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (3396 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:576:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (5153 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (456 jobs).
ok: cerberus-heaplang build green
== speedbump: rule-use and classification manifest (regenerate; red on a red row or drift) ==
cerberus-lean-proj env: switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_opam, git redirects active
ok: capability manifest regenerated, no drift
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — 15 core modules, none imports an exhibit/example/production module
== speedbump: client boundary (positive clients mention no logic internals; scripts/boundary_check.sh) ==
ALLOWLISTED: Exhibit — 1 internals mention(s): `progA_wpt` (Exhibit.lean, the raw-WP readout of exhibit (a) at the total judgment) opens `stateInterp_iff` directly — found by this check at ar5-manifest 2026-09-04; `progA_wpt` is consumerless since F1 (docs/KNOWN-OPEN-ITEMS.md C3), its deletion or a rewrite over the public `stateInterp_readout` removes the entry
      Exhibit:585:  icases (stateInterp_iff σ2 ns κs nt).mp $$ Hσ
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
ok:   Examples.CallSmoke — 0 internals mentions
ok:   Examples.ReadinessSmoke — 0 internals mentions
ok:   Examples.Layout — 0 internals mentions
BOUNDARY: 17 modules checked, 1 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
scripts/test_unit.sh  15.48s user 1.43s system 94% cpu 17.794 total
EXIT=0
```
(`EXIT=0` is my `echo "EXIT=$?"`.) Line-by-line against the DECISIONS
5e39386 block: identical in every fact; the register's block differs as
R-1 lists (two truncations, `info:` prefixes stripped, env lines and the
`Exhibit:585` hit line elided).

G2 — FULL gate re-run after every plant was reverted (rebuild-after-revert):
identical verdict lines — `376 trio-exact`, `Build completed successfully (456 jobs).`,
`ok: capability manifest regenerated, no drift`, `ok: import direction — 15 core modules …`,
`BOUNDARY: 17 modules checked, 1 internals mention(s) in total, exit=0`,
`ALL GATES GREEN`, exit 0; `grep -c uncapped` = 0; `grep -c 'uses sorry'` = 0.
(Lake's content hashing made the reverted `LoopExhibit.lean` a replay, as
expected: the file is byte-identical to HEAD.)

## 4. What I did NOT check

- The `cmp`-identity of the committed external audit against the primary
  checkout's untracked copy (outside this copy; not verified).
- The pre-range tree was not rebuilt: "no new linter warnings" is from the
  absence of warnings in the five touched files at HEAD, not a before/after
  diff of warning counts (the log's 62 package warnings vs KOI C5's 66 is a
  replay-vs-full-build artefact I did not chase).
- The proof terms of the exhibits beyond what the inventory reports (the
  `Ghost-direct` = 1 readings are the projection hypotheses' TYPES; I did
  not open each `*_wp_readout` term).
- Exhaustiveness of the variant table beyond the six engine functions the
  generator header names; I did not survey `Core_reduction`'s other arms.
- iris-lean's `bigSepL` definitions (the `rfl` unfoldings compiled, which is
  the check).
- DECISIONS entries earlier than the range's tail (only chronological order
  of the appended entries).

## 5. Derived tallies (all DERIVED)

Range: 8 commits; 20 files; Lean diff 5 files. Snapshot: 2971 → 2971
entries, +3/−3. Pins 373 → 376. Manifest: 23/47 = 27+3+0+12+5; consumers
16 (probe at 19: same red set, 0). TSV: 39 rows × 4 cells; 39 files.
Boundary check: 17 subjects, 1 allowlisted hit. Plants: 13 (6 shell, 5
generator, 1 inventory, 1 probe); every plant behaved as the records claim
except the two fail-open paths (C-1, C-2) and the string-literal hazard
(H-1), none of which the records claim to cover. Build cost this audit
(DERIVED from `time`): two FULL gates 17.8 s + ~18 s (replays), snapshot
13.9 s, axioms 1.2 s, six generator runs ≈ 8 s each, inventory 97 s + 1.9 s;
no pass approached the tripwire.
