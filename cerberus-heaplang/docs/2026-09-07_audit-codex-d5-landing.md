# Pre-merge range audit: `codex/demo-residuals` (1e1f584..cdaf189) — the D6 revert, the D5 partial clients, the L2 adaptation

**VERDICT: PASS WITH FIXES** — the Lean content is clean and lands as claimed;
two fixes are required before/at the merge, both docs-only: (F-1) an erratum
in the record for the manifest hunk the rebase dropped (two landed commits are
not gate-green as committed, and the record's two sections silently contradict
each other on it), and (F-2) the shop-window/KOI lines that become false the
moment this merges (ARCHITECTURE §7 "E5's seven new rule rows are
RULE-PARTIAL-UNDEMONSTRATED", README's "40 RULE / 7 RULE-PARTIAL-UNDEMONSTRATED /
twenty-five modules", KOI C19/B20/E) — the charter assigns these to the
orchestrator's landing, so they must ride in the landing commit, not after.

**GRADE: A−** — three trio-exact, non-vacuous theorems whose statements say what
the record says, every one of the seven partial faces reached from a PINNED
public theorem (not merely from a private helper), zero forbidden constructs,
snapshot census exact to the entry; marked down for a record that, after the
orchestrator's rebase, describes a committed manifest that two landed commits
do not contain, and for the front-doc staleness the merge would introduce.

Auditor: fresh, no prior context. Worktree
`/home/dev/projects/cerberus-lean-proj/refined-cerberus/worktrees/codex-residuals`,
HEAD `cdaf189`, main `1e1f584` (verified ancestor). Read in order: `CLAUDE.md`,
`docs/AUDIT-BRIEF.md`, `docs/KNOWN-OPEN-ITEMS.md`,
`docs/2026-09-07_codex-charter-demo-residuals.md`,
`cerberus-heaplang/docs/2026-09-07_codex-residuals-notes.md`,
`cerberus-heaplang/ARCHITECTURE.md`. No tracked file edited, nothing committed,
no `lake build`. Every quoted output below is verbatim; every tally I computed
is labelled DERIVED.

**Deviation disclosed.** The brief asked for Lean scratch files under `/tmp`.
In this sandbox a file written to `/tmp` by one shell is unreadable by the next
(`head: cannot open '/tmp/audit_d5_axioms.lean' for reading: Permission denied`
— the same quirk the adaptation record notes for `/tmp/d5b-build1.log`). I
therefore placed the scratch files under the gitignored
`cerberus-heaplang/.lake/audit-scratch/` (`.gitignore:2:/cerberus-heaplang/.lake`),
ran them through `CERB_MEM_MAX=40G ../scripts/capped ~/.elan/bin/lake env lean`,
and deleted the directory afterwards. `git status --short` is empty before and
after. No build was triggered (`lake env lean` on a standalone file loads the
existing `.olean`s only).

## Findings table

| id | severity | where | claim | how verified |
|---|---|---|---|---|
| F-1 | **Medium** (record accuracy; two landed commits not gate-green as committed; no trust impact at HEAD) | `cerberus-heaplang/docs/2026-09-07_codex-residuals-notes.md:150–161` vs `:451–457`; commits `62685e1`, `56e9d39`; `docs/DECISIONS.md` entry added at `1e1f584` | Codex's original D5 commit `77c237d` DID carry the regenerated `CAPABILITY_MANIFEST.md` (61 lines; 47 RULE / 0 undemonstrated). The orchestrator's rebase resolved the conflict by taking main's file, so the landed D5 commits `62685e1`/`56e9d39` carry a manifest with 7 `RULE-PARTIAL-UNDEMONSTRATED` rows while their generator has 0 — the manifest speedbump would be red at either commit, yet both messages say "FULL gate green; 0 undemonstrated rows". The record's D5 section says the manifest was regenerated (true of `77c237d`), the adaptation section says "the D5 commit `98335e2` carries no manifest change" (true of the rebased commit), and neither explains the other; main's DECISIONS entry says "manifest regenerated" at the rebase, which the rebased tree `df5dc90` contradicts. Final HEAD is correct (`dc1bf00` regenerated it; 0 undemonstrated rows measured). | `git show --stat 77c237d` (7 files incl. the manifest) vs `git show --stat 62685e1` (6 files, no manifest); `git show 62685e1:…/CAPABILITY_MANIFEST.md \| grep -c 'RULE-PARTIAL-UNDEMONSTRATED \|'` = 7; `git show 62685e1:…/capability_manifest.lean \| grep -c 'rulePartialUndemonstrated (N'` = 0; HEAD = 0 rows. |
| F-2 | **Low** (shop-window accuracy at merge; docs-only) | `cerberus-heaplang/ARCHITECTURE.md:889–893`; `cerberus-heaplang/README.md:128`, `:141–142`; `docs/KNOWN-OPEN-ITEMS.md` C19, B20, §E | After the merge main's front documents state facts the tree no longer has: "E5's seven new rule rows are RULE-PARTIAL-UNDEMONSTRATED … no partial corpus derivation consumes their twins yet"; "twenty-five modules classified positive-client/declared-smoke"; "40 RULE, 0 RULE-TOTAL-UNDEMONSTRATED, 7 RULE-PARTIAL-UNDEMONSTRATED"; KOI C19 still lists the seven faces as open, B20 says "three clients touched" (now four: `PartialClients` also discharges by `symOrd_ne_eq_of_num_ne`), §E's expected gate tail reads 901 pins / 483 jobs / 29 modules (now 904 / 484 / 30). The charter (§3, §4) reserves the docs pass for the orchestrator's landing — it must be in the landing commit. | `grep -n "UNDEMONSTRATED\|twenty-five" README.md ARCHITECTURE.md`; HEAD manifest tail `47 RULE … 0 RULE-PARTIAL-UNDEMONSTRATED … 26 consumer modules`. |
| F-3 | Low (hygiene) | `cerberus-heaplang/docs/2026-09-07_codex-D6-post.txt`, `…D5-pre.txt`, `…D5-post.txt`, `…D6-pre.txt` | Three byte-identical 2.6 MB snapshots now sit in the tree (`D6-post` ≡ `D5-pre` ≡ the pre-existing `l1-signatures-post.txt`, SHA-256 `1b7d097d…`); `D5-post.txt` is a snapshot at the retired pin, superseded by `D5b-post.txt`; `D6-pre.txt` (1 MB) is a stale-cache artifact (its first entry is the pre-fuel-arc `CerbND.runNDFuel.eq_def` with `panicWithPosWithDecl`). About 10 MB of redundant text; every hash is already in the record. Recommend keeping `D5b-post.txt` only (and `D6-pre.txt` if the orchestrator wants the stale-cache evidence retained). | `sha256sum` of the six files (below). |
| F-4 | Low (hygiene, C17 class) | `PartialClients.lean:359–360`, `:390`, `:386` | `PartialClients.t5RetQ`, `ψT5` are definitionally equal (`rfl` elaborates) to `CorpusT5Exhibit.t5RetQ`, `ψT5`; `t5Ls` mirrors `t5LsT` minus the budget. Codex avoided a client→client import (C19's queue) by duplication (C17's queue). Add to C17; not a merge blocker. | `example : CerberusHeapLang.PartialClients.t5RetQ = CerberusHeapLang.t5RetQ := rfl` and the `ψT5` twin both elaborate without error. |
| F-5 | Low (record navigability) | record `:14`, `:129`, `:230–234`, `:601` | The record names seven commit hashes that are not in the landed history (`cec16f5`, `f1f2573`, `77c237d`, `42e2205`, `98335e2`, `df5dc90`, `7bdf408`; all dangling objects reachable only by hash) and maps only `7bdf408 → dc1bf00`. A reader of `git log main` cannot find them. Fold a hash map into the F-1 erratum: `cec16f5 → 0cc46ae` (same patch), `77c237d → 98335e2 → 62685e1` (NOT the same patch — the manifest hunk was dropped at the first rebase), `42e2205 → … → 56e9d39`, `df5dc90` = the rebased stage-1 tip, `7bdf408 → dc1bf00` (same tree for `CerberusHeapLang/`). | `git diff A~1 A \| grep -v ^index \| md5sum` per pair (below). |
| F-6 | Low (H: duplication hygiene, recommend only) | `cerberus-heaplang/docs/2026-09-07_codex-stage1-notes.md` (on main) vs the live record | The copy is byte-identical to the record at `df5dc90` and a byte-identical PREFIX of the live record (first 225 of 610 lines, `cmp` clean). Neither file states its relation to the other (the copy has no header; the live record mentions the copy only as a file in main's docs-only diff, `:598`); only the charter §0 says it is a read-only copy. Recommend a one-line header on the copy now ("read-only copy of `codex-residuals-notes.md` at df5dc90 for the stage-2 agent; the live record supersedes it") and deletion when stage 2 closes (the stage-2 charter text must be repointed in the same commit, since that agent rebases before each gate). | `head -c $(wc -c < copy) live \| cmp - copy` → identical; `git show df5dc90:…residuals-notes.md \| diff - copy` → identical. |

Notes (not findings): (N-1) `GATE-EXIT=0` is not printed by `scripts/test_unit.sh` (it ends with `ALL GATES GREEN` and `exit 0`); it is the caller's `echo GATE-EXIT=$?` and the charter's own wording — the adaptation record's tail is explicitly a regex-filtered extract and says so. (N-2) The linter-warning count (33) and the entry-state error counts (39 / 36 / 4) cannot be re-measured without a rebuild, which this audit was forbidden to run; the module has no `set_option` other than `autoImplicit false`. (N-3) At the intermediate commit `62685e1` the library module carried three `#print axioms` commands (a forbidden construct in a library module); the adaptation removed them (E7) and HEAD has none — resolved inside the range, disclosed in the record. (N-4) `decide +kernel` (used in the module's `t5_lookup` macro and `t5RetQ_lookup`) is kernel reduction, used in ten other modules; the banned-axiom check of the pinned theorems' joint cone is negative (below).

## Per-finding detail

### F-1 — the manifest hunk dropped at the rebase

```
$ git show --stat --format='%h %ad %s' --date=iso 77c237d
77c237d 2026-09-07 03:56:48 +0000 codex D5: partial-face clients — FULL gate green; 0 undemonstrated rows; 896 trio-exact pins
 cerberus-heaplang/CerberusHeapLang/Audit.lean      |     5 +
 .../CerberusHeapLang/Examples/PartialClients.lean  |   671 +
 .../docs/2026-09-07_codex-D5-post.txt              | 47159 +++++++++++++++++++
 cerberus-heaplang/docs/2026-09-07_codex-D5-pre.txt | 47085 ++++++++++++++++++
 cerberus-heaplang/docs/CAPABILITY_MANIFEST.md      |    61 +-
 cerberus-heaplang/scripts/capability_manifest.lean |    21 +-
 cerberus-heaplang/scripts/module_classes.tsv       |     1 +
 7 files changed, 94959 insertions(+), 44 deletions(-)

$ git show --stat --format='' 62685e1        (the landed D5 commit)
cerberus-heaplang/CerberusHeapLang/Audit.lean      |     5 +
.../CerberusHeapLang/Examples/PartialClients.lean  |   671 +
.../docs/2026-09-07_codex-D5-post.txt              | 47159 +++++++++++++++++++
cerberus-heaplang/docs/2026-09-07_codex-D5-pre.txt | 47085 ++++++++++++++++++
cerberus-heaplang/scripts/capability_manifest.lean |    21 +-
cerberus-heaplang/scripts/module_classes.tsv       |     1 +
6 files changed, 94928 insertions(+), 14 deletions(-)

undemonstrated rows in manifest @62685e1: 7
undemonstrated rows in manifest @56e9d39: 7
generator classes @62685e1 rulePartialUndemonstrated count: 0
PartialClients in manifest @56e9d39: 0
HEAD manifest RULE-PARTIAL-UNDEMONSTRATED rows: 0
```

Codex's `77c237d` manifest and the worker's `dc1bf00` manifest differ by 14 lines
only (DERIVED: `diff … | grep -c '^[<>]'` = 14 — the L2 changes: `MODULES: 56
classified` → `60`; both read `47 RULE, … 0 RULE-PARTIAL-UNDEMONSTRATED … 0 red,
26 consumer modules`). So Codex's D5 was green as committed at `77c237d`/`42e2205`
(the DECISIONS entry's "orchestrator FULL gate green at 42e2205" is consistent);
the landed `62685e1`/`56e9d39` are not (the speedbump `diff -u "$manifest" "$tmp"`
at `scripts/test_unit.sh:60` would be non-empty). The DECISIONS line "(two
conflicts: TSV union; manifest regenerated)" describes work not present in the
rebased commit `df5dc90` (its manifest = main's; the worker measured the same at
record `:455–457`). Required fix: an erratum paragraph in the record (and in the
landing DECISIONS entry) stating exactly this, plus the hash map of F-5. No Lean
change.

### F-2 — the front documents at merge

```
cerberus-heaplang/ARCHITECTURE.md:889:  census. E5's seven new rule rows are RULE-PARTIAL-UNDEMONSTRATED:
cerberus-heaplang/ARCHITECTURE.md:890:  t5 and t4 consume the total faces; no partial corpus derivation consumes
cerberus-heaplang/ARCHITECTURE.md:891:  their twins yet. These include the exact whole-cell read-footprint
cerberus-heaplang/README.md:128:twenty-five modules classified `positive-client`/`declared-smoke` in
cerberus-heaplang/README.md:141:fragment/mirror boundary): 35 constructors, 78 rows, 40 RULE, 0
cerberus-heaplang/README.md:142:RULE-TOTAL-UNDEMONSTRATED, 7 RULE-PARTIAL-UNDEMONSTRATED, 24 NO-RULE,
```

HEAD's generated tail (`docs/CAPABILITY_MANIFEST.md`): `MANIFEST: 35 constructors,
78 variant rows (47 RULE, 0 RULE-TOTAL-UNDEMONSTRATED, 0 RULE-PARTIAL-UNDEMONSTRATED,
0 PARTIAL-ONLY, 24 NO-RULE, 7 OUT-OF-SCOPE), 0 red, 26 consumer modules`. KOI C19's
"the seven RULE-PARTIAL-UNDEMONSTRATED faces (proved, honestly classified;
disposition = a partial client …)" is discharged by this range; KOI B20's "three
clients touched" becomes four; KOI §E's expected tail (901 / 483 jobs / 29 modules)
becomes 904 / 484 / 30 (the record's verbatim tail, `:526`, `:529`, `:568`).

### F-3 — snapshot duplication

```
1b7d097dc6956c8b258d6e953d5a2ef37687db660d8c80d1790e1b22820113d9  docs/2026-09-07_l1-signatures-post.txt
1b7d097dc6956c8b258d6e953d5a2ef37687db660d8c80d1790e1b22820113d9  docs/2026-09-07_codex-D6-post.txt
1b7d097dc6956c8b258d6e953d5a2ef37687db660d8c80d1790e1b22820113d9  docs/2026-09-07_codex-D5-pre.txt
cbe88d812d2f760ddbdbad037355771c38e7e975ad6838ad1bf35e9859ec40b5  docs/2026-09-07_codex-D5-post.txt   (47159 lines, pre-L2 pin)
52627eebc1a0bd3bdb63794054a131198d466978cbbb191dbfbab1c90ef4b216  docs/2026-09-07_codex-D6-pre.txt    (18551 lines, stale cache)
91f0419bd536e9c149e9eb9f31c29181478b85bc419542d481eb67d1a1bbf739  docs/2026-09-07_codex-D5b-post.txt  (52298 lines, the live one)
```

### F-5 — the hash map (DERIVED by patch-identity, `index` lines stripped)

```
cec16f5 -> 0cc46ae : b283f8bef634 vs b283f8bef634 SAME-PATCH
77c237d -> 62685e1 : 8864e6652463 vs b8c312f49035 DIFFERENT-PATCH      (the manifest hunk, F-1)
98335e2 -> 62685e1 : b8c312f49035 vs b8c312f49035 SAME-PATCH
df5dc90 -> 56e9d39 : ea7b9c9bd72c vs ea7b9c9bd72c SAME-PATCH
git rev-parse 7bdf408:cerberus-heaplang/CerberusHeapLang dc1bf00:cerberus-heaplang/CerberusHeapLang
497f5139988d3df34c3ff95c5592359012c82e0e
497f5139988d3df34c3ff95c5592359012c82e0e
```

## Verified clean — checks A–I with the measurement

**A. Charter compliance / fence.** `git diff --stat 1e1f584 cdaf189` touches
exactly 11 files: `Audit.lean` (+5: the import and three pins under a one-line
comment), the new `Examples/PartialClients.lean`, five snapshot `.txt` (charter
rule 2 mandates them; committing post-snapshots is house practice — cf.
`l1/l2/l2b-signatures-post.txt`), the record, `CAPABILITY_MANIFEST.md`,
`scripts/capability_manifest.lean` (the diff changes only `cls :=` lines: seven
`.rulePartialUndemonstrated (N p) (N t) "mover"` → `.rule (N p) (N t)`), and one
TSV row. NOT touched: `docs/DECISIONS.md`, `docs/KNOWN-OPEN-ITEMS.md`,
`scripts/semantics-pin.env`, any `lake-manifest.json`, anything under
`.cerberus-ws/`. D6's two commits (`0cc46ae`, `0b979bc`) touch only two snapshot
`.txt` and the record — `git diff 0cc46ae~1 0b979bc --stat -- . ':(exclude)*.md' ':(exclude)docs/*'`
lists the two `.txt` only: no Lean/script residue from the reverted implementation.

**B. Forbidden constructs.** Over the range's non-`.txt`/non-`.md` added lines:
`grep -nE 'axiom|sorry|native_decide|bv_decide|ofReduce|maxHeartbeats|maxRecDepth|#print|#eval|100000000|1000000|999999|lemDefaultFuel|driverFuel'`
→ `grep exit=1` (no match). Numerals in the three PUBLIC statements: `0` (the
`hfuel` floor) and `4` twice (the `int` alignment operand, as in `t5_wpt`). The
module's other numerals (DERIVED census): source-symbol numbers 508–529 and
Core-location numbers 15/16/39/40/48/80/81/84 from the transcription, and
`-2147483648`/`2147483647` twice each — the `int` range premises of
`emittedInt_storable` (`Examples/EmittedInt.lean:186`, stated there with the same
numerals), program/ABI constants, not fuel or supply bounds. No new numeric
premise on any public statement: `t5_wpt`'s `600 ≤ sym_supply` is REPLACED in the
partial by the abstract `hfresh` (see D), which the `600` floor implies (checked:
an `example` deriving `hfresh` from `600 ≤ M.runState.sym_supply` elaborates).

**C. Axioms and pins.** Measured (scratch, `lake env lean`, exit 0):

```
'CerberusHeapLang.PartialClients.t5_wps' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.PartialClients.t5_blockSpecs' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.PartialClients.loadBind_wps' depends on axioms: [propext, Classical.choice, Quot.sound]
904        -- #eval CerberusHeapLang.Audit.trioExports.length
904        -- #eval …trioExports.eraseDups.length   (no duplicate pins)
6          -- #eval …axiomFreeExports.length
3          -- pins under CerberusHeapLang.PartialClients.*
joint cone contains Lean.ofReduceBool? false
joint cone contains Lean.ofReduceNat? false
joint cone contains sorryAx? false
```

Pin delta vs main: `git diff 1e1f584 cdaf189 -- Audit.lean` adds exactly the
three names (plus the import); textual count of the `trioExports` list 907 → 910
(DERIVED; the textual count exceeds the evaluated one by six at both revisions,
so the delta is exactly +3). At `46c28dc` (stage-1 main) the textual count is 893,
matching the record's "893 → 896".

**D. Vacuity / strength.** Scratch scan over all 98 constants of the module
(private and auxiliary included), theorem bodies read via `.thmInfo t => t.value`
(`ConstantInfo.value?` is `none` for theorems in this toolchain — the generator
documents the same at `scripts/capability_manifest.lean:446`):

```
TOTAL LemFuel binders = 19; vacuous in statement = 0; bodies scanned = 98
theorem CerberusHeapLang.PartialClients.t5_wps: LemFuel-binders=1 VACUOUS-in-statement=#[] LemFuel-unused-in-proof=#[] explicit-hyps-unused-in-proof=#[]
theorem CerberusHeapLang.PartialClients.t5_blockSpecs: … explicit-hyps-unused-in-proof=#[]
theorem CerberusHeapLang.PartialClients.loadBind_wps: … explicit-hyps-unused-in-proof=#[]
```

Every `[LemFuel]` binder is referenced by its statement (`wps`, `readoutPost`,
`evalPexpr`, `memValueFromValue`, `alignofIval` are all `[LemFuel]`-quantified at
the pin — `Wps.lean:185 variable [LemFuel]`, `:322 def wps`); no H-1-class
binder. Every explicit hypothesis of every theorem is used by its proof; in
particular `hfuel` and `hfresh` of `t5_wps`. `hfuel : 0 < LemFuel.fuel` is
consumed by `wps_create`'s premise `(hfuel : 0 < LemFuel.fuel)` (`Wps.lean:4207`,
applied at `PartialClients.lean:556`, `:572`), the same floor and placement as
`t5_wpt [LemFuel] (hfuel : 0 < LemFuel.fuel)` (`CorpusT5Exhibit.lean:429`, its
`wpt_create (hfuel := hfuel) …` at `:448`/`:465`); `0 <` is the rule's own floor
(the `4 ≤`/`k + 2 ≤` floors elsewhere belong to the total lane's budgets, not
to `wps_create`). Statement parallelism, elaborated (`#check`):

```
@CerberusHeapLang.PartialClients.t5_wps : ∀ {GF} [inst : LemFuel], 0 < LemFuel.fuel → ∀ [SpikeGS …] {M} {p},
  StdE3 M.file → (∀ x, resolveExtern M.extern x = x) → M.labelsAt p = PartialClients.t5RetQ →
  (∀ k, M.runState.sym_supply ≤ k → symOrd CorpusE0.xSym (fresh_given_int k) ≠ .eq ∧ symOrd CorpusE0.t5rSym (fresh_given_int k) ≠ .eq) →
  ∀ f rest, SymFrame f → allocBudget (allocCost M.tagDefs intTy 4 + allocCost M.tagDefs intTy 4) ⊢
    wps M p (PartialClients.t5Ls GF) emptyProcSpec (readoutPost PartialClients.ψT5) CorpusE0.t5Main (f :: rest)
@CerberusHeapLang.t5_wpt : ∀ {GF} [inst : LemFuel], 0 < LemFuel.fuel → ∀ [SpikeGS …] {M} {p},
  StdE3 M.file → (∀ x, resolveExtern M.extern x = x) → M.labelsAt p = t5RetQ → 600 ≤ M.runState.sym_supply →
  ∀ f rest, SymFrame f → allocBudget (…) ⊢ wpt M p (t5LsT GF) emptyProcSpecT 88 (readoutPost ψT5) CorpusE0.t5Main (f :: rest)
```

Same program object `CorpusE0.t5Main` (the whole transcribed `main`, checked
against the emitted text by the corpus-skeleton speedbump), same budget
precondition, same label map and post (F-4: definitionally equal twins);
the partial drops the budget `88` and the `m = 2` label budget (as a partial
judgment should) and REPLACES the numeral floor by the abstract non-collision
premise — strictly more general (implied by `600 ≤ sup`; the E5 audit's B6 shows
the premise is not vacuous: at `sup = 505` the fresh symbol collides with `x`).
Satisfiable: `example : ∀ k, 507 ≤ k → …` elaborates via `symOrd_ne_eq_of_num_ne`
(`fresh_given_int n = Symbol (CerberusFresh.digest ()) n SD_None`,
`generated/Symbol.lean:418`; `xSym`/`t5rSym` are numbered 505/506). No `False`
hypothesis, no contradictory instances. `loadBind_wps` asserts the annotated
LETS-ANNOT result `w = .annot [DA_pos [] (loadFootprint …)] (loadedVal …)`, the
binding `ρ = envAdd x … f :: rest`, and the RETAINED `pointsToCell … dq …` at any
fraction — the whole-cell load with its exact read footprint, as recorded.

**E. Manifest and TSV.** The generator's cone is seeded with every constant of
a consumer module (`byModule`, `capability_manifest.lean:667–676`), so its "0
red" alone would also credit a private helper nobody uses. Stronger check,
measured: the proof-term cone from the PINNED theorems only:

```
cone of CerberusHeapLang.PartialClients.t5_wps: 1204 constants
   wps_load_footprint ∈ cone? true   wps_neg_round ∈ cone? true   wps_excluded_store ∈ cone? true
   wps_excluded_store_eval ∈ cone? true   wps_case_eval ∈ cone? true   wps_neg_bound ∈ cone? true   wps_create ∈ cone? true
   wps_seq_sym_annot ∈ cone? false   wpt_load_footprint ∈ cone? false   wpt_neg_round ∈ cone? false
cone of CerberusHeapLang.PartialClients.loadBind_wps: 594 constants
   wps_load_footprint ∈ cone? true   wps_seq_sym_annot ∈ cone? true   (all others false)
```

All seven partial faces are reached from a pinned public theorem: `Frag.load`
footprint (`wps_load_footprint`: `t5_wps` and `loadBind_wps`), `Frag.sseq_sym`
annotated (`wps_seq_sym_annot`: `loadBind_wps`), `Frag.neg_store` and
`neg_store_op` (`wps_neg_round`), `Frag.excluded_store` (`wps_excluded_store`),
`Frag.excluded_store_op` (`wps_excluded_store_eval`) — these three through the
public composite `wps_neg_bound` (`Wps.lean:5280`, whose body applies them at
`:5302`, `:5345`, `:5346`), the same transitive route by which the TOTAL faces were
credited to `CorpusT5Exhibit` (which names none of `wpt_neg_round`/`wpt_neg_bound`
directly), and `Frag.case_op` (`wps_case_eval`, applied at `PartialClients.lean:241`,
`:353`). No `wpt_*` rule is in any partial cone: no total-to-partial conversion,
as the module header claims. Manifest: the seven rows read `RULE` with
`Examples.PartialClients` as the sole partial consumer (`CAPABILITY_MANIFEST.md`
diff, lines quoted in the record `:468–474`, re-read at HEAD); tail `47 RULE … 0
red, 26 consumer modules`. TSV: `Examples.PartialClients  positive-client  -  …`
— consistent with its role (a client of `API` + `Examples.EmittedInt`, an
`example-support` module), with the boundary check (`ok: Examples.PartialClients —
0 internals mentions`, and the class puts it IN the checked set) and with the
import-direction check (not `core`). No red row.

**F. Snapshot census** (DERIVED, entries split on `----`, keyed by the printed
`<kind> <name> :` head, compared by full text):

```
D5b: pre 5212(names 5212, unparsed 0) post 5219(names 5219, unparsed 0) ADDED 7 REMOVED 0 CHANGED 0 UNCHANGED 5212
   ADDED def CerberusHeapLang.PartialClients.loadBind / theorem …loadBind_wps / def …t5Ls / def …t5RetQ /
         theorem …t5_blockSpecs / theorem …t5_wps / def …ψT5
D5 : pre 4950 post 4957 ADDED 7 REMOVED 0 CHANGED 0 UNCHANGED 4950        (same seven names)
D6 : pre 1949 post 4950 ADDED 3112 REMOVED 111 CHANGED 667 UNCHANGED 1171
```

Exactly the record's three censuses (`:36`, `:178–179`, `:494`), all seven
additions in the new module. Pre = `l2b-signatures-post.txt` SHA-256
`045e9e61…` (matches record `:485`); post = `D5b-post.txt` `91f0419b…`, 52 298
lines (matches `:488–489`).

**G. Record accuracy, spot-checked.** Statement header lines before/after
(`:327–332`) — verified against `git diff -U0 98335e2 7bdf408` (record `:339–434`
reproduces it; `git diff --numstat` = `30 32`, as claimed at `:337`). Manifest
`git diff --numstat 1e1f584 cdaf189` = `31 30` (claimed `:477`). "byte-identical"
`7bdf408` vs `dc1bf00`: `git diff --stat` lists only main's three docs-only files
(the stage-1 copy, the charter, DECISIONS: `3 files changed, 332 insertions(+),
35 deletions(-)` = `git diff --stat 6b6d9a8 1e1f584`), tree object of
`CerberusHeapLang/` identical (`497f5139…`, both). All six SHA-256 values in the
record match. `#print axioms` lines match. 34 private helpers (`grep -cE
'^private (theorem|def|abbrev)'` = 34, claimed `:146`). Cites `Wps.lean:185/:322/
:1333–1334/:4203–4211/:5280`, `EmittedInt.lean:185–186`, `CorpusT5Exhibit.lean:429/
448/465` all land on the named text. Gate-tail shape: every quoted line has the
exact format of `scripts/test_unit.sh`, `scripts/boundary_check.sh` (`BOUNDARY: N
modules checked, 0 internals mention(s) in total, exit=0`) and
`scripts/fuel_numeral_check.sh:196`; see N-1 on `GATE-EXIT`. Timings are
consistent with the commit timestamps (`62685e1` 03:56:48 / `56e9d39` 03:57:39;
`7bdf408` 05:55:38 then the gate 05:55:52–05:56:08; main moved to `1e1f584` at
05:52:15, i.e. before that gate — the record's "after the FULL gate main moved"
is loose but the rebase account and its verification are exact). Not
re-measurable here: the 33 warnings and the 39/36/4 error counts (N-2). The one
substantive inaccuracy is F-1.

**H. Duplication hygiene.** F-6: byte-identical prefix, relation unstated in
either file; recommend, do not fix.

**I. Provenance.** Two `[AGENT]` decisions in the adaptation section (per-
declaration `[LemFuel]`; `hfuel` on `t5_wps`), both mechanically forced by the pin
(`wps_create`'s premise cannot be discharged for an arbitrary instance), both
tagged, the second flagged for re-adjudication — correctly, and no `[USER]` ruling
was needed: relative to main the statement is ADDED, not CHANGED (census F), so
the charter's D5 "ADDED only" holds. The Codex section carries no provenance tags
for its own choices (the `positive-client` class, the local twins of F-4, and the
`hfresh` shape of a pinned export — the charter §5 left stage-1 D5's statement
shape to the agent). The landing DECISIONS entry should record the `hfresh` shape
as the [AGENT] choice it was, and that it is the B19/B20-preferred form (no numeral).

## Fixes required before/at merge (docs-only)

1. **F-1**: append an erratum to `cerberus-heaplang/docs/2026-09-07_codex-residuals-notes.md`
   (and state it in the landing DECISIONS entry): the rebase resolution took
   main's `CAPABILITY_MANIFEST.md`, so `62685e1`/`56e9d39` are manifest-stale as
   committed (7 undemonstrated rows in the file, 0 in the generator) and would
   fail the manifest speedbump; `dc1bf00` restores it; include the F-5 hash map.
2. **F-2**: in the landing commit, update `ARCHITECTURE.md:889–893`,
   `README.md:128`, `:141–142`, and KOI C19 / B20 / §E to the post-merge facts
   (47 RULE / 0 undemonstrated / 26 consumer modules; four clients on B20;
   904 pins / 484 jobs / 30 boundary modules).

Recommended, not required: F-3 (prune redundant snapshots), F-4 (add the twins
to C17), F-6 (header on the stage-1 copy).
