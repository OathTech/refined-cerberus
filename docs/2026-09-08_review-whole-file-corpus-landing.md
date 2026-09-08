# Landing review: `demo-whole-file-corpus` (main `4bc0a98` .. `00db603`), by the orchestrator of the demo line

Reviewer: the refined-cerberus orchestrator [AGENT, 2026-09-08], acting as
the external pre-merge reviewer at the operator's request, as for the t1
slice (`docs/2026-09-08_review-whole-file-t1-landing.md`). Fresh to this
branch; not its author, worker or internal reviewer. Every claim below was
measured in this worktree at `00db603` (clean tree); quoted outputs are
verbatim; my tallies are labelled DERIVED. This file is left UNCOMMITTED for
the branch owner to commit beside their records. It authorises nothing: the
merge is the operator's sign-off.

## Verdict: PASS — no fix required before merge. Grade A−.

The slice delivers what its charter promised: the whole-file route landed
for t1 now covers t5_ifelse, t6_switch and t4_while as well, so all four
supported corpus programs have complete-file certificates over the pinned
Lean frontend's output (option (b)), with shared integer support that has
real consumers, one narrowly generalised rule whose old statement survives
as a specialisation, no change to any frozen file or existing signature, and
front documents that say exactly what is claimed. The previous review's one
required fix — recording the OCaml oracle's identity — is applied. The minus
is a cleanliness regression the charter authorised and the documents
disclose: fourteen new pinned statements carry numeral symbol-supply floors
(F1), the very class the master plan's V1-4a exists to remove.

## 1. What I measured (all at `00db603`)

**Gate, my own run** (`CERB_MEM_MAX=40G TMPDIR="$PWD/.tmp" scripts/test_unit.sh`,
04:30:27–04:31:45 UTC, wrapper `EXIT=0`, 0 modules rebuilt — the author's
cache was current; 0 `UNCAPPED`; per-module boundary lines and the four
repeated nested-build blocks elided):

```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 1b: fuel-numeral grep (scripts/fuel_numeral_check.sh; a numeral outside a *_shipped corollary is red) ==
ok: no fuel numeral (100000000/1000000/999999) outside a *_shipped corollary and no retired fuel constant (77 files scanned, comments stripped)
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:1233:0: CerberusHeapLang export pins: 991 trio-exact, 7 propext-exact, 7 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1233:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (7356 swept, internal details included — count informational, environment-dependent)
Build completed successfully (500 jobs).
ok: cerberus-heaplang build green
== speedbump: rule-use and classification manifest (regenerate; red on a red row or drift) ==
ok: capability manifest regenerated, no drift
== speedbump: corpus skeleton (hand-transcribed emitted Core vs docs/corpus-e0; scripts/corpus_skeleton.lean) ==
ok: corpus skeleton — every transcription matches its emitted text, every plant mismatches
== speedbump: complete emitted corpus files (fresh Cabs, data/supply, original comparator checks) ==
whole-file corpus: OCaml oracle version: git-cn-pin-720-g9a7f7ad31
ok: whole-file t1 — fresh Cabs matches retained fixture
ok: whole-file t1 — metadata, all three comparator checks and singleton return 4 checked
ok: whole-file t1 — independent structural data, quotation, supply and negative checks passed
ok: whole-file t5 — fresh Cabs matches retained fixture
ok: whole-file t5 — metadata, all three comparator checks and singleton return 1 checked
ok: whole-file t5 — independent structural data, quotation, supply and negative checks passed
ok: whole-file t6 — fresh Cabs matches retained fixture
ok: whole-file t6 — metadata, all three comparator checks and singleton return 20 checked
ok: whole-file t6 — independent structural data, quotation, supply and negative checks passed
ok: whole-file t4 — fresh Cabs matches retained fixture
ok: whole-file t4 — metadata, all three comparator checks and singleton return 10 checked
ok: whole-file t4 — independent structural data, quotation, supply and negative checks passed
ok: complete-file corpus comparison and negative checks
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — 19 core modules, none imports an exhibit/example/production module
== speedbump: client boundary (positive clients mention no logic internals; scripts/boundary_check.sh) ==
BOUNDARY: 44 modules checked, 0 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
```

Each of the four instances also passed the `main := none` and
`frontendSupply + 1` negative checks and the nine structural-comparator
self-tests (in the log, elided above). Warnings: 165 lines printed, 33
DISTINCT (DERIVED) — the baseline; one library build plus four nested
dependency builds replay the same warnings (the record says so). Gate wall
time 78 s (was 34 s for t1 alone); `--fast` is unaffected.

**Frozen core and unchanged modules** (byte-identical to main `4bc0a98`,
DERIVED by `git diff --stat`): `Step`, `Wps`, `Soundness`, `Round`,
`Fragment`, `Heap`, `Lang`, `Rules`, `EvalClass`, `DriverCollapse`,
`ProdEntry`, `ProdLoop`, `EmittedFile`, `EmittedMapChecks`,
`EmittedStdCore`. Changed within the fence: `Wpt` (+36/−?: one rule), `Audit`
(+83/−4), `Shipped` (+78), `API` (+16), root imports (+4), `EmittedT1Exhibit`
(+14: consumes the shared facts, statements unchanged), `scripts/capability_manifest.lean`
(+9: three `also` lists), `module_classes.tsv` (+14). New: `EmittedIntSupport`
(178), `EmittedT{4,5,6}Exhibit` (1 708 / 729 / 761), `Examples/EmittedT{4,5,6}`
(529 / 397 / 393), `Examples/EmittedT{4,5,6}Data` (47 266 / 44 156 / 44 816).
No dependency pin, lakefile, manifest or provider file changed.

**Signature census** (my own by-name recount, entries split on `----`,
full-text compare): baseline 5 569 → final 6 081, **ADDED 512, REMOVED 0,
CHANGED 0** — identical to the author's and their reviewer's figures. The
baseline snapshot is byte-identical to main's `2026-09-08_whole-file-final.txt`,
so the baseline IS main's census. Additions by namespace (DERIVED):
`CorpusA7` 496, `EmittedIntSupport` 15, plus `wpt_neg_bound_compare`. Every
existing public statement — including `wpt_neg_bound`, the four wrappers and
their shipped corollaries — is unchanged.

**The one core-rule edit** (`Wpt.lean`): `wpt_neg_bound_compare` weakens the
extern premise from constructor identity (`resolveExtern M.extern x = x`) to
comparison equality (`symCmpK (resolveExtern M.extern x) x = .EQ`), used only
at the final fresh-binder lookup through `evalPexpr_sym_of_compare`; the
original `wpt_neg_bound` is restated verbatim and proved by specialisation
(`symCmpK_laws.refl`). Census CHANGED 0 confirms the old contract; the
generator's `also` lists name the new rule beside the old on the two rows it
touches, and `EmittedIntSupport.wpt_unseq_value_right`/`wpt_intAssign` on
theirs — the manifest regenerates with no drift (30 consumer modules).

**Pins**: 918 → 991 trio-exact (+73: 66 `CorpusA7`, 6 `EmittedIntSupport`,
`wpt_neg_bound_compare`); `propextExports` and `axiomFreeExports` unchanged
(7 / 7). The only removed Audit line is the old list terminator re-added
with a comma.

**Forbidden constructs**: none in the added Lean (`sorry`, `native_decide`,
`bv_decide`, `ofReduce*`, `maxHeartbeats`, `maxRecDepth`, `axiom`,
`#print`/`#eval`, `unsafe`, `implemented_by`: 0 hits). 24 `decide +kernel`
sites (the existing exhibits' pattern, concrete symbol comparisons) and 5
`mkAuxLemma` sites (kernel-checked `Eq.refl` auxiliaries for the concrete
collector/`Q` equalities, as in the t1 slice).

**Elaboration cost** (standalone `lake env lean`, 40G cap, DERIVED):
`EmittedT4Data` 4.0 s, `EmittedT5Data` 3.6 s, `EmittedT6Data` 3.5 s,
`EmittedIntSupport` 1.2 s, `Examples/EmittedT4` 6.5 s, `EmittedT5Exhibit`
11.6 s, `EmittedT6Exhibit` 8.3 s, `EmittedT4Exhibit` 14.1 s. Nothing near the
grind tripwire; the three new 44–47 k-line data terms are cheap for the kernel.

**The statements.** `CorpusA7.T{5,6,4}.certified_production` (EmittedT5Exhibit
:688, EmittedT6Exhibit :719, EmittedT4Exhibit :1666) each state
`CerbND.runND (_root_.drive (restoredFile cmp).tagDefs false (restoredFile cmp) args)
((initial_driver_state frontendSupply (restoredFile cmp) fs).1) = [(Active dres, [], dst')]`
with the advertised value (`lint 1` / `lint 20` / `lint 10`), unblocked,
empty output, at `hfuel : 90 / 80 / 917 ≤ LemFuel.fuel`, under the three
comparator checks, for arbitrary `fs` and `args`. The `_of_capture_eq` twins
(:713 / :744 / :1691) quantify the original `F` and `sup` under
`captureData F = data` and `sup = frontendSupply` (47 / 51 / 92). The three
shipped corollaries (`Shipped.lean`) instantiate the fuel only. No mirror,
collapse or hand-written driver device appears in any statement; the
referent is the genuine pipeline in the option-(b) sense the documents state.

**The t1 review's required fix is applied**: `docs/corpus-a7/README.md` now
records the oracle binary's SHA-256 (`7d1778bb…`) and its `--version`
(`git-cn-pin-720-g9a7f7ad31`); `scripts/check-emitted-corpus.sh` prints the
hash, version, binary and runtime paths on every run (the version line is in
my gate log above). The runner still fails closed if the binary is absent
and byte-compares each fresh Cabs to its fixture.

**Documents**: ARCHITECTURE (+103) describes the four-program route and,
after their reviewer's N1, distinguishes T5/T4's `22 <` source-pointer bound
from T6's `51 ≤` label/driver bound; CLAIMS relabels C14–C17 as retained
wrapper regressions and generalises C19 to the corpus; KOI A7/C20 are
updated for the four programs with option (a) and the six unsupported
programs left open; the master plan and requests register carry dated,
additive progress notes (V1-1b; R-4 settled for t1/t5/t6/t4, general
guarantees open); DECISIONS has two entries, the [USER] one quoting the
operator's authorisation verbatim. Their own fresh adversarial review
(`docs/2026-09-08_review-whole-file-corpus.md`, PASS, N1 corrected) is
careful and its measurements agree with mine where they overlap.

## 2. Findings

| id | severity | where | claim | how verified |
|---|---|---|---|---|
| **F1** | **Low** (statement cleanliness; disclosed; not blocking) | `EmittedT6Exhibit.lean:341, :393, :684`; `EmittedT5Exhibit.lean:501, :649`; `EmittedT4Exhibit.lean:904, :953, :1052, :1282, :1328, :1386, :1427, :1465, :1626` | Fourteen NEW pinned public theorems carry numeral symbol-supply floors: T6's `51 ≤ M.runState.sym_supply` / `51 ≤ sup` (51 IS `frontendSupply`, written as a literal — a duplicated captured value) and T5/T4's `22 < M.runState.sym_supply` / `22 < sup` (22 = the number of the larger of the two live source-pointer symbols — a program-derived literal). The exports discharge them at the exact captured supply (`by decide`), so the ROOT-OF-TRUST statements carry no floor — good, and better than the wrappers' `600`. But the class the master plan's V1-4a exists to remove (B19; 18 old `600` sites) now has 14 more members, all pinned, and gate 1b cannot see them (it matches fuel numerals only). The charter authorised "local non-collision obligations" and the reviewer's N1 disclosed the two shapes. | `grep -nE 'sym_supply|≤ sup|< sup'` over the three exhibits (14 premise sites, DERIVED); `def frontendSupply : Nat := 51` (EmittedT6Data.lean:7); `mainBody_driver_done`/`mainBody_wpt`/`wpt_main`/`blockSpecsT_main` all present in `Audit.lean` |
| F2 | Info | master plan §3.1 G1.1/G1.9, §4.1 V1-4a | Bookkeeping for the plan's next revision: the `600` census stays 18 (the record and their reviewer confirm); the numeral-floor class is now 18 + 14; V1-4a's scope should name the fourteen and prefer `frontendSupply ≤ …` / symbol-number-derived bounds over literals. The four shipped-fuel floors (`50/90/80/917`) are the existing G1.9 class. | source; the plan text |
| F3 | Info (hygiene) | branches `worker-whole-corpus-{charter,t4,t5,t6}`, `review-whole-file-corpus`, `scout-next-whole-file-slice`, and the t1 slice's `worker-whole-file-{compare,docs,range-review}`; worktrees `review-whole-file-corpus`, `scout-next-whole-file-slice`, `demo-whole-file-t1` | Ten auxiliary branches and three idle worktrees from the two whole-file slices remain (the t1 review's F3 was not acted on). After landing: remove the worktrees; delete the branches or register them as superseded in the master plan §2. | `git worktree list`; `git for-each-ref` |
| F4 | Info | `scripts/test_unit.sh`, gate log | The FULL gate's whole-file speedbump now runs four nested dependency builds and inspections (78 s total, all cached); each nested block re-prints the seam check and the nine self-tests, so the gate log grew fourfold. Consider printing the shared preamble once. | my gate log (165 warning lines / 33 distinct) |
| F5 | Info (positive) | `Wpt.lean` | The only core-rule edit is the narrowest possible generalisation, with the old statement preserved and the census confirming it. | diff; census |

No Critical, High or Medium finding. Nothing re-reports a known-open item as
new. The four numeral-floor exhibits are the reason for the minus, not for
a fix: they are honest, disclosed, discharged at the captured supply, and
the plan already owns their removal.

## 3. What a referee would still say (boundaries, not findings)

- **Option (b), four times.** The theorems are about the pinned Lean
  frontend's file from OCaml Cabs; equality with the OCaml-printed Core of
  `docs/corpus-e0/*.annot.core` is not asserted; the loader, quoter and
  structural comparator are executable, checked trusted components;
  option (a) is the recorded mover. All stated on every surface.
- **Fuel floors and supplies.** `hfuel : 90/80/917` are composition bounds
  (the record's table: `88 = 17+55+16`, `78 = 20+58`, `915 = 20+895`, plus
  the driver's two), disclosed as sufficient, not minimal; supplies 47/51/92
  are captured data checked by the speedbump's `+1` perturbation.
- **Six programs remain**: calls (t2, t3, t10), the recursion closed form
  (t9), structs (t7), arrays (t8) — the master plan's Phase II, untouched here.

## 4. Recommended changes (none required before merge)

1. In the master plan's next revision (orchestrator's landing docs, not this
   branch): record the fourteen new numeral-floor sites under G1.1/G1.9 and
   put them in V1-4a's scope with the preferred spellings (`frontendSupply ≤ …`
   for T6; the source-symbol number for T5/T4's `22`).
2. After landing: prune the ten auxiliary branches and three idle worktrees,
   or register them as superseded.
3. Optional: print the whole-file speedbump's shared preamble once per gate
   run rather than once per program.

## 5. Provenance

[USER 2026-09-08]: "Worktree ready for review. Can you add your review to
the worktree for codex." [AGENT]: the measurements above (gate, census,
frozen files, pins, elaboration timings, source reads of the three exhibits'
statements and premises, the `Wpt` diff, the runner and fixture README, the
register/KOI/plan/CLAIMS diffs), the findings and their severities. Read:
the charter (`docs/2026-09-08_whole-file-corpus-charter.md`), the
implementation record, their adversarial review, the t1 landing review. The
merge remains the operator's explicit sign-off; this review recommends it.
