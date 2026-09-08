# Landing review: `demo-whole-file-t1` (main `7040406` .. `d49cd3b`), by the orchestrator of the demo line

Reviewer: the refined-cerberus orchestrator [AGENT, 2026-09-08], acting as
the pre-merge reviewer at the operator's request ("act as a reviewer for the
demo-whole-file-t1 worktree … after which they will land it on main"). Fresh
to this branch; not the author, not one of its workers. Every claim below
was measured in this worktree at `d49cd3b` (clean tree) unless labelled
otherwise; quoted outputs are verbatim; my tallies are labelled DERIVED. This
file is left UNCOMMITTED for the branch owner to commit beside their
records. It authorises nothing: the merge is the operator's sign-off.

## Verdict: PASS WITH FIXES — one required fix (F1, disclosure of a new gate prerequisite), the rest recommended. Grade A−.

The slice does what its charter promised and what the demo master plan's
V1-1 asked for in the option-(b) sense: the pinned Lean frontend's complete
file for `t1.c` — linked std.core and gcc implementation map included —
enters the root-of-trust statement as a machine-quoted data term; the
statement is over the genuine `CerbND.runND (_root_.drive …)` at every fuel
above a disclosed floor; nothing pinned changed; the frozen core is
byte-identical; the reusable machinery is generic in the file; the record and
the front documents say exactly what is and is not claimed. The one gap is
that the FULL gate now depends on an external artefact whose identity is not
recorded anywhere.

## 1. What I measured (all at `d49cd3b`)

**Gate, my own run** (`CERB_MEM_MAX=40G scripts/test_unit.sh`, 01:33:24–01:33:58
UTC, wrapper `EXIT=0`, 0 modules rebuilt — the author's cache was current,
0 `UNCAPPED`; the thirty-four per-module boundary lines elided):

```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 1b: fuel-numeral grep (scripts/fuel_numeral_check.sh; a numeral outside a *_shipped corollary is red) ==
ok: no fuel numeral (100000000/1000000/999999) outside a *_shipped corollary and no retired fuel constant (67 files scanned, comments stripped)
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:1152:0: CerberusHeapLang export pins: 918 trio-exact, 7 propext-exact, 7 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1152:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (6816 swept, internal details included — count informational, environment-dependent)
Build completed successfully (490 jobs).
ok: cerberus-heaplang build green
== speedbump: rule-use and classification manifest (regenerate; red on a red row or drift) ==
ok: capability manifest regenerated, no drift
== speedbump: corpus skeleton (hand-transcribed emitted Core vs docs/corpus-e0; scripts/corpus_skeleton.lean) ==
ok: corpus skeleton — every transcription matches its emitted text, every plant mismatches
== speedbump: complete emitted t1 file (fresh Cabs, data/supply, original comparator checks) ==
ok: whole-file t1 — fresh Cabs matches retained fixture
ok: emitted-file comparison — all three captured-comparator checks pass on the compared instance
ok: emitted-file negative check — main := none rejected by structural and quotation comparisons
ok: emitted-file negative check — frontendSupply + 1 rejected by supply comparison
ok: whole-file t1 — metadata, all three comparator checks and singleton return 4 checked
ok: whole-file t1 — independent structural data, quotation, supply and negative checks passed
ok: complete-file t1 comparison and negative checks
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — 19 core modules, none imports an exhibit/example/production module
== speedbump: client boundary (positive clients mention no logic internals; scripts/boundary_check.sh) ==
BOUNDARY: 34 modules checked, 0 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
```

Warnings: 66 lines printed, 33 DISTINCT (DERIVED, `sort -u`) — the baseline
33; the doubling is the new speedbump's nested dependency build replaying
the same warnings (the record says so; see F5).

**Frozen core** (byte-identical to main `7040406`, DERIVED by `git diff
--stat`): `Step`, `Wps`, `Wpt`, `Soundness`, `Heap`, `Rules`, `Fragment`,
`Lang`, `Round`, `Adequacy`, `EvalClass`. Changed within the charter's Phase-A
fence: `DriverCollapse` (160 lines), `ProdLoop` (178), `ProdEntry` (167),
`EnvLaws` (+47), `Audit` (+34/−4), `Shipped` (+28), `API` (+11), root
imports (+4), `Examples/CorpusE0` (+4, a comment). New modules: `EmittedFile`
(146), `EmittedMapChecks` (299), `EmittedStdCore` (423), `EmittedT1Exhibit`
(664), `Examples/EmittedT1` (294), `Examples/EmittedT1Data` (42 841). No
dependency pin, lakefile, manifest or provider file changed.

**Signature census** (my own by-name recount of the two committed
snapshots, entries split on `----`, full-text compare): baseline 5 227 →
final 5 569, **ADDED 342, REMOVED 0, CHANGED 0** — identical to the author's
and their reviewer's figures. The baseline snapshot is byte-identical to
main's `2026-09-07_codex-refinement-T2-post.txt`, so the baseline IS main's
census. Additions by namespace (DERIVED): `CorpusA7` 159, `EmittedStdCore`
77, `EmittedFile` 60, `EmittedMapChecks` 23, the extern-generalised driver
lane (`DriverDoneAtExtern`, `drive_after_setup_file`, `driverDone_*_extern`,
`fileEntryState`, `evalPexpr_sym_of_compare`, …), `Audit.propextExports` 1.
Every existing public statement is unchanged; the old `t1_certified_production`
and its shipped corollary survive as the labelled wrapper regression.

**Pins**: 906 → 918 trio-exact (+12), a NEW exact category `propextExports`
(7 names, checked by `for n in propextExports do pin [``propext] n`,
Audit.lean:1165), 6 → 7 axiom-free. The categories are exact subsets of the
trio bound; the exhaustive and banned-axiom sweeps are unchanged in kind
(6 816 / 10 261 swept).

**Forbidden constructs**: none in the added Lean. `decide +kernel` appears
at concrete symbol-comparison sites in `EmittedT1Exhibit` (the pattern the
existing exhibits use). The `mkAuxLemma` device (`Examples/EmittedT1.lean:61–75`)
submits an ordinary `Eq.refl` auxiliary theorem to the kernel for the
collector equation — no native evaluation, no `ofReduce*`, covered by the
sweep; its docstring says exactly this.

**Elaboration cost** (standalone `lake env lean` of each new module under
the 40G cap, DERIVED): `Examples/EmittedT1Data` 3.3 s, `EmittedStdCore`
35.2 s (its `by decide` lookups over the data term), `Examples/EmittedT1`
3.7 s, `EmittedT1Exhibit` 3.1 s. No pass anywhere near the grind tripwire;
the 42 841-line data term is cheap for the kernel.

**The statement** (`EmittedT1Exhibit.lean:623–634`, verbatim):

```lean
theorem certified_production [LemFuel] (hfuel : 50 ≤ LemFuel.fuel)
    (cmp : EmittedFile.Comparators)
    (hstd : EmittedStdCore.intLibraryCheck cmp.stdlib = true)
    (hmain : mainLookupCheck cmp.funs = true)
    (hlabels : labelUnionCheck cmp = true)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive (restoredFile cmp).tagDefs false (restoredFile cmp) args)
          ((initial_driver_state frontendSupply (restoredFile cmp) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = lint 4 ∧
      dres.dres_blocked = false ∧ dres.dres_stdout = "" ∧ dres.dres_stderr = ""
```

Its referent is the shipped driver on `restoredFile cmp = EmittedFile.restore
cmp data` — the eleven-field file rebuilt from the quoted data with the
caller's comparators, gated by three finite `Bool` checks — from the
frontend's own initial supply. No mirror, collapse or hand-written driver
device appears in it. The transfer theorem `certified_production_of_capture_eq`
(:648) states the same for an arbitrary original `F` under `captureData F =
data` and `sup = frontendSupply`, which is the honest form of "equal to the
pipeline's file": an equality PREMISE discharged only by the executable
round-trip, exactly the [USER 2026-09-04 Q3] option (b) that the charter,
KOI A7, ARCHITECTURE §3, the README and CLAIMS C19 all state. The shipped
corollary `CorpusA7.T1.certified_production_shipped` (Shipped.lean) is the
advertised t1 certificate; `t1_certified_production_shipped` is retained and
labelled a regression.

**Machinery generality**: `EmittedFile` and `EmittedMapChecks` (the capture,
reconstruction and finite comparator-check theorems) and the extern-carrying
driver lane do not mention t1; `EmittedStdCore` deliberately depends on the
captured library data (its docstring and the charter say so). The author's
reuse experiment on `t5_ifelse.c` (record §B) exercises the tool, not a
theorem — correctly claimed as such.

**Documents**: ARCHITECTURE names the frontend artifact boundary as option
(b), the loader `scripts/emitted_frontend.lean`, the quoter, the `mkAuxLemma`
device, and "the mover is option (a)"; KOI A7 is rewritten "PARTIAL: whole-file
t1 has the option-(b) certificate; t4/t5/t6 and option (a) remain open";
CLAIMS C19's exclusions cell states the fuel floor, the captured supply, the
three checks, the transfer premises, the startup restrictions and "not a
kernel frontend theorem or equality with OCaml printed Core"; the README says
the same; `module_classes.tsv` reclassifies `CorpusT1Exhibit` as the retained
wrapper regression and classifies the six new modules; the manifest
regenerates with no drift (27 consumer modules, 19 claim rows). The master
plan and the requests register receive dated, additive progress notes that
call the slice "V1-1a" and leave V1-1b (t4/t5/t6) and option (a) open, and
mark R-4 "settled for t1" while keeping its general guarantee open — all
consistent with the plan of record. The three DECISIONS entries carry
[USER]/[AGENT] provenance, the [USER] one quoting the operator's autonomous-
execution authorisation verbatim.

**Their own review**: the fresh-reviewer range review
(`docs/2026-09-08_review-whole-file-t1-range.md`, PASS with three
documentation Notes, all confirmed resolved at `a39efb0`) is careful and its
measurements agree with mine where they overlap (census, frozen files, pins,
the proof chain's shape). I did not rely on it.

## 2. Findings

| id | severity | where | claim | how verified |
|---|---|---|---|---|
| **F1** | **Medium — REQUIRED before merge** (disclosure of a new gate prerequisite; not a soundness issue) | `scripts/check-emitted-t1.sh:12–17`, `docs/corpus-a7/README.md`, KOI §E, README "gates" | The FULL gate now depends on an EXTERNAL, UNPINNED artefact: the sibling repository's OCaml build `cerberus-lean/_build/default/backend/driver/main.exe` (+ its runtime dir), resolved by the container convention. The script fails closed if it is absent (exit 1) and byte-compares the fresh Cabs to the committed fixture (so a drifted oracle is caught loudly) — good. But the ORACLE'S IDENTITY is recorded nowhere: not in the fixture README (which gives the Cabs SHA-256 only), not in the speedbump's report, not in KOI/README. Measured: the binary's mtime is 2026-09-05 19:47; the sibling checkout is at `94f339eb4`, not our pin `89f7e68`. Anyone reproducing the gate on another machine, or after the sibling rebuilds, has no way to know which oracle produced the fixture. | `sed -n 8,18p scripts/check-emitted-t1.sh`; `grep -nE 'oracle\|sha\|version\|commit' scripts/check-emitted-t1.sh docs/corpus-a7/README.md` → the binary's identity appears nowhere; `ls -la …/main.exe`; `git -C ../cerberus-lean rev-parse --short HEAD` |
| F2 | Low (statement shape; disclosed) | `EmittedT1Data.lean:7`, `EmittedT1Exhibit.lean:631` | `frontendSupply : Nat := 36` is a captured literal in the root-of-trust statement. It is pipeline DATA (the frontend's initial supply, the same status as the 42 841-line term), checked by the speedbump (`frontendSupply + 1` rejected), quantified in the transfer theorem (`hsup : sup = frontendSupply`), and the charter says "disclosed, not renamed into claims of derivation". Acceptable under the no-magic-values ruling. Worth noting positively: this route has NO `600 ≤ sup` premise — the captured exact supply replaces the magic floor for whole-file t1. | source read; charter §"Implementation fence" |
| F3 | Low (hygiene) | branches `worker-whole-file-compare` (forks from `8eeaf92`, 50 commits ahead of its fork — an old base), `worker-whole-file-docs`, `worker-whole-file-range-review`; their worktrees | Three worker worktrees/branches remain after their content was cherry-picked or adopted. After landing: remove the worktrees; delete the branches or register them as superseded in the master plan §2. | `git worktree list`; `git merge-base` |
| F4 | Low (record hygiene) | `docs/2026-09-08_whole-file-t1-implementation.md` | The record cites ignored logs under `.lake/whole-file-evidence/` (they exist at the WORKTREE ROOT's `.lake/`, not under `cerberus-heaplang/.lake/` — say which; and note that ignored logs are ephemeral by the container rule, so the committed `2026-09-08_whole-file-t1-validation.txt` is the record). | `ls .lake/whole-file-evidence` (present at the root) |
| F5 | Info | KOI C5, `scripts/test_unit.sh` | The gate now prints 66 warning lines for 33 distinct ones because the new speedbump's nested dependency build replays them; C5's baseline method ("lines matching `^warning:`") now over-counts by 2×. Either count DISTINCT lines in C5's method or silence the nested build's replay. | `grep -c` vs `sort -u | wc -l` on the gate log |
| F6 | Info (plan bookkeeping) | master plan §3.1 G1.1, §4.1 V1-4a | The plan's `600`-site count (18) is unchanged by this slice (the wrapper is retained); when V1-1b migrates t4/t5/t6 to this route, the count and V1-4a's scope shrink — note for the plan's next revision, nothing here. | source grep |
| F7 | Info (positive) | `DriverCollapse.lean` | Changed (160 lines) — inside the charter's Phase-A fence; the extern generalisation reconstructs the original statements as specialisations (census CHANGED 0 confirms). | census; diff |

No Critical or High finding. Nothing in the range re-reports a known-open
item as new; A7, C20, B18's cite and the register/plan notes are updated
consistently with the record.

## 3. What a referee would still say (not findings against this slice)

- **Two Cerberus artefacts, one referent.** The theorem is about the pinned
  LEAN frontend's file from OCaml Cabs; the corpus-e0 `.annot.core` text the
  D6 check reads is the OCaml pipeline's. The slice states this everywhere
  it should (ARCHITECTURE §3, README, CLAIMS C19, corpus-a7 README, KOI A7,
  the register's R-4). The demo master plan's G4.3/R-4 question to the
  provider — are the two promised equal? — stays open and is now the one
  thing that separates option (b) from a referee's "genuine output".
- **Option (a) is the mover**, as ARCHITECTURE says. The trusted surface
  grew by the loader and the quoter (executable, checked by round-trip and
  an independent structural `BEq`, not proved); ARCHITECTURE §3 records them
  as such.
- **Startup restrictions** (empty globals/tags, parameterless `main`, one
  TU, no libc, one thread) are premises of `prod_run_eqJ_file` and disclosed;
  globals are the master plan's V2-9.

## 4. Required and recommended changes

Required (F1), in the landing commit, no Lean change:
1. Record the oracle's identity beside the Cabs SHA in `docs/corpus-a7/README.md`:
   the SHA-256 of `cerberus-lean/_build/default/backend/driver/main.exe` as
   used, and the cerberus-lean commit the build corresponds to (the checkout
   at build time; if unknown, say so and record the binary hash only), and
   make `scripts/check-emitted-t1.sh` print the binary's SHA-256 into its
   report so future runs show which oracle they used (a hash MISMATCH need
   not fail the gate — the byte-compare of the Cabs already does — but it
   must be visible).
2. State the new environment prerequisite where gate runners look: KOI §E
   ("the FULL gate's whole-file speedbump needs the sibling repository's
   OCaml driver build at `<path>`; absent ⇒ the gate fails closed at that
   step; `--fast` is unaffected") and the README's gates paragraph.

Recommended (F3–F5): remove the worker worktrees and register or delete
their branches after landing; fix the evidence-log path in the record; count
distinct warning lines in C5.

## 5. Provenance

[USER 2026-09-08]: "can you act as a reviewer for the demo-whole-file-t1
worktree? Write a review for the agent after which they will land it on
main. Write your review direct in their worktree docs folder." [AGENT]: the
measurements above (gate, census, frozen files, pins, elaboration timings,
source reads), the findings and their severities. Read: the charter
(`docs/2026-09-07_whole-file-t1-charter.md`), the implementation record, the
range review and its confirmation, the validation excerpts, the changed
front documents, KOI/DECISIONS/plan/register diffs, `EmittedT1Exhibit.lean`
:560–664, `Examples/EmittedT1.lean` :1–120, the speedbump scripts, the
fixture README, `Audit.lean`'s pin loops. The merge remains the operator's
explicit sign-off; this review recommends it once F1 is applied.
