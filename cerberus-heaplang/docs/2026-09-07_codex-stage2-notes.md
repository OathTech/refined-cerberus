# Codex stage-2 residuals record — 2026-09-07

Worktree: `worktrees/codex-stage2`; branch: `codex/demo-residuals-2`;
entry commit: `1e1f584`. The five required documents were read in order.
All commands ran in this worktree (shell startup disabled after the first
call reported `/usr/bin/bash: /etc/profile: Permission denied`). Every
Lean invocation used `scripts/capped` with `CERB_MEM_MAX=40G`.
`CERB_PROJ` was set to this worktree, `GIT_CONFIG_GLOBAL=/dev/null`
prevented the wrapper's out-of-worktree environment self-load, and
`TMPDIR` was this worktree's `cerberus-heaplang/.lake`.

## D6 — DONE: whole-text transcription check

Implementation commit: `dd3fbbd`.
Rebuilt the check solely in `scripts/corpus_skeleton.lean`. `FullText`
renders expressions, pure expressions, values, patterns, binders, save
initializers, types, operators, symbols and complete location markers.
`FullText.tokens` compares the full lexical streams, ignoring layout
whitespace. The pinned `ocaml_frontend/pprinters/pp_core.ml` supplies the
printer contract. Unprinted metadata (symbol digests, action locations,
save passing modes) cannot be established by a text comparison; unsupported
printed forms produce errors. Source function bodies in std.core use their
source symbol spellings; corpus locals use their emitted numbered spellings.
`rowStreams`, `plantVerdict`, the std.core rows, and `checkCorpus` now use
these full streams. `plantSaveLiteral` changes only `Specified(0)` to
`Specified(7)` in the first applicable save initializer.

All four corpus rows and all three std.core rows are equal. All original
plants still mismatch. Every corpus row exercises the dead-literal plant.
The actual negative run temporarily supplied the t1 row with its dead
initializer changed to 7 to `checkCorpus`; it exited 1. The temporary test
invocation was then replaced by the normal `#eval main` in this executable
script. No library module was edited and no theorem was added.

Frozen surface: the mandatory initial FULL gate was green BEFORE the
pre-snapshot. Both snapshots used, from `cerberus-heaplang/`:

```sh
CERB_MEM_MAX=40G ../scripts/capped ~/.elan/bin/lake env lean scripts/signature_snapshot.lean > docs/2026-09-07_codex-D6-pre.txt
CERB_MEM_MAX=40G ../scripts/capped ~/.elan/bin/lake env lean scripts/signature_snapshot.lean > docs/2026-09-07_codex-D6-post.txt
diff -u docs/2026-09-07_codex-D6-pre.txt docs/2026-09-07_codex-D6-post.txt
```

Diff output is EMPTY, exit 0: ADDED 0, REMOVED 0, CHANGED 0, exactly D6's
allowed list (none). Both SHA-256 hashes:
`045e9e6133034636b9b3ac595a9494e7aad35573757338ea7c57a8abd805e390`.

Before the final gate, `git -c rebase.autoStash=true rebase main` reported
`Current branch codex/demo-residuals-2 is up to date.` and reapplied the
fenced script change without conflicts. Baseline and final gate both report
`CerberusHeapLang export pins: 901 trio-exact, 6 axiom-free-exact` (expected
unchanged). Package warning count: 33 before and 33 after, counting lines
matching `^warning: CerberusHeapLang[/\.]`; the script has no warnings.
`git diff --check` is clean.

Initial mandatory FULL gate tail, verbatim:

```text
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

D6 final FULL gate tail, verbatim:

```text
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

D6 dead-literal plant output, verbatim:

```text
# Corpus full-text check (D6: leaves, symbols, types, operators, punctuation and locations)

| corpus file | status |
|---|---|
| t1.annot.core | transcribed |
| t10_evenodd.annot.core | pending — E6 (`Eccall`; mutual recursion) |
| t2.annot.core | pending — E6 (`Eccall`; the helper call in a `for` loop) |
| t3_ptrarg.annot.core | pending — E6 (`Eccall`, `PtrValidForDeref`) |
| t4_while.annot.core | transcribed |
| t5_ifelse.annot.core | transcribed |
| t6_switch.annot.core | transcribed |
| t7_struct.annot.core | pending — outside E — KOI B4 (`tagDefs`) |
| t8_array.annot.core | pending — E6 (arrays; `PtrValidForDeref`) |
| t9_fact.annot.core | pending — E7 (the outcome-list closed form) |

coverage sweep: every corpus file rowed or pending; plant (t1 row dropped) fails (expected)

| file | proc | tokens | term = text | plant: bound dropped | plant: Astd stripped | plant: Specified unwrapped | plant: save initialiser unwrapped | E5 operand plants |
|---|---|---|---|---|---|---|---|---|
FAIL: t1.annot.core/main: full text mismatch
  first difference at token 304: term `7`, text `0`
FAIL: t1.annot.core: no save initialiser Specified(0) for the dead-literal plant
| t1.annot.core | main | 312 | DIFFER | mismatch (expected) | mismatch (expected) | mismatch (expected) | mismatch (expected) | case scrutinee: n/a; if condition: n/a; case pattern: n/a |
dead-literal plant: t5_ifelse.annot.core/main: save Specified(0) -> Specified(7): mismatch (expected)
| t5_ifelse.annot.core | main | 652 | equal | mismatch (expected) | mismatch (expected) | mismatch (expected) | mismatch (expected) | case scrutinee: mismatch (expected); if condition: mismatch (expected); case pattern: mismatch (expected) |
dead-literal plant: t6_switch.annot.core/main: save Specified(0) -> Specified(7): mismatch (expected)
| t6_switch.annot.core | main | 726 | equal | mismatch (expected) | mismatch (expected) | mismatch (expected) | mismatch (expected) | case scrutinee: mismatch (expected); if condition: mismatch (expected); case pattern: mismatch (expected) |
dead-literal plant: t4_while.annot.core/main: save Specified(0) -> Specified(7): mismatch (expected)
| t4_while.annot.core | main | 1504 | equal | mismatch (expected) | mismatch (expected) | mismatch (expected) | mismatch (expected) | case scrutinee: mismatch (expected); if condition: mismatch (expected); case pattern: mismatch (expected) |

# E3: transcribed std.core fragment vs the pinned std.core source

| fun | tokens | term = source | plants (applicable: verdict) |
|---|---|---|---|
| is_representable_integer | 16 | equal | Ivmin/Ivmax swapped: mismatch (expected) |
| conv_int | 47 | equal | first if's branches swapped: mismatch (expected) |
| conv_loaded_int | 35 | equal | first case's alternatives reversed: mismatch (expected) |

scripts/corpus_skeleton.lean:485:0: error: corpus-skeleton: FAIL
PLANT-EXIT=1
```

Time from the pre-snapshot through recording: approximately 7.3
minutes (pre-snapshot 05:56:02
UTC; recorded 06:03:18 UTC), plus required initial reads and the
baseline gate. No individual build or proof pass approached one hour.

## D7 — DONE: head-form scaffold and E5 duplications

Implementation commit: `ad27dd3`.

The source census at this checkout found 51 head-form scaffold sites:
2 in Soundness, 12 in DriverCollapse, and 37 in Round (the charter's
42-site count is stale). They now use the single private theorem
`map_cons_of_eq`, through `step_ctx_head`. It exposes the generated
`step_ctx` map, applies the get_ctx cons equation, and abstracts the
untouched mapped suffix before redex case splits. The old intermediate
`key` / `head?` / `cons_of_head?` scaffolds are gone from these sites.
The existing public `cons_of_head?` theorem is retained unchanged.

`step_ctx_excluded_store_eval_ws'` moved, with IDENTICAL name and statement,
from Round to DriverCollapse. The pointer-specific
`step_ctx_excluded_store_eval_ws` delegates to it. The shared
`excluded_store_eval` tactic carries the dispatch for the general success,
shape and two failure faces. The nine repeated recursive-context arms of
`Decomp.lift_neg'` use one `neg_context` macro; the distinct root and bound
cases remain structural cases of the induction.

The three local frame/lookup macro pairs were replaced by the shared
`emitted_frame` / `emitted_lookup` definitions. The three E5
`t4Main_labeledAt` / `t5Main_labeledAt` / `t6Main_labeledAt` proof bodies use
`labeled_main`. `symK_eval` delegates to `symC_eval` at an empty-extern
context. At entry, `depLe*` was already absent, and each of the three pinned
`wpt_t*Load` rules already delegated to `wpt_emittedIntLoad`; these existing
shared proofs were retained. The public `t*Kill_eq` rules were already
single `rfl` wrappers for their distinct source locations; their statements
and bodies are retained (the transcription definitions are outside D7's
fence). No public wrapper was deleted, renamed or restated.

No new public theorem was introduced: the new map lemma is PRIVATE and
covered by the package axiom sweep. No pin edit was made. The five new
snapshot entries are the parser definitions of the shared tactics;
`neg_context` and its parser are local/private. Frozen-surface census:
pre 5212, post 5217, ADDED 5, REMOVED 0,
CHANGED 0. Every existing entry is byte-identical. The complete diff is
exactly the shared-definition additions permitted by D7:

```diff
--- docs/2026-09-07_codex-D7-pre.txt	2026-09-07 06:04:11.727073809 +0000
+++ docs/2026-09-07_codex-D7-post.txt	2026-09-07 06:16:52.627622108 +0000
@@ -45346,12 +45346,24 @@
 def CerberusHeapLang.t6frAssign :
 Nat → Nat → Int → CerbMem.PointerValue → Fmap sym value → Fmap sym value
 ----
+def CerberusHeapLang.tacticEmitted_frame :
+ParserDescr
+----
+def CerberusHeapLang.tacticEmitted_lookup :
+ParserDescr
+----
+def CerberusHeapLang.tacticLabeled_main_ :
+ParserDescr
+----
 def CerberusHeapLang.tacticLoc_split_ :
 ParserDescr
 ----
 def CerberusHeapLang.tacticLoc_split_at__ :
 ParserDescr
 ----
+def CerberusHeapLang.tacticStep_ctx_head_ :
+ParserDescr
+----
 theorem CerberusHeapLang.take_sum_succ :
 ∀ (vs : List Int) (i : Nat) (h : i < vs.length),
   (List.take (i + 1) vs).sum = (List.take i vs).sum + vs[i]
@@ -51658,6 +51670,9 @@
 ∀ {params : List (sym × core_base_type)} {pes : List (generic_pexpr Unit sym)}
   {pe : generic_pexpr Unit sym}, pe ∈ CerberusHeapLang.zipArgs params pes → pe ∈ pes
 ----
+def CerberusHeapLang.«tacticExcluded_store_eval_,_,_,_,_=>_» :
+ParserDescr
+----
 def CerberusHeapLang.«term_↦c[_]_;_» :
 TrailingParserDescr
 ----
```

Snapshot commands are the D6 commands with `D7` substituted, using the
same capped environment. SHA-256 pre:
`045e9e6133034636b9b3ac595a9494e7aad35573757338ea7c57a8abd805e390`;
post: `0cb8fd9f6d05c813b2b296fa31c751566c96f9e74e8a1ce93ba3478417608df8`.

The initial direct-cons proof exposed the generated map's suffix to
simplification and hit the existing heartbeat limit in Soundness.
Abstracting that suffix fixed the proof without changing any limit;
Soundness then built in 42 seconds (later rebuild 24 seconds).
Two subsequent macro-quotation type errors were corrected. The round-layer
build passed (Round 22 seconds). All builds were capped, and no red build
was committed on the working branch. Before the final FULL gate,
`git -c rebase.autoStash=true rebase main` reported the working branch
up to date, without conflicts. The final FULL gate reports the expected
unchanged `901 trio-exact, 6 axiom-free-exact` pins, and 33 package warnings
(33 before). The changed modules introduce no warnings.
`git diff --check` is clean. An independent source-text comparison also
found all 676 public theorem statements in the seven edited modules
unchanged; the compiled snapshot above is the acceptance evidence.

D7 final FULL gate tail, verbatim:

```text
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

Time from pre-snapshot through recording: approximately
13.5 minutes
(06:04:11–06:17:43 UTC).
No individual build or proof pass approached one hour.

## D1 — BLOCKED: driver-kill adequacy interface

BLOCKED: the fixed `hwp` requires a kill-capable total/prefix judgment that
the existing Wpt interface does not provide; implementing that design is
outside D1's fence; parked at codex/park-D1
`55b54b531fd1dfe4bc88844fa3004cb1081e74c6`.

Investigation parked without inventing a new judgment or theorem statement.
The fixed requirement asks for `wpt_driver_done_alloc`'s premise list with
`hwp` delivering a KILL classification. `Wpt.lean:151–206` defines the
current total judgment: its terminal clause is a `SpikeVal` postcondition;
its nonterminal step clause requires `PrimStep.Reducible` and continues
through every mirrored step. There is no kill clause (`evalClass` and
`EvalFail` do not occur in Wpt). A pure classifier equality is a theorem
about operand evaluation, not a derivation of this judgment on a prefix
ending at a killing redex.

`ProdLoop.lean:444–458` consumes that judgment with `readoutPost ψ`, where
`ψ : value → Mem → Prop`. Its existing result `DriverDoneAt` at
`ProdLoop.lean:63–87` requires an `NDactive` PROGRAM-DONE outcome. Substituting
a classifier equality into the readout cannot change that result into an
`NDkilled` outcome. In addition, the generic launch premises describe an
arbitrary `e₀`, memory, environment and context; they do not tie a cold-start
file `f`, supply `sup`, filesystem and arguments to those inputs.

The existing useful downstream components are present:
`overflow_driver2_killed` / `overflow_driver2_killed_frame` prove the UB036
kill from `progCE3_atAdd`; `drive_after_setup_lib_killed` in ProdEntry
already propagates a driver kill through setup. They do not provide the
missing prefix judgment. Completing the requested generic lemma therefore
requires a specified kill-capable total/prefix interface and its adequacy,
or a changed premise list/goal allowing a direct engine-prefix proof.
That is a design choice outside this fixed D1 goal; editing Wpt is outside
D1's fence. No vacuous theorem, new assumption, trace-as-premise, renamed
judgment or replacement statement was introduced. No Lean source was edited.


After parking, switched to `codex/demo-residuals-2` and reset it to its last
green commit `9defae7`; the investigation and pre-snapshot remain committed
on the park branch. `git rebase main` reported the branch up to date,
without conflicts. The restored FULL gate is green with unchanged
901 trio-exact / 6 axiom-free-exact pins and 33 package warnings.

Both D1 snapshots used the charter's capped command. Their diff is EMPTY
(exit 0): ADDED 0, REMOVED 0, CHANGED 0. Both SHA-256 hashes:
`0cb8fd9f6d05c813b2b296fa31c751566c96f9e74e8a1ce93ba3478417608df8`. This establishes that parking
preserved the working branch's public surface; it does not establish D1.

D1 restored FULL gate tail, verbatim:

```text
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

Time spent: approximately 4.0 minutes since
D7's record commit, including the investigation, snapshots, parking and
restored gate (recorded 06:21:58 UTC). No proof campaign or single
build approached one hour. D1 remains BLOCKED; no whole-run overflow
theorem is claimed.

## D2 — BLOCKED: inconsistent fixed range premise

BLOCKED: the fixed goal requires a numeral-free range copied verbatim from
a rule whose range has numeric bounds; changing that spelling requires a
statement choice outside the charter; parked at codex/park-D2
`09f9b9018a53f54e32931e1d1230d83a26c75fea`.

The requested fixed statement says `hrange` is the range premise for
`n + 1` spelled EXACTLY as `wps_c_add` in IntRules, with “no numeral”.
The actual `wps_c_add` at `IntRules.lean:586–598` has two numeric sum
premises, verbatim:

```lean
    (hs : -2147483648 ≤ n1 + n2) (hs' : n1 + n2 ≤ 2147483647) :
```

Its total twin has the same two premises. There is no numeral-free range
predicate in this rule to copy. Substituting `n` and `1` leaves these
numeric bounds; using engine min/max expressions instead changes the
required verbatim spelling; combining both inequalities or retaining only
the upper one (using `hn` for the lower bound) chooses a statement the
charter has not fixed. IntRules is outside D2's fence and may not be
changed to manufacture the requested spelling.

The implementation path after a corrected statement is visible: Heap
already has `intToBytes_eq` / `intToBytes_length` and unsigned fold lemmas
(Heap.lean:778–825), while `three_storable` / `three_reconstruct` in
EmittedCExhibit are literal-3 proofs and the total proof's frame/label
helpers are also specialized to 3/4. No claim is made that symbolic
storability is impossible. The blocker is the contradictory acceptance
statement: the charter calls it fixed and disallows choosing a new shape.
No Lean source was edited and no theorem was fabricated. The park stores
this investigation and D2's fresh pre-snapshot.

After parking, returned the working branch to `51efef2`. `git rebase main`
reported it up to date, without conflicts. The restored FULL gate is green
with unchanged 901 trio-exact / 6 axiom-free-exact pins and 33 package
warnings. No public theorem was added or changed.

Both capped D2 snapshots are byte-identical: diff EMPTY, exit 0,
ADDED 0, REMOVED 0, CHANGED 0. Both SHA-256 hashes:
`0cb8fd9f6d05c813b2b296fa31c751566c96f9e74e8a1ce93ba3478417608df8`. This is restoration evidence,
not a claim that D2 was implemented.

D2 restored FULL gate tail, verbatim:

```text
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

Time spent: approximately 3.6 minutes since
D1's record commit, including investigation, snapshots, parking and the
restored gate (recorded 06:25:32 UTC). No build or proof pass approached
one hour. D2 remains BLOCKED.


## D3 — BLOCKED: required gate change outside the fence

The fixed acceptance requires gate 1b to reject `600` outside a
`*_shipped` corollary and requires a plant demonstrating that rejection.
`test_unit.sh:41–45` delegates gate 1b to
`scripts/fuel_numeral_check.sh`. That script's `NUMERALS` at line 37
matches the existing fuel spellings only; it does not match `600`.
Neither script is in D3's fence. The fence permits one module for
`symBound`, the three corpus exhibits, Audit pins and this record.
Consequently the mandatory gate extension cannot be completed within the
fence. Moving a gate implementation into an exhibit or Audit pin list
would not be an authorized substitute. No source implementation was begun
once this acceptance blocker was established; this park preserves the
investigation and the fresh pre-snapshot.

Read-only execution of the existing gate while all 14 premises are still
present confirms the missing check (this is not the requested successful
plant test):

```text
ok: no fuel numeral (100000000/1000000/999999) outside a *_shipped corollary and no retired fuel constant (60 files scanned, comments stripped)
GATE1B-EXIT=0
```

Complete `hsup : 600 ≤ …` census at this head (2 + 3 + 9 = 14):

| File | Line | Declaration | Bound target |
| --- | ---: | --- | --- |
| CorpusT5Exhibit.lean | 426 | t5_wpt | M.runState.sym_supply |
| CorpusT5Exhibit.lean | 543 | t5_certified_production | sup |
| CorpusT6Exhibit.lean | 423 | wpt_t6Case2 | M.runState.sym_supply |
| CorpusT6Exhibit.lean | 473 | t6_blockSpecsT | M.runState.sym_supply |
| CorpusT6Exhibit.lean | 749 | t6_certified_production | sup |
| CorpusT4Exhibit.lean | 778 | wpt_t4AssignS | M.runState.sym_supply |
| CorpusT4Exhibit.lean | 827 | wpt_t4AssignI | M.runState.sym_supply |
| CorpusT4Exhibit.lean | 926 | wpt_t4Body | M.runState.sym_supply |
| CorpusT4Exhibit.lean | 1154 | wpt_t4LoopStep | M.runState.sym_supply |
| CorpusT4Exhibit.lean | 1199 | wpt_t4WhileCont | M.runState.sym_supply |
| CorpusT4Exhibit.lean | 1254 | t4_blockSpecsT | M.runState.sym_supply |
| CorpusT4Exhibit.lean | 1292 | wpt_t4WhileEntry | M.runState.sym_supply |
| CorpusT4Exhibit.lean | 1315 | t4_wpt | M.runState.sym_supply |
| CorpusT4Exhibit.lean | 1426 | t4_certified_production | sup |

No `symBound`, specification lemma or negative pipeline theorem is
claimed. The blocker concerns completion under the file fence; it is not
a claim that program-derived symbol bounds are unprovable.

BLOCKED: D3 requires changing gate 1b, but its implementation scripts are
outside the explicit D3 file fence; parked at codex/park-D3
`450c87eddab3a2d97fb08ac52bf92f13cdf3bddb`.

After parking, returned the working branch to `539c83f`. `git rebase main`
reported it up to date, without conflicts.

The restored FULL gate is green with unchanged 901 trio-exact /
6 axiom-free-exact pins and 33 package warnings. Both capped D3
snapshots are byte-identical: diff EMPTY, exit 0; ADDED 0, REMOVED 0,
CHANGED 0. Both SHA-256 hashes:
`0cb8fd9f6d05c813b2b296fa31c751566c96f9e74e8a1ce93ba3478417608df8`.
This verifies preservation of the working branch, not completion of D3.

D3 restored FULL gate tail, verbatim:

```text
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

Time spent: approximately 5.5 minutes since
D2's record, including investigation, census, snapshots, parking and the
restored gate (recorded 06:31:04 UTC). No build or proof pass
approached one hour. D3 remains BLOCKED.


## D4 — BLOCKED: required placement and pins outside the fence

The requested definition and rule replacement are understood. The current
pure continuation premise is identical in both rules:

```lean
⌜∃ k, s = fresh_given_int k ∧ M.runState.sym_supply ≤ k⌝
```

It occurs at `Wps.lean:5295` / `Wpt.lean:4876`, inside
`wps_neg_bound` / `wpt_neg_bound`. The requested abstraction packages this
existential with the conjunction reversed; no unrelated statement change
would be needed to perform that replacement.

However, D4 requires `FreshAbove.intro` and `FreshAbove.ne_of_lt` as
new public lemmas, and charter §1 rule 4 requires every new public theorem
to be measured trio-exact and pinned in `Audit.lean`. D4's explicit fence
omits Audit: it permits Rules, Wps, Wpt, E5 exhibit proof bodies and the
record. The pin lists are actual closed lists (`trioExports` at
`Audit.lean:270`, with the existing two rules pinned at lines 939/942),
checked by the exact-pin loop at lines 1116–1131; the separate exhaustive
sweep does not automatically pin newly added exports. Therefore adding the
mandatory public lemmas cannot meet the mandatory pin requirement within
this fence. Making the lemmas private, leaving them unpinned, modifying the
pin list through another module or treating a bounded sweep as an exact
pin would not meet the charter.

There is also a placement mismatch: the goal says FreshAbove lives beside
SymFrame, but `SymFrame` is defined in `EnvLaws.lean:309`, which is outside
D4's fence. Placing FreshAbove in Rules would require an interpretation of
“beside” as a different module; it would still not resolve the pin fence.

The existing direct total-rule application is in
`Examples/EmittedInt.lean:227`; its continuation statement at line 211
and the corpus wrapper statements (T4 line 726, T5 lines 193/381, T6 line
241) still expose the old existential. The charter freezes those client
statements, so any eventual implementation must preserve them while
adapting their proof bodies. This is not claimed as an additional blocker.
No PartialClients file was changed. No Lean source, theorem, pin or public
statement was changed; the park preserves the investigation and the fresh
pre-snapshot. No claim is made that the freshness lemmas are unprovable.

BLOCKED: D4's mandatory new public theorem pins require Audit, and its
requested placement beside SymFrame points to EnvLaws; both files are
outside D4's fence; parked at codex/park-D4
`2ad35c790c6051d9364dd7a3888a847609c5ef44`.

After parking, returned the working branch to `c5d60d9`. `git rebase main`
reported it up to date, without conflicts.

The restored FULL gate is green with unchanged 901 trio-exact /
6 axiom-free-exact pins and 33 package warnings. Both capped D4
snapshots are byte-identical: diff EMPTY, exit 0; ADDED 0, REMOVED 0,
CHANGED 0. Both SHA-256 hashes:
`0cb8fd9f6d05c813b2b296fa31c751566c96f9e74e8a1ce93ba3478417608df8`.
This verifies preservation of the working branch, not completion of D4.
No new public theorem was added, so there is no new axiom output or pin.

D4 restored FULL gate tail, verbatim:

```text
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

Time spent: approximately 3.2 minutes since
D3's record, including investigation, snapshots, parking and the restored
gate (recorded 06:34:18 UTC). No build or proof pass approached
one hour. D4 remains BLOCKED. The six authorized deliverables have now
been processed in order; work stops here, with D8/D9 untouched.
