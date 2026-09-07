> **Read-only copy** (made 2026-09-07 by the orchestrator for the stage-2
> Codex agent): the stage-1 record `docs/2026-09-07_codex-residuals-notes.md`
> as of commit `df5dc90`, before the L2-pin adaptation appended its section.
> The live record supersedes this file (its "Orchestrator landing notes"
> section explains the relation); this copy is deleted when stage 2 closes
> and the stage-2 charter text is repointed in the same commit. Do not edit.

# Codex residuals record — 2026-09-07

## D6 — BLOCKED: whole-text transcription check

BLOCKED: the frozen signature surface changed outside D6's allowed list
(none), between the capped pre-snapshot and the post-snapshot following a
full build. The pre-snapshot reproduced the already-present untracked
snapshot byte for byte. The full baseline gate then rebuilt dependencies
and the package. No package Lean source or pin was edited. The evidence
indicates stale primed build artifacts at entry, but the charter requires
revert and report regardless of cause; the pre-snapshot was not replaced.
The implementation was reverted with `git restore` to the source tree at
`f1f2573`; `git diff --exit-code` was empty before committing the evidence.
Evidence commit: `cec16f5c10472d9d16500ef0284c735255cd27c9`. No D6 implementation is retained.

Attempted changes, all confined to `scripts/corpus_skeleton.lean`:
`FullText` renderer/tokenizer helpers, `plantSaveLiteral`, and `checkCorpus`;
`rowStreams`, `plantVerdict`, the std.core checks and `main` consumed the
complete token streams. Constants, symbols, operator spellings, binder
and label types, punctuation and complete location markers were retained;
only layout whitespace was ignored. All four corpus rows and all three
std.core rows were equal; every existing plant and each dead-literal plant
mismatched. A temporarily corrupted t1 table row produced exit 1, quoted
below. All these script changes were reverted after the snapshot failure.

Frozen-surface command (from `cerberus-heaplang/`, for pre and post):
`../scripts/capped "$HOME/.elan/bin/lake" env lean scripts/signature_snapshot.lean`
with stdout written to `docs/2026-09-07_codex-D6-pre.txt` and
`docs/2026-09-07_codex-D6-post.txt`, respectively. Every invocation used
`CERB_MEM_MAX=40G`. `CERB_PROJ` was the worktree root,
`GIT_CONFIG_GLOBAL=/dev/null` prevented the wrapper's out-of-worktree env
self-load, and `TMPDIR` was the worktree's `cerberus-heaplang/.lake`.

Snapshot diff: `diff -u` exited 1. Derived declaration census, splitting
on the snapshot's `----` separator and comparing by printed name:
pre 1,949; post 4,950; ADDED 3,112; REMOVED 111; CHANGED 667;
UNCHANGED 1,171. **All added/removed/changed entries violate the allowed
list (none).** For example, `CerberusHeapLang.AtomicStep` gains a `Ctl`
argument; `CerbND.runNDFuel.eq_def` changes its zero-fuel branch from a
`panicWithPosWithDecl` to `[(Killed st0 CerbND.fuelExhaustedKill, [], st0)]`.
The complete before/after texts are committed as the required snapshots.
SHA-256 pre: `52627eebc1a0bd3bdb63794054a131198d466978cbbb191dbfbab1c90ef4b216`.
SHA-256 post: `1b7d097dc6956c8b258d6e953d5a2ef37687db660d8c80d1790e1b22820113d9`.

Verification: the original baseline, candidate implementation, and restored
source tree each passed `CERB_MEM_MAX=40G scripts/test_unit.sh`.
`git rebase main` before the candidate final gate and again before the
restored final gate reported the branch up to date, with no conflicts.
All three runs reported 893 trio-exact pins (expected unchanged: 893).
Package linter warning count was 48 in each run, counted from lines
beginning `warning: CerberusHeapLang/` or `warning: CerberusHeapLang.lean:`.
The candidate script had no warnings. No new theorem was added.
The restored gate's corpus step uses the original skeleton checker; its
green result does not claim delivery of D6.

Restored FULL gate tail, verbatim:

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

The candidate FULL gate's last 12 lines were identical to this restored
tail. The following is the exact output of the temporary dead-literal run
(candidate `#eval checkCorpus` with only t1's save literal changed),
including its captured process exit status. This is evidence for the
reverted candidate, not a claim about the restored checker:

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

scripts/corpus_skeleton.lean:504:0: error: corpus-skeleton: FAIL
PLANT-EXIT=1
```

Time spent from the fresh pre-snapshot through recording: approximately
14.3 minutes (03:32:44–03:47:00 UTC), plus the initial
required document reads. No single build or proof pass approached one hour.


## D5 — DONE: partial-face clients

Implementation commit: `77c237dc959690ee8539d5a38be2eeb987f039ab`.
Added `CerberusHeapLang/Examples/PartialClients.lean` as a `positive-client`
module. `PartialClients.t5_wps` proves the complete `CorpusE0.t5Main` with
the partial judgment; `PartialClients.t5_blockSpecs` verifies its return
label, whose readout is `Specified(1)`. The proof uses the public partial
rules directly. Its freshness hypothesis requires that every symbol drawn
at or above the initial supply differs from the two source bindings used
after assignment; no numeral is introduced as a supply or execution bound.
The original total proof and every existing statement are untouched.

`PartialClients.loadBind_wps` proves a whole-cell load followed by a strong
symbol binder and a return of that symbol. Its postcondition retains the
same points-to ownership, the exact read footprint, and the updated
binding. This forces the annotated-head face `wps_seq_sym_annot` and the
exact-footprint face `wps_load_footprint`. The t5 proof also consumes the
footprint face, the two `wps_neg_round` rows, `wps_excluded_store`,
`wps_excluded_store_eval`, and `wps_case_eval` through its private proof
composition helpers. The new module contains 34 private helper declarations
(evaluator, environment, and partial-rule composition facts), all included
in the in-build axiom sweep. It imports only `API` and example support.

Added its row in `scripts/module_classes.tsv`. Changed exactly the seven
`.rulePartialUndemonstrated` data rows in `scripts/capability_manifest.lean`
to `.rule`, removing the mover argument required only by the former class.
No row's shape, rule names, or `also` list changed. Regenerated
`docs/CAPABILITY_MANIFEST.md` using the gate's command, from the package:
`../scripts/capped "$HOME/.elan/bin/lake" env lean scripts/capability_manifest.lean`.
All seven rows name `Examples.PartialClients` as their partial consumer;
the generator's proof-dependency traversal verifies that consumption.

```text
MANIFEST: 35 constructors, 78 variant rows (47 RULE, 0 RULE-TOTAL-UNDEMONSTRATED, 0 RULE-PARTIAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 24 NO-RULE, 7 OUT-OF-SCOPE), 0 red, 26 consumer modules
```

Added only the three theorem pins and the import needed to resolve them
in `Audit.lean`. Each new public theorem was measured with `#print axioms`
(the commands remain in the new module). Exact output:

```text
'CerberusHeapLang.PartialClients.t5_wps' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.PartialClients.t5_blockSpecs' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.PartialClients.loadBind_wps' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Frozen surface: the capped pre-snapshot matched D6's rebuilt post-snapshot
byte for byte. After the final full gate, ran the same capped
`scripts/signature_snapshot.lean` command as D6, writing
`docs/2026-09-07_codex-D5-pre.txt` and `docs/2026-09-07_codex-D5-post.txt`.
The environment settings and cap were the same as recorded for D6.
Derived census: pre 4,950 declarations; post 4,957; ADDED 7; REMOVED 0;
CHANGED 0; UNCHANGED 4,950. The entire diff is the following additions,
exactly within D5's ADDED-only allowance:

- `CerberusHeapLang.PartialClients.loadBind`
- `CerberusHeapLang.PartialClients.loadBind_wps`
- `CerberusHeapLang.PartialClients.t5Ls`
- `CerberusHeapLang.PartialClients.t5RetQ`
- `CerberusHeapLang.PartialClients.t5_blockSpecs`
- `CerberusHeapLang.PartialClients.t5_wps`
- `CerberusHeapLang.PartialClients.ψT5`

SHA-256 pre: `1b7d097dc6956c8b258d6e953d5a2ef37687db660d8c80d1790e1b22820113d9`.
SHA-256 post: `cbe88d812d2f760ddbdbad037355771c38e7e975ad6838ad1bf35e9859ec40b5`.
The generator data changes are separately within D5's explicit allowance;
they do not contribute package declarations to this snapshot.

Validation: capped elaboration of the new module and package build both
passed. `git rebase main` immediately before the final gate reported the
branch up to date, with no conflicts. Final command from the worktree root:
`CERB_MEM_MAX=40G scripts/test_unit.sh`. Expected pins: 893 + 3 = 896;
measured: 896 trio-exact. Package linter warnings: 48 before, 48 after,
using D6's counting method; the new module has zero linter warnings.
The full gate regenerated the manifest with no drift, reported 30 boundary
modules with zero internal mentions, and passed its banned-method and
whole-package axiom sweeps. `git diff --check` was clean.

Final FULL gate tail, verbatim:

```text
ok:   Examples.CallSmoke — 0 internals mentions
ok:   Examples.ReadinessSmoke — 0 internals mentions
ok:   Examples.Layout — 0 internals mentions
ok:   Examples.CorpusE0 — 0 internals mentions
ok:   Examples.CorpusE5 — 0 internals mentions
ok:   Examples.EmittedInt — 0 internals mentions
ok:   CorpusT4Exhibit — 0 internals mentions
ok:   Examples.PartialClients — 0 internals mentions
BOUNDARY: 30 modules checked, 0 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
GATE-EXIT=0
```

Time spent from the fresh pre-snapshot through recording: approximately
9.3 minutes (03:48:18–03:57:39 UTC).
No single build or proof pass approached one hour. Stage 1 ends here:
D6 is BLOCKED and reverted; D5 is DONE. No later deliverable was started.
