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
