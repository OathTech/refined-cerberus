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


## D5 re-based onto the L2 pin (orchestrator's worker)

[AGENT 2026-09-07] Not Codex: the orchestrator's worker, in
`worktrees/codex-residuals` on `codex/demo-residuals`, entering at
`df5dc90` (the four Codex commits rebased onto main `6b6d9a8`, the L2
re-pin; `.lake`/`.cerberus-ws` primed at cerberus-lean
`89f7e688530c6910884518811d645e4e892e4507`, LemLib `f6542f8`). Task: make
D5 (commit `98335e2`) build and pass at the new pin, changing nothing else.
The charter's §1 rules bind: fence = `CerberusHeapLang/Examples/PartialClients.lean`
(proofs and forced binders), `docs/CAPABILITY_MANIFEST.md` (regenerated),
the snapshot `docs/2026-09-07_codex-D5b-post.txt`, this record. No other
file was edited; `Audit.lean`'s three pins, `scripts/capability_manifest.lean`
and `scripts/module_classes.tsv` stand as rebased. Every `lake`/`lean`
invocation through `scripts/capped` at `CERB_MEM_MAX=64G` (sole builder);
zero `UNCAPPED` lines in every log. `git rebase main` was not needed: main
stayed at `6b6d9a8` (= the branch's merge-base) throughout, re-checked
before the commit and before the gate.

### Entry state, verbatim classes

`lake build` at `df5dc90`: `PartialClients.lean` red with 39 errors —
36 × `failed to synthesize instance of type class LemFuel` and three
downstream of those (`Invalid dotted identifier notation: The expected type
of .IV could not be determined` at `alignofIval_intTy`; `Failed to rewrite
using equation theorems for t5BoolBranch` and `No goals to be solved` on
statements that had elaborated to `sorry`). With the binders in place, 4
errors remained, all `Application type mismatch: The argument
Nat.le_of_ble_eq_true ?m … is expected to have type Nat` at `wps_bound`
(three sites) and `wps_bound_wseq_tuple` (one site). After the fixes below:
0 errors, 0 warnings from the module.

### What the pin forced — every edit, with its reason

- **E1 `[LemFuel]` on six pure-evaluator / memory-conversion helpers**
  (`alignofIntPe_eval`, `alignofIval_intTy`, `unspec_encodes`,
  `unspecIntPe_eval`, `t5BoolBranch_eval`, `t5CondPe_eval`): their
  statements mention `evalPexpr`, `memValueFromValue` or
  `CerbMem.alignofIval`, each `[LemFuel]`-quantified at the pin (the engine's
  pure evaluator reads the ambient instance — FUEL.md §1, §4; the same
  binder the sibling `EmittedInt.lean:32/41/50/82/100/179` carries).
- **E2 `[LemFuel]` on ten `wps`-stating private helpers**
  (`wps_unseq_pure_right`, `wps_emittedIntStore`, `wps_t5Load`, `wps_t5Gt`,
  `wps_t5Cond`, `wps_t5AssignBlock`, `wps_t5Bool`, `t5Ls_readout`,
  `wps_t5Return`, `wps_t5If`): the judgment `wps` (Wps.lean:185
  `variable [LemFuel]`, `:322`) and `readoutPost` are `[LemFuel]`-quantified.
- **E3 the three public theorems**: `[LemFuel]` on `t5_wps`, `t5_blockSpecs`,
  `loadBind_wps` (same reason as E2); `t5_wps` additionally
  `(hfuel : 0 < LemFuel.fuel)` — see the decision below.
- **E4 `wps_create`'s new premises** at the two `create` sites of `t5_wps`:
  `(hfuel := hfuel) (halign := by decide) (haddr := rfl)` — the public
  allocation rule (Wps.lean:4203–4211) now carries `hfuel : 0 < LemFuel.fuel`,
  `halign : 0 < alignN`, `haddr : get_with_address a = none` (L2 record §6,
  Z2-alloc); the discharge is byte-for-byte the sibling total client's
  (`CorpusT5Exhibit.lean:448/465`).
- **E5 the retired fuel ceiling** at `wps_bound` (three sites) and
  `wps_bound_wseq_tuple` (one): the trailing `(Nat.le_of_ble_eq_true rfl)`
  dropped. At `46c28dc` `wps_bound` read `(hnf : negFree b = true) (hpot :
  pot b ≤ lemDefaultFuel)`; at the pin it reads `(hnf : negFree b = true)`
  only (Wps.lean:1333–1334) — R2 retired `pot`/`esize` (L2 record §3).
- **E6 `emittedInt_storable`'s int range** (EmittedInt.lean:185–186, L2 §6
  Z2-mem-repr): `hv1 hv2` supplied in `wps_emittedIntStore`,
  `(by decide) (by decide)` at the literal-3 store in `t5_wps`.
- **E7 `#print axioms` out of the module** (they printed three `info:` lines
  at every build); measured once out of tree (below). One sentence added to
  `t5_wps`'s docstring naming `hfuel`.

Not touched because the pin did not force it (no error, fuel-free at the
pin): `intTy_size_pos`, `intTy_nonatomic`, `intTy_decIndep`, `unspecMval`,
`unspec_storable`, `t5Gt_select`, `t5Cond_select`, `t5BoolBranch`,
`t5Bool_select`, `t5RetQ` and its three lemmas, `t5fr529_lookup`, `t5Ls`,
`ψT5`, `t5Kill_eq`, `t5Store_eq`, `loadBind`, the local macros.

**Decision [AGENT]: explicit per-declaration `[LemFuel]`, not a
`variable [LemFuel]`.** A section variable would be included in every
declaration and trip the unused-section-variable linter on the fuel-free
ones (the L2 audit's H-1 class, twelve `omit`s); the sibling modules
(`EmittedInt`, `CorpusT5Exhibit`) bind it per declaration. Result: the module
contributes zero warnings; the package stays at 33.

**Decision [AGENT]: `hfuel : 0 < LemFuel.fuel` on `t5_wps` is a forced
statement change beyond the brief's "`[LemFuel]`/`hdep`" wording, taken as
being of the same class.** `wps_create` carries it as a premise (Wps.lean:4207;
its docstring: "Side premises require positive memory-bind fuel and
alignment, no requested-address annotation"); no client of the rule can
discharge it without a hypothesis; the sibling total statement is
`t5_wpt [LemFuel] (hfuel : 0 < LemFuel.fuel) [SpikeGS .hasLC GF]`
(CorpusT5Exhibit.lean:429) and the binder is placed identically. No numeral,
no new axiom, kernel-only. `t5_blockSpecs` and `loadBind_wps` needed the
instance only (no fuel hypothesis: `wps_load_footprint`, `wps_seq_sym_annot`,
`wps_pure`, `wps_annot`, `blockSpecs_intro` carry none). The orchestrator may
re-adjudicate; the before/after is below.

### The three public statements — before (`98335e2`) / after (`7bdf408`)

Header lines verbatim; the remainder of each header is unchanged. The
elaborated forms are the three `theorem` entries of
`docs/2026-09-07_codex-D5b-post.txt`.

```text
- theorem t5_wps [SpikeGS .hasLC GF]
+ theorem t5_wps [LemFuel] (hfuel : 0 < LemFuel.fuel) [SpikeGS .hasLC GF]
- theorem t5_blockSpecs [SpikeGS .hasLC GF]
+ theorem t5_blockSpecs [LemFuel] [SpikeGS .hasLC GF]
- theorem loadBind_wps [SpikeGS .hasLC GF]
+ theorem loadBind_wps [LemFuel] [SpikeGS .hasLC GF]
```

The whole module change, `git diff -U0 98335e2 7bdf408 --
cerberus-heaplang/CerberusHeapLang/Examples/PartialClients.lean` (verbatim;
30 insertions, 32 deletions):

```diff
diff --git a/cerberus-heaplang/CerberusHeapLang/Examples/PartialClients.lean b/cerberus-heaplang/CerberusHeapLang/Examples/PartialClients.lean
index 00fcf35..096e583 100644
--- a/cerberus-heaplang/CerberusHeapLang/Examples/PartialClients.lean
+++ b/cerberus-heaplang/CerberusHeapLang/Examples/PartialClients.lean
@@ -22 +22 @@ variable {GF : BundledGFunctors}
-private theorem alignofIntPe_eval {tds : CerbTags.TagDefsMap} (ext : Fmap sym sym)
+private theorem alignofIntPe_eval [LemFuel] {tds : CerbTags.TagDefsMap} (ext : Fmap sym sym)
@@ -28 +28 @@ private theorem alignofIntPe_eval {tds : CerbTags.TagDefsMap} (ext : Fmap sym sy
-private theorem alignofIval_intTy {tds : CerbTags.TagDefsMap} :
+private theorem alignofIval_intTy [LemFuel] {tds : CerbTags.TagDefsMap} :
@@ -43 +43 @@ private def unspecMval : CerbMem.MemValue := CerbMem.unspecifiedMval intTy
-private theorem unspec_encodes {tds : CerbTags.TagDefsMap} :
+private theorem unspec_encodes [LemFuel] {tds : CerbTags.TagDefsMap} :
@@ -50 +50 @@ private theorem unspec_storable (tds : CerbTags.TagDefsMap) : StorableAt tds int
-private theorem unspecIntPe_eval {tds : CerbTags.TagDefsMap} (ext : Fmap sym sym)
+private theorem unspecIntPe_eval [LemFuel] {tds : CerbTags.TagDefsMap} (ext : Fmap sym sym)
@@ -55 +55 @@ private theorem unspecIntPe_eval {tds : CerbTags.TagDefsMap} (ext : Fmap sym sym
-private theorem wps_unseq_pure_right [SpikeGS .hasLC GF]
+private theorem wps_unseq_pure_right [LemFuel] [SpikeGS .hasLC GF]
@@ -100 +100 @@ private theorem wps_unseq_pure_right [SpikeGS .hasLC GF]
-private theorem wps_emittedIntStore [SpikeGS .hasLC GF]
+private theorem wps_emittedIntStore [LemFuel] [SpikeGS .hasLC GF]
@@ -129 +129 @@ private theorem wps_emittedIntStore [SpikeGS .hasLC GF]
-    (emittedInt_encodes _ v) (emittedInt_storable _ v)
+    (emittedInt_encodes _ v) (emittedInt_storable _ v hv1 hv2)
@@ -149 +149 @@ private theorem t5Bool_select : select_case subst_sym_expr (lint 0) t5BoolPats =
-private theorem t5BoolBranch_eval {M : MachineCtx} (ρ : EnvStack) :
+private theorem t5BoolBranch_eval [LemFuel] {M : MachineCtx} (ρ : EnvStack) :
@@ -160 +160 @@ private theorem t5BoolBranch_eval {M : MachineCtx} (ρ : EnvStack) :
-private theorem t5CondPe_eval {M : MachineCtx} (hstd : StdE3 M.file) {ρ : EnvStack}
+private theorem t5CondPe_eval [LemFuel] {M : MachineCtx} (hstd : StdE3 M.file) {ρ : EnvStack}
@@ -173 +173 @@ private theorem t5CondPe_eval {M : MachineCtx} (hstd : StdE3 M.file) {ρ : EnvSt
-private theorem wps_t5Load [SpikeGS .hasLC GF]
+private theorem wps_t5Load [LemFuel] [SpikeGS .hasLC GF]
@@ -213 +213 @@ private abbrev t5frGt (px : CerbMem.PointerValue) (f : Fmap sym value) :=
-private theorem wps_t5Gt [SpikeGS .hasLC GF]
+private theorem wps_t5Gt [LemFuel] [SpikeGS .hasLC GF]
@@ -255 +255 @@ private abbrev t5frCond (px : CerbMem.PointerValue) (f : Fmap sym value) :=
-private theorem wps_t5Cond [SpikeGS .hasLC GF]
+private theorem wps_t5Cond [LemFuel] [SpikeGS .hasLC GF]
@@ -268 +268 @@ private theorem wps_t5Cond [SpikeGS .hasLC GF]
-  iapply wps_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
+  iapply wps_bound _ _ _ rfl
@@ -293 +293 @@ private theorem wps_t5Cond [SpikeGS .hasLC GF]
-private theorem wps_t5AssignBlock [SpikeGS .hasLC GF]
+private theorem wps_t5AssignBlock [LemFuel] [SpikeGS .hasLC GF]
@@ -315 +315 @@ private theorem wps_t5AssignBlock [SpikeGS .hasLC GF]
-  iapply wps_bound_wseq_tuple _ _ _ _ _ _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
+  iapply wps_bound_wseq_tuple _ _ _ _ _ _ _ _ rfl
@@ -346 +346 @@ private theorem wps_t5AssignBlock [SpikeGS .hasLC GF]
-private theorem wps_t5Bool [SpikeGS .hasLC GF]
+private theorem wps_t5Bool [LemFuel] [SpikeGS .hasLC GF]
@@ -392 +392 @@ def ψT5 : value → Mem → Prop := fun v _ => v = lint 1
-private theorem t5Ls_readout [SpikeGS .hasLC GF] :
+private theorem t5Ls_readout [LemFuel] [SpikeGS .hasLC GF] :
@@ -402 +402 @@ private theorem t5Ls_readout [SpikeGS .hasLC GF] :
-theorem t5_blockSpecs [SpikeGS .hasLC GF]
+theorem t5_blockSpecs [LemFuel] [SpikeGS .hasLC GF]
@@ -432 +432 @@ private theorem t5Kill_eq (x : sym) : CorpusE0.t5Kill x =
-private theorem wps_t5Return [SpikeGS .hasLC GF]
+private theorem wps_t5Return [LemFuel] [SpikeGS .hasLC GF]
@@ -448 +448 @@ private theorem wps_t5Return [SpikeGS .hasLC GF]
-  iapply wps_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
+  iapply wps_bound _ _ _ rfl
@@ -482 +482 @@ private abbrev t5frIf (px pr : CerbMem.PointerValue) (f : Fmap sym value) :=
-private theorem wps_t5If [SpikeGS .hasLC GF]
+private theorem wps_t5If [LemFuel] [SpikeGS .hasLC GF]
@@ -533,2 +533,4 @@ private theorem t5Store_eq (a : List annot) (loc : CerbLocation.Loc) (pe2 pe3 :
-    it carries no numeric supply or execution bound. -/
-theorem t5_wps [SpikeGS .hasLC GF]
+    it carries no numeric supply or execution bound. `hfuel` is the public
+    allocation rule's own premise at the L2 pin (`wps_create`: positive
+    memory-bind fuel), not a bound introduced by this proof. -/
+theorem t5_wps [LemFuel] (hfuel : 0 < LemFuel.fuel) [SpikeGS .hasLC GF]
@@ -554 +556 @@ theorem t5_wps [SpikeGS .hasLC GF]
-  iapply wps_create _ _ empty_annotation .Prov_none 4 intTy (PrefSource (t5Reg 15 84) [CorpusE0.xSym])
+  iapply wps_create (hfuel := hfuel) (halign := by decide) (haddr := rfl) _ _ empty_annotation .Prov_none 4 intTy (PrefSource (t5Reg 15 84) [CorpusE0.xSym])
@@ -570 +572 @@ theorem t5_wps [SpikeGS .hasLC GF]
-  iapply wps_create _ _ empty_annotation .Prov_none 4 intTy (PrefSource (t5Reg 15 84) [t5rSym])
+  iapply wps_create (hfuel := hfuel) (halign := by decide) (haddr := rfl) _ _ empty_annotation .Prov_none 4 intTy (PrefSource (t5Reg 15 84) [t5rSym])
@@ -582 +584 @@ theorem t5_wps [SpikeGS .hasLC GF]
-  iapply wps_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
+  iapply wps_bound _ _ _ rfl
@@ -594 +596 @@ theorem t5_wps [SpikeGS .hasLC GF]
-    (emittedInt_encodes _ 3) (emittedInt_storable _ 3)
+    (emittedInt_encodes _ 3) (emittedInt_storable _ 3 (by decide) (by decide))
@@ -634 +636 @@ def loadBind (loc : CerbLocation.Loc) (ann : core_run_annotation) (x : sym)
-theorem loadBind_wps [SpikeGS .hasLC GF]
+theorem loadBind_wps [LemFuel] [SpikeGS .hasLC GF]
@@ -667,4 +668,0 @@ theorem loadBind_wps [SpikeGS .hasLC GF]
-#print axioms t5_wps
-#print axioms t5_blockSpecs
-#print axioms loadBind_wps
-
```

### `#print axioms`, measured once out of tree

From `cerberus-heaplang/`, a scratch file (ephemeral, under `.lake/`, deleted
at slice end) `import CerberusHeapLang.Examples.PartialClients` + the three
commands, run as `CERB_MEM_MAX=64G ../scripts/capped ~/.elan/bin/lake env lean
.lake/d5b-scratch/axioms.lean`. Output verbatim (exit 0):

```text
'CerberusHeapLang.PartialClients.t5_wps' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.PartialClients.t5_blockSpecs' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.PartialClients.loadBind_wps' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The module carries no `#print`/`#eval` (`grep -n '#print\|#eval'` empty).

### The manifest

Regenerated exactly as the gate does, from `cerberus-heaplang/`:
`CERB_MEM_MAX=64G ../scripts/capped ~/.elan/bin/lake env lean
scripts/capability_manifest.lean > docs/CAPABILITY_MANIFEST.md` (exit 0). The
rebase had left the file at main's content (the D5 commit `98335e2` carries
no manifest change). Summary line verbatim:

```text
MANIFEST: 35 constructors, 78 variant rows (47 RULE, 0 RULE-TOTAL-UNDEMONSTRATED, 0 RULE-PARTIAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 24 NO-RULE, 7 OUT-OF-SCOPE), 0 red, 26 consumer modules
```

`grep -c '| RULE-PARTIAL-UNDEMONSTRATED |'` = 0. The seven rows' constructor,
class and partial-consumer cells (DERIVED extraction, `awk -F'|'` on the
regenerated file):

```text
 `Frag.load`  ::  RULE  :: `wps_load_footprint` — Examples.PartialClients
 `Frag.sseq_sym`  ::  RULE  :: `wps_seq_sym_annot` — Examples.PartialClients
 `Frag.neg_store`  ::  RULE  :: `wps_neg_round` — Examples.PartialClients
 `Frag.neg_store_op`  ::  RULE  :: `wps_neg_round` — Examples.PartialClients
 `Frag.excluded_store_op`  ::  RULE  :: `wps_excluded_store_eval` — Examples.PartialClients
 `Frag.excluded_store`  ::  RULE  :: `wps_excluded_store` — Examples.PartialClients
 `Frag.case_op`  ::  RULE  :: `wps_case_eval` — Examples.PartialClients
```

`git diff --stat` vs main for the file: 31 insertions, 30 deletions (the
module row, the MODULES line 59→60 / 25→26, the seven class cells, and
`Examples.PartialClients` joining the consumer lists of the rules it uses).

### The snapshot census

Pre = `docs/2026-09-07_l2b-signatures-post.txt` (L2's final, committed at
`317dd29`; SHA-256
`045e9e6133034636b9b3ac595a9494e7aad35573757338ea7c57a8abd805e390`). Post =
`docs/2026-09-07_codex-D5b-post.txt`, taken after the full build at this tree
with `CERB_MEM_MAX=64G ../scripts/capped ~/.elan/bin/lake env lean
scripts/signature_snapshot.lean` (exit 0; 52,298 lines; SHA-256
`91f0419bd536e9c149e9eb9f31c29181478b85bc419542d481eb67d1a1bbf739`).
DERIVED census, entries split on the `----` separator and compared by
printed name and full text:

```text
pre 5212; post 5219; ADDED 7; REMOVED 0; CHANGED 0; UNCHANGED 5212
ADDED   def CerberusHeapLang.PartialClients.loadBind
ADDED   theorem CerberusHeapLang.PartialClients.loadBind_wps
ADDED   def CerberusHeapLang.PartialClients.t5Ls
ADDED   def CerberusHeapLang.PartialClients.t5RetQ
ADDED   theorem CerberusHeapLang.PartialClients.t5_blockSpecs
ADDED   theorem CerberusHeapLang.PartialClients.t5_wps
ADDED   def CerberusHeapLang.PartialClients.ψT5
```

The brief said "exactly the three public theorems ADDED": the four public
defs are the module's own (`loadBind`, `t5Ls`, `t5RetQ`, `ψT5`), the same
seven names D5's original census listed as ADDED (the D5 section above);
nothing outside the module changed text. The three theorems' entries carry
`[inst : LemFuel]`, and `t5_wps`'s `0 < LemFuel.fuel →`, as forced.

### The FULL gate, at commit `7bdf408` (tree clean)

Order: the adaptation (module + manifest + snapshot) was committed first so
the gate runs on an exact commit; this record is the docs-only second commit.
`CERB_MEM_MAX=64G scripts/test_unit.sh` from the worktree root,
05:55:52–05:56:08 UTC (the build was fully cached from the preceding capped
`lake build` of the same tree: 484 jobs). Tail verbatim, the lines matching
`^==|^ok:|^info: CerberusHeapLang|^ALL GATES|^GATE-EXIT|^Build completed|^BOUNDARY|^ALLOWLISTED|^FAIL`,
unmodified:

```text
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 1b: fuel-numeral grep (scripts/fuel_numeral_check.sh; a numeral outside a *_shipped corollary is red) ==
ok: no fuel numeral (100000000/1000000/999999) outside a *_shipped corollary and no retired fuel constant (61 files scanned, comments stripped)
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:1121:0: CerberusHeapLang export pins: 904 trio-exact, 6 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1121:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (6532 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1121:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (9763 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (484 jobs).
ok: cerberus-heaplang build green
== speedbump: rule-use and classification manifest (regenerate; red on a red row or drift) ==
ok: capability manifest regenerated, no drift
== speedbump: corpus skeleton (hand-transcribed emitted Core vs docs/corpus-e0; scripts/corpus_skeleton.lean) ==
ok: corpus skeleton — every transcription matches its emitted text, every plant mismatches
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — 19 core modules, none imports an exhibit/example/production module
== speedbump: client boundary (positive clients mention no logic internals; scripts/boundary_check.sh) ==
ok:   Exhibit — 0 internals mentions
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
ok:   TwoLabelExhibit — 0 internals mentions
ok:   EvenOddExhibit — 0 internals mentions
ok:   EmittedAExhibit — 0 internals mentions
ok:   EmittedBExhibit — 0 internals mentions
ok:   EmittedCExhibit — 0 internals mentions
ok:   CorpusT1Exhibit — 0 internals mentions
ok:   CorpusT5Exhibit — 0 internals mentions
ok:   CorpusT6Exhibit — 0 internals mentions
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

Pins: 901 (L2) + 3 (D5) = 904 trio-exact; 6 axiom-free-exact unchanged.
`warning: CerberusHeapLang/*` lines in the gate log: 33 (Heap 2, Potential
31 — the L2 baseline; the new module contributes none). `UNCAPPED` lines: 0.
`git diff --check` clean. Standalone `scripts/fuel_numeral_check.sh` before
the gate: `ok … (61 files scanned, comments stripped)`.

### Time and scratch

From entering the worktree (05:45 UTC) to this record: about 20 minutes
including the document reads. Longest single pass: the first capped
`lake build` at `df5dc90` (the failing module plus Lake's replay of the
primed dependencies' logs); the module alone elaborates in 3.2 s. No pass
approached the one-hour tripwire. Scratch (build logs, the edit script, the
`#print axioms` file) lived in `cerberus-heaplang/.lake/d5b-scratch/` and is
deleted with this commit; the first background build's log went to
`/tmp/d5b-build1.log`, unreadable from the sandbox shell, and the build was
re-run with the log under `.lake/` instead. D6 remains BLOCKED as recorded
above (not this worker's task); no other deliverable was started.

### Rebase after the gate (the orchestrator's instruction, [AGENT] executed)

After the FULL gate at `7bdf408` main moved `6b6d9a8` → `1e1f584` — three
DOCS-ONLY commits (`git diff --stat 6b6d9a8 1e1f584`: the stage-2 charter
`docs/2026-09-07_codex-charter-demo-residuals.md`, the read-only stage-1 copy
`cerberus-heaplang/docs/2026-09-07_codex-stage1-notes.md`, a `docs/DECISIONS.md`
entry; 3 files, +332/−35; no Lean, manifest, TSV or snapshot file). `git
rebase main`: six commits replayed, zero conflicts. Gated adaptation commit
`7bdf408` → rebased `dc1bf00`. Verification: `git diff --stat 7bdf408 dc1bf00
-- cerberus-heaplang` = the stage-1 copy only (+225 lines); `git diff 7bdf408
<rebased head> -- cerberus-heaplang/CerberusHeapLang cerberus-heaplang/CerberusHeapLang.lean
cerberus-heaplang/docs/CAPABILITY_MANIFEST.md cerberus-heaplang/scripts
cerberus-heaplang/docs/2026-09-07_codex-D5b-post.txt cerberus-heaplang/lakefile.toml
cerberus-heaplang/lake-manifest.json scripts` = 0 lines; the tree object of
`cerberus-heaplang/CerberusHeapLang` is `497f5139988d3df34c3ff95c5592359012c82e0e`
at both commits. Not re-gated, per the instruction (the gated content is
byte-identical). This record's commit is the amended second commit of the
slice; the working tree is clean.
