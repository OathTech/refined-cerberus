# Range audit — `codex/demo-residuals-2` (1e1f584..bf4554d), fresh skeptical auditor, 2026-09-07

**VERDICT: PASS** — no trust property is broken; no fix is REQUIRED before an
ff-only merge. Four Low findings and four Notes are listed; each has a
recommended (non-blocking) disposition for the orchestrator's landing
(record erratum, snapshot de-duplication, provenance tags, KOI C17 update).

**GRADE: A-** — every trust-bearing claim in the range re-measured true
(zero statement changes public or private, zero forbidden constructs, no
limit change, pins unchanged, cap enforced, D6 instrument fail-closed and
plant-red, four blocks correct under the charter as written); the record
carries one unreproducible count ("676"), no provenance tags, and the range
lands 12 snapshot files of which 11 are byte-duplicates.

Auditor: fresh, no prior context. Worktree
`/home/dev/projects/cerberus-lean-proj/refined-cerberus/worktrees/codex-stage2`,
HEAD `bf4554d`, base `main` = `1e1f584` (verified ancestor). Range = 8 commits.
Read in order: CLAUDE.md, docs/AUDIT-BRIEF.md, docs/KNOWN-OPEN-ITEMS.md, the
charter `docs/2026-09-07_codex-charter-demo-residuals.md`, the record
`cerberus-heaplang/docs/2026-09-07_codex-stage2-notes.md`, ARCHITECTURE.md §7.
No `lake build` was run; no tracked file was edited; scratch lived only under
the gitignored `cerberus-heaplang/.lake/audit-scratch/` (deleted at the end);
every Lean invocation went through `scripts/capped` at `CERB_MEM_MAX=40G`.
The agent's own gate/build logs, left in the gitignored `cerberus-heaplang/.lake/`
(`codex-*-gate.log`, `codex-D7-{soundness,round}.log`, `codex-D6-{check,plant}.log`,
`codex-D7-snapshot.diff`), were read as evidence and are cited where used.

Quoted outputs are verbatim unless labelled DERIVED.

## Findings table

| id | severity | where | claim (one line) | how verified |
|---|---|---|---|---|
| F1 | Low | record §D7 ("676 public theorem statements") | The count 676 is not reproducible; column-0 `theorem` (non-private) count over the seven edited modules is 713 at BOTH 1e1f584 and bf4554d. The substantive claim (no statement changed) holds for all 713. | grep count at both commits (DERIVED, method stated below) + header-block diff |
| F2 | Low | `cerberus-heaplang/docs/2026-09-07_codex-D{1,2,3,4,6,7}-{pre,post}.txt` | 12 snapshot files (2.98 MB each, 35.7 MB) land; 3 are byte-identical to the pre-existing `2026-09-07_l2b-signatures-post.txt`, the other 9 are byte-identical to each other. Only `D7-post` carries new content. | `sha256sum` |
| F3 | Low | charter §2 D3 FENCE; record §D3 | A second D3 fence defect the record does not name: `Shipped.lean:306/323/340` restate `600 ≤ sup →` and pass `hsup` to `t{4,5,6}_certified_production`; changing the production premise forces a Shipped.lean edit (outside the fence). The 14-premise census is correct as scoped ("in the three exhibits"). | `grep -n '600 ≤'` over the package; Shipped.lean read |
| F4 | Low | record (whole file) | Zero `[AGENT]`/`[USER]` tags. The four BLOCKED decisions, the "charter's 42-site count is stale" correction and the D6 scope statement ("unprinted metadata … cannot be established") are agent-called and unlabelled (CLAUDE.md: decisions carry provenance). | `grep -n '\[AGENT\|\[USER'` → none |
| N1 | Note | record §D6; `scripts/corpus_skeleton.lean` `FullText.annotations` | Disclosure incomplete, instrument correct: the renderer silently accepts (does not print) `Aexpr`/`Astmt`/`Alabel`/`Acerb`/`Ainlined_label`/`Auid`/`Aattrs`/`Avalue` and drops `Erun`'s annotation; this set EQUALS pp_core.ml's unprinted set at debug ≤ 3 (pp_core.ml:557–602, 659), so a text comparison cannot see them. `Aexpr` (35) and `Astmt` (54) occur in the transcriptions. The record lists only digests / action locations / save passing modes. Also `Examples/CorpusE0.lean`'s header (out of D6's fence) still describes the retired opaque-leaf skeleton. | pp_core.ml read; `grep -oE` over CorpusE0.lean |
| N2 | Note | KOI C17; `Soundness.lean:3306` | Post-D7 hygiene residue for KOI C17: `cons_of_head?` is now consumerless (only mention: an Audit.lean:170 comment); the positive-store `step_ctx_store_eval_ws'/_shape/_fail2/_fail3` bodies still duplicate the excluded-store ones (the shared macro is `excludedStoreOpRedex`-specific); `t*Kill_eq`, `t*Load` (Examples/CorpusE0.lean), `t6frAssign` remain (frozen surface / fence). C17's "42-site" text should read 51 → 0. | grep; diff read |
| N3 | Note | charter §2 D2/D3/D4 line cites | The charter's cites were already stale at 1e1f584 by 6–7 lines (e.g. `CorpusT5Exhibit.lean:550` → actual `:543`; `:432` → `:426`; T6 `:756/:429/:479` → `:749/:423/:473`; T4 `:785` → `:778`). The record's own cites are exact. | `sed -n` at HEAD |
| N4 | Note | record gate tails | `GATE-EXIT=0` is the agent's shell echo (test_unit.sh prints only `ALL GATES GREEN`; `grep -c GATE-EXIT scripts/test_unit.sh` = 0). The quoted tails ARE verbatim from the agent's logs (md5 of the last 12 lines identical across all 7 gate logs), but the line's provenance should be stated. Also: the brief said "ten snapshot files"; there are twelve. | log tails; script grep |

No Critical or High finding. No KOI entry is contradicted; nothing here
re-cites a KOI item as new (B15/B16/B19/B20 are the D1–D4 targets, still
open; C17 is the D7 target, partially closed — N2 lists the residue).

## Per-finding detail

### F1 — "676 public theorem statements" (Low, record accuracy)

Record §D7: "An independent source-text comparison also found all 676 public
theorem statements in the seven edited modules unchanged".

Measurement (DERIVED; method: lines matching
`^(@\[[^]]*\] )?(protected )?theorem ` per module, i.e. column-0, non-private):

```
=== public theorem counts (column-0 theorem, not private) @HEAD ===
Soundness: public=322 private=1
DriverCollapse: public=69 private=0
Round: public=197 private=0
CorpusT4Exhibit: public=56 private=0
CorpusT5Exhibit: public=24 private=0
CorpusT6Exhibit: public=34 private=0
OverflowExhibit: public=11 private=0
TOTAL public (DERIVED): 713
=== same @main ===
TOTAL public @main (DERIVED): 713
=== indented theorems (inside namespace/section) @HEAD ===
Soundness: 0
DriverCollapse: 0
Round: 0
```

A second, independent method (header-block extraction, every
`theorem|lemma|def|abbrev|instance|structure|inductive|macro|…` at column 0,
text up to the first `:=`, keyed by kind+name, compared by full text) finds
CHANGED 0 in every module — the record's substantive claim is TRUE for all
713; only the number is wrong or uses an undisclosed method. Disposition:
KOI §D erratum ("676" → "713 by column-0 count; 0 changed"), orchestrator.

### F2 — snapshot duplication (Low, hygiene)

```
0cb8fd9f6d05c813b2b296fa31c751566c96f9e74e8a1ce93ba3478417608df8  2026-09-07_codex-D1-pre.txt
0cb8fd9f6d05c813b2b296fa31c751566c96f9e74e8a1ce93ba3478417608df8  2026-09-07_codex-D2-pre.txt
0cb8fd9f6d05c813b2b296fa31c751566c96f9e74e8a1ce93ba3478417608df8  2026-09-07_codex-D3-pre.txt
0cb8fd9f6d05c813b2b296fa31c751566c96f9e74e8a1ce93ba3478417608df8  2026-09-07_codex-D4-pre.txt
045e9e6133034636b9b3ac595a9494e7aad35573757338ea7c57a8abd805e390  2026-09-07_codex-D6-pre.txt
045e9e6133034636b9b3ac595a9494e7aad35573757338ea7c57a8abd805e390  2026-09-07_codex-D7-pre.txt
0cb8fd9f6d05c813b2b296fa31c751566c96f9e74e8a1ce93ba3478417608df8  2026-09-07_codex-D1-post.txt
0cb8fd9f6d05c813b2b296fa31c751566c96f9e74e8a1ce93ba3478417608df8  2026-09-07_codex-D2-post.txt
0cb8fd9f6d05c813b2b296fa31c751566c96f9e74e8a1ce93ba3478417608df8  2026-09-07_codex-D3-post.txt
0cb8fd9f6d05c813b2b296fa31c751566c96f9e74e8a1ce93ba3478417608df8  2026-09-07_codex-D4-post.txt
045e9e6133034636b9b3ac595a9494e7aad35573757338ea7c57a8abd805e390  2026-09-07_codex-D6-post.txt
0cb8fd9f6d05c813b2b296fa31c751566c96f9e74e8a1ce93ba3478417608df8  2026-09-07_codex-D7-post.txt
045e9e6133034636b9b3ac595a9494e7aad35573757338ea7c57a8abd805e390  2026-09-07_l2b-signatures-post.txt
```

Sizes: 2 976 046 bytes (the `045e…` class) / 2 976 370 bytes (the `0cb8…`
class). The SHA-256 values match the record's claims exactly (D6 pre = post =
`045e…`; D7 pre `045e…` → post `0cb8…`; D1–D4 pre = post = `0cb8…`).
Byte-identical classes: {l2b-post, D6-pre, D6-post, D7-pre} and {D7-post,
D1-pre, D1-post, D2-pre, D2-post, D3-pre, D3-post, D4-pre, D4-post}.
Recommendation: keep `2026-09-07_codex-D7-post.txt` (the only new content);
drop the other eleven and let the record's recorded hashes stand as the
evidence (D7-pre = l2b-post by hash; the D1–D4 "restoration" pairs = D7-post
by hash). A docs-only commit on top; the charter mandated writing the files,
so landing them is not a fence violation — this is bang-for-buck hygiene.

### F3 — D3's second fence defect: Shipped.lean (Low, charter/record completeness)

```
Shipped.lean:306:          600 ≤ sup →
Shipped.lean:323:          600 ≤ sup →
Shipped.lean:340:          600 ≤ sup →
```
and each `*_shipped` proof ends `exact t{4,5,6}_certified_production (by show _ ≤ 100000000; omega) sup hsup fs args`.
If D3 rewrote `(hsup : 600 ≤ sup)` to `(hsup : symBound … ≤ sup)` in the three
production theorems, these three proofs would no longer typecheck (an `hsup :
600 ≤ sup` is not a `symBound … ≤ sup`), forcing an edit of `Shipped.lean`,
which D3's fence (`ProdEntry.lean` or one module for `symBound`,
`CorpusT4/T5/T6Exhibit.lean`, `Audit.lean` pins, the record) does not list.
The record's block reason (gate 1b outside the fence) is sufficient and
correct; this is an additional defect the orchestrator should fold into D3's
re-charter. The record's census of 14 `hsup : 600 ≤ …` premises is exact
(see F/verified-clean below); the Shipped.lean `600`s are the gate's allowed
`*_shipped` class and outside the charter's "in the three exhibits" scope.

### F4 — provenance tags (Low)

```
=== provenance tags in the record ===
(none)
```
Agent-called decisions in the record without a tag: BLOCKED D1, D2, D3, D4;
"the charter's 42-site count is stale" (measured true: 37/12/2 = 51 at
1e1f584, see D below); the D6 scope statement on unprinted metadata. No
[USER] decision was misattributed; no statement shape for a public export was
chosen by the agent (I, verified clean). Disposition: the orchestrator's
DECISIONS/KOI entries carry `[AGENT 2026-09-07]` for the four blocks.

### N1 — D6 disclosure vs the renderer's silent-accept set (Note)

`FullText.annotations` (scripts/corpus_skeleton.lean) accepts without printing:
`Aexpr | Astmt | Auid _ | Alabel _ | Acerb _ | Ainlined_label _ | Aattrs _ | Avalue _`
and THROWS on any other kind. pp_core.ml at the pin
(`.cerberus-ws/ocaml_frontend/pprinters/pp_core.ml:557–602`): `Aloc` → range
only + `maybe_print_location`; `Astd` → `{-# … #-}` comment; `Auid` → range
only; `Amarker`/`Amarker_object_types`/`Abmc`/`Atypedef` → PRINTED comments
(the renderer throws on these — fail-closed, correct); `Aattrs`/`Avalue` →
printed only at debug level > 3; `Alabel`/`Acerb`/`Ainlined_label`/`Astmt`/
`Aexpr` → `acc` (unprinted). `Erun (_, sym, pes)` (pp_core.ml:659) drops its
annotation; `Store0 (is_locking, …)` (:701–702) IS distinguished
(`store_lock`/`store`) and the renderer's `actionKeyword` mirrors it. So the
instrument's blind spots are exactly the printer's, and every printed form the
renderer does not know raises an error. In the transcriptions:
```
     35 Aexpr
     89 Aloc
     29 Astd
     54 Astmt
```
The record discloses three unprinted classes and omits the annotation kinds
and `Erun`'s annotation. Not a fail-open: nothing is defaulted to "equal"; the
comparison is `textToks == termToks` over the full lexical stream and the text
has no representation of these fields. Recommend one sentence in the record.
`Examples/CorpusE0.lean:17–49` (the module header) still documents the
opaque-`leaf` skeleton; outside D6's fence — a docs-pass item.

### N2 — KOI C17 residue after D7 (Note)

```
=== cons_of_head? consumers across the package ===
CerberusHeapLang/Audit.lean:170:`one_step_unseq_aux_collect`, `cons_of_head?`, `Decomp.ccallFree_plug`,
CerberusHeapLang/Soundness.lean:3306:theorem cons_of_head? {α : Type} {l : List α} {s : α} (h : l.head? = some s) :
```
Public, frozen, unpinned, now consumerless. The excluded-store family shares
`excluded_store_eval` (DriverCollapse.lean:1504; used at DriverCollapse:1542,
Round:4106/4129/4161) but the positive-store twins do not (their bodies are
`step_ctx_head hget; unfold storeOpRedex; cases ctx <;> (dsimp only; rw [step_action_store_eval …]; …)`
— textually the same finish as the excluded ones). `t*Kill_eq` (public `rfl`
wrappers, frozen), `t{4,5,6}Load` (Examples/CorpusE0.lean, out of fence) and
`t6frAssign` remain; the record states this and it is consistent with the
charter's ACCEPTANCE ("REMOVED = the clones' PRIVATE helpers only; CHANGED 0")
— the charter's GOAL text over-promised relative to its own acceptance.

### N3 — charter cites stale (Note)

At 1e1f584/HEAD: `EmittedCExhibit.lean:732` ✓ (`exhibitC_prod_e3`),
`Wps.lean:5280` ✓, `Wpt.lean:4860` ✓; but `CorpusT5Exhibit.lean:550` is inside
`t5_certified_production`'s conclusion (the `hsup` premise is at :543);
`:432` → :426; `CorpusT6Exhibit.lean:756/:429/:479` → :749/:423/:473;
`CorpusT4Exhibit.lean:785` → :778. Uniform 6–7-line drift from the activation
commit; harmless; the record's table is exact.

### N4 — `GATE-EXIT=0` provenance; "ten" vs twelve (Note)

test_unit.sh's last line is `ALL GATES GREEN` (or `FAST-GATE GREEN …`);
`GATE-EXIT=0` in every quoted tail is the agent's `echo "GATE-EXIT=$?"` into
its log. The tails are otherwise verbatim (last 12 lines of all seven agent
gate logs have one md5). The audit brief's "ten snapshot files" is twelve.

## Verified clean — A through I, with the measurement

### A. Fence compliance — CLEAN
```
git diff --stat 1e1f584 bf4554d   (21 files)
 CorpusT4Exhibit.lean 41 | CorpusT5Exhibit.lean 37 | CorpusT6Exhibit.lean 51 |
 DriverCollapse.lean 595 | OverflowExhibit.lean 4 | Round.lean 1340 | Soundness.lean 90 |
 12 × docs/2026-09-07_codex-D*-{pre,post}.txt | docs/2026-09-07_codex-stage2-notes.md 563 |
 scripts/corpus_skeleton.lean 260
```
D6's fence (script + record) and D7's fence (Round, DriverCollapse,
Soundness, exhibit PROOF BODIES, record) plus the charter-mandated snapshots
cover every file. `OverflowExhibit.lean`'s 4-line change is the proof body of
`symK_eval` only (statement unchanged; now `exact symC_eval (M := { spikeCtx with … }) …`).
Untouched (measured `git diff --quiet`): `docs/DECISIONS.md`,
`docs/KNOWN-OPEN-ITEMS.md`, `scripts/semantics-pin.env`,
`cerberus-heaplang/lake-manifest.json`, `lakefile.toml`, `Audit.lean`,
`cerberus-heaplang/docs/2026-09-07_codex-stage1-notes.md`; `.cerberus-ws/`
appears in 0 diff paths; `Examples/PartialClients.lean` is absent on this
branch (D5 lands separately). Import lists of all seven modules identical.
D1–D4: each park branch is exactly one commit off the working branch (bases
9defae7 / 51efef2 / 539c83f / c5d60d9) adding one `D<n>-pre.txt` + record
text; `git diff --name-only <park>~1 <park> | grep -E '\.(lean|sh|toml|json|env)$'`
→ `(none)` for all four. The D1–D4 commits on the working branch touch only
snapshots + the record. `git diff --check 1e1f584 bf4554d` → exit 0.

### B. Forbidden constructs — CLEAN
Added lines of the whole range grep'd for
`axiom|sorry|native_decide|bv_decide|ofReduce|maxHeartbeats|maxRecDepth|#print|#eval|100000000|1000000|999999|admit|unsafe|implemented_by|extern`:
zero hits (the only hits of the wider pattern were four `decide +kernel`
lines inside the shared macros). `decide +kernel` is kernel-checked (no
`ofReduceBool`), is not in the banned class, and is NOT new: at 1e1f584 the
exhibits already used it (T4 17, T5 6, T6 3, Overflow 4); at HEAD T4 14, T5 3,
T6 0, Overflow 4, Soundness 3 (the macros) — the same tactic moved into the
shared definitions. `set_option` census in the seven modules at both commits:
only `set_option autoImplicit false` (Soundness:50, DriverCollapse:98,
Round:178, T4:16, T5:22, T6:20, Overflow:57). There is NO `set_option
maxHeartbeats` in Soundness.lean at main or HEAD; the record's "hit the
existing heartbeat limit" refers to the default. Macro bodies expanded and
read: `step_ctx_head` = `unfold step_ctx; dsimp only; rw [map_cons_of_eq _ h]; generalize List.map _ _ = post`;
`emitted_frame` = `repeat first | assumption | apply SymFrame.add`;
`emitted_lookup` = the old `t*_lookup` verbatim with `emitted_frame`;
`labeled_main` = `unfold LabeledAt; (prepare); rw [fmapLookupBy_addBy_empty, if_pos (by decide +kernel)]`;
`excluded_store_eval` = `step_ctx_head; unfold excludedStoreOpRedex; cases ctx <;> (dsimp only; rw [step_action_store_eval (.inr (act_none_of_pair …)) (PePure.not_constrained …)]; finish)`;
`neg_context` (local, Round:2561) = the nine arms' shared prefix verbatim.
No `#eval`/`#print` left in a library module.

### C. Frozen surface — CLEAN
Recomputed census (entries split on `----`, keyed `<kind> <name> :`, compared by full text):
```
pre entries 5212 keys 5212 dupkeys 0
post entries 5217 keys 5217 dupkeys 0
ADDED 5
  + ('def', 'CerberusHeapLang.tacticEmitted_frame')
  + ('def', 'CerberusHeapLang.tacticEmitted_lookup')
  + ('def', 'CerberusHeapLang.tacticLabeled_main_')
  + ('def', 'CerberusHeapLang.tacticStep_ctx_head_')
  + ('def', 'CerberusHeapLang.«tacticExcluded_store_eval_,_,_,_,_=>_»')
REMOVED 0
CHANGED 0
```
Header-block diff of the seven modules (1e1f584 vs bf4554d), including
PRIVATE declarations: Soundness ADDED `private theorem map_cons_of_eq` + 4
macros; DriverCollapse ADDED macro `excluded_store_eval` + `theorem
step_ctx_excluded_store_eval_ws'`; Round ADDED `local macro neg_context`,
REMOVED `step_ctx_excluded_store_eval_ws'`; T4/T5/T6 REMOVED the local
`t{4,5,6}_frame`/`t{4,5,6}_lookup` macros; OverflowExhibit no header change;
**CHANGED 0 in every module** — no statement of any theorem/def, public or
private, changed. D6 snapshot diff EMPTY (D6-pre = D6-post = l2b-post by SHA).

### D. D7 correctness/quality — CLEAN (residue in N2)
Idiom counts at 1e1f584 → bf4554d:
```
== Soundness       cons_of_head? 3 -> 1 | have key 2 -> 0 | .head? = 3 -> 1 | step_ctx_head 0 -> 3 | List.head?_cons 2 -> 0
== DriverCollapse  cons_of_head? 12 -> 0 | have key 12 -> 0 | .head? = 12 -> 0 | step_ctx_head 0 -> 12 | List.head?_cons 12 -> 0
== Round           cons_of_head? 37 -> 0 | have key 37 -> 0 | .head? = 37 -> 0 | step_ctx_head 0 -> 33 | List.head?_cons 37 -> 0
```
Sites at main: 2 + 12 + 37 = 51 (the record is right, KOI C17's 42 is stale).
Accounting at HEAD (DERIVED): Soundness 1 macro def + 2 uses; DriverCollapse
1 use inside `excluded_store_eval` + 11 direct (the 12th old site,
`step_ctx_excluded_store_eval_ws`, now `exact step_ctx_excluded_store_eval_ws' …`);
Round 33 direct + 3 via `excluded_store_eval` (shape/fail2/fail3) + 1 moved
out (`ws'`) = 37. The retained `cons_of_head?` (Soundness:3306) is the public
theorem itself. `map_cons_of_eq` read: `xs = x :: rest → xs.map F = F x :: rest.map F`
by `rw [h, List.map_cons]` — general and trivially sound; the `generalize`
abstracts the mapped suffix so `simp`/`dsimp` never touch it (the recorded
heartbeat episode's fix; no limit changed). `step_ctx_excluded_store_eval_ws'`
statement text (up to `:= by`) at main-Round vs HEAD-DriverCollapse: `diff` →
IDENTICAL; consumers: Round:7047, DriverCollapse:1575, Audit pin :901 unchanged.
`Decomp.lift_neg'`: nine arms → `neg_context` (Round:2597–2629), root/bound
arms structural; `labeled_main` used in all three `t*Main_labeledAt`;
`symK_eval` delegates to `symC_eval` (EmittedCExhibit:221; OverflowExhibit
already imported it). `depLe` at main: 0 occurrences (record correct).
Build times from the agent's logs: `codex-D7-soundness.log:1851: ✔ [108/108] Built CerberusHeapLang.Soundness (42s)`,
`codex-D7-round.log:2857: ✔ [431/431] Built CerberusHeapLang.Round (22s)`
(both as recorded); the "later rebuild 24 s" has no retained log (olean mtime
06:11:40 vs the log's 06:08:36 is consistent with a later rebuild after the
macro additions) — not contradicted, not verifiable. D7 gate log module times:
OverflowExhibit 1.0 s, T6 4.4 s, T5 3.7 s, T4 9.1 s, Audit 1.8 s. No
pre-range per-module baseline exists in the tree; nothing is near the tripwire.

### E. D6 correctness — CLEAN (disclosure gap in N1)
`scripts/corpus_skeleton.lean` read in full. Every catch-all arm of `symbol`,
`location`, `integerBase/Ty`, `cty`, `objectTy`, `val`, `pexpr`, `action`,
`expr`, `annotations` (unknown kind) THROWS; `pat` throws on a shown
annotation; `ctorName` (CorpusE0.lean:191) is `Except` and throws on an
unknown constructor; `tokens` emits every non-whitespace character (no
position skipped); the row verdict is `textToks == termToks` (list equality,
both directions). Read-only run, `CERB_MEM_MAX=40G ../scripts/capped ~/.elan/bin/lake env lean scripts/corpus_skeleton.lean`, exit 0, 1.99 s wall:
```
dead-literal plant: t1.annot.core/main: save Specified(0) -> Specified(7): mismatch (expected)
| t1.annot.core | main | 312 | equal | mismatch (expected) | mismatch (expected) | mismatch (expected) | mismatch (expected) | case scrutinee: n/a; if condition: n/a; case pattern: n/a |
dead-literal plant: t5_ifelse.annot.core/main: save Specified(0) -> Specified(7): mismatch (expected)
| t5_ifelse.annot.core | main | 652 | equal | … |
dead-literal plant: t6_switch.annot.core/main: save Specified(0) -> Specified(7): mismatch (expected)
| t6_switch.annot.core | main | 726 | equal | … |
dead-literal plant: t4_while.annot.core/main: save Specified(0) -> Specified(7): mismatch (expected)
| t4_while.annot.core | main | 1504 | equal | … |
| is_representable_integer | 16 | equal | Ivmin/Ivmax swapped: mismatch (expected) |
| conv_int | 47 | equal | first if's branches swapped: mismatch (expected) |
| conv_loaded_int | 35 | equal | first case's alternatives reversed: mismatch (expected) |
corpus-skeleton: ok — 4 corpus row(s) and 3 std.core row(s) equal, every plant mismatches
```
(`…` elides the four E1–E4 plant columns, all `mismatch (expected)`.) The
dead-literal plant is exercised on EVERY row (4/4) as claimed. Negative run
reproduced independently from a scratch copy of the script whose `#eval`
feeds `checkCorpus` the t1 row with `(plantSaveLiteral r.term).1`:
```
FAIL: t1.annot.core/main: full text mismatch
  first difference at token 304: term `7`, text `0`
FAIL: t1.annot.core: no save initialiser Specified(0) for the dead-literal plant
| t1.annot.core | main | 312 | DIFFER | …
.lake/audit-scratch/plant_t1.lean:485:0: error: corpus-skeleton: FAIL
PLANT-EXIT=1
```
identical in content to the record's quote and to the agent's
`codex-D6-plant.log`. Token counts vs the retired skeleton (baseline gate log):
121/271/299/591 → 312/652/726/1504 — the comparison is now whole-text.

### F. Block reasons D1–D4 — all four blocks CORRECT under the charter as written; the charter, not the agent, is the defect in each
- D1: `Wpt.lean:152–207` (`def wpt.pre` … `termination_by k => k`) read: the
  terminal clause is the `toVal` postcondition, the nonterminal clause demands
  `PrimStep.Reducible` and a step; `grep -c` in Wpt.lean: `evalClass` 0,
  `EvalFail` 0, `Killed` 0 (the 29 `kill` hits are the Core `kill` action
  rules `wpt_kill*`). `wpt_driver_done_alloc` (ProdLoop.lean:444) concludes
  `DriverDoneAt` (ProdLoop.lean:63), an `NDactive` outcome. The fixed statement
  ("the SAME premise list except `hwp` delivers a KILL classification") is not
  derivable from this judgment. Charter defect (statement fixed against a
  judgment with no kill face).
- D2: `IntRules.lean:586–598` verbatim: `(hs : -2147483648 ≤ n1 + n2) (hs' : n1 + n2 ≤ 2147483647) :`
  (line 596); `wpt_c_add` (:601) has the same two. "Spelled EXACTLY as
  `wps_c_add`'s … — no numeral" is self-contradictory. Charter defect.
- D3: `scripts/fuel_numeral_check.sh:37`
  `NUMERALS='100000000|100_000_000|10\s*\^\s*8|1000000|1_000_000|10\s*\^\s*6|999999|999_999'`
  does not match `600`; `scripts/test_unit.sh:41–42` delegates gate 1b to it;
  neither script is in D3's fence, yet the ACCEPTANCE requires extending the
  gate and planting it. Charter defect (plus F3). The 14-premise census
  re-measured line for line: T5 426/543; T6 423/473/749; T4
  778/827/926/1154/1199/1254/1292/1315/1426 — matches the record's table exactly.
- D4: `Audit.lean:270` `def trioExports : List Name := [`, `wps_neg_bound`/`wpt_neg_bound`
  pinned at :939/:942, exact-pin loop :1116–1131 (`for n in trioExports do pin allowedAxioms n`);
  `def SymFrame` at `EnvLaws.lean:309`; charter §1 rule 4 mandates pinning
  every new public theorem; D4's fence omits `Audit.lean` and `EnvLaws.lean`.
  The premise text `⌜∃ k, s = fresh_given_int k ∧ M.runState.sym_supply ≤ k⌝`
  is at Wps.lean:5295 / Wpt.lean:4876 as the record says, and the client
  wrappers at EmittedInt:211/227, T4:726, T5:193/381, T6:241 expose it (record
  correct). Charter defect.

### G. Record accuracy — CLEAN except F1/N4
From the agent's seven gate logs (baseline, D6, D7, D1–D4), each:
`warnings(^warning: CerberusHeapLang[/.]): 33`; `info: … Audit.lean:1116:0: CerberusHeapLang export pins: 901 trio-exact, 6 axiom-free-exact`;
`Build completed successfully (483 jobs).`; `corpus-skeleton: ok — 4 corpus row(s) and 3 std.core row(s) equal, every plant mismatches`;
`BOUNDARY: 29 modules checked, 0 internals mention(s) in total, exit=0`; `ALL GATES GREEN`.
Snapshot census 5212/5217/+5/0/0 and both SHA-256 values: re-measured, exact.
51 = 2/12/37: re-measured, exact. `codex-D7-snapshot.diff` in `.lake` equals
the record's quoted diff. Timeline vs artefacts (all UTC 2026-09-07):
baseline gate 05:55:17 (BEFORE the first pre-snapshot 05:56:02 — charter rule
2 honoured) → D6 check 06:00:17 / plant 06:00:44 / gate 06:01:29 / commits
06:02:36, 06:03:18; D7 pre-snapshot 06:04:11 → Soundness log 06:08:36 →
Soundness.olean 06:11:40, DriverCollapse.olean 06:12:46, Round.olean 06:14:20
(Round log 06:14:21) → gate 06:15:50 → post-snapshot 06:16:52 → commits
06:17:43 (author) — 9defae7's committer date is 06:17:58, i.e. an amend 15 s
later, harmless; D1 gate 06:20:47 → 06:21:58; D2 06:24:33 → 06:25:32; D3
gate-1b 06:28:48, gate 06:29:54 → 06:31:04; D4 06:33:06 → 06:34:18. Every
recorded time is consistent with the artefacts. D6 script warnings: 0
(`codex-D6-check.log`), as recorded.

### H. Hygiene and the capped environment — CLEAN (F2 is the snapshot item)
`scripts/capped` read: the env self-load block (`if [[ -z CERB_PROJ || -z GIT_CONFIG_GLOBAL ]] … source env.sh`)
is skipped when both are set; the cgroup path (`cgroup_direct_try`) is
independent of it. Measured under the record's exact environment:
```
=== capped cgroup measurement under the record's env ===
cgroup=/user.slice/user-1000.slice/user@1000.service/app.slice/capped-3500201-1788808135913912465
memory.max=42949672960
memory.swap.max=0
GIT_CONFIG_GLOBAL=/dev/null
CERB_PROJ=/home/dev/projects/cerberus-lean-proj/refined-cerberus/worktrees/codex-stage2
exit=0
```
42949672960 = 40 GiB. The cap was enforced; `GIT_CONFIG_GLOBAL=/dev/null`
only removes the offline git redirects (a fetch would fail loudly, not run
uncapped); `TMPDIR=…/.lake` only relocates `mktemp` files. No `UNCAPPED`/
`KILLED` banner in any of the seven gate logs. Leftovers in the gitignored
`.lake/` (`codex-*.log`, `codex-D7-snapshot.diff`) are ephemeral and useful;
`git status --short` is empty apart from this report.

### I. Provenance — CLEAN except F4
No public statement was added, removed or changed (C); therefore no
statement shape was chosen by the agent. No [USER] decision is claimed. The
tags are simply absent (F4).

## What could not be run, and why
- A rebuild to re-derive the 33-warning count and the `483 jobs` line was not
  run (forbidden by the brief); both were taken from the agent's seven gate
  logs in `.lake/`, which the orchestrator's independent FULL gate at bf4554d
  (claimed green in the brief) is the second source for.
- The "later rebuild 24 seconds" for Soundness has no retained log.

## Cleanup
`cerberus-heaplang/.lake/audit-scratch/` deleted at the end of the audit; the
agent's `.lake/codex-*` logs were left in place (gitignored, evidentiary).
