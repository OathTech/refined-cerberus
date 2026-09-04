# ARCHITECTURE.md — fresh full review (review 4, of the rewrite)

**VERDICT: B+ — FAIL** (near pass; every finding below is a local edit).
Reviewer: fresh (reviewer 4; no prior contact with this document, its
predecessor, or reviewer 3's report until after the cold read and the
source verification were complete). Standard: grumpy PL professor, "would
I sign this as the paper's system section" — A passes, B or below fails.
Tree: `worktrees/review-arch-4`, detached at `cd68c46`. Method: source
reading only (no `lake`/`lean` invocation); every claim checked was
checked against the `.lean` text at `cd68c46`, the scripts, the generated
manifest, the pinned semantics workspace of the primary checkout
(`git -C .cerberus-ws rev-parse` = `f95ef8d9c`, read-only), LemLib at the
primary checkout's `.lake`, `docs/DECISIONS.md`, `docs/KNOWN-OPEN-ITEMS.md`
(KOI), `docs/CLAIMS.md`, `docs/CAPABILITY_MANIFEST.md` and the archive
record. Reading order: ARCHITECTURE.md cold, as the intended reader; then
the context files and the sources; then (last) reviewer 3's report and
the author's disposition table.

Summary of the verdict. The document now IS a description of the system:
the object, what is proved, what is trusted, how to read an export, the
instruments, the exclusions, the ledger — in that order, findable, with
the disclosures a reader needs (the static fuel premise, the
annotation-free fragment, the fixed `⊤` mask, the empty tag-definition
and extern premises, the ruled Reynolds/O'Hearn reading, the fragment
boundary and the fifteen no-rule variants, the negative total-correctness
result, the trust base and what is not trusted). The counts are right
(23 constructors, 21/26 mask sites, 402 pins, 50/30/0/0/15/5 rows, 18
consumers, 19 boundary modules, 11 claim rows / 90 names, ten `MemWF`
fields), the nine-statement premise table is exact, the two worked
readings match the source verbatim, the shop-window is clean (all 23
date stamps sit inside provenance tags or record paths; no
"former/until/since/deleted"; no `driveU`), and the archive is
byte-identical to `b8413a5` from its line 52 on. It fails the A bar on
four sentences a system section cannot contain: a `[USER]` quotation
labelled *verbatim* that contains eleven words absent from the register
it cites (P-1); an "only … are mask-generic" claim falsified by three
raw-WP lemmas in the same file (T-1); a "who consumes them" list that
omits three of nine consumers (T-2); and an "exactly" paragraph on the
root-of-trust statements that contradicts itself within six lines (T-3).
Each is a one-line fix; none is a gap in what is proved.

## Findings, ranked by severity

### HIGH

**P-1. A `[USER]` quotation labelled "verbatim" is not the register's
text.** Lines 542–545: "[USER], verbatim: 'the outer loop is the
'scheduler' loop and the inner loop is the 'single threaded' loop. And
for our logic, which (for now) is sequential, the scheduler is
degenerate, we never see schedule changes.'" The cited register entry
(`docs/DECISIONS.md:1787`ff, "FUEL IS A DEFECT…") records: "the outer
loop is the 'scheduler' loop and the inner loop is the 'single threaded'
loop … the scheduler is degenerate, we never see schedule changes" — an
ELISION where the document has "And for our logic, which (for now) is
sequential,". `grep -rn "for now) is sequential"` over `docs/`,
`cerberus-heaplang/docs/`, README, WALKTHROUGH, API.lean and the archive
finds the phrase in ARCHITECTURE.md only. Whether the words were said or
not, the record does not contain them; a front document may quote only
what the register records, and "verbatim" must mean the register's text
including its elision (CLAUDE.md, record integrity: quoted outputs are
verbatim). The meaning is harmless; the label is false, and it is
attached to the one ruling on which the reading of every closed partial
form rests.
Fix: replace the quotation with the register's, elision included —
"[USER], verbatim from the register: 'the outer loop is the 'scheduler'
loop and the inner loop is the 'single threaded' loop … the scheduler is
degenerate, we never see schedule changes'" — and, if the fuller
sentence exists in the conversation, have the orchestrator append it to
DECISIONS first.

### MEDIUM

**T-1. "only `AtomicStep`/`wp_of_atomic` … are mask-generic" is false.**
Lines 121–123: "Both judgments are stated at the top invariant mask `⊤`
(21 sites in `Wps.lean`, 26 in `Wpt.lean`; only `AtomicStep`/
`wp_of_atomic`, `Rules.lean:194`/`:210`, are mask-generic)." The counts
are right (`grep -o '⊤' | wc -l` = 21 / 26). But `Rules.lean:1584`
`theorem wp_store … {E : CoPset}`, `:1614` `theorem wp_load … {E :
CoPset}` and `:1676` `theorem spike_wp_wand … {E : CoPset}` are
mask-generic too. The true statement is the one the reader needs: the
RAW-WP layer of `Rules.lean` is mask-generic; the two STATEMENT judgments
are not.
Fix: "(…; the raw-WP layer of `Rules.lean` — `AtomicStep`,
`wp_of_atomic`, `wp_store`, `wp_load`, `spike_wp_wand` — is mask-generic;
the two statement judgments are not)".

**T-2. The collapse consumers list omits three of the nine
`wps_sound_empty` consumers.** Lines 183–188: "Who consumes them:
`wps_sound` is the Iris-level readout of `Examples/CallSmoke.lean:330`,
`FibRecExhibit.lean:648` and `EvenOddExhibit.lean:501`; `wps_sound_empty`
of Exhibit, StructExhibit, CaseExhibit, LoopExhibit, FibExhibit and
ArrayExhibit; `wpt_sound` of the pinned export `cs_twp_readout`". The
`wps_sound` and `wpt_sound` lists are exact (grep, non-comment lines).
`wps_sound_empty` is also consumed at `WseqExhibit.lean:107`,
`ListRevExhibit.lean:1434` and `TwoLabelExhibit.lean:531` (code lines,
verified). A list answering "who consumes them" that is two-thirds
complete is a false sentence, and it is the sentence that replaced
reviewer 3's T-2.
Fix: "… `wps_sound_empty` of Exhibit, StructExhibit, CaseExhibit,
LoopExhibit, FibExhibit, ArrayExhibit, WseqExhibit, ListRevExhibit and
TwoLabelExhibit; …".

**T-3. "Package definitions in these statements, exactly" is not exact,
and contradicts itself.** Lines 358–363: "The conclusions use the pure
readout predicates `CellCoh` (exhibit A, the counter loop),
`Sat`/`SeedChain` (list reversal; …) and the exhibits' value/byte
constants (`fibSpec`, `ivVal`, `sevenVal`, `sevenBytes`, `intUndefBytes`,
`intTy`); the dispose, region-loop, malloc-list and even/odd conclusions
are over engine fields only." `even_odd_certified_production`
(`EvenOddExhibit.lean:721`–`:732`) concludes `dres.dres_core_value =
ivVal (1 - n % 2)` — `ivVal` is `def ivVal` at `LoopExhibit.lean:63`, a
package definition, so the even/odd conclusion is NOT over engine fields
only, and the paragraph names `ivVal` as used and then says even/odd
uses none. `list_reverse_certified_production`
(`ProdLoopExhibit.lean:1435`–`:1451`) also uses `ptrVal`
(`ListRevExhibit.lean:466`, a package definition) and the abbreviation
`CellMap` (`Adequacy.lean:1407`), neither listed. Under a heading that
says "exactly", these are errors.
Fix: "… the exhibits' value/byte constants (`fibSpec`, `ivVal`,
`ptrVal`, `sevenVal`, `sevenBytes`, `intUndefBytes`, `intTy`); the
dispose, region-loop and malloc-list conclusions are over engine fields
only; even/odd's is `ivVal (1 - n % 2)`." Or state the exemption as the
WALKTHROUGH does — "nothing package-defined but the authored program,
its wrapper and the pure readout predicates/constants" — and list the
constants once.

**D-1. `hbsz` is named in two places and explained in neither.** Lines
673–675: "`hbsz` inside `Frag.case_value` (`Soundness.lean:4296`) is
carried, not proved (§2.2; KOI B7)"; line 714: "the carried `hbsz`
premise are the residual". A reader is told a premise is "carried" but
not what it says or why it matters. `Soundness.lean:4296`–`:4297`:
`hbsz : ∀ e', select_case subst_sym_expr cval pats = some e' → esize e' ≤
esize (caseRedex …)` — the selected branch's size is bounded by the case
node's, so the static size bound survives the substitution; it is a
hypothesis of fragment MEMBERSHIP that a client must discharge per
program rather than a theorem. README's register says exactly this in
one line; the normative surface should too.
Fix (§6): "`Frag.case_value` carries `hbsz` — the selected branch's
`esize` is bounded by the case node's (`Soundness.lean:4296`) — as a
membership premise the client discharges per program, not a theorem
(KOI B7)."

**C-1. Length: 738 lines, and the author's "no prose sentence exceeds
four wrapped lines" is not true of the text.** The reading order is right
and the new content is load-bearing; the document is nonetheless about
100 lines longer than it needs to be, in three identifiable places, and
several sentences are too long to check:
- *Sentences over four lines (prose, not name-enumerations):* lines
  95–103 (one sentence: `Config`, `Ctl`, its three fields, their engine
  meaning, `MachineCtx`'s six fields — 8 lines); 79–86 (the `current_loc`
  argument — 6 lines); 142–151 (the atomic-spec sentence, 9 lines);
  165–172 (the structural-rules sentence, semicolon-chained across 8
  lines); 194–200 (`CerberusRound`, 6 lines); 269–276 and 278–284 (the
  partial lane, 7 and 6 lines); 305–311 (the projection, 7 lines);
  484–492 (the `DriverSafeCtl` reading, 9 lines); 545–551 (the scheduler
  consequence, 7 lines); 564–574 (the manifest classes, 11 lines);
  605–616 (the boundary pattern, 11 lines). Each should be two or three
  sentences; the `Ctl`/`MachineCtx` one should be a two-line list.
- *§5, the manifest bullet (lines 564–589, 26 lines)* reproduces the
  manifest header's "WHAT GREEN ESTABLISHES / DOES NOT ESTABLISH" in
  substance. The header is the generated, gate-diffed text; the front
  document should say what the instrument is (5 lines), give the tail
  line, and cite the header for the exact guarantee. Saves ~15 lines and
  removes a second copy that can drift.
- *§7, Goals 1 and 2 (lines 701–716)* restate §2.4 and §2.2. A ledger
  needs: goal, status, the closing theorem names, the record. Six lines
  for the two. Saves ~10 lines. Goal 3's content (the `MemWF` fields and
  preservation theorems, lines 717–732) is NOT stated elsewhere and
  belongs in §2 (a §2.6 "The memory invariant"), with §7 pointing at it.
- *§6* restates §1/§4 for masks, fuel, tags (lines 661–672) — acceptable
  as a register, but each should be one line plus the KOI number and the
  section pointer (saves ~6 lines).
- *Glossary:* the right size and the right place; "a round" and "a lane"
  could be one line each. Two terms it lacks are used before or without
  definition: "the trio" (first at line 344, "pinned trio-exact (§3)",
  defined at 387–388) and the engine's round names `PCALL`/`RETURN`
  (line 99), `PROGRAM-DONE` (line 275), `ACTION_EVAL` (not used here but
  in the manifest) — one glossary line: "the engine's round names, as
  in `Core_reduction.lean`: PCALL, RETURN, PROGRAM-DONE…".
- *The two worked readings (§4)* are the right size; the premise list is
  the best part of the document.
- *Duplication with the other surfaces:* §1 "The fragment" and README
  "Scope, exactly" cover the same ground; §6 and README's "Registered
  divergences and limitations" table overlap on ~10 rows. That is by
  design (the README is the register, ARCHITECTURE the normative
  statement) and acceptable; but ARCHITECTURE sends the reader to
  README "Scope, exactly" and WALKTHROUGH §7, both of which are written
  in the slice vocabulary the rewrite just removed from ARCHITECTURE
  (README:34–58: "kill/free arc K2", "since calls arc C4", "fragment
  closure, 2026-09-02"; WALKTHROUGH:1717–1740: "C1 (2026-09-03) made …
  C2 added … C3 added … C4 closed"). Not this document's defect; noted
  for the orchestrator as the next shop-window pass.
Concrete target: ~630 lines, by the cuts above; nothing that is a
disclosure goes.

### LOW

**T-4. "their `_op` forms" implies a `create_op` that does not exist.**
Lines 68–70: "the memory actions `store`/`load`/`create`/`kill`/`alloc`
at evaluated operands, and their `_op` forms at operands in the covered
pure grammar". `Frag` (`Soundness.lean:4150`–`:4314`, 23 constructors,
counted) has `store_op`, `load_op`, `kill_op`, `alloc_op` and `memop_op`;
`create` (`:4167`) exists only at evaluated operands. Fix: "and the
`_op` forms of `store`/`load`/`kill`/`alloc` at operands in …".

**T-5. Off-by-three engine cite.** Lines 547–549: "`new_drive_core_threads`
calls the per-thread loop through its fixed-budget wrapper (generated
`Driver.lean:352`–`:355`)". At the pin, `:352`–`:354` are blank/comment,
the `def` starts at `:355` and the call `drive_nonmemory_steps_aux2
_lemReader_tagDefs` is at `:358`. Fix: "`:355`–`:358`".

**T-6. `KOI C11–C13` cites a closed item as an instrument limit.** Lines
690–692: "the variant table is a reviewed reading, the boundary check is
text-based, the claim matrix is prose (§5; KOI C11–C13)". KOI C13 is
"CLOSED at H1a (TSV header …)"; the two open instrument limits are C11
(the comment stripper is not string-literal-aware) and C12 (per-module
allowances). The claim matrix being prose is not a KOI item at all; it is
stated in CLAIMS.md's header. Fix: "(§5; KOI C11, C12; CLAIMS.md
header)".

**T-7. Two small imprecisions in §1.** (a) Lines 101–103: "`MachineCtx`
(`:405`–`:413`) carries the file, the tag definitions, the extern map,
the thread identity, `currentLoc` and the run state" — the structure has
eight fields; `parent : Option Nat` and `errno : PointerValue` are
omitted. "carries" is not "exactly", but the reader who opens the file
finds two fields the document did not mention; add them or say "among
its fields". (b) Line 7: "`scripts/semantics-pin.env`" — the file is at
the repository root (`../scripts/semantics-pin.env` from the package);
every other root-script cite in the document uses the `../scripts/`
form.

**D-2. "not a restriction added here" over-claims for the tag table.**
Lines 459–461: "`drive fmapEmpty false` fixes empty tag definitions and
no concurrency — the shipped driver's own sequential mode, not a
restriction added here." `false` (no concurrency) is the shipped
driver's mode — the generated `drive` fails with "CONCURRENCY IS BROKEN"
at `true` (`Driver.lean:530`). `fmapEmpty` is the tag-definition table
of the WRAPPED FILE, a parameter the statement chooses; a program with
struct tags would need another table and is outside every adequacy
theorem (`htd : M.tagDefs = fmapEmpty`, KOI B4 — "a narrowing"). The
sentence should not let the tag restriction ride on the concurrency
one. Fix: "… `false` is the shipped driver's own sequential mode;
`fmapEmpty` is the wrapped file's (empty) tag-definition table — the
`htd` premise of §4, KOI B4."

**S-1. Two narrative residues in §7.** (a) Lines 720–722: "cursor bounds
(incl. `la_pos : 0 < lastAddress`, added on orchestrator direction,
[AGENT 2026-09-03], DECISIONS 'KILL/FREE K3 LANDED')" — "added on
orchestrator direction" is how the field came to be, not what it is;
the provenance tag alone carries the record. Fix: "(incl. `la_pos : 0 <
lastAddress`; [AGENT 2026-09-03], DECISIONS 'KILL/FREE K3 LANDED')".
(b) Lines 736–738: "The arc records that closed the goals — fragment
closure, kill/free, calls, the fuel-lane restatement, the
external-audit response, the hygiene slices — are indexed in …" —
"slices" is the vocabulary the rewrite removed; the archive's header
already names the arcs. Fix: "The records of the arcs that closed the
goals are indexed in `docs/2026-09-04_architecture-history-archive.md`."

**S-2. Pointers INTO this document from the other surfaces went stale
with the renumbering, and the rewrite did not fix them.** `docs/CLAIMS.md:44`
"outside `Frag` (ARCHITECTURE §7, KOI B8 …)" — the fragment boundary is
now §6; KOI B7 "ARCHITECTURE §6 (lines ~412–444)" — the line range is the
old document's; KOI B9 "ARCHITECTURE §7" — the parametric deferral is now
§6; `README.md:835` "not a gate — ARCHITECTURE §7" — the inventory is now
§5; `EvenOddExhibit.lean:4`/`TwoLabelExhibit.lean:4` "ARCHITECTURE §7"
(history in module headers; harmless). The manifest generator's
"ARCHITECTURE §7 Goal 2" (`capability_manifest.lean:97`) still resolves.
The rewrite notes (deviation 5) say README was checked for
contradictions but not for pointers. Fix: the four pointers above, in
the same commit as the ARCHITECTURE fixes (CLAIMS.md and README are
package files; KOI is orchestrator-owned — flag it).

**C-2. One term used before definition.** "trio" — line 344 ("All nine
are pinned trio-exact (§3)") precedes its definition at lines 387–388.
Either gloss it or write "pinned with axiom set exactly the classical
trio (§3)".

## Verified true (the cites checked, and how)

Method: `sed -n`/`grep -n` over `CerberusHeapLang/*.lean` and
`scripts/*` in the review worktree at `cd68c46`; over the primary
checkout's `.cerberus-ws/lean_frontend/generated/*.lean` (pin verified
`f95ef8d9c` by `git rev-parse`) and `.lake/packages/LemLib/lean-lib/
LemLib.lean`; over `docs/DECISIONS.md`, `docs/KNOWN-OPEN-ITEMS.md`,
`cerberus-heaplang/docs/{CLAIMS,CAPABILITY_MANIFEST}.md`,
`docs/2026-09-04_h1-notes.md`. 60+ cites checked; the ones below are the
load-bearing ones.

- **Glossary.** `drive_nonmemory_steps_aux2_lemFuel` generated
  `Driver.lean:346` ✓; `Frag` `Soundness.lean:4149` ✓; `Step`
  `Step.lean:1456` ✓; `spikeCtx`/`spikeCtl`/`procCtx`/`procCtl`
  `Step.lean:3355`/`:3331`/`:3363`/`:3336` ✓ (`spikeCtl = ⟨[], none,
  default⟩`, `procCtl p = ⟨[], some p, default⟩`); `prodCtx`/`prodCtl`
  `ProdEntry.lean:580`/`:567` ✓; speedbumps `DECISIONS:265` [USER
  2026-09-02] ✓.
- **§1.** 23 constructors at `:4150`–`:4314` (listed and counted:
  val_pure, store, load, create, kill, kill_op, alloc, alloc_op, sseq,
  annot, save, if_, run, sseq_spec, pure_sym, load_op, sseq_sym,
  memop_vals, memop_op, store_op, case_value, wseq, call) ✓; `PePure`
  `:2007` with val/sym/op/arrayShift and `isMirroredOp` (`:2001`) = the
  eight ops Add/Sub/Mul/Eq/Lt/Le/Gt/Ge ✓; `BareHead` `:3981` ✓; the
  annotation-free header `:4129`–`:4147` says what the document says,
  including the mover ✓; `Ctl` `:371`–`:374` (κ, proc, execLoc) ✓;
  `Config` `:400` ✓; `MachineCtx` `:405`–`:413` (see T-7a); `Step.call`
  `:2047` pushes `(ctl.proc, ctx) :: ctl.κ` ✓; `callRedex?` `:703` ✓;
  `Step.ret`/`ret_annot` `:2079`/`:2096` ✓; `Step.ctl_cases` `:2250` ✓;
  `Lang.lean:58` `primStep := … Step p.1.M …` ✓; `wps` `Wps.lean:301`,
  `wps.pre` `:217` with the four clauses (value / jump / call / step —
  read) ✓; `LabelSpec` `:113`, `ProcSpec` `:129` ✓; `wpt` `Wpt.lean:200`,
  `⌜1 + m ≤ k⌝` at `:167`, `1 + m + k' ≤ k` at `:172` ✓; mask sites 21/26
  ✓; `AtomicStep` `Rules.lean:194` (∀ E₁ E₂ : CoPset) and `wp_of_atomic`
  `:210` `{E : CoPset}` ✓ (but see T-1); TRUST ARCHITECTURE [USER
  2026-08-29] `DECISIONS:86` and CLAUDE.md ✓; THE BOUNDARY IS FAIL-CLOSED
  [USER 2026-09-02] `DECISIONS:816` ✓; THE DEMO'S SCOPE, RESTATED [USER
  2026-09-04] `DECISIONS:2130`, quotation verbatim with elision ✓.
- **§2.1.** All twelve atomic specifications at the cited lines
  (`:264`, `:365`, `:557`, `:648`, `:767`, `:863`, `:991`, `:1204`,
  `:1316`, `:1502`) ✓; `load_atomic` takes `dq : DFrac` ("load at any
  fraction") ✓; `wps_of_atomic` `Wps.lean:345`, `wpt_of_atomic`
  `Wpt.lean:664` ✓; `isAtomicMemberAccess` generated `CerbMem.lean:1949`,
  `| none => false` (read), used at `:2003` (`loadM`) and `:2067`
  (`storeM`) ✓; the bundles `Heap.lean:2749/2714/2734/3319/3310/3481/
  3683/3783/3793/2464/2475` ✓; `wps_frame_labels`/`wpt_frame_labels`
  `Wps.lean:701`/`Wpt.lean:563` ✓; `blockSpecs_intro`/`blockSpecsT_intro`
  `:3195`/`:2975` ✓; `procSpecs_intro`/`procSpecsT_intro` `:3287`/`:3032`
  ✓; `wps_call`/`wps_call_root` `:417`/`:473`, `wpt_call`/`wpt_call_root`
  `:726`/`:758` ✓; `Rules.lean:35`–`:44` says no raw-WP sequencing rule
  and why ✓; `wps_sound_cps` `:3440`, `wp_ret`/`wp_ret_annot`
  `:3326`/`:3367`, `wps_sound`/`_empty` `:3637`/`:3657`; `wpt_sound_cps`
  `:3173`, `wpt_sound`/`_empty` `:3382`/`:3400` ✓; `wps_sound` consumers
  exactly `CallSmoke:330`, `FibRecExhibit:648`, `EvenOddExhibit:501` ✓;
  `wpt_sound` consumer exactly `cs_twp_readout` (`CallSmoke:455`, at
  `:461`) ✓ (see T-2 for `wps_sound_empty`).
- **§2.2.** `CerberusRound` `Round.lean:195`, `loop_step` `:965` ✓;
  `engine_step_matchU` `:1010`–`:1015` matches the quoted block
  character for character ✓; `step_iff_cerberusRound` `:1598` with
  `hstep : ∃ c', Step …` ✓; `frag_round_complete` `:5369` concludes
  `RoundComplete` = `(∃ c', Step M c c') ∨ ShippedRefusal M c ∨ OpenRound
  M c` (`:408`) ✓; `ShippedRefusal` `:214` arms error/killed/fork/panic/
  panic_env/panic_memop/error_next/panic_noproc ("the `panic` family") ✓;
  `OpenRound` `:357` with `eval_uncovered` `:379`, `run_surplus` `:393` ✓;
  `complete_store` `:2300` … `complete_ret` `:5351` ✓;
  `cerberusRound_classify` `:5476` premises `hwf : M.SeqWF`, `hκ : ctl.κ =
  []`, `hf`, `hsz` ✓; `RoundClass` `:1631` five arms ✓; the
  "WHAT CONSUMES WHAT" header `:141`–`:153` says what §2.2 says ✓;
  `loop_step_frag`/`loop_step_frag'` `DriverCollapse.lean:2118`/`:2024` ✓.
- **§2.3.** `dgBody` `DivergeExhibit.lean:69`, `dg_loop_exhausts` `:126`
  (∀ fl dst acc … `NDkilled CerbND.fuelExhaustedKill`),
  `diverge_total_unprovable` `:172` (any `σ₀ m₀ hcoh Ls Ψ k`, `hwp : … ⊢
  blockSpecsT … ∗ wpt … k Ψ (dgBody ra) …` → `False`) ✓.
- **§2.4.** `drive_nonmemory_steps_aux2_wrapper_defeq` generated
  `CerbND.lean:396`–`:397` `rfl`, `drive_wrapper_defeq` `:467` `rfl` ✓;
  `spike_step_adequacy`/`_alloc` `Adequacy.lean:568`/`:667` apply
  `wp_strong_adequacy_gen` (`:581`, `:683`) ✓; `engine_adequacy`/`_alloc`
  `:1278`/`:1344` ✓; `DriverSafeCtl` `:932` — read in full: ∀ dst acc fl;
  thread_states singleton; layout; `core_extern = fmapEmpty`; file;
  `LabeledProcs`; `CtlTied`; exhaustion or `NDactive … Step_done2 v` ✓;
  `LabeledProcs`/`CtlTied` `DriverCollapse.lean:2178`/`:2205` ✓;
  `drive_safe_aux` `:1079` `private` ✓; `ControlOk` `:800`, `FragProcs`
  `:767` ✓; `loop_zero_exhausts`/`loop_step_done_exhaust`/`loop_step_done`
  `:2246`/`:2257`/`:392` ✓; `wpt_driver_cps` `ProdLoop.lean:609`
  (premises read), `DriverDoneCtl` `:456` with `k + 2 ≤ fl` ✓,
  `driverDoneCtl_step` `:537`, `wpt_driver_done_procs` `:799`,
  `DriverDoneAt`/`wpt_driver_aux`/`wpt_driver_done`/`_alloc`
  `:56`/`:175`/`:290`/`:358` ✓; `project_triple_pure` `:1605`,
  `MemTriple` `:1518` (`P ##ₘ R`, `Sat … (union P R)`, `DriverSafeCtl`) ✓,
  `project_triple_pure_alloc` `:1743`, `MemTriple_alloc` `:1669`,
  `LaunchCoh` `:422`–`:432` (coh, `wf : MemWF σ`, `budget : B ≤ headroom
  σ.lastAddress`) ✓; the `*_consequence` lemmas `:1909` (`pure_`) …
  `:2007` (`cells_`) ✓; `Sat` `:1415`, `DeadAt` `:1900` ✓; `prodFile`
  `ProdEntry.lean:125`, `prodFileWith` `:544`, `prodFile_eq_with` `:549`
  `rfl` ✓; `prod_run_eqJ_procs` `:716` with `hfl : k + 2 ≤
  CerbFuel.driverFuel` ✓; `prod_run_eqJ` `:402`; `prod_run_safe_procs`
  `:768` — statement read: `drive_lemFuel fuel`, singleton, `Killed dst'
  fuelExhaustedKill ∨ Active dres ∧ ψ …` ✓; `prodMem₀` `:212`,
  `prodMem₀_memWF` `:243` ✓.
- **§2.5, the table.** All nine signatures read in full
  (`ProdExhibit.lean:264`; `ProdLoopExhibit.lean:75`, `:620`, `:1435`;
  `DisposeExhibit.lean:1479`; `RegionLoopExhibit.lean:633`;
  `MallocListExhibit.lean:1654`; `FibRecExhibit.lean:865`;
  `EvenOddExhibit.lean:721`): every premise in the table is present and
  no input-dependent premise is missing (`hn`, `hfuel` bounds `2n+6`,
  `6n+8`, `7n+5`, `25n+9`, `3n+6`, `fibRounds n.toNat + 4`; `hcost`,
  the two `hB`s exactly as printed) ✓; none carries a termination
  hypothesis ✓; `CerbFuel.driverFuel = 100000000` generated
  `CerbFuel.lean:71` ✓; `fibRounds` `FibRecExhibit.lean:450` (3, 3, +9),
  `fibRounds_closed` `:470` `fibRounds n + 9 = 12 * fibSpec (n+1)` ✓;
  `regionCost`/`headroom` `Heap.lean:2322`/`:2267` ✓; `ml_budget_bridge`
  `MallocListExhibit.lean:1626` ✓; `SeedChain` `ListRevExhibit.lean:1210`
  ✓; `fib_rec_certified` `:814` and `even_odd_certified` `:673` take
  `(fuel : Nat)` ✓. (Package definitions in conclusions: see T-3.)
- **§3.** `allowedAxioms` `Audit.lean:159`–`:160` = the trio ✓; pin loop
  `:615`–`:616` ✓; the sweep `:617`–`:636` (theorems of every
  `CerberusHeapLang.*` module) and the banned-axiom sweep `:637`–`:653`
  (`sorryAx`/`ofReduceBool`/`ofReduceNat`, every constant kind) ✓; 402
  pins — the verbatim gate line in `docs/2026-09-04_h1-notes.md:752`
  ("export pins: 402 trio-exact") ✓; sub-trio notes `:354`–`:356`,
  `:380`–`:384`, `:523`–`:525`, `:552`–`:553` ✓; "There is no declared
  boundary axiom" `Audit.lean:45` verbatim ✓; gate 1 `../scripts/
  test_unit.sh:28` ✓; the pinned tree: `grep -rln '(sorry'` over the
  primary checkout's `generated/*.lean` = 0 files, `^axiom` = 0 ✓; the
  referent rule [USER 2026-09-02] in CLAUDE.md ✓.
- **§4.** `fib_certified_production` and `counter_loop_certified` quoted
  verbatim (diffed by eye against `ProdLoopExhibit.lean:75`–`:89` and
  `LoopExhibit.lean:427`–`:439`) ✓; the section variables `loc ann ra mo
  bty xbty` (`LoopExhibit.lean:403`–`:404`) ✓; `Coh`/`CellCoh`
  `Heap.lean:386`/`:358` ✓; premises of `engine_adequacy`
  `:1278`–`:1296`, `project_triple_pure` `:1605`–`:1613`, `wpt_driver_cps`
  `:609`–`:620`, `wpt_driver_done_procs` `:799`–`:809` — `htd`, `hex`,
  `hκ`, `hQf`, `hQpot`, `hPf`, `hfrag`, `hpot`, `hcoh`/`hl`, `hcl`, `hwp
  … @ NotStuck; ⊤` all present as described ✓; `pot` `Potential.lean:43`,
  header "step-monotone size potential" ✓; `lemDefaultFuel = 1000000`
  `LemLib.lean:56` ✓; `shipped_done` `Round.lean:1661` ✓; the fuel ruling
  [USER 2026-09-03] `DECISIONS:1787` and the two-loop reading there ✓
  (quotation: see P-1); `new_drive_core_threads` calls the wrapper
  (`Driver.lean:358`; see T-5); `current_proc_opt := (some main_sym)` at
  `Driver.lean:530` ✓; the fuel-parameter review `../docs/2026-09-04_
  review-of-fuel-parameter-design.md` has a §5 "Our restatement, sized" ✓.
- **§5.** `test_unit.sh:28/:39/:47/:65/:88` are the gate/speedbump
  headers named ✓; the import-direction check (`:65`–`:87`) greps `core`
  modules for `import CerberusHeapLang.(*Exhibit|Examples.|Prod)` ✓;
  `boundary_check.sh:46` is the pattern and it contains every name the
  document lists ✓; the check applies to `positive-client`/`declared-smoke`/
  `example-support` (`boundary_check.sh:7`–`:8`) ✓; TSV header lines 8–11
  say exactly the fail-hard sentence the document paraphrases ✓; the
  manifest tail: 23 constructors, 50 rows, 30/0/0/15/5, 0 red, 18
  consumers; CLAIMS 11 rows / 90 names ✓; 18 consumers = the sixteen
  program exhibits + CallSmoke + ReadinessSmoke (manifest MODULES line)
  ✓; the ten classes (TSV/manifest) ✓; `BOUNDARY: 19 modules checked, 0
  internals mention(s) in total, exit=0` at `h1-notes.md:781` ✓;
  `parametric_inventory.lean:1`–`:16` ON DEMAND [AGENT 2026-09-04],
  fail-closed ✓ (`DECISIONS:1916` AR5-MANIFEST entry exists).
- **§6.** The fifteen NO-RULE variants: matched one-for-one against the
  manifest's 15 NO-RULE rows (3 store, 3 load, 3 create, 4 kill, 1
  alloc, 1 memop_vals) ✓; the five OUT-OF-SCOPE variants likewise ✓;
  `hjmp` `DriverCollapse.lean:2035`, `CtlTied.noproc` `:2213` ✓; KOI
  numbers A1/A2/A3/B1–B9/B11/B12/B14 point at entries that say what the
  document says they say ✓ (C13: see T-6); the parametric deferral
  `DECISIONS:372`–`:384` [USER 2026-09-02] ✓ (the document's tag lacks
  the date — see P-2 below, folded into LOW).
- **§7.** THE DEMO'S ACCEPTANCE GOALS `DECISIONS:703` — the quoted
  fifteen words are the register's inner quotation, verbatim ✓; `MemWF`
  `Heap.lean:1583` ten fields (live_lt, dead_lt, live_dead, disj,
  cursor_lo, size_nonneg, la_wf, la_pos, dyn_lo, dyn_disj — listed) ✓;
  `CohG.wf : get? mk 0 ≠ none → MemWF σ` (`:2632`ff, "under cursor
  presence") ✓; `create_fresh_global` `:1801`; `MemWF.loadM/storeM/
  allocateObject/allocateRegion/killM` `:1817/:1877/:1898/:1937/:2010`,
  with `storeM` over `lk : Bool`, `allocateObject` over `initOpt`,
  `killM` over `isDyn` ✓; `la_pos` [AGENT 2026-09-03] `DECISIONS:1142` ✓.
- **Shop-window.** 23 `2026-` tokens, every one inside a `[USER …]`/
  `[AGENT …]` tag or a `docs/…` path (listed by grep) ✓; zero
  "former/formerly/until/since/deleted/driveU" ✓; `K3`/`AR5` occur only
  inside two cited DECISIONS titles ✓; every `docs/…` and `../docs/…`
  path cited exists (`ls`) ✓; the archive from its line 52 is
  byte-identical to `git show b8413a5:cerberus-heaplang/ARCHITECTURE.md`
  (diff exit 0; 686 lines) ✓ — nothing load-bearing for the present was
  lost: I read the archive's header table and spot-read its §2, §6 and
  §7; every present-tense fact there (the `Ctl` liveness, the region
  type-blindness, the `MemWF` fields, the `la_pos` provenance, the
  two-bridge design, the `hbsz` premise) is in the new §1/§2/§6/§7.

Minor provenance note folded here (not a separate finding): line 688
"([USER] deferral, KOI B9; …)" has no date; the register has it
(`DECISIONS:372`, [USER 2026-09-02]). Add the date.

## Reviewer 3's findings — genuinely resolved?

One word each: T-1 resolved; T-2 resolved-with-defect (this review's
T-2: the `wps_sound_empty` list is incomplete); T-3 resolved; T-4
resolved-with-defect (this review's T-3: `ivVal`/`ptrVal`); T-5
resolved; T-6 resolved; D-1 resolved; D-2 resolved; D-3
resolved-with-defect (this review's T-1: the "only" clause); D-4
resolved-with-defect (this review's P-1: the "verbatim" quotation); D-5
resolved; S-1 resolved; S-2 resolved; S-3 resolved; S-4 resolved (two
residues, this review's S-1); C-1 resolved; C-2 resolved (except "trio",
C-2 here); C-3 partly (the table is there; a dozen prose sentences still
run 6–11 lines, C-1 here); C-4 resolved; P-1 resolved; P-2 resolved.
Exceptions in one sentence: every finding was acted on in the text, not
merely marked, but four of the fixes introduced a new false or
incomplete sentence at the point of repair (the mask "only", the
consumer list, the "exactly" paragraph, the quotation) — the pattern is
an author verifying the review's suggested fix text rather than the
tree, and it is exactly what a re-review is for.

## Not checked

- No `lake`/`lean` invocation: the 402-pin count, the axiom sweeps and
  the gate tail are taken from the verbatim gate transcript in
  `docs/2026-09-04_h1-notes.md` §8 (the second §8, at `29d9195`) and
  `DECISIONS` (H1 entry), not re-run. (`trioExports` name-tokens counted
  by grep = 405, which includes double-backtick names inside list-body
  comments; the build's own count is the authority.)
- iris-lean internals (`wp_strong_adequacy_gen`'s statement, `Language`
  laws) — taken as the library's.
- The pinned tree's differential-validation numbers (README "What you
  are asked to take on faith") — not this document's claims.
- `README.md` and `WALKTHROUGH.md` beyond the sections this document
  points at and the pointer grep in S-2; their own shop-window state is
  noted under C-1 but not reviewed.
- `docs/2026-09-04_h1-notes.md` beyond §8; the AR5 and F1 records; the
  hygiene of `KNOWN-OPEN-ITEMS.md` itself (B8's two-label/mutual-recursion
  items are closed by H1b and still listed — the rewrite notes flag it;
  orchestrator-owned).
- The claim that `Examples/MirrorCoverage.lean` witnesses every RULE and
  NO-RULE row (a CLAIMS.md C6 claim, not an ARCHITECTURE claim).
- Whether `evalClass`'s `.uncovered` leaf set (a `Proc`-named unbound
  symbol, a binop at two floats, `OpEq` at two ctypes) is exhaustive of
  the engine's accepted-but-unmirrored leaves — the document says the
  residual is a superset and claims no more; I did not read EvalClass.lean
  beyond its header.
