# ARCHITECTURE.md — fresh full review (review 3)

**VERDICT: B− — FAIL.** Reviewer: fresh (no prior contact with this
document or its predecessors); standard: grumpy PL professor, "would I
sign this as the paper's system section". Tree: `worktrees/review-arch`
detached at `e242342` (= main). Method: source reading only (no Lean
invocation); every load-bearing claim of ARCHITECTURE.md was checked
against the `.lean` text, the scripts, the generated manifest, the
pinned semantics workspace at `f95ef8d9c`, `docs/DECISIONS.md`,
`docs/KNOWN-OPEN-ITEMS.md` (KOI) and the external audit of 2026-09-04.

Summary of the verdict. The mathematical core of the document is
accurate: the statement shapes of `engine_step_matchU`,
`cerberusRound_classify`, `DriverSafeCtl`, `DriverDoneCtl`,
`engine_adequacy`, `project_triple_pure`, `prod_run_safe_procs`,
`prod_run_eqJ_procs`, the eight closed statements and their `hfuel`/`hB`
hypotheses, the manifest counts, the MemWF field count and the
instrument descriptions are all true of the tree (see "Verified true").
It fails on three axes a system section cannot fail on: (1) a handful of
false or stale sentences (an enumeration of 12 items labelled "15", a
"no export consumes" claim contradicted by a pinned export, a stale
engine line cite, an undisclosed premise on a root-of-trust statement, an
instrument overclaim); (2) disclosure gaps for the intended reader — the
document never says that the fragment is annotation-free so that no
C-elaborated program is in it, never mentions the `pot … ≤ lemDefaultFuel`
(10^6) hypotheses that every adequacy theorem carries, never mentions
that both judgments are fixed at the top mask, never states the ruled
Reynolds/O'Hearn reading, and never mentions the negative
total-correctness result; (3) it is written as a changelog, not a
description: 42 date stamps, 22 `K<n>` slice ids, 16 `C<n>` slice ids,
three CLOSED arc chronicles filed under "open items", and a
paragraph on a `sorry` that no longer exists. A professor would return
it with "describe the system; put the history in the records" written
across §6–§7.

The fixes are mechanical and the document can reach A with one focused
rewrite pass: correct the five T- items, add the six D- sentences, then
cut every sentence that begins with "since", "until", "former",
"deleted", "was", a slice id or a date (there are about seventy) and
replace each with a pointer to the record that owns the history.

---

## Findings, ranked by severity

Ids: T- truth, D- disclosure, S- shop-window, C- clarity, P- provenance.
Line numbers are `cerberus-heaplang/ARCHITECTURE.md` at `e242342`.

### HIGH

**T-1. The NO-RULE enumeration lists 12 variants under a count of 15.**
Lines 598–603: "15 NO-RULE (the locking store; union-member pointers at
load and store; the read-only-cell load at the statement level;
zero-size, atomic and non-inert `create` types; the static kill of a
region; `free(NULL)`; `free` of a created object at a colliding base;
the zero-cost `alloc`; the function-vs-concrete `PtrEq`)". That
parenthetical enumerates 12 rows. The manifest
(`docs/CAPABILITY_MANIFEST.md`, tail line "50 variant rows (… 15
NO-RULE …)") has three more, the AR5 range audit's C-3 additions: kill
of either kind through a union-member pointer (row `Frag.kill`),
whole-object store at an atomic-typed allocation (row `Frag.store`),
whole-object load at an atomic-typed allocation (row `Frag.load`). The
count was updated (per DECISIONS 2026-09-04 AR5 range-audit entry,
"counts updated in README/ARCHITECTURE") but the list was not. A reader
checking the arithmetic finds the front document wrong.
Fix: add "kill of either kind through a union-member pointer; the
whole-object load and store at an atomic-typed allocation" to the
parenthetical, or drop the enumeration and point at the manifest.

**T-2. "metatheorems no export consumes" is false.** Line 171–173:
"`wpt_sound_cps` (strong induction on the budget) with
`wpt_sound`/`wpt_sound_empty` into TWP (metatheorems no export
consumes)". `Examples/CallSmoke.lean:455–461` — `theorem cs_twp_readout
… := by refine (csMain_wpt …).trans ?_ … (wpt_sound (ctl := ⟨[], some
csMain, ℓ⟩) rfl 6 …)` — consumes `wpt_sound`, and `cs_twp_readout` is a
pinned export (`Audit.lean:504`: ``CerberusHeapLang.cs_twp_readout``).
`wps_sound` is consumed by eight exhibit modules (Exhibit, Loop,
Struct, Fib, FibRec, Case, Wseq, CallSmoke — grep). If the parenthetical
is meant to say "no CLOSED (shipped-driver) export consumes them", say
that; as written it is false.
Fix: "(the TWP/WP collapses at the entry control; consumed by the
exhibits' Iris-level readouts, by no shipped-driver statement)".

**D-1. The static fuel premise `pot … ≤ lemDefaultFuel` is absent from
the document.** `grep -c 'pot \|hpot\|Potential' ARCHITECTURE.md` = 0.
Every adequacy theorem carries it: `engine_adequacy` (Adequacy.lean:1278–
1290: `hQpot : … pot cont ≤ lemDefaultFuel`, `hpot : pot e₀ ≤
lemDefaultFuel`), `project_triple_pure` (:1605–1613, same),
`wpt_driver_done_procs` (ProdLoop.lean:799–809: `hpot`), `wpt_driver_cps`
(:609–620: `pot e ≤ lemDefaultFuel`), and `MachineCtx.FragProcs`
(Adequacy.lean:767–773: `potBound`, `labels … pot cont ≤ lemDefaultFuel`).
`lemDefaultFuel = 10^6` is LemLib's constant
(`.lake/packages/LemLib/lean-lib/LemLib.lean:56`). §4 says the lanes hold
"AT EVERY `fl`" (line 195) and §6 says "at EVERY fuel `fl`" (line 358):
true of the DRIVER-LOOP fuel, but the reader is never told that a second,
fixed fuel constant (the pure evaluator's) remains a hypothesis of every
statement — this is exactly KOI A1 ("`… ≤ lemDefaultFuel` hypotheses at
~60 sites"), which the brief says must be on this surface. README/API
disclose it; ARCHITECTURE, the normative statement, does not.
Fix (§4, after "AT EVERY `fl`"): "Every adequacy theorem also carries the
STATIC premises `pot e ≤ lemDefaultFuel` and `pot cont ≤ lemDefaultFuel`
per registered body (`Potential.lean`; `FragProcs.potBound`) — the pure
evaluator's fuel `lemDefaultFuel = 10^6` is a fixed LemLib constant, not
quantified; with the shipped `CerbFuel.driverFuel = 10^8` of the closed
forms it is the fuel defect of KOI A1, ruled upstream (DECISIONS
2026-09-03 'FUEL IS A DEFECT')."

**D-2. The fragment boundary "annotation-free, therefore no
C-elaborated program" is absent.** `grep -i 'located\|annotation-free'`
finds nothing relevant (the two "located" hits are "relocated" and
"colliding"). `Soundness.lean:4129–4144` ("THE FRAGMENT IS
ANNOTATION-FREE … A located node would falsify that equation. Located
Core …") and README line 626 ("The fragment is annotation-free (`Expr []`
at every node); located Core is outside `Frag`") state it; CLAIMS.md
"Not claimed" lists "located Core (every C-elaborated program): outside
`Frag`". For a PL reader who arrives from the title "separation logic
over Cerberus Core" this is the single most important scope fact and the
normative document does not carry it. KOI B8 lists concurrency, function
pointers and external calls (§7 has those) but the C-front-end boundary
is missing from ARCHITECTURE entirely.
Fix (§2, where `Frag` is declared): "The fragment is ANNOTATION-FREE
(`Expr []` at every node, Soundness.lean `Frag` header): the programs
are authored Core; located Core — every program the Cerberus C front end
elaborates — is outside `Frag`, because the round's `current_loc`
equation would be falsified by a located node."

**D-3. The top-mask restriction (KOI B11) is absent.** `grep -c 'mask\|⊤'`
= 0. `wps` and `wpt` hard-code `⊤` (Wps.lean: 21 sites, Wpt.lean: 26 —
measured, matching DECISIONS 2026-09-04). The external audit's Finding 3
was DEFERRED by ruling; CLAIMS.md discloses it under "Not claimed";
ARCHITECTURE §3, which describes both judgments, says nothing. A reader
who knows Iris will ask on the first page.
Fix (§3, one sentence): "Both judgments are stated at the top invariant
mask (`⊤`; `AtomicStep`/`wp_of_atomic` are mask-generic, the statement
judgments are not) — mask-polymorphic composition is not available
(KOI B11, deferred by [USER] 2026-09-04)."

### MEDIUM

**T-3. Stale engine line cite.** Line 492–493: "`isAtomicMemberAccess =
false` at `alloc.ty = none` (CerbMem.lean:1619)". At the pin
`f95ef8d9c`, `.cerberus-ws/lean_frontend/generated/CerbMem.lean:1619` is a
string-conversion arm (`| .Int_leastN_t n => …`); `isAtomicMemberAccess`
is defined at :1949 and used at :2003 (`loadM`) and :2067 (`storeM`). The
Mirror-OCaml doctrine makes file:line cites load-bearing; a stale one is
a defect. (Audit.lean's ":1573 dynamic check" is likewise stale — `killM`
is at :1895, the check at :1913 — outside this document's scope, noted.)
Fix: "CerbMem.lean:1949 (definition), :2003/:2067 (the load/store
checks)".

**T-4. The "which root-of-trust statements name package definitions"
bookkeeping is inexact, and a premise is undisclosed.** Lines 314–316
call `fib_rec_certified_production` "the second root-of-trust statement
with a package definition in its text" and lines 321–323 call
`region_loop_certified_production` "the one root-of-trust statement with
package definitions beyond the program and `prodFile` in its text".
`exhibitA_prod` (ProdExhibit.lean:264–270) concludes `∃ i a : Int,
CellCoh fmapEmpty dst'.layout_state i ⟨a, intTy, (sevenBytes fmapEmpty)⟩`
— `CellCoh` is `structure CellCoh` at Heap.lean:358, a package
definition. The K4 audit (M-1) and WALKTHROUGH phrase the exemption as
"nothing package-defined but the authored program, its `prodFile` wrapper
and the pure readout predicates"; ARCHITECTURE dropped the readout
exemption and so its count is wrong. Separately,
`region_loop_certified_production` carries a third package-definition
premise the document never mentions: `(hcost : 0 < regionCost al sz)`
(RegionLoopExhibit.lean:633) — the statement is vacuous at zero cost,
which a reader of lines 317–324 (which list only `hfuel` and `hB`) cannot
know.
Fix: restore the readout exemption ("beyond the program, `prodFile` and
the pure readout predicates `CellCoh`/`DeadAt`") and add `hcost : 0 <
regionCost al sz` to the region-loop premise list.

**T-5. Instrument overclaim.** Lines 632–634: "Every instrument fails
hard on an unclassified package module, a classified module absent from
the build, or a class outside the vocabulary." The TSV's own header
(`scripts/module_classes.tsv` lines 8–11) says: "all three fail hard on a
class outside the vocabulary, on a listed module absent from the built
environment, and (the Lean scripts) on a package module absent from this
list" — the bash `boundary_check.sh` has no unclassified-module detection
(no such check in the script; grep for "unclassified"/module discovery:
none). Two of three instruments, not "every".
Fix: "the two Lean instruments fail hard on an unclassified package
module; all three on a classified module absent from the build or a
class outside the vocabulary."

**D-4. The ruled Reynolds/O'Hearn reading is not stated.** DECISIONS
2026-09-03 [USER] fixes: "the triple's semantics is the THREAD-level
statement (single-thread loop, ∀ fuel); the scheduler loop is degenerate
for the sequential fragment … the intended closed meaning is the 'for
every outcome in the run's outcome list' form, of which the proved
singleton equation is the sequential strengthening." ARCHITECTURE §6
(lines 370–376) gives the MEASUREMENT ("the `fuel` parameter of
`drive_lemFuel` bounds the OUTER `driver2` rounds only … the 'however
long the run' content lives in the loop-level fact `DriverSafeCtl`") but
never the reading: neither "thread-level statement = the triple's
semantics", nor "scheduler degenerate for the sequential fragment", nor
the outcome-list meaning (KOI B5: "Doc surfaces to state the outcome-list
reading explicitly"). KOI B5 defers this to the A1 restatement slice, but
the front document is exactly the surface a reader uses to interpret
`prod_run_safe_procs`'s singleton equation; one sentence now costs
nothing and prevents the over-reading "the ∀ fuel of the closed form is
the run-length quantifier".
Fix (§6, after line 376): "READING ([USER 2026-09-03]): the triple's
semantics is the THREAD-level statement `DriverSafeCtl` (the single-
thread loop, ∀ fuel); the scheduler loop `driver2` is degenerate for the
sequential fragment (one round, no schedule change) and becomes live only
under concurrency or external C calls; the closed form's singleton
EQUATION is the sequential strengthening of the intended 'for every
outcome in the run's outcome list' meaning (KOI B5)."

**D-5. The empty-tag-definitions premise is not stated for the adequacy
lanes.** §4 line 192: "with empty extern, the context's file and the
registration ties" — `engine_adequacy` (Adequacy.lean:1279) also requires
`htd : M.tagDefs = fmapEmpty`; so do `project_triple_pure` (:1606),
`wpt_driver_cps` (:610) and `wpt_driver_done_procs` (:800), and
`loop_step_frag` (DriverCollapse.lean:2119). KOI B4 records this
narrowing and says it is disclosed in WALKTHROUGH §1.1; the normative
document mentions `fmapEmpty` only as the production `drive fmapEmpty
false …` (line 286–287), never as a premise of the generic theorems. A
reader must learn that no struct/union tag definitions exist in any
proved configuration.
Fix (§4, line 192): "with EMPTY tag definitions and extern map
(`M.tagDefs = fmapEmpty`, `M.extern = fmapEmpty` — the production
driver's `drive fmapEmpty false …`; KOI B4), the context's file …".

**S-1. §7 "THE OTHER OPEN ITEMS" is three closed-arc chronicles.** Lines
478–574: "**Loads and stores through a REGION pointer — CLOSED at K5
(2026-09-03; K4's finding).**" (29 lines), "**The kill/free arc K0–K5.1 —
CLOSED (2026-09-03).** … In one line each: K0 … K1 … K2 … K2.5 … K3 … K4 …
K5 …" (29 lines), "**The calls arc C1–C4 — CLOSED (2026-09-03).** … In one
line each: C1 … C2 … C3 … C4 …" (27 lines). None of these is open; each
already has its dated record (`docs/2026-09-03_kill-free-arc-record.md`,
`docs/2026-09-03_c{1,2,3,4}-notes.md`, `docs/2026-09-03_k5-notes.md`).
A system section describes the region access rules, the kill/free rules
and the call machinery as they ARE (they are already described in §3,
§4, §6); the arc narratives belong in the records. Under the heading
"open items" they also bury the two items that are open (the two-label
exhibit; the deferred parametric interfaces).
Fix: delete the three CLOSED bullets; keep "Still open, by design"
(mutual recursion, function pointers, two-label exhibit, parametric
interfaces) as a five-line list with KOI B8/B9 pointers; one line at the
head of §7: "Arc records: kill/free K0–K5.1, calls C1–C4, fuel-lane F1,
external-audit response AR5 — `docs/2026-09-03_*`, `docs/2026-09-04_*`."

**S-2. §6 carries a paragraph about a `sorry` that does not exist.**
Lines 274–285: "ADMISSIONS IN THE PINNED SEMANTICS TREE: NONE (measured
2026-09-03). … until the 2026-09-03 re-pin it carried one generated
admission — two `(sorry : String)` terms in the debug-log branch of
`auxAddToRfLoad` in the generated concurrency model (`Cmm_op.lean`),
outside every export cone — which the fuel-arc head closes …". Verified
at the pin: `grep -rln '(sorry' generated/*.lean` is empty. The system
section needs one sentence ("The pinned tree declares no `axiom` and
contains no `sorry` (measured at `f95ef8d9c`; `sorryAx` reaches no
package constant, Audit.lean)"); the history of the former admission is
`docs/2026-09-03_repin-fuel-notes.md`'s.

**S-3. The mirror's certification paragraph (§2, lines 29–84) is a
changelog inside one sentence.** Quoted fragments: "calls arc C1 made
them live, C2 added the two rules that write them" (35–36); "(the trust
rule of 2026-09-02; the 2026-09-03 standards-audit response), and since
the fuel-lane restatement (2026-09-03) no adequacy lane consumes them at
all" (67–69); "since calls arc C4" (110–111); "What is established, in
the auditor's words: '…' — now with the backward classification at every
fragment refusal outside the residual" (134–138; the quote is from the
2026-09-02 detailed audit, which predates completeness, so the sentence
describes the system by quoting a description that was superseded and
patching it with "now with"). Each of these is a "was … until …"
construction. Fix: state the present tense fact and cite the record:
e.g. "`Ctl` is live: `Step.call` pushes `(ctl.proc, ctx)`, `Step.ret` pops
it, every other rule threads it (`Step.ctl_cases`)"; "`dischargeStep`/
`outcomesU` are proof devices of Round.lean's classification; no export
or adequacy lane mentions or consumes them"; drop the auditor quote and
write the claim directly.

**S-4. Slice ids and dates as reader vocabulary.** Counts in the
document: `2026-` × 42, `K[0-9]` × 22, `C[1-4]` × 16, `F1` × 3,
`AR5|ar5` × 5, "former" × 5, "deleted" × 3, "since" × 8, "until" × 2.
Representative sentences a fresh reader cannot parse without the
register: line 296 "and, since calls arc C4, `fib_rec_certified_production`
… the first statement whose run makes the driver's PCALL and RETURN
rounds"; 328–331 "(the DECISIONS register's 'nine production statements'
count the generic pipeline theorem `prod_run_eqJ` as well — the same
eight plus `prod_run_eqJ`)"; 386–391 "The former package loop `driveU`
around the engine's `step_ctx`, and every statement over it, are deleted;
the former obstacle (the shipped driver's out-of-fuel arm was LemLib's
kernel-opaque `fuelExhaustedWith`) was lifted by the cerberus-lean fuel
arc (pin `f95ef8d9c`; the request: …)"; 407 "the package loop `driveU` is
deleted"; 410–411 "the ruled sequence (re-pin → calls arc C1–C4 →
fuel-lane restatement) is complete"; 456–457 "a field added at K3 on
orchestrator direction, recorded [AGENT] in DECISIONS"; 472–474 "The
former footprint-relative launch facts were retired as fields (K1 re-adds
`cur_meta_lo` …)"; 536–541 "(and, until the fuel-lane restatement of
2026-09-03, a `_total` twin over the package loop)"; 572–574 "(The total
`driveU` lane at the empty table, left at C4, was deleted with the loop in
the fuel-lane restatement, 2026-09-03.)"; 626–628 "formerly counted among
the 18 'client modules'"; 648–651 "The two the manifest slice carried
while `ar5-readout` was in flight (`DisposeExhibit`/`MallocListExhibit`,
the readout helpers since relocated into Adequacy/API) were dropped when
the slices combined"; 665–668 "the six stale seeds of the F1 renaming are
refreshed — …". Fix: for each, keep the present fact (if any) and move
the narrative to its record. The word `driveU` should not appear in a
description of a system that has no `driveU`.

**C-1. The negative total-correctness result is absent.** CLAIMS.md
C5 (`diverge_total_unprovable`, `dg_loop_exhausts`, DivergeExhibit.lean:
126, 172) is a headline claim — "the self-jump loop has NO total
derivation at any budget … false, not merely unprovable" — and the
external audit singles it out (§6, "The divergence exhibit addresses the
desired theorem"). ARCHITECTURE never mentions it (`grep -c iverg` = 1,
a false hit on "divergences"). A system section that presents a total
judgment must present the one theorem showing it is not vacuously
satisfiable. Fix (§3 or §6, three lines): the statement shape
(`diverge_total_unprovable : … (hwp : ⊢ blockSpecsT … ∗ wpt … k Ψ (dgBody
ra) …) : False`, via `dg_loop_exhausts`: the shipped loop exhausts at
every fuel on the self-jump).

### LOW

**C-2. Undefined house terms at first use.** "lane" (first at line 18
"(§4, §6)", then line 75 "BOTH adequacy lanes") — never defined; it means
"a chain of lemmas from a judgment to a driver-level fact". "profile"
(line 239 "a context profile (`procCtx`, the default file)", line 382
"the profile `spikeCtx`/`spikeCtl`") — never defined. "shipped" — used
~30 times, never defined (the generated driver as generated, unmodified).
"seeded" is defined only at line 376, after being needed at 302. "root of
trust" first at line 71, defined at 289. "collapse" first at line 166
with a parenthetical only. Fix: a five-line glossary at the head of §2
(mirror, round, lane, collapse, profile, seeded, shipped, root-of-trust
lane, production statement).

**C-3. Sentence length.** The §2 opening sentence runs lines 29–42 (14
lines, five nested parentheticals and em-dash asides); the §6
root-of-trust sentence runs lines 289–328 (40 lines, one sentence). A
professor cannot check a 40-line sentence; neither can a reader. Fix:
one statement per sentence; the `hfuel`/`hB` list as a table (statement
| file | input-dependent premises).

**C-4. `spikeCtl` and `procCtx` are used without a cite.** `spikeCtl` is
`Step.lean:3331` (`⟨[], none, default⟩`), `procCtx`/`prodCtx` are
ProdEntry/Adequacy; §6 (ii) uses both as if introduced.

**T-6 (precision, not error). "every export's axiom set is exactly
`propext`, `Classical.choice`, `Quot.sound`" (lines 267–269).** True of
the 376 pinned exports (Audit.lean `trioExports`), but Audit.lean itself
records public-named lemmas with SUB-trio cones that are deliberately
unpinned and bounded by the sweep (`fibRounds_closed` `[propext,
Quot.sound]`, `regionCost_pos`, `freshBase_*`, `runND_killed` with no
axioms; Audit.lean:352–353, 378–381, 521–523, 550–552). "Exactly" is the
pin's property; "at most" is every export's. Fix: "every pinned export's
axiom set is exactly the trio; every theorem of the package is bounded
by it (the sweep)".

**P-1. "in the auditor's words" (line 134) names no audit.** The quote is
from `docs/2026-09-02_cerberus-heaplang-detailed-audit.md` (grep
"verified forward connection"). An unattributed quotation in a normative
document is a provenance gap; combined with S-3 the fix is to delete the
quote.

**P-2. "the trust rule of 2026-09-02" (line 67) and "the fragment-closure
ruling" (line 108) carry uneven tags.** Line 108 correctly tags [USER
2026-09-02] (verified: DECISIONS line 816, "THE BOUNDARY IS FAIL-CLOSED
…", verbatim [USER]). Line 67's "trust rule of 2026-09-02" is the [USER]
referent rule (CLAUDE.md) but is untagged. Minor; tag it or point at
CLAUDE.md. No sentence in the document presents an [AGENT] decision as a
ruling (checked: la_pos [AGENT] at 457 — correct per DECISIONS 1142; the
parametric-inventory ON DEMAND decision [AGENT 2026-09-04] at 660 —
correct per DECISIONS 1916–1930; the acceptance goals [USER 2026-09-02]
at 395 — correct per DECISIONS 703; speedbumps [USER 2026-09-02] at 582 —
correct per DECISIONS 265).

---

## Verified true (load-bearing claims checked, and how)

- **§1/§4 referent.** Both lanes are over `drive_nonmemory_steps_aux2_lemFuel`
  from any driver state: `DriverSafeCtl` (Adequacy.lean:932–953) and
  `DriverDoneCtl` (ProdLoop.lean:456–475) quantify `∀ dst acc fl` with
  `dst.core_state0.thread_states = [(0, (none, ctlThread th₀ e ρ ctl))]`,
  `dst.core_file = M₀.file`, `LabeledProcs`, (`CtlTied` for the partial
  lane), conclusion `runOne (drive_nonmemory_steps_aux2_lemFuel fl fmapEmpty
  acc [0]) dst = …`; exhaustion arm `NDkilled CerbND.fuelExhaustedKill`;
  delivered thread at `⟨[], pfin, ℓfin⟩` ("the empty call stack"). The
  shipped loop is its `driverFuel` instance
  (`CerbND.drive_nonmemory_steps_aux2_wrapper_defeq`, generated
  CerbND.lean:396; `CerbFuel.driverFuel = 100000000`, CerbFuel.lean:71;
  `drive_wrapper_defeq : drive = drive_lemFuel CerbFuel.driverFuel := rfl`,
  CerbND.lean:467).
- **§2 certification statement** quoted at lines 44–47 is verbatim
  `Round.lean:1009–1014` (`hf : Frag e`, `hsz : esize e ≤ lemDefaultFuel`,
  `hs : Step …`, any `ctl ctl'`, cons-shaped env, no `SeqWF`).
  `step_iff_cerberusRound` (Round.lean:1597) takes `hstep : ∃ c', Step …`
  — "two-sided under the hypothesis that a mirror step exists" ✓.
  `cerberusRound_classify` (Round.lean:5475) takes `hwf : M.SeqWF`,
  `hκ : ctl.κ = []` ✓; its five arms `value_done`/`value_annot`/`step`/
  `refused`/`open_` (RoundClass, :1630–1657) ✓. `frag_round_complete`
  (:5368) at `hnv : toVal e = none` ✓. `ShippedRefusal` arms
  error/killed/fork/panic family (:213–355) and `OpenRound.eval_uncovered`/
  `run_surplus` (:356–400) match §2's descriptions, including "the
  classifier answers `.uncovered` at the FIRST such leaf and carries NO
  engine claim about the whole operand" (docstring :358–378).
  `complete_store … complete_memop_vals` exist (:2299–5350). `SeqWF` is
  `parent : M.parent = none` (Step.lean).
- **§2 "consumed by NO adequacy export".** `engine_step_matchU` appears in
  Adequacy.lean/DriverCollapse.lean/Potential.lean/WseqExhibit.lean only
  in comments (grep with context); `dischargeStep`/`outcomesU`/
  `stepDischarge_run` appear 0 times in Adequacy.lean, ProdLoop.lean,
  ProdEntry.lean (1 comment hit in DriverCollapse.lean). Both lanes'
  round: `loop_step_frag`/`loop_step_frag'`/`_same`/`_same'` exist with
  the stated premise shapes (DriverCollapse.lean:2118, 2024, 1981, 1377;
  the primed forms carry `hjmp : ∀ l params cont, lookupLabel … → ∃ p,
  th₀.current_proc_opt = some p ∧ LabeledAt …` — "the registration tie
  only at a jump" ✓).
- **§2 fragment declaration.** `BareHead` constructors: `val_pure`,
  `create`, `memop_vals`, `memop_op`, `alloc`, `alloc_op`, `call`
  (Soundness.lean:3981–4017) ✓. `Frag.case_value` carries `hbsz`
  (Soundness.lean, the `case_value` constructor) ✓; README line 642
  registers it ✓. `Ctl` = `⟨κ, proc, execLoc⟩` (Step.lean:371–374),
  `Config := CoreExpr × EnvStack × Ctl × Mem` (:400), `Step.call`/`ret`/
  `ret_annot` (:2047, 2079, 2096), `Step.ctl_cases` (:2250),
  `Step.env_depth` (:2534), `callRedex?` (:703) ✓.
- **§3 judgments.** `wps M p Ls Θ Ψ e ρ` is `fixpoint (wps.pre M p Ls Θ)`
  (Wps.lean:301–304); `wps.pre` dispatches `toVal` / `jumpRedex?` /
  `callRedex?` / step (contractivity proof :313–343 shows the four arms) ✓.
  `wpt` by well-founded recursion with `⌜1 + m ≤ k⌝` (Wpt.lean:167) and
  `hb : 1 + m + k' ≤ k` (:172) ✓. `wps_frame_labels` (:697),
  `blockSpecs_intro` (:3185), `procSpecs_intro` (:3277), `wps_call`
  (:417), `wps_call_root` (:472), `wps_sound_cps` (:3430), `wps_sound`
  (:3627), `wps_sound_empty` (:3647), `wp_ret`/`wp_ret_annot` (:3316,
  3357); `wpt_frame_labels` (Wpt.lean:557), `blockSpecsT_intro` (:2963),
  `procSpecsT_intro` (:3020), `wpt_call`/`_root` (:719, 751),
  `wpt_sound_cps` (:3161), `wpt_sound`/`_empty` (:3370, 3388) ✓.
  `AtomicStep` (Rules.lean:194), `wp_of_atomic` (:210, mask-generic `E`),
  the eight atomic specs at :264–1502 incl. `regionLoadAt_atomic`/
  `regionStoreAt_atomic` (:767, :863) ✓. "no raw-WP sequencing rule …
  false at a populated label map" — Rules.lean header line 37 ✓.
- **§4 fuel arms.** F1 record §3 (docs/2026-09-03_f1-notes.md:279–300)
  measured fuel 0 / 1 / ≥2 as stated; `loop_step_done` (DriverCollapse.
  lean:392), `loop_step_done_exhaust` (:2257), `loop_zero_exhausts`
  pinned; generated `drive_nonmemory_steps_aux2_lemFuel` `| 0 => … NDkilled
  (Error0 CerbFuel.fuelExhaustedLoc CerbFuel.fuelExhaustedMsg)`
  (Driver.lean:344–345) ✓. `new_drive_core_threads` calls the WRAPPER
  `drive_nonmemory_steps_aux2` (Driver.lean:352–355) — so `drive_lemFuel`'s
  fuel bounds the outer rounds only ✓ (A2). `wpt_driver_cps` conclusion
  `DriverDoneCtl … (k + kc)` with continuation `(k' + kc)` and
  `wpt_driver_done_procs` at `⟨[], some p, ℓ⟩` (ProdLoop.lean:609–627,
  799–815) ✓; `k + 2 ≤ fl` ✓.
- **§5 projection.** `project_triple_pure` (Adequacy.lean:1605–1625) →
  `MemTriple` (:1518–1523: `∀ R, P ##ₘ R → ∀ σ, Sat … (union P R) → ∀ th₀,
  … → DriverSafeCtl … (fun v σ' => post R v σ')`) ✓; `hpost` names `CohG`,
  `metaInterp`, `byteInterp` (the documented exception) ✓; all eleven
  `*_consequence` lemmas exist (:1909–2007) ✓; `DeadAt` public (:1900) ✓;
  AR5-readout record §3 shows the before-state hits and the boundary
  gate line "BOUNDARY: 17 modules checked, 1 internals mention(s)" ✓.
- **§6 the eight closed statements.** All eight theorems exist at the
  cited files; execution function `CerbND.runND (_root_.drive fmapEmpty
  false (prodFile…/prodFileWith…) args) ((initial_driver_state sup … fs).1)`
  in each ✓; `hfuel` texts match exactly (ProdLoopExhibit.lean:77
  `2 * n.toNat + 6`, :623 `6 * n.toNat + 8`; RegionLoopExhibit.lean:636
  `7 * n.toNat + 5`, :635 `hB`; MallocListExhibit.lean:1655–1656 `hB :
  n.toNat * (15 + max al.toNat 1) ≤ 281474976710647`, `25 * n.toNat + 9`;
  FibRecExhibit.lean:866 `fibRounds n.toNat + 4`); `fibRounds 0 = fibRounds
  1 = 3`, `fibRounds (n+2) = fibRounds (n+1) + fibRounds n + 9`,
  `fibRounds_closed : fibRounds n + 9 = 12 * fibSpec (n+1)`
  (FibRecExhibit.lean:450–470) ✓; `ml_budget_bridge` exists (:1626) ✓;
  `prodFile e = prodFileWith [] e := rfl` (ProdEntry.lean:549) ✓;
  `prod_run_eqJ_procs` carries `hfl : k + 2 ≤ CerbFuel.driverFuel` (:716–
  735) ✓; `prod_run_safe_procs` (:768–787) is exactly the quoted shape
  (`∀ fuel`, singleton list, `Killed dst' fuelExhaustedKill ∨ Active dres
  ∧ ψ …`) ✓; `fib_rec_certified` (FibRecExhibit.lean:814) takes `(hn : 0
  ≤ n) … (fuel : Nat)`, no budget bound ✓. `prodCtl = ⟨[], some mainSym,
  ELoc_normal …⟩` (ProdEntry.lean:567) and `prodCtx … currentLoc := other
  "Driver.drive"` ✓; `spikeCtl = ⟨[], none, default⟩` (Step.lean:3331) ✓.
  Generated Driver.lean:528–531 is the "setting the arena of thread 0 to
  the body of the main function" block ✓ (cite :530 acceptable).
- **§6 admissions.** `grep -rln '(sorry' generated/*.lean` at the pin:
  empty ✓. Audit.lean: trio `[propext, Classical.choice, Quot.sound]`
  (:156–158), "There is no declared boundary axiom" (:45) ✓; DECISIONS
  gate quote "376 trio-exact" (line 1938) matches KOI E ✓.
- **§7 Goal 3.** `MemWF` has exactly ten fields (Heap.lean `structure
  MemWF`: live_lt, dead_lt, live_dead, disj, cursor_lo, size_nonneg, la_wf,
  la_pos, dyn_lo, dyn_disj; the `refine ⟨?_,…⟩` at +56 has ten holes) ✓;
  `CohG.wf : get? mk 0 ≠ none → MemWF σ` ("under cursor presence") and
  `CohG.cur_meta_lo` ✓; `LaunchCoh.wf`, `.budget : B ≤ headroom
  σ.lastAddress` (Adequacy.lean:422–432) ✓; `prodMem₀_memWF` (ProdEntry.
  lean:243), `create_fresh_global` (Heap.lean:1801), `MemWF.loadM/storeM/
  allocateObject/allocateRegion/killM` (:1817–2010) ✓; `la_pos` provenance
  [AGENT] per DECISIONS 1142 ✓.
- **§7 K5 laws.** `typedRegionView` (Heap.lean:3481), `_iff`, `_regionView`,
  `_split`, `_join`, `regionOwn_carve`/`_uncarve` (:3487–3653),
  `regionOwn_ne`/`regionOwn_deadRegion_ne`/`metaOwn_ne` (:4057–4088);
  `wps_load_region_at`/`wps_store_region_at`/`wps_load_regionOwn_at`/
  `wps_store_regionOwn_at` (Wps.lean:2891–2989), `wpt_load_region_at`/
  `wpt_store_region_at` (Wpt.lean:2521, 2546) ✓. `isAtomicMemberAccess`
  is checked in `loadM`/`storeM` (generated CerbMem.lean:2003, 2067) ✓
  (the cite is stale, T-3).
- **§7 instruments.** Manifest tail: "23 constructors, 50 variant rows
  (27 RULE, 3 RULE-TOTAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 15 NO-RULE, 5
  OUT-OF-SCOPE), 0 red, 16 consumer modules" ✓; the three
  RULE-TOTAL-UNDEMONSTRATED rows are `wpt_load`, `wpt_case_value`,
  `wpt_wseq` ✓; the five OUT-OF-SCOPE rows are as enumerated ✓; "WHAT
  GREEN ESTABLISHES / DOES NOT ESTABLISH" matches the manifest header
  verbatim in substance ✓. Ten classes in the TSV vocabulary = the ten
  listed ✓; 14 `positive-client` + 2 `declared-smoke` = 16 ✓; boundary
  subjects `positive-client`, `declared-smoke`, `example-support` = 17
  modules ✓ (gate line); the grep pattern in `boundary_check.sh` line 44
  names exactly the internals ARCHITECTURE lists ✓; ONE ALLOWLISTED
  entry (`Exhibit`/`progA_wpt`) in the TSV and the gate tail ✓;
  18 → 16 consumer change (Prod wrappers + DivergeExhibit out,
  ReadinessSmoke in; ar5-manifest notes :186–192) — ARCHITECTURE's
  "the two production wrappers and the negative test … are not consumers"
  is true (it omits ReadinessSmoke joining; not an error). CLAIMS.md: 11
  rows, generator checks names ("86 declaration names checked") ✓.
  Parametric inventory ON DEMAND is an [AGENT] decision (DECISIONS
  1916–1930) ✓.
- **External-audit answers (AR5).** Finding 1's remedy is reflected
  faithfully (variant rows, the five classes, the withdrawal of "0 red
  = coverage", "reviewed reading, not a theorem"); Finding 2's two halves
  (readout lemmas moved to Adequacy/API — `deadObj_consequence`,
  `deadRegion_consequence`, `bigSepL_consequence` pinned, Audit.lean:568–
  571; one module classification; fail-closed inventory; boundary check)
  are reflected accurately; the audit's "Note" (two bridges) is §2's
  documented design, KOI B12 ✓. Finding 3 is NOT reflected (D-3).
- **Record paths.** Every `docs/…md` and `../docs/…md` path cited in
  ARCHITECTURE exists in the tree (scripted check, zero missing).
- **KOI disclosure cross-check (class A/B).** On this surface: A1
  partially (driverFuel yes, lemDefaultFuel/pot no — D-1); A2 yes (lines
  370–376); B1 yes (seeded exhibits, lines 376–380; tree rotation's
  missing statement is NOT mentioned — belongs on README's table, minor);
  B2 yes (lines 380–386); B3 yes (376–380); B4 partly (extern yes,
  tagDefs no — D-5); B5 no (D-4); B6 no (slack in `fib_rec`'s bound — the
  document says "the in-budget bound", does not claim tightness; acceptable);
  B7 yes (Goal 2); B8 yes (§7 still-open list + §6 concurrency); B9 yes;
  B11 no (D-3); B12 yes (§2); B13 yes; B14 yes (with T-1's list defect).

## Not checked

- No Lean was elaborated; no `#print axioms`; the 376-pin count and the
  sweep counts are taken from the recorded gate tails, not re-measured.
- Proof bodies were not read (only statements); in particular I did not
  verify that `drive_safe_aux`'s induction is as described (line 203–209)
  beyond the existence of `ControlOk` (Adequacy.lean:800) and
  `MachineCtx.FragProcs` (:767).
- The eight-binop count of the mirror evaluator, the `evalClass` leaf
  shapes, and the Core_reduction.lean:484 "col 18133" cite were not
  verified.
- The README and WALKTHROUGH were consulted for cross-references only
  (section names exist: "The claim", "The trust story", "What you are
  asked to take on faith", "Registered divergences and limitations",
  WALKTHROUGH §1.1/§7); their content was not reviewed.
- Whether `Examples/MirrorCoverage`'s `engine_step_matchU` instances are
  pinned exports was not checked (irrelevant to the "no adequacy lane"
  claim, which holds).
