# ARCHITECTURE.md — fresh full review (review 5, of the second pass)

**VERDICT: B+ — FAIL** (near pass; every finding is a local edit, none is
a gap in what is proved; the two that carry the grade sit in §3, the
trust section, which must be exact).

Reviewer: fresh (reviewer 5; no contact with earlier versions, reviewer
4's report or the rewrite notes until the cold read and the source
verification were complete). Standard: grumpy PL professor, "would I
sign this as the paper's system section" — A passes, B or below fails.
Tree: `worktrees/review-arch-5`, detached at `dd7b852` ("H1 range audit
(PASS WITH FIXES, A−) landed …"). Method: source reading only — no
`lake`/`lean` invocation; `sed -n`/`grep` over `CerberusHeapLang/**/*.lean`,
`scripts/*`, `../scripts/*`, the generated manifest, the pinned
workspace of the primary checkout (`../.cerberus-ws`, `git log -1` =
`f95ef8d9c`, read-only), LemLib at `.lake/packages/LemLib`,
`docs/DECISIONS.md`, `docs/KNOWN-OPEN-ITEMS.md` (KOI), `docs/CLAIMS.md`,
`docs/CAPABILITY_MANIFEST.md`, `README.md`, `docs/WALKTHROUGH.md`, the
archive record. Reading order: ARCHITECTURE.md cold; then the sources
and context files (≈ 130 cites checked, listed below); then, last,
review 4 and the rewrite notes' "Second pass".

Summary. The document is a description of the system as it is, in the
right order (object → proved → trusted → how to read → instruments →
exclusions → ledger), and it is findable: a reader who knows Iris can
locate every theorem named and the sources say what the text says. Every
count is right (23 constructors; 8 mirrored binops; 21/26 mask sites; 8
`MachineCtx` fields; 10 `MemWF` fields; 4 + 4 + 8 `ShippedRefusal`/
`OpenRound`/`RoundClass` arms as described; 3 + 11 + 1 collapse
consumers exactly; 9 statements with every premise as printed; 402 pins;
50/30/0/0/15/5 rows, 18 consumers, 19 boundary modules, 11 claim rows /
90 names; the 15 NO-RULE and 5 OUT-OF-SCOPE variants one-for-one). Every
`[USER]`/`[AGENT]` tag resolves to its register entry with the date
right and the quotations verbatim (including both ellipses). The
shop-window is clean: all `2026-` tokens sit in tags or record paths;
no slice vocabulary as narrative. It fails the A bar on two sentences
in §3: an axiom-set attribution that the cited `Audit.lean` comments
contradict (T-1), and a trust-base paragraph that names `axiom` and
`sorry` but not the pinned engine's `panic!` arms — the kernel reads
them as `Inhabited` defaults, the register lists this as class A (KOI
A5), and the register's rule is that class A is disclosed on this
surface (D-1). Behind those: three cites moved by the H-1 commit that
landed after the second pass (T-2), and a handful of house terms used
before or without definition (C-3).

## Findings, ranked by severity

### MEDIUM

**T-1. The sub-trio parenthetical misattributes axiom sets, against its
own cite.** Lines 430–434: "A few public-named lemmas have SUB-trio cones
and are deliberately unpinned, bounded by the sweep: `fibRounds_closed`
(`[propext, Quot.sound]`); `regionCost_pos`, `freshBase_*`,
`runND_killed` (no axioms; `:354`–`:356`, `:380`–`:384`, `:523`–`:525`,
`:552`–`:553`)." The cited comments say otherwise: `Audit.lean:380`–`:384`
"NOT pinned (SUB-trio cones `[propext, Quot.sound]`, measured by `#print
axioms` …): the pure bounds `freshBase_ne_zero_of_cost'`/
`headroom_freshBase'`/`freshBase_pos_nat`/`regionCost_pos` (`regionCost_eq`
has no axioms at all)"; `:354`–`:356` likewise `[propext, Quot.sound]`
for `freshBase_ne_zero_of_cost`/`headroom_freshBase`; only `runND_killed`
(`:552`) "has NO axioms". The parenthetical "(no axioms; …)" therefore
covers two names whose cones are `[propext, Quot.sound]`; and the list
omits `BareHead.decomp_call_root` (`[propext]`, `:523`) and `regionCost_eq`
(none, `:384`), which the same cited lines name. In the trust section,
"exactly the trio is the pinned exports' property" must be followed by
an exact statement of what is not pinned and why.
Fix: "… bounded by the sweep: `fibRounds_closed`, `regionCost_pos` and
the `freshBase_*` bounds (`[propext, Quot.sound]`; `:354`–`:356`,
`:380`–`:384`, `:523`–`:525`), `BareHead.decomp_call_root` (`[propext]`,
`:523`), `regionCost_eq` and `runND_killed` (no axioms; `:384`,
`:552`–`:553`)." (Cones as the comments record them; not re-measured —
see "Not checked".)

**D-1. The trust base does not disclose the engine's `panic!` arms, and
KOI A5 (class A) is absent from the document.** Lines 418–421: "The
pinned tree declares no `axiom` and contains no `sorry`: `grep -rn
'(sorry'` over the primed `generated/*.lean` is empty and the build log
has no `declaration uses sorry`." Both facts verified (`grep -rn
'(sorry'` = 0; `^axiom` = 0). But the pinned `generated/CerbMem.lean`
carries ~30 `panic!` arms mirroring OCaml `assert false`/`Not_found`
(`:239`–`:240` `combine_prov`, `:352` `offsetsof`, `:380`–`:468`
`sizeofCtype`/`alignofCtype`, `:553`, `:928`/`:1057` "unknown function
pointer", `:989`–`:1105` `reconstructValue`, `:1169` `typeofMval`), and
the kernel reads `panic!` in pure code as the `Inhabited` default, not
as an abort. KOI A5 records exactly this hazard for `killM` ("read by
the kernel as the `Inhabited` default … Re-check `MemWF.killM` at that
re-pin"), and KOI's header rule is that class A/B items are disclosed on
the surfaces named — this is the trust surface, and no surface (README,
WALKTHROUGH, ARCHITECTURE: `grep -in 'panic!\|Inhabited'` = 0 in all
three) says it. The reader of §3 is told "trusted as a policy decision,
sampled by differential validation" and is entitled to know that the
trusted definitions contain arms whose Lean meaning differs from their
OCaml meaning, and that the package's rules avoid them by premise
(`create_atomic`'s `hsz : 0 < sizeofCtype`, the manifest's NO-RULE
`create` rows) rather than by theorem. Note also that §2.2's "the
`panic` family: the engine's own `failwithI`" (line 231) is LemLib's
opaque `failwithI`, a different mechanism from `panic!`; without a
sentence separating them a reader will conflate the two.
Fix (§3, after the `sorry` sentence, three lines): "The generated tree
does contain `panic!` arms (OCaml `assert false`/`Not_found` mirrors,
e.g. `CerbMem.sizeofCtype` at `Void`), which the kernel reads as the
type's `Inhabited` default, not as an abort; no export's premises reach
one (the `create` rules exclude the offending types by premise —
manifest NO-RULE rows), and the one arm that matters for kills is KOI
A5. `failwithI` (§2.2) is LemLib's opaque failure, a distinct
mechanism." And list KOI A5 in §6 under the fuel/engine items.

### LOW

**T-2. Three `EvenOddExhibit.lean` cites are off by one at this
revision.** The H-1 commit (`dd7b852`, HEAD) inserted one line at
`EvenOddExhibit.lean:307` (hunk `@@ -307,11 +307,12 @@`), after the
second pass was written. Line 194 "`EvenOddExhibit.lean:501`" → the
`wps_sound` call is at `:502`; line 387–388 "`even_odd_certified`
(`EvenOddExhibit.lean:673`)" → `:674` (`:673` is the docstring's last
line); table line 368 "`EvenOddExhibit.lean:721`" → `:722` (`:721` is
the docstring's last line). The document's first paragraph promises
"Every claim is about the tree at this revision". Fix: the three
numbers; and a note to the orchestrator that a `.lean`-touching commit
landing over a cite-bearing front document must re-check the cites
into the touched file (the H-1 record could have carried it).

**D-2. KOI A6 (the pin is not the mainline) is absent.** §3 names the
pin (`f95ef8d9c`) as the semantics of Core but not that cerberus-lean's
mainline is ≥ 34 commits ahead with a `killM` re-mirroring that changes
one exported text (`killM_killed_inv`) at the next re-pin (KOI A6). One
clause after "(iii) The pinned cerberus-lean semantics (`f95ef8d9c`)":
"— a pin, not the mainline; the queued re-pin and its one exported-text
change are KOI A6." Class A, so on this surface by the register's rule;
low because it is about the next tree, not this one.

**C-1. The workspace path lacks its `../`.** Line 6: "the pinned
semantics workspace `.cerberus-ws/lean_frontend/`". From the package
directory that path does not exist; the workspace is at the repository
root (`../.cerberus-ws/lean_frontend/`), and the same sentence writes
`../scripts/semantics-pin.env` in root-relative form (review 4's T-7b
fixed the script path but not the workspace path). Fix: `../.cerberus-ws/`.
Every generated-`Driver.lean`/`CerbMem.lean`/`CerbND.lean`/`CerbFuel.lean`
cite in the document is then reachable.

**C-2. Two size measures, never related.** §2.2 states the certification
and completeness at `esize e ≤ lemDefaultFuel` (lines 215, 241); §4 calls
`pot e ≤ lemDefaultFuel` "THE STATIC FUEL PREMISE" (line 538) with `pot`
"a step-monotone size potential". A reader meets two bounds on the same
constant and is not told how they relate. `Frag.esize_le_pot` exists
(API.lean:85; used at `Adequacy.lean:1208`, `ProdLoop.lean:237`) and is
the one-clause bridge. Fix (§4, after "size potential on terms"): "it
dominates the round-level measure `esize` of §2.2 (`Frag.esize_le_pot`),
so the adequacy premise discharges the certification's."

**C-3. House terms used before or without definition.** (a) *pinned* /
*unpinned* — first at line 196 ("the pinned export `cs_twp_readout`")
and 255 ("unpinned, bounded by the sweep"), defined only by use at §3
line 424–425; (b) *the sweep* — line 255, defined at 426–428; (c) *tie(s)*
— lines 283 ("Its ties are `LabeledProcs` … and `CtlTied`"), 301 ("the
file tie and the whole-file registration tie"), 512 ("the registration
ties"), never defined (they are the equalities/predicates on `dst` in
`DriverSafeCtl`/`DriverDoneCtl`, `Adequacy.lean:935`–`:940`); (d)
*readout* — line 192 ("the Iris-level readouts") and throughout; (e)
*the drain iteration* — line 293; (f) *wakeup-free* — line 207; (g) *the
certification equation* — line 87; the certification (§2.2, line 209) is
the implication `Step → CerberusRound`, not an equation — say "the
certification (§2.2)". Fix: glossary lines for *pinned*, *the sweep*,
*tie*, *readout*; one clause each for (e) and (f) or drop the words;
(g) as above.

**S-1. Two shop-window residues.** (a) Line 447: "No export carries an
interim label." An "interim label" is undefined and exists only relative
to a past state of the tree (KOI B10 is the register's home for it); as
written it is history by negation. Fix: delete, or "No export is
labelled provisional (the referent rule, CLAUDE.md; KOI B10)." (b) Line
643: "[AGENT 2026-09-04] (DECISIONS AR5-manifest entry)" cites a register
entry by slice handle; every other DECISIONS cite in the document quotes
the entry's title. Fix: "(DECISIONS "AR5-MANIFEST LANDED and COMBINED")".

**S-2. An ambiguous record cite.** Lines 426 and 635 cite
"`docs/2026-09-04_h1-notes.md` §8" for the 402 pins and the BOUNDARY
line. That record has two sections numbered "## 8" (`:254`, the gate at
`4acb10d`; `:746`, the gate at `29d9195`); the figures cited are in the
second (`:752`, `:781`). Fix: "§8 (the gate at `29d9195`)" — or the
orchestrator renumbers the record.

**C-4. Length and duplication (judgment on the author's arithmetic).**
731 lines is acceptable for this document: every section is load-bearing
(the §2.5 tables and the §4 premise list are the parts a reader most
needs, and the fifteen variants and nine premises are disclosures), and
the author's case against ~630 is sound. What is removable (~15–20
lines): (i) §5 manifest bullet, lines 606–609 "In short: the table covers
… every claim-matrix name exists" — the sentence before it says the
generated header "states exactly" what green establishes; the paraphrase
is a second copy that can drift (keep the "Not established" sentence);
(ii) §6's first bullet (653–655) repeats §1's boundary sentence verbatim
in substance — one line with the KOI number suffices; (iii) the header's
"The README carries … the register of limitations" (lines 7–9) contradicts
§6 being one — say "§6 lists the limitations with their register numbers;
README's table gives each its discharge or mover", which also tells the
reader why the two overlap (they do, on ~12 rows; by design). Sentences:
one prose sentence runs five wrapped lines (430–434, the T-1 sentence —
splitting it is part of the fix); the block-quote lead-in (566–569) and
the §2.1 type-blindness sentence (160–163) run four. The reading order is
followed; §7's ledger is now the right size.

### Provenance (P-)

No finding. Every tag checked resolves: TRUST ARCHITECTURE [USER
2026-08-29] `DECISIONS:86`/CLAUDE.md:10; SPEEDBUMPS [USER 2026-09-02]
`:265`; THE DEMO'S ACCEPTANCE GOALS [USER 2026-09-02] `:703` (the inner
quotation verbatim); THE BOUNDARY IS FAIL-CLOSED [USER 2026-09-02] `:816`;
KILL/FREE K3 LANDED [AGENT 2026-09-03] `:1135` (`la_pos` at `:1142`); F1
RANGE AUDIT [AGENT 2026-09-03] `:1715` with the [USER 2026-09-03] quotation
at `:1753`–`:1756` verbatim; FUEL IS A DEFECT [USER 2026-09-03] `:1787`
re-quoting with the ellipsis at `:1823`–`:1825`; THE DEMO'S SCOPE,
RESTATED [USER 2026-09-04] `:2130`–`:2133` (the document's ellipsis
elides "just because it's a nice stable interface but it shakes out many
of the theory difficulties." — correct use); PARAMETRIC INTERFACES NOT
ADOPTED [USER 2026-09-02] `:372`; AR5-MANIFEST [AGENT 2026-09-04] `:1916`
("Inventory FAIL-CLOSED … on demand"); the referent rule [USER 2026-09-02]
CLAUDE.md:94. Derived tallies in the document are labelled as counts and
are right.

## Verified true (the cites checked, and how)

Method as in the header. ≈ 130 cites; the load-bearing ones:

- **Header/glossary.** `../scripts/semantics-pin.env` has
  `CERBERUS_LEAN_COMMIT="f95ef8d9c…"` (`:59`) and `git -C ../.cerberus-ws
  log -1` = `f95ef8d9c` ✓; `drive_nonmemory_steps_aux2_lemFuel` generated
  `Driver.lean:346` ✓; `Frag` `Soundness.lean:4149` ✓; `Step`
  `Step.lean:1456` ✓; `spikeCtx`/`spikeCtl`/`procCtx`/`procCtl`
  `:3355`/`:3331`/`:3363`/`:3336` ✓; `prodCtx`/`prodCtl`
  `ProdEntry.lean:580`/`:567` ✓; the round names `reduction: PCALL`/
  `RETURN`/`PROGRAM-DONE` each once in generated `Core_reduction.lean` ✓;
  the trio `Audit.lean:159`–`:160` ✓.
- **§1.** 23 constructors `:4150`–`:4314` (listed by grep, counted) ✓;
  `PePure` `:2007` = val/sym/op/arrayShift, `isMirroredOp` `:2001` = the
  eight ops Add/Sub/Mul/Eq/Lt/Le/Gt/Ge ✓; the `_op` forms exactly
  `store_op`/`load_op`/`kill_op`/`alloc_op` (+ `memop_op`) ✓; `BareHead`
  `:3981` ✓; annotation-free header `:4129`–`:4147` ✓; `Config` `:400`,
  `Ctl` `:371`–`:374` (κ, proc, execLoc), `MachineCtx` `:405`–`:413` with
  exactly the eight fields named ✓; `Step.call` `:2047`, `callRedex?`
  `:703`, `Step.ret`/`ret_annot` `:2079`/`:2096`, `Step.ctl_cases` `:2250`
  ✓; `Lang.lean:58` `instance : Language …` ✓; `wps` `Wps.lean:301`,
  `wps.pre` `:217`, `LabelSpec` `:113`, `ProcSpec` `:129`; `wpt`
  `Wpt.lean:200`, `⌜1 + m ≤ k⌝` `:167`, `1 + m + k' ≤ k` `:172` ✓; `⊤`
  occurrences 21/26 (`grep -o | wc -l`) ✓; `AtomicStep` `:194`,
  `wp_of_atomic` `:210`, `wp_store` `:1584`, `wp_load` `:1614`,
  `spike_wp_wand` `:1676` all `{E : CoPset}`/∀-mask ✓.
- **§2.1.** All ten atomic specifications at the cited lines ✓;
  `wps_of_atomic`/`wpt_of_atomic` `Wps.lean:345`/`Wpt.lean:664` ✓;
  `isAtomicMemberAccess` generated `CerbMem.lean:1949`, used at `:2003`
  (`loadM`) and `:2067` (`storeM`) ✓; the eleven `Heap.lean` bundle cites
  (`:2749`, `:2714`, `:2734`, `:3683`, `:3319`, `:3310`, `:3481`, `:3783`,
  `:3793`, `:2464`, `:2475`) ✓; structural rules `Wps.lean:701/3195/3287/
  417/473`, `Wpt.lean:563/2975/3032/726/758` ✓; `Rules.lean:35`–`:44` says
  there is NO raw-WP sequencing rule and why (a jump discards the
  context) ✓; collapses `Wps.lean:3440/3326/3367/3637/3657`,
  `Wpt.lean:3173/3382/3400` ✓; the consumer table: comment-stripped grep
  over every package module finds exactly 3 `wps_sound` (CallSmoke,
  FibRec, EvenOdd), 11 `wps_sound_empty` (Exhibit ×2, Struct ×2, Case,
  Loop, Fib, Array, Wseq, ListRev, TwoLabel), 1 `wpt_sound` (CallSmoke
  `:461` inside `cs_twp_readout` `:455`); every cited line contains the
  token except EvenOdd `:501` → `:502` (T-2) ✓; `load_atomic_readonly`
  exists `Rules.lean:460` ✓.
- **§2.2.** `CerberusRound` `Round.lean:195`, `loop_step` `:965` ✓;
  `engine_step_matchU` `:1010`–`:1015` matches the quoted block
  character for character ✓; `step_iff_cerberusRound` `:1598` ✓;
  `frag_round_complete` `:5369` (premises `hf`, `hsz : esize e ≤
  lemDefaultFuel`, `hnv`) ✓; `ShippedRefusal` `:214` with arms error/
  killed/fork/panic/panic_env/panic_memop/error_next/panic_noproc — the
  document's five-way description (error, killed, fork, "the `panic`
  family", error_next) is faithful ✓; `OpenRound` `:357` two arms
  `eval_uncovered`/`run_surplus`, mover text at `:377` ✓; `complete_store`
  `:2300` … `complete_ret` `:5351` ✓; `cerberusRound_classify` `:5476`
  premises `hwf : M.SeqWF`, `hκ : ctl.κ = []` ✓; `RoundClass` `:1631`
  five arms exactly as named ✓; "WHAT CONSUMES WHAT" `:141`–`:153` says
  what the document says ✓; `loop_step_frag`/`'` `DriverCollapse.lean:
  2118`/`:2024` ✓; `dischargeStep`/`outcomesU` `Soundness.lean:154`/`:262`,
  referenced only from Round/DriverCollapse/API/Audit/Soundness ✓; the
  round-certification names occur outside `Round.lean` in code only in
  `Examples/MirrorCoverage.lean` (an example, not an adequacy export) ✓.
- **§2.3.** `dgBody` `:69`; `dg_loop_exhausts` `:126` (∀ fl dst acc →
  `NDkilled CerbND.fuelExhaustedKill`); `diverge_total_unprovable` `:172`
  over `σ₀ m₀ hcoh Ls Ψ k hwp` → `False` ✓.
- **§2.4.** `drive_nonmemory_steps_aux2_wrapper_defeq` generated
  `CerbND.lean:396`–`:397` `rfl`; `drive_wrapper_defeq` `:467` `rfl` ✓;
  `spike_step_adequacy`/`_alloc` `:568`/`:667`; `engine_adequacy`/`_alloc`
  `:1278`/`:1344`; `DriverSafeCtl` `:932` read in full (∀ dst acc fl; the
  six ties; exhaustion ∨ `NDactive … Step_done2 v`) ✓; `LabeledProcs`/
  `CtlTied` `:2178`/`:2205`; `drive_safe_aux` `:1079` private; `ControlOk`
  `:800`; `FragProcs` `:767`; `loop_zero_exhausts`/`loop_step_done_exhaust`/
  `loop_step_done` `:2246`/`:2257`/`:392` ✓; `wpt_driver_cps` `ProdLoop.
  lean:609`; `DriverDoneCtl` `:456` read in full (`k + 2 ≤ fl` →
  delivery) ✓; `driverDoneCtl_step` `:537`; `wpt_driver_done_procs` `:799`;
  `DriverDoneAt`/`wpt_driver_aux`/`wpt_driver_done`/`_alloc` `:56/:175/
  :290/:358` ✓; `project_triple_pure` `:1605`, `MemTriple` `:1518`,
  `project_triple_pure_alloc` `:1743`, `MemTriple_alloc` `:1669`,
  `LaunchCoh` `:422`–`:431` (coh, `wf : MemWF σ`, `budget : B ≤ headroom
  σ.lastAddress`) ✓; the eleven `*_consequence` lemmas `:1909`
  (`pure_`) … `:2007` (`cells_`) ✓; `CellMap` `:1407`, `Sat` `:1415`,
  `DeadAt` `:1900` ✓; `prodFile` `:125`, `prodFileWith` `:544`,
  `prodFile_eq_with … := rfl` `:549`, `prod_run_eqJ_procs` `:716`,
  `prod_run_eqJ` `:402`, `prod_run_safe_procs` `:768`, `prodMem₀` `:212`,
  `prodMem₀_memWF` `:243` ✓; `Driver.lean:355`–`:358`
  (`new_drive_core_threads` calling `drive_nonmemory_steps_aux2`) ✓;
  `Driver.lean:530` is one 9,013-character line containing both
  `current_proc_opt := (some main_sym)` and the "CONCURRENCY IS BROKEN"
  kill ✓ (a cite to a 9 KB line is technically right and practically
  unhelpful; not counted).
- **§2.5.** All nine signatures read in full at the cited lines
  (`ProdExhibit.lean:264`; `ProdLoopExhibit.lean:75`, `:620`, `:1435`;
  `DisposeExhibit.lean:1479`; `RegionLoopExhibit.lean:633`;
  `MallocListExhibit.lean:1654`; `FibRecExhibit.lean:865`;
  `EvenOddExhibit.lean:722` — T-2): every premise in the premise table
  is present and none is missing (`hn`; `hfuel` `2n+6`, `6n+8`, `7n+5`,
  `25n+9`, `3n+6`, `fibRounds n.toNat + 4`; `hcost`; both `hB` as
  printed); no termination hypothesis ✓. The package-definitions table
  re-derived from the nine texts: exhibitA `sevenVal`/`sevenBytes`/`intTy`
  (`Layout.lean:57`/`:65`/`:50`) + `CellCoh`; fib `ivVal` (`LoopExhibit.
  lean:63`) + `fibSpec` (`FibExhibit.lean:60`); counter `intUndefBytes`
  (`AllocExhibit.lean:88`) + `sevenBytes`/`intTy`/`CellCoh`; list-reverse
  `ptrVal` (`ListRevExhibit.lean:466`), `SeedChain` (`:1210`), `CellMap`,
  `Sat`; dispose/region/malloc engine fields only (`deadAllocations`,
  `allocations.get?`, `dres_*`); region premises `regionCost`/`headroom`/
  `prodMem₀` (`Heap.lean:2322`/`:2267`, `ProdEntry.lean:212`); malloc's
  `hB` in engine vocabulary, `ml_budget_bridge` `:1626`; fib-rec `ivVal`/
  `fibSpec`, premise `fibRounds` (`:450`: 3, 3, `+9`; `fibRounds_closed`
  `:470` `fibRounds n + 9 = 12 * fibSpec (n+1)`); even/odd `ivVal (1 - n
  % 2)` ✓ — every cell exact. All ten names (nine + `cs_twp_readout`) in
  `trioExports` ✓. `fib_rec_certified` `:814` and `even_odd_certified`
  `:674` take `(fuel : Nat)` ✓. `CerbFuel.driverFuel = 100000000`
  generated `CerbFuel.lean:71` ✓.
- **§2.6.** `MemWF` `Heap.lean:1583`, exactly ten fields in the order
  named ✓; `CohG` `:2632`; `create_fresh_global` `:1801`; `MemWF.loadM/
  storeM/allocateObject/allocateRegion/killM` `:1817/:1877/:1898/:1937/
  :2010` ✓.
- **§3.** Pin loop `Audit.lean:615`–`:616`, sweep `:617`–`:636`, banned
  sweep `:637`–`:653` ✓; "There is no declared boundary axiom" `:45`
  verbatim ✓; 402 pins: `h1-notes.md:752` gate line ("export pins: 402
  trio-exact") and 402 distinct ``` ``CerberusHeapLang.* ``` tokens in
  `Audit.lean` (grep) ✓; `(sorry` grep over generated = 0, `^axiom` = 0
  ✓ (the `sorry` mentions in `CerbStepInstances.lean`/`CerbFunMapInstances.
  lean` are comments describing history); `LemLib.lean:56`
  `lemDefaultFuel = 1000000` ✓; gate 1 `test_unit.sh:28` ✓.
- **§4.** `fib_certified_production` (`ProdLoopExhibit.lean:75`–`:89`) and
  `counter_loop_certified` (`LoopExhibit.lean:427`–`:439`) quoted
  verbatim (diffed by eye, line by line) ✓; section variables
  `LoopExhibit.lean:213`–`:214` ✓; `Coh`/`CellCoh` `Heap.lean:386`/`:358`
  ✓; premises of `engine_adequacy` `:1278`–`:1296`, `project_triple_pure`
  `:1605`–`:1613`, `wpt_driver_cps` `:609`–`:620`, `wpt_driver_done_procs`
  `:799`–`:809` as listed (`hcl` at `:1296`, `hpot` at `:1613`) ✓; `pot`
  `Potential.lean:43` ✓; `shipped_done` `Round.lean:1661` (`hκ : ctl.κ =
  []`) ✓; `hjmp` `DriverCollapse.lean:2035`, `CtlTied.noproc` `:2213` ✓;
  the fuel-parameter review `../docs/2026-09-04_review-of-fuel-parameter-
  design.md` has "## 5. Our restatement, sized" ✓.
- **§5.** `test_unit.sh:28/:39/:47/:65/:88` are the gate/speedbump
  headers named ✓; `boundary_check.sh:46` is the pattern and names every
  internal the document lists ✓; TSV header lines 8–11 = the fail-hard
  sentence ✓; nine classes in use + `engine-mirror-test` reserved = ten;
  16 `positive-client` + 2 `declared-smoke` = 18, the sixteen exhibits +
  CallSmoke + ReadinessSmoke ✓; manifest header `:8`–`:26` "WHAT GREEN
  ESTABLISHES, EXACTLY" ✓, tail "23 constructors, 50 variant rows (30 …
  15 NO-RULE, 5 OUT-OF-SCOPE), 0 red, 18 consumer modules" and "CLAIMS:
  11 claim rows, 90 declaration names" ✓; `BOUNDARY: 19 modules checked,
  0 internals mention(s) in total, exit=0` `h1-notes.md:781` ✓;
  `parametric_inventory.lean:1`–`:16` ON DEMAND, fail-closed ✓; CLAIMS.md
  header "HAND-WRITTEN PROSE, stated as such" ✓.
- **§6.** The fifteen NO-RULE rows matched one-for-one against the
  manifest (3 store, 3 load, 3 create, 4 kill, 1 alloc, 1 memop_vals),
  the five OUT-OF-SCOPE rows likewise ✓; `hbsz` `Soundness.lean:4296` ✓;
  `caseProg_select` `CaseExhibit.lean:68` ✓; `EvalClass.lean` header
  names the residual and its mover ✓; KOI A1/A2/A3/B1–B9/B11/B12/B14/
  C11/C12 say what the document says ✓.
- **§7.** The acceptance-goals inner quotation verbatim `DECISIONS:704`–
  `:706` ✓; the three records exist ✓; the archive exists ✓.
- **Shop-window.** Every `2026-` token inside a tag or a record path
  (grep) ✓; no "former/until/since/deleted/slice" as narrative ✓; `K3`,
  `F1` only inside quoted entry titles; `AR5` once as a handle (S-1b).
  Every `docs/…`/`../docs/…` path cited exists (`ls`) ✓.

## Reviewer 4's findings — genuinely resolved?

- P-1: **disputed-correctly.** The register does contain the full
  sentence — `DECISIONS.md:1753`–`:1756`, wrapped "which (for / now) is
  sequential" across a line break, which is why a single-line grep for
  "for now) is sequential" missed it. The document now cites that entry
  and notes the later entry's ellipsis (`:1823`). "Verbatim from the
  register" is true as written. Correct resolution.
- T-1: resolved (lines 128–131 name the five mask-generic raw-WP lemmas;
  all five verified `{E : CoPset}`).
- T-2: resolved (the table lists all 11 `wps_sound_empty` consumers;
  verified exact) — with one cite since moved by H-1 (T-2 here), not a
  defect of the fix.
- T-3: resolved (the per-statement table; every cell re-derived and
  exact).
- D-1: resolved (`hbsz` explained at lines 684–688, correctly).
- C-1: resolved in substance (long sentences split; §2.6 created; §7
  ledger shortened; glossary entries added) — length 731, which I judge
  acceptable (C-4 here), with ~15–20 lines still removable and one
  five-line sentence remaining (430–434).
- T-4: resolved. T-5: resolved (`:355`–`:358` verified). T-6: resolved
  (KOI C11, C12; CLAIMS.md header). T-7a: resolved (eight fields).
  T-7b: resolved-with-defect (the script path fixed; the workspace path
  in the same sentence still lacks `../` — C-1 here).
- D-2: resolved (lines 482–487, the two restrictions separated).
- S-1a/b: resolved. S-2: resolved for CLAIMS.md:44 and README:835
  (verified); KOI B7/B9 orchestrator-owned, out of scope here.
- C-2: resolved (trio and round names in the glossary; B9 dated).

## Not checked

- No `lake`/`lean` invocation: the 402-pin count, the axiom sweeps, the
  gate tail and the sub-trio cones of T-1 are taken from the verbatim
  gate transcript (`h1-notes.md` second §8) and from `Audit.lean`'s own
  comments, not re-measured. T-1 is a finding against the document's
  consistency with its cite; if `#print axioms` at `dd7b852` disagrees
  with the comments, both surfaces need the fix.
- Whether any export's proof term actually reaches a `panic!` arm of the
  generated tree (D-1 asks for disclosure, not for a theorem); the
  banned-axiom sweep does not see `panic!`, which is a term, not an
  axiom.
- iris-lean internals (`wp_strong_adequacy_gen`, `Language` laws) —
  taken as the library's.
- The differential-validation numbers of README "What you are asked to
  take on faith" — not this document's claims.
- The fuel indices of `loop_step_done_exhaust`/`loop_step_done` (the
  "fuel 1"/"fuel ≥ 2" reading, lines 291–294): statements read at the
  head only.
- README and WALKTHROUGH beyond the sections this document points at and
  the pointer grep; their own shop-window state (slice vocabulary in
  README:34–58 and WALKTHROUGH §7) is reviewer 4's note and stands.
- The hygiene of KOI itself (B7/B9 pointers being fixed by the
  orchestrator; B8 listing closed items).
- Exhaustiveness of `evalClass`'s `.uncovered` leaf set beyond what the
  document claims (a superset).
