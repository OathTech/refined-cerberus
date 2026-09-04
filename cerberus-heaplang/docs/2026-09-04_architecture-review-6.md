# ARCHITECTURE.md — fresh full review (review 6, of the third pass)

**VERDICT: A− — PASS** (two one-clause exactness fixes in §3 required
before the merge ask, T-1 and T-2 below; neither changes what is claimed
as proved, and no class A/B item is missing from the surface).

Reviewer: fresh (reviewer 6; no contact with earlier versions, reviewer
5's report or the rewrite notes until the cold read and the source
verification were complete). Standard: grumpy PL professor — "would I
sign this as the paper's system section"; A− or better passes. Tree:
`worktrees/review-arch-6`, detached at `d80b639`. Method: source reading
only — no `lake`/`lean` invocation; `sed -n`/`grep`/`awk` over
`CerberusHeapLang/**/*.lean`, `scripts/*`, `../scripts/*`, the generated
manifest, the pinned workspace of the primary checkout
(`refined-cerberus/.cerberus-ws/lean_frontend`, `git log -1` =
`f95ef8d9c`, read-only; the worktree has no `.cerberus-ws` of its own),
LemLib at `cerberus-heaplang/.lake/packages/LemLib` of the primary
checkout, `../docs/DECISIONS.md` (tail from `:2010`, plus every cited
entry), `../docs/KNOWN-OPEN-ITEMS.md` (KOI), `../CLAUDE.md`,
`docs/CLAIMS.md`, `docs/CAPABILITY_MANIFEST.md`, `README.md` (the sections
the document points at), the archive record. Reading order:
ARCHITECTURE.md cold; sources and context; then, last, review 5 and the
rewrite notes' "Third pass".

Summary. The document does what its title says: it describes the
system as it is, in the order object → proved → trusted → how to read an
export → instruments → not covered → ledger, and a reader who knows Iris
can go from any sentence to the theorem it is about. I checked ≈ 140
cites (listed below); every count re-derived is right (23 constructors;
8 mirrored binops; 8 `MachineCtx` fields; 10 `MemWF` fields; 8 + 2 + 5
`ShippedRefusal`/`OpenRound`/`RoundClass` arms; 26 `complete_*` lemmas;
11 `*_consequence` lemmas; 3 + 11 + 1 collapse consumers; 9 statements
with every premise as printed and every package definition in their
texts as tabulated; 402 pins; 61/40 `panic!` code arms; 50/30/0/0/15/5
manifest rows, 18 consumers, 19 boundary modules, 11 claim rows / 90
names; the 15 NO-RULE and 5 OUT-OF-SCOPE variants one-for-one). Every
`[USER]`/`[AGENT]` tag resolves to its register entry with the date right
and the quotations verbatim (both ellipses correct). The shop-window is
clean: all 25 `2026-` tokens sit in tags or record paths; slice handles
appear only inside quoted DECISIONS entry titles. Every KOI class A/B
item that the register assigns to this surface is here. What keeps it
from a clean A is precision in the trust section: one enumeration that
says it is what `Audit.lean`'s comments record and is not (T-1), and one
generalisation about the `panic!` arms that is false for seven of the
sixty-one (T-2). Everything else is local wording.

## Findings, ranked by severity

### LOW–MEDIUM (trust section; one clause each)

**T-1. The sub-trio enumeration is presented as what `Audit.lean`'s
comments record, and it is a proper subset of that.** Lines 469–476:
"The public-named lemmas with SUB-trio cones are therefore unpinned, as
`Audit.lean`'s comments record them. `fibRounds_closed`, `regionCost_pos`
and the `freshBase_*` bounds have `[propext, Quot.sound]` (`:354`–`:356`,
`:380`–`:384`, `:523`–`:525`). `BareHead.decomp_call_root` has `[propext]`
(`:523`); `regionCost_eq` and `runND_killed` have no axioms (`:384`,
`:552`–`:553`)." Every attribution given is exactly what the cited
comment says. But `grep -n -i 'sub-trio' Audit.lean` finds three more
comment blocks the sentence does not mention: `Audit.lean:220`–`:222`
(`BareHead.not_annot` `[propext]`, `Decomp.get_ctx_rebuild_action`
`[Quot.sound, propext]`); `:334`–`:339` (the four `∈`/`contains` bridge
lemmas `mem_contains_int`, `contains_cons_int`, `contains_cons_ne_int`,
`int_beq_eq_true`, `[propext, Quot.sound]`); `:463`–`:465`
(`Decomp.callRedex?_inv`, `callRedex?_some`, `pot_plug_call_le`,
`callRedex?_none_of_jumpRedex?_some`). A reader of the trust section will
take the list as complete — "as the comments record them" invites it —
and it names 7 of 17. Fix (either): "… unpinned; `Audit.lean`'s comments
record seventeen, among them `fibRounds_closed` …" — or enumerate the
other ten with their cites. (Cones as the comments record them; not
re-measured.)

**T-2. "Each mirrors an OCaml `assert false`/`failwith` arm, where the
OCaml run aborts" is false for seven of the sixty-one arms.** Lines
446–447. Of the 61 code arms (re-derived below), 54 do carry an OCaml
cite or a `failwith`/`assert` mirror in their message. The other seven
are Lean-side guards with no OCaml counterpart: the five `CerbFS.lean`
refusals (`:166`, `:200`, `:221`, `:241`, `:260`) are the minimal
fs-model's own fail-closed boundary — its header says so, `CerbFS.lean:47`
"Refusal mechanism [deliberate]: `panic!`, not an FsError … the minimal fs
model cannot track …" — where the OCaml performs the real file operation
and does not abort; `CerbTags.lean:34` (`tagDefsUnreachable`, "applied
tagDefs () site survived reader lifting") is a reader-lifting guard; and
`CoreParser.lean:2097` is a fuel guard on a Lean-only scanner. The next
sentence's consequence ("continues where the OCaml faults") is therefore
also wrong for the fs arms: there the Lean definition answers `default`
where the OCaml answers correctly. The disclosure's point survives (the
kernel reads all 61 as `Inhabited` defaults); the characterisation does
not. Fix: "Fifty-four mirror an OCaml `assert false`/`failwith` arm,
where the OCaml run aborts; the five `CerbFS.lean` arms are the fs
model's own fail-closed refusals (`CerbFS.lean:47`–`:54`) where the OCaml
has a real file system, and `CerbTags.lean:34`/`CoreParser.lean:2097`
are Lean-side unreachability guards." Two lines.

### LOW

**T-3. The collapse-consumer table's "exactly" excludes occurrences it
does not say it excludes.** Lines 204–205: "Their consumers, exactly
(non-comment occurrences, every package module)". Comment-stripped grep
agrees with the three rows for the exhibit modules (3 `wps_sound`, 11
`wps_sound_empty`, 1 `wpt_sound` — verified line by line). But
`Audit.lean` is a package module and its pin list names all three as
non-comment `Name` literals (`:178` `wps_sound`, `:181` `wpt_sound`,
`:495` `wps_sound_empty`, `:501` `wpt_sound_empty`); and inside the
defining modules `wps_sound_frame`/`wps_sound_frame_empty` consume
`wps_sound` (`Wps.lean:3664`, `:3685`) and `wpt_sound_empty` consumes
`wpt_sound` (`Wpt.lean:3406`). Fix: "(non-comment occurrences outside
the defining module and `Audit.lean`'s pin list)".

**T-4. "21 sites in `Wps.lean`" counts two comment mentions.** Line 143.
`grep -n '⊤' Wps.lean` = 21 lines, of which `:134` and `:341` are
docstring text; 19 are code. `Wpt.lean`'s 26 are all code. The parenthetical
is a raw grep count offered as a count of sites and is not labelled
DERIVED (the document labels its other derived counts). Fix: "(19 code
sites in `Wps.lean`, 26 in `Wpt.lean`; occurrences DERIVED)". KOI B11
carries the same "21 + 26"; the orchestrator may align it.

**S-1. The slack disclosure is narrower than its register entry.** Lines
740–741: "`fib_rec_certified_production`'s bound has one unit of slack;
nothing claims tightness (KOI B6)." KOI B6 (`../docs/KNOWN-OPEN-ITEMS.md:34`)
records the same class for `even_odd_certified_production` (`3·n + 6`,
shipped loop active at `3·n + 5`) and `tl_wpt` (H1 range audit Note-2).
The pointer is right; the sentence names one of three. Fix: "The budget
bounds of `fib_rec_certified_production` and `even_odd_certified_production`
(and `tl_wpt`'s) carry one unit of slack; nothing claims tightness (KOI
B6)."

**C-1. "generated `CerbMem.lean`" versus "the hand-written seams" is a
terminology collision the document never resolves.** Lines 442–446 say,
in one sentence, "61 in the hand-written seams, 40 of them in
`CerbMem.lean` (e.g. … generated `CerbMem.lean:380`), none in
lem-generated code". A cold reader cannot tell that "generated" names a
directory (`generated/`) that holds both lem output and byte-identical
copies of 23 hand-written files (`../.cerberus-ws/lean_frontend/handwritten_copy.manifest`;
`cmp` identical for `CerbMem.lean`), while "lem-generated" names an
origin. The same usage is at lines 25, 35, 187, 293, 372, 528, 532, 613,
736. Fix: one clause in the header sentence that introduces the
workspace: "(`generated/` holds the lem output and byte-identical copies
of the hand-written seams listed in `handwritten_copy.manifest`; 'generated
`X.lean`' below is that path)".

**C-2. §5's head count does not match its list.** Line 635: "Three run
in the full gate; one instrument is on demand." Six bullets follow: the
manifest, the module classification ("pure data"), the import-direction
check, the boundary check, the claim matrix (whose names the manifest
generator checks), the inventory. The reader has to work out that the
classification is data, that the claim-matrix check rides inside the
manifest run, and that "three" = manifest + import direction + boundary.
Fix: "Four instruments: three run in the full gate (the manifest — which
also checks the claim matrix's names —, the import direction, the
boundary), the inventory is on demand; the module classification is the
data all of them read."

**C-3 (nit). "Five OUT-OF-SCOPE variants lie inside the fragment's
constructors but outside the mirror"** (lines 694–695). For the third,
"an annotated value at the plain-symbol binder", the manifest row
(`CAPABILITY_MANIFEST.md:119`) says it is "excluded by the fragment:
`Frag.sseq_sym` carries `hb : BareHead e1`" — outside `Frag`, not merely
outside the mirror. "Inside the fragment's constructors" is defensible
(the constructor kinds), but "outside the mirror" undersells the
exclusion for that row. Fix: "outside the mirror (one, the annotated head
at the plain-symbol binder, is already outside `Frag` by `BareHead`)".

### Provenance (P-)

No finding. Every tag resolves with its date: TRUST ARCHITECTURE [USER
2026-08-29] `DECISIONS:86`; SPEEDBUMPS, NOT ADVERSARIAL GATES [USER
2026-09-02] `:265`; THE DEMO'S ACCEPTANCE GOALS [USER 2026-09-02] `:703`
(the inner quotation at `:704`–`:706` verbatim); THE BOUNDARY IS
FAIL-CLOSED [USER 2026-09-02] `:816`; KILL/FREE K3 LANDED [AGENT
2026-09-03] `:1135`; F1 RANGE AUDIT [AGENT 2026-09-03] `:1715` with the
[USER 2026-09-03] two-loop remark at `:1753`–`:1756` verbatim (wrapped
"which (for / now)") and the elided re-quote at `:1823`–`:1825`; FUEL IS
A DEFECT IN THE CERBERUS-LEAN SEMANTICS [USER 2026-09-03] `:1787`; AR5-
MANIFEST LANDED and COMBINED [AGENT 2026-09-04] `:1916`; THE DEMO'S SCOPE,
RESTATED [USER 2026-09-04] `:2130`–`:2133` (the document's ellipsis elides
"just because it's a nice stable interface but it shakes out many of the
theory difficulties." — correct); `la_pos` [AGENT 2026-09-03] under the
K3 entry. Derived tallies are labelled DERIVED where the document derives
them (the `panic!` counts), with the one exception T-4.

### Disclosure (D-)

No finding. KOI A1, A2, A3, A5, A6 and B1–B9, B11, B12, B14 are each on
this surface with their number; A4 (LemLib `Pmap` laws at the re-pin) is
assigned by the register to the scout record, not to this surface. The
`panic!` paragraph says what is and is not established (no theorem that
an export's run reaches none; the sweep sees axioms, not terms). The
fixed `⊤` mask, the annotation-free fragment, the static fuel premise, the
outer-fuel quantifier, the singleton equation, the empty `tagDefs`/`extern`,
the seeded/no-procedure profiles, the two bridges and the instruments'
limits are each stated with a register pointer. Nothing is over-claimed:
"trusted as a policy decision, not proved" (§1, §3), "a reviewed reading,
not a theorem" (§5), "characterised, not closed" (§2.2, §6).

### Length, clarity, structure (judgment)

774 lines is acceptable. Every section is load-bearing: the glossary (17
entries; each term is used in at least two sections and none is
decorative), §2.5's two tables (what a reader must read before trusting a
closed statement), §4's premise list (the disclosure that carries KOI
A1/B4), §6's variant table. Duplication is pointer-form only (§1/§6
masks; §2.2/§6 residual; §3/§6 `panic!`, where §6 adds the pin-vs-mainline
`killM` fact). The reading order is followed and findable (numbered
sections, forward references resolve). The author's sentence check (0
over four wrapped lines) is consistent with my read: no sentence made me
re-parse it. The two verbatim theorem readings in §4 are the best part of
the document; a PL reader who reads only §4 comes away with the right
meaning of a triple here.

## Verified true (the cites checked, and how)

Method: `sed -n <line>p` at every cite; `grep`/`awk` for every count.
The load-bearing ones:

- **Header/glossary.** `../scripts/semantics-pin.env`
  `CERBERUS_LEAN_COMMIT="f95ef8d9c…"` and the workspace `git log -1` =
  `f95ef8d9c` ✓; `drive_nonmemory_steps_aux2_lemFuel` generated
  `Driver.lean:346` ✓; `Frag` `Soundness.lean:4149`; `Step` `Step.lean:1456`;
  `spikeCtx`/`spikeCtl`/`procCtx`/`procCtl` `:3355`/`:3331`/`:3363`/`:3336`;
  `prodCtx`/`prodCtl` `ProdEntry.lean:580`/`:567` ✓; `reduction: PCALL`/
  `RETURN`/`PROGRAM-DONE` each once in generated `Core_reduction.lean` ✓;
  the trio `Audit.lean:159`–`:160` ✓; `DriverSafeCtl`'s six ties
  `Adequacy.lean:935`–`:940`, `DriverDoneCtl`'s five `ProdLoop.lean:459`–
  `:463` (+ `k + 2 ≤ fl`) ✓.
- **§1.** 23 `Frag` constructors `:4150`–`:4314` (awk count of `|` arms =
  23; names: val_pure store load create kill kill_op alloc alloc_op sseq
  annot save if_ run sseq_spec pure_sym load_op sseq_sym memop_vals
  memop_op store_op case_value wseq call) ✓; `PePure` `:2007`;
  `isMirroredOp` = Add/Sub/Mul/Eq/Lt/Le/Gt/Ge (8) ✓; `BareHead` `:3981`
  (val_pure, create, memop_vals, memop_op, alloc, call) ✓; the
  annotation-free header `:4129`–`:4147` says what §1 says (the
  `current_loc` forcing fact, the mover) ✓; `Config` `:400`; `Ctl`
  `:371`–`:374` = κ/proc/execLoc; `MachineCtx` `:405`–`:413` = exactly the
  eight fields named ✓; `Step.call` `:2047` pushes `(ctl.proc, ctx)`;
  `callRedex?` `:703`; `Step.ret`/`ret_annot` `:2079`/`:2096`;
  `Step.ctl_cases` `:2250` (unchanged ∨ push ∨ pop) ✓; `Lang.lean:58`
  `instance : Language …` ✓; `wps` `Wps.lean:301`, `wps.pre` `:217`,
  `LabelSpec` `:113`, `ProcSpec` `:129`; `wpt` `Wpt.lean:200`, `⌜1 + m ≤ k⌝`
  `:167`, `1 + m + k' ≤ k` `:172` ✓; `⊤` 21/26 lines (T-4) ✓; `AtomicStep`
  `:194`, `wp_of_atomic` `:210`, `wp_store` `:1584`, `wp_load` `:1614`,
  `spike_wp_wand` `:1676`, all `{E : CoPset}` ✓.
- **§2.1.** All ten atomic specifications at the cited `Rules.lean` lines
  ✓; `load_atomic` takes `(dq : DFrac)` ("at any fraction") ✓;
  `create_atomic`'s `hsz` at `:995` ✓; `wps_of_atomic`/`wpt_of_atomic`
  `Wps.lean:345`/`Wpt.lean:664` ✓; `isAtomicMemberAccess` generated
  `CerbMem.lean:1949`, body `| none => false` at `alloc.ty = none`, used
  at `:2003` (`loadM`) and `:2067` (`storeM`) ✓; the eleven `Heap.lean`
  bundle cites ✓; structural rules `Wps.lean:701/3195/3287/417/473`,
  `Wpt.lean:563/2975/3032/726/758` ✓; `Rules.lean:35`–`:44` "NO raw-WP
  sequencing rule … a jump discards the context" ✓; collapses
  `Wps.lean:3440/3326/3367/3637/3657`, `Wpt.lean:3173/3382/3400` ✓; the
  consumer table's three rows: every cited line contains the call
  (`CallSmoke:330`, `FibRecExhibit:648`, `EvenOddExhibit:502`; the eleven
  `wps_sound_empty` sites; `CallSmoke:461` inside `cs_twp_readout` `:455`)
  ✓ — with T-3's qualification; `load_atomic_readonly` `Rules.lean:460` ✓.
- **§2.2.** `CerberusRound` `Round.lean:195` read in full (singleton
  step list, `can_advance`, `(NDactive NOWAKEUP, …)`) ✓; `loop_step`
  `:965`; `engine_step_matchU` `:1010`–`:1015` matches the quoted block
  character for character ✓; `step_iff_cerberusRound` `:1598`;
  `frag_round_complete` `:5369`; `ShippedRefusal` `:214` with eight arms
  (error, killed, fork, panic, panic_env, panic_memop, error_next,
  panic_noproc) — the document's five-way description is faithful ✓;
  `OpenRound` `:357` two arms, mover text at `:377` ✓; `complete_store`
  `:2300` … `complete_ret` `:5351` (26 lemmas) ✓; `cerberusRound_classify`
  `:5476` with `hwf : M.SeqWF`, `hκ : ctl.κ = []` ✓; `RoundClass` `:1631`
  five arms ✓; "WHAT CONSUMES WHAT" `:141`–`:153` says what §2.2 says ✓;
  `loop_step_frag`/`'` `DriverCollapse.lean:2118`/`:2024` ✓;
  `dischargeStep`/`outcomesU` `Soundness.lean:154`/`:262` ✓; `evalClass`
  `.uncovered` at the first leaf (`EvalClass.lean:28`–`:31`) ✓.
- **§2.3.** `dgBody` `:69`, `dg_loop_exhausts` `:126`,
  `diverge_total_unprovable` `:172` (binders `ra σ₀ m₀ hcoh Ls Ψ k hwp`)
  ✓.
- **§2.4.** `drive_nonmemory_steps_aux2_wrapper_defeq … := rfl` generated
  `CerbND.lean:396`–`:397`; `drive_wrapper_defeq … := rfl` `:467` ✓;
  `spike_step_adequacy`/`_alloc` `:568`/`:667` apply `wp_strong_adequacy_gen`
  (`:581`, `:683`) ✓; `engine_adequacy`/`_alloc` `:1278`/`:1344`;
  `DriverSafeCtl` `:932`; `drive_safe_aux` `:1079` (`private`); `ControlOk`
  `:800`; `FragProcs` `:767` with `body`/`potBound`/`labels` ✓;
  `LabeledProcs`/`CtlTied` `DriverCollapse.lean:2178`/`:2205`, `CtlTied.noproc`
  `:2213`, `hjmp` `:2035` ✓; the fuel reading: `loop_zero_exhausts`
  `:2246` (fuel 0 → kill), `loop_step_done_exhaust` `:2257` (`Nat.succ 0`
  → kill; docstring "the drain iteration on the empty thread list has no
  fuel"), `loop_step_done` `:392` (`Nat.succ (Nat.succ fl)` → active) ✓ —
  read in full, not only at the head; `wpt_driver_cps` `ProdLoop.lean:609`;
  `DriverDoneCtl` `:456` (`k + 2 ≤ fl` → PROGRAM-DONE with `ψ`) ✓;
  `driverDoneCtl_step` `:537`; `wpt_driver_done_procs` `:799`;
  `DriverDoneAt`/`wpt_driver_aux`/`wpt_driver_done`/`_alloc`
  `:56/:175/:290/:358` ✓; `project_triple_pure` `:1605`, `MemTriple`
  `:1518`, `project_triple_pure_alloc` `:1743`, `MemTriple_alloc` `:1669`,
  `LaunchCoh` `:422`–`:432` (coh, `wf : MemWF σ`, `budget : B ≤ headroom
  σ.lastAddress`) ✓; the eleven `*_consequence` lemmas `:1909`–`:2007` ✓;
  `CellMap` `:1407`, `Sat` `:1415`, `DeadAt` `:1900` ✓; `prodFile` `:125`,
  `prodFileWith` `:544`, `prodFile_eq_with … := rfl` `:549`,
  `prod_run_eqJ_procs` `:716` with `hfl : k + 2 ≤ CerbFuel.driverFuel`
  (`:723`), `prod_run_eqJ` `:402`, `prod_run_safe_procs` `:768` read in
  full (the two-arm conclusion as quoted) ✓; `prodMem₀` `:212`,
  `prodMem₀_memWF` `:243` ✓; generated `Driver.lean:355`–`:358`
  (`new_drive_core_threads` calls `drive_nonmemory_steps_aux2`) ✓;
  `Driver.lean:530` contains both "CONCURRENCY IS BROKEN" and
  `current_proc_opt := …` (one very long line; the cite is right).
- **§2.5.** All nine signatures read at `ProdExhibit.lean:264`,
  `ProdLoopExhibit.lean:75`/`:620`/`:1435`, `DisposeExhibit.lean:1479`,
  `RegionLoopExhibit.lean:633`, `MallocListExhibit.lean:1654`,
  `FibRecExhibit.lean:865`, `EvenOddExhibit.lean:722`: every premise in the
  table present and none missing (`hn`; `hfuel` `2n+6`, `6n+8`, `7n+5`,
  `25n+9`, `3n+6`, `fibRounds n.toNat + 4`; `hcost`; both `hB` as printed);
  no termination hypothesis ✓. The package-definitions table re-derived
  from the nine texts: `sevenVal`/`sevenBytes`/`intTy`
  (`Examples/Layout.lean:57`/`:65`/`:50`) + `CellCoh`; `ivVal`
  (`LoopExhibit.lean:63`) + `fibSpec` (`FibExhibit.lean:60`);
  `intUndefBytes` (`AllocExhibit.lean:88`); `ptrVal` (`ListRevExhibit.lean:466`),
  `SeedChain` (`:1210`), `CellMap`, `Sat` (at `ProdLoopExhibit.lean:1449`–
  `:1450`); dispose/region/malloc engine fields only; `regionCost`/
  `headroom`/`prodMem₀` (`Heap.lean:2322`/`:2267`, `ProdEntry.lean:212`);
  `ml_budget_bridge` `:1626`; `fibRounds` `:450` (3, 3, `+9`),
  `fibRounds_closed` `:470` `fibRounds n + 9 = 12 * fibSpec (n + 1)` ✓ —
  every cell exact. `fib_rec_certified` `:814` and `even_odd_certified`
  `:674` take `(fuel : Nat)` ✓.
- **§2.6.** `MemWF` `Heap.lean:1583`, exactly ten fields in the order
  named ✓; `CohG` `:2632` with `wf : get? mk 0 ≠ none → MemWF σ` ("under
  cursor presence") ✓; `create_fresh_global` `:1801`; `MemWF.loadM/storeM/
  allocateObject/allocateRegion/killM` `:1817/:1877/:1898/:1937/:2010` ✓.
- **§3.** `allowedAxioms` `Audit.lean:159`–`:160`; pin loop `:615`–`:616`;
  sweep `:617`–`:636`; banned sweep `:637`–`:653`; "There is no declared
  boundary axiom" `:45` ✓. 402 pins: 402 ``` ``CerberusHeapLang.* ```
  tokens in `trioExports` (`awk`/`grep -o`/`wc`), **402 distinct** (see
  the aside below); `h1-notes.md:752` gate line ✓. The sub-trio comments
  at `:354`–`:356`, `:380`–`:384`, `:523`–`:525`, `:552`–`:553` say exactly
  what the document attributes (T-1 is about the three blocks it omits).
  Pinned tree: `axiom` declarations 0 (`grep -E '^\s*axiom '` over
  `generated/*.lean` and `lean_frontend/*.lean`), `(sorry` 0, LemLib
  `axiom` 0 ✓. **The `panic!` paragraph re-derived**: `grep -c 'panic!'`
  over the nine hand-written seams = 70 lines (CerbDecode 6, CerberusImpl
  2, CerbFloat 5, CerbFS 8, CerbMem 42, CerbND 1, CerbTags 1, CerbUtils 4,
  CoreParser 1); comment lines read one by one = 9 (`CerbFS:47/:51/:91`,
  `CerbFloat:84/:163/:294`, `CerbND:42`, `CerbMem:1127/:2555`); code arms
  61, of which `CerbMem.lean` 40 ✓; no `panic!` in any `generated/*.lean`
  outside the manifest's copy list ✓; `lean_frontend/CerbMem.lean` and
  `generated/CerbMem.lean` `diff -q` identical ✓. `sizeofCtype` `Void0`
  arm `panic!` at generated `CerbMem.lean:380` ✓. The `= default` by `rfl`:
  `CerbMem.lean:1127`–`:1130` is the comment ("`panic!` expands to
  `panicWithPosWithDecl …`; every such term is definitionally `default`")
  and `:1131`–`:1132` is `have hp : ∀ … (panicWithPosWithDecl m d l c msg
  : α) = default := fun _ _ _ _ _ => rfl` — the `rfl` is for the
  expansion of `panic!`, which is the right object ✓. LemLib: `opaque
  failwithI … := default` at `LemLib.lean:173` (comment `:160`–`:172`:
  "opaque: NO equations"), `opaque fuelExhaustedWith … := witness` `:187`
  ✓ — the `opaque`/`panic!` distinction as stated is right;
  `lemDefaultFuel = 1000000` `:56` ✓. `killM`'s dead-allocation arm
  generated `CerbMem.lean:1906`–`:1907` is `fail_ (MerrUndefinedFree
  Free_dead_allocation)` — a kill, as §6 says ✓. Gate 1 `test_unit.sh:28`
  ✓.
- **§4.** `fib_certified_production` (`ProdLoopExhibit.lean:75`–`:89`) and
  `counter_loop_certified` (`LoopExhibit.lean:427`–`:439`) quoted
  verbatim (diffed line by line) ✓; section variables `LoopExhibit.lean:403`
  ✓; `Coh`/`CellCoh` `Heap.lean:386`/`:358` ✓; premises of `engine_adequacy`
  `:1278`–`:1296` (`htd`, `hex`, `hκ`, `hQf`, `hQpot`, `hPf`, `hfrag`,
  `hpot`, `hcoh`, `hwp`, `hcl`), `project_triple_pure` `:1605`–`:1613`,
  `wpt_driver_cps` `:609`–`:620`, `wpt_driver_done_procs` `:799`–`:809`
  (`hl : LaunchCoh …`) as listed ✓; `pot` `Potential.lean:43`,
  `Frag.esize_le_pot` `:100` ✓; `shipped_done` `Round.lean:1661` with
  `hκ : ctl.κ = []` ✓; `DECISIONS:1753`–`:1756` and `:1823` as above ✓;
  `../docs/2026-09-04_review-of-fuel-parameter-design.md` "## 5. Our
  restatement, sized" ✓; `CerbFuel.driverFuel = 100000000` generated
  `CerbFuel.lean:71` (as the second pass verified; not re-read here).
- **§5.** `test_unit.sh:28/:39/:47/:65/:88` are the gate/speedbump headers
  named ✓; `boundary_check.sh:46` is the pattern and names every internal
  the document lists ✓; TSV header lines 8–11 = the fail-hard sentence;
  class vocabulary at `:16`–`:23`, `engine-mirror-test` reserved with no
  member ✓; classes in use 9 (`awk`/`uniq -c`), 16 `positive-client` + 2
  `declared-smoke` = 18 ✓; manifest header `:8`–`:26` ✓; tail "23
  constructors, 50 variant rows (30 RULE, 0 RULE-TOTAL-UNDEMONSTRATED, 0
  PARTIAL-ONLY, 15 NO-RULE, 5 OUT-OF-SCOPE), 0 red, 18 consumer modules"
  and "CLAIMS: 11 claim rows, 90 declaration names checked" ✓;
  `BOUNDARY: 19 modules checked, 0 internals mention(s) in total, exit=0`
  `h1-notes.md:781`, under the second "## 8" (`:746`, the gate at `29d9195`)
  ✓; `parametric_inventory.lean:1`–`:16` ON DEMAND, fail-closed ✓;
  CLAIMS.md header "HAND-WRITTEN PROSE, stated as such" ✓.
- **§6.** The fifteen NO-RULE rows one-for-one (manifest `:84`–`:86`
  store, `:90`–`:92` load, `:94`–`:96` create, `:99`–`:102` kill, `:105`
  alloc, `:122` memop_vals), the five OUT-OF-SCOPE rows (`:113`, `:116`,
  `:119`, `:121`, `:129`) ✓; `hbsz` `Soundness.lean:4296`–`:4297` ✓;
  `caseProg_select … := rfl` `CaseExhibit.lean:68`–`:71` ✓; `EvalClass.lean`
  header names the residual and its mover (`:39`) ✓; `OpenRound` mover
  `Round.lean:377` ✓; KOI A1/A2/A3/A5/A6/B1–B9/B11/B12/B14/C11/C12 say what
  the document says (S-1 for B6) ✓.
- **§7.** The acceptance-goals inner quotation verbatim `DECISIONS:704`–
  `:706` ✓; the three records and the archive exist ✓.
- **Shop-window.** 25 `2026-` tokens, every one inside a `[USER …]`/
  `[AGENT …]` tag or a `docs/2026-…` record path (grep) ✓; slice handles
  (`K3`, `F1`, `AR5`) only inside quoted DECISIONS entry titles (grep for
  `\b(K[0-9]|F1|H1|AR5|C[1-4]|S[0-4]|QA[12]|P[0-6])\b`) ✓; no "former/
  until/since/deleted" as narrative ✓; every `docs/…`/`../docs/…` path
  cited exists ✓.

**Aside for the orchestrator (not a finding against the document; the
register invites it).** KOI C15 says "`Audit.lean`'s pin list has two
duplicate entries (`loop_step_frag`, `loop_step_frag_same`): '402 pins'
is the list length; 400 distinct names." At `d80b639` — and at `dd7b852`,
where the note was made — `trioExports` has 402 ``` ``CerberusHeapLang.* ```
tokens and 402 distinct (`sort | uniq -d` empty). The four names in
question are pairwise distinct: `loop_step_frag` (`:20`) vs
`loop_step_frag'` (`:391`), `loop_step_frag_same` (`:310`) vs
`loop_step_frag_same'` (`:391`) — primed twins, not duplicates. C15's
premise is wrong; the document's "402 pins" is right in both senses.

## Reviewer 5's findings — genuinely resolved?

- **T-1**: resolved as asked — the five groups are attributed exactly as
  `Audit.lean:354`–`:356`, `:380`–`:384`, `:523`–`:525`, `:552`–`:553`
  record them, the rule (pinned = exactly the trio; everything else bounded
  by the sweep) is stated, the five-line sentence is split. Residue: the
  new framing "as `Audit.lean`'s comments record them" makes the list read
  as complete, and the comments record ten more names (my T-1).
- **D-1**: resolved — §3 "The `panic!` arms" (lines 441–461) carries the
  seven contents; counts re-derived here (70/9/61/40, none lem-generated);
  `= default` by `rfl` at `CerbMem.lean:1131`–`:1132`; `opaque` at
  `LemLib.lean:173`/`:187`; §2.2's "LemLib's kernel-opaque failure (not
  the `panic!` arms of §3)" present (line 248); §6 item present (lines
  718–723); README sentence not re-read. Residue: the "Each mirrors an
  OCaml …" generalisation (my T-2).
- **T-2**: resolved — `EvenOddExhibit.lean:502` (`wps_sound` call), `:674`
  (`theorem even_odd_certified`), `:722` (`theorem
  even_odd_certified_production`) all exact at `d80b639`.
- **D-2**: resolved — §3 (iii) "It is a pin, not the mainline; the queued
  re-pin and its one exported-text change (`killM_killed_inv`) are KOI A6."
  matches KOI A6.
- **C-1**: resolved — header line 6 reads `../.cerberus-ws/lean_frontend/`.
- **C-2**: resolved — §4 `hpot` bullet: "it dominates §2.2's round-level
  measure `esize` (`Frag.esize_le_pot : esize e ≤ pot e`, `:100`)";
  `Potential.lean:100` verified.
- **C-3**: resolved — glossary entries *pinned*/*unpinned*, *the sweep*,
  *a tie* (six/five hypotheses verified at `Adequacy.lean:935`–`:940`,
  `ProdLoop.lean:459`–`:463`), *a readout*; "the drain iteration, the
  loop's last pass over the emptied thread list" glossed in place (§2.4);
  "Active means `NDactive NOWAKEUP`" (§2.2; `Round.lean:203`); "falsify
  the certification (§2.2)" (§1).
- **S-1**: resolved — no "interim label" sentence (grep = 0); §5 cites
  "DECISIONS "AR5-MANIFEST LANDED and COMBINED"" (`DECISIONS:1916`).
- **S-2**: resolved — both cites read "`docs/2026-09-04_h1-notes.md` §8,
  the gate at `29d9195`" (lines 464, 674); `:752`/`:781` are under the
  second "## 8" (`:746`).
- **C-4**: resolved — (i) the §5 "In short:" paraphrase is gone (grep =
  0), "Not established:" kept; (ii) §6's first bullet is one line plus the
  five variants; (iii) the header says both surfaces' roles and that they
  overlap by design. Length 774: acceptable (judgment above).

## Not checked

- No `lake`/`lean` invocation: the 402-pin count, the sweeps, the gate
  tail and every axiom-set attribution are taken from the verbatim gate
  transcript (`h1-notes.md` second §8), `Audit.lean`'s list and comments,
  not re-measured with `#print axioms`.
- Whether any export's proof term reaches a `panic!` arm of the pinned
  tree (the document says no theorem states it; I did not attempt one).
- iris-lean internals (`wp_strong_adequacy_gen`, the `Language` laws) —
  taken as the library's.
- The differential-validation claims of README "What you are asked to
  take on faith" — not this document's claims; the README sentence added
  by the third pass was not re-read.
- `CerbFuel.lean:71` (`driverFuel = 100000000`) — taken from the second
  pass's verification.
- Whether every one of the 54 OCaml-mirroring `panic!` arms' cited
  `impl_mem.ml` lines are right (T-2 is about the seven that carry no
  OCaml cite at all).
- WALKTHROUGH.md beyond its existence; README beyond the sections this
  document points at and the headings grep.
- The hygiene of KOI beyond A5/A6/B6/C15 (C15's premise is wrong, above;
  A5's first sentence, per the third pass's observation, describes the
  mainline's `killM` — the document's §6 states the pin's fact correctly).
- Exhaustiveness of `evalClass`'s `.uncovered` leaf set beyond what the
  document claims (a superset).
