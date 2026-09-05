# Range audit 825b5e6..7af24b2 (E3 audit fixes + E4: `unseq`, the head-form certification, THE t1 MILESTONE) — 2026-09-05

**VERDICT: PASS WITH FIXES REQUIRED — A−.** No T- (trust) or C- (coverage)
finding. The `unseq` mirror is exact against the generated engine at the pin
on every admitted arm — the last-reducible-first order of `get_ctx_unseq_aux`,
the value test `is_irreducible = isValE` (the double-annotation arm included),
the completion `one_step_unseq_aux = collectUnseq` (bridged at every fuel), the
UB035 race kill — each read against `core_reduction.lem`/`driver.lem`, proved
by the bridge theorems, and confirmed by executable probes of the generated
engine, the shipped composite and the pinned OCaml oracle (§3). The head form
`s :: post` is the minimal generalisation the engine forces, `pre = []` is a
theorem (`get_ctx_unseq_aux_focus`/`Decomp.get_ctx_at`), the shipped loop's
choice of the head is PROVED inside every `loop_step_*` lemma (the
`find_can_advance (s :: post)` match reduces under `can_advance s = true`), and
the singleton closed forms survive through theorems, not assumptions
(`step_ctx_singleton_of_root`, `Decomp.get_ctx_single`). `t1Main` is a faithful
transcription of `docs/corpus-e0/t1.annot.core` (my own node-by-node comparison,
§2.3), `t1_certified_production`'s statement names the program, the file
builder, the engine and the readout only, `lint 4` is `Specified(4)`, and the
oracle agrees (`Defined {value: "Specified(4)", …}`, exit 4). Census
200/2/162 reproduced; HEAD snapshot `cmp`-identical; 650 pins, 650 distinct,
trio-exact by the build; the twelve headline statements textually unchanged;
every E3 fix genuinely applied except one residue (D-3). The fixes required
are record/shop-window: the "exhaustive pins" claim is false by two (R-1),
ARCHITECTURE carries two slices of stale counts and a wrong statement count
(D-1), the owed cite audit (KOI C18) finds §2.2's own re-measured cites off by
the same commit's docstring edits (D-2), one README residue of E3's D-3 (D-3).

Auditor: fresh, independent (this file; not committed). Fixed detached copy
`worktrees/audit-e4-7af24b2` at 7af24b2; semantics pin `f95ef8d9c`
(`.cerberus-ws` `git log -1` = `f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf`).
Every lake/lean invocation under `scripts/capped` (default 64G cap). Longest
single pass: the signature snapshot, 40.7 s wall; the FULL gate replayed a
primed build in 11.5 s (no module was recompiled — the tree's `.lake` was
already built at HEAD; I did not force a cache-disabled rebuild). Nothing
approached the tripwire. Derived tallies are labelled DERIVED; quoted outputs
are verbatim.

## 0. Method

Read: AUDIT-BRIEF, KNOWN-OPEN-ITEMS, CLAUDE.md, ARCHITECTURE (every E4
sentence checked at HEAD), DECISIONS tail (E-arc rulings, the E3-audit and E4
entries), the design note §B.2/§C.4/§C.9, the E3 range audit, the E4 record
and the E4 closure note. Read the FULL Lean diff of the range (33 files,
+48414/−1667: `Step`/`Wps`/`Wpt`/`Potential`/`EvalClass`/`Adequacy`/`Audit`/
`CorpusE0`/`MirrorCoverage`/`OverflowExhibit` diffs in full; `Round` (3978
diff lines), `Soundness` (2195) and `DriverCollapse` (1214) in full;
`CorpusT1Exhibit.lean` in full (871 lines); the scripts' diffs; the docs
diffs). Read the engine at the pin: `core_reduction.lem` :195–208
(`is_irreducible`), :209–290 (`do_race`, `combine_dyn_annotations`,
`one_step_unseq_aux`), :375–386 (the `Eunseq` arm), :388–405 (LETW-PURE/
ANNOT), :470–520 (`has_ccall`, `is_unseq_with_ccall_aux`), :540–615
(`get_ctx`'s `Eunseq` arm, `get_ctx_unseq_aux`, `apply_ctx`), :1440–1490
(step_ctx's general arm and the UNSEQUENCED-RACE wrapper); `driver.lem`
:900–935 (`can_advance`), :1049–1085 (`find_can_advance`, the loop).
Measured: the FULL gate, a HEAD signature snapshot, the census by script, the
pin list, the axioms of all 155 added theorems, three CLAIMS/skeleton plants,
an executable Lean probe of the generated `get_ctx`/`step_ctx`/the shipped
loop/the shipped composite, the pinned OCaml oracle, a scripted cite check over
ARCHITECTURE.

## 1. Findings, ranked

### R-1 — the "exhaustive pins" claim is false by two; the record's 62/93 split is 64/91 (fix: pin `unseq_focus_round`/`unseq_vals_round`, errata)

E4 record §5 item 6 and §8: "Pins: exhaustive. Every new theorem measured
trio-exact is pinned (62) … 62 exactly the trio, 93 sub-trio"; DECISIONS E4
entry: "Pins 588 → 650 trio-exact; 93 sub-trio facts unpinned (listed)".
MEASURED (`#print axioms` on every one of the 155 theorems the census adds,
§3.6): 64 trio-exact, 91 sub-trio, 0 other. The two trio-exact theorems NOT
pinned are `CerberusHeapLang.unseq_focus_round` and
`CerberusHeapLang.unseq_vals_round` (Examples/MirrorCoverage.lean, the
`engine_step_matchU` instances the record itself advertises in §7). E3's
MirrorCoverage rounds `cAdd_pure_round`/`store_conv_loaded_int_round` ARE
pinned, so this also breaks the module's own precedent. Not a trust gap (the
sweep bounds them; a pin is a check) — a false record claim about the
artefact. Premise verified by measurement: yes. Fix: pin both (650 → 652),
correct §5/§8 and the DECISIONS sentence (64/91), KOI E's expected tail.

### D-1 — ARCHITECTURE states two slices of stale facts at HEAD (fix: restate §1, §2.5, §5, §6)

E4 sentences that are FALSE at HEAD (line numbers at 7af24b2):

- `:87`–`:88` "`Frag e` … has 28 constructors (`:6340`–`:6543`; dialect arc
  E2)" — 29 at HEAD (`Frag.unseq`; the manifest's own tail says 29; my count
  of `inductive Frag`'s arms: 29).
- `:414` "### 2.5 The nine closed shipped-driver statements", `:423` "All nine
  are pinned" — README `:220`/`:523`, CLAIMS C14 and the E4 record call
  `t1_certified_production` the TENTH closed statement; §2.5's table omits it
  (and, since E1–E3, `exhibitA_prod_e1`/`exhibitB_prod_e2`/`exhibitC_prod_e3`).
  The same count is in WALKTHROUGH `:227` ("one of the nine closed
  shipped-driver statements").
- `:711`–`:713` "At this revision (the manifest's tail line): 28 constructors,
  58 rows — 35 RULE, 0 …, 19 NO-RULE, 4 OUT-OF-SCOPE, 0 red, 20 consumer
  modules (dialect arc E2)" — HEAD: `MANIFEST: 29 constructors, 70 variant rows
  (40 RULE, 0 RULE-TOTAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 25 NO-RULE, 5
  OUT-OF-SCOPE), 0 red, 22 consumer modules` (verbatim, §3.1). Two slices
  stale (E3 did not update it either).
- `:724` "(20 modules: the eighteen program exhibits — `EmittedAExhibit` and
  `EmittedBExhibit` among them …)" — 22 at HEAD (`EmittedCExhibit`,
  `CorpusT1Exhibit`).
- `:742`–`:744` "`BOUNDARY: 22 modules checked …`, … the gate at the E2 head"
  — 24 at HEAD.
- `:750` "(12 rows, 104 names)" — HEAD: `CLAIMS: 14 claim rows, 133 declaration
  names checked in the theorem cell, 287 declaration-shaped spans …`.
- `:763` "Four OUT-OF-SCOPE variants" — five at HEAD (the E3 `PEcall` at an
  `Impl`/unknown-`Sym` name row is missing from the list); `:777` "The
  nineteen NO-RULE variants" — 25 at HEAD; the table under it (`:781`–`:790`)
  has NO `unseq` row although E4 added two NO-RULE `Frag.unseq` rows (the race
  kill; the jump/call under the frame), still lists the annotated-head
  `wseq_tuple` binder as NO-RULE (`:789`; RULE since E4, `wps_wseq_tuple_annot`
  — the row's own text says "E4's `unseq` is what would deliver an annotated
  tuple"), and counts the OUT-OF-SCOPE `Impl` call inside "`pure_op` (6, E3)"
  (the manifest has 5 NO-RULE `pure_op` rows). Its rows sum to the manifest's
  25 by coincidence (3+3+3+4+1+1+4+6 vs 3+3+3+4+1+1+3+5+2).
- `:790` is the only ARCHITECTURE sentence saying the built files have an empty
  `impl` map; §2.5/§6 nowhere say the certified t1 file is the THREE-function
  std.core fragment (KOI A7 is disclosed on README/CLAIMS/WALKTHROUGH, not
  here). The brief asked; adding one sentence to §2.5 with the tenth statement
  closes it.

Premise verified by measurement: yes (manifest tail, boundary line, CLAIMS
line, constructor count). The ratified schedule puts a fresh full review at
this milestone; the review will be marking a document that is wrong about its
own tree at this revision unless these are fixed first.

### D-2 — the owed cite audit (KOI C18): ARCHITECTURE's `file:line` cites — including §2.2's seven "re-measured" ones — are stale at HEAD (fix: one scripted pass before the review)

Scripted check (`.audit-scratch/citecheck4.py`, the script compares each
`X.lean:N` / `:N` cite with the declaration line of the identifier the sentence
names): 248 line-cites into `.lean` files; by declaration-line comparison 67
exact (±1), 36 within ±5, 97 off by more than 5 lines or naming a prose region
the script could not attribute (48 of the 97 are table/prose cites the script
cannot resolve — the exhibit-file cites in §2.1's consumer table and §2.5's
statement table I checked by hand: all exact or ≤3 off). DERIVED; the
identifier attribution is heuristic, so the per-file deltas below are what I
verified by `grep -n` on the declarations:

| File (E4 delta) | cite → actual declaration line |
|---|---|
| Round.lean (§2.2, "re-measured" in ddc2f35) | `CerberusRound` :202→205, `ShippedRefusal` :222→225, `OpenRound` :368→371, `loop_step` :1037→1045, `engine_step_matchU` :1103→1111, `step_iff_cerberusRound` :1872→1880, `frag_round_complete` :6532→6540 — the SAME commit that re-measured them (ddc2f35) added the D-3 docstring lines to Round.lean above them (+3 before :380, +8 after); also `RoundClass` :1890→1925, `shipped_done` :1920→1955, `complete_store` :2628→2719, `complete_ret` :6146→6484, `cerberusRound_classify` :6281→6657 |
| Step.lean (+186 … +938) | `RunSup` :486→672, `Ctl` :514→700, `Config` :629→815, `MachineCtx` :634→820, `callRedex?` :1083→1300, `Step` :2387→3097 (twice), `Step.call` :2879→3626, `ret` :2898→3645, `ret_annot` :2910→3657, `ctl_cases` :3022→3769, `spikeCtl` :4502→5440, `procCtl` :4507→5445, `spikeCtx` :4526→5464, `procCtx` :4534→5472 |
| Soundness.lean (+738 … +1730) | `PePure` :2516→3254, the `Frag` header :6257–:6338 and `Frag` :6339→8069 (three cites), constructors :6340–:6543→8070–8270, `hbsz` :6522→8252 |
| Wps.lean (+3 / +360) | `wps` :316→319, `wps.pre` :228→231, `wps_of_atomic` :371→374, `wps_frame_labels` :722→725, `wps_call` :444→447, `wps_call_root` :494→497; `blockSpecs_intro` :3917→4277, `procSpecs_intro` :4009→4369, `wps_sound_cps` :4164→4524, `wp_ret` :4049→4409, `wp_ret_annot` :4091→4451, `wps_sound` :4359→4719, `wps_sound_empty` :4380→4740 |
| Wpt.lean (+397) | `blockSpecsT_intro` :3708→4105, `procSpecsT_intro` :3765→4162, `wpt_sound_cps` :3903→4300, `wpt_sound` :4114→4511, `wpt_sound_empty` :4133→4530 (`wpt` :200→201, `:167`/`:172`, `wpt_of_atomic` :677, `wpt_frame_labels` :565, `wpt_call` :740, `wpt_call_root` :769 exact) |
| DriverCollapse.lean (+114) | `loop_step_frag'` :2237→2351, `loop_step_frag` :2333→2447, `LabeledProcs` :2396→2510, `CtlTied` :2423→2537, `CtlTied.noproc` :2431→2545, `hjmp` :2248→2362, `loop_zero_exhausts` :2466→2580, `loop_step_done_exhaust` :2477→2591 (`loop_step_done` :392→395) |
| Adequacy.lean (+13) | `DriverSafeCtl` :932→945 (its ties :935–:940), `drive_safe_aux` :1088→1101, `engine_adequacy` :1291→1304, `_alloc` :1357→1370, `CellMap` :1420→1433, `Sat` :1428→1441, `MemTriple` :1531→1544, `project_triple_pure` :1618→1631, `MemTriple_alloc` :1682→1695, `_alloc` :1756→1769, `DeadAt` :1913→1926, the `*_consequence` block :1922→1935 (`LaunchCoh` :422, `ControlOk` :800, `FragProcs` :767, `spike_step_adequacy` :568/:667 exact) |
| ProdLoop.lean (+4, pre-existing — the file is untouched in this range) | `DriverDoneCtl` :477→481, `driverDoneCtl_step` :563→567, `wpt_driver_cps` :638→642, `wpt_driver_done_procs` :839→843, `wpt_driver_aux` :181→185, `wpt_driver_done` :309→313, `_alloc` :377→381 (`DriverDoneAt` :58 exact) |
| ProdEntry.lean (+19) | `prod_run_eqJ_procs` :719→738, `prod_run_safe_procs` :771→790 (`prodFile` :125, `prodFileWith` :545/:550, `prod_run_eqJ` :402, `prodCtl` :568, `prodCtx` :583, `prodMem₀` :212, `prodMem₀_memWF` :243 exact) |
| Potential.lean | `pot` :43→44, `Frag.esize_le_pot` :117→172 |
| Audit.lean | "the trio (`:162`–`:163`)" → `allowedAxioms` at :210 (the E3/E4 header paragraphs pushed it; the pin/sweep cites :45/:437/:730–:731/:820–:831/:832–:851/:852–:868 are exact — D-1 of the E3 audit was applied) |
| Rules.lean, Heap.lean, Layout/exhibits, generated `CerbMem`/`Driver`/`CerbFuel`/`CerbND`/LemLib, scripts | exact (`AtomicStep` :194→196, `wp_of_atomic` :210→212 within 2) |

DERIVED tally of the hand-verified rows: 64 cites off by more than 5 lines, 23
off by 2–5. Premise verified: yes. KOI C18 is accurate but understated: the
seven §2.2 cites it excludes are stale too. Fix: a scripted pass (the check
above, or its like) run as the LAST step of the docs commit, not before the
same commit's own docstring edits.

### D-3 — one README residue of the E3 audit's D-3 (fix: one clause)

`README.md:578` still characterises `eval_uncovered` as "(a procedure-named
symbol, a binop at two floats, `OpEq` at two ctypes)" — the ctype leaf has been
mirrored since E3 and the `stdBudget` member is missing. E4's fix (record §10
D-3) touched README `:682`/`:698` (the divergence table) and missed this second
occurrence in the numbered list. ARCHITECTURE `:289`/`:769`, WALKTHROUGH
`:1551`/`:1862`, `Round.lean:114`/`:380`, `EvalClass.lean:37`/`:223` are
correct at HEAD (checked). Premise verified: yes.

### N-1 — the t1 budget carries undisclosed slack (fix: reword the docstring; a KOI B6 line)

MEASURED on the shipped inner loop from the production entry state
(`prodEntryStateLib stdlibE3 [] 0 t1Main default`, §3.4): the arena is the
delivered value after 40 rounds, fuel 41 is the drain exhaustion, fuel 42
reports PROGRAM-DONE (`acc[0] = [done]`); fuels 30–41 are the exhaustion kill.
`t1_wpt` is at budget 48, so `wpt_driver_done_alloc`'s "within k + 2 = 50
iterations" has 8 units of slack (the exact `k` is 40). Nothing in a statement
claims tightness, but `CorpusT1Exhibit.lean:552`–`:555` says "BUDGET 48 … The
budget is the round count of the run plus the delivered values' costs, rule by
rule", which a reader takes as an exact count; the record §6 (ii) tabulates the
48 as if additive. Same class as KOI B6 (fib_rec +1, even_odd +1, tl_wpt); add
the line and say "an upper bound" in the docstring.

### N-2 — the corpus speedbump's "no opaque position" is not "every token compared": a dead-literal plant passes it (no fix required; a sentence)

Planted (§3.7): the `save` initialiser `a_518 := Specified(0)` transcribed as
`Specified(7)` in `t1Main`/`t1MainWith`, CorpusE0 rebuilt, the skeleton
speedbump run: `| t1.annot.core | main | 121 | equal | …` — the plant PASSES
(literals are leaves, as the CorpusE0 header discloses), and the theorem would
still prove (the initialiser is overwritten by `run ret_507(…)`'s argument and
is not part of the registered `(params, cont)`), so neither instrument nor the
oracle readout would see it. Reverted. Disclosed by design; the record's "NO
opaque position left" (§6 (iii)) and CLAIMS C14's "tied to its text … with NO
opaque position" should not be read as full-text equality — one clause in
C14's freshness cell. My own node-by-node comparison (§2.3) found the
transcription consistent with `t1.annot.core` in every position the text shows.

### N-3 — KOI C16's mover is still open after E4's manifest pass

`docs/CAPABILITY_MANIFEST.md:126` (`Frag.pure_op` OUT-OF-SCOPE) still lists the
E1/E3 members and "a `case` whose selected branch the depth guard rejects" but
not E2's other four (a `case` matching no pattern, `UB088`, a constructor
dispatch failure, an undef-then-raise operand list) that ARCHITECTURE `:294`–
`:302` carries. E4 did not claim it; KOI C16 ("E4's row pass to be checked by
the E4 range audit") is accurate: not completed.

### N-4 — CLAIMS C13 names the retired theorems without backticks

`docs/CLAIMS.md:46`: "E3's witnesses t1_unseq_not_frag and
t1_uncovered_exactly_unseq are RETIRED at E4" — unbackticked, so the D-2 name
check does not see them. Honest here (they are said to be retired), but it is
exactly the spelling by which a stale name would pass the check. Cosmetic;
backtick them and add the two to `claimVocabulary` as retired names, or
rephrase.

### H-1 — the head-form proof scaffold is copied ~45 times; a magic fuel literal

Every `step_ctx_*` lemma in Round/Soundness/DriverCollapse now carries the same
twelve-line scaffold (`have key : … (step_ctx …).head? = some … := by unfold
step_ctx; dsimp only; rw [hget]; simp only [List.map_cons, List.head?_cons]; …`
then `cons_of_head?`). One lemma — the step list is `List.map F (get_ctx …)`
(`step_ctx_length` already states half of it), so its head is `F (ctx, r)` at
the decomposition's head — would carry every instance, and each `step_ctx_*`
would reduce to computing `F (ctx, r)`. Also `get_ctx_action 999999` at four
sites (`engine_complete_storeU`/`loadU`/`createU`/`caseU`, `Soundness.lean`
and `Round.lean`) spells `lemDefaultFuel - 1` as a literal that happens to be
right at the pin. Hygiene (KOI C5/C17 class), no defect.

### H-2 — CorpusT1Exhibit boilerplate (acknowledged: record §5 item 10, KOI C17)

Eight frame abbreviations with fifteen `_sf`/`_lookup_*` lemmas, each a
`decide +kernel` chain; `t1sym_eval` duplicates `symC_eval`; `t1_four_*`
duplicate the `three_*` pattern. The record owns it; not re-cited as new.

## 2. What was verified, by item of the brief

1. **`Eunseq`.** (a) SELECTION. `get_ctx`'s `Eunseq` arm (core_reduction.lem
   :544–548) and `get_ctx_unseq_aux` (:590–601: `zs ++ acc`) read; the mirror's
   `Step.unseq_ctx`/`Decomp.unseq` focus the last component with `valsOnly
   es2`, whose engine twin is `List.all es is_irreducible`
   (`all_irreducible_eq_valsOnly`, `is_irreducible_eq_isValE` — proved by cases,
   the `annot(annot(v))` arm answers `false` on both sides, :197–199). The
   engine's list order MEASURED on the generated `get_ctx` (§3.3): three
   reducible components → `[Cunseq(|es1|=2,…), Cunseq(|es1|=1,…),
   Cunseq(|es1|=0,…)]`; t1's `unseq(loadX, pure(Specified(1)))` →
   `[Cunseq(|es1|=1,|es2|=0), Cunseq(|es1|=0,|es2|=1, nested)]` — the head is
   `pure(Specified(1))`, as `t1_wpt` reduces first; a nested `unseq` contributes
   its own components as a block, last-first (`get_ctx_unseq_aux_focus` states
   exactly the head-of-block form). Running the shipped inner loop for 1, 2, 3
   rounds on `unseq(pure 1, pure 2, pure 3)`: `unseq[false,false,true]`,
   `[false,true,true]`, `[true,true,true]`, then `annot(|ds|=0) pure-node`, then
   the value — the LAST component reduces first and the completion wraps an
   `Eannot []` exactly as `Step.unseq_vals` states. (b) COMPLETION.
   `collectUnseq` vs `one_step_unseq_aux` (:258–275): same two value shapes,
   `do_race fps fps_acc` with the new component's annotations first,
   `combine = ++` in the same order, values reversed at the end; the bridge
   `one_step_unseq_aux_collect` is proved at every fuel ≥ length + 1 and
   `step_ctx_unseq_vals` discharges the engine's `Expr annots (Eannot fps
   (mk_value_e (Vtuple cvals)))` by `rfl` after `loc_split`. (c) THE RACE. The
   shipped composite on `unseq(store(int,x,Specified(1)), store(int,x,
   Specified(2)))` → `killed Undef0 … n=1 ub035=true`; on `unseq(store, load)`
   the same; on `unseq(load, load)` and `unseq(pure, pure)` → `active
   value=Specified(0)` (§3.4). The pinned oracle on `int main(void) { int x;
   return (x = 1) + (x = 2); }` → `Undefined {ub: "UB035_unsequenced_race", …}`
   (§3.5; its Core uses `neg(store …)` — E5's negative actions — so the
   composite probe used positive stores). `complete_unseq_vals` classifies
   exactly this as `ShippedRefusal.killed (Undef0 (locUpdTh an …).current_loc
   [UB035_unsequenced_race])`; the probe's location `other_location(Driver.drive)`
   is the un-updated thread location at my `[]`-annotated node, as the mirror
   says. The racy program IS syntactically in `Frag` (`uncoveredKinds … = []`):
   its round is a proved KILL with no rule to deliver a value (`wpt_unseq_vals`
   needs `collectUnseq … = some`) — fail-closed. (d) `ccallFree` vs `has_ccall`
   (:470–498): `ccallFree e = true → has_ccall_lemFuel n e = false` at every
   `n ≥ esize e` (`ccallFree_has_ccall`, by strong induction; `Ecase`/`Elet`/
   `End` answer `false` on the mirror side where the engine walks in — coarser,
   fail-closed; measured: `ccallFree (case …) = false`, `has_ccall (case … [])
   = false`, `uncoveredKinds` reports `unseq-component-ccall-or-case`). No
   corpus program places a `case`/`let`/`nd` inside an `unseq` (t1.core read;
   the record's claim for t2–t10 not re-read). (e) `is_unseq_with_ccall = false`
   on the fragment is `Decomp.unseq_ccall_false` (gains `hsz` in E4: the
   sibling bound needs the fuel), consumed by `engine_step_matchU`,
   `loop_step_frag_same'` and every `complete_*` action row at `rw [hd.unseq_ccall_false hsz]`.
2. **THE HEAD FORM.** `CerberusRound`/every `ShippedRefusal` arm/both `OpenRound`
   arms/every `step_ctx_*`/`stepDischarge_*`/`loop_step_*` state `s :: post`
   (read in the Round/Soundness/DriverCollapse diffs). `pre = []` is
   `Decomp.get_ctx_at` (head form) built on `get_ctx_unseq_aux_focus`: the
   focused component's contexts head the accumulator at fuel `m - |es1| - 1`
   (the fuel accounting matches the generated definition — `get_ctx_unseq_aux_cons`
   is `rfl`). The loop takes the head: `loop_step_of_advance`/`loop_step_tau`/
   `loop_step_action`/`loop_step_memop`/`loop_step_withrs_*` unfold the loop,
   `runOne_read` the `step_ctx` call, and the `find_can_advance (s :: post)`
   match reduces to `some s` under `can_advance s = true` — proved per lemma,
   never assumed; `CerberusRound.loop_step`/`.runND` thread `post` through.
   Determinism is therefore the engine's own (one advanceable head, one
   `NDactive` transition), and the singleton closed forms (`prod_run_eqJ_lib1`
   → `t1_certified_production`) are unchanged in text (census SAME). The
   singleton readings survive as theorems: `step_ctx_singleton_of_root`
   (length 1 ⇒ `[s]`, via `step_ctx_length`) and `Decomp.get_ctx_single` at
   `ctxNoUnseq`; `overflow_step_ctx` and the `engine_complete_*U` witnesses
   keep `= [s]` (census SAME). `frag_round_complete`, `cerberusRound_classify`,
   `step_iff_cerberusRound`, `engine_step_matchU`: statements SAME; the new
   arms `complete_unseq_vals` (both faces) and the `unseq_vals` case of
   `frag_round_complete` read; `Frag.step` preserves `Frag.unseq` through
   `Step.ccallFree_preserved` (every framed step keeps `ccallFree`; `case`
   rounds excluded by `ccallFree (Ecase) = false`).
3. **THE MILESTONE.** (a) Transcription: the FULL-gate row `| t1.annot.core |
   main | 121 | equal | mismatch (expected) ×4 |` (§3.1); my node-by-node
   comparison of `t1Main` (CorpusE0.lean:960–984) against `t1.annot.core`:
   every annotation marker and its ORDER (`[Astd "§6.5.6", Aloc (t1RegP 36 41
   38), Aexpr]` for the `{-# §6.5.6 #-} {-# <1:36,1:41> 1:38 #-}` pair; `Aloc`
   regions/cursors at every printed location), every binder kind (`let strong`
   = `Esseq`, `let weak` = `Ewseq`, `;` = `Esseq` at the wildcard), `bound`,
   `unseq [t1LoadX, t1Spec1]`, the `case` with its two alternatives and the
   `catch_exceptional_condition_add(__conv_int__, __conv_int__)` branch, the
   `undef(<<UB036>>)` wildcard arm, the `kill`s as `Static0 intTy`, `run
   ret_507(conv_loaded_int(int, a_517))`, the `save … (a_518 := Specified(0))
   in pure(a_518)`, the symbol numbers 505–518 where printed. What a wrong
   transcription could still pass: literals (N-2), ctypes (`'signed int'` as
   `intTy`), memory orders (`NA`), the action/`PEundef`/`PrefSource` locations
   and the unprinted `Astmt`/`Aexpr` tags — the leaves the header declares.
   The value path's literals (3, 1) are pinned by the readout = the oracle. (b)
   Statement vocabulary (`CorpusT1Exhibit.lean:827`–`:835`): `sup fs args`,
   `CerbND.runND (_root_.drive fmapEmpty false (prodFileLib stdlibE3 [] t1Main)
   args) ((initial_driver_state sup (prodFileLib stdlibE3 [] t1Main) fs).1) =
   [(nd_status.Active dres, [], dst')]`, `dres.dres_core_value = lint 4`,
   blocked/stdout/stderr — program, file builder, engine, readout; `lint 4 =
   Vloaded (LVspecified (OVinteger (integerIval 4)))` = `Specified(4)`
   (`stringFromCore_value` prints it so, §3.4). (c) `t1Main_frag` by
   `rw [t1Main_eq_with]; exact t1MainWith_frag _ t1_unseq_frag` (structural,
   no decision procedure); `t1_uncovered_none` by kernel `decide` (gate 1: no
   `native_decide`; axioms `[propext]`, §3.6). (d) Oracle: `Defined {value:
   "Specified(4)", stdout: "", stderr: "", blocked: "false"}` and exit 4
   (§3.5, verbatim). (e) Route read: `t1_wpt` (48 = 3+3+3+4+15+4+7+3+3+3,
   the `unseq` as `wpt_unseq_focus 2 9` then `wpt_unseq_focus 6 3` then
   `wpt_unseq_vals` at 3) → `wpt_driver_done_alloc` (`t1Main_frag`,
   `t1Main_pot` by `decide`, `prod_two_int_budget_fits` by `decide`,
   `prodMem₀_launchCoh`) → `prod_run_eqJ_lib1` with `48 + 2 ≤ driverFuel`;
   the measured round count is N-1. (f) The file: `prodFileLib stdlibE3 []
   t1Main` = `prodFileWith [] t1Main` with `stdlib := stdlibE3` — the engine
   reads `stdlib` in `call_function` (the three functions t1 reaches) and in
   `lookupProc` (`hmain`); KOI A7 is exact and disclosed on README `:196`–
   `:200`, CLAIMS C13, WALKTHROUGH `:1816`–`:1819`; NOT in ARCHITECTURE (D-1).
4. **Rule faces.** `wps_unseq_focus`/`wpt_unseq_focus`: Löb / strong-induction
   bind rules under the `Cunseq` frame; the step case uses `Step.unseq_ctx`
   for progress and `Step.unseq_inv` + `focus_unique` to identify the successor
   (the value/jump/call arms of the inversion refuted by `valsOnly_append_cons_false`
   and the `hjr`/`hcr` premises); the value case hands `∀ wa, ⌜wa.erase = w⌝ -∗`
   the exact node (erase keeps the dynamic annotations, drops the static
   lists — what the completion needs). Reynolds/O'Hearn-clean: the focused
   component owns its resources, siblings are inert values, no hidden premise.
   Budgets: `k1 + k2`; `fupd_wpt_nonval` at `k ≤ k'`, `1 ≤ k'`. `wps_unseq_vals`/
   `wpt_unseq_vals` (`3 ≤ k` = the TAU + `deliveryCost_annot` 2) at
   `Ψ (.annot fps (Vtuple cvals))` — the engine's own successor. `wps_wseq_tuple_annot`/
   `wpt_…`: LETW-ANNOT (core_reduction.lem:397–405) — continuation `Expr []
   (Eannot ds e2)` at `update_env (tuplePat pa ls) (Vtuple vs) ρ'`, verbatim the
   engine's `TAU "Ewseq Eannot" (update_env pat cval env) (Expr [] (Eannot xs
   e2))`. `wps_pure`/`wpt_pure` generalised to `Expr a (Epure pe)`: the old
   statement is the instance `a := []` (conservative); recorded in the E4
   record §4 and DECISIONS. `wpt_jump_frame_unseq`: the jump discards the
   frame, as `Step.run` at the descended `jumpRedexU?`.
5. **Census.** Pre: the R-1 regeneration commit 77884f4 adds exactly the eight
   lines `theorem CerberusHeapLang.unspec_bytes …` / `theorem
   CerberusHeapLang.unspec_paddingByte …` (`git show 77884f4`, verbatim in
   §3.2) — the two entries the E3 audit measured missing — and the file is
   39418 lines, the E3 audit's fresh count at 825b5e6; I did not rebuild
   825b5e6 and trust that diff. Post: my HEAD snapshot `cmp`-identical to
   `docs/2026-09-05_e4-signatures-post.txt` (§3.2). Census by my own script over
   the two committed files (DERIVED): pre 4164, post 4362, ADDED 200 (155
   theorems, 29 defs + 7 opaques, 9 constructors), REMOVED 2
   (`CorpusE0.t1_uncovered_exactly_unseq`, `CorpusE0.t1_unseq_not_frag`),
   CHANGED 162. Partition: my heuristic gives 131 head-form + 28 recursors/
   equations + 3 other (`Decomp.unseq_ccall_false` — gains `hsz`, disclosed —
   `wps_pure`, `wpt_pure`); the record's 138 + 2 + 22 counts the six
   `OpenRound`/`ShippedRefusal` recursors and `unseq_ccall_false` in the
   head-form class — the same 162, a classification boundary. The NINE
   production statements, `exhibitA_prod_e1`, `exhibitB_prod_e2`,
   `exhibitC_prod_e3`, `frag_round_complete`, `cerberusRound_classify`,
   `step_iff_cerberusRound`, `engine_step_matchU`, `overflow_step_ctx`,
   `overflow_driver2_killed(_frame)`: all SAME (§3.2). Pins: `trioExports` has
   650 entries, 650 distinct; 589 at 825b5e6; the 62 added are all among the
   155 added theorems, the 1 removed is `t1_unseq_not_frag`; trio-exactness of
   all 650 is the in-build assertion (§3.1). Sub-trio spot-checks (seven, §3.6)
   match the record's listing.
6. **The E3 fixes** — §4 table; D-2's name-check extension planted twice (§3.7:
   a stale name in C14's prose cell → RED; in C11's claim cell → RED; the
   internal plant runs on every invocation — code read, `plantRow` evaluated
   unconditionally); the `save`-initialiser tokenizer's plant runs in the gate
   (row column 8 `mismatch (expected)`).
7. **Shop window at HEAD.** README/WALKTHROUGH/CLAIMS: E4 sentences true
   (`SYNTHETIC` for EmittedC and `stdlibE3`; EmittedA/B synthetic in their
   module headers and CLAIMS C12 says "verbatim exhibit A's shape"; CorpusT1
   "the first over an EMITTED program" in its header, README `:220`/`:523`
   "TENTH"); manifest header 70 rows / 22 consumers, `MODULES: 49 classified`;
   `Audit.lean` cites exact (E3 D-1 applied). ARCHITECTURE: D-1/D-2.
8. **Records.** FULL gate once (§3.1): line for line identical to the DECISIONS
   E4 entry's quoted tail (650 / 5055 / 7812 / 466 jobs / 17 core / 24
   modules / ALL GATES GREEN; exit 0). DECISIONS chronological; the E4 entry's
   counts match the tree except the 62/93 split (R-1). KOI A7/B15–B17/C17/C18
   accurate (C18 understated, D-2; C16 N-3).
9. **Grumpy read.** `Step`'s two rules and the vocabulary (`isValE`, `valsOnly`,
   `focus_exists`/`focus_unique`, `ccallFree`, `collectUnseq`) are clear and
   well-cited; `Step.unseq_inv` is the right inversion. The head-form scaffold
   is H-1. `saveInits`/`cutInit`/`skipTypeToAssign` are a clean small tokenizer
   (quoted literals copied whole, `{-#` inside an initialiser an error, depth-0
   `:=` only). Linter warnings: 60 in the gate log, distribution Potential 46 /
   Round 5 / Rules 2 / Heap 2 / EnvLaws 2 / TreeRot, Struct, ProdLoopExhibit 1
   — the baseline; none in an E4 module.

## 3. Plant/probe log (verbatim)

### 3.1 FULL gate at 7af24b2 (`CERB_MEM_MAX=64G scripts/test_unit.sh`, tree pre-built; lines matching `^==|^ok:|^info: CerberusHeapLang|^ALL GATES|^GATE-EXIT|^Build completed|^BOUNDARY|^ALLOWLISTED|^FAIL|^EXIT`, plus `time`'s line)

```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:818:0: CerberusHeapLang export pins: 650 trio-exact
info: CerberusHeapLang/Audit.lean:818:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (5055 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:818:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (7812 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (466 jobs).
ok: cerberus-heaplang build green
== speedbump: rule-use and classification manifest (regenerate; red on a red row or drift) ==
ok: capability manifest regenerated, no drift
== speedbump: corpus skeleton (hand-transcribed emitted Core vs docs/corpus-e0; scripts/corpus_skeleton.lean) ==
ok: corpus skeleton — every transcription matches its emitted text, every plant mismatches
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — 17 core modules, none imports an exhibit/example/production module
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
ok:   Examples.CallSmoke — 0 internals mentions
ok:   Examples.ReadinessSmoke — 0 internals mentions
ok:   Examples.Layout — 0 internals mentions
ok:   Examples.CorpusE0 — 0 internals mentions
BOUNDARY: 24 modules checked, 0 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
CERB_MEM_MAX=64G scripts/test_unit.sh  10.48s user 1.38s system 102% cpu 11.540 total
EXIT=0
```

Other lines of the same log: the skeleton table row
`| t1.annot.core | main | 121 | equal | mismatch (expected) | mismatch (expected) | mismatch (expected) | mismatch (expected) |`,
`corpus-skeleton: ok — 1 corpus row(s) and 3 std.core row(s) equal, every plant mismatches`;
the regenerated manifest's tail (also `docs/CAPABILITY_MANIFEST.md:161`–`:162`):
`MANIFEST: 29 constructors, 70 variant rows (40 RULE, 0 RULE-TOTAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 25 NO-RULE, 5 OUT-OF-SCOPE), 0 red, 22 consumer modules`,
`CLAIMS: 14 claim rows, 133 declaration names checked in the theorem cell, 287 declaration-shaped spans checked across every cell (45 vocabulary words); plant (deleted name in a prose cell) red as expected`.
Package linter warnings in the log: 60 (`warning: … CerberusHeapLang/`), by module as in §2.9.

### 3.2 Snapshots and census

```
$ ../scripts/capped ~/.elan/bin/lake env lean scripts/signature_snapshot.lean > ../.audit-scratch/head-signatures.txt   (40.723 s wall)
$ cmp ../.audit-scratch/head-signatures.txt docs/2026-09-05_e4-signatures-post.txt && echo CMP-IDENTICAL
CMP-IDENTICAL
$ git show 77884f4 -- docs/2026-09-05_e3-signatures-post.txt | grep "^[+-]" | grep -v "^+++\|^---"
+theorem CerberusHeapLang.unspec_bytes :
+∀ (tds : CerbTags.TagDefsMap),
+  (CerbMem.memValueToBytes tds [] CerberusHeapLang.unspecMval).snd =
+    CerberusHeapLang.intUndefBytes tds
+----
+theorem CerberusHeapLang.unspec_paddingByte :
+CerbMem.paddingByte = CerberusHeapLang.undefByte
+----
$ python3 .audit-scratch/census.py docs/…e3-signatures-post.txt docs/…e4-signatures-post.txt
pre 4164 post 4362
ADDED 200 REMOVED 2 CHANGED 162
REMOVED: ['CerberusHeapLang.CorpusE0.t1_uncovered_exactly_unseq', 'CerberusHeapLang.CorpusE0.t1_unseq_not_frag']
ADDED kinds: Counter({'theorem': 155, 'def': 29, 'ctor': 9, 'opaque': 7})
head-form-forced 131
recursors/equations 28 [… 'CerberusHeapLang.OpenRound.casesOn', '…OpenRound.rec', '…OpenRound.recOn', … '…ShippedRefusal.casesOn', '…ShippedRefusal.rec', '…ShippedRefusal.recOn', … '…callRedex?.eq_def', '…esize.eq_def', '…jumpRedex?.eq_def', '…pot.eq_def']
OTHER 3 ['CerberusHeapLang.Decomp.unseq_ccall_false', 'CerberusHeapLang.wps_pure', 'CerberusHeapLang.wpt_pure']
exhibitA_prod SAME … even_odd_certified_production SAME  exhibitA_prod_e1 SAME  exhibitB_prod_e2 SAME  exhibitC_prod_e3 SAME
frag_round_complete SAME  cerberusRound_classify SAME  step_iff_cerberusRound SAME  engine_step_matchU SAME
overflow_step_ctx SAME  overflow_driver2_killed SAME  overflow_driver2_killed_frame SAME
```

Pins: `trioExports` at HEAD 650 entries, `sort | uniq -d` empty; at 825b5e6 589;
`comm` → 62 new, 1 removed (`CerberusHeapLang.CorpusE0.t1_unseq_not_frag`).

### 3.3 The generated engine at an `unseq` (scratch `Probe.lean`, `lake env lean` under `capped`, 1.4 s)

```
get_ctx u3 (3 reducible): [Cunseq(|es1|=2,|es2|=0,inner=CTX), Cunseq(|es1|=1,|es2|=1,inner=CTX), Cunseq(|es1|=0,|es2|=2,inner=CTX)]
get_ctx u2 (t1's unseq: [loadX, pure(Specified 1)]): [Cunseq(|es1|=1,|es2|=0,inner=CTX), Cunseq(|es1|=0,|es2|=1,inner=nested)]
get_ctx u4 (nested): [Cunseq(|es1|=2,|es2|=0,inner=CTX), Cunseq(|es1|=1,|es2|=1,inner=nested), Cunseq(|es1|=1,|es2|=1,inner=nested), Cunseq(|es1|=0,|es2|=2,inner=CTX)]
get_ctx uv ([reducible, value]): [Cunseq(|es1|=0,|es2|=1,inner=CTX)]
valsOnly / is_irreducible on t1Spec1, t1LoadX: false false false
step_ctx list at u3: [withrs, withrs, withrs]
rounds on u3: [killed:lem: fuel exhausted arena=unseq[false, false, false], killed:lem: fuel exhausted arena=unseq[false, false, true], killed:lem: fuel exhausted arena=unseq[false, true, true], killed:lem: fuel exhausted arena=unseq[true, true, true], killed:lem: fuel exhausted arena=annot(|ds|=0) pure-node, killed:lem: fuel exhausted arena=pure-node]
```

(`u3 = unseq(pure(Specified 1), pure(Specified 2), pure(Specified 3))`;
`u4 = unseq(pure 1, unseq(pure 2, pure 3), pure 4)`; `uv = unseq(pure 1, v)`.
"rounds on u3" runs `drive_nonmemory_steps_aux2_lemFuel fl` for fl = 0..5 from
`prodEntryStateLib stdlibE3 [] 0 u3 default`; the exhaustion verdict is the
loop's at spent fuel — the arena column is the evidence.)

### 3.4 The shipped composite and the shipped inner loop

```
composite on unseq(store x 1, store x 2) : [killed Undef0 loc=other_location(Driver.drive) n=1 ub035=true]
composite on unseq(store x 1, load x)    : [killed Undef0 loc=other_location(Driver.drive) n=1 ub035=true]
composite on unseq(load x, load x)      : [active value=Specified(0) blocked=false out=""]
composite on unseq(pure 1, pure 2)      : [active value=Specified(0) blocked=false out=""]
composite on t1Main: [active value=Specified(4) blocked=false out=""]
t1 rounds (inner loop fuel fl → verdict): [fl=30: killed:lem: fuel exhausted arena=annot(|ds|=2) other, … fl=38: killed:lem: fuel exhausted arena=annot(|ds|=2) other, fl=39: killed:lem: fuel exhausted arena=pure-node, fl=40: killed:lem: fuel exhausted arena=pure-node, fl=41: killed:lem: fuel exhausted arena=pure-node, fl=42: active acc[0]=[done] arena=pure-node, fl=43: active acc[0]=[done] arena=pure-node, fl=44: active acc[0]=[done] arena=pure-node, fl=45: active acc[0]=[done] arena=pure-node]
uncoveredKinds t1Main = []; uncoveredKinds (wrap unseq(store,store)) = []
ccallFree on a case component: false, has_ccall: false; uncoveredKinds: [unseq-component-ccall-or-case, case]
```

(the composite = `CerbND.runND (drive fmapEmpty false (prodFileLib stdlibE3 []
p) []) (initial_driver_state 0 (prodFileLib stdlibE3 [] p) default).1`; the
`store`/`load` programs are `let strong x = create(…) in store(int,x,7) ;
bound(unseq(…)) ; kill(x) ; pure(Specified(0))` with `[]`-annotated nodes;
"pure-node" covers `pure(a_518)` and the delivered value — the value is
reached after 40 rounds, fuel 41 is the drain exhaustion, 42 PROGRAM-DONE.)

### 3.5 The pinned OCaml oracle (from the container root; commands verbatim; `scripts/ce` prints its environment line on stderr)

```
$ scripts/ce cerberus-lean/_build/default/backend/driver/main.exe --nolibc --exec --batch refined-cerberus/worktrees/audit-e4-7af24b2/docs/corpus-e0/t1.c
Defined {value: "Specified(4)", stdout: "", stderr: "", blocked: "false"}
Time spent: 0.040035 seconds
exit=0
$ scripts/ce cerberus-lean/_build/default/backend/driver/main.exe --nolibc --exec refined-cerberus/worktrees/audit-e4-7af24b2/docs/corpus-e0/t1.c
exit=4
$ scripts/ce cerberus-lean/_build/default/backend/driver/main.exe --nolibc --exec --batch refined-cerberus/worktrees/audit-e4-7af24b2/.audit-scratch/oracle/race.c
Undefined {ub: "UB035_unsequenced_race", stderr: "", loc: "<1:32--1:49>"}
Time spent: 0.039596 seconds
exit=1
$ scripts/ce cerberus-lean/_build/default/backend/driver/main.exe --nolibc --exec refined-cerberus/worktrees/audit-e4-7af24b2/.audit-scratch/oracle/race.c
refined-cerberus/worktrees/audit-e4-7af24b2/.audit-scratch/oracle/race.c:1:32: error: undefined behaviour: an unsequenced race occurs during the evaluation of an expression
int main(void) { int x; return (x = 1) + (x = 2); }
                               ~~~~~~~~^~~~~~~~~ 
§6.5#2: …
exit=0
```

(`race.c` = `int main(void) { int x; return (x = 1) + (x = 2); }`; its
`--pp=core` places each assignment in an inner `unseq(pure(x), pure(Specified(n)))`
with `neg(store(…))` — E5's shape, so the composite race probe (§3.4) used
positive stores.)

### 3.6 Axioms

```
'CerberusHeapLang.t1_certified_production' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.Step.unseq_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusE0.t1_uncovered_none' depends on axioms: [propext]
'CerberusHeapLang.Decomp.get_ctx_single' depends on axioms: [propext, Quot.sound]
'CerberusHeapLang.one_step_unseq_aux_collect' depends on axioms: [propext, Quot.sound]
'CerberusHeapLang.get_ctx_unseq_aux_focus' depends on axioms: [propext, Quot.sound]
'CerberusHeapLang.cons_of_head?' does not depend on any axioms
'CerberusHeapLang.t1Main_pot' depends on axioms: [propext]
'CerberusHeapLang.ccallFree_has_ccall' depends on axioms: [propext, Quot.sound]
```

All 155 added theorems (`Axioms.lean`, 1.2 s):
`trio-exact 64 sub-trio 91 OTHER []`;
`trio-exact but NOT pinned: ['CerberusHeapLang.unseq_focus_round', 'CerberusHeapLang.unseq_vals_round']`;
`pinned but not trio-exact: []`; `new pins not among added theorems: []`.

### 3.7 Plants

```
== PLANT 1: stale name t1_unseq_not_frag in C14 prose cell (Known exclusions) ==
MANIFEST: 29 constructors, 70 variant rows (40 RULE, 0 RULE-TOTAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 25 NO-RULE, 5 OUT-OF-SCOPE), 1 red, 22 consumer modules
- **RED**: docs/CLAIMS.md C14 (cell 6): `t1_unseq_not_frag` is declaration-shaped but is neither a constant of the environment (`CerberusHeapLang.`/root/`CerbND.`) nor a `claimVocabulary` word
scripts/capability_manifest.lean:550:0: error: capability manifest: 1 red finding(s) — see the table and PROBLEMS above
== PLANT 2: stale name t1_uncovered_exactly_unseq in C11 claim cell ==
exit=1
- **RED**: docs/CLAIMS.md C11 (cell 1): `t1_uncovered_exactly_unseq` is declaration-shaped but is neither a constant of the environment (`CerberusHeapLang.`/root/`CerbND.`) nor a `claimVocabulary` word
== unplanted rerun ==
exit=0   (output identical to docs/CAPABILITY_MANIFEST.md)
== skeleton with the dead save-initialiser literal changed 0 → 7 (CorpusE0 rebuilt, 1.6 s) ==
| t1.annot.core | main | 121 | equal | mismatch (expected) | mismatch (expected) | mismatch (expected) | mismatch (expected) |
corpus-skeleton: ok — 1 corpus row(s) and 3 std.core row(s) equal, every plant mismatches
```

Both CLAIMS plants reverted (`git status` clean); the CorpusE0 plant reverted
and the module rebuilt at the original text.

### 3.8 Cite check

`python3 .audit-scratch/citecheck4.py` → `line-cites into .lean files: 248;
exact(±1) 67; near(±5) 36; STALE(>5 lines off) 97; undetermined 48` (DERIVED,
heuristic attribution; the hand-verified table is D-2).

## 4. The E3-fix verification table

| id | claimed where | verified at HEAD | verdict |
|---|---|---|---|
| report copied | 1878398 | `docs/2026-09-05_audit-e3-range.md` present, 542 lines | applied |
| R-1 snapshot | 77884f4 | +8 lines = exactly the two E2-fix entries the E3 audit found missing; 39418 lines = its fresh count | applied (by the diff, not by rebuilding 825b5e6) |
| D-1 Audit.lean cites | ddc2f35 | `:45`, `:437`, `:730`–`:731`, `:820`–`:831`, `:832`–`:851`, `:852`–`:868` are the cited texts (`sed -n`) | applied |
| D-2 deleted names as current | 0f8d390, ddc2f35 | no `t1_case_uncovered`/`t1_convLoadedInt_uncovered`/`t1_uncovered_exactly_unseq`/`t1_unseq_not_frag` as current state on README/ARCHITECTURE/WALKTHROUGH/CLAIMS (ARCHITECTURE `:536` and CLAIMS C13 name them as removed/retired); name check extended to every cell, planted internally each run, planted externally by me twice → RED | applied (N-4 cosmetic) |
| D-3 `eval_uncovered` on five surfaces | ddc2f35 | ARCHITECTURE `:289`/`:769`, WALKTHROUGH `:1551`/`:1862`, `Round.lean:114`/`:380`, `EvalClass.lean:37`/`:223` correct; README `:682`/`:698` correct; README `:578` NOT | applied except one README residue (D-3 above) |
| D-4 KOI | orchestrator, 7af24b2 | A7, B15–B17, C16–C18 present | applied |
| D-5 §7 Goal 2 | ddc2f35 | ARCHITECTURE `:846`–`:849` cite the e1–e4 closure records | applied |
| D-6 synthetic file / synthetic exhibit | 0f8d390, ddc2f35 | README `:196`–`:200`, WALKTHROUGH `:1816`–`:1819`, CLAIMS C13 | applied (ARCHITECTURE not, D-1) |
| D-7 "every fuel" | ddc2f35 | `OverflowExhibit.lean:25`, `:45`, `:140`, `:194` say "every POSITIVE fuel"; E3 record §12 erratum | applied |
| R-2 option letter | ddc2f35 | E3 record §12 erratum (option (b)); KOI D | applied |
| R-3 arity row | ddc2f35 | closure-e3 row now `OpenRound.eval_uncovered`, marked | applied |
| R-4 (a)(b)(c) | ddc2f35, 0f8d390 | §8 duplicate gone (diff shows the 25-line removal); §11 HEAD tail appended verbatim with the pre-rebase marker; script summary names both counts | applied |
| R-5 upstream cite | ddc2f35 | `impl:17`–`:19` | applied |
| N-1 C11 order | 0f8d390 | C10, C11, C12, C13, C14 | applied |
| H-1 hygiene | not done, KOI C17 | as recorded | not claimed |

## 5. What I did NOT check

- The 30 per-constructor `complete_*`/`engine_step_matchU` arms individually
  beyond the E4-touched ones (`unseq_vals`, the `unseq_ccall_false hsz`
  threading, the `step_ctx_singleton_of_root` rewrites) — read at the diff
  hunk level; the build is the evidence for the rest.
- A cache-disabled rebuild of the tree (the gate replayed the primed build);
  the axiom pins/sweep are therefore the replayed `info` lines of the same
  Audit.lean at HEAD — the `.olean`s were built from this tree, but I did not
  force `lake build` to recompile.
- Whether t2–t10 place a `case`/`let`/`nd` inside an `unseq` (the record's
  claim; only t1.core and race.c's Core were read).
- The record's build-cost sentences (§9) and the claim that no heartbeat/
  `maxRecDepth` option was set (grep not run).
- The oracle on a program whose `unseq` has three or more reducible components
  (the generated engine's `get_ctx` was probed instead; both are the same
  `.lem` at the pin).
- ProdLoopExhibit/DisposeExhibit/… production-statement bodies (unchanged in
  the range; census SAME).
