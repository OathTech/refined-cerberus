# Range audit L2 (the re-pin): `f1f2573..d8ebad9` — 7 commits

**VERDICT: PASS WITH FIXES REQUIRED — A− on the logic and the pin/statement discipline (no T-, no C- finding); the records and shop-window surfaces at HEAD carry stale and mutually inconsistent sentences that must be fixed before the merge ask (R-1, D-1..D-6, H-1).**

[AGENT auditor 2026-09-07] Fresh, independent range audit in the fixed detached copy
`worktrees/audit-l2-d8ebad9` (HEAD `d8ebad9ec35fba3c5380c724d64fc6440f259690`, detached;
`.cerberus-ws` primed at cerberus-lean `89f7e688530c6910884518811d645e4e892e4507`, LemLib
`f6542f8e6860d12d4655e6648bc4c45dabd1d798`). Nothing committed; nothing outside this copy
touched (the sibling checkouts read-only). Every lake/lean invocation went through
`scripts/capped` at `CERB_MEM_MAX=40G`; no build pass exceeded 35 s (the package was
already built; all 483 jobs replayed). Brief: `docs/AUDIT-BRIEF.md`; register read first:
`docs/KNOWN-OPEN-ITEMS.md` — an entry is cited below only where it is wrong at HEAD.
Quoted outputs are verbatim; tallies marked DERIVED are mine.

Grading frame used: a gap in the logic or its coverage is High; a record/doc sentence that
is false at HEAD is D- (the shop-window rule: "the system as it IS"); a derived tally
stated as fact and wrong is R-; a new linter warning or a statement-hygiene defect is H-;
a possible-in-principle gate bypass with no instance in the tree is a Note.

## 0. Summary of what was verified by measurement (all PASS)

| Item | Result |
|---|---|
| The pin | `scripts/setup-cerberus-dep.sh --check`: `A ok: workspace at pinned commit` / `C ok: 37 hand-written seams byte-identical to the pin`; `.cerberus-ws` HEAD = `89f7e688…`; `cerberus-heaplang/lake-manifest.json` LemLib `rev` = `f6542f8e…`; `.lake/packages/LemLib` HEAD = `f6542f8e…`; six generated files (`Driver`, `Core_eval`, `Core_aux`, `Core_reduction`, `Nondeterminism`, `CerbND`) `cmp`-IDENTICAL to the sibling's `lean_frontend/generated/` |
| Gate 1b | tree green; `--selftest` `SELFTEST OK (5 plants: 3 red as required, 2 positive controls green)`; my plants: statement RED, proof RED (+ four leaks, Notes §3 H-2) |
| The shipped corollaries | thirteen, all `letI : LemFuel := ⟨100000000⟩` in the STATEMENT, side condition `show _ ≤ 100000000; omega`; `fib_rec_…_shipped` via `fibRounds_mono hn'` + `fibRounds_33` (`decide` only on the linear `fibPair 33`); no `decide` on the numeral anywhere (read `Shipped.lean` in full) |
| R2 | `Frag` (`Fragment.lean:491`) has no fuel binder; 20 pinned exports + the unpinned `wpt_driver_done_alloc` carry `evalDepth … ≤ LemFuel.fuel`/`ProcsDepth LemFuel.fuel`; **0 pinned statements mention `FragFuel`/`FragProcsFuel`/`fragFuel_iff`** (`Expr.find?` over all 907 pinned types, my sweep); no `*_fuel` device is pinned |
| Pins | my own `collectAxioms` sweep: `trioExports length 901, distinct 901`; `AUDITOR SWEEP: trio-exact 901/901; axiom-free-exact 6/6; mismatches 0` |
| Snapshot | `scripts/signature_snapshot.lean` re-run at HEAD (32.6 s): `SNAPSHOT cmp-IDENTICAL` to `docs/2026-09-07_l2-signatures-post.txt` (52222 lines) |
| Census totals | pre 4950 / post 5212; ADDED 283 / REMOVED 21 / CHANGED 1483 reproduced exactly by my own classifier; the 21 REMOVED all explained (§5) |
| Oracle | t1 `Specified(4)`, t4 `Specified(10)`, t5 `Specified(1)`, t6 `Specified(20)`, t2 `Specified(3)`, t3 `Specified(4)`, t10 `Specified(1)`, each `exit=0` (§6, with the binary caveat verbatim) |
| FULL gate | `scripts/test_unit.sh` re-run: tail IDENTICAL line for line to the DECISIONS L2 entry (mechanical `diff`, §7); `ALL GATES GREEN`, `GATE-EXIT=0` |
| Cite check | reproduces `301 cites; EXACT 233; DECL 16 … USE 14; HAND 22; PIN 16; NOFILE 0; RANGE 16`; twelve non-EXACT cites hand-checked, all correct (§8) |
| FUEL.md cites | all 44 generated-code cites of §1/§4 and the 5 LemLib cites land on the named declaration (§4) |
| Heartbeat bumps | none at HEAD, none at `f1f2573` (`grep maxHeartbeats|maxRecDepth|synthInstance.max*`) |

## 1. Findings, ranked

No T- (trust) and no C- (coverage/logic) finding. The exports' referents are the genuine
semantics at this pin; every proof method is kernel-only; the fragment is syntactic; the
depth hypothesis is proved sufficient (`aux2_bridge`, `full_eval_bridge`) and measured in
the right direction (§4.3); the closed partial forms are unconditional at every ambient
budget (§4.4).

### R-1 — The pin accounting in the record, ARCHITECTURE §3 and DECISIONS is false (premise verified by measurement: YES)

Record §7: "`Audit.lean`: 893 → 901 trio-exact (the thirteen `*_shipped`, `peDepth_subst`,
`evalDepth_subst`; the L1 count 893 kept — every re-pinned export stays trio-exact …); the
six axiom-free-exact pins unchanged (the class is kept …)". ARCHITECTURE §3 (`:622`–`:624`):
"901 exact pins … the L1 head's 893 plus the thirteen `*_shipped` corollaries and the two
depth-stability lemmas". 893 + 15 = 908 ≠ 901. Measured (`git show f1f2573:…/Audit.lean`
vs HEAD, distinct ``-names): pre 893, post 907 (= 901 trio + 6 axiom-free).

- REMOVED pins (4): `drive_after_setup_lib_lemFuel`, `drive_after_setup_with_lemFuel`,
  `t4Q_pot`, `t6Q_pot`.
- RECLASSIFIED (6): `procCtxF_runState_labeled`, `procCtxF_sym_supply`,
  `procCtx_runState_labeled`, `procCtx_sym_supply`, `prodThread_eq_ctlThread`,
  `prodCtx_extern` moved from `trioExports` to a NEW list `axiomFreeExports`. The class did
  not exist at L1: the L1 gate line is `export pins: 893 trio-exact` (DECISIONS, the L1
  entry), so "the six axiom-free-exact pins unchanged" is wrong — the class arrives with the
  cherry-pick (landability audit §3.5 described it on the branch).
- ADDED pins (18): the thirteen `*_shipped`, `peDepth_subst`, `evalDepth_subst`, AND
  `drive_after_setup_lib_one`, `drive_after_setup_with_one`, `errno_init_eq` (not named).

893 − 4 − 6 + 18 = 901. Trust impact: none (my sweep 901/901, 6/6). Fix: rewrite the
record §7 "Pins." paragraph and ARCHITECTURE `:622`–`:624` with this accounting; a DECISIONS
erratum line ("later governs").

### R-2 — "twenty-three exports restated" is 21 (premise verified: YES)

Record §3 (`:102`) and DECISIONS (`:3310` "23 exports restated over `Frag e` + a depth
hypothesis"). The record's own table lists 21 names; measured: 20 pinned statements carry
`evalDepth … ≤ LemFuel.fuel`/`ProcsDepth LemFuel.fuel` (`cerberusRound_classify`,
`driverDoneCtl_step`, `engine_adequacy`, `engine_adequacy_alloc`, `engine_step_matchU`,
`frag_round_complete`, `loop_step_frag`, `loop_step_frag'`, `loop_step_frag_same`,
`loop_step_frag_same'`, `project_triple`, `project_triple_alloc`, `project_triple_pure`,
`project_triple_pure_alloc`, `semantic_frame`, `semantic_triple_sound`,
`step_iff_cerberusRound`, `wpt_driver_cps`, `wpt_driver_done`, `wpt_driver_done_procs`) plus
`wpt_driver_done_alloc`, which the record calls an export but which is NOT pinned (never
was). Fix: "twenty-one" in both places; say `wpt_driver_done_alloc` is unpinned.

### D-1 — README's Fuel row contradicts FUEL.md, WALKTHROUGH and the generated code on `to_pure` (premise verified: YES)

`cerberus-heaplang/README.md:787` (the divergences table, Fuel row), verbatim: "On the
fragment's proved path only `hack` (generated `Driver.lean:438`, the value read-back of
`finalize`, `:469`) is reached, and it is excluded by `0 < LemFuel.fuel` (…); … `to_pure`/
`to_pures` only from the Core rewriter (`Core_rewrite.lean`), which the driver does not call
— none from a `Frag` program's run". FALSE: `finalize` (generated `Driver.lean:469`)
reads the arena through `to_pure` — `match  to_pure  th_st.arena with  |  some  pe => pe`
— exactly as FUEL.md §4 (`to_pure | (D) | … ON THE PATH: finalize (Driver.lean:469)`),
`finalize_done` (`DriverCollapse.lean:677`, which unfolds `to_pure` at `fuel + 1`) and
WALKTHROUGH `:1760` say. The load-bearing exhaustion account is stated three ways and the
README's is wrong. Fix: README row → "`hack` AND `to_pure` at `finalize`, both (D), both
excluded by `0 < LemFuel.fuel` (`hack_value`, `finalize_done`)".

### D-2 — The narrowing of two production statements is under-disclosed on the normative surface (premise verified: YES)

Measured (word-diff of the two snapshots): `region_loop_certified_production` gained
`0 < al → 0 ≤ sz →`; `malloc_list_certified_production` gained `0 < al →` (plus the
`[LemFuel]` binder and `driverFuel → LemFuel.fuel` on both). This IS a weakening of what
is claimed: at pin `f95ef8d9c` the engine clamped (`allocator` docstring at the pin,
`CerbMem.lean`: "the two callers used to clamp size and align with `.max 1` and map a
negative size to 0 through `.toNat` — silent normalisations the OCaml has nowhere; both
gone"), so the theorems covered every `al` and `sz`; at `89f7e68` `allocator` panics at
`align == 0` and lets a negative size through, so the coverage over `al ≤ 0` / `sz < 0` is
gone. The narrowing is FORCED by the engine (Z2 manifest row `CerbMem`: "NEW `allocator`
…; `allocateRegion` ignores `pref`") and correctly done. Disclosure: README rows `:603`
/`:612` list `0 < al`, `0 ≤ sz` ✓; the record §6 ✓; but ARCHITECTURE §2.5's premise table
— the normative "thirteen closed statements" table — omits them:
`:527` `| region_loop_certified_production | RegionLoopExhibit.lean:612 | hcost : 0 < regionCost al sz, hn, hB : …, hfuel : 7 * n.toNat + 5 ≤ LemFuel.fuel |`
`:528` `| malloc_list_certified_production | MallocListExhibit.lean:1672 | hn, hB : …, hfuel : 25 * n.toNat + 9 ≤ LemFuel.fuel |`;
the DECISIONS L2 entry says "gained `0 < al`" and omits `0 ≤ sz`; KOI B21 lists the RULES
but does not name the two production statements. Fix: add `hal : 0 < al`, `hsz : 0 ≤ sz`
/ `halign : 0 < al` to the two cells (and say "narrowed at the re-pin, forced by the
allocator's contract"); DECISIONS erratum for `0 ≤ sz`; B21: name the two statements.

### D-3 — The `panic!` count is reported four different ways, and ARCHITECTURE §3 is internally inconsistent (premise verified: YES)

ARCHITECTURE `:594`–`:604`: "127 non-comment lines across the twelve hand-written
`lean_frontend/*.lean` seams, 61 of them in `CerbMem.lean` … Fifty-four of them mirror an
OCaml `assert false`/`failwith` arm … seven are Lean-side guards … (the five `CerbFS.lean`
refusals …)". 54 + 7 = 61 is the OLD total (pin `f95ef8d9c`), not 127; `CerbFS.lean` alone
has 36–39 `panic!` at this pin, not five. KOI A5: "61 code arms at the pin, 40 in
`CerbMem.lean`" — the old numbers under a sentence that now says "at the pin". README
(record §9): 119. Measured at the pin over the 37 manifest seams — block-and-line-comment
stripped (the gate's method): **117** (CerbMem 60, CerbFS 36, CerbDecode 7, CerbFloat 5,
CerberusImpl 4, CerbUtils 4, CerbLocation 2, Main 2, CerbND 1, CerbTags 1, CoreParser 1);
raw `grep -c` less comment LINES (ARCHITECTURE's stated method): **126** (CerbFS 39,
CerbMem 60). Neither reproduces 127/61 or 119; "twelve seams" is stale too (37 in
`handwritten_copy.manifest`; eleven files carry a `panic!`). Fix: one method, one number,
on ARCHITECTURE §3, README and KOI A5; re-derive the mirror/guard split or drop it.

### D-4 — KOI B7 (edited at d8ebad9) quotes a statement that no longer exists (premise verified: YES)

B7: "`esize_subst : esize e ≤ lemDefaultFuel → esize (subst_sym_expr x v e) = esize e`
(Soundness.lean:1224 …) … as a kernel-checked equation at the generated definition's fuel
(MEASURED, not a fuel-generic theorem; L2's re-pin corrects the wording)". At HEAD
(`Soundness.lean:1228`): `theorem esize_subst {e : CoreExpr} (x : sym) (v : value) :
esize (subst_sym_expr x v e) = esize e` — NO premise, fully fuel-generic (`subst_sym_expr`
is MEASURED, fuel-free at the pin: generated `Core_aux.lean:531` has no `[LemFuel]`); the
snapshot agrees. The "fix" made the entry wrong in the other direction. Fix: quote the
HEAD statement (and its line, `:1228`, not `:1224`), "unconditional since the pin's measured substitution".

### D-5 — README "Scope" counts stale from L1 (flagged by the worker, not fixed) (premise verified: YES)

`README.md:139`–`:140`: "28 constructors, 58 rows, 35 RULE, 0 RULE-TOTAL-UNDEMONSTRATED,
19 NO-RULE, 4 OUT-OF-SCOPE at this writing (dialect arc E2, 2026-09-05)". The regenerated
manifest (`docs/CAPABILITY_MANIFEST.md:182`): `MANIFEST: 35 constructors, 78 variant rows
(40 RULE, 0 RULE-TOTAL-UNDEMONSTRATED, 7 RULE-PARTIAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 24
NO-RULE, 7 OUT-OF-SCOPE), 0 red, 25 consumer modules`. The record §10 item 5 flagged it
"for the orchestrator"; d8ebad9 did not fix it. Fix: the manifest's line.

### D-6 — FUEL.md §4: a second `drive`-path call site of `hack`/`to_pure`, and the `4 ≤ fuel` floor asserted without its reason (premise verified: YES)

(a) `driver_globals` (generated `Driver.lean:518`–`:530`; the `nd_mapM_` over
`glob_defs` at `:526`) evaluates every global definition through `to_pure`/`hack` before
`main` runs — a second on-path site of both (D) rows, unlisted (FUEL.md: "called once by
`finalize`"). For THIS package it is (C): every certified file has `globs := []`
(`ProdEntry.lean:82`, inherited by `prodFileWith`/`prodFileLib`), so the mapM is over the
empty list — but the table claims to list every fuelled function reachable from `drive` on
the path, so the site and the reason it is (C) here must be stated.
(b) §3 "needs four — a different theorem domain from adequacy" gives no reason. Measured:
`nd_bind_lemFuel`'s `NDnd` arm re-binds every branch at `lemFuel − 1` (generated
`Nondeterminism.lean:213`; `runOne_bind_nd`, `Round.lean:6827`: "Each branch carries the
continuation at the caller's fuel minus one"), and `memop_fork` (`Round.lean:6961`) peels
three forked binds (`runOne_bind_nd` at `:6987`/`:6990`/`:7001`) plus one active bind
(`hF : LemFuel.fuel = n + 4`). So 4 = the ND-fork depth of the memop round + 1. This is
also the one place where "every fuelled call starts from the full ambient" does not hold
within a bind's own tree; §1 should say so in one sentence.

### H-1 — Eleven NEW linter warnings: a vacuous `[LemFuel]` binder on eleven statements, two of them pinned exports (premise verified: YES)

Gate log at HEAD: 44 `warning: CerberusHeapLang/*` lines (baseline 44 as briefed); the E5
audit's 48 were Potential 31, Round 7, Rules 2, Heap 2, EnvLaws 2, TreeRot/Struct/
Soundness/ProdLoopExhibit 1. Now: Potential 31, Heap 2, **Adequacy 8, CallSmoke 3** — the
15 others are gone and these ELEVEN are new to the range (their subjects are L2 names),
all `automatically included section variable(s) unused in theorem …: [LemFuel]`:
`Adequacy.lean:735` (`MachineCtx.FragProcs.toFuel`), `:756` (`spikeCtx_fragProcs`,
PINNED), `:760` (`procCtx_fragProcs`), `:764` (`spikeCtx_procsDepth`), `:768`
(`procCtx_procsDepth`), `:852` (`Decomp.frag_plug_call`, PINNED), `:1403`
(`spikeCtx_labels_frag`), `:1407` (`spikeCtx_labels_depth`); `Examples/CallSmoke.lean:168`
(`csFBody_frag`), `:176` (`csMainBody_frag`), `:196` (`csCtx_procsDepth`). Snapshot texts:
`spikeCtx_fragProcs : ∀ [LemFuel], CerberusHeapLang.spikeCtx.FragProcs`;
`MachineCtx.FragProcs.toFuel : ∀ [LemFuel] [inst : LemFuel] {M}, M.FragProcs → M.ProcsDepth LemFuel.fuel → M.FragProcsFuel`
(a DOUBLE instance binder; likewise `csCtx_procsDepth`). Logically harmless (`LemFuel` is
inhabited; the inner instance shadows), but a fuel binder on a statement about the
fuel-free syntactic fragment is exactly what R2 removed; KOI C5 says each slice fixes what
it introduces; the record does not report the warning count at all. Fix: `omit [LemFuel]
in` (the idiom already used at `Adequacy.lean:741`, `:860`) on the nine; drop the explicit
`[LemFuel]` on `toFuel`/`csCtx_procsDepth` under the section variable; re-baseline C5 at
33.

### H-2 (Notes) — gate 1b leaks (no instance in the tree; plant log §3)

Plants 3–6 GREEN: a numeral in a non-declaration command after a `*_shipped` theorem
(`#eval (100000000 : Nat)` — `hdr_re` only resets `current` on declaration headers);
`10^8`; `100_000_000`; a numeral after a `"--"` string literal (KOI C11's class). Cheap
fix: reset `current` on any line whose first token is not a declaration keyword or
attribute; add `10\s*\^\s*8|100_000_000` to `NUMERALS`. Note-level per the brief.

### Notes (not graded)

- `scripts/signature_census.py`'s `cause()` is regex-first-match: the eight `ml_*` rules
  gained BOTH `0 < al` (Z2-alloc) and `n.toNat ≤ 9223372036854775807` (Z2-mem-repr) and
  are filed under mem-repr only; `0 ≤ n\b` would file any nonnegativity premise under
  Z2-alloc. The record labels the buckets heuristic/DERIVED; the class totals are right.
- DECISIONS has two date inversions (`:967`, `:3023`); the second is the L1 re-append block
  dated as written by design; neither is in this range.
- `wpt_driver_done_alloc` is the one restated statement that is not pinned (never was).
- The record §11's "the longest single pass stayed well under the one-hour tripwire" is
  unmeasured by me (all my builds replayed from cache).

## 2. R2 and the deviation (`evalDepth`, not `pot`) — verified

- `inductive Frag : CoreExpr → Prop` (`Fragment.lean:491`), 35 constructors, no fuel
  binder, no depth field; `FragFuel [LemFuel]` (`Soundness.lean:9297`) is the re-pin's
  inductive with `peDepth pe ≤ LemFuel.fuel` fields; `Frag.toFuel` (`Fragment.lean:753`),
  `FragFuel.toFrag` (`:857`), `FragFuel.evalDepth_le` (`:897`, needs `1 ≤ fuel`),
  `fragFuel_iff` (`:950`: `1 ≤ LemFuel.fuel → (FragFuel e ↔ Frag e ∧ evalDepth e ≤ LemFuel.fuel)`).
  Every export is proved by `X_fuel … (hfrag.toFuel hdep) (hPf.toFuel hPd)` (e.g.
  `Adequacy.lean:1386`). No pinned statement mentions a device (my sweep).
- The deviation's premise is TRUE, measured at `f1f2573`: the adequacy exports carried
  `pot e₀ ≤ lemDefaultFuel` / `pot cont ≤ lemDefaultFuel` (`Adequacy.lean:116`–`:117`,
  `:769`–`:805`); `pot` bounded `esize` for the `get_ctx` ceiling (`Soundness.lean:54`–`:58`,
  `:526` "production budget (get_ctx := get_ctx_lemFuel lemDefaultFuel"); the operand bound
  was the per-constructor field `peDepth pe ≤ lemDefaultFuel` (`Soundness.lean:7222`,
  `:7275`, `:7460`, `:7740`, `:7783`). At the pin `get_ctx` is fuel-free (generated
  `Core_reduction.lean:387`; C3 manifest row `get_ctx`), so the `esize`/`pot` ceiling has
  no referent and `evalDepth` (max `peDepth` over evaluable operands, `Fragment.lean:86`) is
  the measure the evaluator bridge consumes (`step_eval_bridge` at `peDepth pe ≤ fuel`,
  `Soundness.lean:6541`; `aux2_bridge` at `peDepth pe ≤ fuel + 1`, `:7148`;
  `full_eval_bridge` at `peDepth pe ≤ LemFuel.fuel`, `:7199`). Stability under the engine's
  substitution: `peDepth_subst` (`Fragment.lean:307`, through the pin's
  `subst_sym_pexpr_measure_sufficient`), `evalDepth_subst` (`:467`), `evalDepth_subst_fold`
  (`:472`) — which is what lets `Frag.case_value`/`case_op` carry no depth field.
- The floors: `2 ≤ LemFuel.fuel` — FUEL.md §3 cites `loop_step_frag` (two `nd_bind` layers
  per round), `loop_zero_exhausts` (`DriverCollapse.lean:3010`, fuel 0 = the kill),
  `loop_step_done_exhaust` (`:3019`, fuel 1 at PROGRAM-DONE = the drain pass's kill),
  `loop_step_done` (`:436`) — verified at those lines. `4 ≤ LemFuel.fuel` — see D-6(b).

## 3. Probe / plant log (verbatim)

Gate 1b on the tree and its self-test:
```
ok: no fuel numeral (100000000/1000000/999999) outside a *_shipped corollary and no retired fuel constant (60 files scanned, comments stripped)
exit=0
PLANT A (numeral in an ordinary theorem):
  PLANT OK: 2 hit(s)
PLANT B (retired constant):
  PLANT OK: 1 hit(s)
PLANT C (numeral in comments only, positive control):
  PLANT OK: green
PLANT D (numeral inside a *_shipped corollary, positive control):
  PLANT OK: green
PLANT E (numeral in the declaration after a *_shipped one):
  PLANT OK: 2 hit(s)
fuel_numeral_check: SELFTEST OK (5 plants: 3 red as required, 2 positive controls green)
exit=0
```
My six plants (each appended to `TotalAdequacy.lean` or inserted before `end
CerberusHeapLang` in `Shipped.lean`, then reverted with `git checkout`; tree clean after):
```
PLANT 1: numeral in a STATEMENT of an ordinary theorem (TotalAdequacy.lean)
FAIL: cerberus-heaplang/CerberusHeapLang/TotalAdequacy.lean:98: fuel numeral `100000000` outside a `*_shipped` corollary (in theorem plant_stmt)
FAIL: fuel numeral or retired fuel constant outside a *_shipped corollary (above)
exit=1

PLANT 2: numeral in a PROOF of an ordinary theorem
FAIL: cerberus-heaplang/CerberusHeapLang/TotalAdequacy.lean:99: fuel numeral `100000000` outside a `*_shipped` corollary (in theorem plant_proof)
FAIL: cerberus-heaplang/CerberusHeapLang/TotalAdequacy.lean:99: fuel numeral `100000000` outside a `*_shipped` corollary (in theorem plant_proof)
FAIL: fuel numeral or retired fuel constant outside a *_shipped corollary (above)
exit=1

PLANT 3: numeral in a non-declaration command AFTER a *_shipped theorem (Shipped.lean end)
ok: no fuel numeral (100000000/1000000/999999) outside a *_shipped corollary and no retired fuel constant (60 files scanned, comments stripped)
exit=0

PLANT 4: the numeral spelled 10^8 in an ordinary statement
ok: no fuel numeral (100000000/1000000/999999) outside a *_shipped corollary and no retired fuel constant (60 files scanned, comments stripped)
exit=0

PLANT 5: the numeral spelled 100_000_000
ok: no fuel numeral (100000000/1000000/999999) outside a *_shipped corollary and no retired fuel constant (60 files scanned, comments stripped)
exit=0

PLANT 6: numeral after a string literal containing --
ok: no fuel numeral (100000000/1000000/999999) outside a *_shipped corollary and no retired fuel constant (60 files scanned, comments stripped)
exit=0
```
Raw grep of the numerals and retired names over the package (comments included): the only
hits outside `Shipped.lean` are six comment lines (`Fragment.lean:21`, `Adequacy.lean:30`,
`Audit.lean:64`, `:67`, `Potential.lean:5`, `:7`); `Shipped.lean` has 50 occurrences of
`100000000`. `letI : LemFuel := ⟨…⟩` sites: `Shipped.lean` (26, all `⟨100000000⟩`),
`Fragment.lean:989/994/1001/1007/1020` (`⟨evalDepth …⟩`, inside proofs),
`Adequacy.lean:857` (`⟨evalDepth e⟩`), `ProdEntry.lean:185/472/511/545/752/792/827`
(`⟨n + 2⟩`/`⟨1⟩`, inside proofs after `rcases LF with ⟨fuel⟩`). No file-level `instance :
LemFuel` anywhere.

Independent pin sweep (`.audit-scratch/Pins.lean`, `lake env lean`, 1.4 s):
```
trioExports length 901, distinct 901
AUDITOR SWEEP: trio-exact 901/901; axiom-free-exact 6/6; mismatches 0
pinned statements mentioning a device constant: 0
R2 wrappers listed 21; not pinned: #[CerberusHeapLang.wpt_driver_done_alloc]
```

Executable depth probe (`.audit-scratch/Probe.lean`; `eval_pexpr_aux2 fmapEmpty (other
"probe") none fmapEmpty [symAdd a508 (lint 3) fmapEmpty] none (prodFileLib stdlibE3 []
t1Main) pe` at `letI : LemFuel := ⟨n⟩`):
```
(26, 29, 28, 26)                          -- evalDepth t1Main, t4Main, t5Main, t6Main
(26, 2, 1)                                -- peDepth (convLoadedInt a508), (specInt 3), (psym a508)
("VALUE", "VALUE")                        -- conv_loaded_int at ⟨26⟩ and ⟨25⟩
("VALUE", "VALUE", "VALUE", "ERROR \"lem: fuel exhausted\"")   -- specInt at ⟨2⟩,⟨1⟩; psym at ⟨1⟩,⟨0⟩
[(0, "ERROR \"lem: fuel exhausted\""), (1, "ERROR \"lem: fuel exhausted\""), (2, "ERROR \"lem: fuel exhausted\""),
  (3, "ERROR \"lem: fuel exhausted\""), (4, "ERROR \"lem: fuel exhausted\""), (5, "VALUE"), (6, "VALUE"), …, (26, "VALUE")]
(lem: fuel exhausted, CerbLocation.Loc.other "lem: fuel exhausted")
```
Reading: the record's "t1/t4/t5/t6 at most 40" holds (26/29/28/26); `peDepth` is a
SUFFICIENT bound in the proved direction (success at the bound; exhaustion only far below
— `conv_loaded_int` first delivers at 5 against `peDepth` 26, the `stdBudget` 23 being
generous); the evaluator's exhaustion value is the absorbing `Error` at
`fuelExhaustedLoc`/`fuelExhaustedMsg`, i.e. the payload of `fuelExhaustedKill`.

## 4. The exhaustion classification as I derived it (from the generated tree at the pin)

"Zero value" = the `_lemFuel_zero` lemma's right-hand side (all `rfl` in the generated
tree). `fuelExhaustedKill = Error0 CerbFuel.fuelExhaustedLoc CerbFuel.fuelExhaustedMsg`
(`CerbND.lean:98`–`:99`). "Path" = the fragment's execution from `drive` (integer/pointer
cells, `tagDefs = fmapEmpty`, `globs = []`, no `printf`, no C call).

| Function | Cite (generated) | Zero value | My class | Why / where excluded |
|---|---|---|---|---|
| `driver2` | `Driver.lean:422`–`:429` | `ND (fun st => (NDkilled (Error0 fuelExhaustedLoc fuelExhaustedMsg), st))` | (B) | the scheduler round; the partial forms' admitted kill |
| `drive_nonmemory_steps_aux2` | `:385`–`:392` | same | (B) | `new_drive_core_threads` runs it at the ambient (`:399`) |
| `nd_bind` | `Nondeterminism.lean:212`–`:216` | same | (B) | NB the `NDnd` arm re-binds branches at `lemFuel − 1` (`:213`; `runOne_bind_nd`, `Round.lean:6827`) — the source of the 4-floor (D-6b) |
| `runND` / `runNDFuel` | `CerbND.lean:163` / `:117`–`:123` | `[(Killed st0 fuelExhaustedKill, [], st0)]` | (B) | the singleton equation's kill arm |
| `eval_pexpr_aux2` | `Core_eval.lean:156`–`:164` | `Result (Error fuelExhaustedLoc fuelExhaustedMsg)` | (B) | absorbing in `exceptM`; lifted by `liftCore_run` (`Driver.lean`, `Error loc1 str => kill (Error0 loc1 str)`) to `fuelExhaustedKill`; EXCLUDED on the path by `aux2_bridge` (`Soundness.lean:7148`) at `peDepth pe ≤ fuel + 1` ⇐ `hdep`; probe §3 confirms the payload |
| `full_eval_pexpr` | `Core_reduction.lean:94`–`:102` | `fun st => Result (Error fuelExhaustedLoc fuelExhaustedMsg, st)` | (B) | excluded by `full_eval_bridge` (`:7199`) at `peDepth pe ≤ LemFuel.fuel` |
| `step_eval_pexpr` | `Core_eval.lean:150`–`:152` | worker zero = `fuelExhausted (Result (Undef Loc.unknown []))` — OPAQUE | (A) MEASURED | the wrapper runs the worker at `generic_pexpr.lemSize pexpr1`; `Core_eval_lemMeasureProofs.lean:8` `step_eval_pexpr_measure_sufficient`; `step_eval_bridge_default` (`Soundness.lean:7131`) consumes it |
| `memValueFromValue` | `Core_aux.lean:103`–`:110` | worker zero = `fuelExhausted none` | (A) MEASURED (`ctype.lemSize ty1`) | its `Struct`/`Struct` arm (`:106`) calls `are_compatible0` — (C) for the fragment (integer/pointer cells only; `grep OVstruct` over Step/Rules/Heap none — worker's grep, not re-run) |
| `get_ctx`, `subst_sym_pexpr`, `subst_sym_expr`, `update_env_aux` | `Core_reduction.lean:387`, `Core_aux.lean:517`, `:531`, `:903` | — | (A) MEASURED | no `[LemFuel]` binder on any of the four |
| `CerbMem.sizeofCtype` + 5 layout rows | `scripts/fuel_hypotheses.txt` | — | (A) under `CerbTagsWf.Acyclic` | every export at `tagDefs = fmapEmpty`; the package states no `Acyclic` |
| `hack` | `Driver.lean:433`–`:440` | `fuelExhausted Vunit` — OPAQUE | (D) | ON PATH at `finalize` (`:469`) on the value arena `mk_value_e v` (`prepare_exit`, `:413`), excluded by `hack_value` (`DriverCollapse.lean:660`, `0 < LemFuel.fuel`); ALSO reachable from `driver_globals` (`:518`–`:530`) per global definition — (C) here: `prodFile.globs = []` (`ProdEntry.lean:82`) — unlisted in FUEL.md (D-6a) |
| `to_pure` | `Core_aux.lean:600`–`:602` | `fuelExhausted none` — OPAQUE | (D) | ON PATH at `finalize` (`:469`, `match to_pure th_st.arena`), excluded by `finalize_done` (`DriverCollapse.lean:677`, unfolds `to_pure` at `fuel + 1`); also `driver_globals` (`:526`) — (C) here; README says otherwise (D-1) |
| `to_pures` | `Core_aux.lean:605` | `fuelExhausted none` | (D) → (C) | callers `Core_rewrite.lean:255` (the rewriter) and `Core_run.lean:424` (`core_thread_step2`, no caller in `Driver`/`CerbND`/`Main`) |
| `many`, `many1` | `Monadic_parsing.lean:138`, `:143` | `fuelExhausted (ParserM (fun _ => []))` | (D) → (C) | callers `Formatted.lean:312/:317/:322/:392`–`:393` only (the printf format parser) ← `print_eval_conv_aux` (`Driver.lean:268`–`:276`) ← `printf_eval_conv` (`:281`) ← the `printf` fs/builtin path; no `Frag` construct |
| `are_compatible_aux`, `_params_aux0`, `_params0` | `Ctype_aux.lean:112`–`:114` | `fuelExhausted false` | (D) → (C) | `are_compatible0` (`:128`) called only from `memValueFromValue`'s `Struct`/`Struct` arm (`Core_aux.lean:106`) |
| `print_eval_conv_aux` | `Driver.lean:268`–`:276` | `NDkilled fuelExhaustedKill` | (B) → (C) | `printf` only |

Result: agrees with FUEL.md §4 row for row, with the two precision gaps of D-6. On the
proved path no opaque exhaustion arm is evaluated: the (B) rows are the one admitted kill;
the pure evaluator is kept below exhaustion by `hdep`/`hQd`/`hPd` through
`aux2_bridge`/`full_eval_bridge` — including the std.core unfolding, whose budget
`stdBudget nm` (`Step.lean:2504`: 4/17/23) is part of `peDepth (PEcall nm pes) = 1 +
peDepthList pes + stdBudget nm` (`Step.lean:2571`–`:2585`), consumed by
`call_function_of_callBody` (`Soundness.lean:6465`) inside `step_eval_bridge`; the two
(D) rows on the path are evaluated once each, at PROGRAM-DONE, on a VALUE arena, where one
unit suffices (`0 < LemFuel.fuel ⇐ hfuel`).

Consequence checked on the statements (snapshot text): `prod_run_safe_procs [LF : LemFuel]
… (hsafe : 2 ≤ LemFuel.fuel → DriverSafeCtl …) … : ∃ st dst', runND (drive …) … =
[(st, [], dst')] ∧ (st = Killed dst' fuelExhaustedKill ∨ ∃ dres, st = Active dres ∧ ψ …)`
(`ProdEntry.lean:615`); likewise `prod_run_safe_lib` (`:926`), `fib_rec_certified`,
`even_odd_certified` (the `(fuel : Nat)` binder and `CerbND.drive_lemFuel fuel` gone —
word-diff §5). Fuel 0 is `runNDFuel 0` (`CerbND.lean:123`); fuel 1 is
`drive_after_setup_with_one`/`_lib_one` (`ProdEntry.lean:500`, `:780`: the memory lift
exhausts after errno init); fuel ≥ 2 is `DriverSafeCtl` at the ambient counter through
`new_drive_core_threads` (`Driver.lean:399`). No residual hypothesis beyond
`2 ≤ fuel →` inside `hsafe`. KOI A2 is correctly CLOSED; A1 correctly closed for the
exports with the eight-row register residual upstream.

## 5. The LemLib representation change, the memory-contract class, the census

**Representation (the scout's predictions).** `def SymMap {β} (m : Fmap sym β) : Prop :=
Fmap.WF symCmpK m` (`EnvLaws.lean:242`), `symMap_empty := Fmap.WF_empty symCmpK`,
`SymMap.add := Fmap.WF_fmapAddBy symCmpK_laws`, `symAdd_lookup` through
`Pmap.find?_add_same symCmpK_laws` / `Fmap.fmapLookupBy_fmapAddBy_other` — all upstream
`LemLibPmapLaws` (`import LemLibPmapLaws`, `:17`); no local law; no heartbeat bump.
`killM_killed_inv` (`Round.lean:956`): seven rows — `UB179a`, `UB179b`, `UB009_outside_lifetime`,
`MerrUndefinedFree Free_out_of_bound`, `MerrOther "attempted to kill with a function
pointer"`, `… "attempted to kill with a pointer lacking a provenance"`, `… "killM:
Prov_symbolic in concrete model"` — checked arm by arm against `CerbMem.killM` at the pin
(`CerbMem.lean:2175`–`:2234`): the null arm and the `zap_dead_pointers` arm are under
refused switches (`CerbGlobal.has_switch` false), the `Prov_device` arm and the base-match
arm are active, the dead-static arm is the `panic!` (`:2216`) — an ACTIVE outcome, not a
kill — so the disjunction is exhaustive over the kills. Registration-order `rfl`s: the
LemLib-map class (6: `collect_new_eo`, `t4Q_eq`/`_lookup`, `t6Q_eq`/`_lookup`,
`fmapLookupBy_addBy_empty`) — canonical `symAdd` order changed, consistent with the
ascending-order measurement of scout §4 (a″).

**Memory contract (KOI B21).** `allocateRegion_success` new shape (snapshot): premises
`0 < LemFuel.fuel → 0 < alignN → 0 ≤ sizeN → freshBase … ≠ 0 →`; result record
`{ … allocations := insert … { base := …, size := sizeN, prefix_ := PrefMalloc }, …,
lastUsed := some σ.nextAllocId, … }` with the former `writeBytesTo … (List.replicate
sizeN.toNat undefByte)` gone — each forced by `allocateRegion` at the pin
(`CerbMem.lean:2159`–`:2172`: `nd_bind (allocator sizeN alignN)` — hence `0 < fuel`;
`prefix_ := PrefMalloc`; no bytemap write) and by `allocator` (`:2089`–`:2104`: `align ==
0 → panic!`, `lastUsed := some allocId`, no clamps — hence `0 < alignN`, `0 ≤ sizeN`).
`allocateObject_success`: `0 < LemFuel.fuel → 0 < alignN → …` at `reqAddrOpt = none`
(the `some` arm is the fail-stop `panic!`, `:2123`) — hence `wps_create`'s
`get_with_address a = none`. `emittedInt_storable : -2147483648 ≤ n → n ≤ 2147483647 → …`
(`intToBytes signed`). The two production statements: D-2.

**Census (DERIVED; my own classifier `.audit-scratch/census.py`, token-level
normalisation, written without reading the worker's until the comparison).** Totals
reproduced exactly: pre 4950 / post 5212, ADDED 283 / REMOVED 21 / CHANGED 1483. Classes:
mine 1298 binder-only / 127 premise-text / 58 shape vs the worker's 1340 / 82 / 61; 46
disagreements, every one inspected: 43 are my normaliser's residue (binder reordering
into section variables, e.g. `array_sum_certified`; a dropped `peDepth pe ≤ 8` premise on
`t4AndSpecified_frag`, which the worker files as fuel-binder-only — a defensible
convention, stated in its header) and 3 are the fuel-token-only trio the worker files as
shape (`peDepth_sym_le`, `peDepth_val_le`, `saveParamsWithValues_depth`). My 58 shape
entries are exactly 58 of the worker's 61. Verdict: the worker's classification stands.
The 21 REMOVED match the record's list name for name (`CorpusE0.depLe/depLe40`, `depLeB/C`,
`Decomp.frag_plug_call'`, `Frag.esize_le_pot/pot_step_bound/step`,
`MachineCtx.FragProcs.potBound`, `drive_after_setup_{lib,with}_lemFuel`,
`instLanguageCoreRtMemEmptyCoreRVal`, the six `*_pot`, `treeMap_get?_insert_empty`, the two
generated `.eq_def`s). Cause buckets re-run: Z2-alloc 32+15 = 47, Z2-mem-repr 21+3 = 24,
Z1 6, LemLib-map 6, engine-wrapper 7, R2 4+18 = 22, printing 25, fuel-token 3,
unexplained 3 — the DECISIONS line reproduces.

**The thirteen production statements + three partial forms, before → after (word-diff of
the two snapshots; every change forced).** `exhibitA_prod` `+∀ [inst : LemFuel], 12 ≤
LemFuel.fuel →`; `fib_certified_production`, `counter_loop_…` `+[inst : LemFuel]`,
`CerbFuel.driverFuel → LemFuel.fuel`; `list_reverse_…` `+56 ≤`; `dispose_list_…` `+53 ≤`;
`region_loop_…` `+[inst : LemFuel]`, `+0 < al → 0 ≤ sz →`, token; `malloc_list_…`
`+[inst : LemFuel], 0 < al →`, token; `fib_rec_…`, `even_odd_…` `+[inst : LemFuel]`, token;
`t1/t4/t5/t6_…` `+∀ [inst : LemFuel], 50/917/90/80 ≤ LemFuel.fuel →`; `prod_run_safe_procs`
`+[LF : LemFuel]`, `hsafe` under `(2 ≤ LemFuel.fuel → …)`, `(fuel : Nat)` binder and
`CerbND.drive_lemFuel fuel` → `drive`; `fib_rec_certified`, `even_odd_certified` likewise.
Nothing else moved in any of the sixteen.

## 6. Oracle (verbatim) and the binary caveat

`cd /home/dev/projects/cerberus-lean-proj && scripts/ce cerberus-lean/_build/default/backend/driver/main.exe --nolibc --exec --batch refined-cerberus/docs/corpus-e0/<f>.c` (zsh, `exit=${pipestatus[1]}`; `Time spent` lines omitted):
```
== t1
Defined {value: "Specified(4)", stdout: "", stderr: "", blocked: "false"}
exit=0
== t4_while
Defined {value: "Specified(10)", stdout: "", stderr: "", blocked: "false"}
exit=0
== t5_ifelse
Defined {value: "Specified(1)", stdout: "", stderr: "", blocked: "false"}
exit=0
== t6_switch
Defined {value: "Specified(20)", stdout: "", stderr: "", blocked: "false"}
exit=0
== t2
Defined {value: "Specified(3)", stdout: "", stderr: "", blocked: "false"}
exit=0
== t3_ptrarg
Defined {value: "Specified(4)", stdout: "", stderr: "", blocked: "false"}
exit=0
== t10_evenodd
Defined {value: "Specified(1)", stdout: "", stderr: "", blocked: "false"}
exit=0
```
The certified values agree (`t1_certified_production` `lint 4`, t4 `lint 10`, t5 `lint 1`,
t6 `lint 20`). CAVEAT (verbatim measurement): the binary
`cerberus-lean/_build/default/backend/driver/main.exe` has mtime `Sep 5 19:47`
(2026-09-05 19:47:06 +0000); the pin commit is `89f7e6885 2026-09-05 22:34:29 +0000 docs:
orchestrator handoff …`; the commits between the last commit before the mtime
(`9a7f7ad31 19:34:20`) and the pin are `61181efd1`, `9635592ca`, `ec919ce0a`, `aa5fc06c4`,
`596235016`, `7855cc7a3`, `0a62dd7f7`, `89f7e6885`; `git diff --name-only 9a7f7ad31..89f7e6885`
outside `lean_frontend/docs/`, `docs/`, `scripts/`, `lean_frontend/test/` is exactly
`lean_frontend/CLAUDE.md`, `lean_frontend/TODO.md`, `lean_frontend/VALIDATION.md`; `git diff
--stat 9a7f7ad31..89f7e6885 -- frontend backend ocaml_frontend memory util parsers cparser
lem_prelude '*.ml' '*.lem' '*.mli'` is EMPTY. The binary is therefore the pin's OCaml
semantics; the record's caveat ("about three hours … docs/instruments") is accurate. The
sibling's HEAD is 22 commits past the pin; its `generated/` for the six files compared is
byte-identical to the workspace's (the pin-bump commits since are docs-only on those
paths).

## 7. The FULL gate, verbatim (`CERB_MEM_MAX=40G scripts/test_unit.sh`, cached build), matching lines only

```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 1b: fuel-numeral grep (scripts/fuel_numeral_check.sh; a numeral outside a *_shipped corollary is red) ==
ok: no fuel numeral (100000000/1000000/999999) outside a *_shipped corollary and no retired fuel constant (60 files scanned, comments stripped)
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:1116:0: CerberusHeapLang export pins: 901 trio-exact, 6 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1116:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (6450 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1116:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (9664 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (483 jobs).
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
BOUNDARY: 29 modules checked, 0 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
GATE-EXIT=0
```
Mechanical comparison with the DECISIONS L2 entry's block (per-module `ok:   ` lines
elided there, as the entry states): `diff` empty — IDENTICAL. No `UNCAPPED` warning. The
record §11's block at `cc4fe8f` is the same text. Counts against the tree: 901 + 6 pins
(Audit.lean), 19 `core` rows in `scripts/module_classes.tsv`, 29 boundary modules, 60
`.lean` files scanned (59 under `CerberusHeapLang/` + the root), manifest 78 rows / 7
OUT-OF-SCOPE / 35 constructors — all reproduce. DECISIONS' L2 entries are in order.

## 8. Docs at HEAD — what I read and what is true

- **FUEL.md**: every table row of §2/§4 re-derived (§4 above); all 44 generated cites and 5
  LemLib cites verified (`LemLib.lean:63` HISTORY, `:66` `class LemFuel`, `:177`
  `opaque failwithI`, `:191` `opaque fuelExhaustedWith`, `:217` `def fuelExhausted`); §3's
  cites `Adequacy.lean:936` (`DriverSafeCtl`), `ProdLoop.lean:515` (`DriverDoneCtl`),
  `DriverCollapse.lean:2877/:2803/:3010/:3019/:436`, `Round.lean:7874/:7917`,
  `Adequacy.lean:728`, `Fragment.lean:491`, `ProdEntry.lean:577`, `Shipped.lean:79–:337`
  all land (`ProdEntry.lean:615` is `prod_run_safe_procs`'s header). Gaps:
  D-6.
- **ARCHITECTURE**: glossary and §4 (`:767`–`:782` the `hdep`/`hQd`/`hPd` bullet;
  `:803`–`:819` exhaustion; `:841` A2 closed) TRUE; §2.2's `engine_step_matchU` verbatim
  matches `Round.lean:2064`; §2.5 table cites `RegionLoopExhibit.lean:612`,
  `MallocListExhibit.lean:1672` etc. EXACT per the cite tool. FALSE/stale: §2.5 rows
  `:527`/`:528` (D-2), §3 `:594`–`:604` (D-3), §3 `:622`–`:624` (R-1). Counts: 901 pins ✓,
  19 core modules ✓ (`:` import-direction line), 35 constructors ✓, 78 rows / 7 OUT-OF-SCOPE
  ✓ (§6 "Seven OUT-OF-SCOPE", "twenty-four NO-RULE" ✓ against the manifest).
- **README**: `:787` (D-1), `:139`–`:140` (D-5); rows `:603`/`:612` disclose the allocator
  premises ✓; `:1094` `Fragment.lean` row ✓.
- **KOI**: A1 ✓ (names both `hack`/`to_pure` at `finalize`), A2 ✓, A4 ✓ (`LemLibPmapLaws`
  upstream — verified in `EnvLaws.lean`), A6 ✓, B21 ✓ on the rules (D-2 on the production
  statements), §E ✓ (the expected tail is what I got; `worktrees/land-repin` exists).
  A5 (D-3), B7 (D-4) wrong at HEAD.
- **Cite check** (12 hand-checked, all correct): `ARCHITECTURE.md:53` → `Step.lean:6310`
  `def spikeCtx`; `:72` → `ProdLoop.lean:518`/`:523` (the `DriverDoneCtl` ties); `:189` →
  `Step.lean:816` (`sup : RunSup`, `Ctl`'s last field); `:195` → `Step.lean:950`
  (`runState`, `MachineCtx`'s last field); `:367` → `Round.lean:3285` `theorem
  complete_store`; `:376` → `DriverCollapse.lean:2877` `theorem loop_step_frag`; `:444` →
  `ProdLoop.lean:373` `theorem wpt_driver_done`; `:494` → `Shipped.lean:79`
  `exhibitA_prod_shipped`/`:337` `t6_…_shipped`; `:542` → `Layout.lean:60` `sevenVal`;
  `:547` → `Heap.lean:2345` `regionCost`, `:2290` `headroom`.

## 9. Grumpy read of the new Lean and scripts

- `Fragment.lean` (1041 lines, read in full): clean; the bridge is a plain structural
  induction both ways; `evalDepth` is a max, `peDepth` a sum where a sibling keeps
  evaluating (`Step.lean:2565`–`:2570` explains why); no `decide` on anything large; the
  `Frag.*` syntactic twins instantiate the device at `⟨evalDepth e⟩` — a neat trick, stated
  in the header. The only smell is H-1's vacuous binders in `Adequacy.lean`/`CallSmoke.lean`.
- `Shipped.lean` (353 lines, read in full): as claimed; `fibRounds_33` via `fibRounds_closed
  33` + `fibSpec_34` (from `fibPair 33` by `decide`) + `omega`; the docstrings state the
  parameter bounds' derivation. Cosmetic: the `even_odd_…_shipped` header has a stray
  line-break before a comma (`:272`).
- The wrappers (Adequacy/Round/DriverCollapse/ProdLoop): mechanical `X_fuel … (hfrag.toFuel
  hdep) (hPf.toFuel hPd)`; ~40 continuation lines over 140 columns (record §10 item 4,
  disclosed).
- `scripts/fuel_numeral_check.sh`: fail-closed, comment-stripping nested-aware; the leaks
  are H-2 (Notes).
- `scripts/signature_census.py`: the class split (binder-only / premise-text / shape) is
  sound in the direction that matters (my independent classifier converged to it); the
  `cause()` regex chain is order-sensitive (Note).

## 10. What I did NOT check

- The bodies of the 70-file cherry-pick's re-cut PROOFS line by line (kernel-checked; I
  read every restated STATEMENT, the two new modules' headers/definitions, `Fragment.lean`
  and `Shipped.lean` in full, the exclusion lemmas `hack_value`/`finalize_done`/
  `loop_zero_exhausts`/`loop_step_done_exhaust`, the fuel-0/1 collapse lemmas, `killM`/
  `allocator`/`allocateRegion`/`allocateObject` at the pin).
- `WALKTHROUGH.md`, `API.lean`, `CLAIMS.md` beyond grep spot-checks (`to_pure` correct at
  WALKTHROUGH `:1760`; no stale fuel constants outside history sentences).
- The upstream `LemLibPmapLaws` proofs (LemLib's, zero axioms per the pin record).
- The worker's `grep OVstruct` (the struct-cell claim for `are_compatible0`'s
  unreachability); the (C) classification rests on the caller grep over `generated/`
  reported in §4.
- The elaboration time of a full L2 rebuild (record §11 "well under the tripwire" — all my
  builds replayed from cache).
- `worktrees/codex-residuals` and the sibling repos' working trees (out of scope, not
  touched).

Ephemeral scratch (`.audit-scratch/` at the copy's root: the gate log, my classifier
`census.py` and its outputs, `Pins.lean`, `Probe.lean`, the cite TSV) is left untracked for
the orchestrator to inspect or delete; everything it produced is quoted above.

## 11. Required fixes, in one list

1. R-1: pin accounting (record §7, ARCHITECTURE `:622`–`:624`, DECISIONS erratum).
2. R-2: "twenty-three" → twenty-one (record §3, DECISIONS erratum); `wpt_driver_done_alloc` unpinned.
3. D-1: README `:787` — `to_pure` IS on the path at `finalize`.
4. D-2: ARCHITECTURE §2.5 `:527`/`:528` add `hal`/`hsz`/`halign`; DECISIONS erratum `0 ≤ sz`; B21 name the two statements.
5. D-3: one `panic!` count, one method, on ARCHITECTURE §3, README, KOI A5; fix the 54/7 split or drop it; "twelve seams" → the manifest's 37 (eleven carry a `panic!`).
6. D-4: KOI B7 — quote `esize_subst` as it is at HEAD (unconditional; `Soundness.lean:1228`).
7. D-5: README `:139`–`:140` — the manifest's line.
8. D-6: FUEL.md §4 `hack`/`to_pure` rows: the `driver_globals` site and why it is (C) here (`globs := []`); §3: the reason for `4 ≤ LemFuel.fuel` (the `NDnd` decrement, `runOne_bind_nd`, `memop_fork`).
9. H-1: `omit [LemFuel] in` on the eleven; drop the double binders; re-baseline KOI C5.
10. H-2 (optional, cheap): reset the gate's allowance on non-declaration lines; add `10^8`/`100_000_000` spellings.

Nothing above touches a proof or a statement's truth; items 1–8 are sentences, 9 is
statement hygiene on eleven lemmas (two pinned — their pin entries stay, the axiom set is
unchanged).
