# Range audit f9c3c2e..825b5e6 (E3: the impl arithmetic, the std.core unfolding, the file object) — 2026-09-05

**VERDICT: PASS WITH FIXES REQUIRED — A−.** No T- (trust) or C- (coverage)
finding: the E3 mirror is exact against the generated engine at the pin
on every admitted arm (read arm by arm against `core_eval.lem`/`Core_eval.lean`
and confirmed by the bridge THEOREMS `step_eval_bridge`/`stepFail_bridge`/
`call_function_of_callBody`/`call_function_exception_of_callOut`, and by
executable probes of the shipped composite and the pinned OCaml oracle);
the integer rules are Reynolds/O'Hearn-clean (pure premises, the UB036
kill excluded by the client's range obligation, never absorbed); the
acceptance statements say what the records say; census 312/3/369 =
268+11+56+34 reproduced; all nine production statements (+ `exhibitA_prod_e1`,
`exhibitB_prod_e2`) textually unchanged; 589 pins, 589 distinct, trio-exact
by the in-build audit; the rebase resolution is right. The fixes required
are record/shop-window: stale `Audit.lean` cites in ARCHITECTURE, two shop-window
rows naming DELETED theorems as current state, a stale `eval_uncovered`
characterisation on five surfaces (the worker knew and deferred it), the
committed post snapshot not re-taken at HEAD, KNOWN-OPEN-ITEMS untouched by
E3, and four record inaccuracies.

Auditor: fresh, independent (this file; not committed). Fixed detached copy
`worktrees/audit-e3-825b5e6` at 825b5e6; semantics pin `f95ef8d9c`
(`.cerberus-ws` verified `git log -1`). Every lake/lean invocation under
`scripts/capped` with `CERB_MEM_MAX=40G`. Longest single pass: the FULL gate
on the primed tree, 22.8 s wall; nothing approached the tripwire. Derived
tallies are labelled DERIVED; quoted outputs are verbatim.

## 0. Method

Read: AUDIT-BRIEF, KNOWN-OPEN-ITEMS, CLAUDE.md, ARCHITECTURE (E3 sentences
checked at HEAD), DECISIONS tail (E-arc rulings, E2-audit/fixes entry, E3
landing entry), design note §B4/§C.3/§C.9 + ratified point (3), the upstream
`mk_conv_int` note, the E3 record and the E3 closure note. Read the FULL Lean
diff of the range (`git diff f9c3c2e..825b5e6`, 48 files, +46220/−1331: the
new modules `StdCore`/`IntRules`/`EmittedCExhibit`/`OverflowExhibit` in full;
`Step`/`EvalClass`/`Round`/`ProdEntry`/`ProdLoop`/`DriverCollapse`/`Audit`/
`CorpusE0`/`MirrorCoverage` diffs in full; `Soundness` at declaration level
plus every E3 arm of the two bridges; the exhibit diffs at statement level).
Read the engine at the pin: `core_eval.lem` :25–165 (`mk_*`, `call_function`),
:165–335 (`pull_helper`/`pull_constrained`), :340–515 (`step_eval_peop`),
:543–560, :625–652 (`Civmin`/`Civmax`), :815–860, :960–1000, :1050–1090,
:1112–1140; generated `Core_eval.lean` `mk_wrapI`/`mk_conv_int`/`mk_iop`/
`mk_wrapI_op`/`mk_call_catch_exceptional_condition`/`call_function`/
`pull_constrained_lemFuel`; `CerbMem.lean` :1225–1370 (`minIval`/`maxIval`/
`opIval`); `std.core` :1–70, :225–245; the gcc impl :1–40. Measured: the FULL
gate, a HEAD signature snapshot, the census by script, the pin list, an
executable Lean probe of the shipped composite, the pinned OCaml oracle.

## 1. Findings, ranked

### R-1 — the committed post snapshot is not HEAD's (fix: regenerate at HEAD)

`cerberus-heaplang/docs/2026-09-05_e3-signatures-post.txt` (39410 lines) was
taken on the PRE-REBASE E3 tree: a fresh snapshot at 825b5e6 (`lake env lean
scripts/signature_snapshot.lean`, 20.5 s) has 39418 lines and differs
exactly by the two E2-audit entries `unspec_bytes` and `unspec_paddingByte`
(`diff` verbatim: `35865,35869d35864 < theorem CerberusHeapLang.unspec_bytes :
…` and `35874,35876d35868 … < theorem CerberusHeapLang.unspec_paddingByte :
CerbMem.paddingByte = CerberusHeapLang.undefByte`). The brief's "HEAD snapshot
`cmp`-identical" is therefore FALSE. The census itself is unaffected (both
endpoints predate the E2 fixes consistently, and the two entries are in both
f9c3c2e and HEAD): DERIVED by my own script over the two committed
snapshots — pre 3853, post 4162, ADDED 312 / REMOVED 3 / CHANGED 369 — exactly
the record's numbers. Premise verified by measurement: yes. Fix: re-take the
snapshot at HEAD and commit it (same file), note the erratum in the E3 record §9.

### D-1 — ARCHITECTURE's `Audit.lean` cites are stale after E3 (fix: four cite groups)

`cerberus-heaplang/ARCHITECTURE.md:506` "`(`:703`–`:722`)`", `:508` "`(`:723`–`:737`)`",
`:524` "`(`:389`, `:557`–`:558`)`" were correct at f9c3c2e (measured: `git show
f9c3c2e:…/Audit.lean` lines 389, 557–558, 703, 723, 737 are the cited texts).
E3 inserted its 20-line header paragraph (+2 import lines) and 43 pin lines, so
at HEAD the texts are at `Audit.lean:411`, `:579`–`:580`, `:768`–`:787`,
`:788`–`:802` (measured by `grep -n`). `Audit.lean:45` (the no-boundary
sentence, ARCHITECTURE :528) is still right. Premise verified: yes. The
brief asked exactly this; the orchestrator's rebase corrected the pin count
sentence to 589 but not the cites.

### D-2 — two shop-window rows name DELETED theorems as the current state (fix: restate)

(a) `cerberus-heaplang/ARCHITECTURE.md:673` (§6 divergence table): "…and NOT yet
whole: `conv_loaded_int`/`catch_exceptional_condition` (…, E3), `unseq` (E4)…
— t1's `main` is outside `Frag` (`Examples/CorpusE0.lean`:
`t1_convLoadedInt_uncovered`, `t1_case_uncovered`)…" followed by an appended
"E3 (2026-09-05): … ARE admitted … the E2 exclusions flipped to
`t1_convLoadedInt_covered`/`t1_case_covered`". The row contradicts itself and
its first sentence names two theorems E3 REMOVED (census REMOVED = 3, verbatim:
`CorpusE0.convLoadedIntSym`, `CorpusE0.t1_case_uncovered`,
`CorpusE0.t1_convLoadedInt_uncovered`). (b) `cerberus-heaplang/docs/CLAIMS.md:40`
(C12, the E2-fixes text kept at the rebase): consumers column "the
kernel-decided operand exclusions `t1_convLoadedInt_uncovered`/`t1_case_uncovered`
— the two operands outside `PePure`; `main` outside `Frag` follows by the
grammar"; exclusions column "t1's `main` is not in `Frag`". The manifest's
CLAIMS check (119 names) reads the theorem column only, so this passed green.
A reader of CLAIMS at HEAD is sent to theorems that do not exist. Premise
verified: yes (`grep -rn t1_case_uncovered CerberusHeapLang` → 0 hits). Fix:
restate C12's consumer/exclusion cells as E1–E2 history ("… were kernel-decided
OUT at E2; flipped at E3, see C13") and rewrite the ARCHITECTURE row as one
current-state sentence.

### D-3 — the `eval_uncovered` characterisation is stale on five surfaces (fix: drop "`OpEq` at two ctypes", add the budget member)

Since E3 `evalBinop` has the arm `| .OpEq, Vctype ty1, Vctype ty2 => some
(boolValue (ctypeEqual ty1 ty2))` (Step.lean:1300; engine core_eval.lem:347–348,
generated `if ctypeEqual ty1 ty2 then Vtrue else Vfalse`, verified), so ctype
equality is MIRRORED and is no longer an `eval_uncovered` leaf; and the
std.core call over `stdBudget` is a NEW member. Still listing the ctype leaf
and omitting the budget member: `ARCHITECTURE.md:280` and `:751`,
`README.md:562`, `docs/WALKTHROUGH.md:1845`, `Round.lean:113` and `:376`
(the `OpenRound.eval_uncovered` docstring), `EvalClass.lean:32`/`:218`.
The manifest row was updated (correctly). The E3 record §5.8 records the
worker KNEW ("the E2 wording … is stale there — for the E2-fixes owner or the
next ARCHITECTURE review"); the ratified schedule (DECISIONS 2026-09-05
[USER]) puts per-slice shop-window truth on the worker's docs pass, so this is
a required fix, not a deferral. Premise verified: yes.

### D-4 — KNOWN-OPEN-ITEMS untouched by E3; C16's mover only half done (fix: update)

`git log -- docs/KNOWN-OPEN-ITEMS.md` ends at f9c3c2e. At HEAD: the State line
says "after E1 + its audit fixes + E2"; §E's expected FULL tail says 509 pins /
58 rows / 22 modules (HEAD: 589 / 66 / 23, measured below); B8 says emitted
programs "still fail the full `Frag` parse until E3"; C16 says "E3 updates the
row with its slice" — E3 added the ctype-leaf note and the budget arm to the
`Frag.pure_op` OUT-OF-SCOPE row but did NOT add the four E2 members the KOI
entry was about (a `case` matching no pattern, UB088, a constructor dispatch
failure, an undef-then-raise operand list — the E2 closure note's list, which
ARCHITECTURE :280 carries): C16 stays open with its mover missed. E3's own
pending items (record §7: the symbolic-`int` storability lemma, a driver-kill
adequacy lemma, the `is_unsigned` rebuild upstream-tray candidate
core_eval.lem:1086, the `PElet` withdrawal, `-`/`*` rules) are unregistered.
Premise verified: yes.

### D-5 — ARCHITECTURE §7 Goal 2 omits the E3 closure record (fix: one cite)

`ARCHITECTURE.md:824–829` lists the closure re-establishment records for E1
and E2 only; `docs/2026-09-05_fragment-closure-e3-notes.md` exists and
re-establishes `frag_round_complete` at the E3 fragment (verified: the file's
statement and the `complete_*` re-proofs in the Round.lean diff).

### D-6 — the file object's nature and the exhibit's synthetic status are not on the shop window (fix: one sentence each in README/CLAIMS)

`prodFileLib stdlibE3 [] (progCE3 3)` is NOT the pipeline's `--nolibc` file:
`stdlibE3` is a THREE-function fragment of std.core (`is_representable_integer`,
`conv_int`, `conv_loaded_int`, checked against the pinned SOURCE — verified by
me: `StdCore.lean` transcribes `std.core:5–6`, `:25–55`, `:61–67` constructor
for constructor), `impl0 = ∅`, `funinfo = ∅`, `globs = []`. On this file
`conv_int` at a NON-representable value is a KILL where the pipeline's file
would wrap — measured by the executable probe below (`evalClass … (PEcall (Sym
convLoadedIntSym) [sintTyPe, Specified(2147483648)]) = .kill`, the classifier's
`unknownImpl` face, engine `Illformed_program "calling an unknown
impl-function: …"`), so the statement's file is behaviour-equal to the
pipeline's only on programs that reach the three functions and no `Impl`
constant — true of `progCE3` and of t1. This is disclosed in `StdCore.lean`'s
header and the manifest's OUT-OF-SCOPE row, but README :196/:202 and CLAIMS C13
call it "the library-carrying file" without saying "a three-function fragment,
empty impl map". Likewise `EmittedCExhibit` is a SYNTHETIC — t1 with the
`unseq` replaced by `let weak p = pure(x) in load(…)` (module header, manifest
"t1 minus the unseq") — with no `.annot.core` twin and outside the corpus
speedbump; README/CLAIMS/WALKTHROUGH do not say "synthetic" (the E1 audit's
R-1 precedent for `EmittedAExhibit`). Not a logic gap (the statement names
exactly the file it certifies); a disclosure gap on the front surfaces.

### R-2 — the record and DECISIONS mislabel the file-object option (fix: erratum)

E3 record §3 title "option (a), the transcribed `stdlibE3`" and DECISIONS
"FILE OBJECT: option (a) of the design — `stdlibE3` (three transcribed
std.core bodies)". The design note §C.9 letters are: (a) `pipelineFile`
(the elaborator in the statement — "the truest … a grind risk"), (b) the
hand-transcribed term with an executable check, (c) `CoreParser.parseFile`.
What E3 built is (b) (and ratified point (3) is (b)). Premise verified: yes.

### R-3 — the closure note misclassifies the arity-mismatch call (fix: the table row)

`docs/2026-09-05_fragment-closure-e3-notes.md`, row "`f(args)` at a WRONG
arity | … | `ShippedRefusal.panic` … [AGENT] classified as the existing PANIC
face". FALSE at HEAD: `callOut` (EvalClass.lean) returns `StepFail.uncovered`
for any callee FOUND in `stdlib`/`funs` (`| some _ => StepFail.uncovered`) —
that covers the arity mismatch AND a found non-`Fun` declaration (std.core's
`proc`s, a user `Proc`) — so the round is `OpenRound.eval_uncovered`, not a
`ShippedRefusal`; `callOut`'s own docstring says so correctly ("…is the
engine's `failwithI` PANIC (:149–162), not characterized"). The engine does
panic there (`core_eval.lem:149–162`, verified), and `.uncovered` is the honest
fail-closed answer; only the record is wrong. Premise verified: yes.

### R-4 — E3 record defects (fix: dedupe; note the pre-rebase tail)

(a) §8 duplicates the block from `theorem t1_uncovered_exactly_unseq` through
`def pendingCorpus` (record lines 395–420 = 422–445). (b) §11's "verbatim
verdict tail" is the PRE-rebase tail (588 / 4723 / 7368 / `Audit.lean:749`);
at HEAD it is 589 / 4725 / 7370 / `:754` (below). DECISIONS' erratum covers
"588" only — extend it to the four numbers or point to the DECISIONS tail.
(c) §3 quotes the speedbump summary "`corpus-skeleton: ok — 1 row(s) equal`"
under the std.core table: the summary counts corpus rows (t1) only; the three
std.core rows are reported in the table but not in that line (N-, reword the
script's summary or the record's framing).

### R-5 — upstream note cite off by one

`docs/2026-09-05_note-cerberus-lean-conv-int-divergence.md`: "`…gcc_4.9.0….impl:18`–`:20`";
the source has the `fun <Integer.conv_nonrepresentable_signed_integer>` header
at `:17`, `-- TODO doc` at `:18`, `wrapI(ty, n)` at `:19` (measured);
`Step.lean`'s module note has `:17–19`. The note's substantive claim
(`mk_conv_int`'s non-representable arm calls `mk_wrapI` directly, TODO comment
at :76) is TRUE against `core_eval.lem:61–81` (read).

### D-7 — "at EVERY fuel" (fix: "every positive fuel")

`overflow_driver2_killed(_frame)` are stated at `driver2_lemFuel (Nat.succ fl)`;
the docstring and DECISIONS say "at EVERY fuel". Fuel 0 is the sentinel
(`CerbND.driver2_lemFuel_zero`, `fuelExhaustedKill` — used that way in
`prod_run_safe_lib`'s `zero` arm). Say "every positive fuel (fuel 0 is the
exhaustion sentinel)". The "every fuel" of the record §6 has the same reading.

### H-1 — duplication and consumerless lemmas in the new Lean (hygiene; not defects)

`depLeC` (EmittedCExhibit) / `depLe40` (CorpusE0) / `depLe`: three copies of
"depth ≤ 40 → ≤ lemDefaultFuel"; `symC_eval` (at `M`) / `symK_eval` (at
`fmapEmpty`): twins; `prodCtx_labels` / `procCtxF_labels` / `procCtx_labels`:
one proof three times; `evalPexpr_cAdd_overflow` re-runs `evalPexpr_cAdd`'s
first half; `stepFail_cAddBranch_overflow` inlines `stepPexprRaw_cAddBranch_overflow`'s
proof as `hcatch`; the `frXC…frA3C` frame-lookup boilerplate is EmittedB's
pattern copied. Zero-consumer declarations (DERIVED by grep, definitions
excluded): `mk_iop_sub_ival`/`mk_iop_mul_ival` (1 mention each, in a manifest
row string), `stdlibE3_symMap`, `prodFileWith_eq_lib`, `prodFileLib_stdlib`,
`isPePure_isReprBody`/`_convIntBody`/`_convLoadedIntBody`, `peDepth_convIntBody`/
`_convLoadedIntBody`, `PePure.strip`, `prod_run_eqJ_lib`, `prod_run_safe_lib`
(both pinned; the exhibit uses `prod_run_eqJ_lib1`). Class C5/C14 items.
Linter warnings: 60 at HEAD (baseline 60), none in an E3 module (measured:
Potential 46, Round 5, Rules 2, Heap 2, EnvLaws 2, TreeRot/Struct/ProdLoopExhibit 1).

### N-1 — CLAIMS row order C12, C13, C11 (cosmetic).

## 2. What was verified, by item of the brief

1. **The impl arithmetic.** `evalConvInt`/`evalWrapI`/`evalCatch` call the
   generated `mk_conv_int`/`mk_wrapI_op`/`mk_call_catch_exceptional_condition`
   VERBATIM at object integers, `none` otherwise (Step.lean:1352–1370); the
   engine arms :819–827/:828–838/:839–854 read arm by arm: same value cases,
   `Illformed_program` kills at non-integers (classifier `illtypedConvInt`/
   `illtypedWrapI`/`illtypedCatch`, messages identical to :824/:835/:851), the
   out-of-range `catch` → `Undefined.undef loc [UB036]` at `step_eval_pexpr`'s
   `loc` (= the thread's `current_loc`) → classifier `catchOut … = .undef loc
   [UB036]`. `mk_conv_int` (:61–81): `_Bool` ↦ 0/1; `min ≤ n ≤ max` ↦ id; else
   `mk_wrapI` — the design's §B4 table is right. `mk_iop` (:83–91): Add/Sub/Mul/
   Div/Rem_t over `opIval`; Shl/Shr as `IntMul/IntDiv x (IntExp 2 y)`. NO-RULE
   reasons TRUE by reading `CerbMem.opIval` (:1330–1360): `IntDiv` has the
   OCaml zero guard (`if n2 == 0 then 0`), `IntRem_t/IntRem_f` use Lean's
   total `tmod/emod` (a recorded divergence on an input the C elaborator's
   UB045 guard makes unreachable), `IntExp` is `n1 ^ n2.toNat`; the row's "the
   C elaborator guards `/` and `%` with an explicit zero check before this
   node" is the right reason to leave them NO-RULE. `minIval/maxIval (Signed
   Int_)` at `sizeof_ity = some 4`: `-2^31`/`2^31−1` — `int_min_eq`/`int_max_eq`
   are `rfl` (kernel) ✓. `OpAnd`/`OpOr` truth tables = :454–466/:502–511;
   at two INTEGERS the engine's `(_, int, int)` arm precedes and PANICS —
   `binopOut`'s int-int arm precedes too (`.uncovered`) ✓ (probe below).
   `Civmin/Civmax`: `unatomic_ ty`, `Basic (Integer ity)` → `minIval/maxIval`,
   else the engine's `error` PANIC → `none` (:632–647) ✓. `is_unsigned`:
   `AilTypesAux.is_unsigned_integer_type` (the one such def, generated) at a
   ctype; the :1086 `PEis_scalar` rebuild quirk is mirrored verbatim and
   fenced by `peDepth pe = 1` — honest. Probes: oracle and composite agree on
   `INT_MAX + 1` (UB036) and on `3 + 1` (4) — §3.
2. **std.core unfolding.** `lookupFun`/`callBody` = `call_function`'s success
   path (:124–156: `stdlib` first, `funs`, `Impl` → `impl0` `IFun`; arity;
   `foldl2 subst_sym_pexpr`) — proved as `call_function_of_callBody` (an
   equation, no hypothesis beyond `callBody = some`) and the failure twin
   `call_function_exception_of_callOut`. The one-pass return is the body
   UNEVALUATED after `pull_constrained 0` (:965–979) — mirrored by `peStrip`,
   whose arms I checked against `pull_constrained` (:199–307): `wrap`/`wrap_bin`
   arms (`PEop`, `PEarray_shift`, `PEnot`, `PEconv_int`, `PEwrapI`, `PEcatch`,
   `PEis_unsigned`) recurse into the operands; `wrap_list`/`pull_helper` arms
   (`PEctor`, `PEcall`, `PEif`) and the `PEcase` alternatives keep the ORIGINAL
   operands (the `Right` accumulator pushes `pe`, not `pe'`) — `peStrip`
   matches exactly, and the bridge discharges it by E2's `pull_bridge`
   (`hpull`). `PElet` is `wrap_bin` (strips the body): the withdrawal is
   forced, as recorded. Budget: `peDepth (PEcall …) = 1 + Σ args + stdBudget`,
   unfolding only if `peDepth (peStrip body) ≤ stdBudget nm` — the measure
   strictly decreases, so the joint induction is well-founded; the budgets
   4/17/23 equal the transcribed depths (`rfl`). Name collision: the budget
   only gates unfolding; the BODY is always the file's own (`callBody`), so a
   collision can cost `.uncovered`, never a wrong value — confirmed by reading.
   `stdlibE3` vs source: identical constructor for constructor (§B above); the
   speedbump compares TOKEN STREAMS (`pexprSkeleton` of the term vs
   `tokenizeFun` of the source body with comments stripped, `<Impl>` → `impl:`),
   three plants each applied to the row it fits, unplanted row = red; run at
   HEAD (verbatim, §3). The four oracle-cannot-print failures: one reproduced
   verbatim (§3).
3. **The file object.** `prodFileLib lib procs e := { prodFileWith procs e with
   stdlib := lib }`; the engine reads `file.stdlib` first in `call_function`
   AND in `call_proc`/`lookupProc` (hence `hmain`, discharged by
   `stdlibE3_no_main`); the driver's own `main` lookup is on `funs` (the
   collapse's `hlook`). Nothing else the engine reads on `progCE3` is missing
   (no `Impl` reached, no `funinfo`, no `globs`, `tagDefs = ∅` as before). The
   old forms are instances: `prodFileWith_eq_lib : prodFileWith procs e =
   prodFileLib fmapEmpty procs e := rfl`; `prod_run_eqJ_lib(1)`/`prod_run_safe_lib`
   are the `_procs`/one-procedure forms at that file with `DriverDoneCtl`/
   `DriverDoneAt` tied to it. The 268 file-parameter-forced changes: reproduced
   (DERIVED: 255 statements equal after deleting the file binder/argument
   tokens + 13 whose only change is the binder's position/shape, inspected;
   + 11 driver-lane tie (`DriverDoneAt … F`, `dst.core_file = F/M₀.file/
   spikeFile`, `prod_run_eqJ`'s `hdd` at `(prodFile e)`) + 56 loop-exhibit
   derivations at `procCtxF F rs` + 34 recursors/`eq_def`). None of the nine
   production statements nor `exhibitA_prod_e1`/`exhibitB_prod_e2` changed;
   `prod_run_eqJ`/`DriverDoneAt`/`hfile` are pipeline lemmas, not production
   statements. See D-6 for the disclosure gap.
4. **The integer rules.** `wps_c_add`/`wpt_c_add` = `wps_pure`/`wpt_pure`
   (E2's rules, `2 ≤ k`: the PURE round + delivery) at `evalPexpr_cAdd`, which
   is `select_case` at the concrete row + `evalPexpr_conv_int_int`
   (`mk_conv_int_int_in_range`) + `evalPexpr_catch_add_int`
   (`mk_call_catch_add_in_range`). Premises: operand values, six range facts
   (client obligations), the selected-branch equation `hsel` (a syntactic
   engine equation; `rfl` at distinct concrete `a' b'` — it also rules out
   `a' = b'`, correctly). Nothing hidden; the overflow is the client's excluded
   case, and its face is `evalClass_cAdd_overflow = .undef loc [UB036]` at the
   CLASSIFIER's `loc` (the thread's location), not the arm's `uloc` — matches
   :848. `wps/wpt_conv_loaded_int` carry `StdE3 M.file`. Budget: the exhibit's
   `progCE3_wpt` at 28 composes 3+3+4+7+5+3+3 (read), not claimed tight.
5. **Acceptance.** (i) `t1_uncovered_exactly_unseq : uncoveredKinds t1Main =
   ["unseq"] := by decide` — kernel `decide` (gate 1: no `native_decide`
   anywhere); the record and ARCHITECTURE call it a syntactic WALK and the
   mathematical statement is the pair `t1MainWith_frag (u) (hu : Frag u)` /
   `t1_unseq_not_frag` with `t1Main_eq_with … := rfl` — honest. (ii)
   `exhibitC_prod_e3`: statement = `runND (drive fmapEmpty false (prodFileLib
   stdlibE3 [] (progCE3 3)) args) (initial_driver_state sup … fs).1 = [(Active
   dres, [], dst')] ∧ dres.dres_core_value = lint 4 ∧ …` — program, file
   builder, engine, readout only. The literal-3 restriction is disclosed
   (module header, CLAIMS C13 exclusions, record §5.4/§7); the gap is real:
   `three_storable … := ⟨rfl, fun _ => rfl, …⟩` is `rfl` at the literal and no
   `StorableAt tds intTy (integerValueMval (Signed Int_) (integerIval n))`
   lemma exists (grep); registered in the record §7 but NOT in KOI (D-4).
   (iii) `overflow_driver2_killed(_frame)`: over the GENUINE `driver2_lemFuel`
   (generated `Driver.lean:381`) at `Nat.succ fl` from any state whose single
   thread is at arena `progCE3_atAdd` with `b1 ↦ Specified(INT_MAX)`, `b2 ↦
   Specified(1)`: `NDkilled (Undef0 th.current_loc [UB036])` via
   `step_ctx_pure_op_fail` → `loop_step_withrs_eval_killed` → `driver2_killed`.
   The location is the thread's `current_loc` ✓ (engine :848 `loc` = `step_ctx`'s
   thread location; the composite run below prints `exhibitC.c:1:36-41`, the
   preceding `Ewseq`'s `Aloc`, not the arm's line-2 `ecAddLoc`). The whole run
   is disclosed as a MEASUREMENT on every surface I read (module header, CLAIMS
   C13 exclusions, record §6, DECISIONS, README "over the genuine driver's
   round"). D-7 for "every fuel".
6. **Census.** Reproduced exactly (item 3 above; R-1 for the snapshot). 589
   pins: `trioExports` has 589 entries, 589 distinct (`sort | uniq -d` empty),
   `unspec_bytes` at position 509, 80 E3 names after it; trio-exactness of all
   589 is the in-build assertion (`export pins: 589 trio-exact`, §3).
7. **The rebase resolution.** Audit.lean: both groups present, no duplicates
   (above). CLAIMS: C12 byte-identical to f9c3c2e's (the range diff of CLAIMS is
   the single +C13 line); C13 is E3's. README/ARCHITECTURE: E3's superseding
   prose is in place (README :57–66, :183–196; ARCHITECTURE :109–125, :519–522)
   and the E2-fixes text survives (ARCHITECTURE :278–291 carries the completed
   E2 `eval_uncovered` list; `unspec_paddingByte` named at :524) — but the
   cites moved (D-1).
8. **Shop window.** Manifest header/tail at HEAD: "MANIFEST: 28 constructors,
   66 variant rows (37 RULE, 0 RULE-TOTAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 24
   NO-RULE, 5 OUT-OF-SCOPE), 0 red, 21 consumer modules / CLAIMS: 13 claim rows,
   119 declaration names checked / MODULES: 48 classified" and the boundary
   check's 23 modules — as recorded. `Frag.pure_op` OUT-OF-SCOPE row: updated
   for E3, not for E2 (D-4). Synthetic status: D-6.
9. **Records.** FULL gate run once (§3): line for line identical to the
   DECISIONS E3 entry's quoted tail (589 / 4725 / 7370 / 465 jobs / 17 core /
   23 modules / `ALL GATES GREEN`; exit 0). DECISIONS is chronological; the E3
   entry's counts/hashes match the tree (manifest numbers, census, REBASE
   description). Upstream note: substantive claim true, cite off by one (R-5).
10. **Grumpy read.** The new modules are clear and well-cited; StdCore is
    exemplary (source lines, symbol-identity note, budget ties). Over-elaboration
    is mild (H-1). One clarity nit: `stdBudget` is documented as "keyed by the
    printed name" — it is keyed by the `SD_Id` description string of the symbol,
    which is what `symbol_compare` ignores; the docstrings say so.

## 3. Plant/probe log (verbatim)

### 3.1 FULL gate at 825b5e6 (`CERB_MEM_MAX=40G scripts/test_unit.sh`, package pre-built; lines matching `^==|^ok:|^info: CerberusHeapLang|^ALL GATES|^Build completed|^BOUNDARY|^FAIL`, then `time`'s line and my `EXIT` echo)

```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:754:0: CerberusHeapLang export pins: 589 trio-exact
info: CerberusHeapLang/Audit.lean:754:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (4725 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:754:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (7370 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (465 jobs).
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
ok:   Examples.CallSmoke — 0 internals mentions
ok:   Examples.ReadinessSmoke — 0 internals mentions
ok:   Examples.Layout — 0 internals mentions
ok:   Examples.CorpusE0 — 0 internals mentions
BOUNDARY: 23 modules checked, 0 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
scripts/test_unit.sh  19.87s user 2.21s system 96% cpu 22.842 total
EXIT=0
```

Package linter warnings in the same log: 60 in `CerberusHeapLang/` (baseline 60).

### 3.2 The std.core speedbump section of that run (verbatim, gate log lines 3089–3097)

```
# E3: transcribed std.core fragment vs the pinned std.core source

| fun | tokens | term = source | plants (applicable: verdict) |
|---|---|---|---|
| is_representable_integer | 9 | equal | Ivmin/Ivmax swapped: mismatch (expected) |
| conv_int | 32 | equal | first if's branches swapped: mismatch (expected) |
| conv_loaded_int | 15 | equal | first case's alternatives reversed: mismatch (expected) |

corpus-skeleton: ok — 1 row(s) equal, every plant mismatches
```

### 3.3 HEAD signature snapshot (`../scripts/capped ~/.elan/bin/lake env lean scripts/signature_snapshot.lean`, 20.496 s wall) vs the committed post snapshot

```
$ cmp .audit-scratch/head-signatures.txt cerberus-heaplang/docs/2026-09-05_e3-signatures-post.txt
.audit-scratch/head-signatures.txt cerberus-heaplang/docs/2026-09-05_e3-signatures-post.txt differ: byte 1995394, line 35865
$ diff … | head
35865,35869d35864
< theorem CerberusHeapLang.unspec_bytes :
< ∀ (tds : CerbTags.TagDefsMap),
<   (CerbMem.memValueToBytes tds [] CerberusHeapLang.unspecMval).snd =
<     CerberusHeapLang.intUndefBytes tds
< ----
35874,35876d35868
< ----
< theorem CerberusHeapLang.unspec_paddingByte :
< CerbMem.paddingByte = CerberusHeapLang.undefByte
```

Census script over the two committed snapshots (DERIVED): `pre 3853 post 4162`,
`ADDED 312 REMOVED 3 CHANGED 369`, `REMOVED: ['CerberusHeapLang.CorpusE0.convLoadedIntSym',
'CerberusHeapLang.CorpusE0.t1_case_uncovered', 'CerberusHeapLang.CorpusE0.t1_convLoadedInt_uncovered']`;
production statements `exhibitA_prod`, `counter_loop_`/`fib_`/`list_reverse_`/
`dispose_list_`/`region_loop_`/`malloc_list_`/`fib_rec_`/`even_odd_certified_production`,
`exhibitA_prod_e1`, `exhibitB_prod_e2`: all `SAME`.

### 3.4 Executable probe of the shipped composite (a scratch Lean file importing `CerberusHeapLang`, `lake env lean` under `capped`, 2.9 s wall; output verbatim)

```
"killed undef ubs=1 ub036=true loc=exhibitC.c:1:36-41 out=[]"
"active value=Specified(4) blocked=false out=[]"
"active value=Specified(-2147483647) blocked=false out=[]"
[(0, "killed error0 loc=other_location(lem: fuel exhausted) msg=lem: fuel exhausted"),
  (1, "active value=Specified(4) blocked=false out=[]"), (2, "active value=Specified(4) blocked=false out=[]"),
  (3, "active value=Specified(4) blocked=false out=[]"), (4, "active value=Specified(4) blocked=false out=[]"),
  (5, "active value=Specified(4) blocked=false out=[]")]
"OpAnd int int: uncovered"
"kill"
"__conv_int__(INT_MAX+1): val -2147483648"
"catch_div(7,0): val 0"
```

Lines: (1) `runND (drive fmapEmpty false (prodFileLib stdlibE3 [] (progCE3
2147483647)) []) (initial_driver_state 0 … default).1` — the UB036 kill at the
thread's location (the record's measurement reproduced; location printed by
`CerbLocation.stringFromLocation`); (2) `progCE3 3` → `Specified(4)`; (3)
`progCE3 (-2147483648)` → `Specified(-2147483647)`; (4) `CerbND.drive_lemFuel k`
for k = 0..5 on `progCE3 3`: fuel 0 = the sentinel, every positive outer fuel
completes (KOI A2's reading confirmed: the outer fuel bounds `driver2` rounds
only); (5) `evalClass … (PEop OpAnd 1 2) = .uncovered` (the engine panics
there — fail-closed); (6) `evalClass … conv_loaded_int('signed int',
Specified(2147483648)) = .kill` on the E3 file (the `Impl` call, D-6); (7)
`evalClass … (PEconv_int (Signed Int_) 2147483648) = .val -2147483648`
(`mk_conv_int`'s wrap); (8) `evalClass … catch_exceptional_condition_div(7, 0)
= .val 0` (the memory model's zero-guarded `IntDiv`; the NO-RULE row's reason
verified).

### 3.5 The pinned OCaml oracle (from the container root; commands verbatim)

```
$ scripts/ce cerberus-lean/_build/default/backend/driver/main.exe --nolibc --exec refined-cerberus/worktrees/audit-e3-825b5e6/.audit-scratch/oracle/ovf.c
refined-cerberus/worktrees/audit-e3-825b5e6/.audit-scratch/oracle/ovf.c:1:46: error: undefined behaviour: an exceptional condition occurs during the evaluation of an expression
int main(void) { int x = 2147483647; int y = x + 1; return y; }
                                             ~~^~~ 
§6.5#5: 
5   If an exceptional condition occurs during the evaluation of an expression (that is, if the
    result is not mathematically defined or not in the range of representable values for its
    type), the behavior is undefined.
exit=0
$ scripts/ce cerberus-lean/_build/default/backend/driver/main.exe --nolibc --exec refined-cerberus/worktrees/audit-e3-825b5e6/.audit-scratch/oracle/ok.c
exit=4
$ scripts/ce cerberus-lean/_build/default/backend/driver/main.exe --nolibc --pp=core refined-cerberus/worktrees/audit-e3-825b5e6/.cerberus-ws/runtime/libcore/std.core 2>&1 | tail -5
unknown location  error: multiple declaration of 'unspec_to_zero_proxy'
exit=0
```

(`ovf.c` = `int main(void) { int x = 2147483647; int y = x + 1; return y; }`;
`ok.c` the same at 3. The oracle's `--pp=core ovf.c` emits the `+` as
`case (a_510, a_511) of | (Specified(a_512: integer), Specified(a_513: integer)) =>
Specified(catch_exceptional_condition_add('signed int', __conv_int__('signed int', a_512),
__conv_int__('signed int', a_513))) | _: (loaded integer,loaded integer) =>
undef(<<UB036_exceptional_condition>>) end` — `cAddPats`'s shape.) The oracle's
UB location is the `+` expression's source range (1:46–50), the composite's is
the synthetic program's `Ewseq` `Aloc` (1:36–41 = the `x + 1` range in
`exhibitC.c`): both are the thread's current location.

### 3.6 Pin list

```
$ sed -n '190,752p' Audit.lean | grep -o '``CerberusHeapLang[…]*' | wc -l   → 589
$ … | sort | uniq -d | wc -l                                              → 0
$ grep -n unspec_bytes pins.txt                                           → 509
$ awk 'NR>509' pins.txt | wc -l                                           → 80
```

## 4. What I did NOT check

- `Soundness.lean`'s 30 file-threading inversion arms individually (read at
  declaration level and the E3 arms of `step_eval_bridge`/`stepFail_bridge`/
  `evalPexpr_peStrip`/`PePure.strip`); `Wps.lean`/`Wpt.lean` diffs (census:
  file-threading only); the loop exhibits' `procCtxF` refactor beyond the
  census classification.
- The kernel-side non-reduction claim of the record §6 (`decide +kernel` on the
  whole run) — not re-measured.
- The oracle at other `iop`s (`-`, `*`, `/`, shifts) and at `wrapI` (unsigned);
  the `is_unsigned` rebuild quirk by execution.
- That `pull_bridge` (E2) is stated exactly as the E3 call arm consumes it
  (took the green build as the evidence).
- The E4 worktree and anything outside the audit copy.
