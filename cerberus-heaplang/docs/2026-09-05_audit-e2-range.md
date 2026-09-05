# Range audit: E1 fixes + E2 (`3e75a1e..b5ed995`, the emitted-Core dialect slice 2) — 2026-09-05

**VERDICT: PASS WITH FIXES REQUIRED — grade A− (the loaded-value evaluator, the one-pass mirror, the `undef` KILL face, the tuple binders and the `Unspecified` store are exact against the generated engine at the pin, executably as well as by kernel-checked equation; the fixes are one instrument-hygiene defect — the corpus-skeleton speedbump fails SILENTLY — and a set of stale or over-stated sentences on the shop-window and record surfaces).**

Auditor: fresh, independent, on the fixed detached copy `worktrees/audit-e2-b5ed995`
(HEAD `b5ed995`, detached). Standard: `docs/AUDIT-BRIEF.md`; the mirror-OCaml
doctrine (every mirrored engine behaviour = the generated Lean at the pin
`f95ef8d9c`, exactly). Every lake/lean invocation went through `scripts/capped`
with `CERB_MEM_MAX=40G` (one builder at a time; another build ran concurrently
in `dialect-e1`, untouched). Nothing committed, merged or pushed; no other
worktree, the primary checkout or `main` touched. Scratch lived in the copy's
untracked `.audit-scratch/` (deleted at the end; every output quoted below is
verbatim from it). Provenance: [AUDITOR] for everything I measured or judged;
quotes are verbatim; tallies marked DERIVED are mine.

Range: `9ea6c93` (E1 audit report copied), `16bcfdc` (E1 fixes), `f6e54e5`
(E2 1/n: evaluator, classifier), `eaafebc` (E2 2/n: rows, binder rules,
exhibit B, pins), `ef26e2f` (E2 3/n: corpus skeleton into pure expressions),
`192a82f` (E2 4/4: records, closure successor, census, docs pass), `b5ed995`
(DECISIONS/KOI, two upstream notes). `git diff --stat`: 48 files,
+47868/−2492 (37186 of the additions are the post snapshot).

## 0. What was measured

- FULL gate run on the copy (`scripts/test_unit.sh`, capped, 40G): a cache
  REPLAY of the primed tree (50 `Replayed` lines) — verdict tail in §11, exit 0;
  60 package linter warnings, each blamed to a pre-range commit (§9).
- The generated engine at the pin read arm by arm against the mirror:
  `core_eval.lem:536–604` (step_eval_pexpr's wrapper `Pexpr [] () <$>`, `strip`,
  `PEsym`, `PEundef`'s `loc'` resolution), `:607–723` (`PEctor`: `EU.mapM self
  pes`, the `Ctuple`/`Cspecified`/`Cunspecified` arms, the `(_, Nothing) ->
  PEctor ctor pes'` rebuild, the `(_, Just cvals)` kill), `:725–745` (`PEcase`:
  `select_case subst_sym_pexpr cval pat_pes` → `strip pe''` UNEVALUATED, no
  match → `error`), `:794–815` (`PEnot`), `:1008–1047` (`PEif`: `strip <$> self
  pe2` in the SAME pass), `:1110–1145` (`eval_pexpr_aux2`: pull, one pass, value
  test, recurse); `core_aux.lem:2014–2058` (`match_pattern`/`select_case`),
  `:2426–2450` (`update_env_aux`: the `Ctuple` `foldr` over the truncating
  `zip`, the `CaseCtor ctor pats, _` catch-all `error`); `core_reduction.lem:
  283–299` (PURE), `:320–339` (Ecase EVAL/CASE), `:386–425` (LETW-PURE/ANNOT,
  LETS-PURE/ANNOT); `driver.lem:171–185` (`liftCore_run`); the generated
  `Core_eval.lean:155–158` (`eval_pexpr_aux2_lemFuel`), `Core_aux.lean:855–866`
  (`update_env_aux_lemFuel`: the catch-all is LemLib's opaque `failwithI`, zero
  `panic!` in the file), `Core_reduction.lean:84–100` (`eval_pexpr20` passes
  `th_st.current_loc`; `full_eval_pexpr_lemFuel`), `CerbMem.lean:565–600`,
  `:683–697` (`paddingByte`, `memValueToBytes`'s `MVunspecified` arm),
  `Core_aux.lean:104` (`memValueFromValue`'s `Vloaded (LVunspecified ty')` arm
  at ANY `ty`).
- The mirror read: `Step.lean` (`peDepth`, `evalTyCtor`, `evalCtor`,
  `isMirroredCtor`, `isPePure`, `stepPexprRaw`/`stepPexprsRaw`/`stepPexpr`,
  `evalPexpr`/`evalPexprList`, `TupleLeaf`/`tuplePat`, the seven E2 `Step`
  constructors), `Soundness.lean` (`PePure`, `Frag`, `step_ctx_pure_op_raw`,
  `step_ctx_sseq_val_pure`, `aux2_bridge`, `step_eval_bridge`,
  `stepPexpr_of_PePure`/`_shape`, `evalPexpr_step`, `pull_bridge`),
  `EvalClass.lean` in full (2090 lines), `Round.lean` (`ShippedRefusal`,
  `OpenRound`, `update_env_aux_tuple_mismatch`, `complete_beta_tuple`,
  `complete_wbeta_tuple`, `complete_wbeta_sym`, `complete_pure_op`,
  `frag_round_complete`, `cerberusRound_classify`), `EmittedBExhibit.lean` in
  full, `Examples/CorpusE0.lean` (header, plants, t1, witnesses, table, ledger),
  `scripts/corpus_skeleton.lean`, `Examples/MirrorCoverage.lean` (diff),
  `Audit.lean` (diff), `Heap.lean:212` (`StorableAt`), `AllocExhibit.lean:88`.
- EXECUTABLE PROBES (`.audit-scratch/Probe.lean`, `lake env lean`, capped): the
  SHIPPED COMPOSITE `CerbND.runND (drive fmapEmpty false (prodFile p) [])
  (initial_driver_state 0 (prodFile p) CerbFS.fs_initial_state).1` on four
  programs (UB036 at a non-library undef location; UB036 at a LIBRARY undef
  location; a `case` matching NO pattern; exhibit B as control) beside the
  mirror classifier `evalClass` on the same operands; `select_case`/
  `stepPexprRaw`/`evalPexpr` at the no-match operand; the `Unspecified` byte
  image by `rfl`; `Lean.collectAxioms` on the 82 pins new in the range and on
  `pull_bridge`; seven corpus-skeleton plants by term surgery on `t1Main`
  (§6); the N-2 "file without a row" plant against the real script; a
  two-line test of `IO.Process.exit` inside `#eval` (§6, H-1).
- Census reproduced from the two committed snapshots by my own parser; the
  HEAD snapshot regenerated and `cmp`'d; the 50 CHANGED names partitioned
  against the record's three lists by set comparison (§8).
- The six externally visible `EvalClass` statements diffed pre/post (source
  text and machine-printed type); the 28 `Frag` constructors diffed pre/post
  as normalised full text (comments stripped) (§5, §7).
- 140 `file:line` cites of ARCHITECTURE checked against the declaration lines
  at HEAD by script (§10).

## 1. Loaded values and the pure evaluator (PASS)

**Constructors.** `evalCtor` (Step.lean:1518): `Civalignof/Civsizeof/
Cunspecified` at `[Vctype ty]` through `evalTyCtor` (`Cunspecified ↦ Vloaded
(LVunspecified ty)`), `Cspecified [Vobject ov] ↦ Vloaded (LVspecified ov)`,
`Ctuple vs ↦ Vtuple vs`, everything else `none` — EXACTLY `core_eval.lem:614–
615, 680–683` (`(Ctuple, Just cvals) -> Vtuple cvals`, `(Cspecified, Just
[Vobject oval])`, `(Cunspecified, Just [Vctype ty])`). The engine's other
success arms (`Cnil`/`Ccons`/`Carray`/bitwise/`Cfvfromint`/`Civfromfloat`/
`CivNULLcap`) are outside `isMirroredCtor` and hence outside `PePure` —
fail-closed by grammar. The engine's `(_, Just cvals)` KILL (an ill-typed
constructor application, e.g. `Specified(Unspecified(int))`) is classified
`.uncovered` by `stepFailList` (all operand passes succeed → `stepFailList []
= .uncovered`), as the EvalClass header says ("a constructor dispatch
failure") — fail-closed, no engine claim; a computable kill left as a mover
(N-1).

**The one pass.** `stepPexprRaw` (Step.lean:1583) is `step_eval_pexpr`'s
body arm for arm: `PEval v ↦ valPe v`; `PEsym ↦ lookup_env (resolveExtern ext
x) ρ` (the engine's `Map.lookup sym core_extern` then `lookup_env`; the
unbound-`Proc` null-pointer arm is `none` → classified); `PEop`/
`PEarray_shift`: both operands passed, dispatch at two values, else the node
REBUILT with the passed operands (the engine's `EU.return (PEop …)` shape);
`PEctor`: `stepPexprsRaw` (= `EU.mapM self pes`), dispatch at all-values,
else `PEctor c rs` rebuilt; `PEcase`: the scrutinee passed, at a value
`(select_case subst_sym_pexpr cval pats).map reannot0` — the engine's
`EU.return (strip pe'')` under the wrapper `Pexpr [] () <$>` IS `reannot0`
(`strip (Pexpr _ _ pe_) = pe_`, lem:545), the branch UNEVALUATED; at a
non-value `PEcase r pats` rebuilt; no match → `none` (engine: `error`, the
opaque `failwithI` PANIC — classified `.uncovered`, §2); `PEnot`: `Vtrue ↦
Vfalse`, `Vfalse ↦ Vtrue`, other value → `none` (engine `EU.fail
illtypedPEnot`, classified `.kill`), non-value → `PEnot r`; `PEif`: guard
passed, `Vtrue ↦ (stepPexprRaw pe2).map reannot0` (the engine's `strip <$>
self pe2`, the branch evaluated IN THE SAME PASS — verified at lem:1013–1016),
`Vfalse` likewise, other value → `none` (kill), non-value → `PEif r1 pe2
pe3`. The pattern matcher is the ENGINE'S OWN `select_case subst_sym_pexpr`
(generated `Core_aux`), not a re-implementation — so tuple/`Specified`/
wildcard matching and the no-match `Nothing` are the engine's by definition.
`step_eval_bridge` (Soundness.lean:3911, pinned trio-exact) is the
arm-by-arm equation `step_eval_pexpr_lemFuel fuel … pe = exception_undef_return
r` at every `fuel ≥ peDepth pe`, every level counter, location, call location,
memory; `stepFail_bridge` (EvalClass.lean, pinned) is its failing twin.

**The pass count.** `eval_pexpr_aux2_lemFuel (n+1)` = pull, ONE
`step_eval_pexpr` pass, `valueFromPexpr` test, recurse at `n`
(Core_eval.lean:155, verbatim read). `case` returns the selected branch
unevaluated, so its value costs a further pass; `evalPexpr_case` recurses on
`reannot0 pe''` under the guard `peDepth (reannot0 pe'') ≤ peDepthAlts pats`
(Step.lean:1667) so the depth strictly decreases per non-value pass
(`evalPexpr_step`). `aux2_bridge` (Soundness.lean:4260, pinned) states the
round budget as `peDepth pe ≤ fuel + 1 → eval_pexpr_aux2_lemFuel (fuel + 1) …
= return (inr v)` — i.e. actual fuel `F = fuel + 1 ≥ peDepth pe` rounds,
which by the strict decrease is enough (a term of depth `d` needs at most `d`
passes). The PRE-E2 statement had NO fuel premise at all (any `fuel + 1`
sufficed: the E1 grammar evaluated in one pass) — so E2 ADDED a premise, a
forced weakening correctly listed in the census's forced class; the closure
record's parenthetical "the E1 statement was at `peDepth pe ≤ fuel`" is
wrong (R-1). `pull_bridge` (`pull_constrained` is annotation renormalisation
on `PePure`) is sub-trio `[Quot.sound, propext]` (measured, §8) and
correctly unpinned.

**Executable agreement** (§A.1): exhibit B through the shipped composite
delivers `Active value=Specified(4)` — the value the mirror evaluator
computes (`casePe_eval`, `specSum_select` by `rfl` through the engine's own
`select_case`).

## 2. `undef(<<UB>>)` as a KILL (PASS — exact, executably)

Engine (lem:596–604): `loc' = match (ub, parent_call_loc_opt) with |
(UB088, Just call_loc) -> call_loc | _ -> if is_library_location undef_loc
then loc else undef_loc`, then `Exception.return (Undefined.undef loc' [ub])`,
where `loc` is `eval_pexpr20`'s `th_st.current_loc` (Core_reduction.lean:84)
on the thread the closure `full_eval_pexpr'` captured — the ORIGINAL thread,
before the general arm's location write (the E1 audit's finding, §1 there).
`liftCore_run` (driver.lem:171–185 / Driver.lean:247): `U.Undef loc ubs ->
ND.kill (ND.Undef loc ubs)` = the shipped `Undef0 loc1 ubs`. Mirror:
`undefOut loc undef_loc ub` (EvalClass.lean) = `.uncovered` at UB088 (the
call-location parameter — fail-closed, no engine claim), else `.undef (if
isLibraryLocation undef_loc then loc else undef_loc) [ub]`; `complete_pure_op`
passes `ctl.curLoc` (the PRE-update location) as `loc`;
`full_eval_bridge_undef` is stated at `th.current_loc`; `EvalFail.reason
(.undef l u) = Undef0 l u` (`rfl`, checked); the round is
`ShippedRefusal.killed fl.reason` through `step_ctx_pure_op_fail` +
`advance_withrs_failed_eval` (both pinned). Never a default: the mirror
evaluator answers `none` (`evalPexpr_undef`), no `Step` rule fires, the
refusal arm carries the engine's own `NDkilled (Undef0 …)`.

Executable probe (§A.1, the shipped composite, no mirror): a program whose
`case` hits the wildcard `undef(<<UB036>>)` at a non-library location
`exhibitB.c:3:10-20` → `Killed Undef0 loc=exhibitB.c:3:10-20
ubs=[UB036_exceptional_condition]`; the mirror classifies the same operand
`undef loc=exhibitB.c:3:10-20 ubs=[UB036_exceptional_condition]` — EXACT
(constructor, location, UB list). At a LIBRARY undef location the engine
reports `loc=other_location(Driver.drive)` — the PARKED thread's
`current_loc`, NOT the redex node's own `Aloc exhibitB.c:9:1-40`, confirming
original-thread evaluation — and the mirror at `ctl.curLoc = other
"Driver.drive"` answers the same. Both agree; the `.undef` face is the
engine's exact outcome.

## 3. Store of `Unspecified(ty)` (PASS; R-2 on the header's attribution)

Engine: `memValueFromValue ty (Vloaded (LVunspecified ty'))` = `some
(unspecifiedMval ty')` at ANY `ty` (Core_aux.lean:104, the `_, Vloaded
(LVunspecified ty') => some (CerbMem.unspecifiedMval ty')` arm);
`memValueToBytes` at `MVunspecified ty` = `(fpm, List.replicate (sizeofCtype
ambient ty) paddingByte)` with `paddingByte = { prov := .Prov_none,
copyOffset := none, value := none }` (CerbMem.lean:569, 587–589). The
exhibit: `unspec_encodes` (`rfl`) is that arm at `intTy`; `unspec_storable :
StorableAt tds intTy unspecMval` (`rfl` at GENERIC `tds`) is the five
`StorableAt` fields (`compat`, `fpm`, `len`, `bytes_fpm`, `stored_dec`,
Heap.lean:212–229) — NONE of which states the byte list. The rule `wps_store`
(Wps.lean:3149) concludes the cell at `(memValueToBytes M.tagDefs [] mv).2`
— the ENGINE'S image, not a claimed list — so the exhibit's statement never
asserts what the unspecified bytes are; the final `CellCoh … fourBytes` is
the image of `fourMval`, again `memValueToBytes` by definition. Correct and
honest at the statement level. The module header's sentence "which is
byte-for-byte the fresh cell's `undefByte`s; measured, not assumed:
`unspec_storable`" attributes to `unspec_storable` a fact it does not
state. The fact IS true: `example (tds) : (CerbMem.memValueToBytes tds []
unspecMval).2 = intUndefBytes tds := rfl` and `example : CerbMem.paddingByte =
undefByte := rfl` both elaborate (§A.1, my probe) — the design note §B3's
open measurement, closed here. R-2: reword, or add that one-line theorem
(it is what the header claims exists).

## 4. Tuple binders (PASS; the classification is honest)

Engine LETS-PURE/LETW-PURE (lem:407–414 / 389–396): `Esseq pat (Expr _
(Epure pe1)) e2` at `valueFromPexpr pe1 = Just cval` → `TAU (update_env pat
cval env) e2`; the `-ANNOT` arms → `TAU … (Expr [] (Eannot xs e2))`.
Mirror `Step.sseq_tuple_pure/annot`, `wseq_tuple_pure/annot`,
`wseq_sym_pure/annot` (Step.lean:2724–2762): head `ofValA (.pure a1 b1
(Vtuple vs))` / `(.annot a1 a2 b1 ds (Vtuple vs))`, successor `e2` / `Expr []
(Eannot ds e2)` at `update_env (tuplePat pa ls) (Vtuple vs) (ev0 :: evs)` —
the ENGINE'S `update_env` (so the `Ctuple` arm's `foldr` over the truncating
`zip`, core_aux.lem:2444–2447, is inherited: any arity is a step, as the
record says), control `ctl.upd a`. Engine equations
`step_ctx_sseq_val_pure/_annot`, `step_ctx_wseq_val_pure/_annot`
(Soundness.lean:6098 …) are pattern-GENERIC (one equation per binder kind)
and pinned trio-exact; `update_env_tuple2` computes the two-leaf binding by
`rfl` through `update_env_aux_lemFuel`. The weak plain-symbol binder binds
any value verbatim (`CaseBase (Just sym, _)` arm) — `complete_wbeta_sym` is
always a step.

The NON-tuple head: `update_env_aux`'s catch-all `(CaseCtor ctor pats, _)` is
`failwithI ("WIP: Core_aux.update_env_aux ==> …")` in the generated Lean
(Core_aux.lean:861–866; ZERO `panic!` in `Core_aux.lean` — this is LemLib's
OPAQUE `failwithI`, not a `panic!`-`Inhabited` arm, so KOI A5's
"kernel reads it as `default`" does NOT apply here: the kernel has no
equation for it). `update_env_aux_tuple_mismatch` (Round.lean:2609): `∃ msg,
update_env_aux (tuplePat pa ls) v ev0 = failwithI msg` for every `v ≠ Vtuple
_` — proved by `cases v` at the concrete fuel; `complete_beta_tuple`/
`complete_wbeta_tuple` classify it as `ShippedRefusal.panic_env msg` (the
PRE-EXISTING arm, Round.lean:284 at `3e75a1e`, whose statement is "the step
is a TAU whose successor thread's ENVIRONMENT HEAD is `failwithI msg`" — the
Lean definition's behaviour, with the docstring stating that OCaml's strict
`update_env` aborts during the round while Lean's opaque term defers the
abort to the first read). Honest on both counts. Two wording items: the
record and the closure note call it `ShippedRefusal.panic` (R-1), and the
`panic_env` docstring still names only "a `Cspecified` binder meeting a
non-`Specified` value" (D-3). The executable probe's no-match `case` (§A.1)
shows the compiled face of the same family: `PANIC at
_private.LemLib.0.failwithIImpl … PEcase, mismatched` and the run CONTINUES
to `Active value=<non-int>` — the mirror answers `.uncovered` for it, which
is the right fail-closed reading.

## 5. `Frag.pure_sym` → theorem; `Frag.pure_op`; completeness (PASS)

Full-text diff of the two `Frag` inductives (comments stripped, §A.4): 25 →
28 constructors; REMOVED `pure_sym`; ADDED `pure_op {an pe} (hnv :
valueFromPexpr pe = none) (hp : PePure pe) (hd : peDepth pe ≤ lemDefaultFuel)`,
`sseq_tuple`, `wseq_tuple`, `wseq_sym`; the other 24 constructors TEXTUALLY
IDENTICAL. `Frag.pure_sym` (Soundness.lean:6553) is a theorem with the
constructor's exact statement (census: `ctor` → `theorem`, type identical),
proved as `.pure_op rfl (.sym pb x) (peDepth_sym_le pb x)`. Hence every
pre-E2 `Frag` derivation is a post-E2 derivation (the one retired
constructor is an instance) and the generalisation is conservative — and it
is a genuine generalisation (`PePure` grew by five arms, all of which
`pure_op` now reaches). `frag_round_complete` (Round.lean:6162): statement
verbatim the 2026-09-02 one (census: unchanged); the dispatch gains
`pure_e → complete_pure_op`, `beta_tuple`/`wbeta_tuple`/`wbeta_sym` arms;
`OpenRound` keeps its two arms (Round.lean:365–400, `eval_uncovered` now
listing the `Ecase` scrutinee in `operandsOf`); `ShippedRefusal` gains no arm
(the `killed` arm now also carries `Undef0` through `EvalFail.reason`). The
`.uncovered` face's new members — UB088, a `case` matching no pattern, a
branch the depth guard rejects, the undef-then-raise constructor list, a
constructor dispatch failure — each answer `.uncovered` with no engine claim
(`OpenRound.eval_uncovered` states only the step's SHAPE), and the EvalClass
header lists them. Fail-closed as required.

## 6. `conv_loaded_int`, t1, the skeleton speedbump (PASS as a speedbump; H-1)

`t1_convLoadedInt_uncovered : isPePure (convLoadedInt a508) = false := by
decide` and `t1_case_uncovered` (CorpusE0.lean) are kernel-decided;
`convLoadedInt` is `PEcall (Sym …)`, admitted by no `PePure` arm, so
`Frag.store_op` (which requires `PePure` operands) rejects t1's two stores
and its `run` argument — t1's `main` is not in `Frag`. Confirmed by
reading; NOTE that `¬ Frag t1Main` is not itself a stated theorem (the
README/CLAIMS phrase "decided by the kernel (`t1_convLoadedInt_uncovered`,
`t1_case_uncovered`)" names the operand-level decisions, from which the
whole-term exclusion follows by the `Frag` grammar — N-4, wording).

**What the extended check compares now** (CorpusE0 header, verified against
`pexprSkeleton`/`pexScan`): the preorder skeleton of expression nodes
(printed `Astd`s in reverse order, a `loc` marker when `get_loc` finds an
`Aloc`, the node keyword) PLUS, since E2, the constructor-level skeleton of
the pure expressions under `pure`, under every action's operands and under
`run`'s arguments — `Specified`/`Unspecified`/`Ivalignof`/…, `tuple`,
`case`/`alt`/`endcase`, `undef`, `not`, `if`/`then`/`else`, `op`,
`array_shift`, `__conv_int__`, `catch_exceptional_condition_<op>`, a
`PEcall`'s printed name; symbols, literals, ctypes and typed pattern binders
are the opaque token `leaf`. Still OPAQUE (annotation-free checked only):
`save` initialisers, expression-level `if`/`case` scrutinees, `Elet`,
`memop`, `pcall`/`ccall` arguments. Fail-closed where blind: a printed
annotation inside a pure region, a marker in an opaque region, list
literals, out-of-vocabulary constructors/values are ERRORS.

**Plants** (§A.3, my term surgery on `t1Main`, tree untouched): the three
recorded plants RED (bound dropped at token 13, `Astd` stripped at 13,
`Specified` unwrapped at 17); MY plant `Specified(3)` → `Unspecified(int)`
RED at token 17 (`Unspecified` vs `Specified`); the case's undef arm dropped
RED (token 67); the arms swapped RED (53); `conv_loaded_int(a)` → `a` in the
store RED (22); an `Aloc` inside a pure `Specified` → ERROR (fail-closed);
constant 3 → 4 PASSES (the documented `leaf` blind spot). t1 stream 118
tokens ✓ (record §6). The N-2 fix is REAL: a corpus file without a table
row (`docs/corpus-e0/zz_plant.annot.core`, created and deleted) makes the
script exit 1.

**H-1 — but the failure is SILENT.** `scripts/corpus_skeleton.lean:155` ends
`main` with `IO.Process.exit 1`. Inside `#eval`, Lean captures the action's
stdout/stderr to emit as a message AFTER evaluation; `IO.Process.exit`
terminates the process first, so EVERY diagnostic the script prints on
failure — the coverage-sweep `FAIL: corpus file … has no transcription row`,
the `skeleton ≠ text` first-difference lines, the plant verdicts — is
discarded. Measured: the N-2 plant run produced exit 1 with stdout AND stderr
EMPTY but for `capped`'s env line (§A.3, twice, stdout and stderr captured
separately); a two-line control (`IO.println; IO.eprintln; IO.Process.exit 1`
under `#eval`) prints nothing; the same with `throw (IO.userError …)` prints
both lines plus `error: corpus-skeleton: FAIL` and exits 1 (§A.3). The gate
therefore reports `FAIL (speedbump): corpus skeleton red (a transcription
drifted …, the tokenizer hit a blind spot, or a plant matched …)` with no way
to tell which — a fail-noisy defect in an instrument whose whole point is to
say WHERE the transcription drifted. The other two Lean instruments use
`throw`/`throwError` (`capability_manifest.lean:332`,
`parametric_inventory.lean:242–290`) and do not have this problem. Fix: replace
`IO.Process.exit 1` with `throw (IO.userError "corpus-skeleton: FAIL")`.

## 7. `EvalClass.lean` rewritten (PASS)

The six statements named in the record §7.12 — `evalClass_val_iff`,
`evalClassList_vals_iff`, `full_eval_bridge_kill`, `eval1_bridge_kill`,
`mapM_eval1_kill`, `mapM_save_kill` — have IDENTICAL machine-printed types in
the two snapshots (census: `unchanged`); in source, `evalClassList_vals_iff`
moved its five leading binders into a `variable` block (type unchanged), and
the two `_kill` bridges became one-line corollaries of their `_fail` twins.
Other public changes in the module are exactly the census's forced list
(`aux2_bridge_kill`, `evalClass_of_none`/`evalClassList_of_none` three-way
through `fail?`, `binopOut`/`shiftOut` returning `StepFail`,
`foldM_args_kill`/`step_ctx_run_kill` at `evalClassFold`,
`step_eval_bridge_kill` at `stepClass`) and the deletions listed in §8. The
pass structure is the engine's (§1): `stepClass` = one pass, `classIter` = the
iteration under the mirror's depth guard, `evalClass` = the mirror's value
where it has one, `classIter` otherwise; `evalClass_val_iff` keeps the `.val`
face equal to the mirror evaluator. The bridge is proved level by level in
the success bridge's shape (`stepFail_bridge` → `stepClass_bridge_fail` →
`classIter_bridge` → `aux2_bridge_fail` → `full_eval_bridge_fail`/
`eval1_bridge_fail`), with both faces through the one currency `EvalFail`
(`.pure`/`.run` its two monadic renderings; `runEU_fail`,
`stExceptUndef_bind_fail_apply` the laws).

## 8. Census, pins, snapshot (PASS)

- HEAD snapshot regenerated (`lake env lean scripts/signature_snapshot.lean`,
  capped) and `cmp`'d against `docs/2026-09-05_e2-signatures-post.txt`:
  `CMP-IDENTICAL` (37186 lines).
- My parser (records split on `\n----\n`, name = second token of the first
  line): `PRE 3406 POST 3853 ADDED 459 REMOVED 12 CHANGED 50` — the record's
  line reproduced exactly. The 50 CHANGED names equal, as a set, the union of
  the record's three lists (18 value-currency-forced + 1 H-2 + 31
  recursors/equations): `record minus mine: set()`, `mine minus record:
  set()` (§A.4). My reading of the 18: every one is either a statement over
  the one-pass mirror/`StepFail`/`EvalFail` (the currency), a recursor-shaped
  equation of a definition that grew, or the `case_inv`/`sseq_inv`/`wseq_inv`
  disjunctions widened by the new constructors — none re-shapes an adequacy
  or production statement. The 31 are recursors/`casesOn`/`below` of
  `Decomp`/`EvalListOut`/`EvalOut`/`Frag`/`PePure`/`Redex`/`Step` — extended
  inductives. The 1 is `wpt_driver_aux` (`sp` dropped; the theorem is
  unpinned and internal).
- The 22 headline statements ALL `unchanged`, incl. the nine production
  statements, `prod_run_eqJ_procs`, `prod_run_safe_procs`,
  `fib_rec_certified`, `even_odd_certified`, `MemTriple`/`SemTriple`/
  `MemTriple_alloc`, `engine_adequacy`, `frag_round_complete`,
  `engine_step_matchU`, `cerberusRound_classify`, `step_iff_cerberusRound`,
  `exhibitA_prod_e1`; also `DriverSafeCtl`/`DriverDoneCtl` (types).
- REMOVED (12), all accounted for: `Frag.below.pure_sym` (the constructor
  retired), `evalPexpr_none_of_shape` (false once `case` selects by value),
  `stExpect_mapM_eval1_kill`/`stExpect_mapM_full_eval_kill` (subsumed by the
  `_fail` forms), `binopOut_val_iff`/`shiftOut_val_iff` (the functions no
  longer return values), `evalClass_peStrip`/`peStrip_idem` (moved to
  `stepPexpr_peStrip`/`isPePure_peStrip`), `evalClass.eq_def`/
  `evalClassList.eq_def`/`evalPexpr.induct`/`isPePure.induct`
  (auto-generated for re-shaped definitions). None was pinned.
- `pull_bridge` unpinned: `collectAxioms` = `#[Quot.sound, propext]` (§A.2),
  sub-trio as the record and `Audit.lean`'s comment say — the correct
  disposition under the exact-trio pin rule.
- Pins: 80 E2 names + the 2 N-3 names = 82 listed; `trio-exact: 82 / 82`
  (`[Classical.choice, Quot.sound, propext]` each, §A.2); 428 + 80 = 508 ✓
  (gate: `508 trio-exact`).

## 9. The E1 fixes (all genuinely applied)

| id | finding | verified how | verdict |
|---|---|---|---|
| C-1 | README/CLAIMS/WALKTHROUGH stated the pre-E1 world | grep for `23 constructors`/`annotation-free`/`BareHead`-as-live/`hcl`/`M.currentLoc`; README:28–70 "Scope, exactly" read (binders, `PePure`, E2 currency, `case_eval` mirror-only), :129 (28/58/35/19/4), :176–191 (located Core, E1/E2, what keeps t1 out); CLAIMS:40 (C12) and :45 ("Not claimed" restated); WALKTHROUGH:40–50 (`MemTriple` re-quoted without `hcl`), :1470–1540, :1785–1830 | applied. ONE residue: WALKTHROUGH:433 "over `th₀`'s `errno` and `current_loc`" is FALSE at HEAD — `ctlThread` sets `current_loc := ctl.curLoc` (DriverCollapse.lean:2379–2385; its own docstring: "only `errno` is `th₀`'s") — D-2 |
| D-1 | ARCHITECTURE's 16 stale sentences | each of the E1 audit's §11 sentences re-read at HEAD | the 16 fixed (28 constructors; annotated/live location bullet; `Ctl` five fields; `MachineCtx` seven; `ctl.upd`; `⟨[], some p, ℓ, lc, sp⟩`; 508 pins; sub-trio list; `hcl` bullet gone; 28/58/…/20; consumer set 20; `BOUNDARY: 22`; four OUT-OF-SCOPE/nineteen NO-RULE; closure records; the tie glossary). REMAINING staleness (the disposition table's own flag, not in KOI): 92 of 140 `file:line` cites point at a wrong line (§10) — D-1 |
| D-3 | `Adequacy.lean:1272`, `:1447` docstrings | diff read | applied ("the location LIVE on the control, `ctl.curLoc`, since E1") |
| H-1 | 62 → 143 warnings | gate log: 60 unique `warning: CerberusHeapLang/*` lines; each line `git blame`d — commits `a030cc5 752eb18 639ee1b 61eaeea 29f475f b8df7b5 df1a24f e157941 02aa29c 0f1558a 2f15f98 4e86c08 c18d339`, EVERY one an ancestor of `3e75a1e` (`git merge-base --is-ancestor`) | applied; the range introduces ZERO remaining warnings; 60 = KOI C5 |
| H-2 | `wpt_driver_aux`'s unused `sp` | ProdLoop.lean diff: binder dropped, `ctl.sup` threaded | applied |
| R-1 | `EmittedAExhibit` "as the elaborator would" | module header + `progAE1` docstring rewritten (an E1 SYNTHETIC, the corpus's actual placements stated); E1 record §4 reworded | applied |
| R-2 | 395 split over-stated | E1 record: sentence in §7 item 7, ERRATUM section before the 395 list, frame-rule row added to §1; DECISIONS E1-audit entry carries the erratum; KOI §D lists it | applied |
| R-3 | `loc_update_*` mis-described | MirrorCoverage header rewritten (mirror-level vs engine-round witnesses); E1 record §5 reworded with the correction dated | applied |
| N-1 | `prodCtl.sup = default` placeholder | E1 record §2(B): "Design caution for E5 … PLACEHOLDER …" | applied |
| N-2 | corpus file without a row silently unchecked | `pendingCorpus` ledger (nine files, each with its owing slice) + `coverageSweep` + its own plant (t1's row dropped must fail); my plant: exit 1 | applied (fail-closed) — but SILENT on failure, H-1 above |
| N-3 | `loc_update_lib/_none` unpinned | Audit.lean diff; axioms measured trio | applied (426 → 428) |

## 10. Shop-window truth at HEAD (PASS on content; D- items)

- Counts: 28 constructors (`Frag` at HEAD has 28, §A.4), 58 rows / 35 / 0 /
  0 / 19 / 4 / 0 red / 20 consumers (manifest tail line verbatim), 508 pins
  (gate), 22 modules (gate) — README:129, ARCHITECTURE §5, CLAIMS, KOI §E all
  agree. The 19 NO-RULE rows in ARCHITECTURE §6's table sum to 19 (3+3+3+4+
  1+1+4). The consumer set "20 modules: the eighteen program exhibits …
  `Examples.CallSmoke`, `Examples.ReadinessSmoke`" — 18 positive-client
  modules in the TSV ✓.
- Synthetics: `EmittedAExhibit` header and docstring say "E1 SYNTHETIC … not
  the elaborator's own"; `EmittedBExhibit` header says "an E2 SYNTHETIC (the
  elaborator's own placements are t1Main's)"; the E2 record §4 says
  "SYNTHETIC"; ARCHITECTURE §5 lists both among the exhibits without the word
  but §1's second bullet sends the reader to `Examples/CorpusE0.lean` for the
  elaborator's Core. Adequate.
- Live-state fields: `Ctl := ⟨κ, proc, execLoc, curLoc, sup⟩`, `MachineCtx`
  seven fields, `RunSup` on `Ctl.sup` untouched by every E2 rule (every new
  `Step` constructor ends in `ctl.upd a`; `Step.ctl_cases` re-proved over the
  seven new arms, Step.lean:3090–3096) ✓.
- ARCHITECTURE at HEAD, remaining stale sentences (D-1): (i) glossary
  "*`Frag`* … (`Soundness.lean:4149`)" and "*the mirror* — `Step` …
  (`Step.lean:1456`)" are pre-E1 cites (actual 6339 / 2387); (ii) §1 "`Frag
  e` (`Soundness.lean:6317`) has 28 constructors (`:6318`–`:6339`)" — 6317 is
  inside the header comment, the inductive is at 6339; (iii) by script, 92 of
  140 `file:line` cites do not land on the named declaration (Wps/Wpt/Round/
  DriverCollapse/Adequacy/ProdLoop/ProdEntry/Rules/exhibit statements — the
  files grew in E1/E2; Heap/Potential/Layout/most exhibits' definitions still
  land); the D-1 disposition flagged this and deferred it to the t1-milestone
  review, but it is on no register; (iv) §2.2 "`eval_uncovered`: an operand
  containing a leaf the engine's evaluator ACCEPTS where the mirror evaluator
  does not (a `Proc`-named unbound symbol, a binop at two floats, `OpEq` at
  two ctypes)" — since E2 the face also holds shapes the engine does NOT
  accept (a `case` matching no pattern is the engine's PANIC; UB088 is an
  undef whose location the classifier cannot decide; a constructor dispatch
  failure is an engine KILL) — the sentence's characterisation is now
  incomplete; §6 lists only the depth-guard case. The same sentence recurs
  in README:666 and WALKTHROUGH's residual bullets (D-2). The EvalClass
  header itself is complete and correct.

## 11. Records (PASS; corrections listed)

FULL gate on the copy (`scripts/test_unit.sh`, capped, `CERB_MEM_MAX=40G`; a
cache REPLAY — 50 `Replayed` lines — so the 60 warnings are the tree's).
Verdict tail, UNMODIFIED lines matching
`^==|^ok:|^info: CerberusHeapLang|^ALL GATES|^GATE-EXIT|^Build completed|^BOUNDARY|^ALLOWLISTED|^FAIL`,
verbatim:
```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:684:0: CerberusHeapLang export pins: 508 trio-exact
info: CerberusHeapLang/Audit.lean:684:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (4305 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:684:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (6702 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (461 jobs).
ok: cerberus-heaplang build green
== speedbump: rule-use and classification manifest (regenerate; red on a red row or drift) ==
ok: capability manifest regenerated, no drift
== speedbump: corpus skeleton (hand-transcribed emitted Core vs docs/corpus-e0; scripts/corpus_skeleton.lean) ==
ok: corpus skeleton — every transcription matches its emitted text, every plant mismatches
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — 15 core modules, none imports an exhibit/example/production module
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
ok:   Examples.CallSmoke — 0 internals mentions
ok:   Examples.ReadinessSmoke — 0 internals mentions
ok:   Examples.Layout — 0 internals mentions
ok:   Examples.CorpusE0 — 0 internals mentions
BOUNDARY: 22 modules checked, 0 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
```
Exit status 0 (my wrapper's `exit=0` line). Line for line identical to the
DECISIONS E2 entry's quoted block except its final `GATE-EXIT=0`, the
orchestrator's wrapper line (not printed by the script; as in the E1 audit).
Also present in the gate log (the passing run): the corpus-skeleton table
line `| t1.annot.core | main | 118 | equal | mismatch (expected) | mismatch
(expected) | mismatch (expected) |` and `corpus-skeleton: ok — 1 row(s) equal,
every plant mismatches` — the record §6's verbatim output.

Counts/hashes vs the tree: manifest tail ✓; `CLAIMS: 12 claim rows, 104
declaration names checked` ✓; snapshots 3406/3853 ✓; pins 508 ✓; warnings 60
✓; t1 118 tokens ✓; progBE2 budget 30 ✓ (`progBE2_wpt`); "six commits on
3e75a1e" = the six listed ✓ (`b5ed995` is the entry). DECISIONS is
chronological (…2026-09-04 entries, then three 2026-09-05 entries in order).
KOI updated for E2 (state line, B7/B8 E-arc status, C5 60, §D erratum, §E
expected tail) ✓.

The two upstream notes: `…subst-esize.md` — accurate to the tree's situation
(`hbsz` carried, discharged by `rfl` per program; `esize (subst_sym_expr x v
e) = esize e` NOT proved in the tree — the note says "We will prove it in our
tree"); the note's `Core_aux.lean`'s `subst_sym_expr` reference ✓. BUT KOI B7's
E-arc sentence "the general size-preservation lemma is carried locally" reads
as if the lemma exists; nothing in `CerberusHeapLang/*.lean` states it (grep:
comment mentions only, Soundness.lean:6510, CaseExhibit.lean:29) — R-3.
`…conv-int-divergence.md` — accurate to `core_eval.lem:61–81` (`mk_conv_int`:
`_Bool ↦ 0/1`; in `[min, max] ↦ n`; else `mk_wrapI ity n_ival` with the TODO
comment) and to `gcc_4.9.0_x86_64-apple-darwin10.8.0.impl:18–20`
(`<Integer.conv_nonrepresentable_signed_integer>(ty, n) := wrapI(ty, n)`); the
`std.core:61–67` `conv_loaded_int` cite ✓.

Record corrections (R-1): `docs/2026-09-05_fragment-closure-e2-notes.md` — (a)
"`ShippedRefusal.panic` (`update_env_aux_tuple_mismatch`)" → the arm used is
`ShippedRefusal.panic_env` (the E2 record §1 and §7.5 say `ShippedRefusal.panic`
too); (b) "the E1 statement was at `peDepth pe ≤ fuel`, correct for E1's
grammar, too tight for `case`" → E1's `aux2_bridge`/`aux2_bridge_kill` had NO
round-fuel premise; E2 ADDED `peDepth pe ≤ fuel + 1`. The E2 record §7.2 states
the change correctly ("restated at the round budget"); only the closure note's
history is wrong. (c) The E2 record §2(D)/header claim about `unspec_storable`
— R-2.

Design-note premises vs delivery (not findings; for the record): §C.2 planned
pattern-GENERIC binders (`matchPattern` premise), `case_op` and `let_` in
`Frag`, `wps_case_eval`/`wps_let`, `OpOr/OpAnd`, a NEW `store_unspecified`
rule, and said "t5_ifelse.core and t6_switch.core are `Frag` after E2". E2
delivered flat tuple binders only (§7.6), `case_eval` mirror-only (§7.4), no
`Elet`/`And`/`Or` (fail-closed by grammar), no new store rule (measured
unnecessary — §3 here), and no t5/t6 claim (they need E3/E5, as the design
sentence itself concedes in its parenthesis). Deviations 1–12 are recorded in
§7; the t5/t6 acceptance sentence is not addressed anywhere — N-3.

## 12. Grumpy read of the new Lean

- `Step.lean` (E2): `stepPexprRaw`/`evalPexpr`/`peDepth` are small, arm-per-
  engine-arm, cited; the SUM-at-`case`/`if` depth measure is explained in
  place and is the right measure. Good.
- `EvalClass.lean`: the pass-structured classifier is the right shape and the
  header is the most accurate description of the residual on any surface.
  `stepFail` RE-WALKS the traversal `stepPexprRaw` already performs (a second
  copy of the evaluation order); the drift risk is bounded by
  `stepFail_bridge`, but one function returning `Except StepFail pexpr`
  would remove the duplication and the "arms the pass cannot reach are
  `.uncovered`" caveat. The `_kill` corollaries kept for E1 callers are fine.
- `Round.lean`: `complete_beta_tuple` and `complete_wbeta_tuple` are four
  15-line blocks differing only in the constructor name and the engine
  equation (`step_ctx_{s,w}seq_val_{pure,annot}`); a `by_cases`-generic
  helper over the binder kind would halve them. Not blocking.
- `EmittedBExhibit.lean`: a clean client (0 internals mentions); the wps/wpt
  proofs are the house near-duplicates; nine `fr*_lookup_*` lemmas are the
  usual environment boilerplate; `depLeB` duplicates `CorpusE0.depLe`
  verbatim (both `peDepth pe ≤ 9 → ≤ lemDefaultFuel`) — fold into one
  public lemma. `hnolabel` names `(procCtl mainSym).proc` while launching at
  `ctl := prodCtl` (the E1 audit's remark, still there).
- `Examples/CorpusE0.lean`: 862 lines, mostly `partial def` tokenizer —
  instrument code in the package, correctly `example-support`; the header is
  precise about its blind spots. `scripts/corpus_skeleton.lean`: clear,
  fail-closed on read/tokenize/skeleton errors — except that its own failure
  path is silent (H-1).
- No new linter warnings from the range (§9). No heartbeat/maxRecDepth option
  anywhere in the diff (grep).

## Findings, ranked

| # | Grade | Finding | Evidence | Fix required | Premise verified by measurement |
|---|---|---|---|---|---|
| H-1 | Instrument hygiene (fail-noisy defect) | The corpus-skeleton speedbump discards ALL its diagnostics on failure: `scripts/corpus_skeleton.lean:155` `IO.Process.exit 1` inside `#eval` kills the process before Lean emits the captured stdout/stderr; a failing run reaches the gate log as `FAIL (speedbump): corpus skeleton red (…)` with no row, no first-difference, no coverage-sweep line | §A.3: the N-2 plant → exit 1, stdout and stderr EMPTY (twice); the two-line `IO.Process.exit` control prints nothing; the `throw` control prints both lines and `error: corpus-skeleton: FAIL`, exit 1 | replace `IO.Process.exit 1` with `throw (IO.userError "corpus-skeleton: FAIL")` (one line; `capability_manifest.lean`/`parametric_inventory.lean` already use `throw`) | yes |
| D-1 | ARCHITECTURE staleness | (i) glossary cites `Soundness.lean:4149` (`Frag`), `Step.lean:1456` (`Step`) pre-E1; §1 `Frag` cite `:6317` (actual 6339); (ii) 92 of 140 `file:line` cites do not land on the named declaration (§10; Wps/Wpt/Round/DriverCollapse/Adequacy/ProdLoop/ProdEntry/Rules and the exhibit statements' lines); (iii) §2.2's `eval_uncovered` characterisation ("a leaf the engine's evaluator accepts where the mirror does not") omits E2's non-accepted members (no-match PANIC, UB088, constructor dispatch failure, undef-then-raise); §6 lists the depth guard only | the D-1 disposition flagged (ii) itself and deferred it to the t1-milestone review, but no register carries it; (iii) is a content sentence | (ii): a cite refresh pass or a register line (KOI) until the t1 review; (i)/(iii): three sentences | yes (script over 140 cites; §A.4 count) |
| D-2 | Shop-window residue | WALKTHROUGH:433 "`ctlThread` … over `th₀`'s `errno` and `current_loc`" is FALSE — `ctlThread` writes `current_loc := ctl.curLoc` (DriverCollapse.lean:2379–2385, whose docstring says "only `errno` is `th₀`'s"); README:666 and WALKTHROUGH's two residual bullets characterise `eval_uncovered` by the three E1 leaf shapes only (as D-1(iii)) | read against the definition | reword :433 ("over `th₀`'s `errno`"); add E2's members (or "among them") to the three residual sentences | yes |
| D-3 | In-code docstring | `ShippedRefusal.panic_env` (Round.lean:284–294) still describes only "a `Cspecified` binder meeting a non-`Specified` value"; since E2 it also classifies the tuple binder at a non-tuple head | read | one clause | yes |
| R-1 | Record inaccuracies | `docs/2026-09-05_fragment-closure-e2-notes.md` + E2 record §1/§7.5: the non-tuple head is classified `ShippedRefusal.panic` → actually `ShippedRefusal.panic_env` (`complete_beta_tuple`, Round.lean:2972/2987); closure note: "the E1 statement was at `peDepth pe ≤ fuel`" → E1's `aux2_bridge`/`_kill` had NO round-fuel premise (snapshot `2026-09-04_e1-signatures-post.txt`), E2 ADDED `peDepth pe ≤ fuel + 1` | pre/post statements §A.4 | two sentences | yes |
| R-2 | Misattributed measurement | `EmittedBExhibit.lean` header (and record §2(D)): "byte-for-byte the fresh cell's `undefByte`s; measured, not assumed: `unspec_storable`" — `StorableAt` (Heap.lean:212) has no byte-list field; nothing in the tree states `(memValueToBytes tds [] unspecMval).2 = intUndefBytes tds`. The FACT is true: both `example … := rfl` elaborate (§A.1) | my `rfl` probe | add the one-line theorem the header claims exists, or reword to "the rule's post-image is the engine's own `memValueToBytes`; the equality with `intUndefBytes` holds by `rfl` (unstated)" | yes |
| R-3 | Register wording | KOI B7 (E-arc status): "the general size-preservation lemma is carried locally" — no such lemma exists in `CerberusHeapLang/*.lean` (comment mentions only); `hbsz` is a carried PREMISE discharged per program by `rfl`; the upstream note says "we WILL prove it" | grep | "…is NOT proved; `hbsz` is discharged per program; the note promises the general lemma" | yes |
| N-1 | Mover, not a defect | A constructor dispatch failure the engine KILLS with a computable `Illformed_program "…<====>…"` (e.g. `Specified(Unspecified(int))`) is classified `.uncovered` (fail-closed) rather than `.kill` | `stepFailList [] = .uncovered` read; header lists it | optional `.kill` arm with the printed message, as `illtypedPEif` does | yes |
| N-2 | Duplication | `complete_beta_tuple`/`complete_wbeta_tuple`: four cloned blocks; `depLeB` = `CorpusE0.depLe`; `stepFail` re-walks `stepPexprRaw` | read | hygiene, optional | yes |
| N-3 | Record completeness | The design note §C.2's acceptance sentence ("t5_ifelse.core and t6_switch.core are `Frag` after E2") is neither met nor addressed in the record's deviation list (§7 covers the pattern-generic binder, `case_op`, `let_` implicitly) | read | one line in §7 | yes |
| N-4 | Wording | README:191/CLAIMS:45 "t1's `main` … decided by the kernel (`t1_convLoadedInt_uncovered`, `t1_case_uncovered`)": what is kernel-decided is two operands' non-membership in `PePure`; `¬ Frag t1Main` follows by the grammar but is not a stated theorem | read | "the operands … are kernel-decided outside `PePure`, so `main` is outside `Frag`" | yes |

No T- (trust) finding: no unsound or vacuous rule; no statement saying other
than the docs say (the docs' errors are stale cites, one false tie sentence
and under-descriptions of a fail-closed residual); no construct claimed
covered without a proved AND consumed rule (the six new rules are consumed
by `EmittedBExhibit`, manifest RULE rows); the `undef` KILL, the tuple
binders and the one-pass mirror are exact against the generated engine at
the pin, by kernel-checked equation and by executable run; 82/82 new pins
trio-exact; `pull_bridge` sub-trio as declared; the nine production
statements and the 22 headlines textually unchanged.

## A. Probe and plant logs (verbatim)

### A.1 `.audit-scratch/Probe.lean` §A–§C (`lake env lean`, capped; the `libleanshared.so` backtrace lines of the engine's compiled PANIC elided, marked)
```
## UB036 at a non-library undef loc: 1 execution(s)
   Killed Undef0 loc=exhibitB.c:3:10-20 ubs=[UB036_exceptional_condition]
## UB036 at a LIBRARY undef loc: 1 execution(s)
   Killed Undef0 loc=other_location(Driver.drive) ubs=[UB036_exceptional_condition]
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: PEcase, mismatched ==> [other_location(Driver.drive)](Specified(1), Unspecified('signed int'))
backtrace:
[… 96 libleanshared.so frames elided …]
## case matching NO pattern (engine panic): 1 execution(s)
   Active value=<non-int>
## exhibit B itself (control): 1 execution(s)
   Active value=Specified((some 4))
evalClass ubCase     : undef loc=exhibitB.c:3:10-20 ubs=[UB036_exceptional_condition]
evalClass ubCaseLib  : undef loc=other_location(Driver.drive) ubs=[UB036_exceptional_condition]
evalClass noMatchCase: uncovered
select_case no-match = none? true
stepPexprRaw noMatchCase = none? true
evalPexpr ubCase = none? true
unspec image length: 4
```
(Programs: `ubCase := PEcase (tuplePe (specIntPe 1) unspecIntPe) specSumPats`
under `Expr [Aloc (ebLoc 9 1 9 40), Astmt] (Epure ·)`, wrapped by `prodFile`;
`ubCaseLib` the same with the wildcard arm's `PEundef` at
`region ⟨"libcore/std.core",3,1⟩ …`; `noMatchCase` with the `Specified` row
only; the mirror at `loc := CerbLocation.other "Driver.drive"`, `ρ :=
[fmapEmpty]`. The three `example … := rfl` lines of §C — `(EvalFail.undef l
u).reason = Undef0 l u`, `(EvalFail.kill c).reason = Other (DErr_core_run c)`,
`(memValueToBytes tds [] unspecMval).2 = intUndefBytes tds`, `paddingByte =
undefByte` — elaborated without error.)

### A.2 Pin axiom sets (`Lean.collectAxioms`)
```
pins listed: 82
trio-exact: 82 / 82
  CerberusHeapLang.pull_bridge: #[Quot.sound, propext]
  CerberusHeapLang.frag_round_complete: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.engine_step_matchU: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.exhibitB_prod_e2: #[Classical.choice, Quot.sound, propext]
```
(The 82 = the 80 E2 names of the `Audit.lean` diff + `loc_update_lib`,
`loc_update_none`.)

### A.3 Corpus-skeleton plants by term surgery (`Probe.lean` §E, no tree edit) and the N-2 plant
```
text tokens: 118
baseline t1Main                          : PASSES (blind spot)
plant S1 Specified(3) -> Unspecified(int) : RED (mismatch; first diff at token 17: term `Unspecified` vs text `Specified`)
plant S2 constant 3 -> 4                  : PASSES (blind spot)
plant S3 case: undef arm dropped          : RED (mismatch; first diff at token 67: term `endcase` vs text `alt`)
plant S4 case: arms swapped               : RED (mismatch; first diff at token 53: term `leaf` vs text `tuple`)
plant S5 store conv_loaded_int(a) -> a    : RED (mismatch; first diff at token 22: term `leaf` vs text `conv_loaded_int`)
plant S6 Aloc inside a pure Specified     : ERROR (fail-closed): a pure expression node carries a printed annotation (Astd/Aloc) — the skeleton compares no location inside pure expressions (fail-closed)
script plant: bound dropped               : RED (mismatch; first diff at token 13: term `loc` vs text `std:§6.5#2`)
script plant: Astd stripped               : RED (mismatch; first diff at token 13: term `bound` vs text `std:§6.5#2`)
script plant: Specified unwrapped         : RED (mismatch; first diff at token 17: term `leaf` vs text `Specified`)
EmittedB progBE2 vs t1 text (control)     : RED (mismatch; first diff at token 2: term `loc` vs text `create`)
```
("PASSES" on the baseline is the expected green; "PASSES (blind spot)" on S2
is the documented `leaf` opacity of literals.)

The N-2 plant against the REAL script (`docs/corpus-e0/zz_plant.annot.core`
created, script run, file deleted; stdout and stderr captured separately):
```
exit=1
--- stdout
--- stderr
cerberus-lean-proj env: switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_opam, git redirects active
```
(`git status --short` after: only `.audit-scratch/` untracked.) The
`IO.Process.exit`-in-`#eval` control (`.audit-scratch/ExitTest.lean`:
`IO.println "STDOUT-BEFORE-EXIT"; IO.eprintln "STDERR-BEFORE-EXIT";
IO.Process.exit 1`) and the `throw` control:
```
--- exit variant
cerberus-lean-proj env: switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_opam, git redirects active
exit=1
--- throw variant
cerberus-lean-proj env: switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_opam, git redirects active
STDOUT-BEFORE-THROW
STDERR-BEFORE-THROW
../.audit-scratch/ThrowTest.lean:5:0: error: corpus-skeleton: FAIL
exit=1
```

### A.4 Census, snapshot, `Frag` diff, cite check
```
PRE 3406 POST 3853 ADDED 459 REMOVED 12 CHANGED 50
18 1 31 50 50
record minus mine: set()
mine minus record: set()
```
```
CMP-IDENTICAL
  37186 ../.audit-scratch/head-signatures.txt
  37186 docs/2026-09-05_e2-signatures-post.txt
```
`Frag` constructors, full text with comments stripped:
```
pre ctors 25 post ctors 28
REMOVED: pure_sym
ADDED: pure_op :: pure_op {an : List _root_.annot} {pe : generic_pexpr Unit sym} (hnv : valueFromPexpr pe = none) (hp : PePure pe) (hd : peDepth pe ≤ lemDefaultFuel) : Frag (pure
ADDED: sseq_tuple :: sseq_tuple {an pa : List _root_.annot} {ls : List TupleLeaf} {e1 e2 : CoreExpr} : Frag e1 → Frag e2 → Frag (Expr an (Esseq (tuplePat pa ls) e1 e2))
ADDED: wseq_tuple :: wseq_tuple {an pa : List _root_.annot} {ls : List TupleLeaf} {e1 e2 : CoreExpr} : Frag e1 → Frag e2 → Frag (Expr an (Ewseq (tuplePat pa ls) e1 e2))
ADDED: wseq_sym :: wseq_sym {an pa : List _root_.annot} {x : sym} {bty : core_base_type} {e1 e2 : CoreExpr} : Frag e1 → Frag e2 → Frag (Expr an (Ewseq (symPat pa x bty) e1 e2))
```
(no `CHANGED:` line — the other 24 constructors are identical.)
ARCHITECTURE cite check (declaration-line grep over 140 cites):
```
cites checked: 140; at the declaration line: 48; stale: 92
```
Six `EvalClass` statements, pre vs post source (`diff`): `evalClass_val_iff`
IDENTICAL; `evalClassList_vals_iff` binders moved to `variable` (type
identical in the snapshots); `full_eval_bridge_kill`/`eval1_bridge_kill`
statement identical, proof now a corollary; `mapM_eval1_kill`,
`mapM_save_kill` IDENTICAL.

Warnings by blame (60 unique sites → commit): `a030cc5` 10, `752eb18` 9,
`639ee1b` 4, `29f475f` 2, `61eaeea` 2, `b8df7b5` 2, `df1a24f` 2, `e157941` 2,
`02aa29c` 1, `0f1558a` 1, `2f15f98` 1, `4e86c08` 1, `c18d339` 1 — all
`pre-range` by `git merge-base --is-ancestor <c> 3e75a1e`.

## B. What I did NOT check

- The bodies of the pre-existing `Step` rules' engine equations and the
  30-arm inversions beyond their E2-new arms (I relied on
  `engine_step_matchU`'s kernel check, trio-exact, and on the pinned E2
  equations).
- The PCALL/RETURN rounds and the supplies at E2 (untouched by E2: every new
  `Step` constructor ends in `ctl.upd a`; `Step.ctl_cases` re-proved).
- `evalClassList`/`evalClassFold`'s Exception-first vs first-failure orders
  executably (read against `exception_undef_mapM`/`except_sequence` and the
  proofs `exception_undef_mapM_cons_*`; the lemmas are pinned).
- The E2 record's build-cost figures (§9) — not reproducible without a cold
  rebuild, which box etiquette discouraged with a concurrent E3 build.
- The 459 ADDED names individually (spot-read by namespace against the
  record's grouping).
- Whether every remaining ARCHITECTURE prose sentence outside §1–§3, §5–§6
  is true at HEAD (I read §1–§7 once and checked the cites by script).
- `deps/refinedc`, branch `refinedc/dev`, and the concurrent `dialect-e1`
  worktree (not touched, per the brief).
