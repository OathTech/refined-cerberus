# Response to the independent audit of b34998d..c2c4e4d (2026-09-03)

Audit: `docs/2026-09-03_audit-since-b34998d.md` (fourth auditor,
dependency-tracing, read-only; brief `../../docs/AUDIT-BRIEF.md`).
Verdict there: sound at the theorem level; M-1 (Medium) the residual
`OpenRound.eval_uncovered` is documented as engine-accepted operands and
"every rejected operand is a proved engine KILL" overstates (engine
counterexample by execution); N-1..N-6 notes; "merge after the M-1
wording fix". Branch `fragment-closure`, from `7abc0e1` (the audit
commit). Remit: DOCS + COMMENTS + ONE SCRIPT CHANGE — no Lean statement,
proof or import edit. Verified mechanically: for every touched `.lean`
file, the comment-stripped source (all `/- … -/` blocks and `--` lines
removed, whitespace normalized) is byte-identical to `HEAD`'s.

Every decision below is [AGENT] unless tagged. Quoted outputs are
verbatim; derived tallies are labelled.

## 1. Finding → fix → location

| Finding | Fix | Location |
|---|---|---|
| M-1 (the residual described as engine successes; the KILL-coverage sentence overstates) | Every "an operand the engine ACCEPTS / does NOT reject where the mirror does not evaluate" replaced by the tree's truth (§2): the classifier answers `.uncovered` at the FIRST uncovered LEAF and carries no engine claim; the arm's whole-operand outcome is NOT characterized and includes engine KILLs (the auditor's `f + 1` counterexample, quoted with its engine output) and panics (a float guard under `Eif`); "every rejected operand is a proved engine KILL" replaced by "every operand the classifier REJECTS is a proved engine KILL; operands the classifier leaves UNCOVERED are not characterized (the residual is a superset of the engine-accepted shapes)"; the mover named: `evalClass` computing the engine's value at the three leaf shapes. The `complete_*` docstrings that said "an operand outside the mirror evaluator that the engine accepts is the residual" now say "the classifier leaves uncovered (an accepted-but-unmirrored leaf; the whole operand's outcome not characterized)". `complete_pure_sym`'s docstring is untouched: at a bare symbol redex the operand IS the leaf, and the engine does evaluate it to the null function pointer. | `Round.lean`: module header (gap (c) paragraph), `OpenRound` docstring, `OpenRound.eval_uncovered` docstring, `complete_if`/`_run`/`_save`/`_load_op`/`_memop_op`/`_store_op` docstrings; `EvalClass.lean` header (`EvalOut.uncovered` bullet: first-leaf behaviour + the counterexample); `Soundness.lean` header ("THE SECOND FUEL BOUND, AND THE OPERAND GRAMMAR"); `README.md` "Where the headline claim rests" para 3 and the "Registered divergences" row (+ its mover column); `ARCHITECTURE.md` §2 (completeness paragraph) and §7 (residual bullet); `docs/WALKTHROUGH.md` §5 (the `OpenRound` sentence) and §7 (the residual bullet); `../docs/DECISIONS.md` — a new ERRATUM entry appended (the closure entry itself untouched, register is append-only) |
| N-1 (the round is beside the adequacy chain; headers say `engine_step_matchU` discharges each drive step) | The nine header/docstring sentences trued (§3): the `driveU` lanes consume the device lemma `outcomesU_of_step` (Soundness.lean, over `dischargeStep`); the production collapse `prod_run_eqJ` consumes `loop_step_frag`; `CerberusRound` and its certification/completeness are the reference relation, consumed by no adequacy export. A "WHAT CONSUMES WHAT" paragraph added to Round.lean's header; `engine_step_matchU`'s docstring and Round.lean's line 20 no longer say `loop_step_frag` "is this theorem's instance" — it has the same shape, proved independently. One sentence added to ARCHITECTURE §2 saying exactly this; §4's "engine_step_matchU makes it the engine's round" and §6's "which is what the total lane consumes" corrected. README: the trust diagram's total-lane box, the `Round.lean` module-table row. WALKTHROUGH §5 (two sentences in "Adequacy"). | `Adequacy.lean`:92-97 and `drive_classifyU` docstring; `TotalAdequacy.lean`:14-17, :19, `wpt_drive_aux` docstring; `Wpt.lean`:31-33, :2196; `Potential.lean`:7-10; `DivergeExhibit.lean`:14-15, :47-48, `dg_driveU_more` docstring; `Round.lean` header + `engine_step_matchU` docstring; `ARCHITECTURE.md` §2, §4, §6; `README.md` diagram + module table; `docs/WALKTHROUGH.md` §5 |
| N-2 (stale counts/locations) | 139 → 159, `Audit.lean:216` → `Audit.lean:253` (the `#eval` line that emits the sweep), each labelled "at the time of writing" | `README.md` trust-diagram preamble and the expected tail (+ a note under it); `docs/WALKTHROUGH.md` §6 |
| N-3 (`SeqWF` attributed to `engine_step_matchU`) | The premise removed; the theorem's actual statement quoted; `SeqWF` located where it is (`cerberusRound_classify`, for `value_done`) | `ARCHITECTURE.md` §2 first paragraph |
| N-4 (the iff slogan's two exceptions) | Wherever "mirror steps iff the engine has a successful deterministic round" appears, the same or the next sentence names the REMOVE-ANNOT value round (`value_annot`) and `error_next` (an engine SUCCESS round into an ILLTYPED-next configuration, filed under refusals). The naming question (does an engine-success round belong under `ShippedRefusal`) is left to the operator, noted in the DECISIONS erratum. | `README.md` "Where the headline claim rests"; `ARCHITECTURE.md` §2; `docs/WALKTHROUGH.md` §5; the DECISIONS erratum |
| N-5 (`--check` never re-verifies the lem-generated content; the `lean_frontend/generated` guard leg is vacuous for git-diff) | Section B's already-primed branch (which is what `--check` reaches) now runs `tools/check_lem_sync.sh --check-lean` in `$WS`, fail-closed; the CONTENT_PATHS guard comment states that the `lean_frontend/generated` leg is vacuous (gitignored upstream) and that the stamp is the real check. Transcript §4. The lem tool's commit is NOT recorded in `.primed-from` (the auditor's optional second suggestion) — out of the one-line remit. | `scripts/setup-cerberus-dep.sh` |
| N-6 (`complete_beta_sym` narrowed, recorded) | No change: the auditor's record is the record; the closure notes already disclose it under "Public statements changed". | — |

Also: the README "Records" list gains the audit and this response
(newest first).

## 2. M-1 — the replacement, and why this wording

The auditor's fact, re-read in the tree: `evalClass` (EvalClass.lean,
the `PEop`/`PEarray_shift` arms) propagates a child's `.uncovered`
without evaluating the rest, and the `EvalClass` header already said
"`EvalOut.uncovered` — the engine SUCCEEDS with a value the mirror does
not compute, OR THE OUTCOME IS NOT CHARACTERIZED HERE". Every other
surface dropped the second clause. The auditor's probe (audit §Method,
verbatim outputs): `isPePure pe0 = true`, `"classifier: uncovered"`,
`"engine: Exception (Illformed_program [unknown location] ill-typed
PEop ==> <core_pexpr>)"`, `"engine on leaf: Result"` — the leaf is
accepted, the whole operand is killed. Not re-run here (the remit is
docs; the auditor's transcript is quoted, not re-derived).

The canonical replacement, as placed in `OpenRound.eval_uncovered`'s
docstring (Round.lean), verbatim:

> An operand of the configuration's redex, in the covered grammar, that
> the mirror evaluator does not evaluate and that the CLASSIFIER leaves
> uncovered: `evalClass … = .uncovered` (EvalClass.lean). The classifier
> answers `.uncovered` at the FIRST uncovered LEAF — a symbol unbound in
> the environment but naming a `Proc` of the file (the engine evaluates
> that leaf to the null function pointer), one of the eight mirrored
> binops at two floating-point operands, or `OpEq` at two ctypes — and
> carries NO engine claim about the whole operand. So this arm contains
> operands whose whole-operand outcome is NOT characterized, INCLUDING
> ones the engine KILLS (`f + 1` with `f` a `Proc`-named unbound symbol
> is `PePure`, classified `.uncovered`, and the engine kills it as
> `Illformed_program … ill-typed PEop` — 2026-09-03 audit, by execution)
> or PANICS (a float guard under `Eif`). The engine's round is the
> operand-evaluation with-runstate step; its successor is not
> characterized here. Every operand the classifier REJECTS (`evalClass …
> = .kill err`) is a proved engine KILL (`ShippedRefusal.killed (Other
> (DErr_core_run err))`, the `complete_*` lemmas); operands the
> classifier leaves UNCOVERED are not characterized — the residual is a
> SUPERSET of the engine-accepted shapes. The mover: `evalClass`
> computing the engine's value at the three leaf shapes.

The one-line form used on the shop-window surfaces: "every operand the
classifier REJECTS is a proved engine KILL; operands the classifier
leaves UNCOVERED are not characterized (the residual is a superset of
the engine-accepted shapes)".

What was NOT changed: the Lean statements. `OpenRound.eval_uncovered`
claims only `evalClass … = .uncovered` and the step's shape
(`[Step_with_runstate2 rsk m]`), so `frag_round_complete` was and is
true as stated; the overclaim was prose only (the auditor's grading).
The `EvalClass.lean` header's "This is the RESIDUAL … every occurrence
is environment- or file-dependent" is kept and made exact ("a SUPERSET
of the engine-accepted shapes").

## 3. N-1 — the consumers, as the tree has them

Checked before wording (derived by grep, this tree):
`CerberusRound|frag_round_complete|cerberusRound_classify` outside
Round.lean occur only in `Audit.lean` (pins) and `API.lean` (the table);
`outcomesU_of_step` is used at `Adequacy.lean:881` (`drive_classifyU`),
`TotalAdequacy.lean:430/478` (`wpt_drive_aux`), `DivergeExhibit.lean:128`
(`dg_driveU_more`); `loop_step_frag` is used at `ProdLoop.lean:139`
(`wpt_driver_done`, feeding `prod_run_eqJ`). One precision relative to
the audit's summary sentence ("the partial lane consumes
`outcomesU_of_step` … the total lane `loop_step_frag`"): BOTH `driveU`
lanes — partial `drive_classifyU` and total `wpt_drive_aux` — consume
`outcomesU_of_step`; it is the PRODUCTION collapse (`prod_run_eqJ` via
`wpt_driver_done`) that consumes `loop_step_frag`. The wording placed
says exactly that.

The sentences changed (file:line at `HEAD`, before → after, abbreviated):

1. `Adequacy.lean:92` "Each drive step is `engine_step_matchU`'s unique engine behaviour (`drive_classifyU`)" → "discharged by the device lemma `outcomesU_of_step` (Soundness.lean): the mirror step's unique `outcomesU` outcome over `dischargeStep` (`drive_classifyU`) — NOT by the shipped-round certification `engine_step_matchU` (Round.lean), which this lane does not consume".
2. `Adequacy.lean:828` (`drive_classifyU` docstring) "via `engine_step_matchU`, one certification case per step" → "via the device lemma `outcomesU_of_step` (Soundness.lean), one case per step"; `:833` "`engine_step_matchU`'s `esize` obligation" → "`outcomesU_of_step`'s `esize` obligation".
3. `TotalAdequacy.lean:14` "`engine_step_matchU` discharging one engine step per budget unit" → "the device lemma `outcomesU_of_step` (Soundness.lean, over `dischargeStep`) discharging one `driveU` step per budget unit — the shipped-round certification `engine_step_matchU` (Round.lean) is not consumed here".
4. `TotalAdequacy.lean:18` "the per-step `engine_step_matchU` obligation" → "the per-step `outcomesU_of_step` obligation".
5. `TotalAdequacy.lean:355` (`wpt_drive_aux` docstring) "one engine step (`engine_step_matchU`) per budget unit" → "one `driveU` step (`outcomesU_of_step`, the device lemma) per budget unit".
6. `Wpt.lean:31` "`engine_step_matchU` discharging one engine step per budget unit" → "the device lemma `outcomesU_of_step` (Soundness.lean) discharging one `driveU` step per budget unit"; `:2196` "one engine round (`engine_step_matchU` at the create redex)" → "one `driveU` round (`outcomesU_of_step` at the create redex)".
7. `Potential.lean:7` "every engine-step certification (`engine_step_matchU`) carries `esize e ≤ lemDefaultFuel`" → "every per-step engine equation — the device lemma `outcomesU_of_step` the `driveU` lanes consume, `loop_step_frag` the production collapse consumes, the certification `engine_step_matchU` — carries …".
8. `DivergeExhibit.lean:15` "each round is the certified self-step, `engine_step_matchU`" → "each round is the self-step, discharged by the device lemma `outcomesU_of_step`"; `:47` "reached through the certified mirror step (`engine_step_matchU` on `dg_self_step` …)" → "reached through the mirror step (`outcomesU_of_step` on `dg_self_step` …)"; `:118` (`dg_driveU_more` docstring) likewise.
9. `Round.lean:20` and the `engine_step_matchU` docstring (`:785`) "`loop_step_frag` … is this theorem's instance at the production profile" → "has this theorem's shape at the production profile — proved there independently, not derived from this theorem"; new header paragraph "WHAT CONSUMES WHAT".

ARCHITECTURE §2, the sentence a reader needs (verbatim): "The round is
the REFERENCE RELATION the certification and the completeness below are
stated over; it is consumed by NO adequacy export — the adequacy chain
does not go through it: the `driveU` lanes (partial `drive_classifyU`,
total `wpt_drive_aux`) discharge each drive step with the device lemma
`outcomesU_of_step` (Soundness.lean, over `dischargeStep`), and the
production collapse (`prod_run_eqJ`) consumes `loop_step_frag`
(DriverCollapse.lean), which is proved independently of `CerberusRound`
by its own per-redex case analysis (Round.lean header, "WHAT CONSUMES
WHAT")."

## 4. N-5 — `scripts/setup-cerberus-dep.sh --check`, this worktree

Before the change (verbatim; exit 0):

```
== setup-cerberus-dep: A ok: workspace at pinned commit
== setup-cerberus-dep: B ok: primed (ddcfc919972a31bc43a0454e6b2e76a19e6c4594 2026-09-02T01:54:34Z)
== setup-cerberus-dep: C ok: 21 hand-written seams byte-identical to the pin
== setup-cerberus-dep: DONE. Lake consumes /home/dev/projects/cerberus-lean-proj/refined-cerberus/worktrees/fragment-closure/.cerberus-ws/lean_frontend as a path dependency.
```

After the change (verbatim; exit 0):

```
== setup-cerberus-dep: A ok: workspace at pinned commit
== setup-cerberus-dep: B ok: primed (ddcfc919972a31bc43a0454e6b2e76a19e6c4594 2026-09-02T01:54:34Z)
check_lem_sync: lean OK (src f4c0096697fb68c508acbe35423ed0fce77c6988ceafcaffe772924358e8a624, gen 6c2ae2041cceb0aed61cae04917144131fe96940e2aec6213d43b13b9d8fd5e7)
== setup-cerberus-dep: B ok: Lean lem-sync stamp verified in the workspace
== setup-cerberus-dep: C ok: 21 hand-written seams byte-identical to the pin
== setup-cerberus-dep: DONE. Lake consumes /home/dev/projects/cerberus-lean-proj/refined-cerberus/worktrees/fragment-closure/.cerberus-ws/lean_frontend as a path dependency.
```

The stamp leg runs in the already-primed branch of section B, so it
runs on every invocation over a primed workspace (setup re-runs
included), fail-closed with a re-prime instruction. The auditor's
residual path — a source whose committed `.lem` equals the pin's but
whose `generated/` is stale, primed green, stamp `--record-lean`'d
against the stale tree — is NOT closed by this (the stamp catches
later drift only; the auditor said so); closing it needs the primary
checkout to carry its own Lean stamp (`make lean-prelude-src` writes
it), which is cerberus-lean's side. Recorded, not fixed.

## 5. The gate

FULL gate (`scripts/test_unit.sh`, everything through `scripts/capped`;
`pgrep -af 'lake build'` empty before the run; started after every
Lean/ARCHITECTURE/WALKTHROUGH/DECISIONS/script edit above — the README
"Records" list entry and this record file were written while it ran and
are not build inputs), tail verbatim:

```
ℹ [445/447] Built CerberusHeapLang.Audit (1.4s)
info: CerberusHeapLang/Audit.lean:253:0: CerberusHeapLang export pins: 159 trio-exact
info: CerberusHeapLang/Audit.lean:253:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (2581 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:253:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (4065 constants of every kind swept, internal details included — count informational, environment-dependent)
✔ [446/447] Built CerberusHeapLang (823ms)
Build completed successfully (447 jobs).
ok: cerberus-heaplang build green
== speedbump: capability manifest (regenerate; red on a red row or drift) ==
cerberus-lean-proj env: switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_opam, git redirects active
ok: capability manifest regenerated, no drift
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — no core module imports an exhibit/example/production module
ALL GATES GREEN
GATE-EXIT=0
```

## 6. Borderline / for the orchestrator

- The audit's summary sentence for N-1 attributes `loop_step_frag` to
  "the total lane"; the tree has the total `driveU` lane
  (`wpt_drive_aux`) on `outcomesU_of_step` and the production collapse
  on `loop_step_frag`. The wording placed follows the tree (§3).
- `complete_pure_sym`'s docstring ("the engine evaluates it to the null
  function pointer") is left as is: at a bare symbol redex the operand
  is the leaf and the engine claim is correct at the leaf. Every other
  `complete_*` docstring that said "the engine accepts" now says "the
  classifier leaves uncovered".
- WALKTHROUGH §5's sentence "`cerberusRound_classify` … sorts every
  `Frag` configuration into `value_done` … or `refused`" (before the
  `frag_round_complete` block) omits `open_`; the five-arm list appears
  correctly a paragraph later. Not in the audit; left untouched (a
  reader-level nit, one word).
- N-4's naming question (an engine-success round under
  `ShippedRefusal`) is the operator's; the erratum records it as open.
