# Response to the standards audit of the overnight stack (2026-09-03)

Worker record, branch `calls-c1`, worktree `worktrees/calls-c1`, base
`0b86bd2` (docs-only since the C2 head `8d28c21`, FULL gate green there
at 316 pins). The audit: `../../docs/2026-09-03_standards-audit-overnight-stack.md`
(findings M-1, M-2, M-4, N-2..N-7 closed here; M-3 and N-1 are the
orchestrator's, handled separately; the FULL-gate re-run for the
DECISIONS record is the orchestrator's — this record quotes the worker's
run). Provenance: every decision here is [AGENT] unless tagged; the
disposition of M-2 (unpin, not relabel) was directed in the dispatch
brief. NO statement or proof changed: the Lean edits are the
`trioExports` list (four names removed), comments in `Audit.lean` and
`Step.lean`, and the documentation table in `API.lean`. Quoted outputs
are verbatim; tallies I computed are labelled DERIVED with the method.

## Finding → fix → location

| Finding | Fix | Location |
|---|---|---|
| **M-1** — two shop-window surfaces asserted "THE ONE KNOWN ADMISSION … two `(sorry : String)` terms … `Cmm_op.lean`" | Both paragraphs replaced by the README's measured statement: none at pin `f95ef8d9c`; the former admission described as history closed by the fuel-arc head; the grep result below | `ARCHITECTURE.md` §6 ("ADMISSIONS IN THE PINNED SEMANTICS TREE: NONE"); `docs/WALKTHROUGH.md` §6; README "The trust story" bullet "Neither the semantics workspace …" still said "does contain one generated `sorry` (next bullet)" — fixed to "contains no admission at this pin" |
| **M-2** — "`dischargeStep`/`outcomesU` … appears in no export's statement" false at HEAD: four pinned lemmas mention the devices | Option (a): the four UNPINNED from `trioExports` (they are proof devices with a package-defined referent, bounded by the exhaustive sweep); the two sentences made exact ("no EXPORT's statement mentions it — the lemmas that do … are proof devices, unpinned and internal"); `Audit.lean` header records the unpin; `API.lean` gains a "Below the line" row naming the devices | `CerberusHeapLang/Audit.lean` (`trioExports`, header, two comments); `ARCHITECTURE.md` §2 and §4; `docs/WALKTHROUGH.md` §5; `CerberusHeapLang/API.lean` (row "The `driveU` lane's proof devices") |
| **M-4(a)** — README exhibits row stated `struct_create_store_adequacy` in the retired plan form `[⟨8, structTy⟩]` | Row now reads the pinned shape `MemTripleU_alloc spikeCtx spikeCtl spikeEnv prog ∅ (allocCost fmapEmpty structTy 8) ψ` (read off `docs/2026-09-03_c2-signatures-post.txt`, which also carries the C1 control argument `spikeCtl` the audit's proposed text omitted) | `README.md` exhibits table |
| **M-4(b)** — "165 trio-exact" / "165 export pins" | 312 (the count after the unpin), `Audit.lean` line as printed by the gate | `README.md` "How to build and verify" expected tail and "The trust diagram"; `docs/WALKTHROUGH.md` §6 |
| **M-4(c)** — Records listed K0–K4 only | K0–K5.1 with every slice note and range audit named; the re-pin, C1, C2 and their audits; the standards audit and this response | `README.md` "Records" |
| **M-4(d)** — snapshot pointers at `pr3-C` | `docs/2026-09-03_c2-signatures-post.txt`; the dedupe explained in one sentence (kept file per content, references redirected, identity re-verified by md5 in the standards audit) | `README.md` exhibits preamble and "Records"; `docs/WALKTHROUGH.md` header |
| **N-2** — engine quotes normalized without a marker | One erratum paragraph naming the three blocks and each elision (comments and binder types dropped in `call_proc` and the value arm; commas inserted in `loop_step_frag`); content preserved | `docs/2026-09-03_c2-notes.md` §1 |
| **N-3** — the dedupe rewrote quoted commands in place | The K5 audit's `cmp` line restored to the command as run, with the dedupe and the md5 re-verification outside the code span; the re-pin record's §6 sentence untangled the same way | `docs/2026-09-03_k5-audit.md` Q5; `docs/2026-09-03_repin-fuel-notes.md` §6. The other in-place rewrites (`X (byte-identical to the former Y, deduplicated …)`) read correctly and were left |
| **N-4** — "old plan forms derivable" is derivable up to `hsz` | Stated on both surfaces: derivable UNDER THE EXTRA PREMISE `hsz : 0 < sizeof ty`, which `PlanFits` implied (its `advanceCursor` guard); not literally derivable (`allocCap` is deleted) | `docs/2026-09-03_k2.5-notes.md` §4 (erratum); `docs/WALKTHROUGH.md` §4 |
| **N-5** — stale text | `Audit.lean` K4 comment: "not statable" → the K4 state, closed at K5, the list pinned below; `Step.lean` SCOPE: "admits the STATIC kill only until K3" → any `kill_kind` in both `Step` and `Frag`, K3 lifted the restriction (the `Frag.kill` constructor carries no kind premise — Soundness.lean, "any kind"); ARCHITECTURE §7 heading and the arc record's title "K0–K4" → "K0–K5.1" (the record's title carries a one-line retitling note); WALKTHROUGH §6 "165 theorems" → 312; WALKTHROUGH §7 "until the … request lands" → the request HAS landed at the pin, the fuel-lane restatement is the pending slice | `CerberusHeapLang/Audit.lean`; `CerberusHeapLang/Step.lean`; `ARCHITECTURE.md` §7; `docs/2026-09-03_kill-free-arc-record.md`; `docs/WALKTHROUGH.md` §6, §7 |
| **N-6** — audit item codes in the shop window | Every `M-n`/`N-n` outside the Records sections replaced by plain words ("a finding of the K4 range audit", "raised by the K2 range audit", "the K0 range audit's scenario", …); the two codes remaining in README are inside "Records", describing an audit record | `README.md` (7), `ARCHITECTURE.md` (6), `docs/WALKTHROUGH.md` (9) — DERIVED by `grep -nE '\b[MNL]-[0-9]+\b'` before/after |
| **N-7** — the "(1/3)" title; PROVISIONAL list completeness; `la_pos` | K2 record: one-line erratum (two commits, no 2/3 or 3/3; commit titles are immutable). ARCHITECTURE §6 PROVISIONAL list now names `SemTripleU_iff_Mem`, `MemTripleU_alloc_of_MemTripleU`, `*_semantic`, `list_reverse_demo`, `counter_loop_certified_irrelevant_binding` beside the classes already listed, and states the criterion ("every pinned export whose statement reaches `driveU` through a package definition, none other"); the two lemma names also added to the README/WALKTHROUGH/API.lean PROVISIONAL lists. `la_pos`: one clause in ARCHITECTURE §7 goal 3 and in the README's `MemWF` register row — a field added at K3 on orchestrator direction, recorded [AGENT] in DECISIONS, a stronger launch premise | `docs/2026-09-03_k2-notes.md`; `ARCHITECTURE.md` §6, §7; `README.md`; `docs/WALKTHROUGH.md` §1.3; `CerberusHeapLang/API.lean` header |

### The audit's API.lean premise, checked before the remedy

M-2 says `API.lean` "lists 'all of Soundness except `Frag` (`stepDischarge_*`,
`engine_step_matchU`, …)' under 'The surface (PUBLIC — import and use
freely)'". At HEAD that row is the third row of the SECOND table, "Below
the line (INTERNAL — visible, not part of the surface)" (three columns,
"Why internal" filled) — the names were already below the line. So the
"move" is a no-op; what was missing was any mention of the Adequacy-side
devices. Done instead: `stepDischarge_*` taken out of the certification
row and a dedicated internal row added for the lane's proof devices
(`dischargeStep`/`outcomesU`/`stepOutcomes`; `stepDischarge_*`,
`outcomesU_of_step`, `outcomesU_of_call`, `outcomesU_of_ret`,
`drive_classifyU`, `drive_classifyU_aux`), stating why they are not
exports and that they are unpinned.

## The four unpinned names

Removed from `trioExports` (`CerberusHeapLang/Audit.lean`), 316 → 312:

- `stepDischarge_run` (Soundness.lean) — statement mentions `dischargeStep`;
- `outcomesU_of_call` (Adequacy.lean) — statement mentions `outcomesU`;
- `outcomesU_of_ret` (Adequacy.lean) — statement mentions `outcomesU`;
- `drive_classifyU_aux` (Adequacy.lean) — statement mentions `driveU`
  (and carries `hPf : M.FragProcs`).

Why unpin rather than label: the pin list is "THE PUBLIC EXPORTS"; the
2026-09-02 trust rule says proof devices "live in proofs only". A lemma
whose statement's referent is a package-defined device is a device, not
an export, whatever its cone. They remain theorems of the package and
are bounded by the exhaustive sweep (Audit.lean check 2) — the trio
bound on them is unchanged, only the pin is gone. Nothing else in the
list moved; the sweep's verdicts are unchanged.

## M-1: the measurement (verbatim)

From `cerberus-heaplang/`, against the primed workspace at
`f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf` (`.cerberus-ws/.primed-from`,
verbatim: `f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf 2026-09-03T05:52:15Z`):

```
$ grep -rn '(sorry' ../.cerberus-ws/lean_frontend/generated/*.lean; echo "grep exit=$?"
grep exit=1
```

No hits. The broader `grep -rn 'sorry'` over the same files returns 19
lines, every one prose inside a comment (CerbCabsInstances.lean:5,
CerbFunMapInstances.lean:6/8/13/48/50, CerbStepInstances.lean:7/57/67/78/79/85,
CerbCall.lean:51, CerbCtypeInstances.lean:5, CerbConcurrency.lean:23/24,
CerberusFresh.lean:155, Core_reduction.lean:276 — the `sorry` at
CerbFunMapInstances.lean:8 is a backticked quotation of a retired
generated line inside a doc comment); `Cmm_op.lean` has no hit. This
agrees with the README's "none (measured 2026-09-03)" and with the
audit's own measurement.

## N-7: PROVISIONAL list completeness (DERIVED)

Method: a script over `docs/2026-09-03_c2-signatures-post.txt` (the
printed TYPE of every pinned name) and the package sources — the closure
of package definitions whose bodies mention `driveU` (`dischargeStep`,
`outcomesU`, `stepOutcomes`, `MemTripleU`, `MemTripleU_alloc`,
`SemTripleU`, `ProvenTripleU`, `DriveDoneAt`), then every pinned export
whose printed type mentions a member. A textual approximation of the
audit's `Expr.getUsedConstants` measurement, not a replacement for it.
Result, of the 316 pre-unpin pins: 44 reach `driveU` — the 13 adequacy
exports already listed, `SemTripleU_iff_Mem`,
`MemTripleU_alloc_of_MemTripleU`, `exhibit{A,B,C}_semantic`,
`list_reverse_demo`, `counter_loop_certified_irrelevant_binding`, every
`*_certified`/`*_total`/`*_engine`/`*_adequacy`/`*_launch_smoke`
exhibit, `counter_loop_certified_registration`, and the four devices
now unpinned. The nine `hPf : M.FragProcs` carriers among the pins
(snapshot grep, DERIVED): `engine_adequacyU`, `engine_adequacyU_alloc`,
`project_triple`, `project_triple_alloc`, `project_triple_pure`,
`project_triple_pure_alloc`, `semantic_frameU`, `semantic_triple_soundU`,
`drive_classifyU_aux` (the last now unpinned; `drive_classifyU` is not
pinned).

## The fast gate (after the unpin; verbatim tail)

`CERB_MEM_MAX=48G ./scripts/test_unit.sh --fast`, exit 0, log of 3411
lines; quoted: lines 1–3, 286–290, 3405–3411 (the omitted lines are the
two builds' job listings and linter warnings; the final `FAST-GATE-EXIT=0`
line is the invoking shell's echo of the script's exit status, appended
to the log):

```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 2: capped build, root package (elaborates its axiom audit) ==
info: RefinedCerberus/Audit.lean:75:0: RefinedCerberus axiom sweep: 2 theorems, all cones within the classical trio
info: RefinedCerberus/Audit.lean:75:0: RefinedCerberus banned-axiom sweep: 3 constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
Build completed successfully (371 jobs).
ok: root build green
== gate 3: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:469:0: CerberusHeapLang export pins: 312 trio-exact
info: CerberusHeapLang/Audit.lean:469:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (3208 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:469:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (4938 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (454 jobs).
ok: cerberus-heaplang build green
FAST-GATE GREEN (gates 1-3 only — not a claim-point result; say fast-gate in the commit)
FAST-GATE-EXIT=0
```

The pin count moved 316 → 312 (the four devices) and nothing else in the
audit's output changed against the C2 record's tail (3208 theorems swept,
4938 constants swept — the same environment).

## The FULL gate (verbatim tail)

`CERB_MEM_MAX=48G ./scripts/test_unit.sh` at the final tree, exit 0, log
of 3416 lines; quoted: lines 1–3, 286–290 and 3405–3416 (the omitted
lines are the two builds' job listings and linter warnings; line 3411 is
the container env banner printed by `scripts/ce`; the final `GATE-EXIT=0`
line is the invoking shell's echo of the script's exit status, appended
to the log). The orchestrator re-runs this gate independently for the
DECISIONS record; this is the worker's run.

```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 2: capped build, root package (elaborates its axiom audit) ==
info: RefinedCerberus/Audit.lean:75:0: RefinedCerberus axiom sweep: 2 theorems, all cones within the classical trio
info: RefinedCerberus/Audit.lean:75:0: RefinedCerberus banned-axiom sweep: 3 constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
Build completed successfully (371 jobs).
ok: root build green
== gate 3: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:469:0: CerberusHeapLang export pins: 312 trio-exact
info: CerberusHeapLang/Audit.lean:469:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (3208 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:469:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (4938 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (454 jobs).
ok: cerberus-heaplang build green
== speedbump: capability manifest (regenerate; red on a red row or drift) ==
cerberus-lean-proj env: switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_opam, git redirects active
ok: capability manifest regenerated, no drift
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — no core module imports an exhibit/example/production module
ALL GATES GREEN
GATE-EXIT=0
```

## Borderline items, for the orchestrator

- The first fast-gate run was logged to `/tmp/` — outside the worktree
  and unreadable from this sandbox afterwards; the log was deleted and
  the gate re-run with its log inside the worktree's gitignored
  `.lake/audit-scratch/` (removed at the end). No other write left the
  worktree.
- `API.lean` header prose (not a table row) gained the two lemma names
  in its PROVISIONAL list, for consistency with README/ARCHITECTURE/
  WALKTHROUGH; the dispatch scoped `API.lean` edits to table rows.
- The arc record `docs/2026-09-03_kill-free-arc-record.md` was retitled
  K0–K5.1 with a note; its body still records K5/K5.1 under "What
  remains" rather than in "The slices" — left as written (a record).
- The dedupe's other in-place rewrites (`X (byte-identical to the
  former Y, deduplicated …)` inside code spans, ~30 lines across the
  records) were left: they read as intended and the audit verified the
  identities. Only the two lines that had become nonsense
  (self-comparison, "is a copy of itself") were restored.
