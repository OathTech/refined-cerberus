# Audit-response-3 notes — the response to the 2026-09-02 detailed audit

Audit: `../../docs/2026-09-02_cerberus-heaplang-detailed-audit.md` (third
independent auditor, at `d50e776`). Charter: the two last entries of
`../../docs/DECISIONS.md` — the [USER 2026-09-02] genuine-driver /
request-upstream ruling and the [AGENT 2026-09-02] detailed-audit
disposition; the upstream request
`../../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md`.
Remit: docs + small code, one change at a time, statements FROZEN
(snapshot pre/post identical except for moved declarations and the
audit-script change). Branch `audit-response-3` from `08af594`. Three
commits:

| Commit | Content | Gate |
|---|---|---|
| A `8e5ca7b` | docs + headers only (no statement/proof/import edits): PROVISIONAL labels, root-of-trust lane, H-1 wording, M-1, M-2, ARCHITECTURE.md; the RelSem names removed per the coordinator's amendment | fast-gate green, 4:17 wall |
| B `2e15b5c` | L-1 (the audit script) + L-2 (the moves); README/WALKTHROUGH build-section counts | fast-gate green, 3:48 wall |
| C (this) | this record; README records list | FULL gate green (§8, run at B's tree; C is docs-only) |

Every decision below is [AGENT] unless tagged. Quoted text is verbatim;
derived tallies are labelled. Mid-slice amendment from the coordinator
([USER 2026-09-02]: the RelSem work is being removed from cerberus-lean's
main): do NOT keep the RelSem disclaimer; replace every mention of
`RelSem.Machine.Step`/`runND_sound`/`HarnessAdequate`/`relsemcore` with
the plain statement that the engine round `CerberusRound` is the
mirror's only reference. Executed in commit A (§2).

## 1. Finding → fix → location

| Finding | Fix | Location |
|---|---|---|
| [USER] ruling: exports over `driveU` are not the root-of-trust statement | Label PROVISIONAL, in the ruling's exact sense, on every describing surface of every `driveU` export; name the total-lane production statements as THE root-of-trust exports and rest the README's headline claim on them; delete nothing, add no driver code | §2 lists the surfaces |
| H-1 (no unqualified two-sidedness) | The auditor's qualified sentence adopted verbatim; the certification stated as one-directional; `step_iff_cerberusRound` two-sided only given a mirror step; `cerberusRound_classify`'s `refused` arm proves no engine fact; sound, not proved complete; mirror completeness the registered open item. The RelSem disclaimer REMOVED (amendment) | README "The trust story" claim 1, the register row, the trust diagram, "One reference relation"; WALKTHROUGH §5 ("What the certification is, precisely"), §7; Round.lean header + `step_iff_cerberusRound`/`cerberusRound_classify` docstrings; ARCHITECTURE.md §2 |
| M-1 (freshness footprint-relative) | Documented exactly: `LaunchCoh` constrains tracked cells only (`id_lt`, `addr_lo`); a `create` is fresh from the logical footprint, not from untracked allocations in an arbitrary concrete state; the production cold start is globally well formed (`prodMem₀_launchCoh`); a global memory well-formedness invariant registered for the malloc/free arc | Adequacy.lean `LaunchCoh` section header; Heap.lean header (STATE INTERPRETATION paragraph); WALKTHROUGH §4 ("Freshness is footprint-relative"); README register row; ARCHITECTURE.md §7 |
| M-2 (API table inconsistent) | `allocCap_intro` → the launcher/internal row; `CellCoh`, `Coh`=`Sat` → PUBLIC as "the pure memory view (the boring post's vocabulary)"; `CohG`/`metaInterp`/`byteInterp` in premises stated as THE ONE DOCUMENTED EXCEPTION with the rule "a client discharges these only through the public `*_consequence` lemmas" | API.lean header (new paragraph + table rows); README "The public API" paragraph and trust claim 2. ReadinessSmoke's header does not cite the table — unchanged |
| L-1 (sweeps skip internal details while saying "every") | Both skips removed; sentences state the scope; one-time plant | Audit.lean; §4 |
| L-2 (Step-proved witnesses in a positive exhibit) | `store_sym_lit_step`/`store_lit_sym_step` moved verbatim to `Examples/MirrorCoverage.lean` (NOT a client); ProdExhibit header corrected; DivergeExhibit header states the negative-test exception | §5 |
| L-3 (no short normative architecture statement) | `ARCHITECTURE.md` | §6 |

## 2. PROVISIONAL — the surfaces touched

The label's sense, placed verbatim on each surface: "a sound fact about
`driveU`, this package's loop around the engine's `step_ctx`; not yet the
root-of-trust statement, which is over the shipped driver and awaits the
cerberus-lean fuel-exhaustion outcome
(docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md);
restated with no other change when it lands."

The exports labelled: `MemTripleU`, `MemTripleU_alloc`, `SemTripleU`,
`project_triple`, `project_triple_pure`, `project_triple_alloc`,
`project_triple_pure_alloc`, `semantic_triple_soundU`, `semantic_frameU`,
`engine_adequacyU`, `engine_adequacyU_alloc`, `wpt_engine_boundU`,
`wpt_engine_boundU_alloc` (all over `driveU` — checked against the
snapshot), and every exhibit whose execution function is `driveU` (the
README table's 13 `driveU` rows, `*_certified`/`*_total`/`*_engine`/
`*_adequacy`/`alloc_create_launch_smoke`/
`counter_loop_certified_registration`). The root-of-trust exports:
`exhibitA_prod`, `fib_certified_production`,
`counter_loop_certified_production`, `list_reverse_certified_production`
(over the shipped `runND ∘ drive ∘ initial_driver_state`), and
`prod_run_eqJ`.

Surfaces:

- README: the first paragraph; "The claim" (two new paragraphs — "Where
  the headline claim rests" and "PROVISIONAL" — and the shipped-pipeline
  paragraph retitled "the root-of-trust lane"); "The exhibits" intro and
  the Execution column (13 rows "— PROVISIONAL", 2 rows "— ROOT OF
  TRUST"); "The trust story" claim 1 (rewritten around the two lanes) and
  the fuel register row; the trust diagram ("drive statements —
  PROVISIONAL, over driveU"; "whole-program production statements — THE
  ROOT-OF-TRUST EXPORTS"); "The public API" paragraph.
- WALKTHROUGH: the intro; §1.1 (a PROVISIONAL paragraph after
  `MemTripleU`; the headline sentence); §1.2 (the production statement
  marked root-of-trust; `list_reverse_certified` marked PROVISIONAL); §1.3
  ("The two lanes, labelled"); §2 (the `driveU` parenthesis); §5 (the
  adequacy faces and the production entry); §7 (two new bullets).
- Adequacy.lean: header item 1 (`driveU` renamed "THIS PACKAGE'S LOOP")
  and a PROVISIONAL paragraph; docstrings of `driveU`, `MemTripleU`,
  `MemTripleU_alloc`, `SemTripleU`, `project_triple`,
  `project_triple_pure`, `project_triple_alloc`,
  `project_triple_pure_alloc`, `engine_adequacyU`,
  `engine_adequacyU_alloc`, `semantic_triple_soundU`, `semantic_frameU`.
- TotalAdequacy.lean: header PROVISIONAL paragraph; docstrings of
  `wpt_engine_boundU`, `wpt_engine_boundU_alloc`.
- API.lean: header PROVISIONAL paragraph; the two Adequacy rows' family
  names.
- ARCHITECTURE.md §6 (the two lanes).
- ProdExhibit.lean header: `exhibitA_prod` named a root-of-trust export.

Not touched (outside the enumerated surfaces): the individual exhibit
modules' theorem docstrings (`fib_certified` etc.); the README table and
WALKTHROUGH carry their label. A follow-up may add a one-line label per
exhibit docstring; no statement would change.

## 3. H-1 — the sentences placed

Verbatim, on each surface: "a sound Iris program logic for the package's
restricted relational mirror, with a verified forward connection to
successful Cerberus engine rounds on proved-safe executions". Placed in
README "The trust story" claim 1, WALKTHROUGH §5, Round.lean header,
ARCHITECTURE.md §2. Each placement states the two facts:
`engine_step_matchU` is one-directional (mirror step ⇒ engine round);
where the mirror is stuck no engine fact is proved
(`cerberusRound_classify`'s `refused` arm: `toVal c.1 = none` and
`∀ c', ¬ Step M c c'`, nothing about `outcomesU`), except at the four
redexes `cerberusRound_refused_store`/`_load`/`_create`/`_case` — so the
logic is SOUND but not proved COMPLETE for the fragment; mirror
completeness on the fragment is the registered open architecture item.
Sentences a reader could take as two-sided without the qualification,
removed or qualified: README register row "classified two-sidedly
wherever the mirror steps" → the one-directional statement; the trust
diagram's "two-sided where the mirror steps" → "two-sided only GIVEN a
mirror step"; Round.lean's `step` arm gloss "(the two-sided arm: …)" →
"(two-sided GIVEN the mirror step: …)"; `step_iff_cerberusRound`'s
docstring gains "The hypothesis `hstep` is load-bearing: this is not a
completeness theorem for the mirror".

The amendment: README "**Two presentations, one engine.**" → "**One
reference relation.**"; the trust diagram's "NOT bridged to relsemcore"
→ "the mirror's ONLY reference"; "What the diagram does not contain: a
bridge to `relsemcore`" dropped; WALKTHROUGH §7's relsemcore bullet
replaced by the mirror-completeness bullet; Round.lean's "THE RelSemCore
DISCLAIMER" paragraph → "THE ONLY REFERENCE". Grep for the four names
over `*.lean`/`*.md`/`*.sh`/`*.toml` in the repository, excluding the
dated records (`docs/2026-*`, `cerberus-heaplang/docs/2026-*`) and the
append-only `docs/DECISIONS.md`: zero hits. (The root package's
`RefinedCerberus/Audit.lean:9` cites "relsem/RelSem/Audit.lean" as the
lineage of its gate — none of the four names, and outside this package;
left as is.)

## 4. L-1 — the audit-script change, its run time, the plant

**The change** (Audit.lean, commit B): in the exhaustive trio sweep and
in the banned-axiom sweep the line `if n.isInternalDetail then continue`
is deleted; the two `logInfo` sentences gain "(internal details
included)"; the header states the exact scope and this history.

**Measured run time** of the audit module (`../scripts/capped
~/.elan/bin/lake env lean CerberusHeapLang/Audit.lean`, the whole
elaboration including import loading), verbatim `time` lines:

- before: `1.09s user 0.60s system 95% cpu 1.785 total` — counts
  `1158 theorems`, `1950 constants`;
- after: `1.13s user 0.65s system 100% cpu 1.778 total` — counts
  `2249 theorems`, `3536 constants`;
- after, with `Examples/MirrorCoverage.lean` in the tree: `1.16s user
  0.48s system 99% cpu 1.644 total` — the same counts (the two moved
  theorems were already counted).

Derived: +1,091 theorems and +1,586 constants swept, at no measurable
cost; both passes include internal details (the preferred option).

**The plant** (one-time, NOT retained). Appended to the leaf module
`CerberusHeapLang/WseqExhibit.lean` (imported by Audit.lean and the lib
root only):

```lean
/-- L-1 PLANT (audit-response-3, NOT RETAINED): an internal-detail
    (private) sorry that the pre-change sweeps skipped. -/
private theorem plant : True := by sorry
```

Run 1 — the NEW sweeps (`../scripts/capped ~/.elan/bin/lake build`,
exit code 1), verbatim lines:

```
warning: CerberusHeapLang/WseqExhibit.lean:128:16: declaration uses `sorry`
info: CerberusHeapLang/Audit.lean:191:0: CerberusHeapLang export pins: 116 trio-exact
error: CerberusHeapLang/Audit.lean:191:0: CerberusHeapLang axiom sweep FAILED: theorem _private.CerberusHeapLang.WseqExhibit.0.CerberusHeapLang.plant carries axiom sorryAx, outside the classical trio [propext,
 Classical.choice,
 Quot.sound]. Either the proof is wrong (sorry / a non-kernel method) or a trust decision is being made implicitly — the trust base is the trio, exactly; any change happens in Audit.lean, same commit, with provenance.
error: Lean exited with code 1
error: build failed
../scripts/capped ~/.elan/bin/lake build  1.56s user 0.97s system 107% cpu 2.352 total
```

Run 2 — the ORIGINAL sweeps (Audit.lean restored to `08af594`, plant
kept; exit code 0), verbatim lines — the finding, measured:

```
warning: CerberusHeapLang/WseqExhibit.lean:128:16: declaration uses `sorry`
info: CerberusHeapLang/Audit.lean:191:0: CerberusHeapLang export pins: 116 trio-exact
info: CerberusHeapLang/Audit.lean:191:0: CerberusHeapLang axiom sweep: 1158 theorems bounded by the trio
info: CerberusHeapLang/Audit.lean:191:0: CerberusHeapLang banned-axiom sweep: 1950 constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
Build completed successfully (445 jobs).
../scripts/capped ~/.elan/bin/lake build  1.66s user 0.99s system 102% cpu 2.593 total
```

Then the plant was reverted (`WseqExhibit.lean` byte-identical to
`08af594`; `git status` clean) and the tree rebuilt green. (Line 191 is
the `#eval` line before commit B's header edit; it is line 206 after.)

## 5. L-2 — the moves

`store_sym_lit_step` and `store_lit_sym_step` (proved by
`Step.store_eval`) moved verbatim from `ProdExhibit.lean` to the new
`CerberusHeapLang/Examples/MirrorCoverage.lean`, whose header says it is
NOT a client (it imports `CerberusHeapLang.Rules`, not the API; no
exhibit imports it; the lib root and Audit.lean import it so the sweeps
cover it). The rule-level instances at the same shapes,
`wps_store_sym_lit`/`wpt_store_lit_sym`, stay in ProdExhibit: they are
proved through the public `wps_store_eval`/`wpt_store_eval`, which is
what a client does, and they are what keeps the capability manifest's
`Frag.store_op` consumer list unchanged (ProdExhibit stays a consumer;
the FULL gate's manifest regeneration reports no drift). ProdExhibit's
header claim "no `Step.*` … in any proof of this module" is now true and
says why. `DivergeExhibit.lean`'s header states the narrow exception for
its `Step.run` use (`dg_self_step`): a NEGATIVE test may name a mirror
step to reach an engine fact; a POSITIVE exhibit may not. Grep over
`*Exhibit.lean` for `Step.<name>` applications in proof positions after
the move: `DivergeExhibit.lean:95: Step.run …` only.

## 6. L-3 — the architecture statement

`cerberus-heaplang/ARCHITECTURE.md`: 152 lines, 1,069 words (about two
pages), seven sections — the semantic authority; the mirror and its
one-directional certification; the two judgments; adequacy; the
projection; the two trust claims and the two lanes; the open items
(mirror completeness, the fuel-exhaustion request, footprint-relative
freshness, the deferred parametric interfaces). Every sentence names its
theorem; field vocabulary only. Linked from the README's first paragraph,
the WALKTHROUGH's intro, and the repository README (which gained a
four-line pointer).

## 7. The snapshot diff, classified

`scripts/signature_snapshot.lean` at `08af594` (pre) and at commit B
(post): both 18,687 lines; the pre snapshot is byte-identical to
`docs/2026-09-02_pr3-C-signatures-post.txt` (so no new snapshot file is
committed — the dedupe practice); `diff pre post` is EMPTY. Classified:
no statement added, removed or changed; the two MOVED declarations
(`store_sym_lit_step`, `store_lit_sym_step`) print with the same names
and types (the snapshot does not record the module of origin, so a pure
move is invisible to it, as expected); the audit-script change touches
no statement. Zero strikes.

## 8. The FULL gate (run at commit B's tree; this commit is docs-only)

`scripts/test_unit.sh`, exit code 0. Verbatim: the gate headers and
verdicts, then the tail.

```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 2: capped build, root package (elaborates its axiom audit) ==
ok: root build green
== gate 3: capped build, cerberus-heaplang (elaborates its axiom audit) ==
ok: cerberus-heaplang build green
== speedbump: capability manifest (regenerate; red on a red row or drift) ==
ok: capability manifest regenerated, no drift
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — no core module imports an exhibit/example/production module
ALL GATES GREEN
scripts/test_unit.sh  261.13s user 9.77s system 122% cpu 3:41.17 total
```

```
ℹ [444/446] Replayed CerberusHeapLang.Audit
info: CerberusHeapLang/Audit.lean:206:0: CerberusHeapLang export pins: 116 trio-exact
info: CerberusHeapLang/Audit.lean:206:0: CerberusHeapLang axiom sweep: 2249 theorems (internal details included) bounded by the trio
info: CerberusHeapLang/Audit.lean:206:0: CerberusHeapLang banned-axiom sweep: 3536 constants of every kind (internal details included) checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
Build completed successfully (446 jobs).
ok: cerberus-heaplang build green
== speedbump: capability manifest (regenerate; red on a red row or drift) ==
cerberus-lean-proj env: switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_opam, git redirects active
ok: capability manifest regenerated, no drift
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — no core module imports an exhibit/example/production module
ALL GATES GREEN
scripts/test_unit.sh  261.13s user 9.77s system 122% cpu 3:41.17 total
```

## 9. Borderline, for the orchestrator

- The plant build logs carry a dependency-side warning, verbatim:
  `warning: generated/Cmm_op.lean:283:5: declaration uses `sorry`` — in
  the pinned semantics workspace's generated concurrency model
  (`auxAddToRfLoad`, a set-comprehension remnant), not in this package.
  The sweeps prove it enters none of our cones (the banned-axiom sweep,
  internal details included, reports `sorryAx` absent); it is a
  cerberus-lean matter, recorded here for the semantics team.
- The exhibit modules' individual theorem docstrings carry no PROVISIONAL
  line (§2); the README table and the WALKTHROUGH label them.
- `RefinedCerberus/Audit.lean:9` (root package) cites
  "relsem/RelSem/Audit.lean" as its gate's lineage; none of the four
  names, outside this package, unchanged.
- The `hbsz` gap and the additive-capacity face (professor review 2)
  remain as recorded in `2026-09-02_pr3-notes.md`; untouched here.
