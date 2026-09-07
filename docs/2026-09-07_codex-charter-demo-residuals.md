# Charter: the demo's residual deliverables — one agent, one worktree, one deliverable at a time

Status: DRAFT for the operator ([USER 2026-09-07]: "use codex within a
very tightly scoped worktree … you write a very tight charter for what
should be delivered. The codex agent is good at meeting goals, but bad at
drift / focus unless the goal is very clear"; "Could we roll them into one
charter? I agree about waiting until L2 lands"). ACTIVATES only when the
orchestrator has merged L2 (the re-pin) and written the activation line in
§0 with the exact main commit and pin. Nothing in this charter authorises
a merge or a push.

## 0. Activation — staged unlocks (filled in by the orchestrator)

The deliverables unlock in three stages so the agent never works in files
the orchestrator's landings (L2 the re-pin, L3 the actual file, L4
`seq_rmw`) are changing. Work ONLY in `worktrees/codex-residuals`, branch
`codex/demo-residuals`, primed (`.lake`, `.cerberus-ws`) by the orchestrator.

- **Stage 1 — UNLOCKED NOW** (main `46c28dc`; the charter itself is commit `77ea20d`/its merge; pin `f95ef8d9c`): D6 (a
  script the landings do not touch) and D5 (a new module + generator rows).
- **Stage 2 — UNLOCKED 2026-09-07** (main `6b6d9a8` = the L2 re-pin; pin
  cerberus-lean `89f7e688530c6910884518811d645e4e892e4507`, LemLib
  `f6542f8e6860d12d4655e6648bc4c45dabd1d798`, Lean 4.32.2). Worktree
  `worktrees/codex-stage2`, branch `codex/demo-residuals-2`, primed from a
  FRESHLY GATED cache. ORDER: D6 first (redo — stage 1's D6 was blocked by a
  stale-cache snapshot, not by the deliverable; the implementation was not
  retained), then D7 (alone — the round layer), then D1, D2, D3, D4. Stage
  1's D5 is being landed separately by the orchestrator; do not touch
  `Examples/PartialClients.lean`.
- **Stage 3 — unlocks when L4 has merged** (line to be written): D8, D9.

## 1. The rules (read before every deliverable; they are the charter)

1. **One deliverable at a time, in the ORDER OF WORK stated at the head of §2 (by stage).** Do not start the
   next until the current one is committed on a green FULL gate. Do not
   reorder. Do not add deliverables.
2. **Frozen surface.** BEFORE THE FIRST PRE-SNAPSHOT OF THE SESSION, run the
   FULL gate once (`CERB_MEM_MAX=40G scripts/test_unit.sh`) so the build
   cache is current — a snapshot taken against stale artifacts is not a
   baseline (stage 1's D6 was lost to exactly this). Then, before each
   deliverable, take a signature snapshot
   (`scripts/signature_snapshot.lean` → `cerberus-heaplang/docs/<date>_codex-D<n>-pre.txt`);
   after it, the post snapshot. The diff must be EXACTLY the deliverable's
   "allowed changes" list — nothing else may change text. Anything else
   changed = the deliverable failed; revert and report.
3. **Fence.** Each deliverable lists the files you may edit. Any other
   file is read-only. Never edit `docs/DECISIONS.md`, `docs/KNOWN-OPEN-ITEMS.md`,
   `scripts/semantics-pin.env`, `lake-manifest.json`, anything under
   `.cerberus-ws/`, or the sibling repositories.
4. **Forbidden.** New `axiom`; `sorry`; `native_decide`, `bv_decide`,
   `ofReduce*`; any `set_option maxHeartbeats`/`maxRecDepth` increase; any
   numeral standing for a fuel or supply bound; removing or renaming a
   pinned export; changing a pinned export's statement unless the
   deliverable's allowed-changes list names it verbatim. Every new public
   theorem is measured trio-exact (`#print axioms` = `propext`,
   `Classical.choice`, `Quot.sound`) and pinned in `Audit.lean`.
5. **Gate.** `CERB_MEM_MAX=40G scripts/test_unit.sh` (never an uncapped
   `lake`/`lean`). A deliverable is done only when the tail reads
   `ALL GATES GREEN` / `GATE-EXIT=0`, the pin count is the expected one, and
   the package linter warning count has not increased. Quote the tail
   verbatim in the record.
6. **Record.** One file, `cerberus-heaplang/docs/<date>_codex-residuals-notes.md`,
   one section per deliverable: what changed (names), the snapshot diff
   classified against the allowed list, the gate tail verbatim, the time
   spent. No other docs are written or edited unless a deliverable's fence
   names one (then only the named lines).
7. **Stop rules — PARK, do not revert** ([USER 2026-09-07]). A deliverable
   with no visible path to green (a proof that needs a statement change
   outside its allowed list, a missing engine fact, a design choice, a
   frozen-surface diff you cannot explain): STOP; commit the work in
   progress AS IT IS to a park branch `codex/park-D<n>` created from the
   current head (a red build is fine THERE — never on the working branch);
   then reset the working branch to its last green commit; write
   "BLOCKED: <what, where, why>; parked at codex/park-D<n> <hash>" in the
   record; move to the next deliverable. Never `git restore`/discard work.
   Do not widen the fence to get through. Any single build or
   proof pass approaching one hour: stop and report (the project's grind
   ban, not a time box). The operator's check-in is the only other clock. When the last deliverable
   is done or blocked: stop; do not start anything else; do not "clean up".
8. **Rebase.** Before each deliverable's final gate: `git rebase main`.
   Conflicts in your fenced files: resolve keeping main's version of
   anything outside your allowed changes. Conflicts elsewhere: stop and
   report.
9. **Commits.** One per deliverable (plus one for its record section),
   message = `codex D<n>: <deliverable title> — <what was verified>`.

## 2. The deliverables — the ORDER OF WORK is: D6, D5 (stage 1); D7, D1, D2, D3, D4 (stage 2); D8, D9 (stage 3). The numbering below is by topic, not order.

Each: GOAL (what exists afterwards, verbatim where a statement),
ACCEPTANCE (checkable), ALLOWED CHANGES (the only statement-text changes
permitted), FENCE (files). There are no time boxes ([USER 2026-09-07]:
"the real time box is just I get impatient and check in"); the only clock
is the project's one-hour tripwire on a single build or proof pass.

### D1 — the driver-kill adequacy lemma (KOI B16)
GOAL (fixed 2026-09-07 against main 6b6d9a8): a theorem
`wpt_driver_killed_alloc` in `ProdLoop.lean`, the dual of
`wpt_driver_done_alloc` (ProdLoop.lean:444): the SAME premise list except that
the total-judgment hypothesis `hwp` delivers a KILL classification (the
existing kill faces: `evalClass_cAdd_overflow = .undef loc [UB036…]` and its
kin in `OverflowExhibit.lean`/`EvalClass.lean`), with conclusion the
whole-run kill: `CerbND.runND (_root_.drive fmapEmpty false f args)
((initial_driver_state sup f fs).1) = [(nd_status.Killed dst' (Undef0 loc ubs),
([] : List String), dst')]` for the `loc`/`ubs` the face names. Then the
application: `overflow_certified_killed [LemFuel] (hfuel : _ ≤ LemFuel.fuel)
(sup) (fs) (args)` — the overflow program (OverflowExhibit.lean's, at the
program's own `INT_MAX` operand as it is written there) has, through the
genuine pipeline, exactly one outcome and it is the UB036 kill — replacing
the record's compiled-run measurement by a theorem. ACCEPTANCE:
`overflow_driver2_killed`'s content restated as a whole-run theorem
`overflow_certified_killed` over the genuine pipeline at every fuel above
the bound; pinned trio-exact; the record's compiled-run measurement is
now a corollary. ALLOWED CHANGES: ADDED only. FENCE:
`CerberusHeapLang/ProdLoop.lean`, `ProdEntry.lean`, `OverflowExhibit.lean`,
`Audit.lean` (pin list only), the record.

### D2 — the symbolic-int storability lemma (KOI B15)
GOAL (fixed 2026-09-07): `exhibitC_prod_e3` (EmittedCExhibit.lean:732)
generalised from the literal `3` to a variable: `theorem exhibitC_prod_e3
[LemFuel] (hfuel : 30 ≤ LemFuel.fuel) (n : Int) (hn : 0 ≤ n) (hrange : <the
range premise for `n + 1` spelled EXACTLY as `wps_c_add`'s in IntRules.lean —
no numeral>) (sup : Nat) (fs : CerbFS.FsState) (args : List String) : ∃ dres
dst', CerbND.runND (_root_.drive fmapEmpty false (prodFileLib stdlibE3 []
(progCE3 n)) args) ((initial_driver_state sup (prodFileLib stdlibE3 [] (progCE3
n)) fs).1) = [(nd_status.Active dres, ([] : List String), dst')] ∧
dres.dres_core_value = lint (n + 1) ∧ dres.dres_blocked = false ∧
dres.dres_stdout = "" ∧ dres.dres_stderr = ""`, proved via a new `Heap.lean`
lemma giving the byte image of `Specified(n)` at an `int` cell for every
in-range `n` (KOI B15). ACCEPTANCE: the
generalised `exhibitC_prod_e3` (n quantified, `hn` range premise) pinned;
the literal-3 version retired. ALLOWED CHANGES: `exhibitC_prod_e3`'s
statement (before/after named), ADDED lemmas. FENCE: `Heap.lean`,
`EmittedCExhibit.lean`, `Audit.lean` (pins), the record.

### D3 — the program-derived symbol bound (KOI B19)
GOAL (fixed 2026-09-07): a computable `symBound : Core file → Nat` (one plus
the largest source symbol number occurring in the file; `symBound_spec`
proved) and the SIX `hsup` premises rewritten: `(hsup : 600 ≤ sup)` →
`(hsup : symBound (prodFileLib stdlibE3 [] <tMain>) ≤ sup)` at
CorpusT5Exhibit.lean:550, CorpusT6Exhibit.lean:756, CorpusT4Exhibit.lean (the
production statement), and `(hsup : 600 ≤ M.runState.sym_supply)` → `(hsup :
symBound <the M's file> ≤ M.runState.sym_supply)` at CorpusT5Exhibit.lean:432,
CorpusT6Exhibit.lean:429/:479, CorpusT4Exhibit.lean:785; plus ONE negative
theorem: for t5 at `sup = 505` (the E5 audit's measured collision) the genuine
pipeline's outcome is a kill (`nd_status.Killed …`). ACCEPTANCE: `600` absent
from every statement (gate 1b is extended to red on `600` outside a
`*_shipped` — plant it); the six premises read as above.
ALLOWED CHANGES: the three `hsup` premises; ADDED. FENCE: `ProdEntry.lean`
(or wherever `symBound` belongs — one module), `CorpusT4/T5/T6Exhibit.lean`,
`Audit.lean` (pins), the record.

### D4 — the fresh-symbol abstraction (KOI B20)
GOAL (fixed 2026-09-07): in `wps_neg_bound` (Wps.lean:5280) and
`wpt_neg_bound` (Wpt.lean:4860) the client-visible conjunct
`s = fresh_given_int k ∧ M.runState.sym_supply ≤ k` (as printed there) is
replaced by `FreshAbove M.runState.sym_supply s`, where `def FreshAbove (sup :
Nat) (s : sym) : Prop := ∃ k, sup ≤ k ∧ s = fresh_given_int k` lives beside
`SymFrame` with `FreshAbove.intro` and `FreshAbove.ne_of_lt` (a fresh symbol
differs from every symbol numbered below `sup`); NOTHING else in the two
statements changes; every existing client (the E5 exhibits, `PartialClients`
if present) re-derived through `FreshAbove` only. ACCEPTANCE: the snapshot
diff = exactly the two rules + `FreshAbove` and its two lemmas ADDED; no
client statement changes.
ALLOWED CHANGES: the two rules. FENCE: `Rules.lean`, `Wps.lean`, `Wpt.lean`,
the E5 exhibits' proof bodies, the record.

### D5 — the partial-face clients (manifest: 7 RULE-PARTIAL-UNDEMONSTRATED rows)
GOAL: partial-correctness (`wps`) clients that consume each undemonstrated
partial rule — one `t5` partial client is expected to close five; the
remaining two per the manifest's row texts. ACCEPTANCE: the regenerated
manifest reports `0 RULE-PARTIAL-UNDEMONSTRATED`; the generator's row
classes updated to `.rule`. ALLOWED CHANGES: ADDED only (plus the
generator's data rows). FENCE: a new `Examples/PartialClients.lean` (+ its
`module_classes.tsv` row), `scripts/capability_manifest.lean` (row classes
only), `docs/CAPABILITY_MANIFEST.md` (regenerated), `Audit.lean` (pins),
the record.

### D6 — the whole-text transcription check
GOAL: `scripts/corpus_skeleton.lean` compares the transcribed term's FULL
text including leaves (constants, symbols) against the emitted `.core`,
not a constructor skeleton with opaque leaves. ACCEPTANCE: the
dead-literal plant (`Specified(0)` → `Specified(7)` in a `save`
initialiser) goes RED; all existing rows still `equal`; every existing
plant still mismatches; the gate step green. ALLOWED CHANGES: none
(script only). FENCE: `scripts/corpus_skeleton.lean`, the record.

### D7 — the head-form scaffold and the E5 duplications (KOI C17)
GOAL: ONE lemma over `step_ctx = map F (get_ctx …)` carrying the 42-site
`key … head? … cons_of_head?` scaffold; the clone families (excluded-store
`step_ctx_*`, `lift_neg'`'s ten arms, the tripled client `t*Load`/
`t*Kill_eq` macros, `depLe*` triplicate, `symC/symK_eval` twins, the three
labels-proof copies) reduced to one definition each. ACCEPTANCE: snapshot
byte-identical (ADDED = the one lemma and the shared definitions; REMOVED =
the clones' PRIVATE helpers only; CHANGED 0); pin count unchanged; gate
green; warnings not up. ALLOWED CHANGES: none to public statements.
FENCE: `Round.lean`, `DriverCollapse.lean`, `Soundness.lean`, the exhibit
proof bodies, the record.
concurrently — it touches the round layer).

### D8 — LOCKED until the second activation line: lift the empty tag-definitions premise (KOI B4)
GOAL: the struct program `docs/corpus-e0/t7_struct.c` certified end to end:
`t7_certified_production` over the genuine pipeline with the FILE's tag
definitions (not `fmapEmpty`), transcribed verbatim, oracle cross-check
recorded. ACCEPTANCE: the theorem (shape fixed at the second activation);
the corpus check covers `t7`'s whole `main`; `htd : M.tagDefs = fmapEmpty`
generalised to the file's tag table on the adequacy chain with the E-arc's
member-shift constructs classified. ALLOWED CHANGES: the adequacy
theorems' `htd` premise (listed at activation), ADDED. FENCE: to be set
at the second activation.

### D9 — LOCKED until the second activation line: the coupling-library extraction (Lane C item 6)
GOAL: a second Lake package `cerberus-iris/` (name fixed at activation)
holding the fragment-INDEPENDENT coupling (the `Heap` coupling, `MemWF`,
the bundles, `EnvLaws`, `MachineCtx`/`Ctl`/`Config`, the ND collapse, the
cold start — the module list fixed at activation from the Lane C note §6),
the demo importing it. ACCEPTANCE: every pinned export of the demo present
with IDENTICAL name and axiom set; every statement byte-identical (the
snapshot diff is EMPTY); both gates green; the manifest/CLAIMS/boundary/
skeleton instruments unchanged. ALLOWED CHANGES: none. FENCE: the new
package, `lakefile`s, `CerberusHeapLang.lean` imports, the record. TIME
BOX: 2 days.

## 3. What is NOT in this charter
E6/E7 (the call protocol and the scheduler lift — designed with the
operator first, then chartered separately); anything in the RefinedC
layer; any docs pass (ARCHITECTURE/README/WALKTHROUGH are edited only by
the orchestrator's landing of this branch); any change to the pin.

## 4. Handoff back
When the last unlocked deliverable is done or blocked: the branch is left
on its last green commit with the record complete; the orchestrator runs
the independent FULL gate, dispatches the fresh-reviewer range audit,
writes the DECISIONS/KOI entries, and brings the operator the merge ask.

## 5. Provenance
[USER 2026-09-07]: the request and the single-charter form. [AGENT]
(orchestrator): the factoring, the rules, the time boxes. Statements
marked "fixed at activation" are filled in by the orchestrator at each
stage's activation so the agent never chooses a statement shape (stage 1's
D5/D6 need none: D5's targets are the manifest's seven
RULE-PARTIAL-UNDEMONSTRATED rows as printed in `docs/CAPABILITY_MANIFEST.md`;
D6's target is the script's own plant).
