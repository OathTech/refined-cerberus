# Charter: total refines partial — `wps_of_wpt` (one agent, one worktree, two deliverables, in order)

Status: DRAFT for the operator (2026-09-07). Activates only when the
orchestrator has filled in §1. Nothing in this charter authorises a merge
or a push. Every file:line below was measured in the tree this charter
activates on (Lean content of the D5 + stage-2 landing; see §1) and was
re-verified by an independent reviewer before the operator saw it (§8).

## 0. GOAL

Prove that the total statement judgment refines the partial one: for every
budget `k`, `wpt M p Ls emptyProcSpecT k Ψ e ρ ⊢ wps M p (LabelSpecT.forget Ls) emptyProcSpec Ψ e ρ`,
where `LabelSpecT.forget` erases the label specification's variant index
(`∃ m`). Then instantiate it once, on the while-loop corpus program: the
partial judgment for `t4Main` obtained from its total certificate `t4_wpt`.
Exactly three declarations are added (§3, statements fixed verbatim); the two
theorems are trio-exact and pinned (two lines in `Audit.lean`); nothing else in
the package changes except, conditionally, the regenerated capability manifest
(§3 T2).

## 1. Activation (filled in by the orchestrator; the agent does not start before)

- main commit: the one carrying this charter (`git log -1 --format=%h main`
  in the worktree; its Lean tree is `2e18821`'s); pin: cerberus-lean
  `89f7e688530c6910884518811d645e4e892e4507`, LemLib
  `f6542f8e6860d12d4655e6648bc4c45dabd1d798`, Lean 4.32.2.
- environment (what stage 2 needed in this sandbox): `CERB_PROJ=<worktree
  root>`, `GIT_CONFIG_GLOBAL=/dev/null` (both set ⇒ `scripts/capped` skips
  sourcing the container's `env.sh` outside the worktree),
  `TMPDIR=<worktree>/cerberus-heaplang/.lake` (`test_unit.sh` uses `mktemp
  "${TMPDIR:-/tmp}/…"`; `/tmp` files are not readable across shells here),
  `CERB_MEM_MAX=40G`. `capped` prints one env line and must never print an
  uncapped warning.
- worktree: `worktrees/codex-refinement`, branch `codex/total-refines-partial`,
  cut from that main and primed (`.lake`, `.cerberus-ws`) from a FRESHLY GATED
  cache of the same Lean tree.
- record file (this deliverable set writes its OWN file):
  `cerberus-heaplang/docs/2026-09-07_codex-refinement-notes.md`.
- expected baseline gate at activation: `export pins: 904 trio-exact, 6
  axiom-free-exact`, `Build completed successfully (484 jobs)`, `BOUNDARY: 30
  modules checked, 0 internals mention(s) in total, exit=0`, 33 package
  warnings.

## 2. The rules (read before every deliverable; they are the charter)

1. **Order.** T1, then T2. Do not start T2 until T1 is committed on a green
   FULL gate. Do not add deliverables. Do not "clean up".
2. **Frozen surface.** BEFORE THE FIRST PRE-SNAPSHOT, run the FULL gate once
   from the worktree root: `CERB_MEM_MAX=40G scripts/test_unit.sh` (a snapshot
   against a stale cache is not a baseline). Then the baseline snapshot, from
   `cerberus-heaplang/`:
   `CERB_MEM_MAX=40G ../scripts/capped ~/.elan/bin/lake env lean scripts/signature_snapshot.lean > docs/2026-09-07_codex-refinement-baseline.txt`.
   After each deliverable: the same command to
   `docs/2026-09-07_codex-refinement-T<n>-post.txt`; `diff -u` against the
   previous snapshot (baseline for T1, T1-post for T2). The diff must be
   EXACTLY the deliverable's ADDED list — private declarations do not appear
   in the snapshot; anything else added, removed or changed = the deliverable
   failed → rule 7. Commit ONLY the baseline and the two post files (three
   snapshot files in total; no duplicates).
3. **Fence.** Each deliverable lists the files you may edit; every other file
   is read-only. Never edit `docs/DECISIONS.md`, `docs/KNOWN-OPEN-ITEMS.md`,
   `scripts/semantics-pin.env`, any `lake-manifest.json`, anything under
   `.cerberus-ws/`, anything outside this worktree.
4. **Forbidden.** New `axiom`; `sorry`; `native_decide`, `bv_decide`,
   `ofReduce*`; any `set_option maxHeartbeats`/`maxRecDepth` (the package has
   none — adding one is a defect, not a fix); `#print`/`#eval` left in a
   library module (run them out of tree, quote the output in the record); a
   NEW numeral standing for a fuel or supply bound (copying a premise VERBATIM
   from a pinned statement — T2 copies `t4_wpt`'s `600 ≤ M.runState.sym_supply`
   — is required, not forbidden: that numeral is KOI B19's, not yours);
   removing, renaming or restating any existing declaration; a public helper
   (every helper is `private`; a public one is an ADDED census entry the
   acceptance does not allow → make it private, or park); any new `macro`,
   `syntax`, `notation` or `elab` (a non-`local` one creates a PUBLIC parser
   definition that appears in the census; forbidden either way — write tactic
   blocks inline).
5. **Statement discipline.** The statements in §3 are FIXED. If one does not
   elaborate as written, or a clause turns out not to be derivable, do NOT
   alter it: park (rule 7) with the exact error or the exact clause pair
   (§4 names them). Changing a statement is the orchestrator's decision.
   Binder NAMES and the proof are yours; the printed type (`#check`) must be
   the one in §3 up to binder names, instance names, the pretty-printer's
   field-notation choice (`LabelSpecT.forget Ls` prints as `Ls.forget`), its
   arrow form for hypotheses not used dependently, and its elision of
   `iprop(…)` and named-argument annotations such as `(GF := GF)`.
6. **Gate.** `CERB_MEM_MAX=40G scripts/test_unit.sh` from the worktree root;
   never an uncapped `lake`/`lean`; if `capped` reports an uncapped run or a
   cgroup error, STOP and report it verbatim. Done = the tail reads
   `ALL GATES GREEN` and the script exits 0 (`GATE-EXIT=0` is YOUR echo of
   `$?`, not a line the script prints — label it so), the pin count is the
   expected one (T1: 905; T2: 906), the package warning count — lines of the
   gate log matching `^warning: CerberusHeapLang[/.]` — is not above 33, and
   the manifest step reads `ok: capability manifest regenerated, no
   drift` (see T2's fence for the one case it may not).
7. **Stop rules — PARK, do not revert** ([USER 2026-09-07]). A deliverable with
   no visible path to green inside its fence and its fixed statement: STOP;
   commit the work in progress AS IT IS to a branch `codex/park-T<n>` created
   from the current head (a red build is fine THERE, never on the working
   branch); reset the working branch to its last green commit; write
   `BLOCKED: <what, where, why>; parked at codex/park-T<n> <hash>` in the
   record, tagged `[AGENT]`; move on (T1 blocked ⇒ T2 cannot start: report
   and stop). Never `git restore`/discard work. Do not widen the fence. Any
   single build or proof pass approaching one hour: stop and report (the
   project's grind ban; there is no other clock). After T2 is done or
   blocked: stop.
8. **Rebase.** Before each deliverable's final gate: `git rebase main`.
   Conflicts in your fenced files: keep main's version of anything outside
   your ADDED text. Conflicts elsewhere: stop and report.
9. **Commits.** One per deliverable plus one for its record section (the
   baseline snapshot goes in T1's deliverable commit); message
   `codex T<n>: <title> — <what was verified>`. Never a red gate on the
   working branch.
10. **Record and provenance.** One section per deliverable in the record
    file: the declarations added (names), the `#check` output, the `#print
    axioms` output, the snapshot diff classified against the ADDED list, the
    gate tail (the lines matching `^==|^ok:|^info: CerberusHeapLang|^Build
    completed|^BOUNDARY|^ALL GATES`, unmodified; the thirty per-module
    `ok:   <module> — 0 internals mentions` lines may be replaced by their
    count), the wall time. EVERY decision you take that the charter did not
    take for you (a proof strategy that departs from §4, a private helper's
    statement, a park) is written with the tag `[AGENT]`. Quote outputs
    verbatim; label every tally you derive `DERIVED`.
11. **Out-of-tree checks** (`#check`, `#print axioms`). Write the scratch file
    under `cerberus-heaplang/.lake/scratch/` (gitignored — `.gitignore:2`
    ignores `/cerberus-heaplang/.lake`), `import CerberusHeapLang.Wpt` (T1) or
    `import CerberusHeapLang.CorpusT4Exhibit` (T2) AFTER the deliverable has
    been built by the gate, run from `cerberus-heaplang/`:
    `CERB_MEM_MAX=40G ../scripts/capped ~/.elan/bin/lake env lean .lake/scratch/<file>.lean`,
    quote the output in the record, delete the file before the final gate. No
    scratch file anywhere else in the worktree.

## 3. The deliverables

### T1 — `LabelSpecT.forget` and `wps_of_wpt` (Wpt.lean)

GOAL. Append to `cerberus-heaplang/CerberusHeapLang/Wpt.lean`, immediately
before its final line `end CerberusHeapLang` (line 5250 at activation; the
file's section variables `[LemFuel] {hlc : HasLC} {GF : BundledGFunctors}`
(line 90), `[SpikeGS hlc GF]` (209), `{M : MachineCtx} {p : Option sym} {Ls :
LabelSpecT GF} {Θ : ProcSpecT GF}` (210) are in scope there), these two
declarations, statements verbatim (docstrings required; wording yours):

```lean
/-- The forgetful map from a variant-indexed label specification
    (`LabelSpecT`, Wpt.lean:98) to a plain one (`LabelSpec`, Wps.lean:114):
    the label holds if it holds at SOME variant. -/
def LabelSpecT.forget (Ls : LabelSpecT GF) : LabelSpec GF :=
  fun l vs ρ => iprop(∃ (m : Nat), Ls l m vs ρ)

/-- TOTAL REFINES PARTIAL: a total-judgment derivation at any budget, at the
    empty procedure table, is a partial-judgment derivation at the forgotten
    label specification and the empty table. -/
theorem wps_of_wpt (k : Nat) (Ψ : SpikeVal → EnvStack → IProp GF) (e : CoreExpr)
    (ρ : EnvStack) :
    wpt M p Ls emptyProcSpecT k Ψ e ρ ⊢ wps M p (LabelSpecT.forget Ls) emptyProcSpec Ψ e ρ
```

`emptyProcSpecT` is Wpt.lean:112; `emptyProcSpec` is Wps.lean:137; `wpt` is
Wpt.lean:203, `wps` is Wps.lean:322. Any helper lemma is `private`. The
theorem's proof may use `wpt_unfold` (Wpt.lean:215), the per-clause equations
that follow it — `wpt_val_eq` (:220), `wpt_jump_eq` (:225), `wpt_zero_step_eq`
(:238), `wpt_step_eq` (:264) (they already resolve the dependent `match hk : k`
and the `by omega` continuation) and `wpt_empty_call_false` (:282) — `wps_unfold`
(Wps.lean:327) and the definitions; the induction pattern `induction k using
Nat.strongRecOn generalizing e ρ with` already occurs in the file (Wpt.lean:373).
Prefer NOT to use any `wps_*` RULE lemma
(e.g. `wps_ofVal`, Wps.lean:341) — those names key the capability manifest's
consumer rows (`cerberus-heaplang/scripts/capability_manifest.lean:155`) and would mis-credit T2's
module as a partial consumer; if you do use one, T2's manifest note applies.

ACCEPTANCE (all checkable):
(a) `#check @wps_of_wpt` (out of tree) prints, up to binder names and instance
    names,
    `∀ [LemFuel] {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF] {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} (k : Nat) (Ψ : SpikeVal → EnvStack → IProp GF) (e : CoreExpr) (ρ : EnvStack), wpt M p Ls emptyProcSpecT k Ψ e ρ ⊢ wps M p (LabelSpecT.forget Ls) emptyProcSpec Ψ e ρ`;
    quote the actual output.
(b) `#print axioms CerberusHeapLang.wps_of_wpt` = `[propext, Classical.choice,
    Quot.sound]` (out of tree; quote).
(c) `Audit.lean`'s `trioExports` list (Audit.lean:271–1101; the list at
    1109–1116 is `axiomFreeExports`, not yours) gains the one entry
    `` ``CerberusHeapLang.wps_of_wpt, `` — anywhere in the list (it is unordered;
    the pin loop has no uniqueness check, so add each name ONCE — a duplicate
    inflates the count); nothing else in Audit.lean changes; gate 2 reports
    `export pins: 905 trio-exact, 6 axiom-free-exact`.
(d) census (rule 2), T1-post vs baseline: ADDED exactly
    `def CerberusHeapLang.LabelSpecT.forget` and
    `theorem CerberusHeapLang.wps_of_wpt`; REMOVED 0; CHANGED 0.
(e) FULL gate green (rule 6); warnings ≤ 33; manifest `no drift`.

ALLOWED CHANGES: ADDED only — the two declarations, their private helpers, the
one pin line.
FENCE: `cerberus-heaplang/CerberusHeapLang/Wpt.lean` (APPEND only: no existing
line may change — the census enforces it for public text; `git diff` must show
no `-` lines in this file), `cerberus-heaplang/CerberusHeapLang/Audit.lean`
(the `trioExports` list only), the record, the snapshot files.

### T2 — `t4_wps_of_wpt` (CorpusT4Exhibit.lean)

GOAL. Append to `cerberus-heaplang/CerberusHeapLang/CorpusT4Exhibit.lean`,
immediately before its final line `end CerberusHeapLang` (line 1463 at
activation), the instance of T1 on the pinned total certificate `t4_wpt`
(CorpusT4Exhibit.lean:1313–1318 — its premise list is copied VERBATIM; the
conclusion replaces `wpt … 915 …` by `wps … .forget …`):

```lean
/-- The while-loop corpus program at the PARTIAL judgment, from its total
    certificate `t4_wpt` through `wps_of_wpt`: the same premises, the label
    specification forgotten, the budget gone. -/
theorem t4_wps_of_wpt [LemFuel] (hfuel : 0 < LemFuel.fuel) [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} (hstd : StdE3 M.file)
    (hex : ∀ x, resolveExtern M.extern x = x) (hQ : M.labelsAt p = t4Q) (hsup : 600 ≤ M.runState.sym_supply)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs intTy 4 + allocCost M.tagDefs intTy 4)) ⊢
      wps M p (LabelSpecT.forget (t4LsT GF M.tagDefs)) emptyProcSpec (readoutPost ψT4) t4Main (f :: rest)
```

Proof: `t4_wpt` followed by `wps_of_wpt` (entailment transitivity). The
numeral `600` is `t4_wpt`'s own premise, copied verbatim (rule 4). `t4LsT` is
CorpusT4Exhibit.lean:1027, `ψT4` is :1032.

ACCEPTANCE:
(a) `#check @t4_wps_of_wpt` (out of tree) prints, up to binder names and
    instance names, exactly
    `∀ {GF : BundledGFunctors} [LemFuel], 0 < LemFuel.fuel → ∀ [SpikeGS HasLC.hasLC GF] {M : MachineCtx} {p : Option sym}, StdE3 M.file → (∀ (x : sym), resolveExtern M.extern x = x) → M.labelsAt p = t4Q → 600 ≤ M.runState.sym_supply → ∀ (f : Fmap sym value) (rest : List (Fmap sym value)), SymFrame f → allocBudget (allocCost M.tagDefs intTy 4 + allocCost M.tagDefs intTy 4) ⊢ wps M p (t4LsT GF M.tagDefs).forget emptyProcSpec (readoutPost ψT4) t4Main (f :: rest)`
    (the pretty-printer writes the non-dependent hypotheses as arrows,
    `.hasLC` as `HasLC.hasLC`, drops `iprop(…)`/`(GF := GF)`, and uses field
    notation; the same command on `@t4_wpt` prints the identical premises with
    the total conclusion); quote the actual output. (b) `#print axioms` = the
    trio (quote). (c) `trioExports` gains
    `` ``CerberusHeapLang.t4_wps_of_wpt, `` — pins 906; (d) census T2-post vs
    T1-post: ADDED exactly `theorem CerberusHeapLang.t4_wps_of_wpt`, REMOVED 0,
    CHANGED 0; (e) the client-boundary step still reports
    `ok:   CorpusT4Exhibit — 0 internals mentions` (the statement and proof
    must not mention `wps_unfold`, `wpt_unfold`, `wps.pre`, `wpt.pre` or any
    other name on the internals list, `scripts/boundary_check.sh:46`;
    `wps_of_wpt`, `LabelSpecT.forget`, `emptyProcSpec` are not on it);
    (f) FULL gate green; warnings ≤ 33.

MANIFEST NOTE (fence closure). The capability manifest keys consumer rows on
RULE names. `t4_wps_of_wpt`'s proof-term cone is `t4_wpt`'s cone plus
`wps_of_wpt`'s. If — and only if — the gate's manifest step reports drift
after T2, regenerate the manifest with the gate's own command from
`cerberus-heaplang/`:
`CERB_MEM_MAX=40G ../scripts/capped ~/.elan/bin/lake env lean scripts/capability_manifest.lean > docs/CAPABILITY_MANIFEST.md` (both paths relative to `cerberus-heaplang/`, where the command runs),
quote the row diff in the record, and state `[AGENT]` which rule name entered
which cone and why. Do not edit the manifest by hand; do not edit
`cerberus-heaplang/scripts/capability_manifest.lean`.

ALLOWED CHANGES: ADDED only — the theorem, the pin line; the regenerated
manifest under the note above.
FENCE: `cerberus-heaplang/CerberusHeapLang/CorpusT4Exhibit.lean` (APPEND only),
`cerberus-heaplang/CerberusHeapLang/Audit.lean` (`trioExports` only),
`cerberus-heaplang/docs/CAPABILITY_MANIFEST.md` (regeneration only, under the
note), the record, the snapshot files.

## 4. Why the fixed statements are derivable (the orchestrator's check; the reviewer re-derived it)

`wpt` is well-founded recursion on the budget: `wpt M p Ls Θ k = wpt.pre M p Ls Θ
k (fun k' _ => wpt M p Ls Θ k')` (Wpt.lean:203–206, `wpt_unfold` :215). `wps` is
the guarded fixpoint of `wps.pre` (Wps.lean:322–325, `wps_unfold` :327). Both
`.pre`s discriminate identically: `toVal e`, then `jumpRedex? e`, then
`callRedex? e`, then the step clause (Wpt.lean:152–193; Wps.lean:232–266).
Proof shape: strong induction on `k`, generalising `e` and `ρ` (`Ψ` fixed);
unfold both sides; clause by clause:

| clause | total (`wpt.pre`, Wpt.lean) | partial (`wps.pre`, Wps.lean) | bridge |
|---|---|---|---|
| VALUE (`toVal e = some w`) | `⌜deliveryCost w ≤ k⌝ ∗ \|={⊤}=> Ψ w ρ` (:159) | `\|={⊤}=> Ψ w ρ` (:238) | drop the pure conjunct |
| JUMP (`jumpRedex? e = some lp`) | `\|={⊤}=> ∃ params cont vs ev0 evs m, ⌜ρ = ev0 :: evs⌝ ∗ ⌜lookupLabel …⌝ ∗ ⌜evalPexprs …⌝ ∗ ⌜1 + m ≤ k⌝ ∗ Ls lp.1 m vs ρ` (:162–168) | the same without `m`, ending `Ls' lp.1 vs ρ` (:241–245) | `Ls' = Ls.forget`: the witness is `m`; drop `⌜1 + m ≤ k⌝` |
| CALL (`callRedex? e = some (ctx, f, pes)`) | `… ∗ (emptyProcSpecT f m vs).1 ∗ …` (:171–179, the table's first component at :177) where `(emptyProcSpecT f m vs).1 = ⌜False⌝` (`emptyProcSpecT_fst`, Wpt.lean:116–117) | anything (:248–256) | ex falso under the fupd and the existentials (`wpt_empty_call_false`, Wpt.lean:282, already gives `⊢ \|={⊤}=> ⌜False⌝`) |
| STEP, `k = 0` | `⌜False⌝` (:181–182) | — | ex falso |
| STEP, `k = k' + 1` | `∀ κ ℓ lc sp σ₁ ns obs nt, ⌜M.runState.sym_supply ≤ sp.sym⌝ -∗ stateInterp σ₁ ns obs nt ={⊤,∅}=∗ ⌜Reducible …⌝ ∗ ∀ r σ₂ eₜ, ⌜… -<[]>-> (r, σ₂, eₜ)⌝ ={∅,⊤}=∗ stateInterp σ₂ (ns + 1) obs nt ∗ wpt … k' Ψ r.e r.ρ` (:183–193) | `∀ κ ℓ lc sp σ₁ ns obs obs' nt, ⌜…⌝ -∗ stateInterp σ₁ ns (obs ++ obs') nt ={⊤,∅}=∗ ⌜Reducible …⌝ ∗ ▷ ∀ r σ₂ eₜ, ⌜… -<obs>-> (r, σ₂, eₜ)⌝ -∗ £ 1 ={∅,⊤}=∗ stateInterp σ₂ (ns + 1) obs' nt ∗ wps … Ψ r.e r.ρ` (:257–266) | `obs : List Empty`, so `obs = []` (`match obs with \| [] => rfl \| x :: _ => x.elim`), hence `obs ++ obs' = obs'` and `-<obs>->` is `-<[]>->`; instantiate the total clause at `obs := obs'`; the partial clause's `▷` is introduced, its `£ 1` discarded; the continuation is the induction hypothesis at `k'` |

Every asymmetry runs the right way: the total clause is the stronger one
(no later, no credit, a pure conjunct or a budget bound extra). No monotonicity
lemma for `wps` or `wpt` is needed. The only definition introduced is
`LabelSpecT.forget`; the empty tables are related by the CALL clause's
`⌜False⌝` on the total side, so no `ProcSpecT.forget` is needed.

## 5. Fence-closure table (every acceptance criterion → the files it forces → in the fence)

| criterion | forces edits in | fenced |
|---|---|---|
| a new public theorem (T1, T2) | `Audit.lean` (`trioExports`) | yes |
| the new def and theorem | `Wpt.lean` (append) | yes |
| the corollary | `CorpusT4Exhibit.lean` (append) | yes |
| possible consumer-row drift | `cerberus-heaplang/docs/CAPABILITY_MANIFEST.md` (regeneration only) | yes, conditional |
| snapshots | three `docs/*.txt` | yes |
| the record | one new file | yes |
| no new module | root import, `module_classes.tsv`, `API.lean` | not needed — nothing forces them |
| no gate change | `scripts/test_unit.sh`, check scripts | not needed |
| the boundary check | no file — a constraint on T2's text (§3 T2 (e)) | stated |

## 6. Not in this charter

The general procedure table (`Θ : ProcSpecT`; a `ProcSpecT.forget` with
precondition `∃ m` and postcondition `∀ m` is mathematically right and provable
by the same induction; the charter fixes the empty-table statement because it
is what every EMITTED-corpus client uses — the synthetic C3 clients
`FibRecExhibit`/`EvenOddExhibit`/`Examples/CallSmoke` carry their own tables —
and because recovering `emptyProcSpec` from `emptyProcSpecT.forget` needs a
table-equality or Θ-monotonicity lemma that does not exist);
corollaries for t1/t5/t6; the `600` symbol floor (KOI B19, its own slice);
the parked D1–D4 and the locked D8/D9 of the residuals charter; any docs
(ARCHITECTURE/README/CLAIMS — the orchestrator's landing); any pin change.

## 7. Handoff back

When T2 is done or blocked: the branch on its last green commit, the record
complete, nothing else touched. The orchestrator runs the independent FULL
gate, dispatches the fresh-reviewer range audit, writes the DECISIONS/KOI
entries and the docs, and brings the operator the merge ask.

## 8. Provenance

[USER 2026-09-07]: "propose the next codex subagent slice of work … very
cleanly structured with a clear success criterion … mathematically ambitious
but cleanly scoped … review your codex plan doc carefully with a subagent, it
should be correct, and robust against minor errors". [AGENT] (orchestrator):
the choice of theorem, the fixed statements, the fences, §4 and §5. Reviewed
before presentation by a fresh, hostile subagent:
`docs/2026-09-07_review-codex-charter-total-refines-partial.md` (ACCEPT WITH
FIXES, B+ — both statements elaborated in scratch, all five clauses
re-derived, both fences confirmed closed; its nine required textual fixes and
the range corrections are applied in this version). Prior charter defects this document is designed against
(2026-09-07 stage 2, all four blocks): statements not derivable from the
source as it stands (D1, D2) and fences missing files the acceptance forced
(D3, D4 — and D3's `Shipped.lean`, found by the stage-2 audit).
