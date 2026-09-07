# Review: charter `2026-09-07_codex-charter-total-refines-partial.md` (hostile, fresh reviewer)

**VERDICT: ACCEPT WITH FIXES** — the two fixed statements elaborate as written
(measured), every clause of §4 re-derives from the actual `wpt.pre`/`wps.pre`
(re-derived below), both fences are closed for every acceptance criterion; the
fixes are precision/literal-mindedness defects (one wrong line range, one false
factual claim in §6, an under-specified `#check` comparison for T2, an
unspecified scratch-file location and environment), none of which changes a
statement or a fence. Exact textual changes are given per finding.

Reviewer: fresh subagent, 2026-09-07. Tree measured: worktree
`worktrees/codex-residuals`, Lean sources at `48e162d` (HEAD moved to `2e18821`
during the review by docs-only commits; `git diff --stat 48e162d HEAD --
cerberus-heaplang/CerberusHeapLang cerberus-heaplang/CerberusHeapLang.lean
cerberus-heaplang/scripts scripts lakefile.toml lake-manifest.json` is EMPTY).
Nothing committed, no tracked file edited, no `lake build` run; the two scratch
files lived under the gitignored `cerberus-heaplang/.lake/audit-scratch/` and
were deleted; `git status --short` at the end shows only this report and the
charter.

Provenance of every tally below: `DERIVED` = counted by me with the command
quoted; everything in code blocks is verbatim tool output.

## Findings table

| id | severity | charter § | claim | how verified |
|---|---|---|---|---|
| F1 | Medium | §3 T2 (a) + rule 5 | The printed `#check @t4_wps_of_wpt` differs from "the statement above" in ways rule 5's tolerance list (binder names, instance names, field notation) does not cover: arrow form for six hypotheses, `HasLC.hasLC` for `.hasLC`, the elided `iprop(…)` and `(GF := GF)`. A literal agent applying rule 5 ("if one does not elaborate as written … park") has grounds to park. | Elaborated the statement in scratch; output quoted in §C |
| F2 | Medium | rules 3/4/10, §3 T1 (a)(b) | "Out of tree" `#check`/`#print axioms` needs a scratch file; the charter names neither a location inside the fence nor the command. The fence says "every other file is read-only"; `/tmp` is unreadable across shells in this sandbox (stage-2 record set `TMPDIR` to the worktree). | Read rules 3/4/10; `git check-ignore -v` shows `.gitignore:2:/cerberus-heaplang/.lake` ignores `cerberus-heaplang/.lake/…` |
| F3 | Low | §1 | The environment the stage-2 agent had to discover (`CERB_PROJ`, `GIT_CONFIG_GLOBAL=/dev/null`, `TMPDIR=<worktree>/cerberus-heaplang/.lake`; `test_unit.sh:58` uses `mktemp "${TMPDIR:-/tmp}/…"`) is not carried into §1. | stage-2 record lines 5–10; residuals record lines 30–32; `scripts/capped:26–40`; `scripts/test_unit.sh:58` |
| F4 | Low | §3 T1 (c) | "`trioExports` list (Audit.lean:271–1116)" is wrong: `trioExports` is 271–1101; 1103–1116 is `axiomFreeExports` (pinned to `[]`). An insertion "near the end of 271–1116" lands in the wrong list (loud failure, but the cite is wrong). | `awk` print of Audit.lean 1100–1116 |
| F5 | Low | §6 | "every demo client uses the empty table until the call protocol E6 lands" is false: `FibRecExhibit.frSpecT` (:511), `EvenOddExhibit.eoSpecT` (:334), `Examples/CallSmoke.csSpecT` (:374) are non-empty `ProcSpecT` tables. True for the emitted-corpus clients only. The stated reason for excluding the general table ("would need `wps`'s monotonicity in `Θ`") is one route; the other is the pointwise table equality via `BiEntails.to_eq`. No Θ-monotonicity lemma exists (correct as far as it goes). | `grep -rn "ProcSpecT GF :="`; `grep -n "Θ₁\|Θ₂\|mono_Θ"` (empty); iris `BI.lean:112` |
| F6 | Low | §0 | "nothing else in the package changes" contradicts the two required pin lines (Audit.lean) and the conditional manifest regeneration. | Read §0 vs §3 |
| F7 | Low | rule 4 | "any new `macro` … creates a PUBLIC parser definition that appears in the census": true for `macro`, false for `local macro` (CorpusT4Exhibit.lean:276 `local macro "t4_source"` is absent from the census; Soundness.lean:10528 `macro "emitted_frame"` appears as `def CerberusHeapLang.tacticEmitted_frame`). Rule is conservative and harmless; rationale overstated. | `git show HEAD:…D7-post.txt \| grep` |
| F8 | Low | rule 6 | "the package warning count is not above 33" gives no counting method; the records count lines matching `^warning: CerberusHeapLang[/.]` in the gate log. A different count blocks spuriously. | stage-2 record lines 52–53; DECISIONS.md:3599 |
| F9 | Low | rule 2 vs rule 9 | Rule 9 allows one commit per deliverable plus one per record section; rule 2 requires committing the baseline snapshot, which has no named commit. | Read rules 2, 9 |
| F10 | Info | §3, §4 cites | Several ranges start one line early or end one line late (`:161–168` → clause 162–168; `:170–179` → 171–179; `:240–245` → 241–245; `:247–256` → 248–256; `Wps.lean:322–324` → 322–325; `CorpusT4Exhibit.lean:1313–1319` → statement 1313–1318, 1319 is `iintro Hcap`). None misleads. | Numbered prints below |
| F11 | Info | §5 | Inserting pin lines shifts every later Audit.lean line (the `#eval` at 1121 → 1122/1123); doc cites to `Audit.lean:11xx` go stale. `cite_check.sh` exists (`cerberus-heaplang/scripts/cite_check.sh`) but is NOT in the gate (KOI C18) — orchestrator's landing, not the agent's. | `ls cerberus-heaplang/scripts`; KOI C18 |

No Critical or High finding. No REJECT-level finding: no fixed statement fails to
elaborate; no clause fails to derive; no acceptance criterion forces an edit
outside its fence.

## Per-finding detail and required textual changes

### F1 (Medium) — T2's `#check` comparison is under-specified

Charter §3 T2 ACCEPTANCE (a), current text:

> (a) `#check @t4_wps_of_wpt` prints the statement above up to binder names (quote it);

Rule 5, current text:

> the printed type (`#check`) must be the one in §3 up to binder names, instance names, and the pretty-printer's field-notation choice (`LabelSpecT.forget Ls` may print as `Ls.forget`).

Measured output (scratch, statement verbatim from the charter, body `sorry`):

```
@t4_wps_of_wpt : ∀ {GF : BundledGFunctors} [inst : LemFuel],
  0 < LemFuel.fuel →
    ∀ [inst_1 : SpikeGS HasLC.hasLC GF] {M : MachineCtx} {p : Option sym},
      StdE3 M.file →
        (∀ (x : sym), resolveExtern M.extern x = x) →
          M.labelsAt p = t4Q →
            600 ≤ M.runState.sym_supply →
              ∀ (f : Fmap sym value) (rest : List (Fmap sym value)),
                SymFrame f →
                  allocBudget (allocCost M.tagDefs intTy 4 + allocCost M.tagDefs intTy 4) ⊢
                    wps M p (t4LsT GF M.tagDefs).forget emptyProcSpec (readoutPost ψT4) t4Main (f :: rest)
```

Differences from the source statement NOT covered by rule 5: (i) `hfuel`,
`hstd`, `hex`, `hQ`, `hsup`, `hf` print as arrows (non-dependent hypotheses);
(ii) `.hasLC` prints `HasLC.hasLC`; (iii) `iprop(…)` and `(GF := GF)` are
elided; (iv) `{GF}` (the section variable) comes first. T1's acceptance (a)
already gives the `∀ …, … ⊢ …` form and it matches (see §C); T2's does not.

REQUIRED CHANGE — replace T2 (a) with:

> (a) `#check @t4_wps_of_wpt` (out of tree) prints, up to binder names and instance names, exactly:
> `∀ {GF : BundledGFunctors} [LemFuel], 0 < LemFuel.fuel → ∀ [SpikeGS HasLC.hasLC GF] {M : MachineCtx} {p : Option sym}, StdE3 M.file → (∀ (x : sym), resolveExtern M.extern x = x) → M.labelsAt p = t4Q → 600 ≤ M.runState.sym_supply → ∀ (f : Fmap sym value) (rest : List (Fmap sym value)), SymFrame f → allocBudget (allocCost M.tagDefs intTy 4 + allocCost M.tagDefs intTy 4) ⊢ wps M p (t4LsT GF M.tagDefs).forget emptyProcSpec (readoutPost ψT4) t4Main (f :: rest)`
> (the pretty-printer writes non-dependent hypotheses as arrows, `.hasLC` as `HasLC.hasLC`, drops `iprop(…)`/`(GF := GF)`, and uses field notation); quote the actual output.

and extend rule 5's tolerance list to: "up to binder names, instance names, the
pretty-printer's field-notation choice, its arrow form for hypotheses not used
dependently, and its elision of `iprop(…)`/named-argument annotations".

### F2 (Medium) — where the out-of-tree `#check`/`#print axioms` file lives

Rule 3: "every other file is read-only". Rule 4: "`#print`/`#eval` left in a
library module (run them out of tree, quote the output in the record)". Rule 10
requires quoting `#check` and `#print axioms` output. No location and no
command are given for the scratch file. In this sandbox files under `/tmp`
are not readable across shells (the stage-2 record set `TMPDIR` to the
worktree for that reason). Measured: `git check-ignore -v
cerberus-heaplang/.lake/audit-scratch/T1.lean` → `.gitignore:2:/cerberus-heaplang/.lake`
(exit 0), so anything under `cerberus-heaplang/.lake/` is invisible to `git
status` and to the census.

REQUIRED CHANGE — add to rule 4 (or a new rule 11):

> Out-of-tree checks: write the scratch file under `cerberus-heaplang/.lake/scratch/` (gitignored — `.gitignore:2`), `import CerberusHeapLang.Wpt` (T1) / `import CerberusHeapLang.CorpusT4Exhibit` (T2) after the deliverable has been built by the gate, run `CERB_MEM_MAX=40G ../scripts/capped ~/.elan/bin/lake env lean .lake/scratch/<file>.lean` from `cerberus-heaplang/`, quote the output, delete the file before the final gate. No scratch file anywhere else in the worktree.

### F3 (Low) — environment facts not carried forward

Stage-2 record lines 5–10 (verbatim): "All commands ran in this worktree
(shell startup disabled after the first call reported `/usr/bin/bash:
/etc/profile: Permission denied`). Every Lean invocation used `scripts/capped`
with `CERB_MEM_MAX=40G`. `CERB_PROJ` was set to this worktree,
`GIT_CONFIG_GLOBAL=/dev/null` prevented the wrapper's out-of-worktree
environment self-load, and `TMPDIR` was this worktree's
`cerberus-heaplang/.lake`." `scripts/capped:26` sources the container's
`scripts/env.sh` (outside the worktree) unless both `CERB_PROJ` and
`GIT_CONFIG_GLOBAL` are set; `scripts/test_unit.sh:58` is `tmp="$(mktemp
"${TMPDIR:-/tmp}/capability_manifest.XXXXXX")"`.

SUGGESTED CHANGE — add to §1: "environment (as stage 2): `CERB_PROJ=<worktree root>`, `GIT_CONFIG_GLOBAL=/dev/null`, `TMPDIR=<worktree>/cerberus-heaplang/.lake`, `CERB_MEM_MAX=40G`; `scripts/capped` prints an env line and must never print an uncapped warning."

### F4 (Low) — wrong line range for `trioExports`

Charter §3 T1 (c): "`Audit.lean`'s `trioExports` list (Audit.lean:271–1116)".
Measured:

```
271: def trioExports : List Name := [
…
1100:   ``CerberusHeapLang.peDepth_subst,
1101:   ``CerberusHeapLang.evalDepth_subst]
1102:
1103: /-- M2 re-pin [AGENT 2026-09-06]: these six previously trio-exact
…
1109: def axiomFreeExports : List Name := [
…
1116: ]
```

REQUIRED CHANGE: `Audit.lean:271–1116` → `Audit.lean:271–1101` (and say
"append before the closing `]` at line 1101, or after any entry — the list is
unordered; the loop at 1133 pins each name, no ordering or uniqueness check;
a DUPLICATE entry would inflate the count to 906/907, so add each name once").

### F5 (Low) — §6's factual claims

Charter §6: "a `ProcSpecT.forget` with precondition `∃ m` and postcondition
`∀ m` is mathematically right, but its empty-table instance would need `wps`'s
monotonicity in `Θ`, an extra lemma; every demo client uses the empty table
until the call protocol E6 lands".

Measured — non-empty tables exist in three clients:

```
CerberusHeapLang/EvenOddExhibit.lean:334:def eoSpecT : ProcSpecT GF := fun g m vs =>
CerberusHeapLang/FibRecExhibit.lean:511:def frSpecT : ProcSpecT GF := fun _ m vs =>
CerberusHeapLang/Examples/CallSmoke.lean:374:def csSpecT : ProcSpecT GF := fun _ m vs =>
```

The emitted-corpus clients (EmittedC, CorpusT1/T4/T5/T6, PartialClients) use
only `emptyProcSpecT`/`emptyProcSpec` (grep counts: T4 `emptyProcSpecT`=6,
T5=3, T6=6, PartialClients `emptyProcSpec`=3, no `ProcSpecT GF :=` in any).

Mathematics: the `∃ m` pre / `∀ m` post shape IS right (CALL clause: the total
side supplies one `m` with `(Θ f m vs).1` — witness for `∃`; the continuation
receives `(Θ.forget f vs).2 ret = ∀ m, (Θ f m vs).2 ret`, instantiate at that
`m`, then the IH at `k'`). The general theorem `wpt M p Ls Θ k ⊢ wps M p
Ls.forget Θ.forget` is provable by the SAME induction with no monotonicity.
What the empty-table corollary would then need is `emptyProcSpecT.forget =
emptyProcSpec`, which is NOT definitional (`∃ m : Nat, ⌜False⌝` vs `⌜False⌝`;
`∀ m, ⌜True⌝` vs `⌜True⌝`) but is provable pointwise via
`BIBase.BiEntails.to_eq` (iris `BI.lean:112`: `(h : P ⊣⊢ Q) : P = Q`) — an
alternative to Θ-monotonicity. Θ-monotonicity does not exist:
`grep -n "Θ₁\|Θ₂\|mono_Θ\|mono_Theta\|Θ'" Wps.lean Wpt.lean` → no matches;
`wps_mono_Ls` (Wps.lean:633) and `wpt_mono_Ls` (Wpt.lean:429) exist for `Ls`,
`wps_wand` (Wps.lean:516) for `Ψ`.

REQUIRED CHANGE — replace the parenthesis with: "a `ProcSpecT.forget` with precondition `∃ m` and postcondition `∀ m` is mathematically right and provable by the same induction; the charter fixes the empty-table statement because it is what every EMITTED-corpus client uses (the synthetic C3 clients FibRecExhibit/EvenOddExhibit/CallSmoke carry their own tables) and because recovering `emptyProcSpec` from `emptyProcSpecT.forget` needs a table-equality or Θ-monotonicity lemma that does not exist".

### F6 (Low) — §0 wording

Charter §0: "Exactly three declarations are added (§3, statements fixed
verbatim); the two theorems are trio-exact and pinned; nothing else in the
package changes." The pins ARE package changes (two lines in Audit.lean), and
the manifest may be regenerated.

REQUIRED CHANGE: "… trio-exact and pinned (two lines in Audit.lean); nothing else in the package changes except, conditionally, the regenerated capability manifest (§3 T2)."

### F7 (Low) — `local macro` and the census

D7-post census (kept at HEAD): `grep -n "t4_source\|tacticT4"` → no match,
although `CorpusT4Exhibit.lean:276` is `local macro "t4_source" : tactic => …`;
`grep -nE "^def CerberusHeapLang\.[^ ]*(tactic|term|«)"` → 8 hits including
`def CerberusHeapLang.tacticEmitted_frame :` (from `Soundness.lean:10528:macro
"emitted_frame"`). So non-local macros appear; local ones do not. The rule
"no macro of any kind" is fine as a rule; its parenthetical is overstated.
OPTIONAL CHANGE: "(a non-`local` one creates a PUBLIC parser definition that
appears in the census; forbidden either way — write tactic blocks inline)".

### F8 (Low) — warning-count method

Records: stage-2 notes lines 52–53 "Package warning count: 33 before and 33
after, counting lines matching `^warning: CerberusHeapLang[/\.]`"; DECISIONS.md:3599
"33 warnings each: (i) `bf4554d` alone". REQUIRED CHANGE to rule 6: "the
package warning count — lines of the gate log matching `^warning:
CerberusHeapLang[/.]` — is not above 33".

### F9 (Low) — the baseline snapshot's commit

Rule 2: "Commit ONLY the baseline and the two post files"; rule 9: "One per
deliverable plus one for its record section". REQUIRED CHANGE to rule 9: "…
(the baseline snapshot goes in T1's deliverable commit)".

### F10, F11 — informational, no change forced

Off-by-one range starts (F10) are listed in the cite table; F11 is for the
orchestrator's landing.

## A. Cite table (every file:line in the charter)

Legend: ✓ lands on the named text; ≈ off by one at a boundary, not misleading; ✗ wrong.

| cite | actual line text (verbatim, trimmed) | verdict |
|---|---|---|
| Wpt.lean:5250 `end CerberusHeapLang` | `5250: end CerberusHeapLang` (file is 5250 lines) | ✓ |
| Wpt.lean:90 | `variable [LemFuel] {hlc : HasLC} {GF : BundledGFunctors}` | ✓ |
| Wpt.lean:209 | `variable [SpikeGS hlc GF]` | ✓ |
| Wpt.lean:210 | `variable {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}` | ✓ |
| "in scope there" (no `section`/`end` between 210 and 5250 except `section CreateRuleT` 4018 … `end CreateRuleT` 4094) | grep of `^(variable\|section\|end\|namespace\|omit)`: 86, 88, 90, 115, 209, 210, 941, 949, 4018, 4094, 5250 | ✓ |
| Wpt.lean:98 `LabelSpecT` | `abbrev LabelSpecT (GF : BundledGFunctors) : Type :=` | ✓ |
| Wpt.lean:112 `emptyProcSpecT` | `def emptyProcSpecT {GF : BundledGFunctors} : ProcSpecT GF :=` | ✓ |
| Wpt.lean:116–117 `emptyProcSpecT_fst` | 115 `omit [LemFuel] in`; 116 `@[simp] theorem emptyProcSpecT_fst {GF …} (f : sym) (m : Nat)`; 117 `(vs : List value) : (emptyProcSpecT (GF := GF) f m vs).1 = iprop(⌜False⌝) := rfl` | ✓ |
| Wpt.lean:152–193 `wpt.pre` | 152 `def wpt.pre [SpikeGS hlc GF] …` … 193 `stateInterp σ₂ (ns + 1) obs nt ∗ F k' (by omega) Ψ r.e r.ρ)` | ✓ |
| Wpt.lean:159 VALUE | `\| some w => iprop(⌜deliveryCost w ≤ k⌝ ∗ \|={⊤}=> Ψ w ρ)` | ✓ |
| Wpt.lean:161–168 JUMP | 161 `match jumpRedex? e with`; 162 `\| some lp =>`; 163–168 the `iprop(…)` ending `⌜1 + m ≤ k⌝ ∗ Ls lp.1 m vs ρ)` | ≈ (clause body 162–168) |
| Wpt.lean:170–179 CALL, ":177 first component" | 170 `match callRedex? e with`; 171 `\| some (ctx, f, pes) =>`; 177 `(Θ f m vs).1 ∗`; 179 `F k' (by omega) Ψ (apply_ctx ctx (ofValA (.pure a1 [] ret))) ρ)` | ≈ (171–179); :177 ✓ |
| Wpt.lean:181–182 STEP k=0 | 181 `match hk : k with`; 182 `\| 0 => iprop(⌜False⌝)` | ✓ |
| Wpt.lean:183–193 STEP k'+1 | 183 `\| k' + 1 =>` … 193 as above | ✓ |
| Wpt.lean:203–206 `wpt` | 203 `def wpt [SpikeGS hlc GF] (M …) (Ls : LabelSpecT GF)`; 206 `\| k => wpt.pre M p Ls Θ k (fun k' _ => wpt M p Ls Θ k')`; 207 `termination_by k => k` | ✓ |
| Wpt.lean:215 `wpt_unfold` | 215 `theorem wpt_unfold (k : Nat) (Ψ …) (e : CoreExpr)` | ✓ |
| Wps.lean:114 `LabelSpec` | `abbrev LabelSpec (GF : BundledGFunctors) : Type :=` | ✓ |
| Wps.lean:137 `emptyProcSpec` | `def emptyProcSpec {GF : BundledGFunctors} : ProcSpec GF :=` | ✓ |
| Wps.lean:232–266 `wps.pre` | 232 `def wps.pre [SpikeGS hlc GF] (M …) (Ls : LabelSpec GF)` … 266 `stateInterp σ₂ (ns + 1) obs' nt ∗ F Ψ r.e r.ρ)` | ✓ |
| Wps.lean:238 VALUE | `\| some w => iprop(\|={⊤}=> Ψ w ρ)` | ✓ |
| Wps.lean:240–245 JUMP | 240 `match jumpRedex? e with`; 241 `\| some lp =>`; 242–245 ending `… ∗ Ls lp.1 vs ρ)` | ≈ (241–245) |
| Wps.lean:247–256 CALL | 247 `match callRedex? e with`; 248 `\| some (ctx, f, pes) =>`; 255 `▷ ∀ (ret : value) (a1 : List annot), (Θ f vs).2 ret -∗`; 256 `F Ψ (apply_ctx …) ρ)` | ≈ (248–256) |
| Wps.lean:257–266 STEP | 257 `\| none =>`; 258 `iprop(∀ (κ …` … 266 | ✓ |
| Wps.lean:322–324 `wps` | 322 `def wps [SpikeGS hlc GF] (M …) (Ls : LabelSpec GF)`; 323 `(Θ : ProcSpec GF) :`; 324 `(SpikeVal → EnvStack → IProp GF) → CoreExpr → EnvStack → IProp GF :=`; 325 `fixpoint (wps.pre M p Ls Θ)` | ≈ (322–325) |
| Wps.lean:327 `wps_unfold` | 327 `theorem wps_unfold [SpikeGS hlc GF] {M …} {Ls : LabelSpec GF}`; 330 `wps (GF := GF) M p Ls Θ Ψ e ρ ⊣⊢ wps.pre M p Ls Θ (wps M p Ls Θ) Ψ e ρ :=` | ✓ |
| Wps.lean:341 `wps_ofVal` | 341 `theorem wps_ofVal {Ψ …} (w : SpikeVal)`; 344 `rw [wps_unfold.to_eq]` | ✓ |
| CorpusT4Exhibit.lean:1463 `end CerberusHeapLang` | `1463: end CerberusHeapLang` (file is 1463 lines) | ✓ |
| CorpusT4Exhibit.lean:1313–1319 `t4_wpt` | 1313 `theorem t4_wpt [LemFuel] (hfuel : 0 < LemFuel.fuel) [SpikeGS .hasLC GF]` … 1318 `wpt M p (t4LsT GF M.tagDefs) emptyProcSpecT 915 (readoutPost ψT4) t4Main (f :: rest) := by`; 1319 `iintro Hcap` | ≈ (statement 1313–1318) |
| "premise list copied VERBATIM" | `diff <(charter 177–181 with name substituted) <(file 1313–1317)` → `IDENTICAL` | ✓ |
| CorpusT4Exhibit.lean:1027 `t4LsT` | `def t4LsT (GF : BundledGFunctors) [SpikeGS .hasLC GF]` (a plain `def`, no `noncomputable`) | ✓ |
| CorpusT4Exhibit.lean:1032 `ψT4` | `def ψT4 : value → Mem → Prop := fun v _ => v = lint 10` | ✓ |
| CorpusT4Exhibit.lean:24 | `variable {GF : BundledGFunctors}` (in scope at 1463; only `local macro` at 276 between) | ✓ |
| Audit.lean:271–1116 `trioExports` | 271 `def trioExports : List Name := [` … 1101 `` ``CerberusHeapLang.evalDepth_subst] ``; 1109 `def axiomFreeExports : List Name := [`; 1116 `]` | ✗ (F4: 271–1101) |
| Audit.lean pin loop (my check of 1116–1135) | 1124 `let pin (expected : List Name) (n : Name) : CoreM Unit := do`; 1133 `for n in trioExports do pin allowedAxioms n`; 1135 `logInfo s!"CerberusHeapLang export pins: {trioExports.length} trio-exact, …"` — no sort/`eraseDups`/uniqueness check | ✓ (insertion anywhere in the list is fine; a duplicate would count twice) |
| scripts/boundary_check.sh:46 | `pattern='\b(CohG\|metaInterp\|byteInterp\|cursorInterp\|budgetInterp\|budgetAuth\|stateInterp_iff\|stateInterp_eq\|wps\.pre\|wpt\.pre\|wps_unfold\|wpt_unfold\|step_ctx\|one_step0\|step_action\|drive_nonmemory_steps[A-Za-z0-9_]*\|driver2\|loop_step_frag[…]*\|engine_step_matchU\|CerberusRound\|cerberusRound[A-Za-z0-9_]*)\b\|\bStep\.[A-Za-z_][A-Za-z0-9_']*'` | ✓ |
| scripts/capability_manifest.lean:155 | `cls := .rule (N "wps_load") (N "wpt_load"),` | ✓ |
| §1 "904 trio-exact, 6 axiom-free-exact" | DERIVED: `sed -n 271,1101p Audit.lean \| grep -o '``CerberusHeapLang\.…' \| wc -l` → `904`; axiomFree → `6`; duplicates → none. Record `codex-residuals-notes.md:526`: `info: CerberusHeapLang/Audit.lean:1121:0: CerberusHeapLang export pins: 904 trio-exact, 6 axiom-free-exact` | ✓ |
| §1 "484 jobs" | record :529 `Build completed successfully (484 jobs).` | ✓ |
| §1 "30 modules checked" | record :568 `BOUNDARY: 30 modules checked, 0 internals mention(s) in total, exit=0`; DERIVED from `module_classes.tsv`: 30 rows of class positive-client/declared-smoke/example-support | ✓ |
| §1 "33 package warnings" | DECISIONS.md:3599 `0 \`UNCAPPED\`, 33 warnings each: (i) \`bf4554d\` alone`; record :575 `\`warning: CerberusHeapLang/*\` lines in the gate log: 33` | ✓ |
| rule 6 "`ok: capability manifest regenerated, no drift`" | test_unit.sh:62 `echo "ok: capability manifest regenerated, no drift"` | ✓ |
| T2 (e) "`ok:   CorpusT4Exhibit — 0 internals mentions`" | boundary_check.sh:81 `echo "ok:   $short — 0 internals mentions"`; CorpusT4Exhibit is `positive-client` (tsv line 84) | ✓ |
| rule 4 "T2 copies `t4_wpt`'s `600 ≤ M.runState.sym_supply` … KOI B19's" | KNOWN-OPEN-ITEMS.md:61 `\| B19 \| **The numeral \`600\` in the three root-of-trust statements** …` | ✓ |
| §8 "D3's `Shipped.lean`, found by the stage-2 audit" | not re-verified (docs-only history; outside the Lean checks asked for) | — |

## B. Clause table — re-derived from the actual definitions

Setting: strong induction on `k` generalising `e ρ` (`Ψ`, `M`, `p`, `Ls` fixed),
IH: `∀ k' < k, ∀ e ρ, wpt M p Ls emptyProcSpecT k' Ψ e ρ ⊢ wps M p Ls.forget
emptyProcSpec Ψ e ρ`. Unfold the left with `wpt_unfold` (an `=`; Wpt.lean:215)
and the right with `wps_unfold.to_eq` (`⊣⊢` → `=` via `BIBase.BiEntails.to_eq`,
iris `BI.lean:112`; the file's own `wps_ofVal`/`wps_mono_Ls` do exactly `rw
[wps_unfold.to_eq]; simp only [wps.pre, …]`). Both `.pre`s discriminate on the
same `toVal e`, `jumpRedex? e`, `callRedex? e` (Wpt.lean:158/161/170;
Wps.lean:237/240/247), so `cases htv : toVal e`, `cases hjr : jumpRedex? e`,
`cases hcr : callRedex? e` split both sides in lockstep. `Ψ` IS fixed through
the recursion: total continuations are `F k' (by omega) Ψ …` (:179, :193),
partial `F Ψ …` (:256, :266). `IProp GF = UPred (IResUR GF)` is `BIAffine`
(iris `Instances/UPred/Instance.lean:506: instance : BIAffine (UPred M)`), so
any hypothesis may be dropped.

| clause | total side (verbatim) | partial side (verbatim) | entailment | verdict |
|---|---|---|---|---|
| VALUE `toVal e = some w` | `:159 iprop(⌜deliveryCost w ≤ k⌝ ∗ \|={⊤}=> Ψ w ρ)` | `:238 iprop(\|={⊤}=> Ψ w ρ)` | `sep_elim_right` (pure is affine); same mask `⊤`, same `Ψ w ρ` | ✓ |
| JUMP `jumpRedex? e = some lp` | `:163–168 \|={⊤}=> ∃ params cont vs ev0 evs (m : Nat), ⌜ρ = ev0 :: evs⌝ ∗ ⌜lookupLabel (M.labelsAt p) lp.1 = some (params, cont)⌝ ∗ ⌜evalPexprs … lp.2 = some vs⌝ ∗ ⌜1 + m ≤ k⌝ ∗ Ls lp.1 m vs ρ` | `:242–245 \|={⊤}=> ∃ params cont vs ev0 evs, ⌜ρ = ev0 :: evs⌝ ∗ ⌜lookupLabel … lp.1 = some (params, cont)⌝ ∗ ⌜evalPexprs … lp.2 = some vs⌝ ∗ Ls' lp.1 vs ρ` with `Ls' = LabelSpecT.forget Ls`, i.e. `Ls' lp.1 vs ρ = iprop(∃ (m : Nat), Ls lp.1 m vs ρ)` by unfolding the def | `fupd_mono`; `exists_elim` ×6 / `exists_intro` ×5 in the SAME order (params, cont, vs, ev0, evs; `m` last on the total side); the three pure conjuncts identical; drop `⌜1 + m ≤ k⌝`; `exists_intro m` for `Ls.forget`. `∃ m` is the RIGHT direction (`∀ m` would be unprovable: the total side supplies one `m`) | ✓ |
| CALL `callRedex? e = some (ctx, f, pes)` | `:172–179 \|={⊤}=> ∃ params body vs (m k' : Nat) (hb : 1 + m + k' ≤ k), ⌜lookupProc …⌝ ∗ ⌜params.length = vs.length⌝ ∗ ⌜evalPexprs …⌝ ∗ (Θ f m vs).1 ∗ ∀ ret a1, (Θ f m vs).2 ret -∗ F k' (by omega) Ψ (apply_ctx ctx …) ρ` at `Θ := emptyProcSpecT`, where `(emptyProcSpecT f m vs).1 = iprop(⌜False⌝)` (`emptyProcSpecT_fst`, `rfl`, :116–117) | `:249–256 \|={⊤}=> ∃ params body vs, … ∗ (Θ f vs).1 ∗ ▷ ∀ ret a1, (Θ f vs).2 ret -∗ F Ψ …` at `Θ := emptyProcSpec` | `wpt_empty_call_false` (Wpt.lean:274–283) already gives `wpt M p Ls emptyProcSpecT k Ψ e ρ ⊢ \|={⊤}=> ⌜False⌝`; then `fupd_mono` + `pure_elim False`. The partial clause's `▷` and `(emptyProcSpec f vs).1 = ⌜False⌝` are irrelevant — anything under `\|={⊤}=>` follows. No `ProcSpecT.forget` needed | ✓ |
| STEP `k = 0` (all three `none`) | `:182 \| 0 => iprop(⌜False⌝)` (`wpt_zero_step_eq`, :238–242) | `:258–266` (anything) | `pure_elim False` | ✓ |
| STEP `k = k' + 1` | `:184–193 ∀ κ ℓ lc sp σ₁ ns (obs : List Empty) nt, ⌜M.runState.sym_supply ≤ sp.sym⌝ -∗ stateInterp σ₁ ns obs nt ={⊤,∅}=∗ ⌜PrimStep.Reducible (⟨e, ρ, ⟨κ, p, ℓ, lc, sp⟩, M⟩, σ₁)⌝ ∗ ∀ r σ₂ eₜ, ⌜(…, σ₁) -<([] : List Empty)>-> (r, σ₂, eₜ)⌝ ={∅,⊤}=∗ stateInterp σ₂ (ns + 1) obs nt ∗ F k' (by omega) Ψ r.e r.ρ` (`wpt_step_eq`, :262–276, already discharges the dependent `by omega` and the `match hk : k`) | `:258–266 ∀ κ ℓ lc sp σ₁ ns (obs obs' : List Empty) nt, ⌜M.runState.sym_supply ≤ sp.sym⌝ -∗ stateInterp σ₁ ns (obs ++ obs') nt ={⊤,∅}=∗ ⌜PrimStep.Reducible (…)⌝ ∗ ▷ ∀ r σ₂ eₜ, ⌜(…, σ₁) -<obs>-> (r, σ₂, eₜ)⌝ -∗ £ 1 ={∅,⊤}=∗ stateInterp σ₂ (ns + 1) obs' nt ∗ F Ψ r.e r.ρ` | Intro `κ ℓ lc sp σ₁ ns obs obs' nt` (pure ∀s); `cases obs with \| nil => … \| cons x _ => exact x.elim` makes `obs = []`, so `[] ++ obs' = obs'` (definitional, `List.nil_append`) and the step hypothesis is literally `-<[]>->`; instantiate the total ∀ at `obs := obs'` — both `stateInterp` occurrences match (`σ₁ ns obs' nt`, `σ₂ (ns+1) obs' nt`); masks `⊤,∅` and `∅,⊤` identical; the pure Reducible conjunct identical; `▷` by `BI.later_intro` (iris `BI.lean:77: later_intro {P : PROP} : P ⊢ ▷ P`) on the right conjunct; `£ 1` introduced and dropped (affine); inside the `={∅,⊤}=∗`, `fupd_mono` with `sep_mono_r (IH k' (Nat.lt_succ_self k') r.e r.ρ)` | ✓ |

No clause fails; no hidden asymmetry: masks agree everywhere; `▷` and `£ 1`
occur only on the partial (weaker) side; `deliveryCost`, `1 + m ≤ k`, `1 + m +
k' ≤ k` are extra pure premises on the total side only; the existential order
matches with the total's extra `m` last; `obs : List Empty` forces `obs = []`.
The charter's §4 table is correct in every row, and its "No monotonicity lemma
for `wps` or `wpt` is needed" is correct. The per-clause equations
`wpt_val_eq`/`wpt_jump_eq`/`wpt_zero_step_eq`/`wpt_step_eq`/`wpt_empty_call_false`
(Wpt.lean:220–283) are public, are none of the manifest's 145 rule names
(`grep -oE 'N "…"' scripts/capability_manifest.lean` — `wps_ofVal` at :129 is
one; `wpt_*_eq`, `wpt_unfold`, `wps_unfold`, `wpt_mono_k`, `wpt_empty_call_false`
are not), so T1 may use them without manifest consequences; the induction
pattern `induction k using Nat.strongRecOn generalizing e ρ with` is already in
the file (Wpt.lean:434, `wpt_mono_Ls`).

## C. Elaboration outputs (verbatim)

Both runs: from `cerberus-heaplang/`, `CERB_MEM_MAX=40G ../scripts/capped
~/.elan/bin/lake env lean .lake/audit-scratch/T<n>.lean`; `capped` printed
`cerberus-lean-proj env: switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_opam, git redirects active`,
no uncapped warning, no cgroup error. Scratch files: T1 = `import
CerberusHeapLang.Wpt`, `namespace CerberusHeapLang`, the three `variable` lines
of Wpt.lean:90/209/210 and its `open` line, the charter's `def
LabelSpecT.forget` verbatim (with its docstring), the charter's `theorem
wps_of_wpt` verbatim with body `by sorry`; T2 = `import
CerberusHeapLang.CorpusT4Exhibit`, the same def inside a section with the Wpt
variables, then CorpusT4Exhibit.lean's `open` lines (18–22) and `variable {GF :
BundledGFunctors}` (24), the charter's `theorem t4_wps_of_wpt` verbatim with
body `by sorry`.

T1 (exit 0, 1.2 s):

```
.lake/audit-scratch/T1.lean:22:8: warning: declaration uses `sorry`
@wps_of_wpt : ∀ [inst : LemFuel] {hlc : HasLC} {GF : BundledGFunctors} [inst_1 : SpikeGS hlc GF] {M : MachineCtx}
  {p : Option sym} {Ls : LabelSpecT GF} (k : Nat) (Ψ : SpikeVal → EnvStack → IProp GF) (e : CoreExpr) (ρ : EnvStack),
  wpt M p Ls emptyProcSpecT k Ψ e ρ ⊢ wps M p Ls.forget emptyProcSpec Ψ e ρ
@LabelSpecT.forget : {GF : BundledGFunctors} → LabelSpecT GF → LabelSpec GF
LabelSpecT : BundledGFunctors → Type
@emptyProcSpecT : {GF : BundledGFunctors} → ProcSpecT GF
@wpt_unfold : ∀ [inst : LemFuel] {hlc : HasLC} {GF : BundledGFunctors} [inst_1 : SpikeGS hlc GF] {M : MachineCtx}
  {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF} (k : Nat) (Ψ : SpikeVal → EnvStack → IProp GF) (e : CoreExpr)
  (ρ : EnvStack), wpt M p Ls Θ k Ψ e ρ = wpt.pre M p Ls Θ k (fun k' x => wpt M p Ls Θ k') Ψ e ρ
'CerberusHeapLang.wps_of_wpt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Comparison with §3 T1 acceptance (a): identical up to instance names (`inst`,
`inst_1`) and field notation (`Ls.forget`) — both tolerated by rule 5. ✓
`def LabelSpecT.forget` compiles as a plain `def` (no `noncomputable` needed;
same as `t4LsT`, CorpusT4Exhibit.lean:1027, and `emptyProcSpecT`,
Wpt.lean:112). It picks up NO `[LemFuel]`/`[SpikeGS]` from the section (the
def's own `(Ls : LabelSpecT GF)` binder shadows the section's `{Ls}` without
error). `iprop(∃ (m : Nat), …)` syntax accepted. The `#print axioms` line
format is `'CerberusHeapLang.wps_of_wpt' depends on axioms: [ … ]`; without the
`sorry` the list will read `[propext, Classical.choice, Quot.sound]` as the
charter states.

T2 (exit 0, 1.5 s):

```
.lake/audit-scratch/T2.lean:28:8: warning: declaration uses `sorry`
@t4_wps_of_wpt : ∀ {GF : BundledGFunctors} [inst : LemFuel],
  0 < LemFuel.fuel →
    ∀ [inst_1 : SpikeGS HasLC.hasLC GF] {M : MachineCtx} {p : Option sym},
      StdE3 M.file →
        (∀ (x : sym), resolveExtern M.extern x = x) →
          M.labelsAt p = t4Q →
            600 ≤ M.runState.sym_supply →
              ∀ (f : Fmap sym value) (rest : List (Fmap sym value)),
                SymFrame f →
                  allocBudget (allocCost M.tagDefs intTy 4 + allocCost M.tagDefs intTy 4) ⊢
                    wps M p (t4LsT GF M.tagDefs).forget emptyProcSpec (readoutPost ψT4) t4Main (f :: rest)
@t4_wpt : ∀ {GF : BundledGFunctors} [inst : LemFuel],
  0 < LemFuel.fuel →
    ∀ [inst_1 : SpikeGS HasLC.hasLC GF] {M : MachineCtx} {p : Option sym},
      StdE3 M.file →
        (∀ (x : sym), resolveExtern M.extern x = x) →
          M.labelsAt p = t4Q →
            600 ≤ M.runState.sym_supply →
              ∀ (f : Fmap sym value) (rest : List (Fmap sym value)),
                SymFrame f →
                  allocBudget (allocCost M.tagDefs intTy 4 + allocCost M.tagDefs intTy 4) ⊢
                    wpt M p (t4LsT GF M.tagDefs) emptyProcSpecT 915 (readoutPost ψT4) t4Main (f :: rest)
```

The T2 statement elaborates; its printed premises are character-identical to
`t4_wpt`'s; the conclusion differs exactly as the charter says (`wpt …
emptyProcSpecT 915 …` → `wps … .forget emptyProcSpec …`). The proof
`(t4_wpt hfuel hstd hex hQ hsup f rest hf).trans (wps_of_wpt _ _ _ _)`
type-checks by inspection of the two printed types (`BIBase.Entails.trans`,
iris `BI.lean:98`); `915` is inferred, so no numeral need appear in T2's proof.
The scratch directory was deleted afterwards (`git status --short` → only `??
docs/2026-09-07_codex-charter-total-refines-partial.md` plus this report).

## D. Fence closure (per acceptance criterion)

| criterion | forces edits in | in fence? | evidence |
|---|---|---|---|
| T1 (a)(b) `#check`/`#print axioms` out of tree | a scratch file (no tracked file) | location unspecified — F2 | `.gitignore:2:/cerberus-heaplang/.lake` |
| T1 (c) pin `wps_of_wpt`, 905 | `Audit.lean` `trioExports` | yes | list is unordered; loop 1133 has no uniqueness/sort check; `trioExports.length` printed (1135) — one line added → 905 exactly |
| T1 (d) census ADDED = `def CerberusHeapLang.LabelSpecT.forget`, `theorem CerberusHeapLang.wps_of_wpt` | `Wpt.lean` append | yes | `signature_snapshot.lean:31 if n.isInternalDetail then continue` excludes `_private.*`, `match_*`, `proof_*`, `_*`; D7-post census: 5217 entries, `_private` count 0, kinds `def 1436 / theorem 3214 / ctor 416 / inductive 56 / opaque 42 / rec 56`; `def`s ARE included (`def CerberusHeapLang.t4LsT :` at 44549) — so `LabelSpecT.forget` appears as a `def` line and private helpers do not |
| T1 (e) gate green, manifest `no drift` | none | — | Wpt is class `core` (tsv:33), not a consumer (`consumerClasses = ["positive-client","declared-smoke"]`, manifest :415), so a new theorem in Wpt enters no consumer cone → no drift possible from T1 |
| T1 fuel-numeral gate | none | — | T1 text has no numeral; `NUMERALS='100000000\|100_000_000\|10\s*\^\s*8\|1000000\|1_000_000\|10\s*\^\s*6\|999999\|999_999'` (fuel_numeral_check.sh:37) |
| T2 (a)(b) | scratch file | F2 | — |
| T2 (c) pin `t4_wps_of_wpt`, 906 | `Audit.lean` | yes | — |
| T2 (d) census ADDED = `theorem CerberusHeapLang.t4_wps_of_wpt` | `CorpusT4Exhibit.lean` append | yes | a term-mode proof creates no auxiliary constants; a docstring is not a constant |
| T2 (e) boundary `0 internals mentions` | none — text constraint | stated | pattern (boundary_check.sh:46) does not match `wps_of_wpt`, `LabelSpecT.forget`, `forget`, `emptyProcSpec`, `readoutPost`, `t4LsT`, `t4_wpt`, `Entails.trans`, `BIBase.Entails.trans`; `\bStep\.` does not match `PrimStep.Reducible` (no word boundary inside `PrimStep`); docstrings are stripped (`/-` … `-/`) before grep (:50–52). Wpt.lean is `core` → not checked, so T1 may mention `wpt.pre`/`wps_unfold` freely |
| T2 fuel-numeral gate | none | — | `600`, `4`, `0` do not match the regex (verified against :37 and the `(?<![0-9A-Za-z_])…(?![0-9A-Za-z_])` guards at :87) |
| T2 (f) manifest | `docs/CAPABILITY_MANIFEST.md` regeneration, conditional | yes | CorpusT4Exhibit is a consumer (manifest :98 lists it). Cone = `getUsedConstants` closure over our constants (:449–486). Drift happens iff `wps_of_wpt`'s proof term reaches a partial RULE name (e.g. `wps_ofVal`, :129) that CorpusT4Exhibit's cone did not already contain → that row's consumer list grows. Can it go RED instead? Only `.ruleTotalUndemonstrated`/`.rulePartialUndemonstrated` rows go red on a new consumer (:719, :732); the current manifest has `0 RULE-TOTAL-UNDEMONSTRATED, 0 RULE-PARTIAL-UNDEMONSTRATED` (CAPABILITY_MANIFEST.md:183), so a new partial consumer can only DRIFT, never RED. The regeneration clause therefore suffices and its file is fenced; `scripts/capability_manifest.lean` need not be touched |
| `cite_check.sh` | not in the gate (`test_unit.sh` has no such step; KOI C18) | — | append-only edits shift no existing Wpt/CorpusT4Exhibit line; Audit.lean insertions shift later lines (F11, orchestrator's) |
| root import / `module_classes.tsv` / `API.lean` | none | correctly "not needed" | no new module; `API.lean` is a docstring table no script reads (`grep -rn "API.lean" scripts` → comments only) |
| the census file count | three files (`…-baseline.txt`, `…-T1-post.txt`, `…-T2-post.txt`) | yes | consistent between rule 2, rule 10 and the (d) criteria; no name collision in `cerberus-heaplang/docs/` (`ls \| grep refinement` → none) |

## E. Rule consistency (literal reading)

- Pin counts 905/906 from a measured 904 — consistent.
- `484 jobs`, `30 modules`, `33 warnings`, `904` — all match the record and
  my counts (§A).
- Rule 2's "private declarations do not appear in the snapshot" — verified.
- Rule 2 "APPEND only / no `-` lines" for Wpt.lean and CorpusT4Exhibit.lean —
  achievable (both files end with `end CerberusHeapLang`; inserting before it
  yields only `+` lines). Audit.lean's pin insertion is an insertion inside a
  list (a `+` line), consistent with the fence "the `trioExports` list only".
  Nothing else forces a modification of an existing line.
- Rule 6 vs T2's manifest note — consistent ("see T2's fence for the one
  case it may not").
- Rule 5 vs T2 (a) — F1 (the tolerance list is too narrow for T2's printed
  form).
- Rule 3 vs rules 4/10 — F2 (where the out-of-tree file lives).
- Rule 9 vs rule 2 — F9 (the baseline snapshot's commit).
- §0 vs §3 — F6 (pins are package changes). Otherwise §0 is short,
  self-contained and states exactly T1's theorem and T2's instance.
- Rule 7 (park), rule 8 (rebase `main` — `main` exists in this repo and is an
  ancestor of the tree), rule 1 (order) — no contradiction found.

## F. Mathematical sanity

- `LabelSpecT.forget := fun l vs ρ => iprop(∃ m, Ls l m vs ρ)` is the right
  forgetful map for the JUMP clause: the total side supplies one `m`
  (Wpt.lean:165, :168), the partial side needs `Ls' lp.1 vs ρ` (Wps.lean:245)
  — `exists_intro m`. `∀ m` would be WRONG (not derivable: nothing gives `Ls`
  at other variants).
- The empty-table restriction is honest for the emitted-corpus clients, NOT
  for "every demo client" (F5): three synthetic C3 clients carry non-empty
  `ProcSpecT` tables. The choice remains a legitimate scoping decision.
- §6's general-table shape (`∃ m` pre / `∀ m` post) is mathematically
  correct (derivation in F5). Its stated reason is imprecise: the general
  theorem needs no monotonicity; the empty-table CORollary would need either
  Θ-monotonicity (none exists — grep empty) or the pointwise table equality
  `emptyProcSpecT.forget = emptyProcSpec` via `BiEntails.to_eq`. Stating T1
  directly at the empty table, as the charter does, avoids both.

## G. Other

- The stage-2 experience (`/etc/profile: Permission denied`, `TMPDIR`,
  `CERB_PROJ`, `GIT_CONFIG_GLOBAL`) is exactly the class of friction a literal
  agent turns into a park or an improvisation; F3 carries it into §1.
- `wpt_step_eq`/`wpt_zero_step_eq` already resolve the `match hk : k with` and
  the dependent `F k' (by omega)`, so the agent never has to fight the
  dependent match; the charter's "may use `wpt_unfold` … and the
  definitions" could name these five per-clause lemmas explicitly (and the
  existing induction pattern at Wpt.lean:434) to shorten the path — optional.

## Grade

**B+** — the load-bearing content (two fixed statements, five-clause
derivation, two fences, all counts) is correct and was confirmed by
measurement and elaboration; the document still carries one wrong line range,
one false factual claim, and an under-specified `#check` comparison plus an
unspecified scratch location — precisely the "minor errors" class the operator
asked to be robust against, all fixable by the textual changes above without
touching a statement or a fence.
