# Audit: range `6df8982..a994676` (branch `codex/total-refines-partial`, the Codex refinement slice T1 + T2)

**VERDICT: PASS** — no fix is required before merge. Every charter
constraint, every fixed statement, every count and every quoted output in
the range was re-measured in this worktree and holds; no logical or
coverage gap; no trust property touched. The six notes below are all
Info-level (three are the orchestrator's landing items the charter itself
assigns to the orchestrator, three are observations that force nothing).

Auditor: fresh subagent, 2026-09-07, read-only in
`worktrees/codex-refinement` (HEAD `a994676`, base `main` = `6df8982`,
confirmed ancestor). Nothing committed, no tracked file edited, no
`lake build`, no uncapped Lean invocation. Two scratch files lived under
the gitignored `cerberus-heaplang/.lake/audit-scratch/`
(`.gitignore:2:/cerberus-heaplang/.lake`) and were deleted with the
directory; `git status --short` at the end shows only this report.
Provenance of every tally: `DERIVED` = computed by me with the command
named; code blocks are verbatim tool output.

Read first, in order: CLAUDE.md, docs/AUDIT-BRIEF.md, docs/KNOWN-OPEN-ITEMS.md,
the charter `docs/2026-09-07_codex-charter-total-refines-partial.md`, the
record `cerberus-heaplang/docs/2026-09-07_codex-refinement-notes.md`, the
pre-launch review `docs/2026-09-07_review-codex-charter-total-refines-partial.md`,
ARCHITECTURE.md §5 and §7.

## Findings table

| id | severity | file:line | claim (one line) | how verified |
|---|---|---|---|---|
| N1 | Info (orchestrator landing item) | `cerberus-heaplang/README.md:1037–1039`; `docs/KNOWN-OPEN-ITEMS.md:124` | The shop-window "expected FULL gate tail" still quotes `Audit.lean:1121:0 … 904 trio-exact`; at HEAD it is `Audit.lean:1123:0 … 906 trio-exact`. Not the agent's (README/KOI are outside the fence; charter §6/§7 assigns docs to the orchestrator). | `git grep -nE 'Audit\.lean:1[0-9]{3}'` over `*.md`; T2 final gate log line quoted below |
| N2 | Info | charter §1 (`docs/2026-09-07_codex-charter-total-refines-partial.md`) | "`capped` prints one env line" is inaccurate under the very environment §1 prescribes: with `CERB_PROJ` and `GIT_CONFIG_GLOBAL` both set, `scripts/capped:26–40` skips sourcing `env.sh` and prints nothing. The RECORD states this correctly (record :27–29); the charter sentence is the imprecise one. Charter text is already on `main`; a one-line erratum at the landing suffices. | Read `scripts/capped:26–40`; `grep -l 'cerberus-lean-proj env' .lake/codex-refinement-*.log` → no match in any of the agent's five gate logs |
| N3 | Info | `git branch --list 'codex/park-*'` | `codex/park-D1..D4` exist — all committed 06:20–06:32 UTC on 2026-09-07 (the stage-2 residuals charter, documented on main in `docs/2026-09-07_codex-charter-demo-residuals.md`, `cerberus-heaplang/docs/2026-09-07_codex-stage2-notes.md`, DECISIONS). Pre-range; not this slice's. No `codex/park-T*` exists. | `git log -1 --format='%h %cd %s'` per branch; `git grep -c 'codex/park-D' 6df8982 -- docs cerberus-heaplang/docs` |
| N4 | Info | `cerberus-heaplang/.lake/codex-refinement-*.{log,meta,diff}` (13 files, gitignored) | The agent's gate/check/snapshot logs are still on disk under the ignored `.lake/`. They are primary evidence (I diffed the record against them — every quote is byte-identical) and are invisible to git; the container rule makes scratch ephemeral, so the orchestrator may delete them at the landing. `scratch/` is empty (the check files were deleted as the record says). | `ls -la --time-style=full-iso cerberus-heaplang/.lake/` |
| N5 | Info (orchestrator docs pass) | `cerberus-heaplang/{README.md,ARCHITECTURE.md,docs/CLAIMS.md,CerberusHeapLang/API.lean}` | Neither `wps_of_wpt` nor `t4_wps_of_wpt` nor `LabelSpecT.forget` appears on any shop-window surface yet (only in DECISIONS' charter entry). Expected — charter §6 "any docs … the orchestrator's landing". `t4_wps_of_wpt` is a corollary (its proof term's direct constants are `t4_wpt`, `wps_of_wpt` and the statement's constants — nothing else) and should be documented as such. | `grep -rn 'wps_of_wpt\|LabelSpecT.forget'` over those files; `getUsedConstantsAsSet` output below |
| N6 | Info | record :31–40 (`.bash_logout` / "nono-sandbox skill") | A login-shell artefact outside the gate log; the record says no permission/profile change was made. In-repo consequence: none — `git status --short` empty, `git status --short --ignored` shows nothing outside `.lake/`, `.cerberus-ws/`, `worktrees/`, `.refinedc-ws/`, `.opamroot/`. The home directory is outside my remit and was not inspected. | `git status --short --ignored \| grep -vE '\.lake/\|\.cerberus-ws\|worktrees/\|\.refinedc-ws\|\.opamroot'` → empty |

No Critical, High, Medium or Low finding. No KOI entry is contradicted or
worsened by this range; the range creates no new open item.

## Per-finding detail

### N1 — stale expected gate tail on two surfaces (orchestrator's)

`cerberus-heaplang/README.md:1037–1039` and `docs/KNOWN-OPEN-ITEMS.md:124`
give the expected FULL tail as `export pins: 904 trio-exact, 6
axiom-free-exact` at `Audit.lean:1121:0`. The T2 final gate log
(`.lake/codex-refinement-T2-final-gate.log`, byte-identical to the record's
quote) reads:

```
info: CerberusHeapLang/Audit.lean:1123:0: CerberusHeapLang export pins: 906 trio-exact, 6 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1123:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (6479 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1123:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (9679 constants of every kind swept, internal details included — count informational, environment-dependent)
```

Both files are outside the charter's fence (rule 3 forbids KOI edits
outright), so this is the landing's docs item, not a defect of the range.
No PROSE cite (backticked `Audit.lean:N`) in ARCHITECTURE.md, README.md or
CLAIMS.md points at or beyond the first insertion line (1067): the only ones
are `ARCHITECTURE.md:582` (`Audit.lean:264`–`265`), `:685` (`:45`) and `:681`
(`:494`/`:664`/`:789`, already `USE`-class before this range). DERIVED with
`grep -noE 'Audit\.lean[\`]?:[0-9]+' ARCHITECTURE.md README.md docs/CLAIMS.md`
and `scripts/cite_check.sh ARCHITECTURE.md` (`TMPDIR` pointed at my scratch
dir; the script is read-only without `--fix`), whose summary line was
`cite-check: ARCHITECTURE.md — 301 cites; EXACT 218; DECL 32 (fixed 0; …);
USE 16; HAND 22; PIN 13; NOFILE 0; RANGE 18 (never rewritten)` — none of the
non-EXACT rows names `Audit.lean` at a shifted line. So the pin insertions
made NO existing cite stale; only the two quoted expected tails.

### N2 — the charter's `capped` sentence vs the wrapper's behaviour

`scripts/capped:26–40` (verbatim excerpt):

```
if [[ -z "${CERB_PROJ:-}" || -z "${GIT_CONFIG_GLOBAL:-}" ]]; then
  …
  if [[ -n "$_env_sh" ]]; then
    # shellcheck source=/dev/null
    source "$_env_sh"
  else
    echo "capped: note — no scripts/env.sh found above $(dirname "$_capped_self"); proceeding with the current environment" >&2
  fi
fi
```

The "env line" (`cerberus-lean-proj env: switch=… , git redirects active`)
is printed by `env.sh` when sourced, i.e. only when one of the two variables
is unset. Under the charter's §1 environment nothing is printed — which is
what the record says ("emits no environment banner") and what the agent's
five gate logs show (no such line). My own scratch runs did NOT set the two
variables and therefore did show the env line; both behaviours are the
script's. No action on the range.

### N3 — the park branches

```
codex/park-D1 55b54b5 2026-09-07 06:20:04 +0000 codex D1: park driver-kill adequacy — current total judgment has no kill terminal interface
codex/park-D2 09f9b90 2026-09-07 06:23:49 +0000 codex D2: park symbolic-int generalization — verbatim rule has numeric range contrary to fixed goal
codex/park-D3 450c87e 2026-09-07 06:29:20 +0000 codex D3: park program-derived symbol bound — gate fence conflict and 14 premises verified
codex/park-D4 2ad35c7 2026-09-07 06:32:30 +0000 codex D4: park fresh-symbol abstraction — required placement and audit pin fence conflicts verified
```

All four predate this range (first commit 20:30:39 UTC) by fourteen hours
and are the stage-2 charter's documented parks (KOI B15/B16/B19/B20 cite
them). This slice parked nothing: no `codex/park-T1`/`T2` branch, and the
worktree reflog shows only the four range commits after the two
fast-forwards of the launch-incident fix (DECISIONS' last entry):

```
a994676 HEAD@{2026-09-07 20:36:26 +0000}: commit: codex T2: corollary record — checks, census and final full gate quoted
a9cbd77 HEAD@{2026-09-07 20:35:02 +0000}: commit: codex T2: while-loop partial corollary — full gate, exact signature and trio verified
d5b410f HEAD@{2026-09-07 20:31:30 +0000}: commit: codex T1: refinement record — checks, census and full gate quoted
a0b728c HEAD@{2026-09-07 20:30:39 +0000}: commit: codex T1: total refines partial — full gate, exact signatures and trio verified
6df8982 HEAD@{2026-09-07 20:05:58 +0000}: merge codex-charter-3: Fast-forward
1c5eac1 HEAD@{2026-09-07 20:04:21 +0000}: merge codex-charter-3: Fast-forward
2e18821 HEAD@{2026-09-07 19:39:19 +0000}: reset: moving to HEAD
```

(No `rebase` entry: a `git rebase main` on an up-to-date branch is a no-op
and writes none — consistent with the record's "reported the branch up to
date"; it cannot be positively confirmed from the reflog.)

### N4 — the agent's logs under `.lake/` (evidence, then ephemeral)

```
-rw-rw-r-- 1 1000 1000 163107 2026-09-07 20:25:29.838001153 +0000 codex-refinement-baseline-gate.log
-rw-rw-r-- 1 1000 1000 165398 2026-09-07 20:28:42.621151051 +0000 codex-refinement-T1-built-gate.log
-rw-rw-r-- 1 1000 1000    491 2026-09-07 20:28:59.472896401 +0000 codex-refinement-T1-check.log
-rw-rw-r-- 1 1000 1000 163107 2026-09-07 20:30:15.303741429 +0000 codex-refinement-T1-final-gate.log
-rw-rw-r-- 1 1000 1000     28 2026-09-07 20:30:15.307455678 +0000 codex-refinement-T1-final-gate.meta
-rw-rw-r-- 1 1000 1000 106133 2026-09-07 20:27:19.173399923 +0000 codex-refinement-T1-proof.log
-rw-rw-r-- 1 1000 1000   1459 2026-09-07 20:29:31.282413665 +0000 codex-refinement-T1-snapshot.diff
-rw-rw-r-- 1 1000 1000 163269 2026-09-07 20:32:41.673476029 +0000 codex-refinement-T2-built-gate.log
-rw-rw-r-- 1 1000 1000     28 2026-09-07 20:32:41.677235866 +0000 codex-refinement-T2-built-gate.meta
-rw-rw-r-- 1 1000 1000   1337 2026-09-07 20:33:00.342184173 +0000 codex-refinement-T2-check.log
-rw-rw-r-- 1 1000 1000 163107 2026-09-07 20:34:27.036821511 +0000 codex-refinement-T2-final-gate.log
-rw-rw-r-- 1 1000 1000     28 2026-09-07 20:34:27.039666171 +0000 codex-refinement-T2-final-gate.meta
-rw-rw-r-- 1 1000 1000   1567 2026-09-07 20:33:32.152685532 +0000 codex-refinement-T2-snapshot.diff
```

Used in §F below. They are worth keeping until the landing (they let the
orchestrator re-check any quote) and deleting after.

### N5 — the corollary's status

`t4_wps_of_wpt`'s proof term references exactly (Lean `getUsedConstantsAsSet`,
restricted to our namespace; verbatim):

```
CerberusHeapLang.t4_wps_of_wpt: 26 direct CerberusHeapLang constants:
  CerberusHeapLang.CorpusE0.t4Main
  CerberusHeapLang.LabelMap
  CerberusHeapLang.LabelSpecT.forget
  CerberusHeapLang.MachineCtx
  CerberusHeapLang.MachineCtx.extern
  CerberusHeapLang.MachineCtx.file
  CerberusHeapLang.MachineCtx.labelsAt
  CerberusHeapLang.MachineCtx.runState
  CerberusHeapLang.MachineCtx.tagDefs
  CerberusHeapLang.SpikeGS
  CerberusHeapLang.StdE3
  CerberusHeapLang.SymFrame
  CerberusHeapLang.allocBudget
  CerberusHeapLang.allocCost
  CerberusHeapLang.emptyProcSpec
  CerberusHeapLang.emptyProcSpecT
  CerberusHeapLang.intTy
  CerberusHeapLang.readoutPost
  CerberusHeapLang.resolveExtern
  CerberusHeapLang.t4LsT
  CerberusHeapLang.t4Q
  CerberusHeapLang.t4_wpt
  CerberusHeapLang.wps
  CerberusHeapLang.wps_of_wpt
  CerberusHeapLang.wpt
  CerberusHeapLang.ψT4
  aux decls with prefix CerberusHeapLang.t4_wps_of_wpt: []
```

It adds nothing beyond `t4_wpt` + `wps_of_wpt`; its value is as the one
pinned INSTANCE of the metatheorem on an emitted-corpus certificate. The
shop-window text should say "corollary of `t4_wpt` by `wps_of_wpt`" — the
orchestrator's docs pass (charter §6), not a finding.

## Verified clean — A to I, with the measurement

### A. Charter compliance — CLEAN

`git diff 6df8982 a994676 --stat` (verbatim):

```
 cerberus-heaplang/CerberusHeapLang/Audit.lean      |     2 +
 .../CerberusHeapLang/CorpusT4Exhibit.lean          |    12 +
 cerberus-heaplang/CerberusHeapLang/Wpt.lean        |    68 +
 .../docs/2026-09-07_codex-refinement-T1-post.txt   | 52325 ++++++++++++++++++
 .../docs/2026-09-07_codex-refinement-T2-post.txt   | 52344 +++++++++++++++++++
 .../docs/2026-09-07_codex-refinement-baseline.txt  | 52313 ++++++++++++++++++
 .../docs/2026-09-07_codex-refinement-notes.md      |   449 +
 7 files changed, 157513 insertions(+)
```

Exactly the fence: seven files, zero deletions anywhere. Per commit
(`git show --numstat`): `a0b728c` = Wpt 68/0, Audit 1/0, baseline + T1-post
snapshots; `d5b410f` = record 245/0; `a9cbd77` = CorpusT4Exhibit 12/0,
Audit 1/0, T2-post snapshot; `a994676` = record 204/0 — rule 9's shape
exactly (baseline in T1's deliverable commit, per F9 of the review).

- `Wpt.lean`: the diff is a single hunk `@@ -5247,4 +5247,72 @@` with 68
  `+` lines and NO `-` line, ending `+ ` / ` end CerberusHeapLang` — the
  insertion is immediately before the final `end CerberusHeapLang`
  (base line 5250 → HEAD line 5318).
- `CorpusT4Exhibit.lean`: single hunk `@@ -1460,4 +1460,16 @@`, 12 `+`
  lines, no `-`, immediately before the final `end CerberusHeapLang`
  (1463 → 1475).
- `Audit.lean`: exactly two `+` lines, at HEAD lines 1067
  (`` ``CerberusHeapLang.wps_of_wpt, ``) and 1084
  (`` ``CerberusHeapLang.t4_wps_of_wpt, ``), both inside `trioExports`
  (`def trioExports` at 271, closing `` ``CerberusHeapLang.evalDepth_subst] ``
  at 1103; `def axiomFreeExports` at 1111–1118). `diff <(git show
  6df8982:…/Audit.lean) <(grep -vE '^  ``CerberusHeapLang\.(wps_of_wpt|t4_wps_of_wpt),$' Audit.lean)`
  → empty: removing the two pin lines reproduces the activation file
  exactly (the record's claim, confirmed).
- Untouched, measured empty: `git diff --stat 6df8982 a994676 --
  docs/DECISIONS.md docs/KNOWN-OPEN-ITEMS.md scripts/semantics-pin.env
  cerberus-heaplang/lake-manifest.json lake-manifest.json .cerberus-ws
  cerberus-heaplang/docs/CAPABILITY_MANIFEST.md cerberus-heaplang/lakefile.toml
  cerberus-heaplang/scripts scripts cerberus-heaplang/CerberusHeapLang.lean`
  → no output.
- Park branches: see N3 (none from this slice).
- Rebase: `main` = `6df8982` is an ancestor of HEAD (`git merge-base
  --is-ancestor` → true); the branch is linear on main.

### B. Statements verbatim — CLEAN

- Charter §3 T1 code block (docstrings stripped) vs `Wpt.lean:5250–5259`
  (docstrings stripped, trailing ` := by` removed): `diff` → IDENTICAL.
  `LabelSpecT.forget`'s body is exactly
  `fun l vs ρ => iprop(∃ (m : Nat), Ls l m vs ρ)`; Lean's `#print` of the
  compiled def: `fun {GF} Ls l vs ρ => iprop(∃ m, Ls l m vs ρ)`.
- Charter §3 T2 code block vs `CorpusT4Exhibit.lean:1467–1472`: `diff` →
  IDENTICAL (modulo docstring and the trailing ` :=`).
- `t4_wps_of_wpt`'s premise lines 1467–1471 vs `t4_wpt`'s 1313–1317 with
  the name substituted: `diff` → IDENTICAL, character for character. The
  conclusions differ exactly as the charter says:
  `wpt M p (t4LsT GF M.tagDefs) emptyProcSpecT 915 (readoutPost ψT4) t4Main (f :: rest)` →
  `wps M p (LabelSpecT.forget (t4LsT GF M.tagDefs)) emptyProcSpec (readoutPost ψT4) t4Main (f :: rest)`.
- My elaboration (from `cerberus-heaplang/`, `CERB_MEM_MAX=40G
  ../scripts/capped ~/.elan/bin/lake env lean .lake/audit-scratch/audit-check.lean`,
  importing `CerberusHeapLang.CorpusT4Exhibit`; `capped` printed its env
  line, no uncapped warning, no cgroup error), verbatim:

```
@LabelSpecT.forget : {GF : BundledGFunctors} → LabelSpecT GF → LabelSpec GF
def CerberusHeapLang.LabelSpecT.forget : {GF : BundledGFunctors} → LabelSpecT GF → LabelSpec GF :=
fun {GF} Ls l vs ρ => iprop(∃ m, Ls l m vs ρ)
@wps_of_wpt : ∀ [inst : LemFuel] {hlc : HasLC} {GF : BundledGFunctors} [inst_1 : SpikeGS hlc GF] {M : MachineCtx}
  {p : Option sym} {Ls : LabelSpecT GF} (k : Nat) (Ψ : SpikeVal → EnvStack → IProp GF) (e : CoreExpr) (ρ : EnvStack),
  wpt M p Ls emptyProcSpecT k Ψ e ρ ⊢ wps M p Ls.forget emptyProcSpec Ψ e ρ
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
'CerberusHeapLang.LabelSpecT.forget' depends on axioms: [propext, Quot.sound]
'CerberusHeapLang.wps_of_wpt' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.t4_wps_of_wpt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

  Against charter §3 acceptance (a): T1 identical up to instance names
  (`inst`, `inst_1`) and field notation (`Ls.forget`) — rule 5's tolerances;
  T2 identical to the charter's quoted form (the charter's (a) text already
  gives the arrow/`HasLC.hasLC`/field-notation form). Against the record's
  quoted outputs (record :112–116 and :279–301): identical. Against the
  agent's own check logs (`.lake/codex-refinement-T{1,2}-check.log`): the
  record's blocks are byte-identical to the logs (`diff` → IDENTICAL).

### C. Axioms and pins — CLEAN

- `#print axioms` (above): both theorems exactly
  `[propext, Classical.choice, Quot.sound]`; the def is sub-trio
  (`[propext, Quot.sound]`) — a def is not pinned and the charter does not
  ask for it.
- `trioExports` entries (DERIVED: `sed -n 271,<close>p Audit.lean | grep -oE
  '``CerberusHeapLang\.[A-Za-z0-9_.'\'']+' | wc -l`): base 904 → HEAD 906;
  `sort | uniq -d` → none. Each new name occurs exactly once in the whole
  file (`grep -c` → 1 and 1). `axiomFreeExports` block base vs HEAD: `diff`
  → IDENTICAL. Gate 2's printed count at each stage (all five agent logs):
  `904` (baseline) → `905` (T1 built, T1 final) → `906` (T2 built, T2 final).

### D. Proof quality and forbidden constructs — CLEAN

- Grep of every `+` line of the range's Lean diff for
  `sorry|axiom|native_decide|bv_decide|ofReduce|set_option|#print|#eval|#check|macro|syntax|notation|elab|decide|admit|unsafe|implemented_by|extern|partial |noncomputable|opaque|private|Heartbeats|RecDepth`:
  three hits, all false positives — the word "partial" inside two
  docstrings and `M.extern` (matches `extern`). No forbidden construct.
- `wps_`/`wpt_` identifiers in the added text (DERIVED, `grep -oE
  '\b(wps|wpt)[._][A-Za-z0-9_.]*' | sort | uniq -c`):
  `2 wps_of_wpt`, `4 wps.pre`, `1 wps_unfold.to_eq`, `1 wpt_empty_call_false`,
  `1 wpt_jump_eq`, `1 wpt_step_eq`, `1 wpt_val_eq`, `1 wpt_zero_step_eq`.
  None is among the manifest's 145 rule names (`grep -oE 'N "[^"]+"'
  scripts/capability_manifest.lean | sort -u | wc -l` → 145; a grep of
  that list for `unfold|of_wpt|forget|emptyProcSpec|val_eq|jump_eq|step_eq|call_false|wps_pre|wpt_pre`
  → none). Term-level confirmation (my scratch, verbatim):

```
wps_* names in the TRANSITIVE cone of wps_of_wpt: #[CerberusHeapLang.wps_of_wpt, CerberusHeapLang.wps_unfold]
transitive cone size (all roots): 11675
```

  and `wps_of_wpt`'s DIRECT constants in our namespace are 47: the five
  equations `wpt_val_eq`, `wpt_jump_eq`, `wpt_zero_step_eq`, `wpt_step_eq`,
  `wpt_empty_call_false`, plus `wps_unfold`, `wps`, `wps.pre` (+ its
  `match_1/3/5` auxiliaries), `wpt`, `emptyProcSpec`, `emptyProcSpecT`,
  `LabelSpecT.forget`, `deliveryCost`, `toVal`, `jumpRedex?`, `callRedex?`,
  `lookupLabel`, `lookupProc`, `evalPexprs`, `ofValA`, and the structure
  types/projections/instances. `aux decls with prefix
  CerberusHeapLang.wps_of_wpt: []` — no private helpers, no generated
  auxiliaries (the record's "no private helpers" holds at the term level).
- Every lemma used is public and pre-existing at base (`git show
  6df8982:…/Wpt.lean | grep -n`): `wpt_unfold` :215, `wpt_val_eq` :220,
  `wpt_jump_eq` :225, `wpt_zero_step_eq` :238, `wpt_step_eq` :264,
  `wpt_empty_call_false` :282; `wps_unfold` Wps.lean:327. `grep -nE
  '^private .*(…)' Wpt.lean` → none private.
- The proof as read (Wpt.lean:5257–5316), clause by clause against §4:
  `induction k using Nat.strongRecOn generalizing e ρ` (the file's existing
  pattern); `rw [wps_unfold.to_eq]`; VALUE: `rw [wpt_val_eq k htv]; simp only
  [wps.pre, htv]; iintro ⟨-, H⟩; iexact H` — drops the pure `deliveryCost`
  conjunct; JUMP: `rw [wpt_jump_eq …]; simp only [wps.pre, …,
  LabelSpecT.forget]; imod H with ⟨%params, %cont, %vs, %ev0, %evs, %m, %hρ,
  %hl, %hv, -, HL⟩; imodintro; iexists params, cont, vs, ev0, evs; … iexists
  m; iexact HL` — the five existentials in the same order, `⌜1 + m ≤ k⌝`
  dropped (`-`), `m` the witness for `∃ m`; CALL: `ihave HF :=
  wpt_empty_call_false htv hjr hcr $$ H; imod HF with %hF; exact hF.elim` —
  ex falso under the fupd, exactly §4; STEP `zero`: `rw [wpt_zero_step_eq
  …]; iintro %hF; exact hF.elim`; STEP `succ m`: `rw [wpt_step_eq m …]; simp
  only [wps.pre, …]; iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ;
  cases obs with | cons o _ => exact o.elim | nil => …; simp only
  [List.nil_append]; imod H $$ %κ %ℓ %lc %sp %σ₁ %ns %obs' %nt %hsb Hσ with
  ⟨$, H⟩; imodintro; inext; iintro %r %σ₂ %eₜ %Hstep -; imod H $$ %r %σ₂ %eₜ
  %Hstep with ⟨$, H⟩; imodintro; iapply IH m (Nat.lt_succ_self m) (r.e) (r.ρ)
  $$ H` — the `List Empty` elimination (`o.elim`), the total clause
  instantiated at `obs := obs'`, the `Reducible` pure conjunct framed (`$`),
  `▷` introduced (`inext`), the credit `£ 1` dropped (the `-`), IH at `m <
  m + 1`. Exactly §4's five rows; no monotonicity lemma; nothing specific to
  `Ψ`, `M`, `p` or `Ls` (all section variables, `Ψ` an explicit parameter
  never inspected).
- No `decide`, no kernel evaluation of large terms, no `set_option`. Build
  cost, from artifacts rather than the record: `.lake/codex-refinement-T1-proof.log`
  ends `✔ [412/412] Built CerberusHeapLang.Wpt (5.1s)` /
  `Build completed successfully (412 jobs).` (a module-targeted build; the
  record's "6 seconds" is the shell wall time). The `.olean` mtimes:
  `Wpt.olean` 20:27:18; then the 40 transitive dependents of Wpt (DERIVED by
  closing the `import` graph — `TotalAdequacy`, `IntRules`, `API`, the 23
  exhibits, the smokes/examples, `ProdEntry/ProdLoop`, `Shipped`, `Audit`;
  the heavy `Soundness`/`Round`/`Step`/`Wps` are NOT dependents and were not
  rebuilt) at 20:27:59–20:28:24, with the T1-built gate log written 20:28:42
  — consistent with the record's 46 s; T2's gate rebuilt only
  `CorpusT4Exhibit` 20:32:23, `Shipped` 20:32:24, `Audit` 20:32:26 (record:
  28 s). No heartbeat pressure is plausible at these numbers.
- `LabelSpecT.forget` is a plain `def` (no attribute, no `noncomputable`,
  no `abbrev`) with exactly the charter's body.

### E. Frozen surface — CLEAN

Recomputed by a script of my own (entries split on `----`, keyed
`<kind> <name>`, compared by full text; DERIVED):

```
baseline -> T1-post: entries 5224 -> 5226; ADDED 2; REMOVED 0; CHANGED 0
  ADDED   def CerberusHeapLang.LabelSpecT.forget
  ADDED   theorem CerberusHeapLang.wps_of_wpt
T1-post -> T2-post: entries 5226 -> 5227; ADDED 1; REMOVED 0; CHANGED 0
  ADDED   theorem CerberusHeapLang.t4_wps_of_wpt
```

Baseline provenance: 5224 entries = 5219 (`…_codex-D5b-post.txt`) + 5, as
the brief predicted. Stronger: the baseline's name set minus D5b-post's is
exactly five `def`s (`tacticEmitted_frame`, `tacticEmitted_lookup`,
`tacticLabeled_main_`, `tacticStep_ctx_head_`,
`«tacticExcluded_store_eval_,_,_,_,_=>_»`), each present in
`…_codex-D7-post.txt` with identical text; no name of D5b or D7 is missing
from the baseline; no common entry's text differs (`text-changed common: 0`
against both). So the baseline IS the census of D5b ∪ D7 = main 6df8982's
Lean tree. The record's claim that the activation tree equals `2e18821`'s:
`git rev-parse 6df8982:cerberus-heaplang/CerberusHeapLang` =
`2e18821:…` = `53d0a0ecd1183b85cc43efbe37355344cb68228f` (HEAD:
`78294d1fc695bac1990d44c2a0b2711ac39169b4`); `git log 2e18821..6df8982` is
two docs-only commits.

The three snapshot files are distinct (sha256
`53598b2b…`, `639753cc…`, `7d3a4bb8…`); `sha256sum cerberus-heaplang/docs/*.txt |
uniq -d` finds one duplicate pair, both pre-existing 2026-08-31 files
(`listrev-signatures-pre` = `phase2-s4-signatures-post`) — outside the range.
Exactly three new snapshot files, none duplicated.

### F. Record accuracy — CLEAN

Every quoted block in the record was diffed against the agent's on-disk
logs (`.lake/codex-refinement-*`) AND, where possible, re-derived from the
committed files:

- Baseline gate tail (record block) vs `grep -E '^==|^ok:|^info:
  CerberusHeapLang|^Build completed|^BOUNDARY|^ALL GATES'
  codex-refinement-baseline-gate.log` → IDENTICAL; T1 final tail vs
  `…T1-final-gate.log` → IDENTICAL; T2 final tail vs `…T2-final-gate.log`
  → IDENTICAL. The intermediate `T1-built`/`T2-built` logs' tails are
  identical to their finals (same counts).
- `#check`/`#print axioms` blocks vs `T1-check.log`/`T2-check.log` →
  IDENTICAL; vs my own elaboration → identical (above).
- Snapshot `diff -u` blocks vs `T1-snapshot.diff`/`T2-snapshot.diff` →
  IDENTICAL; and vs `diff -u` RECOMPUTED from the committed files (bodies)
  → IDENTICAL; the header timestamps in the record equal the working-tree
  files' mtimes (`20:26:28.428148482`, `20:29:31.160415521`,
  `20:33:32.030687447`).
- Warning count method: `grep -cE '^warning: CerberusHeapLang[/.]'` → 33 in
  all five gate logs (baseline, T1-built, T1-final, T2-built, T2-final);
  `grep -ci uncapped` → 0, `grep -c KILLED` → 0, `grep -ci cgroup` → 0 in
  each; `^ALL GATES GREEN` once in each.
- `GATE-EXIT=0`/`WALL-SECONDS` labelled as agent reporting: correct —
  `scripts/test_unit.sh` ends `echo "ALL GATES GREEN"` and falls off to exit
  0 (`GATE FAILURE`/`exit 1` otherwise); the three `.meta` files hold
  `GATE-EXIT=0` / `WALL-SECONDS=17|28|17` matching the record.
- "no private helpers", "no partial RULE lemma is used": confirmed at the
  term level (§D). "Removing the two new pin lines … reproduces its
  activation contents exactly": confirmed (§A). "Wpt.lean 68 added lines, 0
  removed; Audit.lean 1 added line" / "CorpusT4Exhibit.lean 12 added lines,
  0 removed; Audit.lean 1 added line": `git show --numstat` confirms.
- Environment claims: `scripts/capped:26–40` skips `env.sh` when
  `CERB_PROJ` and `GIT_CONFIG_GLOBAL` are both set (the record's wording is
  exact; see N2 for the charter's); `test_unit.sh:58` uses `mktemp
  "${TMPDIR:-/tmp}/capability_manifest.XXXXXX"` (so `TMPDIR` in the worktree
  is the right move); the agent's logs carry no env banner, no uncapped
  warning.
- `.bash_logout` note: repo-side null (N6).
- Timings vs commit timestamps: baseline gate log 20:25:29 → baseline
  snapshot 20:26:28 → proof build 20:27:19 → T1-built gate 20:28:42 → T1
  check 20:28:59 → T1-post snapshot 20:29:31 → T1 final gate 20:30:15 → T1
  commit 20:30:39 → record 20:31:30 → T2-built gate 20:32:41 → T2 check
  20:33:00 → T2-post snapshot 20:33:32 → T2 final gate 20:34:27 → T2 commit
  20:35:02 → record 20:36:26 (author = committer dates; all monotone; rule
  2's "FULL gate before the baseline snapshot", rule 1's order, and rule 11's
  "delete the scratch file before the final gate" — `scratch/` is empty,
  mtime 20:33:00 — are all consistent with the artefacts).

### G. The theorem's meaning — CLEAN

- `LabelSpec GF = sym → List value → EnvStack → IProp GF` (Wps.lean:114);
  `LabelSpecT GF = sym → Nat → List value → EnvStack → IProp GF`
  (Wpt.lean:98). `LabelSpecT.forget Ls l vs ρ = ∃ m, Ls l m vs ρ` is the
  ∃-forget — the direction §4 justifies (the total JUMP clause supplies one
  `m`, Wpt.lean:163–168; `∀ m` would be underivable).
- `wps_of_wpt` says, for arbitrary `M p Ls Ψ e ρ` and every budget `k`,
  that the total judgment at the empty table entails the partial judgment
  at the forgotten label specification and the empty table — total refines
  partial at the empty table, with the same `[LemFuel]` instance on both
  sides (one binder) and the same `Ψ`. Both empty tables are `⌜False⌝`
  preconditions (Wpt.lean:112, Wps.lean:137), so the CALL clause is vacuous
  on the total side and no `ProcSpecT.forget` is needed.
- `t4_wps_of_wpt` is a pure corollary (N5); it should be documented as
  such on the shop-window surfaces at the landing.

### H. Downstream instruments — CLEAN

- `git diff 6df8982 a994676 -- cerberus-heaplang/docs/CAPABILITY_MANIFEST.md`
  → empty (byte-identical); all four gate logs after the baseline read
  `ok: capability manifest regenerated, no drift` (as the review predicted:
  Wpt is `core`; `wps_of_wpt` is not a RULE name, so T2's module gained no
  consumer row).
- `cite_check.sh`: no prose cite went stale (N1 details); the two quoted
  expected tails (README, KOI §E) did.
- Boundary check: the pattern at `scripts/boundary_check.sh:46` applied to
  the comment-stripped T2 text (`CorpusT4Exhibit.lean:1464–1475`) → no hit;
  the gate's `ok:   CorpusT4Exhibit — 0 internals mentions` and
  `BOUNDARY: 30 modules checked, 0 internals mention(s) in total, exit=0`
  are in both T2 logs.

### I. Provenance — CLEAN

The record carries seven `[AGENT]` tags (lines 15, 31, 38, 174, 256, 360,
435) on: the proof strategy (follows §4), the login-shell artefact, the
sandbox handling, the `-c rebase.autoStash=true` choice (twice), the
transitivity proof, and the completion audit. No `[USER]` tag appears in the
record (`grep -n '\[USER'` → none), so nothing is misattributed. No
statement shape was chosen by the agent: both statements are the charter's
verbatim (§B), the only agent choices being binder names (none changed —
the charter's binders were kept) and the proof. Every tally the record
derives is labelled `DERIVED`. The record uses the charter's section
structure (one section per deliverable, checks, census, gate tail, wall
time).

## Grade

**A** — a small, exactly-scoped range whose every claim (fence, statements,
axioms, pins, census, gate quotes, timings, environment) re-measures true,
with the proof matching the charter's derivation row for row and no
`wps_*` rule in its cone; the only residue is the orchestrator's own
docs-pass items (N1, N5) and three observations that force nothing.
