# Whole-file t1 — landing fixes and verification

Status: landing fixes verified on `demo-whole-file-t1`; primary landing
verification is recorded below when complete. [AGENT 2026-09-08].

The independent [landing review](2026-09-08_review-whole-file-t1-landing.md)
of `7040406..d49cd3b` returned PASS WITH FIXES (A−), with one required
disclosure fix, F1. The earlier
[implementation record](2026-09-08_whole-file-t1-implementation.md) and
[validation excerpts](2026-09-08_whole-file-t1-validation.txt) remain the
proof and signature record; this follow-up changes no Lean source or pin.

[USER], verbatim in the working session:
> The review landed on your worktree. Can you make the identified fixes, then land on main?

This authorizes landing after the fixes and checks. It supersedes the
initial feature handoff's pending merge authorization; no push is authorized.

## Review disposition

- **F1 fixed.** `scripts/check-emitted-t1.sh` now prints the actual OCaml
  binary SHA-256, embedded version, binary path and runtime path on each
  run. The [fixture README](corpus-a7/README.md) records the measured
  identity, including the binary's self-reported build revision, separately
  from the sibling checkout's current HEAD and our pinned Lean semantics.
  The build was not independently reproduced. The full-gate prerequisites,
  absence behavior and unaffected `--fast` tier are stated in both READMEs
  and KOI §E. The hash is provenance, not a new pin; the existing fresh-Cabs
  byte comparison remains the relevant drift check.
- **F2 accepted as disclosed.** Supply 36 is captured pipeline data, with
  equality explicit in the transfer theorem and a negative supply check.
  The whole-file certificate does not have the old `600 ≤ sup` premise.
- **F3 addressed in the branch register; cleanup follows landing.** The
  master plan §2 identifies `worker-whole-file-compare` (`cd45c3f`),
  `worker-whole-file-docs` (`cd03831`) and
  `worker-whole-file-range-review` (`9219800`) as superseded records.
  Retain those refs for provenance; remove their clean worktrees after
  landing, without merging the comparator worker's older base.
- **F4 fixed.** The implementation record explicitly locates its ignored
  `.lake/whole-file-evidence/` paths at the feature worktree root, identifies
  the logs as ephemeral and points to committed validation excerpts.
- **F5 fixed.** KOI C5 counts unique full `warning: CerberusHeapLang/`
  lines, separating repeated demo diagnostics from dependency diagnostics.
- **F6 recorded.** The master plan keeps its 18 `600` sites and adds a
  note to recount and reconsider V1-4a when the later migrations occur.
  Adding certificates while retaining wrappers does not remove their
  premises.
- **F7 acknowledged.** No change to the positive finding: all existing
  public signatures remain intact. The proof-layer census is unchanged
  by these documentation and reporting fixes.

The package README's nearby audit summary now describes the exact
declared axiom subsets, consistent with the already-verified audit, and
enumerates the full gate's current speedbumps. The root README's build
example keeps the package `cd` in a subshell so the following gate command
runs from the root.

## Feature verification

Command, from the feature worktree root:

```bash
CERB_MEM_MAX=40G TMPDIR="$PWD/.tmp" scripts/test_unit.sh \
  > .lake/whole-file-landing-evidence/feature-gate.log 2>&1
```

Exit 0. Selected output below is verbatim (intervening build diagnostics
and per-module boundary lines omitted). The ignored log is ephemeral; this
committed excerpt is the durable record.

```text
ok: no banned proof-method references
ok: no fuel numeral (100000000/1000000/999999) outside a *_shipped corollary and no retired fuel constant (67 files scanned, comments stripped)
info: CerberusHeapLang/Audit.lean:1152:0: CerberusHeapLang export pins: 918 trio-exact, 7 propext-exact, 7 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1152:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (6816 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1152:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (10261 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (490 jobs).
ok: cerberus-heaplang build green
ok: capability manifest regenerated, no drift
ok: corpus skeleton — every transcription matches its emitted text, every plant mismatches
whole-file t1: OCaml oracle SHA-256: 7d1778bba8defb85233c4be211ab9cbe4b32dae13cf4afc9de79fae3c9302cd4
whole-file t1: OCaml oracle binary: /home/dev/projects/cerberus-lean-proj/cerberus-lean/_build/default/backend/driver/main.exe
whole-file t1: OCaml oracle runtime: /home/dev/projects/cerberus-lean-proj/cerberus-lean/_build/install/default
whole-file t1: OCaml oracle version: git-cn-pin-720-g9a7f7ad31
ok: whole-file t1 — fresh Cabs matches retained fixture
ok: emitted-file comparison — all three captured-comparator checks pass on the compared instance
ok: emitted-file negative check — main := none rejected by structural and quotation comparisons
ok: emitted-file negative check — frontendSupply + 1 rejected by supply comparison
ok: whole-file t1 — metadata, all three comparator checks and singleton return 4 checked
ok: whole-file t1 — independent structural data, quotation, supply and negative checks passed
ok: complete-file t1 comparison and negative checks
ok: import direction — 19 core modules, none imports an exhibit/example/production module
BOUNDARY: 34 modules checked, 0 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
```

DERIVED tallies from that log: 66 demo warning occurrences, 33 distinct
demo warnings (the existing Potential/Heap baseline), zero `UNCAPPED`.
Including dependency diagnostics gives 1,115 warning occurrences and 658
distinct lines; these are not the C5 demo count. All nine structural
comparison tests passed. `bash -n scripts/check-emitted-t1.sh` and
`git diff --check` passed. There is no diff from `d49cd3b` in Lean source,
lakefiles, dependency manifests or `scripts/semantics-pin.env`.

Both the feature and primary pinned-workspace checks passed, including
37 hand-written seams byte-identical to pin
`89f7e688530c6910884518811d645e4e892e4507`.

The citation speedbump ran on all eight edited documents. No new
`file:line` citations were introduced. Its remaining nonexact reports are
preexisting: the package README's manifest/semantics region citations,
KOI B18's two old Step line numbers, pinned-source ranges, and a historical
CLAUDE line-101 reference in the append-only decisions register. No
automatic historical rewrite was made.
