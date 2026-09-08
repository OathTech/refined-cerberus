# Whole-file t1 implementation record

Status: COMPLETE on `demo-whole-file-t1`, 2026-09-08; no merge or push authorized.
Charter: [whole-file t1](2026-09-07_whole-file-t1-charter.md).
Baseline main `7040406`; proposal `969281f`; charter/baseline `5bcbdd1`.

Evidence-path convention: every `.lake/whole-file-evidence/…` path in this
record is relative to the **feature worktree root**, not its
`cerberus-heaplang/` package directory. Ignored logs and generated reuse
scratch are ephemeral; the committed
[validation excerpts](2026-09-08_whole-file-t1-validation.txt) are the durable
record. Landing-review fixes and merge authorization are recorded separately
in [the landing record](2026-09-08_whole-file-t1-landing.md); authorization
statements below describe the initial feature handoff.

## Phase A — proof port

Re-cut G2 `520654f..5bfe992` onto current main. No G3 scheduler work,
provider edits, dependency changes, or edits to the frozen proof core.
The current driver-step proof body retains D7's shared head derivations.
The generalized rounds and allocation launcher use syntactic `Frag` with
explicit `evalDepth`; internal induction helpers use `FragFuel`. Existing
empty-extern contracts specialize the generalized implementation.

The complete-file client has fuel-independent `mainBody_frag` and separate
`mainBody_evalDepth`. Its memory-value witnesses are local, and its tuple
update uses the existing generic `update_env_tuple2_mixed`; it needs no
import of the legacy t1 wrapper exhibit.

Validation, 2026-09-08, from this worktree (all Lean commands capped):

```sh
CERB_MEM_MAX=40G TMPDIR="$PWD/.tmp" scripts/test_unit.sh --fast
```

Verbatim verdict excerpts (ignored log `.lake/whole-file-evidence/phase-a-fast.log`):

```text
info: CerberusHeapLang/Audit.lean:1137:0: CerberusHeapLang export pins: 917 trio-exact, 6 axiom-free-exact
Build completed successfully (490 jobs).
ok: cerberus-heaplang build green
FAST-GATE GREEN (gates 1-2 only — not a claim-point result; say fast-gate in the commit)
```

This is an intermediate build result. Full frontend checks, additional
representation-proof pins, claim surfaces, and fresh range review follow.

## Phase B — integration and verification plan

Comparator worker commits `7c36b18` and `cd45c3f` supply the independent
constructor comparison and the capture/inspection speedbump. The former was
cherry-picked as `4920268`; the latter's two scripts were extracted because
its branch already contained the old G2 wrapper. The unchanged G2
loader/quoter/inspector and retained Cabs were adopted explicitly from
`5bfe992`. Parent verification follows below; worker success is not the
claim-point result.

The shipped interface is an additive
`CorpusA7.T1.certified_production_shipped`. The actual existing name is
`t1_certified_production_shipped` (the charter abbreviated it as
`t1_shipped`); its old wrapper contract is preserved and labelled regression,
so no replacement alias or changed existing statement is needed.
The corpus table is a text/transcription regression table, not a certificate
name table: its shape and entries stay intact, with its t1 role clarified.

The representation audit now asserts seven exact `[propext]` cones and the
axiom-free fold transfer, as measured by `#print axioms`. These are subsets
of the existing trust bound, not new boundary axioms. The new execution
corollary is pinned separately. The exhaustive and banned-axiom sweeps
remain unchanged.

Parent integrated fast gate, 2026-09-08, exited 0. Verbatim verdict excerpts
from `.lake/whole-file-evidence/phase-b-fast.log`:

```text
info: CerberusHeapLang/Audit.lean:1152:0: CerberusHeapLang export pins: 918 trio-exact, 7 propext-exact, 7 axiom-free-exact
Build completed successfully (490 jobs).
ok: cerberus-heaplang build green
FAST-GATE GREEN (gates 1-2 only — not a claim-point result; say fast-gate in the commit)
```

The parent independently ran `CERB_MEM_MAX=40G scripts/check-emitted-t1.sh`
after integration; exit 0. Verbatim result lines:

```text
emitted-file data round-trip: independent structural data, quotation and supply match
ok: emitted-file comparison — all three captured-comparator checks pass on the compared instance
ok: emitted-file negative check — main := none rejected by structural and quotation comparisons
ok: emitted-file negative check — frontendSupply + 1 rejected by supply comparison
ok: whole-file t1 — metadata, all three comparator checks and singleton return 4 checked
ok: whole-file t1 — independent structural data, quotation, supply and negative checks passed
```

All nine structural regressions also passed: reflexivity, changed main,
the provider equality's ignored nested annotation, that annotation retained
through its enclosing constructors, map height, absent versus present-empty
map, Float signed zero, NaN reflexivity, and adjacent finite mantissa bits.
The comparator uses observed `Float.toBits`; this runtime canonicalizes the
NaN payloads produced by `Float.ofBits`, so no payload-retention claim is made.

A separate reuse experiment generated fresh Cabs for
`docs/corpus-e0/t5_ifelse.c` with the same read-only OCaml driver and ran:

```sh
CERB_MEM_MAX=40G scripts/inspect-emitted-file.sh \
  .lake/whole-file-evidence/reuse/t5.cabs.json \
  .lake/whole-file-evidence/reuse/t5.json 1000 \
  .lake/whole-file-evidence/reuse/T5Data.lean CerberusHeapLang.CaptureReuseT5
```

Exit 0: generated data elaborated and passed independent structural,
quotation, supply, and same-instance comparator checks. The diagnostic
report observed frontend supply 47, startup supply 48, and the singleton
Active `Specified(1)` with empty trace/output, unblocked. This exercises
reuse of the tool with a different program and namespace. It adds no t5
whole-file theorem; generated scratch remains ignored.

## Signature and scope comparison

The capped `scripts/signature_snapshot.lean` ran against the green
baseline and final proof source. Snapshots are
`cerberus-heaplang/docs/2026-09-08_whole-file-{baseline,final}.txt`; detailed
name census: `2026-09-08_whole-file-signature-census.txt` beside them.

DERIVED: 5,227 baseline declarations, 5,569 final; **342 added, zero removed,
zero changed**. Besides the repository census, a strict comparison of every
existing complete printed block (without binder or whitespace normalization)
also finds zero changed blocks. Thus the original wrapper, old launchers,
public fragment boundaries and other program contracts are preserved.
The snapshot excludes internal-detail names; the axiom sweep includes them.

The additions split by namespace/role (DERIVED, names in the census):

| role | additions |
|---|---:|
| generic capture and finite-map machinery | 83 |
| generic extern/driver support | 20 |
| captured-library adapter | 77 |
| t1 data, body, proof and shipped consumer | 159 |
| exact-axiom audit category | 1 |
| dependency equation lemmas realized in the package | 2 |

The last two are `Pmap.mergeGo.eq_def` and `Pmap.split.eq_def`; no provider
file changed. The frozen files (`Step`, `Wps`, `Wpt`, `Soundness`, `Heap`,
`Rules`, `Fragment`), dependency pins and other program proofs have no diff
from main `7040406`. Only the old corpus table's explanatory comment changes.

## Phase C — claims and independent review

Claim documents adopted from worker `2f3f677` as `e904b9c`, including the
R-4 bounded producer disposition and the F-5 distinction between the pure
Impl fallback and the manifest's procedure call. The full-file certificate
uses representable integers, so it needs no new Impl procedure rule.
A7 is partial: option (b) for t1 is the claim; other corpus files and the
elaborator-in-statement target remain open. Full gate and fresh range-review
verdicts follow at completion.


The full claim gate passed at `c9215cc`, then passed again after the
review-note/citation corrections at `a39efb0` and manifest regeneration.
Both runs were capped at 40G. Final verbatim verdict excerpts are retained
in [validation](2026-09-08_whole-file-t1-validation.txt); full ignored logs
are `.lake/whole-file-evidence/{full-gate,final-gate}.log`. The gate reports
918 trio-exact, 7 propext-exact and 7 axiom-free-exact pins, with no banned
axiom in any package constant's cone. The regenerated manifest has 19 claim
rows, 204 theorem-cell names and 362 all-cell spans, 27 consumer modules and
zero red rows; import direction and all 34 boundary-checked modules pass.
The 33 distinct package warning lines are identical to baseline (66 lines
printed because the inspector's dependency build replays the same warnings).
No invocation reported UNCAPPED.

The [fresh range review](2026-09-08_review-whole-file-t1-range.md) at
`7040406..c9215cc` is PASS, with no substantive logical or coverage gap.
Its three Notes concern exact-category prose, stale manifest counts and
the scope of old empty-extern routes. All three are corrected by `a39efb0`:
three exact pin categories are explicit, current counts come from the
manifest, and the old-route premise account points to the new extern route.
The additional C11 audit-category reference is checked by the regenerated
manifest and the final full gate. No Lean source changed after the strict
signature snapshot.

Citation speedbumps were run on all nine edited claim documents, followed
by targeted reference repairs against current source and a parent rerun.
All missing-file flags in the edited README/FUEL account were abbreviated
LemLib paths, now resolved through the package path. Remaining nonexact
references are historical/preexisting drift (KOI C18) or explicit ranges;
the changed DriverDoneCtl hypothesis-range endpoints were checked by hand.
No broad citation rewrite or new gate was introduced.


The fresh reviewer's final confirmation (`9219800`, report-only) re-reads
the corrected ARCHITECTURE and CLAIMS and checks the remaining reference
repairs at `a39efb0`: **PASS, all N1–N3 resolved, no substantive issue**.
The final parent manifest/gate results above discharge the validation left
to the parent in that report. The charter is complete. The primary checkout
is clean on main `7040406`; all work is committed in the feature worktree.
No merge or push was performed, and neither is authorized by this handoff.
