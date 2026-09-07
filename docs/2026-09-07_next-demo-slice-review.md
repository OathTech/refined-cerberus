# Review of the master plan and proposed next slice

[AGENT, 2026-09-07] Proposal for discussion, not a ratified charter or a
feature implementation. Reviewed main `7040406`, the revision-2 master
plan and requests register, their previous review, the known-open-items
register, and the relevant source. Review standard: [AUDIT-BRIEF.md](AUDIT-BRIEF.md).
All writes for this review are inside `refined-cerberus`, in worktrees.

**Recommendation: V1-1a, the complete-file t1 certificate.** Re-cut the G2
work onto current main and finish its executable frontend comparison.
One acceptance program, one production theorem over the shipped driver,
and one explicit account of how that theorem's file came from C. This
addresses the plan's largest current gap without changing the logic's
judgments or waiting for the scheduler work.

## Assessment of the plan

The plan's ordering is technically motivated. Its criterion-4 gap is
visible directly in `CorpusT1Exhibit.lean:806`: `t1_certified_production`
runs `prodFileLib stdlibE3 [] t1Main`. `ProdEntry.lean:680` builds that file
by replacing the library in `prodFileWith`, which ultimately inherits
`impl0 := fmapEmpty` from `prodFile` at line 81. The whole linked file is
therefore a material improvement to what the theorem says.

Keep these scope distinctions explicit when turning the plan into work:

1. V1-1 already distinguishes t1 from t4/t5/t6; give these separate
   acceptance points. G2 supplies t1 only. The other programs require
   fresh data and proofs against their actual bodies and startup state.
2. The proposed call-free tag is an interim milestone. The recorded
   disposition still includes E6 in v1; this proposal does not ratify
   the alternative boundary in master-plan section 7.1. The logical-variable
   question also remains real: `ProcSpec` at `Wps.lean:130` is indexed by
   a symbol and argument values, and `ProcSpecT` at `Wpt.lean:108` adds a
   natural-number budget, not a general ghost parameter shared by pre/post.
3. Split future V1-4c into a derived-while-rule deliverable and mechanical
   cleanup. Warning removal, dead declarations, and a new public rule have
   different acceptance criteria. Neither is needed to land t1's whole file.

One technical correction to the companion register: F-5 says that linking
the impl map makes the `Eproc _ (Impl _) _` row live on every integer
conversion. G2's actual conversion branch is a **pure `PEcall (Impl ...)`**
(`EmittedStdCore.lean:188`), distinct from the procedure row at
`CAPABILITY_MANIFEST.md:181`. Its representable-int proofs
(`eval_convIntInst`, line 313, and `eval_convLoadedInt_spec`, line 343)
take the successful range-check branch and avoid that implementation call.
The t1 proof supplies those range premises (`EmittedT1Exhibit.lean:227`,
consumed at lines 354 and 431). The file retains the implementation map;
this does not require adding a new procedure-call rule for t1. F-5 should
describe out-of-range pure conversion support separately from `Eproc`.

This is a correction to a future-dependency claim, not a soundness defect.
The review does not treat the already registered A7, procedure-index, or
two-adequacy-route limitations as new findings.

## Evidence for the recommendation

References to G2 below are at commit `5bfe99288faafd74356ddc804f2b4c92026bca8d`,
the end of `3aac95d..5bfe992`, before the parked branch's scheduler changes.
For example, inspect a source with
`git show 5bfe992:cerberus-heaplang/CerberusHeapLang/EmittedT1Exhibit.lean`.
The isolated source worktree is `worktrees/review-g2-source`.

| Assumption | Evidence and limit |
|---|---|
| A complete-file t1 theorem already exists. | G2 `EmittedT1Exhibit.lean:605`, `CorpusA7.T1.certified_production`, concludes a singleton active result of `CerbND.runND (_root_.drive F.tagDefs false F args) ((initial_driver_state frontendSupply F fs).1)`, with value `lint 4`, no blocking, and empty output. Here `F` is `restoredFile cmp`. This is source inspection plus a fresh capped build, not merely the old branch's claimed green status. |
| It preserves the file rather than only the main body. | G2 `EmittedFile.lean:40` defines data for all eleven fields, including exact optional map trees; the eight comparator functions are separate parameters. `restore_capture` and `restore_eq_of_data_eq` prove reconstruction with the original comparators. The 42,841-line `Examples/EmittedT1Data.lean` is generated data. |
| The comparator assumptions have an actual passing instance. | The theorem requires `intLibraryCheck`, `mainLookupCheck`, and `labelUnionCheck`. The fresh inspector run at fuel 50 passes all three using the frontend's captured comparators. The checks have kernel-proved transfer lemmas in `EmittedFile`, `EmittedMapChecks`, `EmittedStdCore`, and `Examples/EmittedT1`. This executable instance check does not turn the frontend into a kernel theorem. |
| The full library and implementation map are retained. | Fresh inspection reports 110 stdlib entries, 6 impl entries, 11 function and file-extern entries, zero globals and tag definitions, frontend supply 36, and initialization supply 37. The runtime extern map used by the proof is separately proved equal to `create_extern_symmap (restoredFile cmp)` (`Examples/EmittedT1.lean:89`); its singleton shape should not be confused with the file's eleven-entry extern table. |
| The theorem does not need general C calls. | G2 changes neither `Step`, `Wps`, `Wpt`, `Soundness`, `Heap`, nor `Rules` relative to its base `520654f`. It generalizes delivery/startup to retain the runtime extern map in `DriverCollapse`, `ProdLoop`, and `ProdEntry`, and proves the actual body's membership and public total derivation. The G3 scheduler work is later in git history. |
| The fixture is reproducible from the C source available here. | Re-running the documented read-only OCaml `--nolibc --cabs-json docs/corpus-e0/t1.c` command produces a byte-identical Cabs fixture. Its SHA-256 is `e89a6a7bbff9cc30a9203010ff8c01beb5b496a0c9fad2ac8c1a6cd416b69134`. Feeding this fresh output through the pinned Lean frontend passes the retained-data round trip at fuel 50 and executes to `Specified(4)`. This is evidence for this program and these producer artifacts, not general cross-frontend equivalence. |
| The loader follows the relevant production path. | Compared G2 `scripts/emitted_frontend.lean:27` with pinned `Main.lean:874–1045`: load std.core and the gcc implementation, set the TU digest, call `frontendTU` at supply zero, link the singleton file list, then `convert_file`. The production path passes the resulting supply/file into initialization and `drive`. This comparison applies to a fresh process, one TU, and no libc. It is a source-level correspondence check, not a proof about IO. |
| No provider source change is needed for the demonstrated result. | The fresh isolated build and inspector use the existing `89f7e688530c6910884518811d645e4e892e4507` pin. Workspace verification passes all 37 hand-written seams and the generated-source sync stamp. No edits to the sibling semantics or Lem repositories were made. |
| Landing it on main requires adaptation. | A non-mutating `git apply --check` of the G2 Lean delta onto `7040406` fails at `API.lean`, `Audit.lean`, `DriverCollapse.lean`, and `ProdLoop.lean`. The old checkpoint builds; the re-cut onto current main has not been implemented or proved green in this review. |

## Proposed work contract

The user's follow-up asks whether this builds generic machinery as well as
certifying t1. **Yes: reusable interfaces are part of the deliverable.**
Much of the reference implementation already has the required generality;
the slice lands and completes it against current main.

| Reusable output | Generality and evidence in G2 |
|---|---|
| `EmittedFile.Data`, capture/restore, and reconstruction theorems | Quantified over an arbitrary engine `file core_run_annotation`; independent of t1 and its body. |
| `EmittedFile` lookup checks and `EmittedMapChecks` operation checks | Parameterized by key/value types, comparators, and finite map trees; correctness is about the shipped map operations, not a particular program. |
| `DriverDoneAtExtern`, `wpt_driver_done_alloc_extern`, and `prod_run_eqJ_file` | Parameterized by context/file, program, postcondition, and budget under their stated fragment, startup, and resource premises. The closed file theorem retains empty globals/tag definitions and parameterless main. |
| Loader and quoter | Take an input file and runtime context; the reusable capture path is separate from t1's fixture-specific inspection obligations. |

Require these interfaces to have no hard-coded t1 data or result. The old
empty-extern delivery theorem should remain a specialization of the new
general theorem (already the shape of G2 `ProdLoop.lean:491`), and the old
library-file startup theorem should specialize the new file theorem
(`ProdEntry.lean`, `drive_after_setup_lib`). Existing clients thereby test
compatibility while t1 consumes the newly supported whole-file case.

The generated t1 data, its body derivation, and its concrete checks are the
program-specific component. `EmittedStdCore.HasIntLibrary` is a reusable
lookup contract, but its declaration data comes from the captured library;
it is not arbitrary-library correctness. G2's
`hasIntLibrary_of_stdlib_data_eq` makes the intended reuse explicit: another
file supplies the same library data and passing comparator checks. t4/t5/t6
can reuse these interfaces while supplying their own files and body proofs.

**Acceptance program:** `docs/corpus-e0/t1.c`:

```c
int main(void) { int x = 3; int y = x + 1; return y; }
```

**Deliverable:** the advertised t1 result drives the captured complete
post-link, post-conversion file through the pinned engine, with the same
observable conclusion as G2: value 4, a singleton active outcome, no
blocking, and empty output for every execution fuel at least the sufficient
bound. The file has empty globals/tag definitions and a parameterless main.
The frontend capture uses a documented fixed fuel; the theorem quantifies
the execution fuel for that captured file. It does not quantify over arbitrary
frontend runs.

Use the already recorded option-(b) boundary: machine-quoted data plus an
executable comparison. Retain `certified_production_of_capture_eq` (G2
`EmittedT1Exhibit.lean:629`) to state precisely the premises for transfer to
an original file. Its `hdata` equality and comparator hypotheses are not
silently discharged by an executable test. The loader/quoter belong in the
account of trusted production of the artifact; `restore_capture` only proves
capture/restoration, not the quoter or frontend correct. Keep option (a),
the elaborator in the theorem's referent, recorded as a later target.

Implementation scope:

- Re-cut the six G2 support/client modules (`EmittedFile`, `EmittedMapChecks`,
  `EmittedStdCore`, `EmittedT1Exhibit`, `Examples/EmittedT1`, and
  `Examples/EmittedT1Data`) and the necessary `EnvLaws`, `DriverCollapse`,
  `ProdLoop`, and `ProdEntry` extensions. Preserve current main's repairs.
  Update API/root imports, exact audit pins, module classification, the
  relevant shipped corollary, and the small set of affected claim surfaces.
- Integrate the positive data/supply and comparator checks into the full
  test run as a speedbump. Connect it to reproducible Cabs generation from
  `t1.c`, so the result is not only a check against a stale JSON fixture.
  Keep source paths stable: locations are part of the captured data.
- Add an independent structural comparison on `EmittedFile.Data`, alongside
  quotation comparison. It must inspect tree shape/heights and annotations.
  Existing `Fmap` equality compares binding lists (`LemLib.lean:1174`) and
  is insufficient for this exact-data claim. Inspect leaf instances as part
  of implementation; if floating values are supported, match the quoter's
  explicit bit representation. Do not claim arbitrary-file equality proved.
- Include a small negative check: a changed retained main field must be
  rejected at the data comparison. Record the loader/quoter boundary and
  `reference_main_labels`'s `mkAuxLemma` proof construction in ARCHITECTURE;
  the latter submits an equality proof to the kernel and adds no native
  reduction axiom.
- Advertise the complete-file theorem as the t1 certificate. My proposed
  wrapper disposition is to retain the older `CorpusT1Exhibit` proof as an
  explicitly named regression for this slice, with the Q7 disposition
  recorded in the charter. It must not remain the advertised genuine-file
  evidence. Update A7 as closed for t1 in option-(b)'s sense and still open
  for the other corpus files and option (a).

The frontend identity question R-4 is an entry checkpoint, as the master
plan requires. Proposed answer for this slice: the file comes from the
**pinned Lean frontend consuming OCaml Cabs**, with its linked std.core and
gcc implementation. Record the local path comparison above and settle that
referent before implementation. Do not assume equality with OCaml's printed
Core, or advertise such equality without a provider guarantee. No new
structured-dump API is technically required for the demonstrated t1 route;
the existing loader accesses the in-memory file directly. If the intended
referent must instead be the OCaml elaborator's exact Core file, R-4 needs
an answer before this certificate can satisfy that intent.

Explicit exclusions: t4/t5/t6 migration, `seq_rmw`, C calls, scheduler
changes, kill adequacy, procedure logical variables, coupling extraction,
and a semantics re-pin. Broad freshness/fuel-floor restatement stays with
V1-4a; record the captured supply 36 and sufficient execution bound 50
honestly. Naming a literal is not deriving it.

## Acceptance and stopping points

The scope is medium: one externally visible capability with existing proof
material, but several startup/driver lemmas and a sizeable generated data
artifact. The plan's 1–2 days is a planning estimate, not a measured rebase
cost. The four apply-check conflicts are concrete work still to do.

At the feature claim point require a capped full build on the re-cut
worktree, exact axiom checks, the fresh frontend comparison, a rejected
perturbed-data check, and an accurate signature delta. The old wrapper and
existing clients must still satisfy their stated contracts. Follow with the
repository's independent range review and explicit merge sign-off; this
review is not that future implementation audit.

If the re-cut requires changing the frozen judgments/mirror, adopting G3,
changing the semantics pin, or replacing a proof by native computation,
stop and report the precise dependency instead of expanding the slice.

## Validation performed for this proposal

The review branch is `review-next-demo-slice`, based on main `7040406`.
The separate detached worktree `review-g2-source` contains unchanged G2
source at `5bfe992`. Its package/dependency build caches were copied from
the parked worktree, then the semantics were verified and the full gate
was independently run. The build rebuilt G2 modules against that source.
This validates the reference checkpoint, not an unimplemented merge.

Commands and selected verbatim results are in the companion
[validation record](2026-09-07_next-demo-slice-validation.txt).
No feature source, dependency pin, main branch, or external repository was
changed by this review.
