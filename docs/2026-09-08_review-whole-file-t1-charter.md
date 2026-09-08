# Fresh review of the whole-file t1 charter

[AGENT, 2026-09-08] Independent pre-launch review against
[AUDIT-BRIEF.md](AUDIT-BRIEF.md), after reading AGENTS.md,
[KNOWN-OPEN-ITEMS.md](KNOWN-OPEN-ITEMS.md), the accepted
[proposal](2026-09-07_next-demo-slice-review.md), and the
[charter](2026-09-07_whole-file-t1-charter.md). Main baseline `7040406`;
reference G2 `5bfe992` in `worktrees/review-g2-source`.
This review inspected source and history only. No Lean builds or source
edits were run; the orchestrator owns the heavy lane. The sole write is
this review record. It is a charter review, not the future implementation
range audit or permission to merge.

**Verdict: PASS for launch.** The proposed slice is feasible and
appropriately bounded. During review the orchestrator corrected C1 and
made N1/N2 explicit in the charter; the reviewer re-read those edits and
verified their disposition. The two implementation constraints below make
existing requirements concrete. Neither requires a scope expansion or
another user approval. No new soundness defect was found in the inspected
reference chain; existing disclosed boundaries are not re-raised as
findings.

## C1 — distinguish generic machinery from captured-library support

Required result 2 initially said “No generic module depends on t1's data or result.”
The planned G2 `EmittedStdCore` module imports `Examples.EmittedT1Data`
at line 4. Its `findStdFun` reads `CorpusA7.T1.data.stdlib` at line 18;
`intLibraryCheck` checks precisely that tree at lines 65–68. Its
`HasIntLibrary` contract is reusable for another file, but the declaration
data and associated comparison are fixed to the captured library.
`hasIntLibrary_of_stdlib_data_eq` at line 108 states this restriction
directly.

The accepted proposal already discloses this distinction. The charter's
unqualified wording should do so too: prohibit t1 dependencies in the
generic capture/map/driver machinery, and describe `EmittedStdCore` as
support for this captured standard library, reusable under the same
library-data/lookup premises. Factoring a separate library artifact is
another possible implementation, but is not needed to honor the accepted
scope. Do not claim arbitrary-library correctness merely because the file
argument is quantified.

Disposition: corrected in required result 2. The fixture-independent
machinery is named explicitly; the separate `EmittedStdCore` adapter's
captured-library-data restriction is disclosed.

## Concrete implementation constraints

**N1 — structural comparison must bypass annotation-insensitive ctype
equality throughout its dependencies.** The charter already requires
annotation preservation; this is evidence of a specific trap, beyond
the Fmap binding-list equality identified in the proposal.
Pinned `generated/CerbCtypeInstances.lean:29–35` overrides both `ctype`
and `ctype_` BEq with `ctypeEqual`, which deliberately ignores type
annotations. `CerbMem.lean:208–240` and generated Core value comparisons
contain nested comparisons of these types. Merely deriving BEq for the
top-level Data or installing a late local leaf override can retain an
existing parent's old dictionary. Derive the constructor dependency
closure before its parents, or use a separate structural comparison
class. Preserve every Pmap Node argument, including its stored height;
for Float use the quoter's bit representation. A small nested-type
annotation example is a useful focused check of this actual failure mode.
No arbitrary-file equality theorem or certification framework is needed.
Disposition: the charter now explicitly requires dependency-closure
comparison and identifies the existing ctype override.

**N2 — re-cut against main's R2 interface, not G2's former fragment
interface.** At baseline, `ProdLoop.lean:390` has the `FragFuel` launcher
proof device and `:444` the public launcher with syntactic `Frag` and
separate `evalDepth` premises for the body and labels. G2's corresponding
new extern launcher at `:448` predates that split. Its extern-capable
round/launcher and t1 membership proofs therefore need the same adaptation;
a wholesale G2 file replacement would lose this current-main repair.
The ordinary old signatures must remain unchanged, and the new public
interfaces should follow their R2 shape. Keep D7's shared `step_ctx_head`
proofs while introducing the extern parameter. This is work inside the
listed files; no frozen judgment or provider change is implied.
Disposition: Phase A now explicitly preserves R2's public interfaces,
keeps the fuelled proof devices separate, and requires fuel-free t1
membership.

## Why the principal technical assumptions hold

The reference capture/reconstruction layer is genuinely generic.
`EmittedFile.Data` retains all eleven engine-file fields, distinguishing
empty maps from comparator-bearing maps with empty trees. Its
`restore_capture` and `restore_eq_of_data_eq` proofs reconstruct using
the original comparators. `EmittedFile` and `EmittedMapChecks` contain
no t1 reference. Their finite checks prove facts about the actual
lookup/union operations rather than assuming a globally canonical order.

The generic execution extension has the required statement shape.
G2 `ProdEntry.lean:950`, `prod_run_eqJ_file`, quantifies the complete
file, program, supply, postcondition and budget, retains
`create_extern_symmap F`, and concludes a singleton result of genuine
`runND (drive F.tagDefs false F args)` from `initial_driver_state`.
Empty globals/tag definitions and parameterless main are explicit
premises. `drive_after_setup_lib` and `prod_run_eqJ_lib1` specialize
the generic file lemmas. `ProdLoop` retains the empty-extern launcher
as a specialization of the new extern form.

G2 `EmittedT1Exhibit.lean:605` is the promised consumer: execution fuel
at least 50, three explicit comparator checks, captured supply 36,
result `lint 4`, a singleton active outcome, unblocked, and empty output.
Its `mainBody_driver_done` supplies the public total-logic launcher.
The transfer result at `:629` keeps capture equality and supply equality
as hypotheses. The representable-int conversion proof in
`EmittedStdCore.lean:313–366` selects the successful range branch;
retaining the implementation map does not make an implementation
procedure call necessary for t1. The proposal's F-5 register correction
therefore belongs in the listed documentation integration.

The selected frontend boundary is accurate for the bounded loading path.
Compared G2 `scripts/emitted_frontend.lean:27–55` with pinned
`Main.lean:874–1045`: load std.core and the gcc implementation, set the
TU digest, run `frontendTU` from supply zero, link the singleton file,
and convert it before initialization. The loader explicitly establishes
the fresh-process empty digest before loading the libraries. This supports
the stated one-TU/no-libc referent; it does not prove IO correspondence or
equality with OCaml's printed Core. The fresh Cabs, data, supply and
comparator checks are the declared executable boundary, not Lean proofs
of the transfer theorem's hypotheses.

The integration fence includes the advertised certificate, shipped
corollary, old wrapper contract, API/audit pins, corpus metadata and claim
surfaces. The A7 disposition remains partial as required. Keeping the
old wrapper as an explicitly named regression, recording actual axiom
cones, checking signature changes, and requiring the final range review
provide an adequate acceptance point without taking G3/G4, changing the
semantics pin, or migrating the other corpus programs.
