# Independent whole-file t1 range review

[AGENT, 2026-09-08] Fresh reviewer, separate worktree
`worker-whole-file-range-review`, at `c9215cc`. Reviewed implementation
range `7040406..c9215cc` against the accepted
[charter](2026-09-07_whole-file-t1-charter.md) and
[proposal](2026-09-07_next-demo-slice-review.md). First read AGENTS.md,
[AUDIT-BRIEF.md](AUDIT-BRIEF.md), and
[KNOWN-OPEN-ITEMS.md](KNOWN-OPEN-ITEMS.md). No source edits, provider edits,
builds, merges or pushes by this reviewer; only this report is written.

**Verdict: PASS, with three documentation Notes below.** No substantive
logical or coverage gap was found in the authorized whole-file t1 slice.
The generic machinery is reusable within its explicit startup restrictions,
the actual t1 proof consumes it, and the final statement is about the
genuine engine. The documented option-(b) frontend boundary is the accepted
scope, not a newly discovered missing proof. The Notes correct induced
prose drift; none calls for stronger trust gates or new proof machinery.

## Scope and method

Read all of `cerberus-heaplang/ARCHITECTURE.md` freshly at this revision;
reviewed the changed claims in the package/root README, WALKTHROUGH,
CLAIMS, FUEL, manifest, master-plan update, request register, known-item
dispositions, DECISIONS addition and implementation/corpus records. Read
the new generic capture/map modules, captured-library adapter, actual t1
projection and body proof, the tool code and shell wrappers, and the
changed driver/startup/audit/shipped interfaces. Checked the corresponding
pinned `Main.runPipeline`, engine file fields, startup and external-map
construction in the parent's verified `.cerberus-ws` read-only.

Independent source/snapshot measurements:

```text
STRICT CENSUS: 5227 5569 added 342 removed 0 changed 0
FROZEN: Step, Wps, Wpt, Soundness, Heap, Rules, Fragment, Lang, Round, Adequacy byte-identical to baseline
PINS: unchanged
```

The census compares each existing complete printed declaration block,
without normalizing binders or whitespace. It confirms the committed
baseline/final census, not an independent elaboration of those snapshots.
The frozen-file comparison is byte-for-byte against `git show 7040406:…`;
the pin comparison covers semantics-pin.env, lakefile.toml, Lake manifest
and lean-toolchain. The source diff retains current main's D7 shared
head-step proof bodies: its changes to the existing round induction are
the extern generalization, with the original statements reconstructed as
specializations. G3 scheduler code is absent.

## The proof chain

1. **Complete representation.** `EmittedFile.lean:40` has exactly the
   eleven fields of pinned `Core.lean:2008`. All eight top-level Fmap
   comparators are separated from data; `none`, `some Empty`, tree shape
   and stored heights remain distinct. `restore_capture` (`:94`) and
   `restore_eq_of_data_eq` (`:107`) reconstruct using the original
   comparator functions. They do not prove the frontend or quoter correct.
2. **Actual finite-map operations.** The lookup-path proof (`EmittedFile.lean:125`)
   equates the engine lookup, not a binding-list surrogate.
   `EmittedMapChecks.lean:17–278` tracks comparisons used by insertion,
   join, split, merge and union, including intermediate reference trees.
   These theorems equate operations under finite checks; they do not claim
   arbitrary malformed trees are valid or that a fuelled operation
   succeeds. `fold_eq_of_mapData_eq` (`:281`) preserves the shipped
   binding-to-set conversion and fold. These modules have no t1 dependency.
3. **Actual extern and original contracts.**
   `loop_step_frag_same_extern'`/`loop_step_frag_same_extern`
   (`DriverCollapse.lean:2554`, `:2672`) retain the context's runtime
   extern map and tie label registration at the resolved procedure.
   The public forms take `Frag` plus `evalDepth`; the internal induction
   uses `FragFuel`. `DriverDoneAtExtern` (`ProdLoop.lean:63`) and
   `wpt_driver_done_alloc_extern` (`:551`) carry that map through
   value delivery, jumps and control-preserving steps. Their old
   empty-map forms specialize the new machinery. No call protocol was
   smuggled into this single-procedure route: the table remains
   `emptyProcSpecT` and calls cannot satisfy it.
4. **Genuine startup and closed execution.** `drive_after_setup_file`
   (`ProdEntry.lean:771`) proves the real no-globals, parameterless-main
   setup prefix, with the same file and initialization state.
   `prod_run_eqJ_file` (`:950`) ties its tag reader to the file's empty
   tag table, keeps `create_extern_symmap F`, consumes delivery at that
   same file/supply, and composes genuine driver completion and finalization.
   Its conclusion is `runND (drive F.tagDefs false F args)
   (initial_driver_state sup F fs).1`, with singleton Active outcome and
   the postcondition. This is generic in file, body, supply, budget and
   postcondition; empty globals/tags and parameterless main remain premises.
5. **The actual t1 body.** `Examples/EmittedT1.lean` projects main from
   the complete retained data. `mainBody_shape` (`:221`) is an equality
   to that body, including annotations, prefixes, types, initializers and
   grouping. Its constructive `mainBody_frag` (`:281`) has no fuel
   parameter; the evaluator bound is separate (`:290`). The collector
   equation submitted via `mkAuxLemma` (`:61`) is a synchronous ordinary
   kernel reflexivity proof, not executable evaluation of a proposition.
   The runtime extern is proved to be a singleton self-binding (`:86`),
   distinct from the eleven-entry file extern table. Comparator equality
   of resolved symbols is the correct premise for environment lookup;
   it does not improperly identify descriptive symbol metadata.
6. **Library and public proof.** `EmittedStdCore.HasIntLibrary` (`:39`)
   exposes three real lookup facts. The adapter deliberately depends on
   the captured library; its reuse theorem (`:108`) requires that library
   data and the comparator checks. The complete map is retained.
   `eval_convIntInst`/`eval_convLoadedInt_spec` (`:313`, `:343`) take the
   representability branch. `convElse2`'s other branch is a pure
   `PEcall (Impl …)`, not `Eproc`; t1 supplies the range facts and needs
   no implementation-procedure rule. `EmittedT1Exhibit.mainBody_wpt`
   (`:302`) uses the existing public total rules at budget 48, owns and
   releases both cells, checks the unsequenced load/addition, and jumps
   to the proved return label. It is then launched with cold-start memory
   and allocation capacity (`:583`).
7. **Advertised result and transfer.** `certified_production`
   (`EmittedT1Exhibit.lean:623`) has all three comparator checks, original
   captured supply 36, every execution fuel at least 50, arbitrary
   filesystem/arguments, sole Active `lint 4`, unblocked, empty output.
   `_of_capture_eq` (`:647`) states data and supply equality explicitly
   for an arbitrary original file. `Shipped.lean:307` adds its shipped
   corollary; the old `t1_certified_production_shipped` contract is intact.

## Executable connection and trust

The loader (`scripts/emitted_frontend.lean:25`) follows pinned
`Main.runPipeline:874–1045` for a fresh process, one TU and no libc:
parse the same libraries before setting the TU digest, frontend from
supply zero, singleton link, then conversion. Its explicit empty-digest
reset and native digest read checks establish the intended loading
context operationally. The comparison makes no cross-frontend equality
claim about OCaml's printed Core.

`scripts/derive_file_beq.lean:32` rederives the whole reachable constructor
dependency closure before each parent. This addresses the real pinned
`CerbCtypeInstances.lean:29–35` annotation-insensitive equality and the
already embedded parent dictionaries. Pmap is rederived; primitive/container
instances are structural and receive the fresh element dictionaries.
Float is compared by observed `toBits`, consistent with quotation; the
NaN canonicalization limit is disclosed. No tool instance enters the
logic library.

The two data comparisons use different operations: the structural derived
BEq on constructor fields, and equality of quoted constructor expressions.
They share type-discovery scaffolding, not the data comparison itself.
The quoter's rendering is checked after re-elaboration. The verifier
(`scripts/inspect-emitted-file.sh:125–154`) also checks the original
comparators on the very frontend instance whose data was compared. Its
three named stdlib lookups use the same lookup construction as
`EmittedStdCore.findStdFun`; after equality to t1 data these are the
theorem's three callee keys. Thus it does not rely solely on comparator
checks from the earlier separate inspection process.

The full speedbump regenerates Cabs using the exact relative C source
path and compares bytes. The negative checks apply `main := none` and
`frontendSupply + 1` to already elaborated values and require the intended
comparisons to reject them. These are useful honest-drift tests, not
proofs of the transfer premises. The inspector's restriction to a main,
this captured stdlib and successful execution at the supplied fuel is
disclosed. Its underlying capture/quoter/comparator is reusable.

Inspected the parent's completed full-gate log at c9215cc; no reviewer
build was run because the parent owned the heavy lane. Selected lines,
verbatim from `.lake/whole-file-evidence/full-gate.log` in its worktree:

```text
info: CerberusHeapLang/Audit.lean:1152:0: CerberusHeapLang export pins: 918 trio-exact, 7 propext-exact, 7 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1152:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (6816 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1152:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (10261 constants of every kind swept, internal details included — count informational, environment-dependent)
ok: emitted-file negative check — main := none rejected by structural and quotation comparisons
ok: emitted-file negative check — frontendSupply + 1 rejected by supply comparison
BOUNDARY: 34 modules checked, 0 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
```

The seven propext-only pins and seven axiom-free pins preserve their
actual smaller cones. The exact-pin change does not enlarge the existing
trio trust bound; the exhaustive and banned sweeps still cover internal
details, including the auxiliary collector theorem. No new boundary axiom
or native proof method is introduced.

## Documentation Notes at c9215cc

- **N1, exact-category prose drift.** ARCHITECTURE `:755–757` still says
  six axiom-free pins and implies sub-trio public lemmas are all unpinned.
  CLAIMS `:28` and C11 (`:51`) describe only trio/empty categories and
  omit `Audit.propextExports`, although C19 now names propext-pinned
  reconstruction theorems. Align these lines with the actual three
  categories. This is a source/docs mismatch in descriptive prose;
  the build checks the correct exact sets.
- **N2, manifest census drift.** ARCHITECTURE `:1006–1012`, `:1037–1038`
  still says 25 consumer modules and 14 claim rows/133 names/290 spans.
  The committed manifest reports 27 consumer modules and 19 rows/203
  names/360 spans. Update or remove the stale duplicated counts; do not
  add another checking instrument. The manifest itself is current.
- **N3, scope of old generic-premise account.** ARCHITECTURE `:874–881`
  calls its list the premises of *every* generic adequacy theorem and
  then says extern is empty in every proved configuration. Its listed
  old routes retain that premise, but the new extern launcher does not.
  Restrict this prose to those routes and point to the new complete-file
  route already correctly described in §2.4. The source and principal
  whole-file claim already agree.

No known-open item is re-reported as a new finding. The broader frontend
proof, other corpus migrations, procedure/scheduler work and frozen-core
limitations remain explicitly outside this slice. This review authorizes
no merge or push. Final documentation corrections and claim-point status
belong in the implementation record.

## Final documentation confirmation at a39efb0

[AGENT, 2026-09-08] Re-read the corrected ARCHITECTURE and CLAIMS in
full at `a39efb0d347e46ad2246a3f91b21755d2915856d`, read corrected FUEL,
and reviewed the complete correction diff and affected passages of the
package README, WALKTHROUGH and KNOWN-OPEN-ITEMS. Compared the correction
range `c9215cc..a39efb0`: it changes those six documents and incorporates
this report; implementation source, tools, proof statements and pins are
unchanged.

**Final verdict: PASS. All three Notes are resolved.**

- **N1 resolved:** ARCHITECTURE `:758–764` distinguishes the three exact
  pin categories and allows public lemmas to have pinned smaller cones.
  CLAIMS `:28` and C11 (`:51`) include `propext` alone and explicitly
  name `Audit.propextExports`, matching `Audit.lean:1123`, `:1139` and
  the exact checks at `:1164–1166`.
- **N2 resolved:** ARCHITECTURE `:1010–1017` names the current consumer
  families, including `EmittedT1Exhibit` and `Examples.PartialClients`,
  and points to the generated census. Its claim/name/span account
  (`:1037–1045`) likewise defers to the manifest run. The stale duplicated
  counts are removed without adding a new checking instrument.
- **N3 resolved:** ARCHITECTURE `:880–889` limits the empty-extern
  account to the existing partial and through-calls routes, and points
  to the actual-extern allocation route for complete-file t1.

The citation repairs now point to the intended declarations and fields,
including `prodCtx` (`ProdEntry.lean:414`), the production total/partial
theorems (`:583`, `:621`), `DriverDoneCtl` (`ProdLoop.lean:631`), and
`ctlThread` (`DriverCollapse.lean:2929`). The repaired source locations
do not broaden their claims. In the complete normative architecture,
the reusable machinery's startup restrictions, the captured-library
adapter's t1-data dependency, and the executable option-(b) frontend
boundary remain explicit; no new misleading whole-file scope was found.

No substantive issue remains from this review. Adding the existing
`Audit.propextExports` declaration to C11 also changes the generated
claim-name census; the parent is regenerating that artifact and owns the
final full gate. The earlier green gate recorded above is evidence for
the unchanged implementation at `c9215cc`, not a claim that this reviewer
ran the final documentation gate. No builds, source edits, merge or push
were performed by this reviewer.
