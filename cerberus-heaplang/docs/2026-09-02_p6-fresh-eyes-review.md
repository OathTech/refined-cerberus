# Fresh-eyes review of README.md + docs/WALKTHROUGH.md (P6)

Reviewer roleplay: a PL researcher who knows separation logic and Iris,
has heard of Cerberus, and has never seen this project. Inputs: the two
front documents ONLY, then a read-only spot-check of the Lean tree under
`CerberusHeapLang/` and the pinned dependency at `../.cerberus-ws`.
Nothing under `docs/2026-*` or `../docs/DECISIONS.md` was opened. No
build was run; every "VERIFIED" below is a textual match of statements,
not a re-elaboration. Tree at commit `1320c7d` ("alloc arc P6 CLOSED").

All Lean quotes are verbatim from the checkout with `file:line`.
Document quotes give `README:line` / `WALKTHROUGH:line`.

---

## 1. What has been proved, in my own words

For a fragment of Cerberus Core — `store`/`load`/`create`, strong and
wildcard-weak sequencing, `if`, value-scrutinee `case`, `save`/`run`
labels, the `PtrEq` memop, `PEsym`/`PEval`/arith/`array_shift` operands —
a separation logic (an iris-lean `WP` plus two label-context judgments,
partial `wps` and total `wpt`) has been built over a hand-written mirror
`Step` of the engine's small step. The mirror is certified against the
real engine: `engine_step_matchU` says that wherever `Step` steps on a
`Frag` program, one round of the engine's own `step_ctx` followed by the
sequential driver's request discharge yields exactly that step. Iris
adequacy then produces Iris-free facts about `driveU` (the iterated
round): the engine never `.killed`s (no UB, no error kill), never goes
`.stuck` (no refusal), and at `.done v σ'` the final memory satisfies a
footprint postcondition — that is `MemTripleU`, reached by
`project_triple`. The total judgment gives unconditional `.done`
equations at a budget. A separate collapse proves that, for closed
programs, the shipped pipeline `runND (drive …) (initial_driver_state …)`
IS that singleton execution. What I must trust: the Lean kernel plus
`propext`/`Classical.choice`/`Quot.sound`; that cerberus-lean's
generated definitions (`step_ctx`, `storeM`/`loadM`/`allocateObject`,
the driver) are "Cerberus" (this is only differentially tested against
the OCaml oracle); that the package's few readout predicates
(`driveU`/`dischargeStep`, `Sat`/`CellCoh`, `SeedChain`) mean what the
docs say; and that the authored Core terms are the programs I care
about. iris-lean is checked, not trusted, for the exports. Fuel
exhaustion (`.more`) is unconstrained; `kill`/free, calls, `Eunseq`,
concurrency and the C frontend are out.

Where the documents misled me (both corrected only by reading the tree):
(i) README:79-80 "ANY Iris triple with a concrete-map precondition"
made me believe allocating clients also project to `MemTripleU`; they do
not (Finding H-1). (ii) README:105-108 promised that every hypothesis
beyond footprint + fuel is listed per exhibit; `hlib :
isLibraryLocation loc = false` and the tied label map are not
(Finding M-1). Everything else in the paragraph above I got right from
the two documents alone.

## 2. The two trust claims

As I understood them (README:130-148, WALKTHROUGH:254-264):

1. **Closed-program exports are Iris-free statements** whose referents
   are engine functions (`step_ctx` + driver discharge in the drive
   lane; `runND ∘ Driver.drive ∘ initial_driver_state` in the
   production lane) plus a handful of pure readout predicates. Iris
   appears only inside their proof terms, and `Audit.lean` pins each
   export's axiom cone to the classical trio. So iris-lean is
   *checked*, not trusted, for these.
2. **The reusable rules are Iris statements** (`pointsToCell`,
   `cellOwn`, `allocCap`, `wps`/`wpt`, …). To *use* the logic I must
   read and understand these definitions — a specification idiom, not
   an axiom set.

The distinction is made clearly and repeated in both documents. One
honest wrinkle the docs themselves flag (README:144-146,
WALKTHROUGH:90-98): `project_triple`'s post is a `∀ ψ : Prop, (… ⊢
⌜ψ⌝) → ψ` obligation mentioning `CohG`, `metaInterp`, `byteInterp` and
`cellOwn` — Iris vocabulary does survive in that one export's
statement, discharged by the `*_consequence` lemmas. Spot-check: the
`*_certified` statements I read (`list_reverse_certified`,
`ListRevExhibit.lean:1455-1480`; `fib_certified_total`,
`FibExhibit.lean:623-628`; `exhibitA_prod`, `ProdExhibit.lean:245-254`)
contain no Iris beyond `Iris.Std.PartialMap` (the finite-map library),
exactly as claimed at WALKTHROUGH:404-407.

## 3. The statement shape

Found at README:74-75 and WALKTHROUGH:29-31 (`s |= P && core_exec(prog,
s) ~~> term ==> term = some(s') && s' |= Q`). The realizing theorem is
`project_triple` (Adequacy.lean:1242), whose conclusion is `MemTripleU`
(Adequacy.lean:1201-1211). I matched the symbol table README:83-90
against the definition: `Sat M.tagDefs σ (union P R)` is `s |= P` with
the frame built in; `driveU M aids n (M.thread e ρ) σ` is `core_exec`;
the two `≠ .killed r` / `≠ .stuck` conjuncts plus the `.done v σ' →
post R v σ'` conjunct are `term = some(s') ∧ s' |= Q`; `.more` is
unconstrained. This is clear and correct.

Exhibit instantiating it: `list_reverse_certified`
(ListRevExhibit.lean:1455-1480) — it is literally the `MemTripleU`
shape unfolded at the `driveJ` profile, with `post` = "∃ p' Q, v = ptrVal
p' ∧ SeedChain Q p' ns.reverse ∧ (dom Q = dom m₀) ∧ Q ##ₘ R ∧ Sat
fmapEmpty σ' (union Q R)". The cells-shaped instance `SemTripleU`
(Adequacy.lean:1110-1121) and its `rfl`-bridge `SemTripleU_iff_Mem`
(Adequacy.lean:1216) are also as described. Note that no exhibit is
stated *as* a `MemTripleU`/`SemTripleU` value except `exhibitA/B/C_
semantic` (`SemTriple`, e.g. Exhibit.lean:369-373); the loop exhibits
unfold the shape by hand. That is fine but worth one sentence (Note
N-4).

## 4. Spot-check table

| # | Claim (doc location) | Theorem / def | What the source says | Result |
|---|---|---|---|---|
| 1 | `MemTripleU` quoted verbatim (WALKTHROUGH:34-46) | `MemTripleU` | Adequacy.lean:1201-1211 — identical text | VERIFIED |
| 2 | `project_triple` quoted verbatim (WALKTHROUGH:68-83); "ANY Iris triple with a concrete-map precondition" (README:79-80) | `project_triple` | Adequacy.lean:1242-1256 identical. Precondition is `[∗map] i ↦ c ∈ P, cellOwn … (.own 1) c` ONLY — no `allocCap`; no `project_triple_alloc` exists (grep) | VERIFIED text / MISMATCH on "ANY" (H-1) |
| 3 | `DriveResult`, `stepOutcomes`, `driveU` quoted (WALKTHROUGH:322-349); `drive = driveU spikeCtx`, `driveJ rs = driveU (rsCtx rs)` (WALKTHROUGH:352-353) | same | Adequacy.lean:90-101, 105-108, 121-129, 147-148, 1633-1635 — identical | VERIFIED |
| 4 | `list_reverse_certified` conclusion as described (WALKTHROUGH:177-195); hypotheses "SeedChain, m₀ ##ₘ R" (README:120) | `list_reverse_certified` | ListRevExhibit.lean:1455-1480: conclusion exactly as described. EXTRA hypothesis `(hlib : CerbLocation.isLibraryLocation loc = false)` (l.1460) and fuel `6 + nsteps ≤ lemDefaultFuel`, `5 + nsteps ≤ …` (l.1463-1464); section variables `loc ann ra mo pbty cbty bbty nbty ubty` (l.1153-1154) | VERIFIED conclusion / MISMATCH hypothesis list (M-1) |
| 5 | `list_reverse_certified_total` at `13 * ns.length + 7`, "no fuel hypotheses" (README:120, WALKTHROUGH:195-197) | `list_reverse_certified_total` | ListRevExhibit.lean:2011-2027: `driveJ … aids (13 * ns.length + 7) … = .done (ptrVal p') σ'`; no fuel hypothesis; carries `hlib` | VERIFIED |
| 6 | `list_reverse_certified_production` quoted verbatim (WALKTHROUGH:145-163) | same | ProdLoopExhibit.lean:1576-1594 identical | VERIFIED |
| 7 | `fib_certified_total`: `driveJ … (2·n+4) … = .done (fib n) σ₀`, no fuel hyp, hyp `0 ≤ n` (README:116) | `fib_certified_total` | FibExhibit.lean:623-628: `(hn : 0 ≤ n) … driveJ (fibRS …) aids (2 * n.toNat + 4) … σ₀ = .done (ivVal (fibSpec n.toNat)) σ₀` | VERIFIED |
| 8 | `exhibitA_prod` described (WALKTHROUGH:880-891) | `exhibitA_prod` | ProdExhibit.lean:245-254: `∀ sup fs args`, runND equation, `dres.dres_core_value = sevenVal`, `∃ i a, CellCoh fmapEmpty dst'.layout_state i ⟨a, intTy, sevenBytes fmapEmpty⟩`, not blocked, empty stdout/stderr | VERIFIED |
| 9 | `prod_run_eqJ` quoted (WALKTHROUGH:852-866) | `prod_run_eqJ` | ProdEntry.lean:448-462 identical | VERIFIED |
| 10 | `wp_store` quoted (WALKTHROUGH:419-428); `wp_load` described with `htrap` (WALKTHROUGH:441-447) | `wp_store`, `wp_load` | Rules.lean:177-186 identical; Rules.lean:285-294 matches description | VERIFIED |
| 11 | `wps_create` quoted (WALKTHROUGH:491-505); `wpt_create` "cost bound `2 ≤ k`" (README:311) | `wps_create`, `wpt_create` | Wps.lean:2503-2517 identical; Wpt.lean:2157-2171 same shape with `{k : Nat} (hk : 2 ≤ k)` | VERIFIED |
| 12 | `wpt.pre`/`wpt` quoted (WALKTHROUGH:560-591); `wpt_run` premise `1 + m ≤ k`; `wpt_sound` into `[{ }]` (WALKTHROUGH:604-609) | `wpt.pre`, `wpt`, `wpt_run`, `wpt_sound` | Wpt.lean:111-137, 142-145 identical; Wpt.lean:516-526 `(hμ : 1 + m ≤ k)`; Wpt.lean:2260-2264 identical | VERIFIED |
| 13 | `engine_step_matchU` quoted (WALKTHROUGH:774-780); `RoundClass` four arms (WALKTHROUGH:784-791); `cerberusRound_refused_*` for store/load/create/case only (README:431) | `engine_step_matchU`, `RoundClass`, `cerberusRound_classify`, `cerberusRound_refused_*` | Soundness.lean:4399-4405 identical; Round.lean:138-155 arms `value_done`/`value_annot`/`step`/`refused`; Round.lean:305,316,328,340 exactly the four refused theorems | VERIFIED |
| 14 | `diverge_total_unprovable`: a total derivation for the self-jump loop is `False` (README:123, WALKTHROUGH:614-616) | `diverge_total_unprovable` | DivergeExhibit.lean:118-125: `(hwp : ∀ [SpikeGS …], ⊢ iprop(blockSpecsT … Ls Ψ ∗ wpt … Ls k Ψ (dgBody ra) [fmapEmpty])) : False` | VERIFIED |
| 15 | `CellCoh` "six fields" (WALKTHROUGH:380); `Coh`/`Sat` quoted (WALKTHROUGH:372-377); "`Sat` = `Coh` (Heap.lean)" (README:86) | `CellCoh`, `Coh`, `Sat` | Heap.lean:303-310 + `dec_indep` = six fields; Heap.lean:331-334 `Coh` identical; `Sat` is at **Adequacy.lean:1072**, not Heap.lean | VERIFIED / location Note N-1 |
| 16 | Audit pins "107 trio-exact" (README:382, WALKTHROUGH:897) | `trioExports` | Audit.lean:78-…: 107 names in the list (110 backticked names in my grep minus the three banned-axiom names that follow the list); all headline theorems named in the README appear (`project_triple`, `list_reverse_certified`, `fib_certified_total`, `exhibitA_prod`, `list_reverse_certified_production`, …). "1184 theorems / 2030 constants / 444 jobs" NOT verified (no build run) | VERIFIED (count) |
| 17 | Capability manifest "18 rows, 0 red" (README:43) | `docs/CAPABILITY_MANIFEST.md`; `inductive Frag` | Manifest footer `MANIFEST: 18 rows, 0 red, 13 exhibit modules`; `Frag` (Soundness.lean:3581) has 18 constructors | VERIFIED |
| 18 | `wps_case_value`/`wps_wseq` at the partial stratum only (README:43-46) | same | Wps.lean:1078, 835 exist; no `wpt_case_value`/`wpt_wseq` anywhere (grep) | VERIFIED |
| 19 | `dischargeStep` mirrors `action_request_sequential2`, "Driver.lean:273" (README:217, WALKTHROUGH:357-359) | `dischargeStep`, dependency | Soundness.lean:153-178 matches request arms with `storeM`/`loadM`/`allocateObject`; `.cerberus-ws/lean_frontend/generated/Driver.lean:273` is `def action_request_sequential2 …` | VERIFIED |
| 20 | "Neither the semantics workspace nor its lem runtime (`LemLib`) declares an axiom"; kernel-opaque constants = `md5Hex`/`digestIO`, `fuelExhausted`, `failwithI` (README:166-172) | dependency grep | No `axiom` declaration in `lean_frontend/{CerberusLean,generated,native}`, LemLib, or iris. BUT `opaque` constants beyond the three named: `CerbGlobal.{backend_name, current_execution_mode, using_concurrency, isDefacto, isPermissive, isAgnostic, isIgnoreBitfields, has_switch}` (generated/CerbGlobal.lean:114-135), `CerberusImpl.{typeof_enum, register_enum}` (generated/CerberusImpl.lean:67,237), `CerberusFresh.{setDigestIO, digest, forceIO}`. `CerbMem.lean` references none of them (0 hits); `Driver.lean` reads `current_execution_mode` twice; DriverCollapse.lean:968 proves `driver2_done` by `cases` on that read | VERIFIED (no axiom) / incomplete list (M-2) |
| 21 | `lemDefaultFuel = 10^6` (README:184-185) | `lemDefaultFuel` | `.lake/packages/LemLib/lean-lib/LemLib.lean:56`: `def lemDefaultFuel : Nat := 1000000` | VERIFIED |
| 22 | Differential-validation lane numbers (README:158-162) | `../.cerberus-ws/lean_frontend/VALIDATION.md` | lines 46, 50, 54, 56, 60, 61 carry 106/106, 16/16, 213/213, 1,669, 2,186 / 1,316 exactly as quoted | VERIFIED (as a record; not re-run) |
| 23 | `lr_wps_frame` quoted "verbatim" (WALKTHROUGH:219-229) | `lr_wps_frame` | ListRevExhibit.lean:1134-1143 identical text, but the proof uses section variables `p rs hQ` where `(hQ : LabeledAt rs p (lrQ loc ann ra mo pbty cbty bbty nbty ubty))` (l.892-893) — an invisible hypothesis tying the context's label map | VERIFIED text / hidden hypothesis (M-1) |
| 24 | `alloc_create_launch_smoke` "at `driveU` fuel exactly 2" (README:119); `tree_rotate_certified_total` "constant budget 19" (README:121); `exhibitA_total` "fuel 6" (README:112) | same | AllocExhibit.lean:162-168 `driveU spikeCtx aids 2 … prodMem₀ = .done v σ'`; TreeRotExhibit.lean:1448 `drive aids 19`; Exhibit.lean:583 `driveU spikeCtx aids 6` | VERIFIED |
| 25 | `Language` instance quoted, no `Language.Context` (WALKTHROUGH:748-758) | Lang.lean | Lang.lean:43-48 identical; Lang.lean:18-23, 80-86 record the deliberate absence | VERIFIED |
| 26 | `ReadinessSmoke` imports ONLY the API (README:342) | `Examples/ReadinessSmoke.lean` | single `import CerberusHeapLang.API` at l.47; `twoField` l.99, `twoField_create` l.269 | VERIFIED |

## 5. Findings

### High

**H-1. "ANY Iris triple" overstates `project_triple`; allocating
programs have no boring-triple face.** README:78-81: "`project_triple`
(Adequacy.lean): ANY Iris triple with a concrete-map precondition and an
ARBITRARY Iris postcondition projects to the boring triple `MemTripleU`".
The tree: `project_triple`'s `hwp` premise is `([∗map] i ↦ c ∈ P,
cellOwn … (.own 1) c) ⊢ WP …` (Adequacy.lean:1249-1250) — footprint
cells only. A client that allocates needs `allocCap` in its
precondition (`wps_create`, Wps.lean:2510), and the only adequacy
theorems that grant it are `engine_adequacyU_alloc`
(Adequacy.lean:967-987) and `wpt_engine_boundU/J_alloc`
(TotalAdequacy.lean:1000, 1042), whose readout post is the Iris-shaped
`readoutPost ψ` (TotalAdequacy.lean:700-703), not a `MemTripleU`. There
is no `project_triple_alloc`/`MemTripleU` for allocating programs
(grep). A reader who has just been told (§3.3) how to allocate and
(§1.1) that "the projection" takes any triple will expect to state
their allocating client as `MemTripleU` and cannot; the allocating
exhibits (`struct_create_store_adequacy`, StructExhibit.lean:802;
`alloc_create_launch_smoke`) are all stated by hand-unfolding the drive
statement. Fix (text): at README:79 and WALKTHROUGH:65-66 replace "ANY
Iris triple with a concrete-map precondition" by "any Iris triple whose
precondition is footprint ownership alone (no `allocCap`); allocating
programs reach the drive statements through
`engine_adequacyU_alloc`/`wpt_engine_boundU_alloc` and are stated with
`readoutPost`; a projection at a `LaunchCoh` precondition does not yet
exist", and add the row to "Registered divergences and seams".

### Medium

**M-1. Exhibit hypotheses are not fully listed, contrary to the table's
own promise; the "verbatim" Iris triple hides a tie hypothesis.**
README:105-108: "hypotheses beyond the seeded footprint and the
engine's own fuel budget are listed". Row `list_reverse_certified`
lists "`SeedChain m₀ head ns`, `m₀ ##ₘ R`"; row
`tree_rotate_certified` "`SeedTree m₀ px t`, disjoint frame"; row
`struct_*` "seeded struct / plan". Each of these also carries `(hlib :
CerbLocation.isLibraryLocation loc = false)` (ListRevExhibit.lean:1460,
2015; TreeRotExhibit.lean:1445; StructExhibit.lean:805) and ranges over
section-variable metadata `loc ann ra mo pbty …`
(ListRevExhibit.lean:1153-1154). `hlib` is a genuine premise (it is a
constructor argument of `Frag.store/load/create`, Soundness.lean:3585,
3589, 3593), and README:194-197 does register it under "frozen
well-formedness" — but not where the table says it will be. Separately,
WALKTHROUGH:219-229 quotes `lr_wps_frame` as verbatim while the
statement depends on section variables `(p : sym) (rs : core_run_state)
(hQ : LabeledAt rs p (lrQ loc ann ra mo pbty cbty bbty nbty ubty))`
(ListRevExhibit.lean:892-893): the Iris triple holds only at a machine
context whose label table is the loop's, which is the crux of how
`wps_run` can "stop tracking". A reader would form the belief that the
triple is context-generic. Fix: add `hlib` (and "metadata `loc ann ra
mo` and base types universally quantified") to the affected rows;
under the `lr_wps_frame` quote add one line: "Section hypotheses not
shown: `p rs` and `hQ : LabeledAt rs p (lrQ …)` — the context's label
map is the loop's (ListRevExhibit.lean:892)".

**M-2. The kernel-opaque constant list is incomplete, and the
configuration question a Cerberus-aware reader will ask is not
answered.** README:167-172 names `md5Hex`/`digestIO`, `fuelExhausted`,
`failwithI`. The generated semantics also declares `opaque
CerbGlobal.has_switch : CerbSwitch → Bool`, `isPermissive`, `isDefacto`,
`isAgnostic`, `isIgnoreBitfields`, `using_concurrency`,
`current_execution_mode`, `backend_name` (generated/CerbGlobal.lean:
114-135) and `CerberusImpl.typeof_enum`/`register_enum`
(CerberusImpl.lean:67, 237). Anyone who knows Cerberus knows its
memory model is switch-configured (PNVI variants, strict pointer
arithmetic, …) and will ask "which configuration is this theorem
about?" The tree's answer is good and undocumented: `CerbMem.lean`
references no `CerbGlobal` constant at all (0 hits), `Core_reduction.lean`
none, and the driver's `current_execution_mode ()` read is discharged
by `cases` on the opaque test (DriverCollapse.lean:495-497, 923-927,
968-985), so the exports hold for every value of every opaque
configuration constant. Fix: extend the README:167 list to "the
`CerbGlobal.*` switch/mode reads and `CerberusImpl.typeof_enum`/
`register_enum`", and add: "the Lean port's `CerbMem` reads no switch;
the one configuration read on the production path
(`current_execution_mode`) is proved by cases, so every export holds
under every configuration".

**M-3. How the `PtrEq` null test avoids the provenance fork is not
stated.** WALKTHROUGH:128-129 ("the null test uses it, no flags
smuggled in") and README:59-60/README:432 (the "differing-provenance
nondeterministic fork" is a fail-closed absence) leave the reader
asking how comparing `cur` (`Prov_some id`) against the null pointer is
not itself a differing-provenance comparison. The tree: `wps_memop_ptreq`
(Wps.lean:1503-1509) carries `(hres : ∀ σ : Mem, applyMemM
(CerbMem.eqPtrval default pv1 pv2) σ = some (b, σ))` — the CLIENT
proves the engine's comparison is a deterministic, memory-preserving
`some`, which is what excludes the `msum` fork, and for null it is a
computation. Fix: one sentence at WALKTHROUGH:128 or §3 "Operands,
memop": "`wps_memop_ptreq` asks the client for the engine's own
`eqPtrval` result as a deterministic equation (`hres`); comparisons
that could fork have no rule".

**M-4. The "two capped builds" are not identified.** README:388-389:
"The trust base is exactly three things: the two capped builds with
their in-build axiom sweeps, plus the banned proof-method grep". The
README describes one build (`cd cerberus-heaplang && lake build`,
README:369-372). A fresh reader cannot tell what the second build is
(presumably the repository root package) or whether it matters for
this package's claims. Fix: name both builds and state that this
package's claims rest on its own build alone.

### Notes

**N-1.** README:86 "`Sat` = `Coh` (Heap.lean)": `Coh` is Heap.lean:331,
`Sat` is Adequacy.lean:1072 (`abbrev Sat … := Coh tds σ m`). Point the
reader at the right file.

**N-2.** `DriveResult.killed`'s docstring, quoted verbatim into
WALKTHROUGH:328-330, says "the full loadM/storeM failure vocabulary —
docs/2026-08-30_spike-recon.md §2.6". This is the one place the front
documents send the reader to a dated note for a load-bearing item (what
"kill" covers). WALKTHROUGH:721-724 does state the OOM policy (a `create`
that cannot be placed is a KILL), so the no-OOM story is answerable
without the note; but the general kill vocabulary (`Undef0`/`Error0`/
`Other` — which `mem_error`s?) is not. One paragraph in §2 would close
it.

**N-3.** Counts I could not verify without a build: "1184 theorems
bounded", "2030 constants", "444 jobs" (README:383-385,
WALKTHROUGH:930-932). The 107 pins I could and did.

**N-4.** No exhibit beyond `exhibitA/B/C_semantic` is *stated* as a
`SemTriple`/`MemTripleU` value; the loop exhibits unfold the shape by
hand (e.g. ListRevExhibit.lean:1467-1480). This is fine, but a sentence
"the loop exhibits state the `MemTripleU` body directly at their
profile" would spare a reader the search for a `MemTripleU` instance.

**N-5.** WALKTHROUGH:198-199 "`list_reverse_demo` instantiates a 3-node
chain with every byte-level side condition by `rfl`" — the statement
(ListRevExhibit.lean:1591-1599) still carries `hlib`, the fuel pair and
`R`; "every side condition" should read "every decode side condition".

**N-6.** README:112 "delivers `Specified(7)`": `sevenVal = Vloaded
(LVspecified (OVinteger (integerIval 7)))` (Examples/Layout.lean:55-56).
Correct; noting it because a reader cannot see it from the docs.

## 6. Three questions the documents should have answered

1. **Under which Cerberus configuration do the theorems hold?** Every
   Cerberus user knows about switches and PNVI variants. The answer
   (none are read by the Lean `CerbMem`; the driver's mode read is
   proved by cases) is in the tree but nowhere in the two documents
   (M-2).
2. **How do I get a boring `MemTripleU` for a program that allocates?**
   §3.3 tells me how to prove the Iris triple with `allocCap`; §1.1
   tells me "the projection" takes any triple; the tree says no such
   projection exists for `allocCap` preconditions and I must state my
   client as a drive equation via `wpt_engine_boundU_alloc` (H-1).
3. **What exactly must I supply for a loop client's context?** The
   walkthrough names `wps_save`/`wps_run`/`blockSpecs_intro` but never
   shows how `procCtx p rs`, `lrRS`, `LabeledAt` and the `hQ` tie are
   built, nor how `wps_load_at`'s `hdec : ∀ lum fpm, reconstructValue …
   = mv` and `wps_create`'s `hinert : ∀ a, decIndep …` are discharged
   (by `rfl`/`fun _ _ => rfl` for scalars, per Heap.lean:311-318 — but
   that is in a docstring, not the docs).

## 7. Verdict

**With these gaps.** From README + WALKTHROUGH + the `API.lean` header
I could write and state a small *non-allocating*, straight-line or
single-loop client: the rule names, their shapes, the `MemTripleU`
target and the `#print axioms` check are all there and all matched the
tree. I would be blocked or misled at three points: (a) an allocating
client cannot be projected to the advertised boring triple (H-1); (b)
the machine-context/label-map plumbing (`procCtx`, `LabeledAt`, the
hidden `hQ`) and the decode side conditions (`hdec`, `hinert`) are only
learnable by copying an exhibit (M-1, Q3); (c) I would have written a
theorem with fewer hypotheses than the tree requires (`hlib`) and been
surprised at the first `Frag` obligation (M-1). None of the gaps is a
soundness gap: every claim I checked is proved as stated or stronger;
the findings are about the two documents' scope qualifiers, not the
theorems.
