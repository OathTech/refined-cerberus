# 2026-09-02 — THE PROJECTION: any Iris triple projects to a boring triple over engine states

Worker record. Provenance: [USER 2026-09-02] (DECISIONS.md, the three
closing 2026-09-02 entries: feature freeze; TWO TRUST CLAIMS; NO BORING
LOGIC — A PROJECTION THEOREM ONLY), verbatim charter: "don't prove the
rules, but show that any iris-level triple can be projected into a
'boring' triple over semantic states. This gives us the ability to state
properties via iris but doesn't mirror the logic." Target statement
shape ([USER], verbatim): "s |= P && core_exec(prog, s) ~~> term ==>
term = some(s') && s' |= Q" for P/Q "just memory + pure properties".
Slice classification (one-change-at-a-time): a spec-FORM addition for
the closed-program story — ONE theorem, its definition, convenience
lemmas, and proof-body de-duplication; NO public statement changed
(§5, the signature snapshot). Quoted outputs are verbatim; tallies
marked DERIVED are computed as stated.

Commits (both on `heaplang-alloc-arc`): `6a7c041` (fast-gate: items 1-3,
the code) and the closing commit (this record, README/WALKTHROUGH trust
paragraphs, snapshots; FULL gate — §6).

## 1. The theorem (verbatim, `CerberusHeapLang/Adequacy.lean`)

The boring triple (the [USER] shape with the frame built in — `R` is
the arbitrary rest footprint and is passed to the post):

```lean
def MemTripleU (M : MachineCtx) (ρ : EnvStack) (e : CoreExpr) (P : CellMap)
    (post : CellMap → value → Mem → Prop) : Prop :=
  ∀ (R : CellMap), P ##ₘ R →
  ∀ (σ : Mem), Sat M.tagDefs σ (Iris.Std.PartialMap.union P R) →
  ∀ (n : Nat) (aids : Nat → Nat), esize e + n ≤ lemDefaultFuel →
    (∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      esize cont + n ≤ lemDefaultFuel) →
    (∀ r, driveU M aids n (M.thread e ρ) σ ≠ .killed r) ∧
    (driveU M aids n (M.thread e ρ) σ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem), driveU M aids n (M.thread e ρ) σ = .done v σ' →
      post R v σ')
```

`SemTripleU` is its instance at the cells-shaped post, definitionally:

```lean
theorem SemTripleU_iff_Mem (M : MachineCtx) (ρ : EnvStack) (e : CoreExpr) (P : CellMap)
    (post : value → CellMap → Prop) :
    SemTripleU M ρ e P post ↔
      MemTripleU M ρ e P (fun R v σ' => ∃ Q : CellMap, post v Q ∧ Q ##ₘ R ∧
        Sat M.tagDefs σ' (Iris.Std.PartialMap.union Q R)) :=
  Iff.rfl
```

THE PROJECTION:

```lean
theorem project_triple {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx} (hwf : M.SeqWF)
    (hQf : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      Frag cont)
    {e : CoreExpr} (hfrag : Frag e) (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (P : CellMap) (Q : ∀ [SpikeGS .hasLC GF], CoreRVal → IProp GF)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ P, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
        WP (⟨e, ev0 :: evs, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ {{ w, Q w }}) :
    MemTripleU M (ev0 :: evs) e P (fun R v σ' => ∀ ψ : Prop,
      (∀ [SpikeGS .hasLC GF] (w : CoreRVal), w.val = v →
        ∀ (mm : SpikeHeapF MetaCell) (mb : SpikeHeapF CerbMem.AbsByte)
          (mk : SpikeHeapF AllocCursor), CohG σ' mm mb mk →
        iprop(Q w ∗ ([∗map] i ↦ c ∈ R, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c) ∗
          metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ⌝ : IProp GF)) → ψ) := by
```

Proof (13 lines): `engine_adequacyU` at the seeded footprint `P ∪ R`;
inside the WP, `spike_wp_wand` to the readout post; the readout is
`stateInterp_readout` (Rules.lean — the ONE open/close of the state
interpretation) applied to `consequences_intro` (interior: the pure
implication law `(∀ ψ, H ψ → Φ ⊢ ⌜ψ⌝) → Φ ⊢ ⌜∀ ψ, H ψ → ψ⌝`, classical
by cases on `H ψ`). No new axiom; cone = the classical trio (Audit pin).

Not an instance of the existing `SemTripleU`: its post is over a
footprint `Q : CellMap` with `Sat σ' (Q ∪ R)` and cannot mention `σ'`
directly, so the memory-post form `MemTripleU` is DEFINED; the relation
runs the other way (`SemTripleU_iff_Mem`, `Iff.rfl`), and
`semantic_triple_soundU` is now PROVED as `project_triple` at the
cells-shaped post with the obligation discharged by `cells_consequence`
(its statement unchanged).

## 2. How it instantiates the operator's shape

`s |= P && core_exec(prog, s) ~~> term ==> term = some(s') && s' |= Q`

| Operator symbol | In `MemTripleU`/`project_triple` |
|---|---|
| `s` | `σ : Mem` — a cerberus-lean `MemState`, arbitrary outside the footprint |
| `s \|= P` | `Sat M.tagDefs σ (P ∪ R)` — `Sat` = `Coh` (Heap.lean): each footprint cell live, writable, in-bounds, exactly those bytes, pairwise range-disjoint; `R` is the arbitrary rest, returned to the post (the frame) |
| `prog` | `(e, ρ)` at the machine context `M` — `M.thread e ρ` is the engine's `thread_state` |
| `core_exec(prog, s) ~~> term` | `driveU M aids n (M.thread e ρ) σ` — the iterated `{step_ctx → dischargeStep}` round of the sequential driver (Adequacy.lean layer 1), at every action-id supply `aids` and every fuel `n` within the engine's get_ctx budgets (`esize e + n ≤ lemDefaultFuel`, and the same for every registered label body — the registered FUEL HONESTY seam, stated, not hidden). At the fixed demo profile `drive = driveU spikeCtx`; the production lane's `runND ∘ Driver.drive ∘ initial_driver_state` is reached from the same conclusions by the DriverCollapse/ProdLoop theorems (unchanged by this slice) |
| `term = some(s')` | `driveU … = .done v σ'` — the delivered value and final memory; the other two conjuncts (`≠ .killed r`, `≠ .stuck`) are "no UB / no error-kill / no refusal or off-protocol step"; `.more` (fuel exhaustion) is unconstrained: partial correctness |
| `s' \|= Q` | `post R v σ'` — for `project_triple`: EVERY pure `ψ` such that, against every coupling witness `CohG σ' mm mb mk` and for every logic value `w` erasing to `v` (`w.val = v`), `Q w ∗ cells(R) ∗ metaInterp mm ∗ byteInterp mb ⊢ ⌜ψ⌝`. "Just memory + pure properties": the pure-consequence lemmas (§3) turn this into `CellCoh σ' i c` (bytes, allocation metadata, bounds of the final memory), `Coh σ' (Q ∪ R)` (frame preserved verbatim), and value facts |

What appears in the conclusion that is NOT engine vocabulary: the
pure-consequence obligation's hypothesis — `Q`, `CohG`, `metaInterp`/
`byteInterp`, Iris `⊢`, and the ghost-state instance binder
`∀ [SpikeGS .hasLC GF]`. These are the specification idiom of trust
claim (2): definitions a reader reads, never opened by a client — the
`*_consequence` lemmas discharge the obligation. The two trust claims
are recorded in `Adequacy.lean`'s header and the README trust story.

## 3. The convenience pure-consequence lemmas (Adequacy.lean)

Shape: `Φ ∗ metaInterp mm ∗ byteInterp mb ⊢ ⌜<memory fact>⌝` under
`CohG σ mm mb mk` — exactly the `h` of `stateInterp_readout` and the
obligation in `project_triple`'s post. Signatures verbatim:

```lean
theorem pure_consequence (φ : Prop) :
    iprop(⌜φ⌝ ∗ metaInterp (GF :=
theorem sep_consequence {Φ₁ Φ₂ : IProp GF} {ψ₁ ψ₂ : Prop}
    (h₁ : iprop(Φ₁ ∗ metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ₁⌝ : IProp GF))
    (h₂ : iprop(Φ₂ ∗ metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ₂⌝ : IProp GF)) :
    iprop((Φ₁ ∗ Φ₂) ∗ metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ₁ ∧ ψ₂⌝ : IProp GF) :=
theorem or_consequence {Φ₁ Φ₂ : IProp GF} {ψ₁ ψ₂ : Prop}
    (h₁ : iprop(Φ₁ ∗ metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ₁⌝ : IProp GF))
    (h₂ : iprop(Φ₂ ∗ metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ₂⌝ : IProp GF)) :
    iprop((Φ₁ ∨ Φ₂) ∗ metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ₁ ∨ ψ₂⌝ : IProp GF) :=
theorem exists_consequence {α : Type _} {Φ : α → IProp GF} {ψ : α → Prop}
    (h : ∀ a, iprop(Φ a ∗ metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ a⌝ : IProp GF)) :
    iprop((∃ a, Φ a) ∗ metaInterp mm ∗ byteInterp mb) ⊢ (⌜∃ a, ψ a⌝ : IProp GF) :=
theorem cellOwn_consequence (tds : CerbTags.TagDefsMap) (i : Int) (dq : DFrac) (c : SpikeCell) :
    iprop(cellOwn tds (GF :=
theorem pointsToCell_consequence (tds : CerbTags.TagDefsMap) (pv : CerbMem.PointerValue)
    (dq : DFrac) (ty : ctype) (bs : List CerbMem.AbsByte) :
    iprop(pointsToCell tds (GF :=
theorem cellsOwn_consequence (tds : CerbTags.TagDefsMap) (Q : CellMap) :
    iprop(([∗map] i ↦ c ∈ Q, cellOwn tds (hlc :=
theorem cells_consequence (tds : CerbTags.TagDefsMap)
    (post : value → CellMap → Prop) (R : CellMap) (vv : value) :
    iprop(((∃ Q : CellMap, ⌜post vv Q⌝ ∗
        ([∗map] i ↦ c ∈ Q, cellOwn tds (hlc :=
```

Added ONLY what the exhibits' postconditions use: whole cell
(`cellOwn`), points-to (`pointsToCell`), a `[∗map]` footprint of cells
(plain, and with a frame — the `SemTripleU`-shaped conclusion), and the
`∗`/`∨`/`∃`/pure combinators (`sep_consequence` uses that pure
conclusions are duplicable, so each conjunct reads out against the
whole interpretation). NOT added (no exhibit postcondition uses them;
the brief's "add only what the exhibits need"): `pointsToView`,
`allocMeta`/`locInBounds` consequences — each would be a two-line
instance of `cellOwn_consequence`/`cellOwn_cellCoh` when a client
appears. `cellOwn_readout`, `pointsToCell_readout`, `cells_readout`
(the existing readout-shaped lemmas) are now one-liners:
`stateInterp_readout fun _ _ _ _ hG => <consequence>`.

## 4. De-duplication (DERIVED: `git diff -U0 3ff811e 6a7c041`, hunk line counts)

Statements UNCHANGED for every row (§5). "Proof lines" exclude the
signature; the new bodies include 2-3 comment lines where noted.

| Readout | Module | Proof lines before → after | How |
|---|---|---|---|
| `cellOwn_readout` | Adequacy | 7 → 1 | `stateInterp_readout` + `cellOwn_consequence` |
| `pointsToCell_readout` | Adequacy | 8 → 1 | + `pointsToCell_consequence` |
| `cells_readout` | Adequacy | 14 → 1 | + `cells_consequence` |
| `semantic_triple_soundU` | Adequacy | 14 → 11 (incl. 2 comment lines) | `project_triple` at the cells-shaped post + `cells_consequence` (the headline is the projection's instance) |
| `arr_wp_readout` | ArrayExhibit | 7 → 2 (+3 comment lines) | `wp_mono` ∘ `stateInterp_readout` ∘ `sep_consequence (pure_consequence _) (cellOwn_consequence …)` |
| `case_wp_readout` | CaseExhibit | 5 → 1 | `stateInterp_readout fun … => pure_consequence _` |
| `wseq_wp_readout` | WseqExhibit | 5 → 1 | same |
| `fib_wp_readout` | FibExhibit | 5 → 1 | same |
| `fibPost_to_readout` | FibExhibit | 5 → 1 | same (term-mode) |
| `loop_readout_val` | LoopExhibit | 20 → 11 (+2 comment lines) | `stateInterp_readout` ∘ (`sep`/`or`/`pure`/`pointsToCell_consequence`) then one `BI.pure_mono` reshaping |
| `struct_create_store_adequacy` (inline readout — a 14th site, same class, not on the brief's list) | StructExhibit | 7 → 3 (+2 comment lines) | `stateInterp_readout` ∘ `pointsToCell_consequence` ∘ `BI.pure_mono` |
| `loop_wp_readout` | LoopExhibit | unchanged | already `wp_mono` ∘ `loop_readout_val` (the collapse `wps_sound` is not readout duplication) |
| `loopPost_to_readout` | LoopExhibit | unchanged | already an instance of `loop_readout_val` |
| `struct_wp_readout` | StructExhibit | unchanged | already `cellOwn_readout` (one line) |
| `lr_wp_readout`, `tr_wp_readout` | ListRev/TreeRot | unchanged | collapse + `lrPost_readout`/`trPost_readout`; no readout body |
| `lrPost_readout`, `trPost_readout` | ListRev/TreeRot | unchanged (residual) | the body is the EXHIBIT-PREDICATE unfolding `isList_to_cells`/`isTree_to_cells` (∃ p' / pure shuffling) into `cells_readout`'s shape — exhibit-specific, not a projection matter; a combinator version was not shorter |

DERIVED totals (`git diff --numstat 3ff811e 6a7c041`, the exhibit
modules only): ArrayExhibit −10/+5, CaseExhibit −5/+1, WseqExhibit −5/+1,
FibExhibit −11/+3, LoopExhibit −20/+13, StructExhibit −9/+5 = 60 lines
removed, 28 added (7 of them comments). Adequacy: −45/+267 (the new
section, the consequence lemmas and their documentation; the three
readouts and the headline lost 42 proof lines).

The nuance to state plainly: the exhibit readouts are Iris-level WP
statements (`Φ ⊢ WP e {{ w, ∀ σ' …, stateInterp … ={⊤,∅}=∗ ⌜ψ w.val σ'⌝ }}`),
so they cannot be literal instances of the engine-level `project_triple`;
they are instances of its IRIS HALF — `stateInterp_readout` over the
pure-consequence lemmas — which is exactly the piece `project_triple`
composes with `engine_adequacyU`. The closed-program exports
(`*_certified`) keep their proofs (engine adequacy + the readouts);
`semantic_triple_soundU` is the one export re-proved THROUGH
`project_triple`, which is therefore consumed.

## 5. Signature snapshot (frozen-corpus check)

`docs/2026-09-02_p5-signatures-post.txt (byte-identical to the former 2026-09-02_projection-signatures-pre.txt, deduplicated 2026-09-02)` (at `3ff811e`; byte-
identical to `2026-09-02_p5-signatures-post.txt`) vs `…-post.txt` (at
`6a7c041`). `diff pre post`: `<` lines (removed/changed): 0.
Added declaration headers, verbatim:

```
> def CerberusHeapLang.MemTripleU :
> theorem CerberusHeapLang.SemTripleU_iff_Mem :
> theorem CerberusHeapLang.cellOwn_consequence :
> theorem CerberusHeapLang.cellsOwn_consequence :
> theorem CerberusHeapLang.cells_consequence :
> theorem CerberusHeapLang.consequences_intro :
> theorem CerberusHeapLang.exists_consequence :
> theorem CerberusHeapLang.or_consequence :
> theorem CerberusHeapLang.pointsToCell_consequence :
> theorem CerberusHeapLang.project_triple :
> theorem CerberusHeapLang.pure_consequence :
> theorem CerberusHeapLang.sep_consequence :
```

Classification: PERMITTED ONLY — 1 definition (`MemTripleU`), 10
public theorems (the projection, the iff, 8 consequence lemmas) and 1
interior helper (`consequences_intro`); no public statement changed or
removed. Audit pins: 97 → 107 trio-exact (the 10 theorems).

## 6. Gates (verbatim)

FAST gate at `6a7c041` (`scripts/test_unit.sh --fast`), verdict lines:

```
info: CerberusHeapLang/Audit.lean:162:0: CerberusHeapLang export pins: 107 trio-exact
info: CerberusHeapLang/Audit.lean:162:0: CerberusHeapLang axiom sweep: 1184 theorems bounded by the trio
info: CerberusHeapLang/Audit.lean:162:0: CerberusHeapLang banned-axiom sweep: 2030 constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
Build completed successfully (444 jobs).
ok: cerberus-heaplang build green
FAST-GATE GREEN (gates 1-3 only — not a claim-point result; say fast-gate in the commit)
rc=0
```

FULL gate (`scripts/test_unit.sh`, the claim point) on the closing tree:

verdict lines verbatim (linter warnings elided), exit code 0:

```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 2: capped build, root package (elaborates its axiom audit) ==
info: RefinedCerberus/Audit.lean:75:0: RefinedCerberus axiom sweep: 2 theorems, all cones within the classical trio
info: RefinedCerberus/Audit.lean:75:0: RefinedCerberus banned-axiom sweep: 3 constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
Build completed successfully (370 jobs).
ok: root build green
== gate 3: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:162:0: CerberusHeapLang export pins: 107 trio-exact
info: CerberusHeapLang/Audit.lean:162:0: CerberusHeapLang axiom sweep: 1184 theorems bounded by the trio
info: CerberusHeapLang/Audit.lean:162:0: CerberusHeapLang banned-axiom sweep: 2030 constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
Build completed successfully (444 jobs).
ok: cerberus-heaplang build green
== speedbump: capability manifest (regenerate; red on a red row or drift) ==
ok: capability manifest regenerated, no drift
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — no core module imports an exhibit/example/production module
ALL GATES GREEN
rc=0
```

Manifest: `ok: capability manifest regenerated, no drift` — no consumer
change reached the manifest, so `CAPABILITY_MANIFEST.md` is unchanged.

## 7. Borderline items and observations

1. **Instance binder in the projected post.** The obligation quantifies
   `∀ [SpikeGS .hasLC GF] (w : CoreRVal), w.val = v → …` because the
   Iris post `Q` and the interpretation are ghost-state-indexed and the
   instance exists only inside the adequacy proof (`genHeap_init`); the
   hypothesis is stronger than the instance-specific one (harmless: every
   consequence lemma is instance-generic). The pretty-printed statement
   (§5 snapshot) shows the binder present.
2. **`iprop`/`⌜⌝` hazard observed during development (fail-open,
   noted).** A `∀ [SpikeGS .hasLC GF] (w' …), …` written INSIDE
   `⌜…⌝` under `iprop(…)` elaborated WITHOUT the instance binder (the
   instance was taken from the context), silently changing the
   proposition; caught because a later `absurd` failed to typecheck. The
   shipped statement places the quantifier outside `iprop` (in
   `MemTripleU`'s post argument) and its elaboration is pinned by the
   snapshot. Not a defect in this tree; recorded for the P6 docs and any
   future statement that puts instance binders under `⌜⌝`.
3. **Frame in the definition.** `MemTripleU`'s post receives the rest
   footprint `R` (rather than a separate `Sat σ' R` conjunct) so the
   projected post can state the JOINT consequences of `Q ∗ cells(R)` —
   needed for `Q ##ₘ R ∧ Coh σ' (Q ∪ R)` (cross-disjointness comes from
   the metadata authority, not from two separate `Sat` facts).
4. **Classical step.** `consequences_intro` is by cases on `H ψ`
   (`Classical` — the trio's `Classical.choice` is already in every
   cone; no new axiom).
5. **Not added (no consumer).** A spike-profile instance of
   `project_triple`, an `allocCap`-launch variant
   (`engine_adequacyU_alloc` shape), and `pointsToView`/`allocMeta`/
   `locInBounds` consequence lemmas — each a few lines when a client
   appears.
6. **A 14th readout site** (`struct_create_store_adequacy`'s inline
   points-to readout) was re-derived alongside the 13 listed: same
   duplication class, statement unchanged. Flagged here rather than
   silently included.
7. **DECISIONS.md not touched** (the orchestrator's register); this
   record is the slice's closure record.
8. **Warnings.** No new warnings in any edited module (the
   `unusedVariables` warnings in Adequacy.lean/StructExhibit.lean are
   pre-existing, line-shifted; compared against the `3ff811e` build).
