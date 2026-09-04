# AR5 readout slice — the client boundary sealed (2026-09-04)

Branch `ar5-readout` off `main` `5d08237`; content commit `e9111d0`; this
record is the only later change. Slice class: INTERNALS REFACTOR (public
statements otherwise FROZEN, snapshot-checked). Origin: the external
Reynolds/O'Hearn separation-logic audit of 2026-09-04
(`docs/2026-09-04_reynolds-ohearn-separation-logic-audit.md`, Finding 2,
the Lean part): DisposeExhibit and MallocListExhibit defined readout
helpers over `CohG`/`metaInterp`, so positive examples depended on the
concrete ghost-state organisation. Quoted outputs are verbatim; tallies
marked DERIVED. Provenance: every decision below is [AGENT] (user
offline); none touches `docs/DECISIONS.md`.

## 0. The measured premise (confirmed by reading, before any edit)

`DeadAt` was defined at DisposeExhibit.lean:909 (exhibit-local).
DisposeExhibit.lean:914–963 held `keep_pure`, `deadObj_dead_keep`,
`deadNodes_dead`; MallocListExhibit.lean:742–770 held
`deadRegions_dead`; the two readouts `dlPost_readout` (975) and
`mlPost_readout` (1217) consumed them inside `stateInterp_readout`'s
obligation with explicit `ihave … metaInterp mm` ascriptions. No public
lemma in Adequacy.lean/API.lean read a dead token out in the
`*_consequence` shape (`deadObj_readout`/`deadRegion_readout` exist, but
as single-token `stateInterp`-wand faces, not composable under the
combinator). The audit's assessment holds: the helpers do not bypass the
logic — they are `deadObj_dead`/`deadRegion_dead` (Heap.lean) folded
down a list — but they name the coupling invariant and the metadata
interpretation in a client module. The boundary grep BEFORE (§3) shows
exactly these two modules with code hits on `CohG`/`metaInterp`.

## 1. What moved to the public projection layer (Adequacy.lean), verbatim

`DeadAt` (same name, type and body as the exhibit-local def; the census
reads it UNCHANGED):

```lean
def DeadAt (σ : Mem) (id : Int) : Prop :=
  σ.deadAllocations.contains id = true ∧ σ.allocations.get? id = none
```

The three new lemmas, in the `Consequences` section (its variables
`{hlc} {GF} [SpikeGS hlc GF] {mm} {mb}`, and for the token faces
`{σ} {mk} (hG : CohG σ mm mb mk)` included):

```lean
theorem bigSepL_consequence {α : Type _} {Φ : α → IProp GF} {ψ : α → Prop}
    (h : ∀ x, iprop(Φ x ∗ metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ x⌝ : IProp GF)) :
    ∀ xs : List α,
    iprop(([∗list] x ∈ xs, Φ x) ∗ metaInterp mm ∗ byteInterp mb) ⊢
      (⌜∀ x ∈ xs, ψ x⌝ : IProp GF)
  | [] => BI.pure_intro fun _ hx => nomatch hx
  | x :: xs =>
    (sep_consequence (h x) (bigSepL_consequence h xs)).trans
      (BI.pure_mono fun ⟨hx, hxs⟩ y hy =>
        (List.mem_cons.mp hy).elim (fun e => e ▸ hx) (hxs y))

theorem deadObj_consequence (tds : CerbTags.TagDefsMap) (id a : Int) (ty : ctype) :
    iprop(deadObj tds (GF := GF) id a ty ∗ metaInterp mm ∗ byteInterp mb) ⊢
      (⌜DeadAt σ id⌝ : IProp GF) :=
  ((BI.sep_mono_right BI.sep_elim_left).trans BI.sep_comm.1).trans (deadObj_dead tds hG id a ty)

theorem deadRegion_consequence (id a : Int) (n : Nat) :
    iprop(deadRegion (GF := GF) id a n ∗ metaInterp mm ∗ byteInterp mb) ⊢
      (⌜DeadAt σ id⌝ : IProp GF) :=
  ((BI.sep_mono_right BI.sep_elim_left).trans BI.sep_comm.1).trans (deadRegion_dead hG id a n)
```

As the snapshot prints them (`docs/2026-09-04_ar5-readout-signatures-post.txt`):

```
theorem CerberusHeapLang.bigSepL_consequence :
∀ {hlc : Iris.HasLC} {GF : Iris.BundledGFunctors} [inst : CerberusHeapLang.SpikeGS hlc GF]
  {mm : CerberusHeapLang.SpikeHeapF CerberusHeapLang.MetaCell}
  {mb : CerberusHeapLang.SpikeHeapF CerbMem.AbsByte} {α : Type u_1} {Φ : α → Iris.IProp GF}
  {ψ : α → Prop},
  (∀ (x : α), Φ x ∗ CerberusHeapLang.metaInterp mm ∗ CerberusHeapLang.byteInterp mb ⊢ ⌜ψ x⌝) →
    ∀ (xs : List α),
      ([∗list] x ∈ xs, Φ x) ∗ CerberusHeapLang.metaInterp mm ∗ CerberusHeapLang.byteInterp mb ⊢
        ⌜∀ (x : α), x ∈ xs → ψ x⌝
----
theorem CerberusHeapLang.deadObj_consequence :
∀ {hlc : Iris.HasLC} {GF : Iris.BundledGFunctors} [inst : CerberusHeapLang.SpikeGS hlc GF]
  {mm : CerberusHeapLang.SpikeHeapF CerberusHeapLang.MetaCell}
  {mb : CerberusHeapLang.SpikeHeapF CerbMem.AbsByte} {σ : CerberusHeapLang.Mem}
  {mk : CerberusHeapLang.SpikeHeapF CerberusHeapLang.AllocCursor},
  CerberusHeapLang.CohG σ mm mb mk →
    ∀ (tds : CerbTags.TagDefsMap) (id a : Int) (ty : ctype),
      CerberusHeapLang.deadObj tds id a ty ∗
          CerberusHeapLang.metaInterp mm ∗ CerberusHeapLang.byteInterp mb ⊢
        ⌜CerberusHeapLang.DeadAt σ id⌝
----
theorem CerberusHeapLang.deadRegion_consequence :
∀ {hlc : Iris.HasLC} {GF : Iris.BundledGFunctors} [inst : CerberusHeapLang.SpikeGS hlc GF]
  {mm : CerberusHeapLang.SpikeHeapF CerberusHeapLang.MetaCell}
  {mb : CerberusHeapLang.SpikeHeapF CerbMem.AbsByte} {σ : CerberusHeapLang.Mem}
  {mk : CerberusHeapLang.SpikeHeapF CerberusHeapLang.AllocCursor},
  CerberusHeapLang.CohG σ mm mb mk →
    ∀ (id a : Int) (n : Nat),
      CerberusHeapLang.deadRegion id a n ∗
          CerberusHeapLang.metaInterp mm ∗ CerberusHeapLang.byteInterp mb ⊢
        ⌜CerberusHeapLang.DeadAt σ id⌝
----
```

The brief's three shapes, mapped: (i) a single `deadObj`/`deadRegion`
token implies the concrete readout under the projection =
`deadObj_consequence`/`deadRegion_consequence` (the projection's
obligation shape, `project_triple`'s `hpost`); (ii) the big separating
conjunction folds = `bigSepL_consequence`, instantiated at the dead
tokens through `exists_consequence` (the list forgets the base) — a
dead list `[∗list] id ∈ ids, ∃ a, deadRegion id a n` reads out as
`∀ id ∈ ids, ∃ a, DeadAt σ id`; (iii) the postcondition-shaped
consequence twin = the same two token faces, mirroring
`cellOwn_consequence`'s style exactly (the post-level readout a client
states is `stateInterp_readout` applied to the composition — already
public, "the one sanctioned combinator"). See §6 for why (i) and (iii)
are one pair of lemmas and why no dead-token-specific LIST lemma was
added.

## 2. What was deleted from the exhibits, verbatim (pre-slice source)

DisposeExhibit.lean (the `DlReadout` section; `keep_pure` KEPT, see §6):

```lean
/-- The engine-facing dead fact of one id: in `deadAllocations`, record
    erased (`killM`, CerbMem.lean:1576-1578). -/
def DeadAt (σ : Mem) (id : Int) : Prop :=
  σ.deadAllocations.contains id = true ∧ σ.allocations.get? id = none

/-- One dead cell's readout, the metadata interpretation returned. -/
theorem deadObj_dead_keep {σ : Mem} {mm : SpikeHeapF MetaCell}
    {mb : SpikeHeapF CerbMem.AbsByte} {mk : SpikeHeapF AllocCursor}
    (hG : CohG σ mm mb mk) (id a : Int) (ty : ctype) :
    iprop(metaInterp (GF := GF) mm ∗ deadObj fmapEmpty id a ty) ⊢
      iprop(⌜DeadAt σ id⌝ ∗ metaInterp mm) :=
  (keep_pure (deadObj_dead fmapEmpty hG id a ty)).trans
    (BI.sep_mono_right BI.sep_elim_left)

/-- Every node of the dead list is dead in the real state. -/
theorem deadNodes_dead {σ : Mem} {mm : SpikeHeapF MetaCell}
    {mb : SpikeHeapF CerbMem.AbsByte} {mk : SpikeHeapF AllocCursor}
    (hG : CohG σ mm mb mk) :
    ∀ ns : List (Int × Int),
    iprop(metaInterp (GF := GF) mm ∗ deadNodes ns) ⊢
      iprop(⌜∀ nd ∈ ns, DeadAt σ nd.1⌝ ∗ metaInterp mm)
  -- (37-line proof by list induction over `deadObj_dead_keep`)
```

MallocListExhibit.lean:

```lean
/-- Every id of the dead list is dead in the real state — through the
    public consequence face `deadRegion_dead` (the metadata
    interpretation returned each time). -/
theorem deadRegions_dead {σ : Mem} {mm : SpikeHeapF MetaCell}
    {mb : SpikeHeapF CerbMem.AbsByte} {mk : SpikeHeapF AllocCursor}
    (hG : CohG σ mm mb mk) :
    ∀ ids : List Int,
    iprop(metaInterp (GF := GF) mm ∗ deadRegions ids) ⊢
      iprop(⌜∀ id ∈ ids, DeadAt σ id⌝ ∗ metaInterp mm)
  -- (28-line proof by list induction over `keep_pure (deadRegion_dead …)`)
```

The two dead-list predicates are now the big separating conjunction (the
`_nil`/`_cons` unfoldings remain `rfl`, their statements and every
statement over `deadNodes`/`deadRegions` UNCHANGED in the census):

```lean
def deadNodes (ns : List (Int × Int)) : IProp GF :=
  iprop([∗list] nd ∈ ns, ∃ a : Int, deadObj fmapEmpty nd.1 a nodeTy)

def deadRegions (ids : List Int) : IProp GF :=
  iprop([∗list] id ∈ ids, ∃ a : Int, deadRegion id a 16)
```

The two readouts now (statements UNCHANGED; the obligation passed to
`stateInterp_readout` is a composition of public lemmas — `hG` is bound,
never opened, its type never written):

```lean
theorem dlPost_readout (ns : List (Int × Int)) (R : CellMap) :
    ∀ (w : SpikeVal) (ρ' : EnvStack),
    iprop(dlPost (hlc := .hasLC) (GF := GF) ns w ρ' ∗ lrCellFrame R) ⊢
      readoutPost (fun v σ' => v = Vunit ∧ (∀ nd ∈ ns, DeadAt σ' nd.1) ∧
        Coh fmapEmpty σ' R) w ρ' := by
  intro w ρ'
  have haux : … :=
    stateInterp_readout (Φ := iprop(deadNodes ns ∗ lrCellFrame R))
      (ψ := fun σ' => Vunit = Vunit ∧ (∀ nd ∈ ns, DeadAt σ' nd.1) ∧ Coh fmapEmpty σ' R)
      (fun _ _ _ _ hG => by
        unfold deadNodes
        refine (sep_consequence
          (bigSepL_consequence
            (Φ := fun nd : Int × Int => iprop(∃ a : Int, deadObj fmapEmpty nd.1 a nodeTy))
            (fun nd => exists_consequence fun a =>
              deadObj_consequence hG fmapEmpty nd.1 a nodeTy) ns)
          (cellsOwn_consequence hG fmapEmpty R)).trans ?_
        exact BI.pure_mono fun ⟨hdead, hcoh⟩ =>
          ⟨rfl, fun nd hnd => (hdead nd hnd).elim fun _ h => h, hcoh⟩)
  iintro ⟨⟨%hw, HD⟩, HF⟩
  subst hw
  iapply haux
  isplitl [HD]
  · iexact HD
  · iexact HF

theorem mlPost_readout (n : Int) (w : SpikeVal) (ρ' : EnvStack) :
    mlPost (hlc := .hasLC) (GF := GF) n w ρ' ⊢
      readoutPost (fun v σ' => v = Vunit ∧
        ∃ ids : List Int, ids.length = n.toNat ∧ ids.Nodup ∧
          ∀ id ∈ ids, DeadAt σ' id) w ρ' := by
  have haux : … :=
    stateInterp_readout
      (Φ := iprop(∃ ids : List Int, ⌜ids.length = n.toNat ∧ ids.Nodup⌝ ∗ deadRegions ids))
      (ψ := …)
      (fun _ _ _ _ hG => by
        unfold deadRegions
        refine (exists_consequence fun ids =>
          sep_consequence (pure_consequence _)
            (bigSepL_consequence (Φ := fun id : Int => iprop(∃ a : Int, deadRegion id a 16))
              (fun id => exists_consequence fun a => deadRegion_consequence hG id a 16) ids)).trans ?_
        exact BI.pure_mono fun ⟨ids, hlen, hdead⟩ =>
          ⟨rfl, ids, hlen.1, hlen.2, fun id hid => (hdead id hid).elim fun _ h => h⟩)
  iintro ⟨%hw, HD⟩
  subst hw
  iapply haux
  iexact HD
```

## 3. The boundary grep, before / after

Command (from `cerberus-heaplang/`):
`grep -n 'CohG\|metaInterp\|byteInterp\|wps.pre\|wpt.pre\|Step\.' CerberusHeapLang/*Exhibit*.lean CerberusHeapLang/Examples/*.lean`

BEFORE (`5d08237`) — 52 lines (DERIVED count). The CODE hits in
POSITIVE exhibits, i.e. the genuine boundary crossings (this slice's
class, "readout via internals"):

```
CerberusHeapLang/DisposeExhibit.lean:921:    (hG : CohG σ mm mb mk) (id a : Int) (ty : ctype) :
CerberusHeapLang/DisposeExhibit.lean:922:    iprop(metaInterp (GF := GF) mm ∗ deadObj fmapEmpty id a ty) ⊢
CerberusHeapLang/DisposeExhibit.lean:923:      iprop(⌜DeadAt σ id⌝ ∗ metaInterp mm) :=
CerberusHeapLang/DisposeExhibit.lean:930:    (hG : CohG σ mm mb mk) :
CerberusHeapLang/DisposeExhibit.lean:932:    iprop(metaInterp (GF := GF) mm ∗ deadNodes ns) ⊢
CerberusHeapLang/DisposeExhibit.lean:933:      iprop(⌜∀ nd ∈ ns, DeadAt σ nd.1⌝ ∗ metaInterp mm)
CerberusHeapLang/DisposeExhibit.lean:945:    ihave H1 : iprop(⌜DeadAt σ nd.1⌝ ∗ metaInterp (GF := GF) mm) $$ [Hmi Hd]
CerberusHeapLang/DisposeExhibit.lean:951:    ihave H2 : iprop(⌜∀ x ∈ ns, DeadAt σ x.1⌝ ∗ metaInterp (GF := GF) mm) $$ [Hmi Hrest]
CerberusHeapLang/DisposeExhibit.lean:988:        ihave H1 : iprop(⌜∀ nd ∈ ns, DeadAt σ nd.1⌝ ∗ metaInterp (GF := GF) mm) $$ [Hmi HD]
CerberusHeapLang/MallocListExhibit.lean:744:    (hG : CohG σ mm mb mk) :
CerberusHeapLang/MallocListExhibit.lean:746:    iprop(metaInterp (GF := GF) mm ∗ deadRegions ids) ⊢
CerberusHeapLang/MallocListExhibit.lean:747:      iprop(⌜∀ id ∈ ids, DeadAt σ id⌝ ∗ metaInterp mm)
CerberusHeapLang/MallocListExhibit.lean:760:        metaInterp (GF := GF) mm) $$ [Hmi Hd]
CerberusHeapLang/MallocListExhibit.lean:767:    ihave H2 : iprop(⌜∀ x ∈ ids, DeadAt σ x⌝ ∗ metaInterp (GF := GF) mm) $$ [Hmi Hrest]
CerberusHeapLang/MallocListExhibit.lean:1233:        ihave H1 : iprop(⌜∀ id ∈ ids, DeadAt σ id⌝ ∗ metaInterp (GF := GF) mm) $$ [Hmi HD]
```

(15 code lines in 2 positive modules — DERIVED. The other 37 BEFORE hits
are the same prose/semantic-test lines listed AFTER.)

AFTER (`e9111d0`) — 37 lines (DERIVED count), verbatim:

```
CerberusHeapLang/CaseExhibit.lean:137:    substitution TAU (`Step.case_value` is the only rule that fires). -/
CerberusHeapLang/RegionLoopExhibit.lean:43:label-context rules; total twins. No `Step.*`, no per-step drive
CerberusHeapLang/DivergeExhibit.lean:38:forever). Deleting the `⌜1 + m ≤ k⌝` conjunct from `wpt.pre`'s jump
CerberusHeapLang/DivergeExhibit.lean:44:audit, L-2): `dg_self_step` is proved by `Step.run`. A client of the
CerberusHeapLang/DivergeExhibit.lean:98:  Step.run (jumpRedex?_run [] ra dgLoopSym [])
CerberusHeapLang/WseqExhibit.lean:18:only — relation rules (Step.wseq_pure/wseq_annot/wseq_ctx) + cone
CerberusHeapLang/WseqExhibit.lean:100:    is the engine's LETW-PURE TAU (`Step.wseq_pure` is the only rule
CerberusHeapLang/FibExhibit.lean:20:  rule (`wps_pure` / `Step.pure_eval` — one big-step engine
CerberusHeapLang/DisposeExhibit.lean:32:`blockSpecs_frame`; total twins). No `Step.*`, no per-step drive
CerberusHeapLang/AllocExhibit.lean:55:operational proof terms: no `Step.*`, no per-step drive equations in
CerberusHeapLang/Examples/ReadinessSmoke.lean:43:this module has zero direct references to the ghost maps / `CohG` /
CerberusHeapLang/StructExhibit.lean:627:operational proof terms in this section (no `Step.*`, no per-step
CerberusHeapLang/Examples/MirrorCoverage.lean:6:`Step` (Step.lean): regression witnesses that a construct shape the
CerberusHeapLang/Examples/MirrorCoverage.lean:21:the call IS `Step.call`'s successor (the callee installed, the frame
CerberusHeapLang/Examples/MirrorCoverage.lean:23:`Step.ret`'s (the value plugged into the captured context, the frame
CerberusHeapLang/Examples/MirrorCoverage.lean:26:`Step.store_eval` covers every such shape, and these two witnesses
CerberusHeapLang/Examples/MirrorCoverage.lean:36:`Step.run`): a negative test shows a derivation is impossible by
CerberusHeapLang/Examples/MirrorCoverage.lean:62:  Step.store_eval rfl hx rfl
CerberusHeapLang/Examples/MirrorCoverage.lean:72:  Step.store_eval rfl rfl hy
CerberusHeapLang/Examples/MirrorCoverage.lean:76:(the operand is not a value) is covered by `Step.kill_eval`, whose
CerberusHeapLang/Examples/MirrorCoverage.lean:88:  Step.kill_eval rfl hx
CerberusHeapLang/Examples/MirrorCoverage.lean:93:`Step.alloc_eval`, whose successor is the canonical alloc redex. -/
CerberusHeapLang/Examples/MirrorCoverage.lean:105:  Step.alloc_eval rfl rfl hn
CerberusHeapLang/Examples/MirrorCoverage.lean:112:CERTIFICATION instances: `engine_step_matchU` at `Step.call` and at
CerberusHeapLang/Examples/MirrorCoverage.lean:113:`Step.ret`, i.e. the shipped driver's round at the call configuration is
CerberusHeapLang/Examples/MirrorCoverage.lean:156:    frame — exactly `Step.call`'s successor. -/
CerberusHeapLang/Examples/MirrorCoverage.lean:165:    (Step.call rfl rfl (smokeFile_lookup_f ra) rfl)
CerberusHeapLang/Examples/MirrorCoverage.lean:169:    and plugs the value into the captured context — exactly `Step.ret`'s
CerberusHeapLang/Examples/MirrorCoverage.lean:179:    Step.ret
CerberusHeapLang/ProdExhibit.lean:37:`store_lit_sym_step`, proved by `Step.store_eval`) MOVED to
CerberusHeapLang/ProdExhibit.lean:39:statements unchanged) — so no `Step.*`, no per-step drive equations,
CerberusHeapLang/ProdLoopExhibit.lean:41:certified operational rounds (`Step.sseq_ctx (Step.create …)` +
CerberusHeapLang/ProdLoopExhibit.lean:42:`driverDone_step` chains) are DELETED — every `Step.*`/
CerberusHeapLang/ProdLoopExhibit.lean:147:`wpt_driver_done_alloc` → `prod_run_eqJ` — no `Step.*`,
CerberusHeapLang/ProdLoopExhibit.lean:709:docs/2026-09-02_qa1-notes.md). No `Step.*`, no per-step drive
CerberusHeapLang/MallocListExhibit.lean:73:No `Step.*`, no per-step drive equations, no state-interpretation
CerberusHeapLang/ListRevExhibit.lean:38:own `PtrEq` memop (Step.lean `Step.memop_ptreq`; the eqPtrval null
```

Classification of the 37 AFTER hits (for the manifest worker's negative
check; `scripts/test_unit.sh` NOT edited here):

| class | lines | reading |
|---|---|---|
| Genuine boundary crossing in a positive client (code) | **0** | the 15 BEFORE code lines are gone |
| Semantic-test module, CODE | MirrorCoverage 62, 72, 88, 105, 165, 179 (6); DivergeExhibit 98 (1) | `Examples/MirrorCoverage.lean` is the generated-engine mirror test by design (its header, line 6); `DivergeExhibit.lean:98` is the negative/unprovability test's engine fact `dg_self_step` (header line 44 discloses it, 2026-09-02 audit L-2) — a total derivation is refuted against the engine, which needs one engine step |
| Prose in a positive client / production wrapper stating the ABSENCE ("no `Step.*`") | RegionLoop 43, Dispose 32, Alloc 55, Struct 627, ProdExhibit 39, ProdLoopExhibit 41, 42, 147, 709, MallocList 73, ReadinessSmoke 43 (11) | self-descriptive negatives; a name-based negative check should either exclude comments or accept these |
| Prose naming an engine rule in an explanation (no code use) | CaseExhibit 137, Wseq 18, 100, Fib 20, ListRev 38, ProdExhibit 37, DivergeExhibit 38, 44 (8) | explanatory; the modules' code uses the `wps_*`/`wpt_*` rules |
| Prose in the semantic-test module | MirrorCoverage 6, 21, 23, 26, 36, 76, 93, 112, 113, 156, 169 (11) | its own header |
| `wps.pre`/`wpt.pre` | DivergeExhibit 38 (prose; already counted in the row above) | the only hit; no judgment unfolding in any client's code |

A negative check that greps CODE only (comments stripped) over the
positive-client set would read zero after this slice, with
`Examples/MirrorCoverage.lean` and `DivergeExhibit.lean` classified as
semantic tests — that classification is the manifest worker's (the
audit's "one authoritative classification of modules").

## 4. The census (DERIVED; pre = `docs/2026-09-03_f1-signatures-post.txt`, 2971 entries — NOT duplicated; post = `docs/2026-09-04_ar5-readout-signatures-post.txt`, 2971 entries)

Compared BY ENTRY (kind + name + printed type),
`scripts/signature_snapshot.lean` at the pre-commit tree (identical Lean
content to `e9111d0`):

- ADDED 3: `bigSepL_consequence`, `deadObj_consequence`,
  `deadRegion_consequence`.
- REMOVED 3: `deadNodes_dead`, `deadObj_dead_keep`, `deadRegions_dead`.
- CHANGED 0.
- UNCHANGED 2968 — including `DeadAt` (def, `Mem → Int → Prop`),
  `dispose_list_certified_production`,
  `malloc_list_certified_production`, `dlPost_readout`,
  `mlPost_readout`, `dlProd_readout`, `ψD`, `ψML`, `deadNodes`,
  `deadRegions`, `deadNodes_nil`/`_cons`/`_append`,
  `deadRegions_nil`/`_cons`, `regionOwn_deadRegions_ne`, `keep_pure`,
  `deadObj_dead`, `deadRegion_dead`, `deadObj_readout`,
  `deadRegion_readout`.

Pins (Audit.lean): 373 → 376 — the three ADDED lemmas, each measured
before pinning (`lake env lean` on a scratch import of
`CerberusHeapLang.Adequacy`, verbatim):

```
'CerberusHeapLang.deadObj_consequence' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.deadRegion_consequence' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.bigSepL_consequence' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No pin removed: none of the deleted helpers was pinned.

## 5. The documentation surfaces

- API.lean: the "ONE DOCUMENTED EXCEPTION" paragraph names the new
  lemmas and states the measured rule (a client module's text names none
  of `CohG`/`metaInterp`/`byteInterp`); the pure-memory-view row gains
  `DeadAt`; the Adequacy (partial) row lists the new `*_consequence`
  lemmas and drops the sentence that pointed clients at
  `deadObj_dead`/`deadRegion_dead`; those two are reclassified BELOW THE
  LINE (Heap's backing lemmas; statements and pins unchanged).
- ARCHITECTURE.md §5 (the projection paragraph — the client-boundary
  sentences only): the new lemmas, `DeadAt`, and the boundary rule as
  measured. No manifest/capability prose touched (the concurrent
  `ar5-manifest` worker's paragraphs).
- The two exhibits' headers and readout docstrings describe the change;
  their history sentences deliberately do NOT spell the internal names
  (so the boundary grep stays clean: "the coupling invariant and the
  metadata interpretation").

## 6. Deviations from the brief and decisions ([AGENT], each with its reason)

1. **(i) and (iii) are one pair of lemmas.** The brief's (i) "a single
   token implies the concrete readout under the projection" and (iii)
   "a postcondition-shaped `*_consequence` twin for dead tokens" both
   denote the projection's obligation shape
   `Φ ∗ metaInterp mm ∗ byteInterp mb ⊢ ⌜…⌝` under `CohG`; the
   post-level readout a client states (`readoutPost`, or
   `project_triple_pure`'s `hpost`) is `stateInterp_readout`/the
   projection applied to that composition, both already public. No
   additional post-level combinator was added — it would restate
   `stateInterp_readout` with the same `CohG`-premised hypothesis.
2. **(ii) is the GENERIC fold, not a dead-token-specific list lemma.**
   `bigSepL_consequence` folds ANY per-element consequence over a
   `[∗list]`; at the dead tokens the element consequence is
   `exists_consequence fun a => deadRegion_consequence hG id a n` (the
   dead list forgets the base). A dead-token-specific list face would
   fix one element shape: DisposeExhibit's list is `List (Int × Int)`
   read at `nd.1`, MallocList's is `List Int` — a `List Int` face would
   serve one exhibit and leave the other on the generic fold anyway
   (a consumerless lemma, KNOWN-OPEN-ITEMS C3's class). No `[∗map]`
   twin (`cellsOwn_consequence` is the map-shaped fold the exhibits
   use; a generic one would be consumerless).
3. **`deadNodes`/`deadRegions` redefined** as the `[∗list]` big
   separating conjunction (bodies changed; names, types, `_nil`/`_cons`
   (`rfl`) and every statement over them UNCHANGED in the census). The
   alternative — keeping structural recursion and proving a bridge
   `deadNodes ns ⊣⊢ [∗list] …` per exhibit — adds two lemmas that say
   the definition twice. iris-lean's `bigSepL_nil`/`bigSepL_cons` are
   `.rfl`, which is what makes the unfoldings `rfl`.
4. **`keep_pure` kept** (DisposeExhibit, moved to its own section): a
   BI utility (`(P ⊢ ⌜φ⌝) → P ⊢ ⌜φ⌝ ∗ P`), not a boundary crossing,
   with eight consumers in MallocListExhibit's distinctness bookkeeping
   (`regionOwn_ne`/`regionOwn_deadRegion_ne` lifts) outside this slice's
   class.
5. **`deadObj_dead`/`deadRegion_dead` reclassified below the line** in
   API.lean's tables (documentation only; statements, snapshot entries
   and pins unchanged). Their K5-era label "PUBLIC consequence faces" was
   the surface that invited the exhibits to open the metadata
   interpretation; the consequence-shaped faces are the new lemmas.
6. **A deterministic heartbeat timeout was hit once and fixed
   structurally, no option bump.** The first draft of `dlPost_readout`'s
   obligation was a single term-mode composition
   `(sep_consequence (bigSepL_consequence (fun nd => …) ns) (…)).trans (BI.pure_mono …)`;
   Lean reported `(deterministic) timeout at isDefEq, maximum number of
   heartbeats (200000)` at the `bigSepL_consequence` application (the
   receiver of `.trans` is elaborated without its expected type, so the
   element predicate `Φ` was a higher-order metavariable when
   `[∗list] x ∈ ns, ?Φ x` met `deadNodes ns`). Fix: tactic block with
   `unfold deadNodes`, `Φ` given explicitly, `refine … .trans ?_`; the
   same shape in `mlPost_readout`. Both compile in the normal budget
   (DisposeExhibit + MallocListExhibit 10.2 s wall together).
7. **First build's log lost.** The worktree's primed `.lake` was stale
   (five `*Exhibit`/EvalClass oleans missing, dated 2026-09-02) and the
   first `lake build` also re-elaborated 76 modules of the
   `.cerberus-ws` semantics dependency; its log was redirected to
   `/tmp`, which the sandbox exposes per-process (unreadable afterwards),
   so its wall time is by the clock only (≈ 12 min, 00:33 → ≈ 00:47).
   Every later log went to `cerberus-heaplang/.lake/ar5-logs/`
   (gitignored, deleted at slice end). A second `lake build`
   immediately after was a no-op replay (0.99 s wall), so the
   re-elaboration was a one-time trace refresh, not a recurring cost.
8. **Not done, by scope:** `scripts/test_unit.sh`, `scripts/*.lean`,
   `docs/CAPABILITY_MANIFEST.md`, README — the concurrent manifest
   worker's files. The FULL gate's manifest speedbump regenerated with
   NO drift at this tree, so this slice does not perturb the manifest.

## 7. Build cost (DERIVED from the logs' `time` lines; all through `scripts/capped`, `CERB_MEM_MAX=40G`, `grep -ci uncapped` = 0 in every kept log)

| step | wall |
|---|---|
| baseline build (stale prime + 76 semantics modules re-elaborated; log lost, §6.7) | ≈ 12 min by the clock |
| baseline re-run (no-op replay; the green pre-state, 373 pins) | 0.99 s |
| Adequacy alone (the new lemmas) | 4.7 s |
| whole package, first exhibit draft (red: the isDefEq timeout at DisposeExhibit) | 23.7 s |
| DisposeExhibit chain, second draft (red: one unsolved goal — a dropped `iexact`) | 3.9 s |
| DisposeExhibit + MallocListExhibit green | 10.2 s |
| whole package after API/ARCHITECTURE/Audit edits (Audit re-elaborated, 376 pins) | 3.3 s |
| FULL `test_unit.sh`, pre-commit tree | 8.3 s |
| FULL `test_unit.sh` at `e9111d0` | 8.5 s |

No pass approached the ~1 h tripwire; the Lean content of the slice
elaborates in seconds. Compiler warnings in the three edited modules: none
attributable to the slice (the package's pre-existing linter warnings are
KNOWN-OPEN-ITEMS C5).

## 8. The FULL gate at `e9111d0` (verbatim)

Run from the worktree root, `CERB_MEM_MAX=40G ./scripts/test_unit.sh`
(the runner's own lines; `grep -ci uncapped` = 0 and `grep -c 'uses
sorry'` = 0 over the whole log; the `GATE-EXIT` line is
`echo "GATE-EXIT=$?"` appended by the worker):

```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:576:0: CerberusHeapLang export pins: 376 trio-exact
info: CerberusHeapLang/Audit.lean:576:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (3396 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:576:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (5153 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (456 jobs).
ok: cerberus-heaplang build green
== speedbump: capability manifest (regenerate; red on a red row or drift) ==
cerberus-lean-proj env: switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_opam, git redirects active
ok: capability manifest regenerated, no drift
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — no core module imports an exhibit/example/production module
ALL GATES GREEN
./scripts/test_unit.sh  7.90s user 0.76s system 101% cpu 8.530 total
GATE-EXIT=0
```

(Between the gate-2 header and the three `info:` lines the log carries
the build's replay/warning lines, elided here; they are the package's
pre-existing linter warnings.) The commit `e9111d0` is the slice's Lean
and shop-window content; this record is the only later change.

## 9. Handoffs

- Manifest worker (`ar5-manifest`): the negative check's classification
  input is §3's table — after this slice the positive clients have zero
  code hits; `Examples/MirrorCoverage.lean` and `DivergeExhibit.lean`
  are the semantic-test modules with code hits by design.
- Range auditor: `deadObj_dead`/`deadRegion_dead` stay pinned and public
  in the snapshot sense (statements unchanged) while API.lean now lists
  them below the line — a documentation reclassification, §6.5; if the
  house wants the pins to track the line, that is a separate ruling.
