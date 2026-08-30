# Spike slice A — build notes (artifacts 1-3 + acceptance package)

[AGENT 2026-08-30] Slice-A worker record. Deliverables:
`RefinedCerberus/Spike/{Step,Heap,Lang,Rules}.lean`, wired into the
lib root before `Audit.lean` (the sweep covers them: 72 theorems, all
cones within the classical trio; the exhibit carries a curated pin).
Everything below is proved over `Step` — the hand-written engine
mirror; artifact 4 (engine certification of Step) is slice B and every
file header says so.

## Acceptance package status (all THEOREMS, all compositional)

| Item | Name | Status |
|---|---|---|
| small axiom store | `Rules.wp_store` | PROVED (UB-excluding, own-1) |
| small axiom load | `Rules.wp_load` | PROVED (UB-excluding, any dq) |
| FRAME | Iris `wp_frame_l/r` + `Rules.triple_frame` | PROVED |
| SEQ/BIND | `wp_bind` (real `Language.Context` for Csseq) + `Rules.wp_sseq` (value form) + `Rules.triple_seq` (assertion form) | PROVED |
| CONSEQUENCE / wp_wand | `Rules.triple_conseq` / `Rules.spike_wp_wand` | PROVED |
| triple definition | `Rules.triple` (P ⊢ WP e @ NotStuck; ⊤ — UB-exclusion IS NotStuck) | DEFINED |
| THE EXHIBIT | `Rules.exhibit` — {x ↦ - ∗ y ↦ a} store(x,7) {x ↦ 7 ∗ y ↦ a} by FRAME on `wp_store` + CONSEQUENCE | PROVED |
| anti-frame negative test | comment-fenced transcript at the end of Rules.lean (verbatim; stuck goal `⊢ y ↦c ty' ; bs'` from an empty spatial context) | RECORDED |

Supporting theorems: `wp_annot_reindex` + `wp_annot` (the annotation
layer, §D8 — the slice's principal technical finding), the Csseq
`Language.Context` instance, three pure-determinism lemmas, the Coh
coupling invariant with `storeM_success`/`loadM_success`/`Coh.store`.

## Design decisions ([AGENT] unless cited)

### D1. Values = `SpikeVal` (bare | one-annot-wrapped); the top-level REMOVE-ANNOT is absorbed into value classification
`is_irreducible` (Core_reduction.lean:293) has exactly two terminal
shapes: a bare pure value and a ONE-layer `Eannot`-wrapped value.
`SpikeVal = pure v | annot ds v` mirrors that. RECORDED DIVERGENCE:
at an empty context the engine additionally taus `{A}v --> v`
(step_ctx's `(CTX, Eannot(value))` arm) before `Step_done2 v`. Step
does NOT contain that unwrap — the iris `ToVal` interface requires
values not to step and `toVal` to be a partial bijection, so the
annotated form is a value here, carrying the same payload. Slice B's
readout statement must compose `toVal e = some (.annot ds v)` with
the engine's `{A}v --> v --> Step_done2 v` tail. This is NOT a
quotient: terms are raw generated AST throughout; only the
terminal-form classification differs, by exactly one engine tau.

### D2. No aid enters the fragment's terms (R-i milder than the recon feared)
step_action's positive non-excluded Store0/Load0 continuations build
`[DA_pos [] fp]` — the aid parameter is UNUSED in the dyn-annots
(Core_reduction.lean:424; the aid matters only for DA_neg/exclusion,
i.e. negative actions, outside the fragment). So Step needs no aid
index at all, and the recon's fallback ("aid as a Step index the
judgments existentially hide") was unnecessary. The small axioms hide
only the FOOTPRINT existentially. The recon's open unknown (identity
of the 2 dyn-annotations on the final seq value) is settled:
`[DA_pos [] fp_store] ++ [DA_pos [] fp_load]` via LETS-ANNOT + ANNOTS.

### D3. Canonical node shapes; `isEmpty` guards in `toVal`
Step's rules use the canonical shapes (`[]` annot lists, `()` bty)
that `mk_value_e`/`mk_value_pe` (Core_aux.lean:302,645) and authored
fragment programs produce. The engine's redex patterns accept
arbitrary annotation lists in some positions (e.g. LETS-PURE matches
`Expr pe1_annots (Epure pe1)`); Step takes the canonical instances —
exact on the fragment cone, a sub-relation elsewhere. Needed for
`ToVal.coe_of_toVal_eq_some` (partial bijectivity) and for
`Context.primStep_fill_inv`. Mechanically, `toVal` checks the lists
by `isEmpty` GUARDS rather than `[]` patterns so the compiled matcher
dispatches on expression constructors only and reduces on non-value
shapes with symbolic annotation lists (a `[]`-pattern version leaves
`toVal (Expr a (Esseq ...))` stuck for symbolic `a`, which broke the
Language instance's `rfl` obligations — found the hard way).

### D4. The rule set (7 rules) and the one load-bearing guard
store / load (request+discharge+continuation fused, mirroring the
recon §3.3 mini-drive), sseq_pure / sseq_annot (LETS-PURE/LETS-ANNOT
at wildcard patterns — `update_env (CaseBase (none,_))` is the env
identity, Core_aux.lean:861-868, so the frozen env is honest),
sseq_ctx / annot_ctx (get_ctx descent + apply_ctx rebuild), and
annot_merge (ANNOTS). `annot_ctx` carries `annotRooted b = false`,
mirroring get_ctx's arm ORDER (the double-annot arm precedes
Cannot-descent, Core_reduction.lean:375) — without the guard Step
would race the merge, which the engine never does. No irreducibility
guard is needed on sseq_ctx: no Step rule fires on an irreducible
term (values by val_stuck; the annot-value shape by rule shapes).

### D5. `loc` in the memory ops
The engine passes `loc' = if isLibraryLocation loc then current_loc
else loc` to loadM/storeM; loc only reaches error payloads, never the
NDactive result or the state. The rules pass the action's own loc;
fragment locations are not library locations. Slice B should either
carry the ¬isLibraryLocation side condition or prove loc-irrelevance
of the active path (trivial).

### D6. Ewseq: NOT included
The plan said "weak (Ewseq) if free". It is not free: three more
rules and a third disjunct in every Esseq-shaped inversion, a second
Context instance, and two more det lemmas. Deferred; the LETW rules
are shape-identical to LETS (one_step0's Ewseq arms) so the extension
is mechanical when wanted.

### D7. Heap: allocation-rooted cells; the Coh invariant; `StorableAt`
Granularity per the recon §5.2 recommendation (recorded reasoning in
Heap.lean's header): ghost cell per allocation id =
`(addr, ctype, byte list)`; the byte list is the Caesium-shaped value
payload (R2). `Coh σ m` additionally pins
`σ.lastUsedUnionMembers = []` and `σ.funptrmap = []` (both are
fragment-invariant: fragment pointers are `PVconcrete none`, and
`StorableAt.fpm` guarantees funptrmap-neutral serialization) — this
makes the engine's `reconstructValue` a pure function of the cell
(`decodeCell`), which `wp_load`'s postcondition needs. Pairwise
range-disjointness of cells is a Coh clause (needed to show untouched
cells re-read unchanged after a store). `StorableAt ty mv` bundles
the type-compat fact (kills storeM's NON-UB `Other` arm — the R4
finding), fpm-neutrality, and exact-footprint serialization length;
it is the spike-scale precursor of the donor's `v ◁ᵥ ty` and for the
concrete int-7 instance all three components are `rfl`.

### D8. The annotation layer — the slice's principal finding (R-i's real cost)
The Esseq frame IS a genuine iris `Language.Context` (wp_bind works
on real strong sequencing — R6's "bind layer dissolves" confirmed on
live proofs). The Eannot frame is NOT: for an annot-rooted body the
engine merges at the root instead of descending, so
`Context.primStep_fill` is false. Worse, the bind-style inverse
(`WP (Eannot ds e) {Φ} ⊢ WP e {Φ ∘ merge}`) is UNPROVABLE in the
logic: at `e = ofVal (.annot ds' v)` the premise is a WP of a
non-value, whose postcondition cannot be extracted without owning the
state interpretation. The workable route, proved here:
- `wp_annot_reindex` (Löb): wraps of the SAME body differing only in
  the dyn-annotation payload step in LOCKSTEP forever (annotations
  never influence fragment stepping), so WPs transfer along any
  `merge`-compatible postcondition translation. The merge case
  re-enters the induction at `(dsA++ds2, dsB++ds2)` — annotation
  payloads are the only moving part.
- `wp_annot` (Löb): value cases directly; annot-rooted body takes the
  one merge step and exits THROUGH the reindexing lemma (premise
  `WP (Eannot ds2 c) {Φ ∘ merge ds}` is reindexed to
  `WP (Eannot (ds++ds2) c) {Φ}` — no inversion needed); plain bodies
  recurse in the Cannot frame.
Both proofs follow the `wp_strong_mono`/`wp_bind_iff` Löb templates
(WeakestPre.lean). This is the reusable full-build asset: any Core
construct that re-wraps continuations in Eannot will lean on it.

### D9. UB exclusion (R4) as delivered
`triple P e Ψ := P ⊢ WP e @ NotStuck; ⊤ {{Ψ}}` — safety is the
NotStuck obligation, and Step has NO step on any NDkilled arm, so a
proved triple asserts the killed channel (UB and non-UB `Other`
alike) is unreachable under the precondition. Per-arm accounting is
in wp_store/wp_load's docstrings; the only failure the load points-to
cannot exclude by itself is the _Bool trap representation, which is
the explicit `cellLoadTrap = false` premise.

### D10. Seq statement shapes
`wp_sseq` is the value-level rule: `WP e1 {v, ▷ WP e2 {w, Φ
(mergeInto v w)}} ⊢ WP (lets _ = e1 in e2) {Φ}` — `mergeInto`
records how the bound value's annotations prefix the continuation's
value (the R-i flow made explicit). `triple_seq` is the acceptance
form {P} e1 {Q} → {Q} e2 {R} → {P} e1;e2 {R} with assertion
postconditions (wildcard binding — the fragment's form per recon
R-ix; sym-binding patterns would pull the pexpr evaluator into the
judgments and are out of fragment).

### D11. Ghost-state non-vacuity
`SpikeGF` (Lang.lean) is a concrete functor list with a
`SpikeGpreS SpikeGF` instance (HeapLangS mirror minus prophecies), so
the prerequisites class is inhabited. The bundled `SpikeGS` (ghost
names + world satisfaction) is constructed by allocation inside an
adequacy proof — exactly where HeapLang builds `HeapLangGS` — and is
slice B's adequacy obligation. Until then, theorems assuming
`[SpikeGS hlc GF]` rest on a class whose pre-stage is witnessed but
whose bundled stage is not yet constructed in-repo. HONEST GAP,
named in Rules.lean's header.

### D12. Operational finding: cross-module matchers never bridge on stuck scrutinees
Two syntactically identical `match` expressions compiled in different
modules produce distinct matcher constants that do NOT unfold during
defeq/simp while the scrutinee is stuck (Lean unfolds matchers only
on constructor scrutinees). Consequence: restating an engine-internal
inline match (e.g. loadM's trap guard) in a hypothesis is unusable by
`rw`/`simp`/`exact` against the unfolded engine goal; the resolution
in `loadM_success` is case-explosion of the scrutinees until both
matchers reduce. Slice B should prefer hypotheses phrased via the
engine's own NAMED functions wherever they exist.

## Recon claims checked against the build

- CORRECT and load-bearing: the type tower and verbatim term
  skeletons (§1.3 compiled unchanged into storeExpr/loadExpr); the
  one-layer memM shape (applyMemM is exactly the recon's); the memM
  seam recommendation (wp_store/wp_load discharge into ONE
  application of the real storeM/loadM); GenHeap fit; the
  granularity recommendation; the minimal-context freeze; wildcard
  env-identity.
- CORRECTED: recon §5.1's sketch signature `toVal : CoreExpr →
  Option value` cannot satisfy `ToVal`'s partial-bijection laws (the
  two terminal forms would collide); the value type must distinguish
  them (`SpikeVal`, D1).
- CORRECTED: recon §5.3's "the seq rule is a lifted-step lemma ...
  not a monadic bind" — in fact wp_bind IS used (the Csseq Context is
  real); the beta is indeed a lifted pure step; the ingredient the
  recon did not predict is the annotation-commuting lemma (D8).
- OVERCAUTIOUS: R-i's aid threading (D2) — no aid in terms at all.
- Recon unknown resolved: the final 2 dyn-annotations are the store's
  and load's `DA_pos [] fp`, concatenated by ANNOTS.
- Still open (slice B): perf regime of step_ctx unfolding in proofs
  (never needed in slice A — Step is the proof-facing relation and
  the memM facts were per-operation), R-ii/R-iii context supplies.

## Derisk register after slice A (derived tallies)

- R1 (seam): unchanged from recon (slice B's finding to close).
- R2 (points-to basis): held at spike scale — the cell carried both
  small axioms, frame, and the exhibit; byte-splitting growth step
  still registered. OPEN→largely retired, final word after S1.
- R3 (WP form): RETIRED — iris WP with full mask/fupd discipline in
  actual use (atomic lifts, step fupds, Löb).
- R4 (UB channel): RETIRED at statement level (D9); engine-level
  meaning lands with artifact 4.
- R5 (provenance honesty): RETIRED — `x` is a real PointerValue; the
  ↦ carries the allocation id and concrete address.
- R6 (bind story): RETIRED — Iris bind over real Esseq proved and
  exercised by the seq rules; the annotation layer (D8) is the
  named residual cost.

## Gate status

`./scripts/test_unit.sh`: ALL GATES GREEN (grep ban + capped build;
capped falls back uncapped-loud in-sandbox per the recorded ruling).
In-build audit: axiom sweep over 72 RefinedCerberus theorems, all
cones within the classical trio; new curated pin on
`RefinedCerberus.Spike.exhibit` (exact trio). No sorry, no
non-kernel methods, no new axioms, no maxRecDepth/heartbeat bumps.

## Anti-frame transcript

See the comment block at the end of Rules.lean (verbatim `lake env
lean` output, 2026-08-30): the derivation without the y-cell in the
precondition is stuck on exactly `⊢ y ↦c ty' ; bs'` with an empty
spatial context after `iframe` consumes the x-cell — locality is
real, not decorative.
