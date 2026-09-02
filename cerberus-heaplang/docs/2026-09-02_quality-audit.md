# 2026-09-02 quality audit — cerberus-heaplang @ `dacface` (branch `heaplang-alloc-arc`)

Independent auditor, dependency-tracing round ([USER 2026-09-02]: "the
feature set is frozen while we get this to a really strong state just
in terms of quality … we're going to do another audit round so we might
find other areas for improvement"). Graded against
`../../docs/AUDIT-BRIEF.md`. Read-only on the tree; this file is the
only write. Every quoted block is verbatim from the tree or from the
tracing script's output at this head; tallies I computed are labeled
DERIVED. Provenance of every judgment here is [AGENT] (auditor).

## 1. Executive verdict

Yes: this is legitimately a classical separation logic over the real
Core semantics, on iris-lean, whose closed-program exports are
statements about cerberus-lean's execution. Traced by proof term (not
by name): all 109 `trioExports` are theorems with axiom set exactly
`[Classical.choice, Quot.sound, propext]`; every drive-lane export's
cone passes through `engine_step_matchU` → `step_ctx`/`storeM`/`loadM`/
`allocateObject`; every production export's cone passes through
`loop_step_frag` → `driver2_done` → `finalize_done` → `prod_run_eqJ`
and reaches `runND`/`_root_.drive`/`initial_driver_state`; every rule in
the README's rule table exists, is a theorem, and (with three
assertion-law exceptions) is consumed by an exhibit. No unsound or
vacuous rule was found; the instance-binder-in-`⌜⌝` hazard has zero
occurrences. Strength, in the brief's terms: the adequacy chain and
the trust story hold; the LOGIC is not yet pristine — one coverage
hole inside the declared fragment (High: the engine's operand-
evaluation arms for `store` and `save` are mirrored only in narrow
sub-cases, and the two flagship production programs are visibly
contorted around it), a dead straight-line production lane still
drawn on the trust diagram, a profile-pinned base stratum, and a
list of partial/total asymmetries and non-classical side conditions
(Medium). Fix those and it is fairly called "classical SL over Core
minus dispose and procedures".

## 2. Method and coverage

**Instrument.** A Lean script over the built environment (Appendix A;
run from `cerberus-heaplang/` as
`CERB_MEM_MAX=48G ../scripts/capped ~/.elan/bin/lake env lean <script>`,
after `pgrep -af 'lake build'` showed no build running). It computes,
with `Lean.Expr.getUsedConstants` over type AND value and a memoized
DFS:

- for each of the 109 names in `CerberusHeapLang.Audit.trioExports`:
  kind, module, `collectAxioms`, the FULL transitive constant closure
  (engine and Iris constants expanded, not just package constants),
  membership of 68 named "spine" theorems in that closure, name-suffix
  landmarks (`wp_strong_adequacy_gen`, `twp_total`, `genHeap_init`,
  `step_ctx`, `storeM`, `loadM`, `allocateObject`, `eqPtrval`, `runND`,
  `drive`, `initial_driver_state`, `driver2`, `finalize`,
  `action_request_sequential2`), every `opaque`/`axiom` leaf reached,
  and the export's direct in-package VALUE consumers (proof-term
  references, internal-detail consumers attributed to their parent,
  `Audit` excluded);
- for 86 rule/law names from the README rule table and the API
  header: existence, kind, module, direct consumers, and which of the
  15 exhibit modules (`*Exhibit`, `Examples.ReadinessSmoke`) have the
  rule in their transitive package cone (the manifest's technique,
  applied to every advertised rule, not only the 18 `Frag` rows);
- theorems of the nine logic modules with no direct value-consumer
  anywhere in the package;
- the hazard scan: every non-internal package constant's pretty-printed
  type, each `⌜…⌝` segment checked for `SpikeGS`/`[inst`, plus a census
  of `∀ [` binders (to confirm the intended instance binders survive
  elaboration);
- logic-module constants whose TYPE mentions `fmapEmpty` or the
  `spike*` profile constants;
- `Frag`'s constructor list from the environment.

Coverage counts (trace output, verbatim): `# audit_trace — 109 exports
in Audit.trioExports`, `package constants: 3636`. Full-cone sizes per
export range 8,496 (`engine_complete`) to ~14k constants. Manual
reading: every declaration header of `Rules`/`Wps`/`Wpt`/`Adequacy`/
`TotalAdequacy`/`Round`/`ProdEntry`/`ProdLoop`/`DriverCollapse`/`Lang`/
`EnvLaws`, the `Step` and `Frag`/`StraightFrag` inductives, the Heap
definitions and laws, every exhibit's exported statement, the README,
WALKTHROUGH, manifest, `API.lean`, and the engine's
`Core_reduction.lean` arms for `Store0`/`Esave`.

Re-verification of the axiom claim (trace, DERIVED from 109 lines of
the form `- axioms: [Classical.choice, Quot.sound, propext]`): 109/109
trio-exact; `sorryAx` absent from every cone.

## 3. Findings

### H-1 (High — coverage inside the declared fragment). The engine's operand-evaluation arms for `store` and `save` are mirrored only in narrow sub-cases; `Frag.save` admits shapes no rule and no mirror step covers; the production programs are contorted around both.

**Claim** (README, "Scope, exactly", verbatim): "`store`/`load`/`create`
actions (both the evaluated-operand and the operand-evaluation
forms), … `Esave`/`Eif`/the context-discarding `Erun`". Manifest:
`Frag.save` → `wps_save`, `Frag.store_op` → `wps_store_eval`.

**Tree's truth.**

Store, operand-evaluation form — the mirror and the rules require BOTH
operands to be non-values (`Step.lean`, `Step.store_eval`; the same
`hnv2`/`hnv3` pair on `Frag.store_op` (Soundness.lean:3581 ff.),
`wps_store_eval` (Wps.lean:1595), `wpt_store_eval` (Wpt.lean:647)):

```lean
  | store_eval {a : List annot} {loc : CerbLocation.Loc}
      ...
      (hnv2 : valueFromPexpr pe2 = none)
      (hnv3 : valueFromPexpr pe3 = none)
      (hv2 : evalPexpr M.tagDefs M.extern ρ pe2 = some (Vobject (OVpointer pv)))
      (hv3 : evalPexpr M.tagDefs M.extern ρ pe3 = some cv) :
```

The engine's arm fires whenever the operand triple is NOT all values
and re-evaluates all three (`.cerberus-ws/lean_frontend/generated/
Core_reduction.lean:424`, `step_action`, verbatim, whitespace
collapsed):

```
| some _, some _, some _ => ACTION_ILLTYPED "Store" | _, _, _ =>
ACTION_EVAL "eval operands of Store" ( stExceptUndef_bind (full_eval_pexpr1 pe1)
(fun (cval1 : value) => stExceptUndef_bind (full_eval_pexpr1 pe2) (fun (cval2 : value) =>
stExceptUndef_bind (full_eval_pexpr1 pe3) (fun (cval3 : value) =>
stExceptUndef_return (wrap (Store0 is_locking (mk_value_pe cval1) (mk_value_pe cval2) (mk_value_pe cval3) mo1)))))
```

So `store(int, p, 7)` with `p` a symbol and `7` a literal — the mixed
shape — is an engine step and a mirror-stuck configuration. (The memop
rule already has the general shape: `wps_memop_eval`'s premise is
`hnv : valueFromPexprs [pe1, pe2] = none`, i.e. "not all values".)

Save — `Frag.save` (Soundness.lean:3581 ff.) admits ANY parameter
initializers:

```lean
  | save {sb : sym × core_base_type}
      {ps : List (sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
      {body : CoreExpr} :
      Frag body → Frag (saveRedex sb ps body)
```

while the mirror and both rules require literal values
(`Step.save`: `(hvals : valueFromPexprs (saveParamPexprs ps) = some cvals)`;
`wps_save` Wps.lean:1037 and `wpt_save` Wpt.lean:599 carry the same
`hvals`). The mirror's own docstring (Step.lean, `Step.save`):
"Non-value parameter pexprs take the engine's EVAL arm (small-step
`eval_pexpr1` mapM) — not mirrored this slice (absence of a step;
authored fragment saves carry value initializers)." The engine
(`Core_reduction.lean:353`, `one_step0`, verbatim, whitespace
collapsed): `| some cvals => /- reduction: SAVE (tau part) -/ TAU
"Esave" (…) e | none => /- reduction: SAVE (eval part) + SAVE-UNDEF -/
EVAL "Esave" (…)`.

The contortion, in the tree's own words (ProdLoopExhibit.lean, the
docstrings of `lrProdPrefix` and `ctrBody`, verbatim): "The build
prefix: two creates (pointers BOUND), three constant binds (the
store-EVAL arm needs non-value operands), four field stores through
the bound pointers, then the jump into the registered loop with (prev
:= NULL, cur := node 1)." and "store 7 through the pointer ARGUMENT
(the stored constant bound per iteration — the mirrored store-EVAL arm
requires non-value operands)". Concretely, `counterProdProg` binds
`ctrSSym := 7` inside the loop body to store it, and enters the loop
with `Erun ra ctrLoopSym [PEval (ivVal n), PEsym ctrPSym]` from OUTSIDE
the `Esave`, whose own initializers are dummies (`PEval (ivVal 0)`,
`PEval nullVal`) — because `save loop(c := p)` has no step.

**Consequence.** No false theorem: a mirror-stuck configuration
defeats `NotStuck`, so the affected programs are unprovable, not
mis-proved (fail-closed absence, as the Step header says). But (i) the
fragment as DECLARED in the README and as ACCEPTED by `Frag` (the
adequacy premise) is wider than what has a rule: `Frag.save` is a
`Frag` member for which neither a rule nor a mirror step exists — the
manifest's row "`Frag.save` → `wps_save`" is true only for the
literal-initializer sub-case; (ii) the two most common shapes of
elaborated C — storing a constant through a pointer variable, and
entering a loop with its live variables — are outside the fragment,
and neither is listed under "Deliberately not here" or in the
divergence table (which lists `Ewseq` at binder patterns, `Ecase`'s
EVAL arm, pure exits beyond `PEsym`, the memop family, the
symbol-binder beta at annotated values; the R-03 row mentions "save's
EVAL round" only as a refusal channel).

**Fix (statements).** Mirror the engine's arms at their true
generality, in the shape `memop_eval` already has:

```
Step.store_eval : valueFromPexprs [pe1, pe2, pe3] = none →
  evalPexpr … pe2 = some (Vobject (OVpointer pv)) → evalPexpr … pe3 = some cv →
  Step M (storeOpRedex loc ann ty pe2 pe3 mo, ρ, σ) (storeExpr loc ann ty pv cv mo, ρ, σ)
Step.save_eval  : valueFromPexprs (saveParamPexprs ps) = none →
  evalPexprs … (saveParamPexprs ps) = some cvals →
  Step M (Esave sb ps body, ρ, σ) (Esave sb (ps with each initializer := PEval cval) body, ρ, σ)
```

with `Frag.store_op`/`wps_store_eval`/`wpt_store_eval` relaxed to the
same premise (`evalPexpr` is the identity on `PEval v`, so the
all-values case is excluded by the premise and nothing else changes),
plus `wps_save`/`wpt_save` at `evalPexprs … = some cvals` (the current
`valueFromPexprs` form becomes the special case). Minimal alternative
if the arc is to stay frozen: narrow `Frag.save` with the `hvals`
premise so the adequacy premise says exactly what is covered, and add
both restrictions to "Deliberately not here". Either way the two
production programs should then be restated in their natural shape.

### M-1 (Medium — duplicated rule family; trust-diagram drift). The straight-line production lane is a dead island, larger than the two names flagged, and the README still draws it as live.

**Claim.** README trust diagram (README.md:377): "generic driver
collapse (DriverCollapse.lean: loop_step_frag, prod_loop_done,
driver2_done, finalize_done — proved from the driver's OWN round
functions …". Module table (README.md:584) headline for
`DriverCollapse.lean`: "`loop_step_frag`, `prod_loop_done`,
`driver2_done`, `finalize_done`". WALKTHROUGH §2 item 8 and §5 name
`prod_loop_done` likewise. `Soundness.lean`'s headline names
`engine_complete`. All four are `trioExports`.

**Tree's truth** (trace output, verbatim):

```
engine_complete  [theorem; Soundness] | direct in-package consumers (1): prod_loop_done
prod_loop_done  [theorem; DriverCollapse] | direct in-package consumers (1): prod_run_eq
prod_run_eq  [theorem; ProdEntry] | direct in-package consumers (1): sem_triple_prod
sem_triple_prod  [theorem; ProdEntry] | direct in-package consumers (0):
```

and no live production export reaches `prod_loop_done` — e.g.
`exhibitA_prod … | spine reached: Decomp.step_factor, launchResources,
spikeCells_alloc, loop_step_frag, driver2_done, finalize_done,
wpt_driver_done_alloc, wpt_driver_aux, prod_run_eqJ, drive_after_setup,
…` (no `prod_loop_done`, no `engine_complete`). `engine_complete` is
stated over `StraightFrag` (Soundness.lean:2058: `(hf : StraightFrag e)
… ∃ o, engineOutcomes aid e (ev0 :: evs) σ = [o] ∧ EngineMatch e (ev0
:: evs) σ o`), a six-constructor inductive whose only other users are
`prod_loop_done`, `prod_run_eq`, `sem_triple_prod` and its own lemmas.
`engine_complete_loadU`/`_createU` (trioExports) are consumed only by
`cerberusRound_refused_load`/`_create`, which are consumed by nothing.

**Consequence.** The live production lane is `Decomp.step_factor →
loop_step_frag → driverDone_step → wpt_driver_aux →
wpt_driver_done(_alloc) → prod_run_eqJ`. The island
{`StraightFrag`, `engine_complete`, `prod_loop_done`, `prod_run_eq`,
`sem_triple_prod`} is a second, older collapse of the same pipeline
(the "conditioned generic production face … no consumer in the package
since P2" that the README registers names only the last two). Not a
soundness issue — everything is trio-exact — but a duplicated rule
family with the trust diagram pointing at the dead copy.

**Fix.** Operator decision, my view below (§5): retire the five
together (delete, or move to a `Legacy`-labeled module outside
`trioExports`), redraw the diagram's collapse row as
`loop_step_frag, driver2_done, finalize_done; wpt_driver_done(_alloc);
prod_run_eqJ`, and drop `engine_complete` from `Soundness.lean`'s
headline in favour of `engine_step_matchU`.

### M-2 (Medium — profile leak into a logic module; non-classical base rules). The base stratum's sequencing/frame/consequence rules are pinned to `spikeCtx` and consumed only by the spike exhibits.

**Claim.** README "Registered divergences": "The tag-definition
environment is an explicit parameter of the heap predicates and rules
(`pointsToCell tds …`, `M.tagDefs`)"; README "The logic": three strata,
the base one with "`wp_store`, `wp_load`, `wp_sseq`, `triple_frame`,
`triple_conseq`, `triple_seq`".

**Tree's truth** (trace §E, verbatim): "Rules (4): wp_sseq[spike*],
wp_annot_reindex[spike*], wp_annot[spike*], wp_env_invariant_stable[spike*]";
Heap/Wps/Wpt/TotalAdequacy: 0. `triple` (Rules.lean:841) is defined at
`spikeEnv`/`spikeCtx` (WALKTHROUGH §3.2 quotes it: `triple P e Ψ := P ⊢
WP ⟨e, spikeEnv, spikeCtx⟩ …`), so `triple_frame`/`triple_conseq`/
`triple_seq`/`exhibit`/`exhibitC_triple` are at `tagDefs = fmapEmpty`
by definition (`spikeCtx.tagDefs = fmapEmpty := rfl`, Step.lean:1894).
`triple_seq` (Rules.lean:1025) is not the classical rule:

```lean
theorem triple_seq [SpikeGS hlc GF] {P Q R : IProp GF}
    {bty : core_base_type} {e1 e2 : CoreExpr} (hf : EnvStable e1)
    (h1 : triple P e1 (fun _ => Q)) (h2 : triple Q e2 (fun _ => R)) :
    triple P (sseqExpr bty e1 e2) (fun _ => R) := by
```

(an extra `EnvStable e1` premise; value-blind posts). Consumers (trace
§B): `wp_sseq` → `provenA`, `triple_seq`; `triple_frame`/`triple_conseq`
→ `exhibit`, `exhibitC_triple`; `wp_annot` → `wp_sseq`; nothing outside
`Exhibit.lean`/`Examples/Layout.lean`. `wp_store`/`wp_load` ARE generic
in `M` (Rules.lean:177, 285).

**Consequence.** The "base stratum" the README presents as one of three
is, apart from the two small axioms, the spike-era lane at a fixed
profile; the live logic's sequencing/frame/consequence are `wps_*`/
`wpt_*`. A reader comparing the three strata finds the base one
narrower in three unrelated ways (fixed context, `EnvStable`,
value-blind posts).

**Fix.** Either generalize (`triple (P) (e, ρ, M) Ψ`; `wp_sseq`,
`wp_annot`, `wp_annot_reindex` over `{M}` exactly as `wp_store` is —
their proofs use nothing of `spikeCtx` a generic `M` lacks, the
statement-stratum twins being the evidence) and state `triple_seq`
classically (`triple P e1 Q → (∀ v, triple (Q v) e2 R) → triple P (e1;
e2) R`, with `EnvStable` discharged inside or made unnecessary by
quantifying `ρ`); or demote in the docs: "the base stratum is the two
small axioms `wp_store`/`wp_load`; sequencing, frame and consequence
are stated at `wps`/`wpt`", and move `wp_sseq`/`triple*` next to the
spike exhibits.

### M-3 (Medium — partial/total asymmetry). The two statement strata do not have the same rule set where the construct is meaningful at both.

**Tree's truth** (declaration index of Wps.lean/Wpt.lean; trace §B).
Partial without a total twin: `wps_load` (the `pointsToCell` load; the
total stratum has `wpt_store_cell` but no `wpt_load_cell`/`wpt_load`),
`wps_case_value`, `wps_wseq`, `wps_fupd`. Total without a partial twin:
`wpt_mono_Ls` (no `wps_mono_Ls`), `blockSpecsT_mono` (no
`blockSpecs_mono`), `wpt_det_step`. Naming: `wps_store` ↔
`wpt_store_cell`, `wps_load` ↔ (none). README states the `Ecase`/`Ewseq`
half honestly ("partial stratum only") but not the `pointsToCell`-load
half (its table lists `wpt_load_at, wpt_store_at, wpt_load_cell_at,
wpt_store_cell_at, wpt_store_cell` — accurate, silent on the gap).

**Consequence.** A total-correctness client cannot load through a
whole-cell `pointsToCell` without first opening it to a view; a total
client with `Ecase`/`Ewseq` has no rule. Neither is unsound; both are
holes in "every construct at both strata where meaningful".

**Fix.** `wpt_load` mirroring `wps_load` (same premises, `3 ≤ k`);
`wpt_case_value` is a direct instance of `wpt_det_step` (the case step
is deterministic and state-independent: `Step.case_value`);
`wpt_wseq` is the `wpt_seq` clone (as `wps_wseq` is of `wps_seq`);
`wpt_fupd` follows from the value clause's `|={⊤}=>`; `wps_mono_Ls` and
`blockSpecs_mono` by the same Löb/induction scaffolding as
`wps_wand`. Rename `wpt_store_cell` → `wpt_store` (or `wps_store` →
`wps_store_cell`) so the two strata read alike.

### M-4 (Medium — side conditions not in clean form; representation leaking into public statements).

(a) **Redex-discipline premises that are derivable.** `wps_pure`
(Wps.lean:1121) `hnv : valueFromPexpr pe = none`; `wps_load_eval`
(:1160) `hnv2`; `wps_store_eval` (:1595) `hnv2`, `hnv3`; and the `wpt_`
twins (Wpt.lean:616, 631, 647). `evalPexpr` is the identity on `PEval
v` (Step.lean:617: `| Pexpr _ _ (PEval v) => some v`), so in the
excluded case the rule's conclusion is the premise verbatim; the
premises exist only because the mirror distinguishes the redex shapes.
Cleaner: drop them (the rule then covers both forms), or — for the
store — the "not all values" premise of H-1. `Frag.case_value`'s
`hbsz : ∀ e', select_case … = some e' → esize e' ≤ esize (caseRedex …)`
appears derivable (`esize` counts expression nodes only and
`select_case` substitutes symbols in a branch of `pats`; not verified
here — if it holds, it is a lemma, not a constructor premise).

(b) **Two vocabularies for "storable".** `wps_store` takes
`(hst : StorableAt M.tagDefs ty mv)` (a five-field structure,
Heap.lean:173); `wps_store_at`/`wpt_store_at`/`wps_store_cell_at`/
`wpt_store_cell_at` inline four of its fields by hand (`hcompat`,
`hfpm`, `hbytes`, `hlen`/`hlenimg`). Cleaner: `StorableAt` everywhere
(strictly stronger by one field; or a two-field `StorableView`).

(c) **The client proves decode-inertness of a spliced image.**
`wps_store_cell_at`/`wpt_store_cell_at` carry `(hdec' : decIndep
M.tagDefs a aty (spliceBytes off (memValueToBytes M.tagDefs [] mv).2
bs))` — a property of the whole allocation image after the store,
which the client must establish for every store into a sub-range. This
is `cellOwn`'s bundled `decIndep` payload surfacing as a rule premise.
Cleaner: a lemma `decIndep_splice` (from `StorableAt.stored_dec` and
`decIndep … bs`) if the engine's `reconstructValue` admits it for the
array/struct constructors the fragment uses; otherwise the payload
belongs on the view, not the whole-cell bundle.

(d) **Two conditional rules where one suffices.** `wps_if_true`/`_false`
(and `wpt_`) take the guard's verdict as a META-level premise `hg :
evalPexpr … g = some Vtrue`. Classical form: one rule with the verdict
inside the logic — `⌜evalPexpr … g = some (boolValue b)⌝ ∗ wps M Ls Ψ
(if b then e2 else e3) ρ ⊢ wps M Ls Ψ (Eif g e2 e3) ρ` — so a guard whose
value is known only from Iris-level facts needs no meta case split.

(e) **Annotation-list asymmetry.** `wps_pure`, `wps_annot`, `wpt_pure`,
`wpt_annot` are stated at `Expr ([] : List annot) …` while `wps_if_*`,
`wps_save`, `wps_run`, `wps_seq*` take `(a : List annot)`. Cleaner:
`a` everywhere (the mirror's `pure_eval` and `annot_*` steps are
already annotation-generic).

(f) **The footprint annotation in the small axioms' posts.** `wps_store`'s
continuation is `∀ fp, pointsToCell … -∗ Ψ (SpikeVal.annot [DA_pos []
fp] Vunit) ρ` (likewise `wps_load*`, `wpt_*`): the engine's `DA_pos`
residue and its footprint are universally quantified in every client
proof. Registered as deliberate ("REMOVE-ANNOT value protocol"), and
`wps_seq` absorbs it via `mergeInto`; still, the textbook `{p ↦ -}
store(p, v) {p ↦ v}` has no `∀ fp`. Cleaner: derived rules for the
annotation-insensitive postcondition class (`Ψ (.annot ds v) ρ = Ψ
(.pure v) ρ`), which every exhibit's `Ψ` satisfies.

(g) **The symbol-resolution seam.** `struct_create_store_wps`
(StructExhibit.lean:704) carries `(hex : M.extern = fmapEmpty)`
because `evalPexpr` resolves `PEsym x` through `resolveExtern ext x`
(Step.lean:617-644). A client statement should not have to know the
extern map exists; cleaner is a lookup lemma at `SymFrame` that
already discharges `resolveExtern` (as `envAdd_lookup` does for the
frame) or `M.extern` folded into the profile the way `M.tagDefs` is.

### Notes

- **N-1 Count drift.** README.md:332: "(`Audit.lean`: 107 export pins,
  every theorem of every module bounded)" vs README.md:484 and the
  build: "109 trio-exact". Fix the number.
- **N-2 Diagram arrow for the total lane.** README trust diagram lists
  "Iris adequacy (… TotalAdequacy.lean: wpt_strongly_normalizing =
  twp_total)" ABOVE "engine drive statements (… wpt_engine_boundU/J
  (_alloc) ⇒ driveU … k = .done v σ')". Trace: `exhibitA_total |
  landmarks (suffix): [genHeap_init, step_ctx, storeM, loadM,
  allocateObject, eqPtrval]` and `wpt_engine_boundJ | spine reached:
  engine_step_matchU, Decomp.step_factor, stepDischarge_run,
  wpt_engine_boundU, wpt_engine_boundJ, wpt_drive_aux, spikeCells_alloc`
  — neither `twp_total` nor `wp_strong_adequacy_gen` nor `wpt_sound` is
  in the cone. The total drive equations are proved by budget induction
  against `engine_step_matchU` (`wpt_drive_aux`), using the BI/fupd
  soundness of the state interpretation, not Iris adequacy; `wpt_sound`
  feeds only `wpt_strongly_normalizing(_alloc)`. WALKTHROUGH §5 states
  this correctly ("proved once by induction on the budget with
  `engine_step_matchU` discharging one engine step per unit
  (`wpt_drive_aux`)"); the README diagram should draw the second arrow.
- **N-3 Dead public names** (trace §C, DERIVED: theorems with no direct
  value-consumer in the package). API-listed: `spike_engine_adequacy_alloc`,
  `wpt_engine_boundJ_alloc`, `wpt_strongly_normalizing_alloc`,
  `MemTripleU_alloc_of_MemTripleU` (added at P6.1 as a fact, never
  used), `pointsToCell_readout` (its twin `cellOwn_readout` has one
  consumer), `allocCap_weaken`, `allocMeta_dup`, `allocMeta_agree`
  (the last three are in the README's assertion-law table with no
  client, against the P4 record "every advertised view law has a
  StructExhibit client" — literally true of the VIEW laws, not of
  these), `driveJ_step`/`driveJ_done`/`driveJ_value_pure`. Internal:
  `Coh.store`, `Coh.store_interior`, `eqPtrval_null_cell`,
  `planFits_insufficient`, `planFits_order_sensitive` (cited by
  WALKTHROUGH §4 as a fact — fine as a documented fact). Exhibit-level:
  `tree_rotate_wps_frame`, `loop_wps_irrelevant_binding` (the `wpt`
  twins are consumed). Under the repo's own no-consumer rule these are
  candidates for deletion or for a consumer; none hides a gap.
- **N-4 Statement cosmetics.** `counter_loop_certified` (LoopExhibit.lean:438)
  concludes `∃ i a, cellPtr idx addr = cellPtr i a ∧ CellCoh fmapEmpty
  σ' i ⟨a, intTy, bs'⟩` — the existential leaked from
  `pointsToCell_consequence`; `cellPtr_inj` collapses it to `CellCoh
  fmapEmpty σ' idx ⟨addr, intTy, bs'⟩`. `list_reverse_terminates`
  (ListRevExhibit.lean:2074) writes `hcoh : Sat (procCtx lrProcSym
  (lrRS …)).tagDefs σ₀ …` where its siblings write `fmapEmpty`
  (definitional). `diverge_total_unprovable` (DivergeExhibit.lean:118)
  is stated from `⊢` (no resources) at the fixed `SpikeGF`; the
  underlying `dg_not_normalizing` is unconditional, so the negative
  test can be stated from any footprint `m₀` at any `GF`, which is the
  stronger and more natural claim.
- **N-5 `stateInert (Ecase _ _) = false`** (TotalAdequacy.lean:476)
  although the value-scrutinee case step is pure; harmless
  (conservative), but the memory-pinning conjunct of
  `wpt_engine_boundU` is then unavailable to programs with `Ecase`.
- **N-6 Opaque-leaf tallies** (DERIVED, my closure over type+value of
  every constant, 109 cones): `CerberusImpl.typeof_enum` 104,
  `CerberusFresh.digest` 52, `failwithI` 93, `fuelExhaustedWith` 105,
  `beqMemValueSafe` 11, `normalise_ctype` 8, `instBEqCore_base_type.beq`
  8, `CerbGlobal.current_execution_mode`/`using_concurrency` 11,
  `has_switch`/`is_CHERI` 8. README's list (P6.1): 102/50/91/103/11/8/8
  and 11/8 — the same leaf set, four counts off by two (a convention
  difference, not a trust difference). Additional Lean-core leaves not
  listed in the README: `Lean.opaqueId` (107), `floatSpec` (99),
  `Std.Internal.idOpaque` (8) — same status as the listed `Float.*`.
- **N-7 `Sat` demands writability.** `CellCoh.alloc` requires
  `al.isReadonly = .IsWritable` (Heap.lean:303 ff.), so a read-only
  allocation cannot appear in any footprint even at a read-only
  fraction. Outside the fragment (every fragment allocation is a
  writable `create`), but it will bite string literals/`const` objects
  later; noted for the roadmap, not graded.
- **N-8 Hypothesis column spot-check.** The README exhibits table's
  "Hypotheses, exhaustively" column matches the elaborated statements
  for every row I compared (`exhibitA_total`, `counter_loop_certified`,
  `fib_certified_total`, `array_sum_certified`, `struct_update_certified`,
  `struct_create_store_wps` incl. `hex`, `struct_create_store_adequacy`,
  `list_reverse_certified(_total/_terminates)`, `tree_rotate_certified(_total)`,
  `case_certified`, `wseq_certified`, `exhibitA_prod`, the three
  `*_production`, `counter_loop_certified_registration`). One wording
  nit: `exhibitB_engine`'s row says "`y` and all unnamed rest verbatim";
  the engine statement names only `xAddr`/`yAddr` bytes — the "rest"
  lives in `exhibitB_semantic`'s `SemTriple` frame `R`.

## 4. Areas for improvement of the logic (the quality list)

| # | Current statement | Proposed cleaner statement |
|---|---|---|
| Q1 | `Step.store_eval`/`Frag.store_op`/`wps_store_eval`/`wpt_store_eval`: `hnv2 : valueFromPexpr pe2 = none`, `hnv3 : valueFromPexpr pe3 = none` | one premise `valueFromPexprs [pe1, pe2, pe3] = none` (the engine's arm; the shape `memop_eval` already has) |
| Q2 | `Frag.save` unconditional; `Step.save`/`wps_save`/`wpt_save` at `valueFromPexprs (saveParamPexprs ps) = some cvals` | `Step.save_eval` + rules at `evalPexprs M.tagDefs M.extern ρ (saveParamPexprs ps) = some cvals`; or `Frag.save` narrowed to the literal form |
| Q3 | `wps_pure`/`wps_load_eval`/`wps_store_eval` (+`wpt_`) carry `hnv…` "not already a value" premises | drop them; `evalPexpr` is the identity on values |
| Q4 | `wps_if_true` (`hg : … = some Vtrue`) and `wps_if_false` (`… = some Vfalse`), meta-level | `⌜evalPexpr … g = some (boolValue b)⌝ ∗ wps M Ls Ψ (bif b then e2 else e3) ρ ⊢ wps M Ls Ψ (Expr a (Eif g e2 e3)) ρ` |
| Q5 | `wps_store_at`/`wpt_store_at`/`*_store_cell_at`: `hcompat`, `hfpm`, `hbytes`, `hlen` inlined | `(hst : StorableAt M.tagDefs vty mv)` as in `wps_store` |
| Q6 | `wps_store_cell_at`/`wpt_store_cell_at`: `hdec' : decIndep M.tagDefs a aty (spliceBytes …)` | lemma `decIndep_splice` discharging it from `hst.stored_dec` and the cell's own `decIndep`; premise removed |
| Q7 | `Frag.case_value`: `hbsz : ∀ e', select_case … = some e' → esize e' ≤ esize (caseRedex …)` | lemma `esize_select_case_le`; premise removed (if provable as expected) |
| Q8 | `wps_pure`/`wps_annot`/`wpt_pure`/`wpt_annot` at `Expr ([] : List annot) …` | `Expr a …` for all four (as `wps_if_*`, `wps_save`, `wps_run`) |
| Q9 | total stratum lacks `wpt_load` (pointsToCell), `wpt_case_value`, `wpt_wseq`, `wpt_fupd`; partial lacks `wps_mono_Ls`, `blockSpecs_mono` | add the six; `wpt_case_value := wpt_det_step …` |
| Q10 | `wps_store` ↔ `wpt_store_cell`; `wps_load` ↔ — | one naming scheme across strata (`*_store`, `*_load`, `*_load_at`, `*_store_at`, `*_load_cell_at`, `*_store_cell_at`) |
| Q11 | `triple`, `wp_sseq`, `wp_annot(_reindex)`, `wp_env_invariant_stable`, `triple_frame/conseq/seq` at `spikeCtx`/`spikeEnv`; `triple_seq` needs `EnvStable e1`, posts `fun _ => Q` | generic `{M}` and `ρ` (as `wp_store`/`wp_load`), classical `triple P e1 Q → (∀ v, triple (Q v) e2 R) → triple P (e1; e2) R`; or demote the base stratum to the two small axioms in the docs |
| Q12 | `∀ fp, … -∗ Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ` in every small axiom's continuation | derived annotation-insensitive forms `… -∗ Ψ (.pure Vunit) ρ` for `Ψ` with `Ψ (.annot ds v) = Ψ (.pure v)` |
| Q13 | `struct_create_store_wps`: `hex : M.extern = fmapEmpty` | a `SymFrame`-level lookup lemma that discharges `resolveExtern`, or `extern` folded into the profile |
| Q14 | `counter_loop_certified` post `∃ i a, cellPtr idx addr = cellPtr i a ∧ CellCoh … i ⟨a, …⟩` | `CellCoh fmapEmpty σ' idx ⟨addr, intTy, bs'⟩` |
| Q15 | `diverge_total_unprovable` from `⊢` at `SpikeGF` | from `[∗map] cellOwn` of any `m₀` with `Coh …`, at any `GF` |
| Q16 | `stateInert (Ecase _ _) = false` | `stateInert (Ecase _ pats) = pats.all (stateInert ∘ Prod.snd)` |
| Q17 | dead island `StraightFrag`/`engine_complete`/`prod_loop_done`/`prod_run_eq`/`sem_triple_prod` (+ `engine_complete_loadU/createU` → `cerberusRound_refused_*`) | retire; one production collapse (`loop_step_frag`/`wpt_driver_done*`/`prod_run_eqJ`) |

## 5. The known items, assessed

- **Fuel side condition.** Honest and on the face of every partial
  statement (`esize e + n ≤ lemDefaultFuel`, per registered label body);
  the total exports are unconditional at derived bounds. One
  consequence worth saying plainly in the README: since `n` is the
  ROUND COUNT, the partial statements say nothing about runs longer
  than ~10⁶ rounds (a loop of 10⁶ iterations is outside them) — the
  seam is the interpreter's real `get_ctx` budget, and the tree treats
  it correctly (`fuelExhaustedWith` is an opaque leaf in 105 cones, never
  unfolded).
- **Synthetic Core entry.** Registered and true (`prodFile`,
  `_root_.drive fmapEmpty false`). The label maps are indeed derived
  from the shipped registration (`fib_labeledAt_production`,
  `loop_labeledAt_production`, each `rfl`-backed via
  `collect_labeled_continuations_NEW`). Note that H-1's contortions are
  what synthetic entry currently REQUIRES of the program shape; a
  C-elaborated `save`/`store` would not fit the fragment.
- **Donor divergences.** Fractional metadata as the exclusivity anchor
  is sound and load-bearing exactly as described: `metaOwn_ne`
  (Heap.lean:2290, `pointsTo_ne`) → `bigSepM_own_disjoint`
  (Adequacy.lean:1405) is what gives `Q ##ₘ R` in the semantic triple.
  The discarded-fraction persistent stratum (`allocMeta`,
  `locInBounds`, `pointsToView_persist`) is admissible because no rule
  writes a metadata cell (`CohG` has no update for `mm` other than
  `create`'s mint); the named mover (the kill arc) is correct — when
  `kill` arrives, persistence of `allocMeta` becomes FALSE and the anchor
  must move to a killable token before any dispose rule is stated.
- **No `wp_bind` / no `Language.Context`.** Correct and verified at the
  relation: `Step.sseq_ctx`/`wseq_ctx`/`annot_ctx` carry the guard
  `(hnj : jumpRedex? e1 = none)` and `Step.run` replaces the whole
  expression (`Step M (e, ev0 :: evs, σ) (cont, bindArgs params vs (ev0
  :: evs), σ)` with `jumpRedex? e = some (l, pes)`), so `K[run …]` and
  `run …` step to the same configuration and `Context.primStep_fill`
  is false. The direct sequencing rules are the right treatment;
  `wps_seq` is the standard bind-shaped rule modulo the annotation
  merge (Q12).
- **Consumerless exports flagged for a decision.** Confirmed by trace
  and widened: `sem_triple_prod` (0 consumers), `prod_run_eq` (consumed
  only by `sem_triple_prod`), `spike_engine_adequacy_alloc` (0 — trace
  §C; it is API-listed, not a `trioExport`), and behind them
  `prod_loop_done`, `engine_complete`, `StraightFrag` (M-1). My view:
  retire all of it. `prod_run_eqJ` subsumes `prod_run_eq` (a
  `DriverDoneAt` at `Q = fmapEmpty` is the straight-line case), the
  `Frag`-lane `loop_step_frag` subsumes `engine_complete`, and
  `sem_triple_prod`'s premises (`hpre`/`hterm`: operational drive
  equations) are exactly the "boring logic" shape the [USER 2026-09-02]
  projection ruling rejected. `spike_engine_adequacy_alloc` is a
  fixed-profile instance of `engine_adequacyU_alloc` (which
  `project_triple_alloc` consumes); keep only if a client appears.
- **`Ecase`/`Ewseq` at the partial stratum only.** A reasonable
  absence under the no-consumer rule, but the asymmetry is
  cheap to close and the brief's standard is "every construct at both
  strata where meaningful": `wpt_case_value` is one application of
  `wpt_det_step` (Wpt.lean:547) to `Step.case_value`; `wpt_wseq` is the
  `wpt_seq` clone. Graded within M-3.
- **The `∀ [inst] …` inside `⌜…⌝` hazard.** Zero occurrences. Trace §D:
  "hazards found: 0"; the census shows the 18 theorems that carry
  instance binders (`project_triple`×2, `project_triple_alloc`×2,
  `engine_adequacyU/J(_alloc)`, `spike_step_adequacy(_alloc)`,
  `spike_engine_adequacy(_alloc)`, `wpt_engine_boundU/J(_alloc)`,
  `wpt_strongly_normalizing(_alloc)`, `wpt_driver_done(_alloc)`,
  `diverge_total_unprovable`) carry them at Prop level, and they
  survive elaboration — e.g. `engine_adequacyU`'s pretty-printed type
  reads `(∀ [inst : CerberusHeapLang.SpikeGS Iris.HasLC.hasLC GF], ([∗map]
  i ↦ c ∈ m₀, …) ⊢ WP …) →`. Source scan (`grep -rn '∀ \['`): every
  hit is a theorem binder or the Prop-level post of the projections;
  none is under `iprop(`/`⌜`.
- **`tds` threading (re-pin option (a)).** Clean where it matters: trace
  §E shows Heap/Wps/Wpt/TotalAdequacy/Lang/Round have NO constant whose
  type mentions `fmapEmpty` or a `spike*` profile; every rule supplies
  `M.tagDefs`. The exceptions: the base stratum (M-2, via `spikeCtx`);
  `Adequacy`'s fixed-profile lanes (`drive`, `driveJ`, `SemTriple`,
  `spike_engine_adequacy(_alloc)`) by design; the production layer
  (`wpt_driver_done*` take `htd : M₀.tagDefs = fmapEmpty`,
  `loop_step_frag` likewise) because the pipeline is `_root_.drive
  fmapEmpty false (prodFile …)` — inherent to the synthetic file, not a
  bake-in in a logic module.

## 6. Answers

**(a) Unacceptable or unaccounted trust gaps.** None found. Every
export is trio-exact (re-verified independently); no `sorryAx`; the
opaque leaves reached are the README's set (N-6: same names, four
counts off by two, three trivial Lean-core names unlisted). The
adequacy chain is as drawn for the partial lane (`wps_sound` →
`spike_step_adequacy` = `wp_strong_adequacy_gen` with `genHeap_init` →
`engine_adequacyU` → `engine_step_matchU` → engine functions) and the
production lane (`wpt_driver_done*` → `loop_step_frag` →
`driver2_done`/`finalize_done` → `prod_run_eqJ` → `runND ∘ drive ∘
initial_driver_state`); the total lane differs from the README diagram
in a way that is documented correctly in the WALKTHROUGH (N-2). The
statements say what the docs say they say (N-8), with the one
precision fault being the fragment sentence (H-1).

**(b) Documentation adequacy for a PL reader.** Adequate and unusually
honest — the hypothesis column, the readout predicates printed in full,
the configuration answer, the opaque-leaf list. Three fixes make it
right: the fragment sentence must state the operand-evaluation and
save restrictions (H-1); the trust diagram and module table must stop
naming the dead lane (M-1) and draw the total lane's arrow (N-2); the
107/109 drift (N-1). The "three strata" presentation should either be
made true (M-2) or reduced to two strata plus two small axioms.

**(c) Ready to be called complete-minus-dispose-and-procedures?** Not
yet. Within the frozen fragment two engine arms the docs count as
covered are covered only in sub-cases (H-1), the total stratum lacks
rules the partial one has (M-3), and the base stratum is a
fixed-profile lane rather than a stratum of the logic (M-2). After
H-1, M-1, M-2 (either resolution), M-3 and Q1–Q8, the claim is fair:
small axioms in classical form at both strata, frame across back
edges, consequence, sequencing, conditionals, loops with invariants
and variants, allocation with an abstract capacity, all projected to
Iris-free statements about the engine.

## Appendix A — the tracing script (verbatim, as run)

Run from `cerberus-heaplang/` after checking no `lake build` is live:
`CERB_MEM_MAX=48G ../scripts/capped ~/.elan/bin/lake env lean audit_trace.lean`.
Note the two operator shadowings inside this environment: Iris
redefines `||` and `>` on the types involved, hence `Bool.or`/`Bool.and`
and `Nat.blt` below.

```lean
import CerberusHeapLang
open Lean Meta

namespace AuditTrace

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => .anonymous

def isPkg (env : Environment) (n : Name) : Bool :=
  (modOf env n).getRoot == `CerberusHeapLang

def short (n : Name) : String :=
  let s := n.toString
  if s.startsWith "CerberusHeapLang." then (s.drop "CerberusHeapLang.".length).toString else s

def shortMod (n : Name) : String := short n

def valueConsts (ci : ConstantInfo) : Array Name :=
  match ci with
  | .thmInfo t => t.value.getUsedConstants
  | .defnInfo d => d.value.getUsedConstants
  | .opaqueInfo o => o.value.getUsedConstants
  | _ => #[]

def allConsts (ci : ConstantInfo) : Array Name := ci.type.getUsedConstants ++ valueConsts ci

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"

abbrev DepM := StateM (Std.HashMap Name (Array Name))

def depsOf (env : Environment) (n : Name) : DepM (Array Name) := do
  if let some d := (← get).get? n then return d
  let d := match env.find? n with | some ci => allConsts ci | none => #[]
  modify (·.insert n d)
  return d

/-- transitive closure; `expand c` decides whether c's own deps are followed -/
partial def cone (env : Environment) (expand : Name → Bool) (seeds : Array Name) :
    DepM (Std.HashSet Name) := do
  let mut seen : Std.HashSet Name := {}
  let mut stack := seeds
  while h : stack.size > 0 do
    let c := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    if !expand c then continue
    for d in ← depsOf env c do
      if !seen.contains d then stack := stack.push d
  return seen

def spine : List Name := [
  `CerberusHeapLang.engine_step_matchU, `CerberusHeapLang.engine_complete,
  `CerberusHeapLang.Decomp.step_factor, `CerberusHeapLang.stepDischarge_run,
  `CerberusHeapLang.wps_sound, `CerberusHeapLang.wps_sound_frame, `CerberusHeapLang.wpt_sound,
  `CerberusHeapLang.spike_step_adequacy, `CerberusHeapLang.spike_step_adequacy_alloc,
  `CerberusHeapLang.engine_adequacyU, `CerberusHeapLang.engine_adequacyU_alloc,
  `CerberusHeapLang.engine_adequacyJ, `CerberusHeapLang.spike_engine_adequacy,
  `CerberusHeapLang.spike_engine_adequacy_alloc, `CerberusHeapLang.drive_classifyU,
  `CerberusHeapLang.project_triple, `CerberusHeapLang.project_triple_alloc,
  `CerberusHeapLang.semantic_triple_soundU, `CerberusHeapLang.semantic_triple_sound,
  `CerberusHeapLang.wpt_engine_boundU, `CerberusHeapLang.wpt_engine_boundJ,
  `CerberusHeapLang.wpt_engine_boundU_alloc, `CerberusHeapLang.wpt_engine_boundJ_alloc,
  `CerberusHeapLang.wpt_drive_aux, `CerberusHeapLang.wpt_strongly_normalizing,
  `CerberusHeapLang.wpt_strongly_normalizing_alloc,
  `CerberusHeapLang.launchResources, `CerberusHeapLang.spikeCells_alloc,
  `CerberusHeapLang.stateInterp_readout,
  `CerberusHeapLang.loop_step_frag, `CerberusHeapLang.prod_loop_done,
  `CerberusHeapLang.driver2_done, `CerberusHeapLang.finalize_done,
  `CerberusHeapLang.wpt_driver_done, `CerberusHeapLang.wpt_driver_done_alloc,
  `CerberusHeapLang.wpt_driver_aux, `CerberusHeapLang.prod_run_eqJ,
  `CerberusHeapLang.prod_run_eq, `CerberusHeapLang.sem_triple_prod,
  `CerberusHeapLang.drive_after_setup, `CerberusHeapLang.cerberusRound_classify,
  `CerberusHeapLang.step_iff_cerberusRound,
  `CerberusHeapLang.wps_create, `CerberusHeapLang.wpt_create,
  `CerberusHeapLang.wp_store, `CerberusHeapLang.wp_load, `CerberusHeapLang.wp_sseq,
  `CerberusHeapLang.wps_store, `CerberusHeapLang.wps_load, `CerberusHeapLang.wps_load_at,
  `CerberusHeapLang.wps_store_at, `CerberusHeapLang.wps_load_cell_at,
  `CerberusHeapLang.wps_store_cell_at, `CerberusHeapLang.wpt_store_cell,
  `CerberusHeapLang.wpt_load_at, `CerberusHeapLang.wpt_store_at,
  `CerberusHeapLang.wpt_load_cell_at, `CerberusHeapLang.wpt_store_cell_at,
  `CerberusHeapLang.blockSpecs_intro, `CerberusHeapLang.blockSpecsT_intro,
  `CerberusHeapLang.wps_frame_labels, `CerberusHeapLang.wpt_frame_labels,
  `CerberusHeapLang.storeM_success, `CerberusHeapLang.loadM_success,
  `CerberusHeapLang.allocateObject_success]

/-- Iris / engine landmarks matched by name SUFFIX in the full cone -/
def suffixLandmarks : List String :=
  ["wp_strong_adequacy_gen", "twp_total", "genHeap_init", "wp_frame_r", "wp_value'",
   "step_ctx", "storeM", "loadM", "allocateObject", "eqPtrval", "runND", "drive",
   "initial_driver_state", "driver2", "finalize", "action_request_sequential2"]

def ruleTable : List (String × List Name) := [
  ("Small axioms", [`CerberusHeapLang.wp_store, `CerberusHeapLang.wp_load,
    `CerberusHeapLang.wps_store, `CerberusHeapLang.wps_load, `CerberusHeapLang.wps_load_at,
    `CerberusHeapLang.wps_store_at, `CerberusHeapLang.wps_load_cell_at,
    `CerberusHeapLang.wps_store_cell_at, `CerberusHeapLang.wpt_load_at,
    `CerberusHeapLang.wpt_store_at, `CerberusHeapLang.wpt_load_cell_at,
    `CerberusHeapLang.wpt_store_cell_at, `CerberusHeapLang.wpt_store_cell]),
  ("Allocation", [`CerberusHeapLang.wps_create, `CerberusHeapLang.wpt_create]),
  ("Frame", [`CerberusHeapLang.triple_frame, `CerberusHeapLang.wps_frame,
    `CerberusHeapLang.wps_frame_labels, `CerberusHeapLang.blockSpecs_frame,
    `CerberusHeapLang.wps_sound_frame, `CerberusHeapLang.wpt_frame,
    `CerberusHeapLang.wpt_frame_labels, `CerberusHeapLang.blockSpecsT_frame]),
  ("Consequence", [`CerberusHeapLang.triple_conseq, `CerberusHeapLang.wps_wand,
    `CerberusHeapLang.wps_fupd, `CerberusHeapLang.wpt_mono, `CerberusHeapLang.wpt_mono_k,
    `CerberusHeapLang.wpt_mono_Ls]),
  ("Sequencing", [`CerberusHeapLang.triple_seq, `CerberusHeapLang.wp_sseq,
    `CerberusHeapLang.wps_seq, `CerberusHeapLang.wps_seq_spec, `CerberusHeapLang.wps_seq_sym,
    `CerberusHeapLang.wps_wseq, `CerberusHeapLang.wpt_seq, `CerberusHeapLang.wpt_seq_spec,
    `CerberusHeapLang.wpt_seq_sym]),
  ("Conditionals, case", [`CerberusHeapLang.wps_if_true, `CerberusHeapLang.wps_if_false,
    `CerberusHeapLang.wps_case_value, `CerberusHeapLang.wpt_if_true,
    `CerberusHeapLang.wpt_if_false]),
  ("Loops", [`CerberusHeapLang.wps_save, `CerberusHeapLang.wps_run,
    `CerberusHeapLang.blockSpecs_intro, `CerberusHeapLang.wpt_save, `CerberusHeapLang.wpt_run,
    `CerberusHeapLang.blockSpecsT_intro]),
  ("Total judgment", [`CerberusHeapLang.wpt_sound, `CerberusHeapLang.diverge_total_unprovable]),
  ("Operands, memop, values", [`CerberusHeapLang.wps_load_eval, `CerberusHeapLang.wps_store_eval,
    `CerberusHeapLang.wps_memop_eval, `CerberusHeapLang.wps_memop_ptreq,
    `CerberusHeapLang.wp_ofVal, `CerberusHeapLang.wps_ofVal, `CerberusHeapLang.wps_pure,
    `CerberusHeapLang.wps_annot, `CerberusHeapLang.wps_annot_reindex,
    `CerberusHeapLang.wpt_load_eval, `CerberusHeapLang.wpt_store_eval,
    `CerberusHeapLang.wpt_memop_eval, `CerberusHeapLang.wpt_memop_ptreq,
    `CerberusHeapLang.wpt_ofVal, `CerberusHeapLang.wpt_pure, `CerberusHeapLang.wpt_annot,
    `CerberusHeapLang.wpt_annot_reindex]),
  ("Assertion laws", [`CerberusHeapLang.pointsToCell_fractional, `CerberusHeapLang.pointsToCell_agree,
    `CerberusHeapLang.pointsToCell_combine, `CerberusHeapLang.pointsToView_split,
    `CerberusHeapLang.pointsToView_join, `CerberusHeapLang.pointsToView_fractional,
    `CerberusHeapLang.pointsToView_agree, `CerberusHeapLang.pointsToView_persist,
    `CerberusHeapLang.pointsToView_locInBounds, `CerberusHeapLang.allocMeta_persistent,
    `CerberusHeapLang.allocMeta_dup, `CerberusHeapLang.allocMeta_agree,
    `CerberusHeapLang.locInBounds_persistent, `CerberusHeapLang.cellPtr_arrayShift,
    `CerberusHeapLang.allocCap_weaken, `CerberusHeapLang.allocCap_intro,
    `CerberusHeapLang.cellOwn_view, `CerberusHeapLang.pointsToCell_cellOwn_iff,
    `CerberusHeapLang.cellOwn_fractional, `CerberusHeapLang.cellPtr_inj]),
  ("Environment seam", [`CerberusHeapLang.envAdd_lookup, `CerberusHeapLang.symFrame_empty]),
  ("Base logic (API)", [`CerberusHeapLang.wp_annot, `CerberusHeapLang.wp_annot_reindex,
    `CerberusHeapLang.wp_env_invariant_stable])]

def logicModules : List Name := [`CerberusHeapLang.Heap, `CerberusHeapLang.Rules,
  `CerberusHeapLang.Wps, `CerberusHeapLang.Wpt, `CerberusHeapLang.Adequacy,
  `CerberusHeapLang.TotalAdequacy, `CerberusHeapLang.Lang, `CerberusHeapLang.EnvLaws,
  `CerberusHeapLang.Round]

def isExhibitMod (m : Name) : Bool :=
  let s := m.toString
  Bool.or (Nat.blt 1 (s.splitOn "Exhibit").length) (Nat.blt 1 (s.splitOn "ReadinessSmoke").length)

def prodMods : List Name := [`CerberusHeapLang.DriverCollapse, `CerberusHeapLang.ProdLoop,
  `CerberusHeapLang.ProdEntry]

def hasSuffix (n : Name) (s : String) : Bool :=
  match n with
  | .str _ last => last == s
  | _ => false

def sortNames (a : Array Name) : Array Name := a.qsort (·.toString < ·.toString)

def fmt (l : List Name) : String := ", ".intercalate (l.map short)

#eval show MetaM Unit from do
  let env ← getEnv
  let exports := CerberusHeapLang.Audit.trioExports
  IO.println s!"# audit_trace — {exports.length} exports in Audit.trioExports"
  let pkg : Array (Name × ConstantInfo) :=
    env.constants.fold (fun acc n ci => if isPkg env n then acc.push (n, ci) else acc) #[]
  IO.println s!"package constants: {pkg.size}"
  let mut rev : Std.HashMap Name (Array Name) := {}
  for (n, ci) in pkg do
    for d in valueConsts ci do
      if Bool.and (isPkg env d) (d != n) then
        rev := rev.insert d ((rev.getD d #[]).push n)
  let parentOf (n : Name) : Name :=
    if n.isInternalDetail then
      let rec go : Name → Name
        | .anonymous => .anonymous
        | m@(.str p _) => if m.isInternalDetail then go p else m
        | .num p _ => go p
      go n
    else n
  let consumersOf (t : Name) : Array Name :=
    let raw := rev.getD t #[]
    let ps := raw.map parentOf
    (ps.filter (fun p => Bool.and (Bool.and (p != t) (p != .anonymous)) ((modOf env p) != `CerberusHeapLang.Audit)))
      |>.foldl (fun (acc : Array Name) p => if acc.contains p then acc else acc.push p) #[]
  let mods := env.header.moduleNames
  let exhibitMods := (mods.filter fun m => Bool.and (m.getRoot == `CerberusHeapLang) (isExhibitMod m))
  let modConsts (m : Name) : Array Name :=
    (pkg.filter fun (n, _) => modOf env n == m).map (·.1)
  let ((exCones : Array (Name × Std.HashSet Name)), st) :=
    (exhibitMods.mapM (fun m => do
      let c ← cone env (isPkg env) (modConsts m)
      pure (m, c))).run {}
  let (prodCone, st) := (cone env (isPkg env) (prodMods.toArray.flatMap modConsts)).run st
  IO.println "\n## A. Exports"
  let mut st := st
  let mut leafCount : Std.HashMap Name Nat := {}
  let mut consumerless : Array Name := #[]
  for n in exports do
    let some ci := env.find? n | IO.println s!"- MISSING {n}"; continue
    let axs := sortNames (← collectAxioms n)
    let (full, st') := (cone env (fun _ => true) #[n]).run st
    st := st'
    let reached := spine.filter full.contains
    let landmarks := suffixLandmarks.filter fun s => full.toList.any (hasSuffix · s)
    let mut leaves : Array Name := #[]
    for c in full.toList do
      match env.find? c with
      | some (.opaqueInfo _) => leaves := leaves.push c
      | some (.axiomInfo _) => leaves := leaves.push c
      | _ => pure ()
    for l in leaves do leafCount := leafCount.insert l (leafCount.getD l 0 + 1)
    let cons := consumersOf n
    if cons.isEmpty then consumerless := consumerless.push n
    IO.println s!"\n### {short n}  [{kindOf ci}; {shortMod (modOf env n)}]"
    IO.println s!"- axioms: {axs.toList}"
    IO.println s!"- full cone size: {full.size}; opaque/axiom leaves: {(sortNames leaves).toList.map short}"
    IO.println s!"- spine reached: {fmt reached}"
    IO.println s!"- landmarks (suffix): {landmarks}"
    IO.println s!"- direct in-package consumers ({cons.size}): {fmt (sortNames cons).toList}"
  IO.println s!"\n### Consumerless exports ({consumerless.size}): {fmt consumerless.toList}"
  IO.println "\n### Opaque/axiom leaves over all export cones (leaf: #exports reaching it)"
  let leafArr := leafCount.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  for (l, k) in leafArr do IO.println s!"- {l}: {k}"
  IO.println "\n## B. Rule table (README/API) — existence, consumers, exhibit cones"
  for (fam, rules) in ruleTable do
    IO.println s!"\n### {fam}"
    for r in rules do
      match env.find? r with
      | none => IO.println s!"- {short r}: MISSING"
      | some ci =>
        let cons := consumersOf r
        let exs := (exCones.filter fun (_, c) => c.contains r).map (fun (m, _) => shortMod m)
        let inProd := prodCone.contains r
        IO.println s!"- {short r} [{kindOf ci}; {shortMod (modOf env r)}]: direct consumers ({cons.size}): {fmt (sortNames cons).toList}; exhibit cones: {exs.toList}; production layer: {inProd}"
  IO.println "\n## C. Theorems in logic modules with NO direct value-consumer in the package (outside Audit)"
  for m in logicModules do
    let mut dead : Array Name := #[]
    for (n, ci) in pkg do
      unless modOf env n == m do continue
      unless ci matches .thmInfo _ do continue
      if n.isInternalDetail then continue
      if (consumersOf n).isEmpty then dead := dead.push n
    IO.println s!"- {shortMod m} ({dead.size}): {fmt (sortNames dead).toList}"
  IO.println "\n## D. Pure-embedding hazard scan (⌜…⌝ segments containing an instance binder) + '∀ [' binder census"
  let mut hazards : Array String := #[]
  let mut instBinderTypes : Array (Name × Nat) := #[]
  for (n, ci) in pkg do
    if n.isInternalDetail then continue
    let s := (← ppExpr ci.type).pretty 200
    let segs := (s.splitOn "⌜").drop 1
    for seg in segs do
      let inside := (seg.splitOn "⌝").headD ""
      if Bool.or (Nat.blt 1 (inside.splitOn "SpikeGS").length) (Nat.blt 1 (inside.splitOn "[inst").length) then
        hazards := hazards.push s!"{short n}: ⌜{inside}⌝"
    let k := (s.splitOn "∀ [").length - 1
    if Nat.blt 0 k then instBinderTypes := instBinderTypes.push (n, k)
  IO.println s!"- hazards found: {hazards.size}"
  for h in hazards do IO.println s!"  - {h}"
  IO.println s!"- constants whose pretty type contains '∀ [' (count): {(instBinderTypes.map fun (n,k) => s!"{short n}×{k}").toList}"
  IO.println "\n## E. Logic-module constants whose TYPE mentions fmapEmpty / spikeCtx / spikeEnv / spikeRunState / spikeFile"
  for m in logicModules do
    let mut hits : Array String := #[]
    for (n, ci) in pkg do
      unless modOf env n == m do continue
      if n.isInternalDetail then continue
      let tc := ci.type.getUsedConstants
      let f := tc.any (hasSuffix · "fmapEmpty")
      let sc := tc.any fun c => [`CerberusHeapLang.spikeCtx, `CerberusHeapLang.spikeEnv,
        `CerberusHeapLang.spikeRunState, `CerberusHeapLang.spikeFile].contains c
      if Bool.or f sc then hits := hits.push s!"{short n}{if f then "[fmapEmpty]" else ""}{if sc then "[spike*]" else ""}"
    IO.println s!"- {shortMod m} ({hits.size}): {", ".intercalate hits.toList}"
  IO.println "\n## F. Frag constructors (environment)"
  match env.find? `CerberusHeapLang.Frag with
  | some (.inductInfo ii) => IO.println s!"- {ii.ctors.length}: {fmt ii.ctors}"
  | _ => IO.println "- Frag not found"
  match env.find? `CerberusHeapLang.StraightFrag with
  | some (.inductInfo ii) => IO.println s!"- StraightFrag {ii.ctors.length}: {fmt ii.ctors}"
  | _ => IO.println "- StraightFrag not found"
  IO.println "\n## G. Export statements (pretty-printed types)"
  for n in exports do
    let some ci := env.find? n | continue
    let s := (← ppExpr ci.type).pretty 110
    IO.println s!"\n### {short n}\n```\n{s}\n```"

end AuditTrace
```

## Appendix B — selected trace output (verbatim)

```
# audit_trace — 109 exports in Audit.trioExports
package constants: 3636
```

```
### Consumerless exports (39): exhibit, exhibitA_engine, exhibitB_engine, exhibitC_engine, exhibitA_total, counter_loop_certified, fib_certified, fib_certified_total, fib_terminates, array_sum_certified, struct_update_certified, list_reverse_demo, list_reverse_certified_total, list_reverse_terminates, tree_rotate_certified, tree_rotate_certified_total, diverge_total_unprovable, case_certified, wseq_certified, cerberusRound_classify, sem_triple_prod, exhibitA_prod, counter_loop_certified_registration, fib_certified_production, counter_loop_certified_production, list_reverse_certified_production, pointsToCell_readout, struct_x_read_shared_wps, cell_read_shared_wps, struct_x_read_persist_wps, tree_rotate_wps_frame, loop_wps_irrelevant_binding, counter_loop_certified_irrelevant_binding, ReadinessSmoke.twoField_load_x, ReadinessSmoke.twoField_load_y, ReadinessSmoke.twoField_store_x, ReadinessSmoke.twoField_store_y, ReadinessSmoke.twoField_create, MemTripleU_alloc_of_MemTripleU
```

(Of these, all but `sem_triple_prod`, `pointsToCell_readout`,
`tree_rotate_wps_frame`, `loop_wps_irrelevant_binding` and
`MemTripleU_alloc_of_MemTripleU` are terminal exhibit statements —
expected consumerless.)

```
## D. Pure-embedding hazard scan (⌜…⌝ segments containing an instance binder) + '∀ [' binder census
- hazards found: 0
```

```
## E. Logic-module constants whose TYPE mentions fmapEmpty / spikeCtx / spikeEnv / spikeRunState / spikeFile
- Heap (0): 
- Rules (4): wp_sseq[spike*], wp_annot_reindex[spike*], wp_annot[spike*], wp_env_invariant_stable[spike*]
- Wps (0): 
- Wpt (0): 
- Adequacy (9): driveJ_succ_eq[fmapEmpty][spike*], drive_succ_eq[fmapEmpty][spike*], spike_engine_adequacy_alloc[spike*], SemTriple_iff_U[spike*], spike_engine_adequacy[spike*], driveJ_scrutinee[fmapEmpty][spike*], drive_scrutinee_env[fmapEmpty][spike*], drive_scrutinee[fmapEmpty][spike*], spikeCtx_labels_none[spike*]
- TotalAdequacy (0): 
- Lang (0): 
- EnvLaws (2): fmapLookupBy_addBy_empty[fmapEmpty], symFrame_empty[fmapEmpty]
- Round (0): 
```

```
## F. Frag constructors (environment)
- 18: Frag.val_pure, Frag.store, Frag.load, Frag.create, Frag.sseq, Frag.annot, Frag.save, Frag.if_, Frag.run, Frag.sseq_spec, Frag.pure_sym, Frag.load_op, Frag.sseq_sym, Frag.memop_vals, Frag.memop_op, Frag.store_op, Frag.case_value, Frag.wseq
- StraightFrag 6: StraightFrag.val_pure, StraightFrag.store, StraightFrag.load, StraightFrag.create, StraightFrag.sseq, StraightFrag.annot
```

```
list_reverse_certified_production  [theorem; ProdLoopExhibit] | spine reached: Decomp.step_factor, launchResources, spikeCells_alloc, stateInterp_readout, loop_step_frag, driver2_done, finalize_done, wpt_driver_done_alloc, wpt_driver_aux, prod_run_eqJ, drive_after_setup, wpt_create, wpt_load_at, wpt_store_at, wpt_load_cell_at, wpt_store_cell_at, blockSpecsT_intro, wpt_frame_labels, storeM_success, allocateObject_success
list_reverse_certified_production  [theorem; ProdLoopExhibit] | landmarks (suffix): [genHeap_init, step_ctx, storeM, loadM, allocateObject, eqPtrval, runND, drive, initial_driver_state, driver2, finalize, action_request_sequential2]
list_reverse_certified  [theorem; ListRevExhibit] | spine reached: engine_step_matchU, Decomp.step_factor, stepDischarge_run, wps_sound, spike_step_adequacy, engine_adequacyU, engine_adequacyJ, drive_classifyU, spikeCells_alloc, stateInterp_readout, wps_load_at, wps_store_at, wps_load_cell_at, wps_store_cell_at, blockSpecs_intro, wps_frame_labels
list_reverse_certified  [theorem; ListRevExhibit] | landmarks (suffix): [wp_strong_adequacy_gen, genHeap_init, step_ctx, storeM, loadM, allocateObject, eqPtrval]
project_triple_alloc  [theorem; Adequacy] | direct in-package consumers (1): struct_create_store_adequacy
wps_sound  [theorem; Wps] | direct in-package consumers (9): arr_wp_readout, case_wp_readout, fib_wp_readout, loop_wp_readout, lr_wp_readout, struct_create_store_adequacy, struct_wp_readout, wps_sound_frame, wseq_wp_readout
wpt_sound  [theorem; Wpt] | direct in-package consumers (2): wpt_strongly_normalizing, wpt_strongly_normalizing_alloc
```

Scratch used during the audit (`~/.cache/heaplang-audit/`, outside
the tree) was removed at the end of the session; the script above is
the complete instrument.
