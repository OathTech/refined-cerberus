# Range audit: E1 (`04059dc..3e75a1e`, the emitted-Core dialect slice 1) — 2026-09-05

**VERDICT: PASS WITH FIXES REQUIRED — grade A− (the logic and the mirror are exact against the engine at the pin; the fixes are documentary and hygienic, but two of them are shop-window surfaces now stating falsehoods and must land before or with the merge).**

Auditor: fresh, independent, on the fixed detached copy `worktrees/audit-e1-3e75a1e`
(HEAD `3e75a1e`, detached). Standard: `docs/AUDIT-BRIEF.md`; the mirror-OCaml
doctrine (every mirrored engine behaviour = the generated Lean at the pin
`f95ef8d9c`, exactly). Every lake/lean invocation went through
`scripts/capped` (`CERB_MEM_MAX=64G` for the first FULL gate, then `40G` on
the orchestrator's mid-audit instruction; one builder at a time). Nothing
committed, merged or pushed; no other worktree touched. Scratch lived in the
copy's untracked `.audit-scratch/` (deleted at the end; its verbatim outputs
are quoted below). Provenance: [AUDITOR] for everything I measured or judged;
quotes are verbatim; tallies marked DERIVED are mine.

Range: `c6c17bd` (library + exhibits adapted), `0171921` (rules, the acceptance
exhibit, the corpus speedbump, witnesses, manifest, pins), `74ec807` (records,
census), `3e75a1e` (DECISIONS). `git diff --stat`: 51 files, +42667/−6723
(32832 of the additions are the post snapshot).

## 0. What was measured (summary of methods)

- FULL gate run once on the copy (`scripts/test_unit.sh`, capped) — verdict
  tail quoted verbatim in §10; exit 0.
- The generated engine at the pin read arm by arm: `core_reduction.lem`
  283–310, 410–425, 508–520, 560–592, 650–665, 1098–1230, 1350–1400;
  `Core_reduction.lean:484` (the general arm's `let maybe_loc := get_loc
  e_annots; let th_st := match maybe_loc with …`, the closure
  `full_eval_pexpr'` bound BEFORE the rebinding, the two `Ebound` arms, the
  PCALL `push_exec_loc psym th_st.current_loc`, the RETURN arm, the
  `ACTION_REQUEST` `loc'`); `Annot.lean:299` (`get_loc`),
  `CerbLocation.lean:180` (`isLibraryLocation`), `core_eval.lem:640–651` /
  `Core_eval.lean:145` (`Civalignof`/`Civsizeof` at `alignofIval
  _lemReader_tagDefs`/`sizeofIval`), `CerbMem.lean:1299–1300`,
  `Core_aux.lean:302` (`mk_value_pe`), `Core_run_aux.lean:400`
  (`initial_core_run_state_given … sym_supply := sup`), `driver.lem:1872–1880`.
- The mirror read against it: `Step.lean` (`RunSup`, `Ctl`, `locUpd`,
  `locUpdTh`, `Ctl.upd`, `Ctl.callPush`, `MachineCtx.thread`, `redexAnnots`,
  `toValA`/`ofValA`, every constructor of `Step`), `Round.lean`
  (`MachineCtx.Embeds`, `CerberusRound`, `engine_step_matchU`, `OpenRound`,
  `frag_round_complete`, `complete_bound_*`, `complete_create_op`,
  `complete_beta_sym`), `Soundness.lean` (`Frag`, `PePure`, `requestLoc`,
  `step_ctx_bound_annot`, `step_ctx_beta_sym_annot`,
  `stepDischarge_create_eval`), `DriverCollapse.lean` (`ctlThread`,
  `loop_step_frag'`/`loop_step_frag`, `CtlTied`), `Adequacy.lean`
  (`DriverSafeCtl`, `MemTriple`, `SemTriple`, `MemTriple_alloc`),
  `ProdLoop.lean` (`DriverDoneAt`, `DriverDoneCtl`, `wpt_driver_aux`),
  `ProdEntry.lean` (`prodCtl`, `prod_run_eqJ`), `Wps.lean`/`Wpt.lean` (the
  `bound`/`create_eval` faces), `EmittedAExhibit.lean`, `Examples/CorpusE0.lean`,
  `scripts/corpus_skeleton.lean`, `Examples/MirrorCoverage.lean` (diff),
  `Audit.lean` (diff).
- An EXECUTABLE ENGINE PROBE (no mirror involved): the generated `step_ctx`
  run at ten located configurations (§1, verbatim in §A).
- The census reproduced from the two committed snapshots by my own parser
  and a token-level normaliser (§6); the HEAD snapshot regenerated and
  `cmp`'d; the 25 new pins' axiom sets computed independently (§6).
- The corpus speedbump planted eight ways by term surgery on `t1Main`
  without editing the tree (§8, verbatim in §A).
- The 143 package linter warnings classified by file and by `git blame`
  against the range (§9).

## 1. Annotations — the location update (PASS)

Engine (verbatim, `core_reduction.lem:1153–1164`):
```
    | (ctx, expr) ->
        let Expr e_annots expr_ = expr in
        let maybe_loc = Annot.get_loc e_annots in
        let th_st = match maybe_loc with
          | Nothing ->
              th_st
          | Just loc ->
              if Loc.is_library_location loc then
                th_st
              else
                <| th_st with current_loc= loc; |>
        end in
```
Generated `Core_reduction.lean:484` (verbatim fragment): `let  maybe_loc  :=
get_loc  e_annots;          let  th_st  := match  maybe_loc with  |  none =>
th_st |  some  loc1 => (               if  CerbLocation.isLibraryLocation
loc1 then                  th_st                else                  {  th_st
with current_loc :=  loc1  })`. Mirror `Step.lean:540`:
`def locUpd (a) (l) := match get_loc a with | none => l | some loc => if
CerbLocation.isLibraryLocation loc = true then l else loc` and `Ctl.upd c a :=
{ c with curLoc := locUpd a c.curLoc }` — EXACT. `get_loc` (Annot.lean:299)
returns the FIRST `Aloc`, skipping every other constructor — the mirror
calls the same generated function, so no re-implementation to diverge.

Original-thread evaluation, updated-thread successors: in the generated code
`let  full_eval_pexpr'  := (fun pe => full_eval_pexpr … th_st …)` is bound
at `Core_reduction.lean:484` BEFORE `let th_st := match maybe_loc …`, so the
closure captures the ORIGINAL thread; `wrap_expr`, `process_action` (hence
the `ACTION_REQUEST` `loc'` fallback `th_st.current_loc`) and the PCALL
`push_exec_loc psym th_st.current_loc` are bound AFTER it and read the
UPDATED thread. The mirror agrees: `evalPexpr` carries no location;
`OpenRound.eval_uncovered` and every `*_kill` equation are stated at the
ORIGINAL `ctl.curLoc`; `requestLoc (locUpdTh an th) loc` (Soundness.lean:1497)
is the updated thread's; `Ctl.callPush` pushes `push_exec_loc f (locUpd a
c.curLoc) c.execLoc`. Successor controls: every general-arm `Step` rule ends
in `ctl.upd a` at the REDEX node's list (`Step.ctl_cases`, Step.lean:2480:
`(∃ a, ctl' = ctl.upd a) ∨ call ∨ ret`); `run`/`call` use `redexAnnots e`,
whose four clauses (Esseq/Ewseq-left on `toVal e1 = none`, the guarded
`Eannot` descent, the `Ebound` descent, Step.lean:958) match `get_ctx`'s
decomposition (lem:521–589) — `toVal e = some` ⟺ `is_irreducible e` (both
accept `v` and `{A}v`, both reject `{A}{B}v`; lem:195–207 vs Step.lean:341).
The ANNOTS-merge successor `Expr (a1 ++ a2)` matches lem:301–304 `Expr
(annots ++ annots2)`. The value arms (PROGRAM-DONE/RETURN/REMOVE-ANNOT,
lem:1102–1151) precede the general arm and do not write — mirrored by
`ret`/`ret_annot` leaving `lc`.

`engine_step_matchU` (Round.lean:1043) is generic in `a` and proves the
successor thread `M.thread c'.1 c'.2.1 c'.2.2.1` with `current_loc :=
ctl'.curLoc` (`MachineCtx.thread`, Step.lean:640) — the theorem IS the
arm-by-arm agreement; it is trio-exact (§6). Executable probe of the
GENERATED `step_ctx` (§A.1, no mirror): non-library `Aloc` → `current_loc`
becomes it; library `Aloc` (`libcore/…`) → unchanged; `Astd`/`Astmt`/`Aexpr`
only → unchanged; REMOVE-ANNOT (value arm) → unchanged; `bound(bound(v))` →
descends to the inner `bound(v)` and reads the INNER node's `Aloc` (library
→ unchanged), exactly `redexAnnots`; a `store` at a LIBRARY `Action` loc
under a non-library node → request at the node's location (`requestLoc`).

Annotation forms: `Frag` is generic in `an` on every constructor, in `pa`/`pb`
on patterns and in the pexpr lists of `PePure`, so NO annotation form the
elaborator emits is rejected by `Frag`; the `Astd "§6.5#2"` on every corpus
`bound` is inert (`get_loc` skips it; probe §A.1 line 3). Answered: nothing
rejected, every `Astd` handled.

## 2. `Ebound` (PASS)

`get_ctx (Ebound e)`: `if is_irreducible e then [(CTX, expr)] else map (Cbound
annot ·) (get_ctx e)` (lem:563–568) = `Step.bound_ctx` (guards `jumpRedex? b =
none`, `callRedex? b = none`, `toVal b = none`) + `Decomp.bound`. REMOVE-BOUND
(lem:1214–1226): `bound({A}v) → wrap_expr expr'` with `expr'` the INNER value
node and `bound(v) → wrap_expr expr'` the value node verbatim, both at the
location-updated thread = `Step.bound_annot : Expr a (Ebound (ofValA (.annot a1
a2 b1 ds v))) → ofValA (.pure a2 b1 v)` (the inner node `Expr a2 (Epure (Pexpr
b1 () (PEval v)))` verbatim, `ds` dropped) and `Step.bound_pure`, controls
`ctl.upd a`. Engine equations `step_ctx_bound_annot` (Soundness.lean:1911:
`[Step_tau2 "CTX, Ebound Eannot(value)" TSK_Misc { locUpdTh an th with arena
:= apply_ctx ctx (ofValA (.pure a2 b1 v)) }]`) and `step_ctx_bound_pure` are
pinned trio-exact. `is_unseq_with_ccall_aux` resets at `Cbound` (lem:514):
`Decomp.unseq_ccall_false` exists (Soundness.lean:744 `| bound _ ih => simpa
[is_unseq_with_ccall_aux] using ih`) and is consumed in Round/DriverCollapse.
Completeness: `bound(v)`/`bound({A}v)` are always mirror steps
(`complete_bound_pure/_annot`); `bound({A}{B}v)` descends to the merge
(`is_irreducible` false, `toVal` none) then REMOVE-BOUND; `bound(bound(v))`
descends (probe §A.1 line 5). The pair is complete: the engine's two
REMOVE-BOUND patterns are exactly `is_irreducible`'s two value shapes.

## 3. Constructor constants and `create_eval` (PASS)

`evalTyCtor tds .Civalignof ty = some (Vobject (OVinteger (CerbMem.alignofIval
tds ty)))` / `.Civsizeof … sizeofIval` (Step.lean:1328) = the generated
`Civalignof, some [Vctype ty1] => … (CerbMem.alignofIval _lemReader_tagDefs)
ty1` (Core_eval.lean:145; lem:648–651), at `M.tagDefs` = the reader
`step_ctx` is applied to. The engine evaluates the argument list first
(`exception_undef_mapM self pes`); `PePure.ctorTy` admits only a LITERAL
`Vctype ty` argument, on which `self` is the identity — fail-closed for any
other operand (outside `PePure`). The fuel idiom is kept: `peDepth (PEctor _
[pe]) = 1 + peDepth pe` and `Frag.create_op` carries `peDepth pe1/pe2 ≤
lemDefaultFuel` (`alignofIval` itself is not fuel-parametric at this call
site; the docstring at Step.lean:1316 says so). `Step.create_eval` = the
Create `(_, _)` arm's `ACTION_EVAL "eval operands of Create"` (lem:656–661;
the generated text at Core_reduction.lean:424 quoted in my notes), successor
`Expr a (… Create (mk_value_pe align) (mk_value_pe ty) …)` at `ctl.upd a`,
pinned to (integer, ctype) so the successor IS `Frag.create`; the
non-(integer, ctype) pair is `ACTION_ILLTYPED "Create"` at distance one
(`complete_create_op` (ii), the `alloc_op` template); kills (iii);
residual (iv). Manifest row `Frag.create_op` RULE (`wps_create_eval`/
`wpt_create_eval`, consumer `EmittedAExhibit`) — correct classification;
the row text names the ACTION_EVAL round and defers the create's own
variants to the `create` rows. `create_alignof_round` (MirrorCoverage) is a
genuine `engine_step_matchU` instance at generic `M`.

## 4. The two live-state changes (PASS, one design caution)

(A) `current_loc`. `ctlThread th₀ e ρ ctl` sets `current_loc := ctl.curLoc`
(DriverCollapse.lean:2216). `loop_step_frag'`/`loop_step_frag` take `hcl :
th₀.current_loc = ctl.curLoc` and deliver `{ th₀ with … exec_loc :=
ctl'.execLoc, current_loc := ctl'.curLoc }` for EVERY `Step` — the
control-preserving rounds, the CALL (`step_ctx_call_ws`: `exec_loc` pushed at
`locUpd a c.curLoc`, matching `push_exec_loc psym th_st.current_loc` at the
updated thread) and the RETURN (`exec_loc`/`current_loc` untouched, matching
the RETURN arm which writes `current_proc_opt`/`env`/`stack0`/`arena` only —
verified at `Core_reduction.lean:484` "reduction: RETURN" fragment). Both are
pinned trio-exact (§6), so the tie is a theorem at every round; the C4 tie
survives with the location added to it. `DriverSafeCtl`/`DriverDoneCtl` keep
the thread as `ctlThread … ctl` and existentially quantify `lcfin spfin` in the
final thread — correct (RETURN never pops them; the final location is
whatever the last general-arm round wrote).

Under-constraint check: the exports lost `hcl : th₀.current_loc =
M.currentLoc` (`engine_adequacy`, `_alloc`, `wpt_driver_cps`,
`wpt_driver_done_procs`; and the DEFINITIONS `MemTriple`/`SemTriple`/
`MemTriple_alloc` lost it in their bodies — invisible to the census, which
records types). This is a STRENGTHENING: `th₀` is now arbitrary and the
statement holds at every `ctl.curLoc`, the thread's location being fixed by
`ctlThread` from the control. Nothing is under-constrained: the location the
run starts at is `ctl.curLoc`, and the production route fixes it to the
parked thread's `other "Driver.drive"` (`prodCtl`, `prod_run_eqJ`'s
`DriverDoneAt … (CerbLocation.other "Driver.drive") …`, `driver.lem:1876`).
The four readouts generalised over `(lc : Loc) (sp : RunSup)` are likewise
strengthenings.

(B) Supplies. `RunSup := ⟨sym, excl⟩` on `Ctl.sup`. "Untouched by every E1
rule": VERIFIED — every `Step` constructor's successor control is `ctl.upd a`
(`upd_sup : (c.upd a).sup = c.sup := rfl`), `ctl.callPush …` (`callPush_sup
:= rfl`), or `⟨κ, p, ℓ, lc, sp⟩` with the same `sp` (`ret`, `ret_annot`);
`Step.ctl_cases` is the closed enumeration. `Embeds.sym/excl` tie
`dst.core_run_state0.sym_supply/excluded_supply` to `c.2.2.1.sup`, and
`CerberusRound` fixes `rs'.sym_supply = c'.2.2.1.sup.sym ∧ rs'.excluded_supply
= c'.2.2.1.sup.excl` — so `engine_step_matchU` proves, for every E1 round
INCLUDING the PCALL `Step_with_runstate2 (RSK_eval …)` round, that the
supplies are unchanged. Sound for E5's writers: an E5 rule that draws a
fresh symbol will state `sup' = ⟨sup.sym + 1, …⟩` on the successor control
and `CerberusRound`'s shape already demands exactly that equality — no
re-shape of `Config`, `Embeds` or `CerberusRound`.

Design caution (not a defect at E1 — the driver lanes leave the supplies
UNTIED, as the record says): `prodCtl.sup = default` (ProdEntry.lean:568,
i.e. `⟨0, 0⟩`), whereas the production initial run state has `sym_supply :=
sup` (generated `Core_run_aux.lean:400`, the statement's own `(sup : Nat)`
binder, possibly advanced by `initial_driver_state`'s draws). When E5 ties
the supplies in the driver lanes (a new `hsup` premise on `loop_step_frag`
and inside `DriverSafeCtl`/`DriverDoneCtl`), `prodCtl` must become
`prodCtl sup` (or carry the post-registration supply) and the four readouts'
`sp` binder is what makes that a local change. The nine production statement
TEXTS will not move (they do not mention `prodCtl`), so "E5 adds writers and
ties, not a re-shape" holds for the STATEMENTS; the record should say that
`prodCtl`'s `default` is a placeholder that E5 replaces. See N-1.

## 5. `BareHead` deleted (PASS)

Before E1, `BareHead` (a literal / `create` / `alloc` / `PtrEq` / a call)
restricted the plain-symbol binder's head so that the head never delivered
`{A}v`, because the mirror lacked LETS-ANNOT at that binder (the 2026-09-02
closure's gap (a), an OUT-OF-SCOPE row). E1 mirrors the arm:
`Step.sseq_sym_annot : Expr a (Esseq (symPat pa x bty) (ofValA (.annot a1 a2 b1
ds v)) e2) → (Expr [] (Eannot ds e2), update_env (symPat pa x bty) v (ev0 ::
evs), ctl.upd a)` = lem:416–423 `lets pat = {A}v in E2 --> {A} { v / pat } E2`,
`TAU "Esseq Eannot" (update_env pat cval env) (Expr [] (Eannot xs e2))` —
EXACT (the result node is `Expr []`, verbatim). Engine equation
`step_ctx_beta_sym_annot` (Soundness.lean:4315, `[Step_tau2 "Esseq Eannot"
TSK_Misc { locUpdTh an th with env := update_env …, arena := apply_ctx ctx
(Expr [] (Eannot ds e2)) }]`) pinned trio-exact; `complete_beta_sym` covers
both betas at `wa : SpikeValA`; probe §A.1 line 6 confirms the engine's
label and the location write. The fragment stays fail-closed at the binder
in the only sense that matters: every head shape it admits is a `Frag`
expression with a mirror rule; the annotated-head row is honestly NO-RULE
(the binder rules `wps_seq_sym`/`wpt_seq_sym` are stated at a bare head;
manifest row 121). `frag_round_complete`'s statement is verbatim the
2026-09-02 one; `OpenRound` keeps its two arms (`eval_uncovered` now reads
`c.2.2.1.curLoc`); the closure record's successor
(`docs/2026-09-05_fragment-closure-e1-notes.md`) is accurate on every point
I checked (five new rows, no new refusal/residual arm, the ORIGINAL-thread
kill locations).

## 6. Census, pins, snapshot (PASS with one record correction, R-2)

- HEAD snapshot regenerated (`lake env lean scripts/signature_snapshot.lean`,
  capped) and `cmp`'d against `docs/2026-09-04_e1-signatures-post.txt`:
  `CMP-IDENTICAL`, 32832 lines.
- My parser (records split on `----`): PRE 3081 / POST 3406 / ADDED 349 /
  REMOVED 24 / CHANGED 583 — the record's numbers reproduced exactly.
  Marker scan (the record's markers): 188 — reproduced exactly.
- REMOVED (24), all accounted for: 16 `BareHead.*` (incl. the pinned
  `BareHead.step` and sub-trio `BareHead.decomp_call_root`/`.not_annot`),
  `Frag.esize_step_bound` (consumerless after the re-cut; `Frag.pot_step_bound`
  is the live bound), `MachineCtx.Embeds.runState` (replaced by
  `labeled`/`sym`/`excl`), `MachineCtx.currentLoc`, `Step.CallOf.ne_same_ctl`
  / `Step.call_ne_same_ctl` (replaced by `…_ne_same_κ`/`…_ne_upd`),
  `get_ctx_annot_pure`, `is_irreducible_annot_pure`,
  `is_irreducible_merge_pure` (the `Expr []`-special-cased lemmas, subsumed
  by the generic `get_ctx_annot_*`/`is_irreducible_annot_of_nv`/
  `is_irreducible_merge`). Losing the `BareHead.step` pin is acceptable: the
  theorem's content (the head grammar always steps) is now
  `complete_beta_sym` + the head's own `Frag` rule; nothing pinned depended
  on it. [AUDITOR] agrees with the deletion over generalisation.
- The split "395 annotation-generalisation only": DERIVED by me with a
  token-level normaliser (drop `{x : List annot}`/`(x : List annot)` binder
  groups and the bound names, drop `[]` tokens and `_root_.`): 244 of the
  395 are pure annotation generalisation; of the remaining 151, at least 38
  carry NON-annotation content that the marker scan cannot see — the new
  constructors in `Frag/Decomp/PePure/Step.{casesOn,rec,recOn,below.*}`
  (`bound`, `create_op`, `ctorTy`, `bound_*`), `Decomp.lift_step` (a new
  `callRedex` hypothesis AND the successor control threaded as `ctl'`),
  `Step.sseq_ctx`/`wseq_ctx`/`annot_ctx` (new guard `hnc : callRedex? e1 =
  none`, `ctl'` threaded), `Step.run`/`jump_inv`/`run_of_jumpRedex`
  (`ctl.upd (redexAnnots e)`), `EngineMatchU.step`, `Frag.step`,
  `Frag.pot_step_bound`, `driverDoneCtl_step`, `Step.env_cons`, `Step.sameTail`,
  `esize/pot/jumpRedex?/callRedex?/evalPexpr/evalClass/isPePure.eq_def`,
  `Decomp.callRedex?_inv`, `Redex.callRedex?_some_inv`, `step_ctx_call_unknown`.
  The remaining ~113 are generalisation shapes my normaliser does not
  handle (`∃ an ra`, `List annot →` argument positions) — not read one by
  one. So the record's 395 is an UPPER bound on the annotation-only class
  and the frame rules' `ctl'`-threading + `hnc` guard is a real mirror-shape
  change that belongs in the FORCED class. R-2.
- The NINE production statements: `exhibitA_prod`, `fib_certified_production`,
  `counter_loop_certified_production`, `list_reverse_certified_production`,
  `dispose_list_certified_production`, `region_loop_certified_production`,
  `malloc_list_certified_production`, `fib_rec_certified_production`,
  `even_odd_certified_production` — ALL UNCHANGED (type text identical in
  the two snapshots). Also unchanged: `prod_run_eqJ_procs`,
  `prod_run_safe_procs`, `fib_rec_certified`, `even_odd_certified`,
  `SemTriple`/`MemTriple`/`MemTriple_alloc` (types), `DriverSafeCtl`/
  `DriverDoneCtl` (types).
- Before/after of the export texts that DID change (statements, from the
  snapshots):
  - `engine_adequacy`, `engine_adequacy_alloc`: `∀ {th₀ : thread_state},
    th₀.current_loc = M.currentLoc → DriverSafeCtl …` → `∀ (th₀ :
    thread_state), DriverSafeCtl …` (premise dropped — strengthening).
  - `wpt_driver_cps`: `hcl` dropped; binders `(lc : CerbLocation.Loc) (sp :
    RunSup)` added; controls `{ κ, proc := some p, execLoc := ℓ }` →
    `{ κ, proc := some p, execLoc := ℓ, curLoc := lc, sup := sp }` (and `ℓ'
    lc' sp'` in the continuation); the value-form change `w.erase`/`ofValA w`.
  - `wpt_driver_done_procs`: same pattern (`hcl` dropped, `(lc) (sp)` added,
    control literal gains the two fields).
  - `wpt_driver_done`, `wpt_driver_done_alloc`: conclusion `DriverDoneAt p Q th₀
    e₀ (ev00 :: evs0) σ₀ ψ k` → `DriverDoneAt p Q th₀ e₀ (ev00 :: evs0)
    ctl.curLoc σ₀ ψ k`.
  - `prod_run_eqJ`: premise `DriverDoneAt … [fmapEmpty] prodMem₀ ψ k` →
    `DriverDoneAt … [fmapEmpty] (CerbLocation.other "Driver.drive") prodMem₀ ψ k`.
  - `DriverDoneAt`: gains the `CerbLocation.Loc` argument.
  - `fr_wp_readout`, `eo_wp_readout`, `cs_wp_readout`, `cs_twp_readout`: `∀ (ℓ :
    exec_location)` → `∀ (ℓ) (lc : CerbLocation.Loc) (sp : RunSup)`, the
    control literal gains `curLoc := lc, sup := sp` (and `cs_twp_readout`'s
    post `csPost w.w w.ρ` → `csPost w.sv w.ρ`).
- Pins: the 25 new pins listed in `Audit.lean` — all trio-exact by my own
  `collectAxioms` run (`[Classical.choice, Quot.sound, propext]` for each of
  the 25, and also for the unpinned `loc_update_lib`, `loc_update_none`,
  and for `engine_step_matchU`, `frag_round_complete`, `loop_step_frag`,
  `loop_step_frag'`). 402 − 1 + 25 = 426 ✓.

## 7. The acceptance exhibit (PASS on content; R-1 on the "as the elaborator would" claim)

`exhibitA_prod_e1`'s statement text is `exhibitA_prod`'s VERBATIM modulo the
program name (checked by `diff` after renaming; identical). The proof route
is the generic one (`progAE1_wpt → wpt_driver_done_alloc → prod_run_eqJ`);
`progAE1` is in the E1 fragment (`progAE1_frag`), every location is a
non-library path (so the update fires), the value delivered is BARE
`Specified(7)`. All four exports pinned trio-exact.

Against the corpus (`docs/corpus-e0/*.annot.core`, ten files): the
elaborator (i) puts `Aloc`+`Astmt` on the `let strong` STATEMENT nodes and
`Aloc`(+`Aexpr`) on `pure`/`let weak` EXPRESSION nodes; (ii) leaves the
`create`/`store`/`load`/`kill` ACTION nodes WITHOUT `Expr` annotations (their
`loc` is in the `Action loc` field; t1Main's own transcription `act loc … =
Expr []` agrees), the one exception being the object-lifetime store
`{-# §6.2.4#6 #-}{-# <loc> #-} store(int, r, Unspecified(int))`
(t5_ifelse.annot.core:13–14) which carries `Astd`+`Aloc`; (iii) never emits
`bound(store(…))` or `bound(load(…))` — a `bound` wraps a full expression
whose body is a `pure`/`let weak …` (a load appears only as `let weak a =
{loc}pure(p) in load(int, a)`; a declaration's store is unbound and
unannotated; an assignment's store is `neg(store …)` under E5's protocol).
`progAE1` puts `[Aloc, Aexpr]` on the create/store/load action nodes and
wraps bare `store`/`load` actions in `bound`. That is a legitimate E1
synthetic that exercises the location update at every round (stronger than
the corpus for the purpose), but it is NOT "exhibit A in the emitted shape
as the elaborator would place annotations": the docstring's "annotation
lists as the elaborator attaches them" and the record §4's "as far as E1
allows" over-state. R-1 (wording).

## 8. The corpus speedbump (PASS as a speedbump; blind spots as documented; N-2)

What it compares: for each `corpusTable` row, the preorder token stream of
the transcribed term's EXPRESSION nodes — per node the printed annotations
(`std:<Astd>` in reverse list order, then `loc` if `get_loc` finds an `Aloc`)
then the node keyword (`lets`/`letw`/`seq`/`bound`/`unseq`…`endunseq`/
`pure`/`store`/…) — against the same stream tokenized off the emitted text
(`tokenizeProc text "main"`; 56 tokens for t1). Pure expressions are opaque
leaves; patterns, symbols, ctypes, memory orders, `Action` locs, `Astmt`/
`Aexpr` (which the printer does not print at all) are NOT compared. A wrong
transcription with the same skeleton PASSES (plants A, D, E below). Fail-
closed where blind: an `Astd`/`Aloc` inside a pure expression is an ERROR
(plant H), a marker inside an opaque region is an ERROR, a missing corpus
file is `FAIL: cannot read …` + exit 1 (`rowStreams`), a tokenizer/skeleton
error is FAIL. NOT fail-closed: a corpus file with NO table row is silently
unchecked (the table drives, the directory is not swept) — acceptable for a
speedbump whose rows are added per slice, but worth one line in the header.
Plant log verbatim in §A.2: constant 3→4 PASSES (blind spot, as documented);
`Astd` string change RED; root `Aloc` dropped RED; annotation ORDER swap
PASSES (order not observable — `get_loc` semantics make it engine-irrelevant
unless two `Aloc`s are present); symbol x→y PASSES (blind spot); `let strong`
→ `weak` RED; `Aloc` on a pure operand ERROR (fail-closed); the script's own
two plants RED. The instrument does what its header says, no more.

## 9. Hygiene regression (H-1, fix required or register)

Package linter warnings at HEAD: 143 (my gate log, `warning: CerberusHeapLang/*`
lines, deduplicated = 143; the orchestrator's 62 → 143). By `git blame` of
each warning's line against the four range commits (DERIVED): 79 NEW-by-line
+ 64 pre-existing (the 62 of KOI C5 plus 2 whose lines the range re-flowed).
All but one are `linter.unusedSimpArgs`; one is an unused variable.

| File | New | Site(s) | What | Fix |
|---|---|---|---|---|
| `Step.lean` | 56 | 2696–2729 (30 arms of the `callRedex?`-some inversion), 2738 (2), 2797/2799, 2813/2815, 2920/2922, 3126–3164 (30 arms of the `jumpRedex?`-some inversion), 3166 (2) | `simp [callRedex?, annotRooted] at hc` / `simp [jumpRedex?, annotRooted] at hj0` / `simp [jumpRedex?] at hj`, `simp [callRedex?] at hc` — the flagged argument (`annotRooted`, and at 2797/2813/2920 `jumpRedex?`/`callRedex?`) is unused | delete the flagged simp argument at each site (or `simp only [callRedex?] at hc`) |
| `Wps.lean` | 8 | 1392, 1565, 2166, 2372 (2 each) | `simp [callRedex?, annotRooted] at h` — both unused | `cases h` / `simp at h` |
| `Wpt.lean` | 8 | 1800, 1996, 2152, 2362 (2 each) | same | same |
| `Potential.lean` | 4 | 121, 166 (cols 44, 51: `pot`, `createOpRedex`) | `simp [esize, pot, createOpRedex]` in the new `create_op` arm | `simp [esize]` (mirror the `alloc_op` arm once it is fixed too) |
| `EmittedAExhibit.lean` | 2 | 167, 235 | `simp only [SpikeVal.val, SpikeVal.mergeInto]` — `SpikeVal.mergeInto` unused | `simp only [SpikeVal.val]` |
| `ProdLoop.lean` | 1 | 195 | `wpt_driver_aux` quantifies `(sp : RunSup)` that its conclusion `DriverDoneAt p Q th₀ e (ev0 :: evs) lc σ ψ k` never uses | drop the binder (an unpinned theorem; the callers pass `_`) — see H-2 |

None is proof-unsafe to fix (deleting an UNUSED simp argument cannot change
the simp set that fired). I did not apply them (not my job per the brief).

## 10. Records (PASS; corrections listed)

FULL gate on the copy (`scripts/test_unit.sh`, capped, `CERB_MEM_MAX=40G`; the
build was a cache REPLAY — `ℹ [458/460] Replayed CerberusHeapLang.Audit` — of
the primed tree, so the warnings are the tree's, not a partial rebuild's).
Verdict tail, UNMODIFIED lines matching
`^==|^ok:|^info: CerberusHeapLang|^ALL GATES|^Build completed|^BOUNDARY|^ALLOWLISTED|^FAIL`,
verbatim:
```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:627:0: CerberusHeapLang export pins: 426 trio-exact
info: CerberusHeapLang/Audit.lean:627:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (3777 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:627:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (5846 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (460 jobs).
ok: cerberus-heaplang build green
== speedbump: rule-use and classification manifest (regenerate; red on a red row or drift) ==
ok: capability manifest regenerated, no drift
== speedbump: corpus skeleton (hand-transcribed emitted Core vs docs/corpus-e0; scripts/corpus_skeleton.lean) ==
ok: corpus skeleton — every transcription matches its emitted text, every plant mismatches
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — 15 core modules, none imports an exhibit/example/production module
== speedbump: client boundary (positive clients mention no logic internals; scripts/boundary_check.sh) ==
ok:   Exhibit — 0 internals mentions
ok:   LoopExhibit — 0 internals mentions
ok:   FibExhibit — 0 internals mentions
ok:   ArrayExhibit — 0 internals mentions
ok:   ListRevExhibit — 0 internals mentions
ok:   TreeRotExhibit — 0 internals mentions
ok:   CaseExhibit — 0 internals mentions
ok:   WseqExhibit — 0 internals mentions
ok:   StructExhibit — 0 internals mentions
ok:   AllocExhibit — 0 internals mentions
ok:   DisposeExhibit — 0 internals mentions
ok:   RegionLoopExhibit — 0 internals mentions
ok:   MallocListExhibit — 0 internals mentions
ok:   FibRecExhibit — 0 internals mentions
ok:   TwoLabelExhibit — 0 internals mentions
ok:   EvenOddExhibit — 0 internals mentions
ok:   EmittedAExhibit — 0 internals mentions
ok:   Examples.CallSmoke — 0 internals mentions
ok:   Examples.ReadinessSmoke — 0 internals mentions
ok:   Examples.Layout — 0 internals mentions
ok:   Examples.CorpusE0 — 0 internals mentions
BOUNDARY: 21 modules checked, 0 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
```
Exit status 0 (`scripts/test_unit.sh 12.15s user 1.83s system 98% cpu 14.190
total`). Line for line identical to the DECISIONS E1 entry's quoted block
except its final `GATE-EXIT=0`, which `scripts/test_unit.sh` does not print
(no such string in the script) — it is the orchestrator's wrapper line; the
worker record §10 correctly omits it. Not a finding; noted so the next
reader does not look for it.

Counts vs the tree: manifest tail `MANIFEST: 25 constructors, 52 variant rows
(32 RULE, 0 RULE-TOTAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 16 NO-RULE, 4
OUT-OF-SCOPE), 0 red, 19 consumer modules` ✓ (record and DECISIONS); `Frag`
has 25 constructors ✓; pins 426 ✓; snapshots 3081/3406 ✓; t1 56 tokens ✓;
progAE1 budget 13 ✓. DECISIONS is chronological (…2026-09-04 entries, then
the 2026-09-05 E1 entry last). The E1 entry's "three commits on main
04059dc" = c6c17bd/0171921/74ec807 ✓ (3e75a1e is the entry itself).

KNOWN-OPEN-ITEMS entries E1 must change (for the follow-up, not blocking):
- Header "State: candidate `hygiene-h1` head" → the E1 candidate.
- E (expected FULL tail): 402 → 426 pins; "50 rows; 30 RULE / 0 / 15 NO-RULE
  / 5 OUT-OF-SCOPE" → "52 rows; 32 / 0 / 16 / 4"; add the corpus-skeleton
  speedbump line; `BOUNDARY: 19 modules` → `21 modules`.
- C5: 62 → 143 (81 introduced by E1, 79 new-by-line; the table in §9).
- B8: add that located Core / the C elaborator's annotations are NO LONGER
  outside the fragment (E1); `Eccall`/concurrency/external calls unchanged.
- B7: unchanged in kind; `OpenRound.eval_uncovered` now reads the control's
  `curLoc` — one cite update.
- B14: the annotated-head `sseq_sym` row moved OUT-OF-SCOPE → NO-RULE (16).
- B12: both bridges now also carry the location (cite `loop_step_frag`'s `hcl`).
- D (errata register): the census split correction (R-2) once DECISIONS records it.

## 11. ARCHITECTURE staleness — every sentence E1 falsified (D-, for the docs pass)

`cerberus-heaplang/ARCHITECTURE.md` is not in the range's diff (confirmed by
`git diff --stat`). Falsified sentences, by line at HEAD:
- :84 "`Frag e` … has 23 constructors (`:4150`–`:4314`)" → 25 (`Soundness.lean:4407`).
- :92–94 "The plain-symbol binder's head is restricted to the bare-value
  producers `BareHead` (`:3981` …)" → `BareHead` deleted; any fragment head.
- :96–103 the whole bullet "*It is annotation-free* … every node is `Expr []`
  … This package keeps that field immutable in `MachineCtx.currentLoc` …
  The programs proved here are authored Core. (The mover, named there: make
  `current_loc` live state.)" → the fragment is annotated; `current_loc` is
  live on `Ctl.curLoc`; the mover landed.
- :117–119 "`Ctl := ⟨κ, proc, execLoc⟩` … the three `thread_state` fields"
  → five fields `⟨κ, proc, execLoc, curLoc, sup⟩`.
- :120–122 "`MachineCtx` … its eight fields are …, `currentLoc` and
  `runState`" → seven fields; `currentLoc` gone; `runState`'s live supplies
  moved to `Ctl.sup` (only `labeled` is tied).
- :127–128 "Every other rule threads the control unchanged (`Step.ctl_cases`)"
  → every other rule writes `curLoc` (`ctl' = ctl.upd a`).
- :326 "the entry control `⟨[], some p, ℓ⟩`" → `⟨[], some p, ℓ, lc, sp⟩`.
- :470 "402 pins" → 426.
- :482–483 "`BareHead.decomp_call_root` and `BareHead.not_annot` have `[propext]`" → gone.
- :606–608 "`hcl : th₀.current_loc = M.currentLoc` — … (the annotation-free
  fragment never rewrites it, §1)" → the premise no longer exists.
- :659–660 "23 constructors, 50 rows — 30 RULE, …, 15 NO-RULE, 5 OUT-OF-SCOPE,
  0 red, 18 consumer modules" → 25 / 52 / 32 / 16 / 4 / 19.
- :671 "18 modules: the sixteen program exhibits, …" → 19 (EmittedAExhibit).
- :688 "`BOUNDARY: 19 modules checked`" → 21.
- :709–713 "Five OUT-OF-SCOPE variants … or, for the annotated head at the
  symbol binder, outside `Frag` itself by `BareHead` … an annotated value at
  the plain-symbol binder" → four OUT-OF-SCOPE; the annotated head is
  admitted, mirrored, NO-RULE.
- §2.2's description of `CerberusRound` ("with the run state replaced by
  some `rs'` whose `labeled` fiber is untouched") is now incomplete: the
  supplies are tied to the successor control.
- §1 glossary "*a tie* … The ties: the thread, the memory, the extern table,
  the file, the registration predicate …" → add the location (in
  `ctlThread`) and, at E5, the supplies.
- The two-loop text (§4 "The ruled reading") is untouched by E1 — nothing to change.
Also stale in-code: `Adequacy.lean:1272` and `:1447` docstrings ("with the
context's `current_loc`") — D-3.

## 12. Grumpy read of the new Lean

- `Step.lean`: the E1 rules are stated in the engine's own shapes with cites
  at each; `Ctl.upd`/`callPush`/`locUpd` are small and definitional
  (`rfl` simp lemmas). Good. The `callRedex?`/`jumpRedex?` inversion proofs
  (2694–2740, 3124–3168) are 30-arm copy-paste with a redundant simp
  argument in every arm — the linter noise of §9; a `first | simp [callRedex?]
  at hc | …` combinator or a `Step.not_callRedex_of_general` lemma would
  halve them. Not blocking.
- `Round.lean`: `Embeds.sym/excl` + the `CerberusRound` equalities are the
  right E5-ready shape; nothing over-elaborate.
- `EmittedAExhibit.lean`: a clean client (0 internals mentions); the wps and
  wpt proofs are the usual near-duplicates (house pattern). `hnolabel` names
  `(procCtl mainSym).proc` while the launch uses `ctl := prodCtl` — works by
  reducibility, reads oddly; write `prodCtl.proc`.
- `Examples/CorpusE0.lean`: a hand tokenizer for printed Core inside the
  package — 520 lines of `partial def`s that are instrument code, not logic.
  It is correctly `example-support`, imports only `Step`, and the boundary
  check covers it; acceptable for a speedbump. The `t1File` path
  `"refined-cerberus/worktrees/dialect-e0/docs/corpus-e0/t1.c"` is an
  environment artefact of the E0 worktree baked into the transcription; it is
  a non-library path (harmless) and the skeleton compares `loc` presence
  only, but it should be noted in the header as "verbatim from the oracle's
  output, path immaterial".
- `scripts/corpus_skeleton.lean`: clear, fail-closed on read/tokenize/skeleton
  errors, plants permanent. Fine.
- Records: precise, cites accurate where I checked (≈30 cites), the FALSIFIED
  design premise ("t1 parses as `Frag`") recorded honestly.

## Findings, ranked

| # | Grade | Finding | Evidence | Fix required | Premise verified by measurement |
|---|---|---|---|---|---|
| C-1 | Correctness of SHOP-WINDOW SURFACES (blocking per the brief) | README, CLAIMS and WALKTHROUGH state the pre-E1 world as fact: README:44–47 "the plain-symbol binder's head restricted to the bare-value producers `BareHead`"; README:121–122 "23 constructors, 50 rows, 30 RULE, … 15 NO-RULE, 5 OUT-OF-SCOPE"; README:158–176 "is stated at `Expr []` … this package keeps `currentLoc` in the immutable `MachineCtx` … Located Core … is therefore outside `Frag` … The mover is to make `current_loc` live state"; README:639 "The fragment is annotation-free (`Expr []` at every node); located Core is outside `Frag`"; README:656 "the pure and annotation rules are stated at `Expr []`"; CLAIMS.md:44 "located Core (every C-elaborated program): outside `Frag`"; WALKTHROUGH:40–47 quotes `MemTriple` WITH `th₀.current_loc = M.currentLoc →` (the definition no longer has it); :87 "whose `current_loc` is the context's"; :1472–1474 "the engine's successor carries `M`'s immutable fields, `current_loc` included — which is why the fragment is annotation-free"; :1782–1790 the "Located Core" not-covered bullet; :1797–1799 "stated at the empty annotation list `Expr []`". All under-claims (they deny coverage that now exists), none over-claims — but false on the shop window. | Docs pass on README ("Scope, exactly", the counts, the limitation table rows), CLAIMS "Not claimed" (drop "located Core"; consider a C-row for the dialect features), WALKTHROUGH (re-quote `MemTriple`; the two "why annotation-free" sentences; the not-covered list). Land with the merge or in the immediately following docs slice — the brief says blocking. | yes (grep + census + definitions read) |
| H-1 | Hygiene regression | 62 → 143 package linter warnings; 79 new-by-blame (+2 re-flowed) — table in §9 | delete the flagged unused simp arguments at the listed sites; drop `wpt_driver_aux`'s `sp` | yes (gate log, blame) |
| R-1 | Record/docstring over-claim | `EmittedAExhibit.lean` docstring "annotation lists as the elaborator attaches them: `Aloc` + `Astmt` on statement nodes, `Aloc` + `Aexpr` on expression nodes, `Astd` on the `bound`s" and record §4 / DECISIONS "exhibit A in emitted shape": the corpus never annotates action nodes with `Aloc`/`Aexpr` (except t5's lifetime store, `Astd`+`Aloc`) and never emits `bound(store …)`/`bound(load …)`; `progAE1` does both | reword to "a synthetic in E1's dialect features (annotations on every node incl. action nodes, `bound` around the two actions, `Ivalignof`) — placements chosen to exercise the location update at every round; the elaborator's own placements are t1Main's" | yes (all ten `.annot.core` files grepped) |
| R-2 | Record tally overstated | "395 change only by the annotation generalisation" (record §9, DECISIONS): ≥ 38 of them carry new constructors / `ctl'` threading / the new `hnc : callRedex? e1 = none` guard on `Step.sseq_ctx`/`wseq_ctx`/`annot_ctx` / `redexAnnots` controls (§6 list) | a later DECISIONS entry (append-only): "188 marker-scan FORCED + ≥ 38 further shape changes the scan missed (frame rules threaded and guarded, new constructors) + ≤ 357 annotation-only"; the frame-rule change deserves a sentence in the record's §1 | yes (token normaliser + keyword scan) |
| R-3 | Record/docstring misdescription | Record §5 and `MirrorCoverage.lean` header: "`loc_update_nonlib`/`_lib`/`_none` and `store_located_step` … all `engine_step_matchU` instances" — the three `loc_update_*` are lemmas about the mirror's `Ctl.upd` alone and `store_located_step` is a `Step` (mirror) witness; none touches the engine. The engine-level witnesses are `bound_*_round`, `create_alignof_round`, `sseq_sym_annot_round` (generic `a`) | reword; optionally add one `engine_step_matchU` instance at a concrete `Aloc` library location (cheap; my §A.1 probe is the executable version) | yes (read the four statements) |
| H-2 | Over-generalised statement | `wpt_driver_aux` (ProdLoop.lean:181–200) binds `(sp : RunSup)` unused in its conclusion (the linter's ProdLoop:195) | drop the binder | yes |
| N-1 | Design caution for E5 | `prodCtl.sup = default` (ProdEntry.lean:568) is a placeholder; the production initial state has `sym_supply := sup` (generated `Core_run_aux.lean:400`) — sound now (supplies untied in the driver lanes) but E5's tie will need `prodCtl sup` and a `hsup` premise threaded through `loop_step_frag`/`DriverSafeCtl`/`DriverDoneCtl`; statement texts of the nine stay | one sentence in the record §2(B) | yes |
| N-2 | Speedbump scope | `corpus_skeleton` is table-driven: a corpus file without a `corpusTable` row is never checked; blind to constants/symbols/patterns/order (documented; plants §A.2) | one header line; optional: list the un-rowed corpus files in the report table | yes (plants) |
| N-3 | Unpinned trio-exact witnesses | `loc_update_lib`, `loc_update_none` are trio-exact but unpinned while `loc_update_nonlib` is pinned | pin all three or none | yes |
| D-1 | ARCHITECTURE staleness | §11 list (16 sentences) | the follow-up docs pass | yes |
| D-2 | KOI updates | §10 list | the follow-up docs pass | yes |
| D-3 | In-code docstrings | `Adequacy.lean:1272`, `:1447` "with the context's `current_loc`" | reword | yes |

No T- (trust) finding: no unsound or vacuous rule, no statement saying other
than the docs say (the docs' errors are under-claims), no construct claimed
covered without a proved and consumed rule, no adequacy hole; the 25 new
pins and the four bridge theorems are trio-exact; the mirror is exact
against the generated engine at every E1 arm I read, and the executable
probe agrees.

## A. Plant and probe logs (verbatim)

### A.1 Engine probe — the GENERATED `step_ctx` on located configurations (`.audit-scratch/EngineProbe.lean`, `lake env lean`, capped, exit 0)
```
## bound(v) at NON-library Aloc: 1 step(s)
   Step_tau2[CTX, Ebound(value)] loc=exhibitA.c:1:17-61 arena=<core_expr> env_frames=1
## bound(v) at LIBRARY Aloc: 1 step(s)
   Step_tau2[CTX, Ebound(value)] loc=other_location(Driver.drive) arena=<core_expr> env_frames=1
## bound(v) at Astd/Astmt/Aexpr only: 1 step(s)
   Step_tau2[CTX, Ebound(value)] loc=other_location(Driver.drive) arena=<core_expr> env_frames=1
## bound({A}v): dynamic annots dropped, inner node verbatim: 1 step(s)
   Step_tau2[CTX, Ebound Eannot(value)] loc=exhibitA.c:1:17-61 arena=<core_expr> env_frames=1
## bound(bound(v)): frame descent: 1 step(s)
   Step_tau2[CTX, Ebound(value)] loc=other_location(Driver.drive) arena=<core_expr> env_frames=1
## lets x = {A}v in pure(x) (LETS-ANNOT at the symbol binder, located): 1 step(s)
   Step_tau2[Esseq Eannot] loc=exhibitA.c:1:17-61 arena=<core_expr> env_frames=1
## REMOVE-ANNOT (value arm, CTX): no location write: 1 step(s)
   Step_tau2[CTX, Eannot(value)] loc=other_location(Driver.drive) arena=<core_expr> env_frames=1
## create(Ivalignof(int), int) located: ACTION_EVAL: 1 step(s)
   Step_with_runstate2[RSK_eval eval operands of Create] (thread inside the monad; not printed)
## store located, non-library Action loc: 1 step(s)
   Step_action_request2[StoreRequest] at exhibitA.c:1:17-61
## store located at a LIBRARY Action loc but non-library node Aloc: 1 step(s)
   Step_action_request2[StoreRequest] at exhibitA.c:1:17-61
```
(Configurations: thread parked at `current_loc := other "Driver.drive"`,
`current_proc_opt := some mainSym`, `stack0 := Stack_empty`, memory
`prodMem₀`, file `prodFile vUnit`; `libLoc = region ⟨"libcore/std.core",3,1⟩ …`,
`srcLoc = region ⟨"exhibitA.c",1,17⟩ ⟨"exhibitA.c",1,61⟩ .noCursor`; in
"bound(bound(v))" the OUTER node carries `srcLoc` and the INNER `libLoc` — the
engine read the inner node's (library) location and left `current_loc`, as
`redexAnnots` predicts. The `<core_expr>` arena print is the generated
printer's opaque form.)

### A.2 Corpus-skeleton plants by term surgery (`.audit-scratch/Plants.lean`, no tree edit, exit 0)
```
text tokens: 56
baseline t1Main: PASSES (blind spot)
plant A constant 3->4          : PASSES (blind spot)
plant B Astd §6.5.6 -> §6.5.7  : RED (mismatch; first diff at 17)
plant C root Aloc dropped      : RED (mismatch; first diff at 0)
plant D root annot order swap  : PASSES (blind spot)
plant E symbol x -> y in stores: PASSES (blind spot)
plant G first `let strong` -> weak: RED (mismatch; first diff at 1)
plant H Aloc on a pure operand : ERROR (fail-closed): a pure expression carries a printed annotation (Astd/Aloc) — the skeleton instrument is blind inside pure expressions; extend it (E2/E3)
plant (script's) bound dropped : RED (mismatch; first diff at 7)
plant (script's) Astd stripped : RED (mismatch; first diff at 7)
missing corpus file            : read fails: no such file or directory (error code: 4294967294)
  file: ../docs/corpus-e0/nonexistent.annot.core
```
("PASSES" on the baseline means the transcription equals the text — the
expected green; "PASSES (blind spot)" on a plant means the wrong
transcription is not caught, exactly as the module header discloses.)

### A.3 Pin axiom sets (`.audit-scratch/PinAxioms.lean`, `Lean.collectAxioms`, exit 0)
All 25 E1 pins, plus `loc_update_lib`, `loc_update_none`, `engine_step_matchU`,
`frag_round_complete`, `loop_step_frag`, `loop_step_frag'`:
`[Classical.choice, Quot.sound, propext]` each (31 lines, identical).

### A.4 Snapshot
`cmp .audit-scratch/head-signatures.txt docs/2026-09-04_e1-signatures-post.txt` → identical (32832 lines).

## B. What I did NOT check

- Every one of the 583 changed statements individually (the split is by
  normaliser + keyword scan; 113 remain unclassified by my tools).
- The bodies of the pre-existing `Step` rules' engine equations beyond the
  E1-new ones and the generalised `annot_merge`/`ret`/`sseq_*`/`run`/`call`
  controls (I relied on `engine_step_matchU`'s kernel check for the rest).
- The E1 record's build-cost figures (§8) — not reproducible without a full
  cold rebuild, which the box-etiquette instruction discouraged mid-audit.
- The PCALL round's location push executably (the probe prints only the
  `Step_with_runstate2` head; the theorem `step_ctx_call_ws` inside
  `loop_step_frag'` is the check, kernel-verified).
- The `hbsz` premise of `Frag.case_value` (unchanged by E1; KOI B7).
- Whether the 64 pre-existing warnings are exactly KOI C5's 62 + 2
  (two re-flowed lines; not traced to their original commits).
- `deps/refinedc` or any RefinedC-side consequence; branch `refinedc/dev`.
