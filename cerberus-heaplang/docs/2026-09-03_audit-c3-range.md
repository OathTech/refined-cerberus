# CALLS C3 range audit (`6d54a89..ebd4076`) — 2026-09-03

[AGENT] Independent auditor record. Audited in the fixed detached copy
`worktrees/audit-c3-ebd4076` (HEAD `ebd4076`, detached; `.lake` and
`.cerberus-ws` primed, cerberus-lean pin `f95ef8d9c`). Read-only except
this file and an ephemeral scratch dir (`.audit-scratch/`, deleted at
the end; every quoted line below was copied from it verbatim before
deletion). Nothing committed, merged or pushed. Every Lean invocation
went through `scripts/capped` with `CERB_MEM_MAX=40G`. Brief:
`docs/AUDIT-BRIEF.md`. Inputs: the range diff (39 files,
+32877/−1235, of which the snapshot is 28852 lines), the worker record
`docs/2026-09-03_c3-notes.md`, the two snapshots
(`_c2-signatures-post.txt` as pre, `_c3-signatures-post.txt` as post),
the C2 range audit `docs/2026-09-03_c2-audit.md`, `docs/DECISIONS.md`,
and the PINNED SEMANTICS at `.cerberus-ws/lean_frontend/generated/`.

Method. (1) Every engine fact the record cites was re-measured on the
pin by string search (`Core_aux.lean:872` `lookup_env`; the RETURN,
PCALL and REMOVE-ANNOT arms of `Core_reduction.lean:484`). (2) The
Lean diff was read in full for Step, Wps, Wpt, Adequacy, TotalAdequacy,
Audit, API, the manifest generator and the smoke; the four re-threaded
exhibit families were read as diffs. (3) The FULL gate was run by the
auditor in the audit copy (twice; the first run's log landed in a
`/tmp` the sandbox would not read back, the second is quoted below).
(4) The snapshot was regenerated at HEAD and compared byte-for-byte;
the census was re-derived by script from the two committed files.
(5) `#print axioms` on 47 names; two `lake env lean` probes (the
empty-table clause entailment; `driveU` executed on the smoke program at
budgets 0–9). (6) Three plant tests, each with rebuild-after-revert.
(7) The 66 package linter warnings attributed by `git blame`.

Quotes are verbatim modulo whitespace runs (the generated file has
double spaces). Tallies marked DERIVED were computed by the auditor's
scripts from committed files.

## Verdict

**PASS — grade A−. Merge-ready for `6d54a89..ebd4076` on operator
sign-off, with two docs-only corrections (R-1, R-2) to land with the
merge; no proof changes required.** No High or Medium finding. The call
clause is the engine's PCALL round clause for clause and the collapse's
return is `Step.ret`/`Step.ret_annot` exactly; the one Löb is used only
under the later; `SameTail` is the right invariant and RETURN's env pop
is a theorem from it (Plant C breaks the proof at exactly that point);
the empty-table instance recovers every pre-C3 rule statement (208 of
the 234 changed statements are equal under the judgment-parameter
embedding — DERIVED; the other 26 are the six shape classes the record
lists, verified word-by-word); `procSpecs_intro` is Hoare's rule with
no circularity (the knot is the collapse's Löb, and the smoke's table is
discharged non-vacuously); the two "forced" claims (§2, §4 of the
record) are forced by the engine text as cited; the census numbers hold
exactly; all 32 new pins and every export checked are trio-exact; the
eight production statements are byte-identical in source and in
pretty-printed type; the `1 + m + k'` budget split is confirmed against
the engine loop by execution (`.done` at exactly 6 drive steps); all
three plants went loud and every revert came back green at 344 pins;
the DECISIONS entry, the gate tail and the LICENSE text match the tree.

Deductions from A: two shop-window imprecisions (a docstring says
"exactly" where the theorem says "entails under the update"; a record
sentence misfiles the production statements), one general law parked in
a smoke file, and the call clause's `q.2.1`/`q.2.2` projections with
their eta-hack in both collapses.

## Findings, ranked

No T- (trust) or High/Medium C- (correctness) findings.

### R-1 (Low — record/docstring): "exactly C2's `⌜False⌝` guard" overstates; the theorem is an entailment under the fancy update

Evidence. `CerberusHeapLang/Wps.lean:131–134`: "Every pre-C3 statement
is recovered at this table: the call clause at `emptyProcSpec` is
exactly C2's `⌜False⌝` guard." `docs/2026-09-03_c3-notes.md:125`: "At
`Θ := emptyProcSpec` the arm is `|={⊤}=> ∃ …, … ∗ ⌜False⌝ ∗ …` — C2's
guard." The C2 arm was the IProp `⌜False⌝`; the C3 arm at the empty
table is `|={⊤}=> ∃ params body vs, ⌜…⌝ ∗ ⌜…⌝ ∗ ⌜…⌝ ∗ ⌜False⌝ ∗ ▷ …`,
a different IProp. What IS proved: for `wpt`, `wpt_empty_call_false`
(`Wpt.lean:273`) — `wpt M p Ls emptyProcSpecT k Ψ e ρ ⊢ |={⊤}=> ⌜False⌝`;
for `wps` there is no twin, and the auditor's probe elaborated it
(`lake env lean`, exit 0):

```lean
example … : wps M p Ls emptyProcSpec Ψ (callRedex ra f []) ρ ⊢ iprop(|={⊤}=> ⌜False⌝) := by
  rw [wps_unfold.to_eq]
  simp only [wps.pre, show toVal (callRedex ra f []) = none from rfl,
    show jumpRedex? (callRedex ra f []) = none from rfl, callRedex?_callRedex, emptyProcSpec_fst]
  iintro H
  imod H with ⟨%params, %body, %vs, %h1, %h2, %h3, %hF, -⟩
  exact hF.elim
```

Every consumer eliminates the clause under a fupd or a WP
(`wpt_drive_aux`'s call case goes through `wpt_empty_call_false` then
`imod`), so all recovered statements are theorems (measured: 208
normalizer-equal statements, the eight production statements identical,
every checked cone trio-exact). The gap is wording only.
Premise verified by measurement: yes (probe above; `wpt_empty_call_false`
read).
Fix required: in `Wps.lean:134` and the record §1 replace "is exactly
C2's `⌜False⌝` guard" by "entails `|={⊤}=> ⌜False⌝` — C2's guard under
the update"; optionally add `wps_empty_call_false` as the `wps` twin of
`wpt_empty_call_false` (five lines, the probe above).

### R-2 (Low — record): the eight production statements are in the UNCHANGED set, not "in the normalizer-verified set"

Evidence. `docs/2026-09-03_c3-notes.md:503–506`: "PRODUCTION STATEMENTS
textually UNCHANGED, all eight: … (in the normalizer-verified set; their
judgments live inside the proofs at the empty table)." The
"normalizer-verified set" is the record's 212 CHANGED-but-shape-only
entries. Measured from the two committed snapshots (DERIVED, script):
all eight names are present in both files with byte-identical entries
and are NOT among the 234 CHANGED names —

```
exhibitA_prod … IDENTICAL not-in-changed
prod_run_eqJ … IDENTICAL not-in-changed
counter_loop_certified_production … IDENTICAL not-in-changed
fib_certified_production … IDENTICAL not-in-changed
list_reverse_certified_production … IDENTICAL not-in-changed
dispose_list_certified_production … IDENTICAL not-in-changed
region_loop_certified_production … IDENTICAL not-in-changed
malloc_list_certified_production … IDENTICAL not-in-changed
```

and their SOURCE text (`git show 6d54a89:…` vs `ebd4076:…`, statement
through `:= by`) is identical: 10/15/19/15/19/21/18/22 lines
respectively. The claim "textually unchanged" is TRUE; the
parenthetical misfiles it. Premise verified by measurement: yes.
Fix required: replace "(in the normalizer-verified set; …)" by "(in the
UNCHANGED set — byte-identical snapshot entries and source; …)".

### R-3 (Note — record, confirmed): the `1 + m + k'` split and the "forced" claims hold by measurement

Not a defect; recorded so the register can cite measurements rather than
prose.

- BUDGET SPLIT (record §1, §9.4; `Wpt.lean:148–195`). Executed
  `driveU` on the smoke program (`csCtx default (BTy_object OTy_integer)
  …`, `csMainBody default`, env `[fmapEmpty]`, control `⟨[], some csMain,
  default⟩`, memory `prodMem₀`, `aids := fun _ => 0`), budgets 0–9,
  verbatim `#eval` output:
  ```
  [(0, "more"), (1, "more"), (2, "more"), (3, "more"), (4, "more"), (5, "more"), (6, "done(v = csInt 4)"),
    (7, "done(v = csInt 4)"), (8, "done(v = csInt 4)"), (9, "done(v = csInt 4)")]
  ```
  Six drive steps: PCALL, SAVE-EVAL, SAVE, PURE, RETURN, PROGRAM-DONE.
  `csMain_wpt` (`CallSmoke.lean:469`) is at budget `6 = 1 + 4 + 1` with
  `m := 4` (three body steps + `deliveryCost 1` for the RETURN) and
  `k' := 1` (the delivered value's `deliveryCost` at the top). The split
  neither double-counts nor under-counts the return on this instance;
  the brief's `1 + m + 1 + k'` would have over-budgeted by one. (The
  general theorem is the C4 driver-lane simulation, not yet stated —
  correctly flagged on every surface, see Q6.)
- §2 FORCED (index = procedure, not control). Measured on the pin,
  `Core_reduction.lean:484`, the RETURN arm writes exactly
  `current_proc_opt`, `env`, `stack0`, `arena`:
  ```
  reduction: RETURN -/ Step_tau2 "end of procedure" tsk ( match th_st.env with | [] => (failwithI "end of proc, found an empty Core_run env" : thread_state) | _ :: env' => { { { { th_st with current_proc_opt := parent_proc_opt } with env := env' } with stack0 := sk' } with arena := apply_ctx caller_ctx (Expr e_annots (Epure (mk_value_pe cval))) } ))
  ```
  and PCALL writes `exec_loc := push_exec_loc psym th_st.current_loc
  th_st.exec_loc`. So `exec_loc` is not restored: a control-indexed
  judgment could not re-enter the caller's continuation. Forced.
- §4 FORCED (`∀ ρ` over the caller tail). `Core_aux.lean:872`, verbatim
  modulo whitespace: `def lookup_env … := fun x => match x with | [] =>
  none | env1 :: xs => (match (fmapLookupBy (@mapKeyCompare (b) _) sym1
  env1) with | none => lookup_env sym1 xs | some ret => some ret)` —
  all frames, top-down; `update_env` (`:868`) writes the head frame only.
  Forced, and free in the smoke (`csF_body_wps` at arbitrary `ρ`).

### H-1 (Hygiene): the 66 linter warnings are ALL pre-existing; none is introduced by this range

Evidence. The auditor's gate log carries 590 `warning:` lines; 524 are
in the semantics dependency (`generated/*`, `LemLib/*`) and 66 in
`CerberusHeapLang/*` (DERIVED tally by file: Potential 50,
TotalAdequacy 4, Round 3, Rules 2, Heap 2, EnvLaws 2, ProdLoopExhibit 1,
StructExhibit 1, TreeRotExhibit 1; by kind: "This simp argument is
unused" 61, unused-variable 5). `git blame -L` on each of the 66 lines
at HEAD: the blamed commits are `a030cc5` (20), `752eb18` (17),
`639ee1b` (12), `d0ae541` (4), and nine others with ≤2 each — dated
2026-08-31 09:30 to 2026-09-03 08:26, all BEFORE `6d54a89`; zero lines
blame to `c75d416`, `a5f7078`, `f2d6304`, `93ca8b7` or `ebd4076`. The
DECISIONS entry's "C3-attribution not established" is now established:
not C3. Premise verified by measurement: yes (blame).
Fix (optional, hygiene pass): drop the unused simp arguments, Potential
first; not a merge condition.

### H-2 (Hygiene/design): a general two-entry lookup law is parked in the smoke

Evidence. `Examples/CallSmoke.lean:109` `csAdd_lookup_two {β} (cmp') (k2
k1 l) (v2 v1 : β) : fmapLookupBy cmp' l (csAdd k2 v2 (csAdd k1 v1
fmapEmpty)) = if symOrd l k2 = .eq then some v2 else if symOrd l k1 =
.eq then some v1 else none` is value-generic and lookup-comparator-
generic (`csAdd` = `fmapAddBy … symCmpK`). `ARCHITECTURE.md:421` lists
"Two `save` labels in one program — OPEN … needs a two-entry label-map
lookup law (`lookupLabel` at `fmapAddBy … (fmapAddBy … fmapEmpty)`) and
EnvLaws has only the singleton `fmapLookupBy_addBy_empty`"
(`EnvLaws.lean:64`). `lookupLabel` (`Step.lean:304`) is `fmapLookupBy
ordCompare` on a `Fmap sym (params × expr)` — the same shape. The smoke
proved the missing law (for adds at `symCmpK`) and filed it as a local
helper. Premise verified: yes (both statements read); NOT verified: that
the exhibits' label maps are built with `fmapAddBy` at `symCmpK` (if
another comparator is used the law needs the `cmpL` generalization
`fmapLookupBy_addBy_empty` already has).
Fix (next EnvLaws slice, not a merge condition): move the law to
EnvLaws as `fmapLookupBy_addBy_addBy_empty` (generalizing the add
comparator as the singleton does), consume it from the smoke, and
re-examine the ARCHITECTURE §7 open item — it may be closable.

### H-3 (Hygiene — clarity): `q.2.1`/`q.2.2` in the call clause, and the eta-hack `hq`

Evidence. `Wps.lean:230–239` and `Wpt.lean:171–180` state the clause over
`q : context × sym × List …` with `q.1`, `q.2.1`, `q.2.2`; both collapses
then need `have hq : callRedex? e = some (q.1, q.2.1, q.2.2) := hcr`
(`Wps.lean` call case; `Wpt.lean` call case) to feed `Step.call`/
`Step.call_inv`, whose statements are at `(ctx, f, pes)`. The
pretty-printed statement `wpt_call_eq` shows `q.snd.fst`/`q.snd.snd`.
Fix (optional): match `| some (ctx, f, pes) =>` in `wps.pre`/`wpt.pre`
(the `simp only [wps.pre, …, hcr]` rewrites still fire at a concrete
`hcr`), delete the two `hq`s.

### H-4 (Nit — docs): three wording items

- `docs/CAPABILITY_MANIFEST.md:17,19` (generated by
  `scripts/capability_manifest.lean:236,238`): "consumed by no exhibit
  is a red row" / "Consumed by (exhibit modules)" while the client set
  now includes `Examples.CallSmoke` (correctly described in the
  generator's header comment and README). Say "client modules".
- The generator hard-codes the one module name
  `CerberusHeapLang.Examples.CallSmoke`
  (`capability_manifest.lean:~155`); a `Examples.*Smoke` pattern would
  not need touching at C4.
- `README.md:60` (root): "iris-lean: see its repository" — the pinned
  `cerberus-heaplang/.lake/packages/iris/LICENSE` is byte-identical to
  the repo's `LICENSE` (measured with `cmp`), i.e. Apache 2.0; batteries
  and Qq likewise identical; LemLib differs (its own license, as stated).

## The questions

### Q1. The judgments and the mirror

`wps.pre` (`Wps.lean:216–248`): four clauses, the call arm at `callRedex?
e = some q` demanding `lookupProc M.file M.extern q.2.1 = some (params,
body)`, `params.length = vs.length`, `evalPexprs … ρ q.2.2 = some vs`,
`(Θ q.2.1 vs).1`, and `▷ ∀ ret, (Θ q.2.1 vs).2 ret -∗ F Ψ (apply_ctx q.1
(pure ret)) ρ`. `Step.call` (`Step.lean:2047`) has premises `hc : callRedex?
e = some (ctx, f, pes)`, `hvs`, `hf`, `hlen` — the same four facts — and
the successor `(body, procEnv params vs :: ρ, ⟨(ctl.proc, ctx) :: ctl.κ,
some f, push_exec_loc f M.currentLoc ctl.execLoc⟩, σ)`; `Step.ret`
(`:2079`) at `(pure v, ev0 :: evs, ⟨(p, ctx) :: κ, q, ℓ⟩)` yields
`(apply_ctx ctx (pure v), evs, ⟨κ, p, ℓ⟩)` — the continuation the clause
is stated at, at env `ρ` = the popped tail, `ℓ` riding; `Step.ret_annot`
(`:2096`) strips one annotation layer at a cons stack, matching the
REMOVE-ANNOT arm measured on the pin (`Step_tau2 "CTX, Eannot(value)"
TSK_Misc { th_st with arena := expr' }`, which precedes the general arm
and does not read `stack0`). The step clause is quantified over `(κ, ℓ)`
and its `Step.ctl_eq hs hcr htv` discharge needs exactly `callRedex? e =
none` and `toVal e = none`, which the clause order provides. Mutual
exclusion `jumpRedex?_none_of_callRedex?_some` is used in `wps_call`.
The contractive instance gains one arm with the `▷` at the continuation
(`OFE.Contractive.distLater_dist`), read.

Empty table: `emptyProcSpec f vs = (⌜False⌝, fun _ => ⌜True⌝)` — R-1
has the precise statement.

`wpt` (`Wpt.lean:197–201`): `| k => wpt.pre M p Ls Θ k (fun k' _ => wpt M p
Ls Θ k')`, `termination_by k => k`, the continuation family `F : ∀ k' <
k, …` — genuine well-founded recursion; `wpt_unfold` by `rw [wpt]`. The
call clause's `hb : 1 + m + k' ≤ k` feeds `F k' (by omega)`; the step
clause is at `k' + 1 → k'`. The four structural lemmas and
`wpt_frame_labels` are `Nat.strongRecOn` inductions (read; each call
case applies the IH at `k₁ < k` by `omega`). The budget split: R-3.

### Q2. `wps_sound_cps`

`Wps.lean:3411–3606`. `iloeb as IH generalizing %p %Ls %Ψ %κ %ℓ %e %ρ %Φ`
with `procSpecs` (`#HP`) fixed and `blockSpecs` (`#HB`) introduced after
the Löb. IH USES: jump case — after `inext` (line `inext` precedes
`iintro %r …`); call case — the first IH (callee body) and both IHs
inside `K'` are after the case's `inext`; step case — after `inext`. The
value case does not use the IH. No use of `IH` precedes a `▷`
elimination; the `wp_lift_step` later pays each. `SameTail ρ ρ'`
(`Step.lean:2502`): `∀ ev0 evs, ρ = ev0 :: evs → ∃ ev0', ρ' = ev0' :: evs`;
`Step.sameTail` is `env_cons' rfl` (control-preserving steps keep the
tail — `update_env` writes the head frame only), `.trans` composes
across jump/step, and in the call case `hst.cons_inv` at `procEnv params
vs :: ρ` yields `ρ' = ev0' :: ρ`, so `wp_ret` lands at `ρ` verbatim and
the clause's continuation `Hcont v` applies at `ρ`. That this is a
theorem and not a coincidence is Plant C: replacing `⌜SameTail ρ ρ'⌝` by
`⌜True⌝` in the statement fails at `Wps.lean:3540:36: Invalid field
cons_inv` (and at the `SameTail.refl`/`.trans` sites) — the pop depends
on the invariant. `wps_sound` = the CPS theorem at `κ := []` with `K :=
wp_value` (`toValRt` at `κ = []`); `wps_sound_empty` = `wps_sound` +
`procSpecs_empty`. Against the pre snapshot: the C2 `wps_sound` and the
C3 `wps_sound_empty` differ by exactly `{ctl : Ctl}` moved after `Ψ`,
`ctl → ctl.proc` at the two judgment indices, and `emptyProcSpec`
appended (word-diff, DERIVED); the C3 `wps_sound` additionally has the
premise `procSpecs M Θ ∗` and the binder `{Θ}`.

`wpt_sound_cps` (`Wpt.lean:3158–3365`): strong induction on `k`; the
jump case lands at `m` with `1 + m ≤ k`; the call case applies the IH at
`m` (callee) and at `k'` (continuation), both `by omega` from `hb`; the
return is `twp_ret`/`twp_ret_annot` (TWP twins of `wp_ret`/`wp_ret_annot`,
read). Deleting `hb` or the jump decrease would leave the `omega`s
without a premise — the F-02 criterion holds for calls.

### Q3. `procSpecs` / `procSpecs_intro` / the smoke's table

`procSpecs M Θ` (`Wps.lean:3240`) is `□ ∀ f params body vs ρ, ⌜lookupProc …
= some (params, body)⌝ -∗ ⌜len⌝ -∗ ∃ Ls, blockSpecs M (some f) Ls Θ Ψ_f ∗
((Θ f vs).1 -∗ wps M (some f) Ls Θ Ψ_f body (procEnv params vs :: ρ))`.
It is an assertion ABOUT the table `Θ` (a value of type `ProcSpec GF`),
not a definition of it — no definitional circularity. Its introduction
(`:3258`) takes meta-level entailments per body (`hW : (Θ f vs).1 ⊢ wps
… Θ …`), so a body proof may assume the table for every call inside,
itself included; nothing in `procSpecs_intro` discharges that
assumption — the collapse does, by the Löb IH applied to the callee
body at the pushed control (the call case's first `iapply IH`). That is
Hoare's rule for recursive procedures in its standard shape and it is
sound for partial correctness by exactly that Löb. The total twin
`procSpecsT` indexes the entry by the callee budget `m` and the
collapse's strong induction discharges it at `m < k` — total
correctness needs no Löb, and the smoke's `csSpecT` puts `4 ≤ m` in the
PRECONDITION, so an unbudgetable body cannot be spec'd.

Non-vacuity of `csCtx_procSpecs` (`CallSmoke.lean:300`): the file
`csFile` binds `main ↦ Proc … [] (f(3))` and `f ↦ Proc … [(x, bty)]
(save …)`; `csFile_lookup_inv` (read; a two-case lookup proof over the
two-entry map, `csAdd_lookup_two`) sends `procSpecs_intro`'s `hW` to two
cases — `main` (arity 0: the precondition `∃ x, vs = [csInt x] ∧ 0 ≤ x`
is refuted by `hlen : [].length = vs.length` after `subst`) and `f`
(`csF_body_wps`, a real `wps_save`/`wps_pure` proof at every `ρ`). The
precondition is satisfiable (`csMain_wps` supplies `⟨3, rfl, by decide⟩`)
and the postcondition is used (`csInt_inj` pins `x = 3`). Not vacuous.
`csCtx_fragProcs` (`:225`) is the first non-`rfl` `FragProcs`: both
bodies through `Frag.save`/`Frag.pure_sym` and `Frag.call`, both label
fibers empty by `csCtx_lookupLabel`. `call_smoke_driveU` (`:377`) is
`engine_adequacyU` at it (PROVISIONAL, `driveU`), trio-exact.

### Q4. The forced claims

Both forced; R-3 has the measurements.

### Q5. Census

Regenerated at HEAD: `lake env lean scripts/signature_snapshot.lean`
(14 s) → 28852 lines, `cmp` against
`docs/2026-09-03_c3-signatures-post.txt`: byte-identical. Pre-snapshot
validity for `6d54a89`: the pre file was taken at the C2 head `8d28c21`
(and re-measured by the worker at `793b58c`); `git diff --stat 8d28c21
6d54a89 -- cerberus-heaplang/CerberusHeapLang …` touches only
`API.lean` (a docs table), `Audit.lean` (the pin list's contents), a
`Step.lean` docstring and `lakefile.toml` comments — no statement can
have changed; `b82e472..6d54a89` touches `lakefile.toml` comments only.
Accepted.

DERIVED from the two committed files (script): pre 2816 entries, post
2897; ADDED 81, REMOVED 0, CHANGED 234 — the record's numbers exactly;
the 81 names are the record's list (tables, `SameTail` family,
`Step.env_depth`/`ret_inv`/`ret_annot_inv`, the four `apply_ctx_*`
equations, the procedure rule, the call rule, the four return devices,
the five collapse faces, `wpt_unfold`/`wpt_empty_call_false`, and 37
`cs*`/`procEnv_single`/`call_smoke_driveU` smoke declarations). Of the
234, the auditor's normalizer (binder `{ctl : Ctl}` → `{p : Option sym}`,
`Ctl →` → `Option sym →`, `procCtl X` → `some X`, `spikeCtl` → `none`,
`M.labelsAt ctl.proc` → `M.labelsAt p`, `ctl` → `p`; on the new side
erase the `Θ` binder and the appended `Θ`/`emptyProcSpec(T)` argument)
finds 208 equal; the worker's found 212 — the difference is that the
auditor's rules also absorb the four DEF types `wps`, `wpt`,
`blockSpecs`, `blockSpecsT` (a `Ctl →` slot and an inserted `ProcSpec GF
→` slot) which the worker hand-inspected, and do not absorb eight
statements whose binder is named `pr` (ReadinessSmoke ×5) or spelled
explicitly (`caseProg_wps`, `wseqProg_wps`, `wps.pre.contractive`) — all
eight are shape-only by word-diff. The remaining 22 word-diffs are
exactly the record's six classes: (i) `wps.pre`, `wpt.pre`,
`wpt.eq_def` (the well-founded form), `wpt_step_eq` and `wpt_call_eq`
(the `(κ, ℓ)` quantification / the clause replacing `iprop(False)`);
(iii) `wps_of_atomic`, `wpt_of_atomic`, `wpt_det_step` (premises at `{
κ := κ, proc := p, execLoc := ℓ }`); (iv) `wps_sound`, `wps_sound_frame`,
`wpt_sound` (`procSpecs(T) M Θ ∗` inserted, `ctl → ctl.proc`); (v) the
six driver lanes (`ctl → ctl.proc`, `emptyProcSpecT` inserted, nothing
else); (vi) `wps_arr_elem_load` (primed binders). Production
statements: R-2.

### Q6. Pins, trust, coverage claims

`Audit.lean:465–495` adds exactly the 32 names the record lists; the
auditor's gate reports `CerberusHeapLang export pins: 344 trio-exact`
(312 + 32). `#print axioms` on the 32 plus `wps_sound`, `wpt_sound`,
`drive_classifyU_aux`, `engine_adequacyU`, `wpt_engine_boundU`,
`wpt_driver_done` and the eight production statements — 47 names — all
`[propext, Classical.choice, Quot.sound]`. Range-added Lean lines
contain no `sorry`, `native_decide`, `bv_decide`, `ofReduce*`,
`maxHeartbeats` or `maxRecDepth` (grep); the smoke's four `decide
+kernel` are kernel-checked and the package idiom (15 modules use it).

Manifest: `Frag.call → wps_call_root`/`wps_call`, consumed by
`Examples.CallSmoke`; `declaredNoRule` now empty, the mechanism kept;
`docs/CAPABILITY_MANIFEST.md`: 23 constructors, 27 rule rows, 0 red, 17
client modules; regenerated with no drift by the auditor's gate. Import
direction speedbump green; `CallSmoke.lean` imports `CerberusHeapLang.API`
only; `Audit.lean` imports it last-but-one. Fail-closedness at the
boundary: `Frag.call` (`Soundness.lean:166`) admits `callRedex ra f pes`
with `∀ pe ∈ pes, PePure pe` and depth bounds — `Eproc _ (Sym f) _` only;
`Frag` has no constructor mentioning `Impl` or `Eccall` (grep: none), so
a program with an implementation-constant or function-pointer call is
not `Frag` and no adequacy export applies; inside the judgment such a
redex has `callRedex? e = none`, falls to the step clause, and has no
mirror step (`callRedex?_proc_impl = none`) — unprovable. Fail-closed.

Claimed vs covered. The total DRIVER lane through calls is NOT covered
and is said so on every surface: README "Deliberately not here" and the
limitations row ("no total export goes through a call yet"),
ARCHITECTURE §3 ("metatheorems no export consumes") and §4 ("stated at
the EMPTY table … C4 extends it"), the record §9.6, the DECISIONS entry
("Worker-flagged, carried to C4"). The PRODUCTION lane through a call
likewise (README, ARCH §4, record §7). What IS covered through a call:
the partial `driveU` lane (`call_smoke_driveU`, PROVISIONAL as every
`driveU` export) and the two collapses into WP/TWP. No overclaim found.

### Q7. Plant tests — see the log below

### Q8. Records

DECISIONS `:1473–1510` "C3 LANDED": commit `93ca8b7` ✓ (`git log`), "rebased
onto main c75d416" ✓ (parent chain `c75d416 → a5f7078 → f2d6304 → 93ca8b7
→ ebd4076`), "Pins 312 → 344" ✓, the record path and snapshot path exist
✓, the quoted gate tail is line-for-line the auditor's own (below) ✓.
Chronology of the tail: entries dated by their subjects — "MERGED AT
b82e472" (merge 17:54; entry written at the C3 dispatch `793b58c`),
"SHAREABLE MAIN" (trim `24c2410` 18:47), "LICENSE" (`c75d416` 19:06),
"EVERY MERGE IS PRECEDED BY A CHECK-IN" (after the license merge), "C3
LANDED" (`93ca8b7` 20:07) — chronological ✓ (the `ebd4076` reorder did
what its message says). The worker record §11's gate quote (lines 1–3
and 3101–3112 of a 3112-line log) is consistent with the auditor's
3114-line log (two added `date` lines). The C2 audit's M-1 (four
[AGENT] deviations, the failed pre-registered criterion) is disposed in
the "MERGED AT b82e472" entry, item (1), by [USER] ✓.

LICENSE: `cmp` byte-identical to `.lake/packages/batteries/LICENSE`,
`…/iris/LICENSE`, `…/Qq/LICENSE`; differs from `…/LemLib/LICENSE`
(expected). NOTICE: "Copyright 2026 Oath Technologies", Apache 2.0
boilerplate ✓. README license section consistent (H-4 nit).

### Q9. Hygiene — H-1

### Q10. Grumpy read

The logic is in good shape: the two judgments are stated once each with
a genuine four-clause shape; the call clause is near-definitionally the
call rule (as the jump clause is the jump rule); the procedure rule has
no Löb and the single Löb sits where RefinedC puts it (the CPS collapse,
`stmt_wp_def` shape); `SameTail` is the smallest invariant that makes
the return a theorem; `Step.env_depth` retires two inline arithmetic
blocks in `drive_classifyU_aux`. The record is thorough and every
"forced" claim cites an engine location that checks out. Weak points,
all minor: R-1's "exactly"; the `q.2.1` projections (H-3); the
`wp_ret`/`wp_ret_annot`/`twp_ret`/`twp_ret_annot` quartet is four copies
of one 30-line proof (accepted — two strata, two shapes); a general law
in a smoke (H-2); `∀ ρ` is justified but the record's "costs nothing" is
true only for bodies whose reads are head-frame hits — which is every
body the fragment can express (`Frag` has no free-symbol reads outside
`PePure` operands resolved in the env), so fine. Recursion is admitted
by the rule but exhibited by nothing until C4 — stated as such. Dead
code: none found (the `apply_ctx_*` equations are consumed by the
sequencing rules' call cases; `SameTail.trans/cons_inv`, `wpt_unfold`,
`emptyProcSpec(T)_fst` all consumed).

## Plant-test log (verbatim)

Runner: `CERB_MEM_MAX=40G ./scripts/test_unit.sh --fast` (gates 1–2 =
the trust base) after each edit, then `git checkout -- Wps.lean` and the
same runner again. Times are wall-clock `date +%T` at start/end. The
baseline for comparison (FULL gate, auditor's run, `20:16:40 →
20:16:48`, all modules replayed from the primed `.lake` whose Lake
traces match the committed sources):

```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:500:0: CerberusHeapLang export pins: 344 trio-exact
info: CerberusHeapLang/Audit.lean:500:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (3301 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:500:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (5053 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (455 jobs).
ok: cerberus-heaplang build green
== speedbump: capability manifest (regenerate; red on a red row or drift) ==
ok: capability manifest regenerated, no drift
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — no core module imports an exhibit/example/production module
ALL GATES GREEN
GATE-EXIT=0
```

(Lines 5 and 3108 of the log are the `capped` env banner
`cerberus-lean-proj env: switch=…/_opam, git redirects active`; no
"uncapped" warning appeared.)

**Plant A — `sorry` in an internal detail of the call-rule cone.**
`Wps.lean:138`: `(emptyProcSpec (GF := GF) f vs).1 = iprop(⌜False⌝) :=
rfl` → `:= sorry` (consumed by `procSpecs_empty` → `wps_sound_empty` →
every exhibit's collapse). `20:24:23 → 20:24:57`; 25 modules rebuilt
(Wps, Wpt, TotalAdequacy, API, ProdLoop, ProdEntry, all 16 exhibit/
example modules incl. CallSmoke) then Audit:

```
warning: CerberusHeapLang/Wps.lean:138:16: declaration uses `sorry`
error: CerberusHeapLang/Audit.lean:500:0: CerberusHeapLang export pin FAILED: CerberusHeapLang.exhibitA_engine depends on axioms [Classical.choice,
 Quot.sound,
 propext,
 sorryAx], expected EXACTLY [Classical.choice, Quot.sound, propext]
error: Lean exited with code 1
error: build failed
FAIL: cerberus-heaplang build red
GATE FAILURE
GATE-EXIT=1
```

Revert + rebuild `20:24:57 → 20:25:31` (26 modules rebuilt):
```
info: CerberusHeapLang/Audit.lean:500:0: CerberusHeapLang export pins: 344 trio-exact
ok: cerberus-heaplang build green
FAST-GATE GREEN (gates 1-2 only — not a claim-point result; say fast-gate in the commit)
GATE-EXIT=0
```

**Plant B — weakened call clause.** `wps.pre`: the line `(Θ q.2.1 vs).1
∗` deleted (the precondition no longer demanded). `20:25:31 → 20:25:34`:

```
error: CerberusHeapLang/Wps.lean:269:28: typeclass instance problem is stuck
  OFE ?m.242
error: CerberusHeapLang/Wps.lean:442:2: isplit: iprop(▷
error: CerberusHeapLang/Wps.lean:494:20: icases: cannot destruct iprop(▷
error: CerberusHeapLang/Wps.lean:552:20: icases: cannot destruct iprop(▷
error: CerberusHeapLang/Wps.lean:615:20: icases: cannot destruct iprop(▷
error: CerberusHeapLang/Wps.lean:716:20: icases: cannot destruct iprop(▷
error: CerberusHeapLang/Wps.lean:822:20: icases: cannot destruct iprop(▷
error: CerberusHeapLang/Wps.lean:1072:22: icases: cannot destruct iprop(▷
…
error: build failed
FAIL: cerberus-heaplang build red
GATE FAILURE
GATE-EXIT=1
```

(`:269` the contractive instance's arm count; `:442` `wps_call`'s
`isplitl [Hpre]`; the `icases` failures are the ten Löb lemmas' call
cases; `wps_sound_cps`'s call case would fail at `Hbody $$ Hpre` — not
reached, the file aborts earlier.) Revert + rebuild `20:25:34 →
20:25:38`: `344 trio-exact`, `FAST-GATE GREEN`, `GATE-EXIT=0`.

**Plant C — broken `SameTail` premise.** `wps_sound_cps` statement:
`⌜SameTail ρ ρ'⌝ -∗ Ψ w ρ' -∗` → `⌜True⌝ -∗ Ψ w ρ' -∗`. `20:25:38 →
20:25:40`:

```
error: CerberusHeapLang/Wps.lean:3430:28: Type mismatch
  SameTail.refl ρ
has type
  SameTail ρ ρ
but is expected to have type
  True
error: CerberusHeapLang/Wps.lean:3482:44: Application type mismatch: The argument
error: CerberusHeapLang/Wps.lean:3540:36: Invalid field `cons_inv`: The environment does not contain `True.cons_inv`, so it is not possible to project the field `cons_inv` from an expression
error: CerberusHeapLang/Wps.lean:3540:17: Tactic `rcases` failed: `x✝ : ?m.2966` is not an inductive datatype
error: CerberusHeapLang/Wps.lean:3595:44: Application type mismatch: The argument
error: Lean exited with code 1
error: build failed
FAIL: cerberus-heaplang build red
GATE FAILURE
GATE-EXIT=1
```

(`:3540` is `obtain ⟨ev0', rfl⟩ := hst.cons_inv` in the call case's
`K'` — the RETURN's env pop is exactly what the invariant buys.) Revert
+ rebuild `20:25:41 → 20:25:44`: `344 trio-exact`, `FAST-GATE GREEN`,
`GATE-EXIT=0`. `git status --short` after the chain: only the untracked
`.audit-scratch/` (deleted after this report was written).

## Not checked / limits

- The pre snapshot was not regenerated at `6d54a89` (no build of that
  revision in the audit copy); accepted on the source-diff argument in
  Q5.
- `iloeb`'s implementation in the pinned iris-lean was not read; the
  audit relies on the proof's structure (every `IH` use after the case's
  `inext`) and on the kernel accepting the term.
- The `∀ ρ` claim "costs nothing" was checked on the smoke only; a body
  reading a caller-frame symbol would need the tail in its spec — not a
  soundness matter.
- H-2's comparator question (whether the exhibits' label maps are built
  at `symCmpK`) was not measured.
- The FULL-gate build cost claimed in the record (≈ 3–4 min cascade)
  was not reproduced; on this box the cascade from `Wps` took 34 s.
- The `driveU` execution (R-3) is one instance; the general accounting
  theorem is C4's, as every surface says.
- Reachability of the engine's `Stack_cons` panic and the residual
  `OpenRound` arms are outside this range (C1/C2 audits).
