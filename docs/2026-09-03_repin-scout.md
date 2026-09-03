# 2026-09-03 — RE-PIN SCOUT: dry run of cerberus-heaplang onto the cerberus-lean FUEL-arc head

Scout record (worker, branch `repin-scout`, worktree
`worktrees/repin-scout`). Scope: report only — no fixes, no proof edits,
no commits anywhere but this scratch branch. Provenance: the operator's
scout brief (2026-09-03); [USER 2026-09-02] genuine-driver ruling and the
fuel request (`docs/DECISIONS.md`;
`docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md`); our
consumer review R1–R3
(`docs/2026-09-02_review-of-cerberus-lean-fuel-arc-design.md`). Quoted
outputs are verbatim; tallies marked DERIVED are grep/diff-derived;
section 3(c) and section 4 are ESTIMATES.

Old pin: `ddcfc919972a31bc43a0454e6b2e76a19e6c4594`. New pin (this dry run):
`f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf` = cerberus-lean mainline
`mdd/cerberus-lean` HEAD at scout time (`git rev-parse HEAD` in the primary
checkout; 35 commits in `ddcfc91..f95ef8d9c`, DERIVED via `git log
--oneline | wc -l`: mem-scale P0–close-out, the freshness hotfix, the
RelSem prune, release-hygiene G1–G9, the fuel arc design R0–R3, commits 1
and 2, close-outs 1 and 2).

The authoritative per-declaration account on their side is
`cerberus-lean/lean_frontend/docs/2026-09-03_fuel-arc-change-manifest.md`
(the "change manifest" below). This record VERIFIES its claims against the
tree at `f95ef8d9c` rather than re-deriving them; discrepancies are listed
in §1.5.

## 1. What landed vs what we asked (R1, R2, R3)

### 1.1 R1 — a fuel-parametric `drive`: DELIVERED (hand-written mirror, kernel-pinned)

`lean_frontend/CerbND.lean:450` (change manifest cites `:446`; see §1.5):

```lean
def drive_lemFuel (fuel : Nat) (_lemReader_tagDefs : Fmap (sym) ((CerbLocation.Loc ×tag_definition)))   (with_concurrency : Bool) (file1 : generic_file (Unit) (core_run_annotation))  (arg_strs : List  String)  : ndM (driver_result) (step_kind) (driver_error) (mem_constraint (CerbMem.IntegerValue)) (driver_state) :=  nd_bind
  ... -- the generated `drive` body verbatim, ONE substitution:
  ... (fun ( _ : Unit) => ( driver2_lemFuel fuel _lemReader_tagDefs)  with_concurrency)) ...
```

and the sync guarantee, `CerbND.lean:467`:

```lean
theorem drive_wrapper_defeq : drive = drive_lemFuel CerbFuel.driverFuel := rfl
```

Delivered DIFFERENTLY from the letter of R1 in two respects, both already
accepted by us: (a) it is not a lem-emitted `drive_lemFuel` but a
hand-written mirror in `CerbND` (design note §1.6 route (ii); route (i)
fails because the L1 fuel mechanism never threads fuel into a callee
reached through its wrapper; route (iii), a lem-backend cross-block fuel
plan, is registered as a next-lem-arc candidate); (b) fuel is threaded
into the MAIN `driver2` call only — the globals phase inside
`driver_globals` runs at the fixed `driverFuel` (our review §7 accepted
exactly this). There is NO `drive_lemFuel_zero` lemma (by design: setup
runs first at fixed budgets; the base case is discharged on the concrete
program by evaluating the fuel-independent setup then
`driver2_lemFuel_zero` — exactly our `drive_after_setup` shape,
ProdEntry.lean:325). Drift in the generated `drive` shows as
`(deterministic) timeout at whnf` in `drive_wrapper_defeq` ON THEIR SIDE
(the remedy is to re-mirror, never a heartbeat bump — CerbND.lean
DriveMirror comment).

Grep facts at `f95ef8d9c` (DERIVED): `drive_lemFuel` — defined once
(CerbND.lean:450), used by `drive_wrapper_defeq` and the exemplar; no
`drive_at` exists; the generated `Driver.lean` `drive` is unchanged in
shape (non-recursive `def`, calls the `driver2` wrapper).

### 1.2 R2 — `_zero` lemmas and wrapper `rfl`s in an importable seam, pinned by a gate on their side: DELIVERED

All in `namespace CerbND`, `lean_frontend/CerbND.lean`, section
`FuelContract` (:294–:415) — importable via `import CerbND` (we already
import it). The kill value and the budget name:

```lean
def fuelExhaustedKill {err : Type} : kill_reason err :=
  Error0 CerbFuel.fuelExhaustedLoc CerbFuel.fuelExhaustedMsg          -- CerbND.lean:80
def ndDefaultFuel : Nat := CerbFuel.driverFuel                          -- CerbND.lean:85
export CerbFuel (fuelExhaustedLoc fuelExhaustedMsg driverFuel)          -- CerbND.lean:70
```

`lean_frontend/CerbFuel.lean` (new hand-written seam, on
`handwritten_copy.manifest`, imported by the GENERATED Nondeterminism.lean
via `declare {lean} extra_import \`CerbFuel\``):

```lean
opaque fuelExhaustedLoc : CerbLocation.Loc := CerbLocation.Loc.other "lem: fuel exhausted"   -- :42
def fuelExhaustedMsg : String := "lem: fuel exhausted"                                        -- :49
def driverFuel : Nat := 100000000                                                             -- :71
```

The nine ND-typed worker `_zero` lemmas (all `:= rfl`; binder names are
the generated ones):

```lean
theorem nd_bind_lemFuel_zero {a b c d e f : Type}
    (n : ndM f b d a c) (f1 : f → ndM e b d a c) :
    nd_bind_lemFuel 0 n f1 = ND (fun st => (NDkilled fuelExhaustedKill, st)) := rfl
theorem liftND_lemFuel_zero {a cs err1 err2 info1 info2 st1 st2 : Type}
    (get2 : st2 → st1) (put1 : st2 → st1 → st2) (liftInfo : info1 → info2)
    (liftErr : err1 → err2) (n : ndM a info1 err1 cs st1) :
    liftND_lemFuel 0 get2 put1 liftInfo liftErr n
      = ND (fun st => (NDkilled fuelExhaustedKill, st)) := rfl
theorem liftAction_lemFuel_zero {a cs err1 err2 info1 info2 st1 st2 : Type}
    (get2 : st2 → st1) (put1 : st2 → st1 → st2) (liftInfo : info1 → info2)
    (liftErr : err1 → err2) (act : nd_action a info1 err1 cs st1) :
    liftAction_lemFuel 0 get2 put1 liftInfo liftErr act = NDkilled fuelExhaustedKill := rfl
theorem print_eval_conv_aux_lemFuel_zero
    (_lemReader_tagDefs : Fmap sym (CerbLocation.Loc × tag_definition))
    (dr_st : driver_state) (th_st : thread_state) (pe : generic_pexpr Unit sym) :
    print_eval_conv_aux_lemFuel 0 _lemReader_tagDefs dr_st th_st pe
      = ND (fun st => (NDkilled fuelExhaustedKill, st)) := rfl
theorem drive_nonmemory_steps_aux2_lemFuel_zero
    (_lemReader_tagDefs : Fmap sym (CerbLocation.Loc × tag_definition))
    (acc : Fmap thread_id (List core_step2)) (xs : List Nat) :
    drive_nonmemory_steps_aux2_lemFuel 0 _lemReader_tagDefs acc xs
      = ND (fun st => (NDkilled fuelExhaustedKill, st)) := rfl
theorem driver2_lemFuel_zero
    (_lemReader_tagDefs : Fmap sym (CerbLocation.Loc × tag_definition))
    (with_concurrency : Bool) :
    driver2_lemFuel 0 _lemReader_tagDefs with_concurrency
      = ND (fun st => (NDkilled fuelExhaustedKill, st)) := rfl
theorem find_array_index_lemFuel_zero (size : Nat) (i : Nat) (ival_ : integer_value_base) :
    find_array_index_lemFuel 0 size i ival_
      = ND (fun st => (NDkilled fuelExhaustedKill, st)) := rfl
theorem easy_update_mem_value_aux_lemFuel_zero
    (_lemReader_tagDefs : Fmap sym (CerbLocation.Loc × tag_definition))
    (loc1 : CerbLocation.Loc) (is_strong : Bool) (write_ty : ctype)
    (sh : List shift_path_element) (write_mval : impl_mem_value)
    (current_mval : impl_mem_value) :
    easy_update_mem_value_aux_lemFuel 0 _lemReader_tagDefs loc1 is_strong write_ty sh
        write_mval current_mval
      = ND (fun st => (NDkilled fuelExhaustedKill, st)) := rfl
theorem memcmp_load_aux_lemFuel_zero
    (_lemReader_tagDefs : Fmap sym (CerbLocation.Loc × tag_definition))
    (ptrval : impl_pointer_value) (offset : Int) (max_offset : Int)
    (acc : List impl_mem_value) :
    memcmp_load_aux_lemFuel 0 _lemReader_tagDefs ptrval offset max_offset acc
      = ND (fun st => (NDkilled fuelExhaustedKill, st)) := rfl
```

The three runner leaves (`:= rfl`):

```lean
theorem runNDFuel_zero {a info err cs st : Type} (m : ndM a info err cs st) (st0 : st) :
    runNDFuel 0 m st0 = [(Killed st0 fuelExhaustedKill, [], st0)] := rfl
theorem runND1Fuel_zero {a info err cs st : Type} (m : ndM a info err cs st) (st0 : st) :
    runND1Fuel 0 m st0 = [(Killed st0 fuelExhaustedKill, [], st0)] := rfl
theorem runND1TraceFuel_zero {a info err cs st : Type} (showInfo : info → String)
    (m : ndM a info err cs st) (st0 : st) :
    runND1TraceFuel showInfo 0 m st0 = ([], [(Killed st0 fuelExhaustedKill, [], st0)]) := rfl
```

Constructor disjointness only (NOT distinctness from a genuine `Error0` —
none ships, by the parametricity argument we endorsed):

```lean
theorem fuelExhaustedKill_ne_Undef0 {err : Type} (loc : CerbLocation.Loc)
    (ubs : List undefined_behaviour) :
    (fuelExhaustedKill : kill_reason err) ≠ Undef0 loc ubs := by
  intro h; cases h
theorem fuelExhaustedKill_ne_Other {err : Type} (e : err) :
    (fuelExhaustedKill : kill_reason err) ≠ Other e := by
  intro h; cases h
```

The wrapper `rfl`s:

```lean
theorem driverFuel_eq : CerbFuel.driverFuel = 100000000 := rfl
theorem driver2_wrapper_defeq : driver2 = driver2_lemFuel CerbFuel.driverFuel := rfl
theorem print_eval_conv_aux_wrapper_defeq :
    print_eval_conv_aux = print_eval_conv_aux_lemFuel CerbFuel.driverFuel := rfl
theorem drive_nonmemory_steps_aux2_wrapper_defeq :
    drive_nonmemory_steps_aux2 = drive_nonmemory_steps_aux2_lemFuel CerbFuel.driverFuel := rfl
theorem hack_wrapper_defeq : hack = hack_lemFuel CerbFuel.driverFuel := rfl
theorem nd_bind_wrapper_defeq {a b c d e f : Type}
    (n : ndM f b d a c) (f1 : f → ndM e b d a c) :
    nd_bind n f1 = nd_bind_lemFuel CerbFuel.driverFuel n f1 := rfl      -- FULLY APPLIED (implicit-binder order)
theorem runND_eq {a info err cs st : Type} (m : ndM a info err cs st) (st0 : st) :
    runND m st0 = runNDFuel CerbFuel.driverFuel m st0 := rfl
theorem runND1_eq {a info err cs st : Type} (m : ndM a info err cs st) (st0 : st) :
    runND1 m st0 = runND1Fuel CerbFuel.driverFuel m st0 := rfl
```

The gate on their side: `scripts/check_theorem_axioms.sh:833` `FUEL_THMS`
lists 28 names (24 `CerbND.*` incl. `drive_lemFuel`, 4 `FuelExemplar.*`;
DERIVED count from the array) and fails closed if any probe does not run
cleanly or any cone leaves `[propext, Classical.choice, Quot.sound]`;
`CerbND.lean` is compiled by their default target, so a renamed generated
binder breaks THEIR build first (R2 as asked). Close-out gate output
(their record §10.1, verbatim): `check_theorem_axioms: FUEL arc leg OK (28
contract lemmas + drive_lemFuel + the ∀-fuel exemplar and its instances,
every cone ⊆ [propext, Classical.choice, Quot.sound])`.

The generated fuel-zero arms in the primed workspace (verified by grep,
`.cerberus-ws/lean_frontend/generated`): Nondeterminism.lean:190
(`nd_bind`), :308 (`liftND`), :311 (`liftAction`, `(fun _ => NDkilled
(Error0 …))`); Driver.lean:232 (`print_eval_conv_aux`), :347
(`drive_nonmemory_steps_aux2`, `(fun _ => ND (fun st => …))`), :382
(`driver2`); Defacto_memory.lean:806/:821/:900 (the memory trio) — every
one reads `ND (fun st => (NDkilled (Error0 CerbFuel.fuelExhaustedLoc
CerbFuel.fuelExhaustedMsg), st))` with no `fuelExhausted` wrapper. The
pure-return arms keep the opaque sentinel: Driver.lean:391 (`hack`:
`fuelExhausted Vunit`), Defacto_memory.lean:285 (`mkUnspec`), :735
(`has_concurRead`).

### 1.3 R3 — `driverFuel` as the citable side-condition name: DELIVERED (budget 10^8)

`CerbFuel.driverFuel : Nat := 100000000`, `driverFuel_eq`, and the wrapper
`rfl`s above. The generated wrapper budgets in the primed workspace
(verified): `nd_bind` = `nd_bind_lemFuel 100000000`; `print_eval_conv_aux`,
`drive_nonmemory_steps_aux2`, `driver2`, `hack` = `*_lemFuel 100000000`;
`liftND`, `liftAction`, `find_array_index`, `easy_update_mem_value_aux`,
`memcmp_load_aux`, and every other fueled declaration (evaluator, memory,
front end) = `*_lemFuel lemDefaultFuel` (10^6, LemLib unchanged). Change
manifest §4, verbatim: "Every exported statement over the drive cone
(`drive`, `driver2`, `nd_bind`, `runND`) has fuel side condition
`CerbFuel.driverFuel`; every other declaration's side condition remains
`lemDefaultFuel` (= 10^6) verbatim (the L1 opt-in guarantee)." Consequence
for us (measured in §3, predicted in §3.3): every `rfl`/`show` of ours
that equates a drive-cone wrapper with `lemDefaultFuel` (or the numeral
`999999`) is dead; `pot e ≤ lemDefaultFuel` / `esize e ≤ lemDefaultFuel`
premises (evaluator fuel) and every `liftND`-layer literal are untouched.

### 1.4 The exemplar's statement shape vs our acceptance criterion: IDENTICAL

`lean_frontend/test/Unit/FuelExemplar.lean:429` (verbatim):

```lean
theorem exemplar_certified_shipped_forall (fuel : Nat) :
    ∀ o ∈ CerbND.runND (CerbND.drive_lemFuel fuel fmapEmpty false exemplarFile ["cmdname"]) (dst₀ 0),
      (∃ st, o.1 = Killed st CerbND.fuelExhaustedKill) ∨ (∃ r, o.1 = Active r ∧ post r o.2.2) := by
  cases fuel with
  | zero => exact exemplar_certified_shipped_zero
  | succ n =>
    obtain ⟨thF, hdrv2⟩ := round_done n
    have hrun := drive_after_setup (n+1) _ hdrv2
    intro o ho
    rw [runND_active hrun] at ho
    have h := List.mem_singleton.mp ho
    subst h
    exact Or.inr ⟨_, rfl, finalize_done fmapEmpty _ _ _ fortyTwo rfl rfl⟩
```

with `dst₀ (sup) := (initial_driver_state sup exemplarFile
CerbFS.fs_initial_state).1` and `post r _ := r.dres_core_value = fortyTwo`.
This is our review §6 shape verbatim (ours reads `dst₀ := (initial_driver_
state sup file fs).1`; theirs fixes `sup = 0` — their record §4: "with the
supply seed `sup` symbolic the fuel-0 unification does not see a singleton
— the shipped statements fix `sup = 0`"; our `drive_after_setup` already
carries `sup` symbolically through `prodPostGlobals`, so this is their
exemplar's limitation, not a contract one). Cone: `[propext,
Classical.choice, Quot.sound]` (their §10.1). The proof is OUR method
(`FuelExemplar.Round` re-derives `runOne`, `runOne_bind_active`,
`runND_active`, `prepare_exit_single`, `loop_step_done`, `process_done`,
`driver2_done`, `finalize_done` — DriverCollapse.lean shapes — plus
`budget_succ : CerbFuel.driverFuel = Nat.succ 99999999 := rfl`, which is
the idiom our budget sites must adopt). The `Round` library is test-local
(NOT part of the `CerbND` contract; "test-local unless the consumer asks").

Base case in their exemplar (`exemplar_certified_shipped_zero`, :117):
`List.mem_singleton.mp ho; subst; exact Or.inl ⟨_, rfl⟩` — the fuel-0 run
of the whole `drive_lemFuel 0` evaluates by `rfl` on their tiny file. On
our production files the same base case goes through `drive_after_setup`
at fuel 0 + `driver2_lemFuel_zero` + `runOne_bind_killed` (no new device).

### 1.5 Change-manifest vs tree discrepancies (findings)

1. Manifest §1 cites `CerbND.drive_lemFuel` at `CerbND.lean:446`; the
   `def` is at `:450` (the DriveMirror section opens at :444). Cosmetic.
2. Manifest §5: "149 `driveU` references across 10 files at their
   audit-response-3 head". At our head 9f0c20b: 157 hits across 23 files
   (DERIVED, `grep -rc driveU` over `cerberus-heaplang/CerberusHeapLang`,
   comments included; Adequacy 48, TotalAdequacy 22, Exhibit 11, ListRev
   8, Diverge 8, Loop 7, Wpt 6, Struct 6, ProdEntry 6, Fib 6, TreeRot 4,
   API 4, Wseq 3, Round 3, Case 3, Array 3, DriverCollapse 2, Alloc 2,
   Step/Soundness/ProdLoop/ProdExhibit/Potential 1 each). Stale count on
   their side, not a tree error.
3. Every other cite checked (CerbFuel.lean:42/:49/:71; CerbND.lean:70/:80/
   :85; the nine arm lines; the wrapper numerals; the 28-name gate) matches.

### 1.6 MERGE-SAFE-WITH-NOTES items that concern the consumer

From their record §9–§10 (second design review, 2026-09-03):

- §9.1 / §10 item 1 (the ∀-fuel exemplar): the brute route ("`unfold`,
  expose the opaque read with `driver2_lemFuel.eq_2`, `generalize`/`cases`,
  then `List.mem_singleton.mp` + `rfl`") "times out at the default 200000
  heartbeats … EVEN AT THE LITERAL FUEL 1"; "the blow-up is the ELABORATOR's
  (Meta) whnf of ONE CONCRETE DRIVER ROUND, not the open fuel variable".
  Their conclusion names our discipline as the only viable shape. For the
  migration: no restatement may lean on `decide`/whnf of a round; every
  fuel-generic step goes through a symbolic round lemma (we have them).
- §10 item 3 (TODO "Step-runner execution ceiling"): at 10^8 the process
  STACK ceiling is binding again ("`Stack overflow detected. Aborting.`,
  exit 134, `d_loop_1000000`/`e_memcpy_1000000`; onset between 10^5 and
  10^6 loop iterations"). Irrelevant to kernel statements; relevant to any
  `#eval`-style smoke we run over long programs.
- §9.6 / §10 item 4: every lane that EXECUTES must carry its own bound
  now that the budget is 10^8 (their parse lane stalled >4 min on an
  oracle-long program before the fix). Our `test_unit.sh` executes nothing
  of the driver at runtime; no action.
- §8 "Not provided": no fuel monotonicity, no distinctness from a genuine
  `Error0`, no `DecidableEq`, no `drive_lemFuel_zero`; `hack` (used by
  `finalize`) keeps the panicking opaque sentinel — the one opaque leaf
  inside a shipped-pipeline export's evaluation, registered in their
  TODO.md ("`finalize`'s opaque leaf (upstream)", already LEAVE in our
  2026-09-03 polish ruling).
- `liftAction_lemFuel_zero` DISCARDS a genuine kill it was lifting (their
  design Q2; our review §5 accepted).

## 2. The semantics delta `ddcfc91..f95ef8d9c` on the code-bearing paths

Verbatim `git -C cerberus-lean diff --stat ddcfc919972a31bc43a0454e6b2e76a19e6c4594 f95ef8d9c -- <path>`:

```
### frontend
 frontend/concurrency/cmm_op.lem              | 13 ++++++++++-
 frontend/model/annot.lem                     |  6 ++---
 frontend/model/core.lem                      |  3 +--
 frontend/model/core_run_aux.lem              | 24 --------------------
 frontend/model/ctype.lem                     |  3 +--
 frontend/model/defacto_memory.lem            | 11 +++++++---
 frontend/model/driver.lem                    | 29 +++++++++++++++++-------
 frontend/model/nondeterminism.lem            | 33 ++++++++++++++++++++++------
 frontend/model/state_exception_undefined.lem |  3 +--
 frontend/model/utils.lem                     |  5 ++---
 10 files changed, 75 insertions(+), 55 deletions(-)
### lean_frontend/native
(empty)
### lean_frontend/*.lean
 .../{relsemcore/RelSem/Call.lean => CerbCall.lean} | 137 ++---
 lean_frontend/CerbFuel.lean                        |  73 +++
 lean_frontend/CerbFunMapInstances.lean             |  11 +-
 lean_frontend/CerbMem.lean                         | 388 ++++++++++++-
 lean_frontend/CerbND.lean                          | 310 +++++++++--
 lean_frontend/CerberusFresh.lean                   |   6 +-
 lean_frontend/Main.lean                            |  28 +-
 lean_frontend/relsemcore/RelSem/Cerberus.lean      | 456 ----------------
 lean_frontend/relsemcore/RelSem/ExecModel.lean     |  95 ----
 lean_frontend/relsemcore/RelSem/Machine.lean       | 602 ---------------------
 lean_frontend/relsemcore/RelSem/RunND.lean         | 356 ------------
 lean_frontend/speclab/... (13 files, harness-side)
 lean_frontend/test/Unit/FuelExemplar.lean          | 449 +++++++++++++++
 lean_frontend/test/Unit/TotalityProofTest.lean     |  17 +-
 26 files changed, 1304 insertions(+), 1728 deletions(-)
### lean_frontend/lakefile.toml
 lean_frontend/lakefile.toml | 29 +++++++++++++++++------------
### lean_frontend/lake-manifest.json
 lean_frontend/lake-manifest.json | 2 +-
### lean_frontend/handwritten_copy.manifest   (NEW, 45 lines: the authoritative hand-written seam list, 23 seams)
### Makefile
 Makefile | 44 ++++++++++++++++++++++++++++----------------
### lean_frontend/generated
(empty — gitignored upstream; the delta shows through the workspace re-prime)
```

LemLib: rev UNCHANGED (`045dcb0d57a171eb4fb3a6eb5abe288c227270ce`); only
the URL moved `https://github.com/septract/lem-lean` →
`https://github.com/OathTech/lem-lean` (lakefile.toml + the one-line
lake-manifest.json diff; release-hygiene G8). Our two manifests still
record the septract URL for the inherited `LemLib` entry; Lake accepted
them as is in both builds (no "manifest out of date" message, nothing
rewritten — `git status` shows only the pin file modified). Per the brief,
`lake update LemLib` was NOT run (rev did not move). The URL mismatch is
cosmetic until someone runs `lake update`; `deps/gitconfig` redirects
both spellings.

The `.lem` deltas that reach generated code (read in full): (1) the fuel
arms and budgets in `nondeterminism.lem`/`driver.lem`/`defacto_memory.lem`
(§1); (2) `core_run_aux.lem`: `initial_core_run_state_seeded` DELETED (the
reasoning-era seed-explicit twin) — we do not cite it (0 hits); (3)
`cmm_op.lem`: the `sorry` target_rep for `pretty_stringFromMem_mem_value`
replaced by `CerbMem.stringFromMemValue` (closes our "Also observed" item;
their `check_sorry_token: OK … 0 sorry tokens`); (4) comment-only edits
in annot/core/ctype/state_exception_undefined/utils.

`CerbMem.lean` (388 lines changed): body changes in exactly two
definitions — `reconstructValue_lemFuel` (array arm, mem-scale C1: the
`List.range nNat |>.map (bytes.drop (i*elemSize) |>.take elemSize)`
re-slicing replaced by `(chunksOf elemSize nNat bytes).map …`) and
`memValueToBytes_lemFuel` (struct arm, mem-scale C3: the `accBs ++
List.replicate pad paddingByte ++ bs` accumulation replaced by a reversed
chunk list flattened once). Signatures unchanged. New definitions/lemmas
(additive): `memValueToBytes_append_lemFuel` (the pre-C3 reference form),
`foldl_append_eq_flatten_reverse{,_aux}`, `memValueToBytes_lemFuel_eq_append`,
`memValueToBytes_eq_append`, `chunksOf`, `chunksOf_eq_range_map`,
`reconstructValue_indexed_lemFuel` (the pre-C1 reference form),
`reconstructValue_lemFuel_eq_indexed`, `reconstructValue_eq_indexed`
(kernel-checked equalities with the old text — available to us as
rewrites if any proof needs the old shape). Everything else in the
CerbMem diff is comment text (the reasoning-era framing scrubbed).

Per-name status of the semantics definitions our package cites
(DERIVED: hit counts over `cerberus-heaplang/CerberusHeapLang` +
`RefinedCerberus`, files/hits; status from the `.lem`/seam diffs):

| name | our cites | signature | body |
|---|---|---|---|
| `reconstructValue` (+`_lemFuel`) | 10 files / 52 | unchanged | CHANGED (array arm, C1) |
| `memValueToBytes` (+`_lemFuel`) | 14 / 177 | unchanged | CHANGED (struct arm, C3) |
| `sizeofCtype` | 14 / 394 | unchanged | unchanged |
| `loadM` | 12 / 105 | unchanged | unchanged |
| `storeM` | 12 / 124 | unchanged | unchanged |
| `allocateObject` | 12 / 99 | unchanged | unchanged |
| `allocateRegion` | 1 / 14 | unchanged | unchanged |
| `killM` | 2 / 14 | unchanged | unchanged |
| `eqPtrval` | 8 / 52 | unchanged | unchanged |
| `arrayShiftPtrval` | 6 / 18 | unchanged | unchanged |
| `step_ctx` | 17 / 401 | unchanged | unchanged (core_run.lem untouched) |
| `step_action` | 4 / 54 | unchanged | unchanged |
| `driver2` (wrapper) | 7 / 25 | unchanged | CHANGED: `:= driver2_lemFuel 100000000` (was `lemDefaultFuel`); worker fuel-0 arm CHANGED (the distinguished kill) |
| `drive` | 25 / 108 (word grep; incl. `driveU`-free mentions) | unchanged | unchanged text; its `driver2` callee's budget moved |
| `initial_driver_state` | 7 / 19 | unchanged | unchanged |
| `action_request_sequential2` | 3 / 19 | unchanged | unchanged |
| `advance_step` | 3 / 52 | unchanged | unchanged |
| `drive_nonmemory_steps_aux2_lemFuel` | 3 / 30 | unchanged | fuel-0 arm CHANGED; wrapper budget → 10^8 |
| `runND` (`CerbND`) | 7 / 43 | unchanged | `runNDFuel` fuel-0 leaf CHANGED (`[(Killed st0 fuelExhaustedKill, [], st0)]`, was the `panic!`/`[]` marker); `ndDefaultFuel` → `driverFuel` (10^8) |
| `nd_bind` (+`_lemFuel`) | 2 / 13 (`_lemFuel`) | unchanged | fuel-0 arm CHANGED; wrapper budget → 10^8 |
| `liftND`/`liftAction`/`liftMem` | (via DriverCollapse/Round) | unchanged | fuel-0 arm CHANGED; budget stays `lemDefaultFuel` |
| `CerbTags.TagDefsMap` | 17 / 215 | unchanged (type alias; `CerbTags.lean` still on the manifest) | unchanged |
| `finalize` / `hack` | 4 / 13 | unchanged | `hack` wrapper budget → 10^8 (opaque sentinel kept) |

## 3. The dry-run build

### 3.1 Workspace at the new pin

`scripts/semantics-pin.env`: `CERBERUS_LEAN_COMMIT` set to
`f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf`; no `.cerberus-ws` existed in
this worktree. `scripts/setup-cerberus-dep.sh`, verbatim (rc 0):

```
== setup-cerberus-dep: A: cloning /home/dev/projects/cerberus-lean-proj/cerberus-lean -> /home/dev/projects/cerberus-lean-proj/refined-cerberus/worktrees/repin-scout/.cerberus-ws @ f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf
Cloning into '/home/dev/projects/cerberus-lean-proj/refined-cerberus/worktrees/repin-scout/.cerberus-ws'...
done.
HEAD is now at f95ef8d9c fuel arc CLOSE-OUT 2 (second design review MERGE-SAFE-WITH-NOTES): the ∀-fuel exemplar by the symbolic route; cone leg siblings; TODO ceiling truth; parse-lane fail-open closed; cites; lean_probe trap
== setup-cerberus-dep: B: priming lean_frontend/generated
== setup-cerberus-dep: B: priming lean_frontend/native
== setup-cerberus-dep: B: priming lean_frontend/.lake
check_lem_sync: lean OK (src 4f2e089b39d5b371973513b3350f81d1b89871976f77df9ba4a25da3421d0c54, gen 49ad8b2c359cb0b36ed12913eb0bb3a4986c0ee582fe8e735e700297d38eee00)
== setup-cerberus-dep: C ok: 23 hand-written seams byte-identical to the pin
== setup-cerberus-dep: DONE. Lake consumes /home/dev/projects/cerberus-lean-proj/refined-cerberus/worktrees/repin-scout/.cerberus-ws/lean_frontend as a path dependency.
```

Note: the primary checkout IS at the pin (`git rev-parse HEAD` =
`f95ef8d9c…`, branch `mdd/cerberus-lean`), so section B's content guard
took the equal-commit path (the guard branch did not need to run); section
C (23 seams byte-identical, from the pin's own `handwritten_copy.manifest`
— the first pin that ships one) passed. `.primed-from`:
`f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf 2026-09-03T05:52:15Z`.

### 3.2 Builds (all through `scripts/capped`, `CERB_MEM_MAX=48G`; no UNCAPPED warning)

Root package (`lake build` in the worktree root), rc 0, 05:52:51 →
05:55:18 (~2.5 min wall): `Build completed successfully (371 jobs).`;
32 Built / 4 Replayed / 0 errors. Built (dep cone up to `CerbMem`, then
ours): `Loc Enum Global Range Bimap Debug Utils Exception Symbol IntegerType
Annot Undefined Ctype CerbCtypeInstances CerbTags Nondeterminism
CerberusImpl IntegerImpl Cn Cabs (126s) AilSyntax Implementation GenTypes
Constraint TypingError ErrorMonad AilTypesAux Mem_common CerbMem
RefinedCerberus.SemanticsSmoke RefinedCerberus.Audit RefinedCerberus`.
Audit output verbatim: `RefinedCerberus axiom sweep: 2 theorems, all cones
within the classical trio` / `RefinedCerberus banned-axiom sweep: 3
constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent
from all cones`.

cerberus-heaplang (`lake build` in `cerberus-heaplang/`), rc 1, 05:56:13 →
06:00:06 (~4 min wall); 70 Built (45 dep modules incl. `Cabs (179s)`,
`Defacto_memory (1.9s)`, `Core_aux (2.0s)`, `Core_run (3.1s)`, `Driver
(1.8s)`, `CerbND (524ms)`; 25 of ours) / 13 Replayed. Verbatim tail:

```
Some required targets logged failures:
- CerberusHeapLang.DriverCollapse
error: build failed
```

### 3.3 Error census

ONE failing module, FOUR errors, ALL of one cause (the R3 budget move:
drive-cone wrappers now unfold to `100000000`, our proofs equate them with
`lemDefaultFuel`/`Nat.succ 999999`). Verbatim:

```
error: CerberusHeapLang/DriverCollapse.lean:123:2: maximum recursion depth has been reached
error: CerberusHeapLang/DriverCollapse.lean:140:2: maximum recursion depth has been reached
error: CerberusHeapLang/DriverCollapse.lean:221:55: Type mismatch
  rfl
has type
  ?m.61 = ?m.61
but is expected to have type
  CerbND.ndDefaultFuel = Nat.succ 999999
error: CerberusHeapLang/DriverCollapse.lean:548:11: maximum recursion depth has been reached
```

| module | errors | site | cause |
|---|---|---|---|
| DriverCollapse | 1 | :123 `runOne_bind_active`: `show runOne (nd_bind_lemFuel lemDefaultFuel (ND g) f) s = _` | FUEL/budget — `nd_bind` is now `nd_bind_lemFuel 100000000`; the `show` forces a 10^8-vs-10^6 numeral defeq (recursion depth) |
| DriverCollapse | 1 | :140 `runOne_bind_killed`: same `show` | FUEL/budget, same |
| DriverCollapse | 1 | :221 `runND_active`: `show CerbND.ndDefaultFuel = Nat.succ 999999 from rfl` | FUEL/budget — `ndDefaultFuel = driverFuel = 10^8` |
| DriverCollapse | 1 | :548 `driver2_done`: `hloop` stated at `drive_nonmemory_steps_aux2_lemFuel lemDefaultFuel` fed to the wrapper call | FUEL/budget — wrapper is at 10^8 |

Renamed-constant errors: 0. Changed-signature errors: 0. Errors from the
CerbMem C1/C3 body changes: 0 in every module that reached the compiler.

Modules that BUILT GREEN at the new pin (25): Step, EnvLaws, Heap, Lang,
Rules, Examples.MirrorCoverage, Wps, Examples.Layout, Wpt, Soundness,
Potential, Adequacy, TotalAdequacy, API, CaseExhibit, WseqExhibit,
Examples.ReadinessSmoke, Exhibit, LoopExhibit, EvalClass, FibExhibit,
DivergeExhibit, ArrayExhibit, ListRevExhibit, TreeRotExhibit. Note that
`Heap`, `Rules`, `Soundness`, `Examples.Layout`, `LoopExhibit`,
`ListRevExhibit` and `TreeRotExhibit` are exactly the modules that unfold
or rewrite `reconstructValue_lemFuel` / `memValueToBytes` (TreeRot:141–
144, :1000–1030, :1350–1379; ListRev:255–258, :1063, :1895; Loop:283;
Layout:160/189/250; struct-typed nodes and `spliceBytes` over
`memValueToBytes` of struct values) — the C1/C3 body changes broke NONE of
them (measured, not guessed).

Modules NOT REACHED (skipped behind the DriverCollapse failure; DERIVED
from the import graph — `Round` imports `DriverCollapse`; everything
production-side imports one of them): `Round`, `ProdLoop`, `ProdEntry`,
`ProdExhibit`, `ProdLoopExhibit`, `StructExhibit`, `AllocExhibit`,
`Audit`. Their breakage is PREDICTED below from a static census of the
same cause (every site that equates a drive-cone wrapper/runner with
`lemDefaultFuel` or the `999999`-family numerals), NOT measured; the
`liftND`/`update_env_aux`/`collect_saves`/evaluator sites at `lemDefaultFuel`
(Round:706/:710/:1907, ProdLoopExhibit:1379–1391, every `show
lemDefaultFuel = 999999 + 1 from rfl` under a `pot`/`esize` bound) stay
valid — those workers remain at 10^6.

Predicted additional breakage (static, unmeasured):

| module | sites | cause |
|---|---|---|
| Round | :3760–3767 (`nd_bind_lemFuel 999999`, `show … nd_bind_lemFuel lemDefaultFuel …`, `lemDefaultFuel = Nat.succ 999999`), :3937 (`bind_branch_active 999998` ×3 — `nd_bind` layers), :3946–3954 (`ndDefaultFuel = Nat.succ 999999`, `runNDFuel_nd 999999`, `runNDFuel 999999`, `runNDFuel_active 999998`) | FUEL/budget |
| DriverCollapse (beyond the 4) | :529 (`hloop` binder at `lemDefaultFuel` — the statement, not just the proof) | FUEL/budget |
| ProdEntry | :327 (`hdrv2 : runOne (driver2_lemFuel lemDefaultFuel …)` — statement), :393 (`driver2_done 999999`) | FUEL/budget |
| ProdLoop | `DriverDoneAt` (:50–) is fuel-generic (`k + 2 ≤ fl`) — likely clean; `prod_run_eqJ` consumers instantiate `fl := lemDefaultFuel` (ProdEntry:392 `hdd … lemDefaultFuel rfl rfl rfl hQe hfl`) | FUEL/budget (the `k + 2 ≤ lemDefaultFuel` premise itself stays TRUE and provable, but the instantiation must become `driverFuel`, and the exported premise should be restated as `k + 2 ≤ CerbFuel.driverFuel` per R3) |
| ProdLoopExhibit, ProdExhibit, StructExhibit, AllocExhibit | the `hfl`/`k + 2 ≤ lemDefaultFuel` discharges feeding `prod_run_eqJ` (ProdLoopExhibit:679 `rw [show lemDefaultFuel = 999999 + 1 from rfl] at hfuel ⊢`) if `prod_run_eqJ`'s premise moves to `driverFuel` | FUEL/budget (follows the ProdEntry restatement) |
| StructExhibit | unmeasured for C3: it is the one struct-typed `memValueToBytes` client not reached | unknown until measured (ListRev/TreeRot suggest clean) |
| Audit | 116 exact export pins: statement text changes (`lemDefaultFuel` → `driverFuel` in premises) move signatures; no cone change expected | mechanical re-pin of the signature file |

### 3.4 An operational observation: the shared path dependency rebuilds on alternation

Both consumers point Lake at the same `.cerberus-ws/lean_frontend` and
Lake builds it in place (`.cerberus-ws/lean_frontend/.lake/build`). The
heaplang build REBUILT the dep cone the root build had just built (`Cabs`
126 s in root, then 179 s again in heaplang; the olean at
`.cerberus-ws/lean_frontend/.lake/build/lib/lean/Cabs.olean` re-stamped
05:59:11), and a second root build immediately afterwards rebuilt it
AGAIN (second root build 06:05:27 → 06:08:16, rc 0, 29 Built / 5 Replayed — the same dep cone `Loc Enum Global Bimap Range Utils Debug Exception Symbol IntegerType Annot Undefined Ctype CerbCtypeInstances CerbTags Nondeterminism CerberusImpl IntegerImpl Cn Cabs AilSyntax Implementation GenTypes Constraint TypingError ErrorMonad AilTypesAux Mem_common CerbMem`, i.e. `Loc`…`CerbMem` + the 3 root modules, `Cabs` recompiled a third time). The 2026-09-02 repin notes recorded the first half of
this ("Primed oleans did not replay … cause not investigated"); it is
not a one-time re-prime effect — each alternation between the two
consumers costs a dep rebuild (~2.5–3.5 min, Cabs-dominated). Cheap today;
worth one look by whoever runs `test_unit.sh` (which builds both) in a
loop.

## 4. Estimate (ESTIMATE, labelled) and recommended slice plan

### 4.1 (a) Mechanical rename/signature fixes

None. No cited constant was renamed; no signature moved. The pin move
itself (env file + `rm -rf .cerberus-ws` + setup) is done in this
worktree and reusable.

### 4.2 (b) Proof breakage from the CerbMem C1/C3 body changes

Measured zero on the seven modules that unfold/rewrite the two changed
definitions (§3.3). Residual: `StructExhibit` (unreached). If it does
break, `CerbMem.memValueToBytes_eq_append` /
`reconstructValue_eq_indexed` restore the old text as a rewrite. Estimate:
0–1 small proof; less than an hour.

### 4.3 The budget move (R3) — the actual measured breakage class

Every site in §3.3 is the same edit: replace `lemDefaultFuel` /
`Nat.succ 999999` / `999999`-family numerals by `CerbFuel.driverFuel` /
`Nat.succ 99999999` / `99999999`-family numerals at the DRIVE-CONE workers
only (`nd_bind`, `driver2`, `drive_nonmemory_steps_aux2`, `runND`/
`ndDefaultFuel`, `hack`), keeping `lemDefaultFuel` at `liftND`/`liftAction`
and every evaluator/static-bound site. Their exemplar shows the idiom that
elaborates at default heartbeats: `theorem budget_succ :
CerbFuel.driverFuel = Nat.succ 99999999 := rfl` then `rw [budget_succ]`
before `unfold`. Sites: DriverCollapse 5 (:100 add `driverFuel_succ`, :123,
:140, :221, :529/:548), Round ~10 (:3760–3767, :3937, :3946–3954), ProdEntry
2 (:327, :393), plus the `hfl` instantiation in `prod_run_eqJ`
(ProdEntry:392) and its clients if the exported premise is restated
(ProdLoopExhibit:679 and the `hfl` discharges in the six production
exhibits). Two design points inside this class, for the orchestrator:
(i) the exported premise `k + 2 ≤ lemDefaultFuel` in `prod_run_eqJ` /
`*_certified_production` is still TRUE and provable at 10^8 (weaker than
needed) — keep verbatim, or restate as `k + 2 ≤ CerbFuel.driverFuel` (R3's
intent; changes the 116-pin signature file); recommendation: restate,
citing `CerbFuel.driverFuel` as the manifest names it; (ii) `nd_bind`
layer arithmetic in Round (:3937 `999998` ×3, `999996`) is numeral
bookkeeping that would be cleaner as `Nat.succ n` lemmas (already the
shape of `bind_branch_active`), not new numerals. Estimate: half a day
including the two rebuild-and-read cycles behind the frontier (Round
first, then the production layer).

### 4.4 (c) The fuel-lane restatement (the `driveU` deletion)

R1 WAS delivered, so the restatement is over the SHIPPED `CerbND.
drive_lemFuel fuel` end to end — setup, main loop, `finalize` — NOT over
`driver2_lemFuel fuel` plus our own `finalize` call; nothing is owed to
the genuine-driver rule beyond deleting `driveU`. Target shape (our
review §6 = their exemplar, per program):

```lean
theorem <program>_certified_shipped (sup : Nat) (fs : CerbFS.FsState) (args : List String) (fuel : Nat) … :
  ∀ o ∈ CerbND.runND (CerbND.drive_lemFuel fuel fmapEmpty false (prodFile e) args)
        ((initial_driver_state sup (prodFile e) fs).1),
    (∃ st, o.1 = Killed st CerbND.fuelExhaustedKill) ∨
    (∃ r, o.1 = Active r ∧ ψ r.dres_core_value o.2.2.layout_state)
```

Pieces and where they come from:

1. `drive_after_setup` (ProdEntry:325) generalised from `_root_.drive` to
   `CerbND.drive_lemFuel fuel` with `hdrv2` at `driver2_lemFuel fuel`: the
   same proof (`unfold CerbND.drive_lemFuel` instead of `unfold
   _root_.drive`; the setup binds are fuel-independent — their
   `FuelExemplar.drive_after_setup` is this theorem on their file). The
   total lane then recovers `_root_.drive` through `CerbND.drive_wrapper_
   defeq`. Small.
2. The base case (fuel 0): `drive_after_setup` needs a KILLED variant —
   `runOne (driver2_lemFuel 0 …) S = (NDkilled fuelExhaustedKill, S)` by
   `driver2_lemFuel_zero`, propagated by `runOne_bind_killed` (exists,
   DriverCollapse:131) through the trailing binds, then `runND` of a
   one-layer killed computation = `[(Killed …, [], S)]` (a `runND_killed`
   sibling of `runND_active`, `rfl`-class). Small.
3. The step case (fuel n+1): ONE engine round through `driver2_lemFuel
   (n+1)` — `driver2_done` (DriverCollapse:525) handles PROGRAM-DONE in
   one round; the PARTIAL lane needs the NOT-done round too: `driver2_
   lemFuel (n+1)` = one `drive_nonmemory_steps_aux2` step (our
   `loop_step_frag`/Round shapes) followed by `driver2_lemFuel n` on the
   successor state, plus the killed/forking arms classified. THIS is the
   real content of the slice: a `driver2_step` lemma (`runOne
   (driver2_lemFuel (n+1) tds false) dst` = either done-in-one-round, or
   `runOne (driver2_lemFuel n tds false) dst'` after one fragment step,
   or a kill) — the fuel-indexed successor of what `DriverDoneAt`
   delivers today by exhausting the loop inside `drive_nonmemory_steps_
   aux2_lemFuel`'s OWN fuel (`fl`, `k + 2 ≤ fl`). Note the two fuels are
   different budgets: `driver2_lemFuel`'s fuel counts driver ROUNDS
   (outer loop, one per `new_drive_core_threads`), while our current
   collapse runs the whole fragment inside ONE round's `drive_nonmemory_
   steps_aux2` loop (whose fuel is the inner `fl`). So for a program
   that terminates in one round (every present exhibit — `driver2_done`
   returns after the first round), the ∀-fuel statement is
   `cases fuel` + `driver2_done n` exactly as their exemplar; the
   induction on `fuel` is only needed for programs that need >1 driver
   round, i.e. that block/fork between rounds (none in the fragment).
   The partial lane's "may not terminate" content therefore lives in
   the INNER fuel `fl`, where the classification needed is: `drive_
   nonmemory_steps_aux2_lemFuel fl` at any `fl` either delivers, kills,
   or exhausts to `fuelExhaustedKill` (by `drive_nonmemory_steps_aux2_
   lemFuel_zero` + our per-step `loop_step_frag` + the ND-bind
   propagation of the kill). That is an induction on `fl` over
   `stepDischarge`-shaped rounds — the material of Round.lean, re-cut
   with a killed disjunct.
4. `MemTripleU` (Adequacy:1132) → restate over the shipped run: the
   inner `driveU M aids n` ↔ engine bridge is what `engine_step_matchU`
   / `loop_step_frag` already prove per step (mirror completeness lands
   the "engine round is classified" half); the ∀-length `driveU` is
   replaced by the ∀-`fl` inner-loop statement of item 3. `project_
   triple*` keep their Iris side verbatim and change only the conclusion
   type; `wpt_engine_boundU*` (total) become the `k`-bounded
   instantiation of the same statement. `SemTripleU_iff_Mem` stays.
5. Cost against the genuine-driver rule: zero — the statement's referent
   is `CerbND.runND ∘ CerbND.drive_lemFuel ∘ initial_driver_state` (all
   shipped; `drive_lemFuel` is kernel-pinned to `drive` by
   `drive_wrapper_defeq`). `runOne`, `driveU`, `stepOutcomes` remain
   proof devices only. The PROVISIONAL labels (Adequacy 16, README 26,
   WALKTHROUGH 9, API 4, TotalAdequacy 4, ARCHITECTURE 4, ProdExhibit 1 —
   DERIVED) are deleted with `driveU`.

Estimate: items 1–2 a day; item 3 (the fuel-indexed round/step
classification with the killed disjunct, over the existing Round
machinery) 2–3 days for the fragment; item 4 (the triple/projection
restatement + exhibits + Audit pins + docs) 1–2 days. Risks: (α) item 3
is the place a grind could start — a `driver2_step` lemma proved by
unfolding a concrete round in the elaborator is exactly what their record
says times out at fuel 1; it must be stated symbolically over an
arbitrary `dst` with the thread-list shape as a hypothesis (our
`driver2_done` already is). (β) the opaque `CerbGlobal.current_execution_
mode ()` read inside `driver2` is cased once per round lemma (their
`driver2_done` does it) — fine, but every new round lemma pays it. (γ)
`sup` symbolic: their exemplar fixes `sup = 0`; our `drive_after_setup`
carries `sup` — keep it symbolic and confirm the fuel-0 unification on
the production file (unmeasured). (δ) `finalize`'s `hack` leaf is opaque
at exhaustion; on terminal states our `finalize_done` evaluates it at
fixed budget — unchanged, but a partial-lane final state reached by an
exhausted INNER loop is not terminal, and `finalize` is never reached
there (the kill short-circuits the bind) — no issue, noted for the
reviewer.

### 4.5 Recommended slice plan (order, risks, what could grind)

1. **Re-pin slice (mechanical; half a day; FAST-GATE commit).** Reuse
   this worktree's `.cerberus-ws` (already primed + built at the pin).
   Fix the §3.3 budget class in DriverCollapse, rebuild to reach Round,
   fix Round's sites, rebuild to reach the production layer, fix
   ProdEntry (+ decide (i) above on the exported premise), run
   `test_unit.sh`. Expected end state: green at the new pin with
   `driveU` still present and PROVISIONAL labels still on. Also: delete
   the "opaque `fuelExhausted`" prose in Adequacy:69, DriverCollapse:44–
   77, Soundness:56/:1527, ProdEntry:45 (it is now false for the ND-typed
   workers) — doc truth, same commit. Could grind: nothing, if the
   `budget_succ` idiom is used (never a numeral defeq via `show`).
2. **Fuel-lane restatement slice (the real one; ~1 week; FULL gate).**
   Items 4.4/1–4 in that order; `driveU` deleted at the end, PROVISIONAL
   removed everywhere, acceptance goal (1) closed. Could grind: item 3
   if attempted by evaluation; stop-and-report if any round lemma
   exceeds default heartbeats.
3. **Pre-merge audit** over the range since the last audited head (K1
   audit at 29f475f + whatever K2 lands), per the 2026-09-03 [USER]
   ruling — the re-pin changes the trust base (new semantics tree), so
   the audit must re-verify the pin (`setup-cerberus-dep.sh --check`),
   the seam identity (section C), and the Audit.lean pins against the
   new signature file.

Sequencing against Lane A: the re-pin slice conflicts textually with K2
in DriverCollapse/Round only at the budget sites (small hunks); land K2
first or rebase the re-pin on it — either is cheap. The restatement
slice touches Adequacy/TotalAdequacy/ProdEntry/ProdLoop headers that K2
also touches (the allocation invariant) — serialise, K2 first.

## 5. What blocked or was not done

- Nothing blocked. No `lake update` was needed (LemLib rev unchanged).
  Manifests untouched.
- The census past the DriverCollapse frontier is PREDICTED (§3.3 second
  table), not measured, because measuring it requires editing proofs,
  which this scout was forbidden to do.
- The content guard of `setup-cerberus-dep.sh` §B did not exercise its
  diff branch (source == pin); section C did run and passed.
- Scratch logs (`.repin-logs/`) were not committed; every quoted line
  above is in the record. The worktree's `.cerberus-ws` (primed + built
  at `f95ef8d9c`) and both packages' `.lake` are left in place for the
  migration worker.
