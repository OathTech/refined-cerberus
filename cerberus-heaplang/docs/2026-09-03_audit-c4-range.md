# CALLS C4 range audit (`d05f724..8094738`) — 2026-09-03

[AGENT] Independent auditor record (fresh auditor, not the C3 one).
Audited in the fixed detached copy `worktrees/audit-c4-8094738` (HEAD
`8094738`, detached; `.lake` and `.cerberus-ws` primed, cerberus-lean pin
`f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf` — read off
`.cerberus-ws/lean_frontend` at the pin). Read-only except this file and
an ephemeral scratch dir (`.audit-scratch/`, deleted after this report
was written; every quoted line below was copied from it verbatim before
deletion). Nothing committed, merged or pushed. Every Lean invocation
went through `scripts/capped` with `CERB_MEM_MAX=40G` (the orchestrator's
mid-audit instruction: a second heavy build started on the box); no
`uncapped` warning appeared in any log. Brief: `docs/AUDIT-BRIEF.md`.
Inputs: the six-commit range (21 files, +32299/−213, of which the
snapshot is 29624 lines), the worker record
`docs/2026-09-03_c4-notes.md`, the two snapshots
(`_c3-signatures-post.txt` as pre, `_c4-signatures-post.txt` as post),
the C3 range audit `docs/2026-09-03_audit-c3-range.md` (handoffs
H-2/H-3/H-4), `ARCHITECTURE.md` read in full as a core document at a
major revision, `docs/DECISIONS.md` tail, and the PINNED SEMANTICS at
`.cerberus-ws/lean_frontend/generated/` plus the pinned LemLib.

Method. (1) The FULL Lean diff was read (Soundness, Adequacy, EnvLaws,
CallSmoke, Wpt/TotalAdequacy headers, Audit, the whole of ProdLoop's
additions) and the two new files `ProdEntry.lean` (post-state, in full)
and `FibRecExhibit.lean` (in full); the pre-existing collapse lemmas the
new lane consumes (`loop_step_frag`, `driver2_done`, `finalize_done`,
`DriverDoneAt`) were read at their statements. (2) Every engine fact the
record cites was re-measured on the pin by string search with byte
offsets. (3) The FULL gate was run by the auditor in the audit copy
(twice: the first log landed in `/tmp`, which the sandbox would not read
back; the second is quoted below). (4) The snapshot was regenerated at
HEAD and compared byte-for-byte; the census was re-derived by script
from the two committed files; the eight pre-C4 production statements were
diffed in source (statement through `:= by`) across the range ends.
(5) `#print axioms` on 40 names. (6) Three `lake env lean` probes: the
registration order (a positive and a NEGATIVE `rfl`), `driveU` on the
two-procedure file at budgets 0..31 for n = 0, 1, 2, 3, and THE SHIPPED
DRIVER'S OWN PER-THREAD LOOP executed at fuel `fibRounds n + 1..4` from
the driver2 entry state. (7) Four plant tests, each with
rebuild-after-revert. (8) The 66 package linter warnings re-tallied by
file against the C3 audit's H-1.

Quotes are verbatim (the generated file has double spaces; engine quotes
are trimmed at the cut boundaries shown). Tallies marked DERIVED were
computed by the auditor's scripts or arithmetic.

## Verdict

**PASS — grade A−. Merge-ready for `d05f724..8094738` on operator
sign-off, with two docs-only corrections (R-1, R-2) to land with the
merge; no proof changes required.** No T- (trust) or C- (correctness)
finding. The load-bearing claim holds by measurement: the production
statement's execution function is the shipped composite `CerbND.runND
(drive fmapEmpty false (prodFileWith …) args) ((initial_driver_state sup
(prodFileWith …) fs).1)` with nothing package-defined in it but the
program, the synthetic file builder and the readout/budget vocabulary
(`fibSpec`, `fibRounds` — both disclosed on every surface); its cone is
`prod_run_eqJ_procs` ← `drive_after_setup_with` (the cold start computed
through the engine's own setup functions, the `main` lookup by the
β-generic law) + `wpt_driver_done_procs` ← `wpt_driver_cps` ← every round
`loop_step_frag` at the live control; every hypothesis is satisfiable and
none trivialises (the section variables are universally quantified — a
bad instantiation can only make the theorem stronger, not vacuous); the
`exec_loc`/`current_loc` tie is exactly the engine's PCALL write and Plant
C shows it load-bearing; the CPS budget induction is well-founded (strong
induction on `k`, the call case at `m < k` and `k' < k` from `1 + m + k' ≤
k`) and the continuation-budget arithmetic closes by `omega` at every
site; `fibRounds` is EXACT (`driveU` reaches `.done` at exactly `fibRounds
n + 2` for n = 0..3); the registration order the worker says it measured
is confirmed by a positive and a falsified negative `rfl`; the census
holds exactly (ADDED 123 / REMOVED 3 / CHANGED 3, the three the
recursors); the HEAD snapshot is byte-identical to the committed post
file; all 28 new pins are trio-exact, the two declared sub-trio names are
`[propext]` and `[propext, Quot.sound]`; the eight pre-C4 production
statements are byte-identical in source and snapshot; all four plants
went loud and every revert came back green at 372; the DECISIONS gate
tail matches the auditor's run line for line; the LICENSE byte-identity
claim holds.

Deductions from A: two stale module headers that the docs rewrite edited
around but did not fix (R-1 — they contradict README/ARCHITECTURE on the
fuel-request status), the ARCHITECTURE §7 ledger header still dated to
the kill/free arc (R-2), and the one-unit slack in the `+ 4` budget
hypothesis that the record's accounting does not name (R-3, a Note).

## Findings, ranked

No T- or C- findings. Nothing in the range is unsound, vacuous or
overclaimed relative to the theorems.

### R-1 (Low — record/docs, in-range): two module headers still say the fuel-exhaustion outcome is AWAITED; README, ARCHITECTURE and Adequacy.lean say it is LIFTED

Evidence. `CerberusHeapLang/TotalAdequacy.lean:43–47` (post-state):
"not yet the root-of-trust statement, which is over the shipped driver
and awaits the cerberus-lean fuel-exhaustion outcome
(docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md,
repository root); restated with no other change when it lands." —
`git blame`: `8e5ca7b9 2026-09-02 17:13` (before the 2026-09-03 re-pin);
the NEXT sentence (lines 48–56) was rewritten in this range by
`4b9a7053` ("the Lean headers' stale C4 forward references"), so the
stale sentence was edited around. `CerberusHeapLang/API.lean:55–58`
carries the identical sentence (also `8e5ca7b9`); API.lean's table was
rewritten in `4b9a705` too. Meanwhile `Adequacy.lean:67–75` says "The
former obstacle … is LIFTED at the current pin (cerberus-lean
`f95ef8d9c`, the fuel arc, re-pinned 2026-09-03)", `README.md:296–300`
"The semantics-side prerequisite HAS LANDED at the current pin … is
lifted", `ARCHITECTURE.md:339–349` the same. The package contradicts
itself on the status of its own PROVISIONAL label's obstacle; a reader of
TotalAdequacy or API (the public-surface module) is told to wait for
something that landed. Premise verified by measurement: yes (grep +
blame). Not a logic gap; a shop-window-adjacent staleness.
Fix required: in `TotalAdequacy.lean:43–47` and `API.lean:55–58` replace
"and awaits the cerberus-lean fuel-exhaustion outcome (…); restated with
no other change when it lands" by Adequacy.lean's wording ("restated with
no other change in the fuel-lane restatement slice; the former obstacle …
is LIFTED at the current pin `f95ef8d9c`").

### R-2 (Low — core document): ARCHITECTURE §7's ledger is dated to the close of the kill/free arc; C4 closed the calls arc

Evidence. `ARCHITECTURE.md:356–357`: "THE THREE ACCEPTANCE GOALS ([USER
2026-09-02], DECISIONS.md), with their status at the close of the
kill/free arc (2026-09-03):" — while the same section's goal-1 bullet
says "the calls arc (C1–C4, CLOSED 2026-09-03 — below)" and the last
bullet is "**The calls arc C1–C4 — CLOSED (2026-09-03).**". The status
header is the one sentence a professor reads to date the ledger, and it
is one arc stale. Premise verified: yes (read).
Fix required: "with their status at the close of the calls arc
(2026-09-03)" (or simply "as of 2026-09-03, C4 landed").

Otherwise the core document is accurate to the tree: every theorem name
in §2/§4/§6/§7 exists at HEAD with the described statement (checked
`BareHead.call`, `BareHead.decomp_call_root`, `wpt_driver_cps`,
`wpt_driver_done_procs`, `DriverDoneCtl`, `LabeledProcs`, `prodFileWith`,
`prodCtl`, `prodCtx`, `prod_run_eqJ_procs`, `prodFile_eq_with` (`rfl`),
`symAdd_lookup(_two)`, `envAdd_lookup`); the eight closed statements
listed in §6 are exactly the eight `runND ∘ drive ∘ initial_driver_state`
statements in the tree; the decision points are disclosed in §4 (the two
lanes) and §7 (the total `driveU` lane "deleted with the lane"); no
history has crept into §1–§6 beyond dated pointers.

### R-3 (Note — record precision): `hfuel : fibRounds n.toNat + 4 ≤ CerbFuel.driverFuel` has one unit of slack; the record's accounting does not name it

Evidence (measured). `driveU` on the two-procedure file at the production
entry control (`frCtx default n B B B B B 0`, `B := BTy_object
OTy_integer`, `prodMem₀`, `aids := fun _ => 0`), verbatim `#eval`:

```
[(0, "more"), (1, "more"), (2, "more"), (3, "more"), (4, "more"), (5, "done(v = fib 0 = 0)"),
  (6, "done(v = fib 0 = 0)"), (7, "done(v = fib 0 = 0)")]
[(0, "more"), (1, "more"), (2, "more"), (3, "more"), (4, "more"), (5, "done(v = fib 1 = 1)"),
  (6, "done(v = fib 1 = 1)"), (7, "done(v = fib 1 = 1)")]
[… (16, "more"),
  (17, "done(v = fib 2 = 1)"), (18, "done(v = fib 2 = 1)"), (19, "done(v = fib 2 = 1)")]
[… (28, "more"), (29, "done(v = fib 3 = 2)"), (30, "done(v = fib 3 = 2)"),
  (31, "done(v = fib 3 = 2)")]
[(0, 3, 5), (1, 3, 5), (2, 15, 17), (3, 27, 29), (4, 51, 53), (5, 87, 89), (6, 147, 149), (7, 243, 245)]
```

(the last line is `(n, fibRounds n, fibRounds n + 2)`). So `.done` at
EXACTLY the certified budget `fibRounds n + 2` for n = 0, 1, 2, 3 —
`fibRounds` is exact, as the record claims (§6), and the C3 auditor's
`1 + m + k'` reading extends to the recursive case. THE SHIPPED LOOP
itself, `runOne (drive_nonmemory_steps_aux2_lemFuel fl fmapEmpty fmapEmpty
[0]) (prodEntryStateWith procs 0 (frMain default n) CerbFS.fs_initial_state)`
at `fl ∈ {fibRounds n + 1, …, + 4}`, verbatim:

```
[(0, [(4, "NDkilled"), (5, "NDkilled"), (6, "NDactive done(fib 0)"), (7, "NDactive done(fib 0)")]),
  (1, [(4, "NDkilled"), (5, "NDkilled"), (6, "NDactive done(fib 1)"), (7, "NDactive done(fib 1)")]),
  (2, [(16, "NDkilled"), (17, "NDkilled"), (18, "NDactive done(fib 2)"), (19, "NDactive done(fib 2)")]),
  (3, [(28, "NDkilled"), (29, "NDkilled"), (30, "NDactive done(fib 3)"), (31, "NDactive done(fib 3)")])]
```

The driver needs exactly `fibRounds n + 3` iterations (the `k − 1` mirror
rounds + the done-recording + the drain); the theorem demands `k + 2 =
fibRounds n + 4`. The slack is the `k + 2 ≤ fl` of `DriverDoneCtl`
(inherited unchanged from the pre-C4 `DriverDoneAt`): the budget `k`
already contains the top-level value's `deliveryCost` (1 for a bare
value, 2 for an annotated one — `wpt`'s value clause), which is what the
done-recording iteration corresponds to, and `driverDoneCtl_value`
spends two further iterations regardless of `k`. `k + 1 ≤ fl` would be
exact in both value shapes (annot: REMOVE-ANNOT + done + drain = 3 =
deliveryCost 2 + 1). The record §6 describes the `+ 2` as "the
done-recording and drain iterations" — an accurate description of
`driverDoneCtl_value`, but the sentence "hence `hfuel : fibRounds
n.toNat + 4`" presents the bound as the sum of exact parts, which it is
not by one. Nothing on any surface claims the `+ 4` is tight, the bound
is an upper bound and the theorem is correct; the `n ≤ 33` reading is
unaffected (`fibRounds 33 + 3 = 68434638 ≤ 10^8 < fibRounds 34 + 3`,
DERIVED). The same slack is in the seven earlier statements' `k + 2`.
Premise verified by measurement: yes (the loop executed).
Fix (optional, a later hygiene slice, not a merge condition): one
sentence in the record §6 naming the slack; the mover, if wanted, is
`DriverDoneAt`/`DriverDoneCtl` at `k + 1 ≤ fl` with `driverDoneCtl_value`
at `k ≥ 1` — an internals change with eight public statements' `hfuel`
constants to retighten, so only worth doing alongside the fuel-lane
restatement.

### R-4 (Note — labels): "eighth root-of-trust statement" (package) vs "ninth production statement" (DECISIONS)

Evidence. ARCHITECTURE §6/§7, README:94, WALKTHROUGH:1688, the
FibRecExhibit header:8 and the Audit.lean pin comment say "eighth
root-of-trust statement"; `docs/DECISIONS.md:1557` says "The ninth
production statement". Both are true under their own count: the census
(record §8) lists "all eight pre-C4" production statements INCLUDING the
generic `prod_run_eqJ`, so 8 + 1 = 9; the closed shipped-driver
statements are 7 + 1 = 8. A reader crossing the two surfaces trips.
Fix (optional): DECISIONS/notes say "the eighth closed shipped-driver
statement (the ninth entry of the production-statement census, which
counts the generic `prod_run_eqJ`)".

### H-1 (Hygiene — nit): the exhibit header quotes a different derived closed form than the theorem it sits above

Evidence. `FibRecExhibit.lean:39–40`: "`fibRounds n ≤ 9 · fib (n + 2)`
(derived), so `n ≤ 33` is in the shipped budget"; `FibRecExhibit.lean:467`
`theorem fibRounds_closed (n : Nat) : (fibRounds n : Int) + 9 = 12 *
fibSpec (n + 1)`; the README/ARCHITECTURE/record quote the theorem's
form. The header's inequality is TRUE (DERIVED: checked for n < 38) but
is a looser bound than the equation proved 430 lines below, in the same
file. Fix: quote the theorem's form in the header.

### H-2 (Hygiene): duplication the decision points do not cover

- `drive_after_setup_with` (`ProdEntry.lean:672–712`) is
  `drive_after_setup` (`:332–367`) verbatim modulo the `hlook` rewrite,
  with `prodPostGlobalsWith`/`prodEntryStateWith` twins of
  `prodPostGlobals`/`prodEntryState`; since `prodFile e = prodFileWith []
  e` is `rfl` (`prodFile_eq_with`), the one-procedure forms could be the
  `[]` instances and the 35-line engine-unfolding proof written once.
  Decision (b) (record §9.3) covers the two DRIVER lanes, not this setup
  collapse; the record §4's "`prod_run_eqJ` was left as it is" is the
  only mention.
- `frDec1_pure`/`frDec1_depth`/`frDec2_pure`/`frDec2_depth`/`frSum_pure`/
  `frSum_depth` (`FibRecExhibit.lean:265–301`): six four-line lemmas of
  one shape; one lemma at `PEop op (PEsym s) (PEval v)`/`(PEsym t)` would
  do.
- `frCtx_labels_cases` (`:244–261`) re-runs the two-key case split that
  `frCtx_labeledProcs` (`:228–241`) and `frFile_lookup_inv` already
  perform.
- `fib_rec_certified_production`'s proof is `have h := …; exact h`
  (`:858–885`).
- `wpt_driver_cps`'s call case has the `pure`/`annot` return arms as two
  ~15-line near-copies (the accepted `twp_ret`/`twp_ret_annot` pattern);
  a "deliver a value at a cons stack in `deliveryCost w` rounds" lemma
  would fold them.

None is a merge condition; the code is otherwise clear — the CPS
induction reads as the record describes it, with the budget arithmetic
where a reader expects it.

### H-3 (Note — record cites): column offsets are approximate; substance verified

Evidence, `.cerberus-ws/lean_frontend/generated/Core_reduction.lean:484`
byte offsets by `grep -ob` (0-based): `reduction: PCALL` at 18150 (record
"col 18133"); the PCALL arm's `exec_loc :=  push_exec_loc  psym
th_st.current_loc  th_st.exec_loc` at 18822 (a second, identical write at
16837 belongs to the neighbouring `Eproc` arm — the function-pointer
path, outside `Frag`); `reduction: RETURN` at 2230 (record "col 2228");
`reduction: REMOVE-ANNOT` at 2944 (record "col 2990" is the `Step_tau2`
that follows). Verbatim, the PCALL thread update:

```
stExceptUndef_return  {  {  {  {  {  th_st  with current_proc_opt :=  some  psym                   }  with env :=  proc_env  ::  th_st.env  }  with exec_loc :=  push_exec_loc  psym  th_st.current_loc  th_st.exec_loc  }  with stack0 :=  Stack_cons2  th_st.current_proc_opt  ctx  th_st.stack0  }  with arena :=  expr1  }
```

— the declared return type `bTy` that `call_proc` reads is dropped on the
floor (`(proc_env, expr1)` is all that comes back), so `prodFileWith`'s
`BTy_unit` is inert as the record says. RETURN (verbatim) writes exactly
`current_proc_opt`, `env`, `stack0`, `arena`:

```
Step_tau2  "end of procedure"  tsk  (                 match  th_st.env with  |  [] => (failwithI  "end of proc, found an empty Core_run env" : thread_state) |  _  ::  env' =>  {  {  {                        {  th_st  with current_proc_opt :=  parent_proc_opt  }  with env :=  env'  }  with stack0 :=  sk'  }  with arena :=  apply_ctx  caller_ctx  (Expr  e_annots  (Epure  (mk_value_pe  cval)))  }
```

`Driver.lean:530` (verbatim, the parked thread) is `prodThread` field for
field:

```
{ arena :=  expr1,stack0 :=  Stack_empty /- … -/,errno :=  errno_ptr_val,current_loc :=  (CerbLocation.other  "Driver.drive"),exec_loc :=  (ELoc_normal  [(main_sym, CerbLocation.other  "Driver.drive")]),env  :=  th_st.env,current_proc_opt :=  (some  main_sym)                } : thread_state
```

`drive` is `Driver.lean:518`, `initial_driver_state` `:446`,
`driver_globals` `:473`; `push_exec_loc` `Core_run_aux.lean:380` conses
onto `ELoc_normal xs`; `exec_location` `:57–62`; LemLib `fmapElements`
"newest insert first (seq-descending)" at `LemLib.lean:531–533` and
`fmapLookupBy` reading the bucket head at `:512–517` — all as cited.
Not a defect.

## The questions

### Q1. The production statement and its cone

Statement (machine-printed by `#check`, verbatim):

```
fib_rec_certified_production : ∀ (sup : Nat) (ra : core_run_annotation) (n : Int)
    (nbty xbty ybty sbty zbty : core_base_type),
    0 ≤ n →
      fibRounds n.toNat + 4 ≤ CerbFuel.driverFuel →
        ∀ (fs : CerbFS.FsState) (args : List String),
          ∃ dres dst',
            CerbND.runND (drive fmapEmpty false (prodFileWith (frProcs ra nbty xbty ybty sbty zbty) (frMain ra n)) args)
                  (initial_driver_state sup (prodFileWith (frProcs ra nbty xbty ybty sbty zbty) (frMain ra n)) fs).fst =
                [(Active dres, [], dst')] ∧
              dres.dres_core_value = ivVal (fibSpec n.toNat) ∧
                dres.dres_blocked = false ∧ dres.dres_stdout = "" ∧ dres.dres_stderr = ""
```

Cone (`FibRecExhibit.lean:858–885`): `prod_run_eqJ_procs sup procs e
hlab ψ (fibRounds n.toNat + 2) hdd (by omega) fs args` with `hlab :=
frCtx_labeledProcs` (DERIVED from the shipped registration by `rfl`,
`collect_new_fr`, through `LabeledProcs.of_fibers` + `symAdd_lookup_two`)
and `hdd := wpt_driver_done_procs … (th₀ := prodThread (frMain ra n)) rfl
(frFile_lookup_main …) prodCtl.execLoc frSpecT frLsT … (prodMem₀_launchCoh
0 _) … (hwp)`, `hwp` returning `frCtx_procSpecsT ∗ fr_blockSpecsT ∗
frMain_wpt` under `frPost_to_readout`. `prod_run_eqJ_procs`
(`ProdEntry.lean:722–750`) instantiates `hdd` at `prodEntryStateWith`,
`acc := fmapEmpty`, `fl := CerbFuel.driverFuel`, the four ties by `rfl`
(the thread IS `ctlThread (prodThread e) e [fmapEmpty] prodCtl` —
`prodThread_eq_ctlThread`, `rfl`; layout `prodMem₀`; extern empty; file),
then `driver2_done 99999999 …` (`10^8 = 99999999 + 1`) and
`drive_after_setup_with` (the setup prefix computed through
`driver_globals`, the `main` lookup — `symAdd_lookup (procDecls_symMap
procs)` at the top entry — the errno `allocateObject`/`storeM` on the cold
memory, the park), and `finalize_done`. The final thread's `pfin`/`ℓfin`
are existential in `DriverDoneCtl` because RETURN never restores
`exec_loc` (measured above); `driver2_done`/`finalize_done` read only the
arena, so nothing the production statement concludes depends on them —
the existential hides nothing the statement needs.

Hypotheses. `hn : 0 ≤ n` — satisfiable, needed (the guard `n < 2` at
negative `n` would deliver `n`, not `fib n.toNat`). `hfuel` — satisfiable
for `n ≤ 33` (R-3). Section variables `sup ra n nbty xbty ybty sbty zbty`
are ∀-bound in the theorem (printed above): the statement holds at EVERY
annotation and EVERY base type; a "bad" instantiation makes it stronger,
never vacuous. `fibSpec` (`FibExhibit.lean:57`) is the standard `0, 1,
n+2 ↦ fib n + fib (n+1)` — not degenerate. `frMain`, `frBody` are
closed Core terms whose only free parameters are the annotation and the
base types, inert in the engine (PCALL drops `bTy`, measured; `call_proc`
zips params with values by position).

The file. `prodFileWith [(fib, [(n, nbty)], body)] (fib(n₀))` sets `funs
:= symAdd mainSym (mainDecl e) (symAdd frSym (Proc unknown none BTy_unit
[(frNSym, nbty)] body) fmapEmpty)`, `main := some mainSym`, everything
else `prodFile`'s inert defaults. It is the file the shipped driver runs
in the statement — synthetic (disclosed as such on every surface), but
the driver's setup on it is COMPUTED (`drive_after_setup_with`'s `(by
rfl)` steps), not assumed. Registration order re-measured (probe,
`lake env lean`, verbatim): the committed `rfl` elaborates; the
insertion-order alternative fails —

```
../.audit-scratch/probe_order.lean:10:70: error: Type mismatch
  rfl
has type
  ?m.10 = ?m.10
but is expected to have type
  collect_labeled_continuations_NEW (frFile ra n nbty xbty ybty sbty zbty) =
    symAdd mainSym fmapEmpty (symAdd frSym (frQ zbty) fmapEmpty)
[0, 701]
```

— the last line is `fmapElements funs` keys: `main` (0) enumerated first,
`fib` (701) second, i.e. newest-insert-first, so `main` is folded first
and ends up the INNER entry, exactly as the record §7 says. (The order is
immaterial to trust: `symAdd_lookup_two` resolves either key.)

`#print axioms`, 40 names: the 28 new pins, `prod_run_eqJ_procs`,
`Decomp.frag_plug_call'`, `loop_step_frag` and the eight pre-C4
production statements are all `[propext, Classical.choice, Quot.sound]`;
`BareHead.decomp_call_root` is `[propext]` and `fibRounds_closed` is
`[propext, Quot.sound]` — the two sub-trio names the record and Audit.lean
declare, exactly.

### Q2. `wpt_driver_cps`

`ProdLoop.lean` (the C4 half). `induction k using Nat.strongRecOn`;
the four clauses of `wpt` in the order `wpt_val_eq` / `wpt_jump_eq` /
`wpt_call_eq` / `wpt_zero_step_eq`+`wpt_step_eq`. Decreases: jump `k =
k' + 1 → k'` (`Nat.lt_succ_self`) with the target's `m ≤ k'` by
`wpt_mono_k`; step `k' + 1 → k'`; call `IH m (by omega)` and `IH k' (by
omega)` from `hb : 1 + m + k' ≤ k`. Budget accounting (read, each `omega`
site): call round `hfstep`: `driverDoneCtl_step` gives `(m + (k' + kc)) +
1`, `.mono` to `k + kc` needs `m + k' + kc + 1 ≤ k + kc` ⇐ `hb`; callee IH
at continuation budget `k' + kc`; its continuation `K'` at `krem ≥
deliveryCost w`: pure — one `Step.ret` round, `(k' + kc) + 1 ≤ krem + (k'
+ kc)` ⇐ `1 ≤ krem`; annot — `Step.ret_annot` then `Step.ret`, `(k' + kc)
+ 2 ≤ krem + (k' + kc)` ⇐ `2 ≤ krem`; then `IH k'` on `apply_ctx ctx (pure
v)` at the popped env `ev0 :: evs` (from `hst.cons_inv`, the `SameTail`
invariant — the C3 audit's Plant C point, reused) and control `⟨κ, some
p, ℓ'⟩`, with the OUTER continuation `HK` (its `SameTail (ev0 :: evs)`
premise is exactly what the IH's continuation receives). The Frag/pot
premises for the plugged continuation come from the C2 plug lemmas
(`hd.frag_plug_call`, `hd.pot_plug_call_le`), whose `sseq_sym` case is
the one proof this range changed (Q4). Every round is
`driverDoneCtl_step` = `loop_step_frag` at `ctlThread` with `hstack`/
`hproc`/`hel` by `rfl` and `hcl` the theorem's premise; the current
procedure must be DECLARED (`hq`) so `LabeledProcs` yields the round's
`LabeledAt`, and `loop_step_frag`'s `rs'.labeled = dst.core_run_state0
.labeled` carries the tie to the next round. `wpt_driver_done_procs` is
`wpt_driver_cps` at `κ = []`, `kc = 0`, `ns = nt = 0` with the
PROGRAM-DONE continuation (`driverDoneCtl_value`/`_annot`) under the
allocation-aware launch (`launchResources` at `LaunchCoh`, here
`prodMem₀_launchCoh 0`). Nothing hidden: `DriverDoneCtl`'s conclusion is
`DriverDoneAt`'s with the thread at `ctlThread … ⟨[], pfin, ℓfin⟩` and two
more ties (file, whole-file registration) as PREMISES — strictly more
demanded of the driver state, not less.

The `exec_loc`/`current_loc` tie: `Step.call` writes `push_exec_loc f
M.currentLoc ctl.execLoc`; the engine writes `push_exec_loc psym
th_st.current_loc th_st.exec_loc` (verbatim above); `loop_step_frag` ties
them by `hel`/`hcl`; at the production entry `prodCtl.execLoc =
ELoc_normal [(mainSym, other "Driver.drive")]` and `prodCtx.currentLoc =
other "Driver.drive"` are the parked thread's literal fields
(`Driver.lean:530`, verbatim above), so `hcl` is `rfl` — and Plant C
(below) shows that changing `prodCtx.currentLoc` breaks the production
proof at exactly that `rfl` (`FibRecExhibit.lean:864:40`).

### Q3. `fibRounds`

R-3 has the measurements: `.done` at exactly `fibRounds n + 2` for
n = 0..3 under `driveU`; the shipped loop done at exactly `fibRounds n +
3`. Recurrence values `3, 3, 15, 27, 51, 87, 147, 243` (n = 0..7); closed
form `12·fib(n+1) − 9` agrees at every n checked (DERIVED); `fibRounds 33
= 68434635`, `fibRounds 34 = 110729571` (DERIVED, the record's numbers).
The per-activation reading (guard 1; base PURE + delivery 2; recursive
`(1 + m₁ + 1) + (1 + m₂ + 1) + save 2 + PURE + delivery 2 = m₁ + m₂ + 9`)
matches `frBody_wpt`'s rewrite `fibRounds (n'-1) + fibRounds (n'-2) + 9 =
((m₁ + 2) + ((m₂ + 2) + 4)) + 1` (`:679–680`) and the rule budgets used
(`wpt_call_root` at `k' := 1`, `wpt_seq_sym` split, `saveEntryCost = 2`
at an evaluated initializer, `wpt_pure` at 2). The `+ 4` is `main`'s `+
2` (call round, top-level delivery) inside the certified `k`, plus the
collapse's `k + 2`; the `k + 2` is one more than the loop needs (R-3),
which is slack, not an off-by-one against the theorem.

### Q4. `BareHead.call`

`Soundness.lean:4007–4017`: the new constructor has EXACTLY `Frag.call`'s
operand grammar (`∀ pe ∈ pes, PePure pe`, `peDepth pe ≤ lemDefaultFuel`);
`BareHead.frag` maps it to `Frag.call`, so no shape enters `Frag` that
was not already in it — `Frag`'s constructor set is unchanged (manifest:
23 constructors). The four `BareHead` lemmas gain one arm each:
`not_annot` (`simp`), `redex` (`Redex.call`), `step` (vacuous by
`Step.call_ne_same_ctl`, a pre-existing lemma — `Step.lean:2398` at
`d05f724`), `frag`. No other file case-splits on `BareHead` (grep: the
mentions in Round.lean, API.lean and the exhibits are docstrings and
uses of the lemmas), so no catch-all could have absorbed the new case.
`BareHead.decomp_call_root` (`Adequacy.lean:898–915`) replaces the
now-false `BareHead.no_call` with the exact fact needed: a `BareHead`
decomposes to a call only at `CTX`, proved from `callRedex?_callRedex`;
its consumer `Decomp.frag_plug_call'`'s `sseq_sym` case plugs the bare
value at the root: `Frag.sseq_sym (.val_pure v) (.val_pure v) hf2` —
fail-closed (the only new admission is the plugged `lets x = pure(v) in
e2`, which IS the RETURN's successor, verbatim from the engine's
`Epure (mk_value_pe cval)`). Mirror completeness and the residual arms
(`eval_uncovered`, `run_surplus`) are untouched in code and need no
update: `complete_call` classifies a call at any decomposition and the
binder's beta after the return is `complete_beta_sym` at a bare value
(`BareHead.not_annot` keeps the LETS-ANNOT beta unreachable). Plant D
shows the unpinned sub-trio lemma is bounded by the sweep in practice.

### Q5. EnvLaws (H-2)

`symAdd {β} := @fmapAddBy sym β instBEqOfMapKeyType symCmpK` — genuinely
β-generic; `SymMap`, `symMap_empty`, `SymMap.add`, `symAdd_lookup` are the
old `SymFrame`/`envAdd_lookup` proofs with `value` abstracted (diff read:
the proof bodies are unchanged but for the type); `envAdd_lookup :=
symAdd_lookup h cmp' l k v` and `SymFrame f := SymMap f` — the instance
exactly. `symAdd_lookup_two` is two applications of `symAdd_lookup` +
`rfl` (the smoke's 15-line direct proof deleted). Consumers: the smoke's
`csFile` now built by `symAdd` and its two lookups by `symAdd_lookup_two`;
`prodFileWith` (`procDecls` by `symAdd`, `SymMap` by induction), the
exhibit's file/label lookups, and `frQ` — the engine's `collect_saves`
result is `symAdd frRSym … fmapEmpty` by `rfl` (`collect_saves_frBody`),
which is the measurement behind ARCHITECTURE §7's "the engine's
`ordCompare`-built label maps have [`symOrd`] by definitional unfolding";
the C3 audit's open comparator question (H-2, "not measured") is
thereby closed. `procEnv_single` moved verbatim (same name/type: not in
the census diff).

### Q6. Census

Regenerated at HEAD: `lake env lean scripts/signature_snapshot.lean`
(13.6 s) → 29624 lines, `cmp` against `docs/2026-09-03_c4-signatures-post
.txt`: byte-identical. DERIVED from the two committed files (script):
pre 2897 entries, post 3017; ADDED 123, REMOVED 3 (`BareHead.no_call`,
`csAdd`, `csAdd_lookup_two` — none pinned, checked against the pre
Audit.lean list), CHANGED 3 (`BareHead.casesOn`, `BareHead.rec`,
`BareHead.recOn` — the recursors; no theorem or def type changed). The
123 = 88 exhibit declarations (DERIVED by prefix, 85 `fr*`/`fibRounds*`/
`fibSpec_small`/`_rec`/`ivVal_inj`/`fib_rec_*` + `fr_blockSpecs`,
`fr_blockSpecsT`, `fr_wp_readout`) + 34 lane/entry/law declarations + the
c3-fixes `wps_empty_call_false` — the record §8's list exactly. Source
text of the eight pre-C4 production statements (statement through `:= by`)
at `d05f724` vs `8094738`: `exhibitA_prod` IDENTICAL (10 lines),
`prod_run_eqJ` (15), `counter_loop_certified_production` (19),
`fib_certified_production` (15), `list_reverse_certified_production` (19),
`dispose_list_certified_production` (21), `region_loop_certified_
production` (18), `malloc_list_certified_production` (22); snapshot
entries identical and not in CHANGED. Pins 344 → 372: the gate says 372.

### Q7. Decision points (a)–(c)

(a) The total `driveU` lane not restated through calls: disclosed at
ARCHITECTURE §4 ("left there deliberately at C4 … deleted in the
fuel-lane restatement"), §7 ("the total `driveU` lane at the empty table
(deleted with the lane)"), README "Deliberately not here" and the
limitations row, WALKTHROUGH §7, the Wpt and TotalAdequacy headers, the
record §9.2, DECISIONS. (b) The single-procedure driver lane kept beside
the general one: ARCHITECTURE §4 last sentence and §6, README limitations
row ("so the eight production statements are reached by two routes"),
ProdLoop header, record §9.3, DECISIONS. (c) H-3 parked with its measured
footprint (56 sites, two eta-hacks): record §9.7, DECISIONS; not a docs
surface item (it is internal hygiene). All three honest; the only
claims of coverage are the theorems' (Q1/Q2); no surface says the
`driveU` lane or the collapse lane goes through calls where it does not.
The manifest (regenerated by the auditor's gate, no drift): 23
constructors, 27 rule rows, 0 red, 18 client modules; `FibRecExhibit` on
six rows including both `Frag.call` rows.

### Q8. Docs rewrite

ARCHITECTURE: R-2; otherwise accurate (Q1 list above), the calls-arc
closing record in §7 is a dated one-line-per-slice pointer, not history
in the shop-window sections. README: scope paragraph, the claim ("eight
are THE root-of-trust exports"), the two new exhibit rows (`fib_rec_
certified`/`fr_wp_readout` marked PROVISIONAL; `fib_rec_certified_
production` with every hypothesis named — checked against the printed
statement), the limitations row, the diagram, the modules table, the
records paragraph and the snapshot pointer all consistent with the tree.
WALKTHROUGH: counts updated to eight; the "What a procedure client
supplies" paragraph (inside §3.3, so the §7 cross-reference resolves)
names the theorems that exist. API.lean: the β-generic laws row and the
production-layer note correct; R-1 for its header. Manifest header (H-4):
"client modules" / declared `clientSmokes` list — done as the C3 audit
asked, and the pattern alternative was rightly rejected (record §9.8).
Root README license line: `cmp LICENSE cerberus-heaplang/.lake/packages/
{batteries,Qq,iris}/LICENSE` — identical, identical, identical;
`…/LemLib/LICENSE differ: byte 1, line 1` — as stated.

### Q9. Plants — the log below

### Q10. Records

DECISIONS `:1553–1595` "C4 LANDED": `cac1ab4` is HEAD's parent and the
range `d05f724..cac1ab4` is five commits (`8ec6745 20:53`, `6def5af
21:03`, `2ad8b20 21:16`, `4b9a705 21:31`, `cac1ab4 21:32`; the DECISIONS
commit `8094738 21:36`) ✓; "Pins 344 → 372" ✓; "ADDED 123, REMOVED 3
(none pinned), CHANGED 3" ✓ (Q6); the record path and both snapshot paths
exist ✓; "the 66 pre-C3 linter warnings unchanged" ✓ (below); the quoted
gate tail is line for line the auditor's own verdict lines (below;
DECISIONS strips the `info: CerberusHeapLang/Audit.lean:534:0:` prefix,
as the previous entries do; the notes §11 quote keeps it). Chronology of
the tail: `… C3 LANDED` (line 1473) → `C3 RANGE AUDIT` (1511) → `C4
LANDED` (1553) — chronological, and the C4 entry is last ✓. The record
§11's "lines 1–3 and 3101–3112 of the 3112-line log" is consistent with
the auditor's 3114-line log (two added `date` lines). Record counts
checked: "18 client modules" ✓, "88 declarations" ✓, "28 pins" ✓ (the
Audit.lean diff adds exactly the 28 names listed), "`fibRounds 33 =
68434635`, `fibRounds 34 = 110729571`" ✓.

### Q11. Grumpy read

The logic added here is the right shape and nothing more: `DriverDoneCtl`
is `DriverDoneAt` with the control made live and two ties added;
`wpt_driver_cps` is `wpt_sound_cps` with the TWP replaced by the pure
delivery fact and the one bookkeeping device the pure conclusion forces
(the additive continuation budget `kc`), the record explains why (§3(i))
and the arithmetic is transparent; `LabeledProcs.of_fibers` makes the
whole-file tie a two-line theorem; `prodFileWith` generalises `prodFile`
with the old one a `rfl` instance; the exhibit proves fib's body ONCE
under the table with no induction (the budget inequality is `Nat.le_refl`
at each call — Hoare's rule doing its job). Weak points, all minor: the
duplication in H-2; the `+ 4` presented as a sum of exact parts (R-3);
two closed forms in one file (H-1). Linter: the auditor's gate log has
590 `warning:` lines, 524 in the semantics dependency and 66 in
`CerberusHeapLang/*` — DERIVED by file: Potential 50, TotalAdequacy 4,
Round 3, Heap 2, Rules 2, EnvLaws 2, ProdLoopExhibit 1, StructExhibit 1,
TreeRotExhibit 1 — the same nine files and counts as the C3 audit's H-1;
ZERO warnings in `FibRecExhibit.lean`, `ProdLoop.lean`, `ProdEntry.lean`,
`Adequacy.lean`, `Soundness.lean` or `CallSmoke.lean`. No new warning in
the range. Range-added Lean lines contain no `sorry`, `native_decide`,
`bv_decide`, `ofReduce*`, `maxHeartbeats` or `maxRecDepth` (grep); the
exhibit's `decide +kernel` uses are the package idiom.

## The FULL gate (auditor's run)

`CERB_MEM_MAX=40G scripts/test_unit.sh` from the audit copy's root,
`21:38:33 → 21:39:01` (all modules replayed from the primed `.lake`),
log 3114 lines; lines 1–5 and 3102–3114 verbatim (line 5 and 3108 are
the `capped` env banner; the `GATE-EXIT` line and the two times are the
invoking shell's):

```
21:38:33
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
cerberus-lean-proj env: switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_opam, git redirects active
info: CerberusHeapLang/Audit.lean:534:0: CerberusHeapLang export pins: 372 trio-exact
info: CerberusHeapLang/Audit.lean:534:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (3456 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:534:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (5256 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (456 jobs).
ok: cerberus-heaplang build green
== speedbump: capability manifest (regenerate; red on a red row or drift) ==
cerberus-lean-proj env: switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_opam, git redirects active
ok: capability manifest regenerated, no drift
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — no core module imports an exhibit/example/production module
ALL GATES GREEN
GATE-EXIT=0
21:39:01
```

## Plant-test log (verbatim)

Runner: `CERB_MEM_MAX=40G ./scripts/test_unit.sh --fast` (gates 1–2 = the
trust base) after each edit, then `git checkout --
cerberus-heaplang/CerberusHeapLang` and the same runner. The auditor's
script filtered the runner's output to lines matching
`error|FAIL|GATE|GREEN|ok:|export pin|sweep|sorry|Build` (so the
multi-line continuation of the `export pin FAILED` message — the axiom
list and the `expected EXACTLY [...]` line, as quoted in full by the C3
audit — is cut after its first line here); `git diff --stat` before each
planted run confirms the edit landed. Times are `date +%T`.

**Plant A — `sorry` in an internal detail of `wpt_driver_cps`'s cone.**
`ProdLoop.lean`, `DriverDoneCtl.mono`: `(by omega)` → `(sorry)`
(consumed by the call case's `.mono` in `wpt_driver_cps`).

```
--- A-planted gate START 21:48:13
 cerberus-heaplang/CerberusHeapLang/ProdLoop.lean | 2 +-
 1 file changed, 1 insertion(+), 1 deletion(-)
ok: no banned proof-method references
error: CerberusHeapLang/Audit.lean:534:0: CerberusHeapLang export pin FAILED: CerberusHeapLang.wpt_driver_cps depends on axioms [Classical.choice,
error: Lean exited with code 1
error: build failed
FAIL: cerberus-heaplang build red
GATE FAILURE
GATE-EXIT=1
--- A-planted gate END 21:48:34
reverted: ?? .audit-scratch/ 
--- A-reverted gate START 21:48:34
ok: no banned proof-method references
info: CerberusHeapLang/Audit.lean:534:0: CerberusHeapLang export pins: 372 trio-exact
info: CerberusHeapLang/Audit.lean:534:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (3456 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:534:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (5256 constants of every kind swept, internal details included — count informational, environment-dependent)
ok: cerberus-heaplang build green
FAST-GATE GREEN (gates 1-2 only — not a claim-point result; say fast-gate in the commit)
GATE-EXIT=0
--- A-reverted gate END 21:49:16
```

**Plant B — `fibRounds` weakened by one.** `FibRecExhibit.lean`: `9 → 8`
in the definition's `n + 2` arm, in `fibRounds_add_two`, in
`fibRounds_rec`, and in `frBody_wpt`'s `show … + 9 = …` (so the weaker
budget is carried consistently into the total proof).

```
--- B-planted gate START 21:49:17
 cerberus-heaplang/CerberusHeapLang/FibRecExhibit.lean | 8 ++++----
 1 file changed, 4 insertions(+), 4 deletions(-)
ok: no banned proof-method references
error: CerberusHeapLang/FibRecExhibit.lean:477:6: omega could not prove the goal:
error: CerberusHeapLang/FibRecExhibit.lean:680:85: omega could not prove the goal:
error: Lean exited with code 1
error: build failed
FAIL: cerberus-heaplang build red
GATE FAILURE
GATE-EXIT=1
--- B-planted gate END 21:49:30
reverted: ?? .audit-scratch/ 
--- B-reverted gate START 21:49:30
ok: no banned proof-method references
info: CerberusHeapLang/Audit.lean:534:0: CerberusHeapLang export pins: 372 trio-exact
info: CerberusHeapLang/Audit.lean:534:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (3456 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:534:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (5256 constants of every kind swept, internal details included — count informational, environment-dependent)
ok: cerberus-heaplang build green
FAST-GATE GREEN (gates 1-2 only — not a claim-point result; say fast-gate in the commit)
GATE-EXIT=0
--- B-reverted gate END 21:49:43
```

(`:680:85` is `frBody_wpt`'s budget split — the TOTAL body proof, on
which `frCtx_procSpecsT` → `fib_rec_certified_production` depends, fails
at exactly the arithmetic that spends the nine rounds; `:477:6` is the
derived `fibRounds_closed`. The partial lane, `fib_rec_certified`, is
untouched by the budget — as it should be.)

**Plant C — the `current_loc` tie broken at the production context.**
`ProdEntry.lean`, `prodCtx`: `currentLoc := CerbLocation.other
"Driver.drive"` → `currentLoc := CerbLocation.unknown`.

```
--- C-planted gate START 21:49:43
 cerberus-heaplang/CerberusHeapLang/ProdEntry.lean | 2 +-
 1 file changed, 1 insertion(+), 1 deletion(-)
ok: no banned proof-method references
error: CerberusHeapLang/FibRecExhibit.lean:864:40: Application type mismatch: The argument
error: Lean exited with code 1
error: build failed
FAIL: cerberus-heaplang build red
GATE FAILURE
GATE-EXIT=1
--- C-planted gate END 21:50:19
reverted: ?? .audit-scratch/ 
--- C-reverted gate START 21:50:19
ok: no banned proof-method references
info: CerberusHeapLang/Audit.lean:534:0: CerberusHeapLang export pins: 372 trio-exact
info: CerberusHeapLang/Audit.lean:534:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (3456 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:534:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (5256 constants of every kind swept, internal details included — count informational, environment-dependent)
ok: cerberus-heaplang build green
FAST-GATE GREEN (gates 1-2 only — not a claim-point result; say fast-gate in the commit)
GATE-EXIT=0
--- C-reverted gate END 21:50:47
```

(`FibRecExhibit.lean:864:40` is `(th₀ := prodThread (frMain ra n)) rfl` —
the `hcl : th₀.current_loc = M₀.currentLoc` argument of
`wpt_driver_done_procs` in the production proof: the tie is exactly what
the PCALL round needs, and nothing else in the file cares.)

**Plant D — `sorry` inside `BareHead.decomp_call_root` (unpinned,
sub-trio).** `Adequacy.lean`, the `call` arm: `exact (Prod.mk.inj
(Option.some.inj hc)).1.symm` → `exact sorry`.

```
--- D-planted gate START 21:50:47
 cerberus-heaplang/CerberusHeapLang/Adequacy.lean | 2 +-
 1 file changed, 1 insertion(+), 1 deletion(-)
ok: no banned proof-method references
error: CerberusHeapLang/Audit.lean:534:0: CerberusHeapLang export pin FAILED: CerberusHeapLang.exhibitA_engine depends on axioms [Classical.choice,
error: Lean exited with code 1
error: build failed
FAIL: cerberus-heaplang build red
GATE FAILURE
GATE-EXIT=1
--- D-planted gate END 21:51:19
reverted: ?? .audit-scratch/ 
--- D-reverted gate START 21:51:19
ok: no banned proof-method references
info: CerberusHeapLang/Audit.lean:534:0: CerberusHeapLang export pins: 372 trio-exact
info: CerberusHeapLang/Audit.lean:534:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (3456 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:534:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (5256 constants of every kind swept, internal details included — count informational, environment-dependent)
ok: cerberus-heaplang build green
FAST-GATE GREEN (gates 1-2 only — not a claim-point result; say fast-gate in the commit)
GATE-EXIT=0
--- D-reverted gate END 21:51:54
===== ALL PLANTS DONE 21:51:54
?? .audit-scratch/
```

(The first pin the sweep reports is `exhibitA_engine` — the unpinned
`decomp_call_root` sits in the cone of `Decomp.frag_plug_call'` →
`drive_classifyU_aux` → `engine_adequacyU` → every `driveU` export, and
of `wpt_driver_cps`; "bounded by the sweep" holds in practice.) `git
status --short` after the chain: only the untracked `.audit-scratch/`
(deleted after this report was written) and this file.

## Not checked / limits

- The plant-run error messages were filtered to their first line by the
  auditor's script (stated above); the full `expected EXACTLY [...]`
  continuation was not re-captured.
- The pre snapshot was not regenerated at `d05f724` (no build of that
  revision in the audit copy); the C3 audit verified the C3 post at
  `ebd4076`, and `ebd4076..d05f724` is the one-theorem c3-fixes commit
  whose entry is counted in ADDED — accepted on that argument.
- `driveU` and the shipped loop were executed at n = 0..3 only; the
  general accounting is the theorem's.
- `iloeb`/iris-lean internals were not read (no Löb is used in this
  range's additions; the strong induction is Lean's `Nat.strongRecOn`).
- The C3-era statements (`wpt_sound_cps`, `procSpecsT_intro`, the plug
  lemmas' non-`sseq_sym` cases) were not re-audited beyond their use
  here; the C3 audit covers them.
- The build cost the record claims (§10) was not reproduced; on this box
  the primed replay took 28 s and the largest plant cascade (Adequacy →
  Audit) 32 s.
- Reachability of the engine's `Stack_cons` panic, the residual
  `OpenRound` arms and the function-pointer `Eproc` arm (the second
  `exec_loc` write at offset 16837) are outside this range.
