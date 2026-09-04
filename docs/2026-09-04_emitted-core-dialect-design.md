# E0 — the emitted-Core dialect: measurement and per-construct design

E0 design-measurement agent [AGENT], 2026-09-04. Read-only: nothing built,
no `.lean` touched. Branch `dialect-e0` at main `2c84134`; the pinned
semantics workspace `.cerberus-ws` is cerberus-lean `f95ef8d9c`
(`scripts/semantics-pin.env`). Trigger and scope: DECISIONS 2026-09-04
"THE EMITTED-CORE DIALECT ARC (E) — APPROVED" (E0 = "engine semantics of
each construct at the pin, the sequential driver's `unseq`/`nd` behaviour,
the evaluator's std.core unfolding, loaded-value shapes; slice sizes").
The corpus (§A) is committed under `docs/corpus-e0/` and is the arc's
acceptance material. Every claim below cites a file:line read in this
pass; every count is DERIVED with its command. Cites into the `.lem`
model are `frontend/model/<f>.lem:<n>` under `.cerberus-ws/`; cites into
the generated Lean are `lean_frontend/generated/<F>.lean:<n>` (the lem
backend emits one definition per line, so a generated cite names the
definition, the `.lem` cite names the arm). Decisions here are [AGENT];
the operator's questions are §D.

## 0. Headline findings (one line each)

1. **The referent dialect is the RAW elaborated Core, not the
   sequentialised one.** The pinned Lean pipeline runs desugar →
   `annotate_program` → `translate` → `link` → `convert_file` → `drive`
   (`lean_frontend/Main.lean:499`–`:597`, `:725`–`:880`): no
   `Core_sequentialise`, no `Core_rewrite`. The OCaml oracle's `--exec`
   default is the same (`sequentialise_core` is a flag, default off,
   `backend/driver/main.ml:491`); the one pass `core_passes` always
   applies, `Core_indet.hackish_order`, is the identity
   (`core_indet.lem:502`–`:504`). So `unseq`, `bound`, tuple patterns and
   the negative-action protocol are all on the executed path. The
   `--sequentialise` emission (also committed, `*.seq.core`) has ZERO
   `unseq` and would remove slice E4 — but a theorem over it is not about
   the program the pipeline runs (§D Q1).
2. **Three load-bearing constructs are missing from the trigger note's
   list**: (a) the NEGATIVE-ACTION protocol `neg(store(…))` — every C
   assignment *statement* elaborates to it (60 occurrences in the corpus;
   t1 alone has none because its stores are declaration initialisers);
   its engine round draws a fresh symbol and a fresh exclusion id from the
   RUN STATE (`core_reduction.lem:1298`–`:1301`), which the mirror's
   `MachineCtx.runState` holds immutable — the same class of change as
   `current_loc` for annotations; (b) `seq_rmw` — postfix `i++`
   (`core_reduction.lem:1228`; driver `SeqRMWRequest2`, `driver.lem:710`),
   t2's `for` loop has one; (c) `memop(PtrValidForDeref, …)` — every
   `*p` dereference (t3, t8; driver `driver.lem:781`, engine
   `CerbMem.lean:2242`), a memory READ of liveness and alignment.
   Also new: `Elet` (pure let at expression level, in every C call),
   `Ecase` at a non-value scrutinee, and general (tuple / `Specified`)
   patterns at `let weak`/`let strong`.
3. **`__conv_int__`, `catch_exceptional_condition_*` and `wrapI` are NOT
   std.core calls**: they are the Core AST constructors `PEconv_int`,
   `PEcatch_exceptional_condition`, `PEwrapI` (`core.lem:243`–`:245`),
   printed with those names (`pp_core.ml:422`–`:424`, `:503`), evaluated
   by the engine's own `mk_conv_int`/`mk_call_catch_exceptional_condition`/
   `mk_wrapI` (`core_eval.lem:29`–`:117`; `Core_eval.lean:76`–`:105`) over
   `CerbMem` integer ops — no unfolding. The genuine std.core calls
   (`PEcall`) in the corpus are `conv_loaded_int`, `conv_int`,
   `params_length`, `params_nth` (`std.core:25`, `:61`, `:108`–`:129`);
   these unfold through `call_function` on `file.stdlib`
   (`core_eval.lem:120`–`:165`), so the statement's file object must carry
   the parsed std.core (the demo's `prodFile` has `stdlib := fmapEmpty`,
   `ProdEntry.lean:125`).
4. **`unseq` in the sequential driver is deterministic and forks only
   when a component is an unsequenced sibling of a C call**: the step
   list has one entry per reducible component, LAST component first
   (`get_ctx_unseq_aux` prepends, `core_reduction.lem:590`–`:601`), and
   the per-thread loop takes the first ADVANCEABLE one
   (`find_can_advance`, `driver.lem:1049`, `:1075`). Measured on the
   oracle (`--exec --mode=exhaustive --batch`): t1–t8 and t10 deliver ONE
   execution each; t9 (`n * fact(n-1)`) delivers 16 executions, all
   `Specified(120)`, because the load of `n` sits beside a `ccall` and is
   not advanceable (`is_unseq_with_ccall`, `core_reduction.lem:501`–`:519`;
   `can_advance`, `driver.lem:907`–`:918`), so the scheduler `ND.pick`s
   among two steps (`driver.lem:1288`). The singleton closed forms
   survive every corpus program but t9; t9 needs the outcome-list form.
5. **`nd` needs no mirror rule for these programs**: the elaborator emits
   `nd(pure(True), pure(False))` ONLY in the `Unspecified(_)` alternative
   of a condition's `case` (`translation.lem:3823`, `:3858`); with a
   specified scalar that alternative is never selected. `Frag.case_value`
   constrains only the SELECTED branch (`Soundness.lean:4296`), so the
   `nd` alternative is admitted syntactically. `End` reduces to
   `Step_nd2` and an `ND.pick` fork (`core_reduction.lem:447`, `:1474`;
   `driver.lem:1041`) — an OUT-OF-SCOPE row, not a slice.
6. **`bound` is two tau rules plus a context**: `Cbound` in `get_ctx`
   (`core_reduction.lem:563`–`:568`), REMOVE-BOUND at a bare or annotated
   value — the annotated form DROPS the dynamic annotations
   (`:1214`–`:1226`); `is_unseq_with_ccall` resets to false at a `Cbound`
   (`:514`) and `break_at_bound_and_sseq` uses it as the negative
   action's boundary (`:868`–`:912`). Size S once annotations are in.
7. **Annotations on the execution path are read at exactly two places**:
   `get_loc` (first `Aloc`, everything else skipped, `annot.lem:101`–
   `:133`) in `step_ctx`'s general arm (`core_reduction.lem:1155`–`:1164`,
   guarded by `is_library_location`), and `get_with_address` (an `Acerb`
   attribute, `cerb_attributes.lem:100`) in `step_action`'s Create arm
   (`core_reduction.lem:648`). The elaborator puts `Aloc`+`Astmt`(+`Aattrs`
   if any) on every statement node (`translation.lem:3701`), `Aloc`+`Aexpr`
   on expression nodes (`:1503`), `Astd "§6.5#2"` on every `bound`
   (`:3556`); the printer shows `Aloc`/`Astd` only (`pp_core.ml:557`–
   `:602`: `Astmt`/`Aexpr`/`Alabel`/`Acerb` print nothing, `Aattrs` only
   at debug > 3) — so the `.annot.core` files under-report the lists.
8. **Loaded values are half in already**: the mirror's `Step.load`
   delivers `(valueFromMemValue mval).2`, i.e. `Vloaded (LVspecified …)`
   or `Vloaded (LVunspecified ty)` (`Step.lean:1489`–`:1500`;
   `core_aux.lem:126`–`:146`), and `Step.store`'s value premise is the
   generic `memValueFromValue` (`Step.lean:1476`), which accepts
   `Vloaded` of either shape (`core_aux.lem:164`–`:181`). What is missing
   is the pure side: the ctors `Cspecified`/`Cunspecified` and `PEcase`
   over `Specified` patterns in the evaluator, the tuple/`Specified`
   patterns at binders, and `conv_loaded_int`.
9. **A direct C call is a PROTOCOL, not one node** (t2, t3, t9, t10):
   `pure(Specified(Cfunction(f)))`, `cfunction(p)` (`PEcfunction`, reads
   `file.funinfo`, `core_eval.lem:899`–`:915`), `params_length`/
   `params_nth` (std.core), `are_compatible` (`PEare_compatible`), `Elet`,
   an argument CELL per parameter (`create`/`store`, killed after the
   call under `unseq(kill, kill)`), then `ccall` — `Step_ccall2`, not
   advanceable, one `driver2` round (`driver.lem:1342`–`:1347`). The
   callee's parameters are POINTERS to those cells (`proc add (a: pointer,
   b: pointer)`). For a `PVfunction` pointer the callee is resolved
   directly, without `funptrmap` (`core_reduction.lem:1370`–`:1374`).
10. **KOI B4 (`tagDefs = ∅`) blocks t7 independently of the dialect**:
    `member_shift` and `Ivalignof('struct P')` read the file's `tagDefs`,
    and the production statements run `drive fmapEmpty …`. Not an E slice
    (§D Q6).

## A. The corpus

Ten libc-free programs under `docs/corpus-e0/`, spanning the demo's
covered features and nothing beyond: `t1.c` (locals + arithmetic),
`t2.c` (helper call in a `for` loop) — the two from the measurement note,
verbatim — `t3_ptrarg.c` (`void set(int *p) { *p = 4; }`), `t4_while.c`
(`while (i < 5 && s < 7)`), `t5_ifelse.c`, `t6_switch.c`, `t7_struct.c`,
`t8_array.c` (`int a[4]`), `t9_fact.c` (recursive factorial),
`t10_evenodd.c` (mutual recursion). Note `t4` uses `i = i + 1` on
purpose (no `seq_rmw`); `t2`'s `i++` is the corpus's one `seq_rmw`.

Emission (verbatim outputs in the files; the `env:` line goes to stderr):

```
cd /home/dev/projects/cerberus-lean-proj
scripts/ce cerberus-lean/_build/default/backend/driver/main.exe --nolibc --pp=core <t>.c                       > <t>.core        # THE ACCEPTANCE MATERIAL
scripts/ce cerberus-lean/_build/default/backend/driver/main.exe --nolibc --pp=core --pp_flags=annot,loc <t>.c  > <t>.annot.core  # Aloc/Astd shown
scripts/ce cerberus-lean/_build/default/backend/driver/main.exe --nolibc --sequentialise --pp=core <t>.c       > <t>.seq.core    # informational (§D Q1)
scripts/ce cerberus-lean/_build/default/backend/driver/main.exe --nolibc --sequentialise --rewrite --pp=core <t>.c > <t>.seqrw.core
```

Execution on the oracle, exhaustive (DERIVED; command
`… --nolibc --exec --mode=exhaustive --batch <t>.c`):

| program | executions | value |
|---|---|---|
| t1 | 1 | `Specified(4)` |
| t2 | 1 | `Specified(3)` |
| t3_ptrarg | 1 | `Specified(4)` |
| t4_while | 1 | `Specified(10)` |
| t5_ifelse | 1 | `Specified(1)` |
| t6_switch | 1 | `Specified(20)` |
| t7_struct | 1 | `Specified(3)` |
| t8_array | 1 | `Specified(6)` |
| t9_fact | **16** (`grep -c '^EXECUTION'`), all `Defined {value: "Specified(120)" …}` (`sort | uniq -c`) | `Specified(120)` |
| t10_evenodd | 1 | `Specified(1)` |

t9 with `--sequentialise`: 1 execution, `Specified(120)`.

**Construct tally over the raw `.core` files** (DERIVED:
`grep -o '<token>' <t>.core | wc -l` per cell; token in the header).

| program | `bound(` | `unseq(` | `let weak` | `let strong` | `save ` | `run ` | `if ` | `case ` | `nd(` | `neg(` | `seq_rmw(` | `ccall(` | `create(` | `store(` | `load(` | `kill(` | `memop(` |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| t1 | 3 | 1 | 3 | 5 | 1 | 1 | 0 | 1 | 3 | 0 | 0 | 0 | 2 | 2 | 2 | 4 | 0 |
| t2 | 7 | 6 | 16 | 16 | 6 | 3 | 8 | 5 | 8 | 1 | 1 | 1 | 4 | 5 | 6 | 5 | 0 |
| t3_ptrarg | 4 | 2 | 9 | 8 | 2 | 1 | 4 | 1 | 4 | 1 | 0 | 1 | 2 | 3 | 2 | 3 | 1 |
| t4_while | 6 | 10 | 18 | 12 | 4 | 2 | 9 | 10 | 7 | 2 | 0 | 0 | 2 | 4 | 6 | 4 | 0 |
| t5_ifelse | 5 | 4 | 8 | 8 | 1 | 1 | 4 | 3 | 6 | 2 | 0 | 0 | 2 | 4 | 2 | 4 | 0 |
| t6_switch | 7 | 3 | 8 | 10 | 5 | 8 | 2 | 1 | 7 | 3 | 0 | 0 | 2 | 5 | 2 | 4 | 0 |
| t7_struct | 3 | 3 | 7 | 8 | 1 | 1 | 0 | 1 | 3 | 2 | 0 | 0 | 1 | 3 | 2 | 2 | 0 |
| t8_array | 5 | 11 | 35 | 6 | 1 | 1 | 6 | 13 | 5 | 4 | 0 | 0 | 1 | 5 | 2 | 2 | 6 |
| t9_fact | 4 | 6 | 11 | 13 | 2 | 3 | 10 | 5 | 5 | 0 | 0 | 2 | 2 | 2 | 3 | 2 | 0 |
| t10_evenodd | 7 | 9 | 16 | 21 | 3 | 5 | 17 | 8 | 9 | 0 | 0 | 3 | 3 | 3 | 4 | 3 | 0 |

(`nd(` counts include the literal substring inside `bound(` — the true
`nd(…)` node count is the `Unspecified` alternative count: one per
`if`/`while`/`for` condition — t1 has none; the raw grep is left as run.
`if ` includes pure `if … then` inside `pure(…)`.)

| program | `conv_loaded_int(` | `conv_int(` | `__conv_int__(` | `catch_exceptional_condition_` | `params_length(` | `params_nth(` | `are_compatible` | `cfunction(` | `Cfunction(` | `Specified(` | `Unspecified(` | `undef(` | `Ivalignof(` | `array_shift(` | `member_shift(` | `not(` | `\/` |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| t1 | 3 | 0 | 2 | 1 | 0 | 0 | 0 | 0 | 0 | 6 | 0 | 1 | 2 | 0 | 0 | 0 | 0 |
| t2 | 8 | 6 | 2 | 2 | 1 | 2 | 3 | 1 | 1 | 20 | 5 | 6 | 4 | 0 | 0 | 5 | 1 |
| t3_ptrarg | 4 | 0 | 0 | 0 | 1 | 1 | 2 | 1 | 1 | 6 | 1 | 5 | 2 | 0 | 0 | 3 | 1 |
| t4_while | 9 | 12 | 4 | 2 | 0 | 0 | 0 | 0 | 0 | 43 | 8 | 3 | 2 | 0 | 0 | 2 | 0 |
| t5_ifelse | 6 | 4 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 15 | 4 | 0 | 2 | 0 | 0 | 1 | 0 |
| t6_switch | 9 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 7 | 1 | 1 | 2 | 0 | 0 | 0 | 0 |
| t7_struct | 5 | 0 | 2 | 1 | 0 | 0 | 0 | 0 | 0 | 6 | 1 | 1 | 1 | 0 | 4 | 0 | 0 |
| t8_array | 9 | 0 | 2 | 1 | 0 | 0 | 0 | 0 | 0 | 44 | 7 | 19 | 1 | 12 | 0 | 0 | 0 |
| t9_fact | 5 | 8 | 0 | 2 | 2 | 2 | 4 | 2 | 2 | 23 | 3 | 9 | 2 | 0 | 0 | 7 | 2 |
| t10_evenodd | 8 | 12 | 0 | 2 | 3 | 3 | 6 | 3 | 3 | 37 | 6 | 13 | 3 | 0 | 0 | 11 | 3 |

`catch_exceptional_condition_` is `_add` (28 over the corpus), `_sub`
(12), `_mul` (4) — the `iop` of `PEcatch_exceptional_condition`. `wrapI`
and `is_representable` do not occur (all corpus arithmetic is `signed
int`; `wrapI` is the unsigned path of `conv_int`, `std.core:48`–`:49`).

**`unseq` arity** (DERIVED: a paren-depth scan counting top-level commas
inside each `unseq(`…`)`, nested occurrences included): 54 two-way, 1
three-way (t2's two-argument call: the `(fp, cfunction(fp))` tuple plus
two arguments). Corpus-wide: 55 `unseq`.

**Distinct callee names in pure position** (DERIVED:
`cat t*.core | grep -o '[A-Za-z_][A-Za-z_0-9]*(' | sort | uniq -c`,
keywords/actions removed): std.core `fun`s — `conv_loaded_int` (264),
`conv_int` (172), `params_nth` (32), `params_length` (28); AST
constructors printed as calls — `__conv_int__` (48),
`catch_exceptional_condition_{add,sub,mul}` (44), `cfunction` (28),
`array_shift` (48), `member_shift` (16), `not` (116), `Ivalignof` (84);
ctor applications `Specified` (842), `Unspecified` (144), `Cfunction`
(35); `undef` (232). No `impl` (`<…>`) constant occurs in any body.

**Loaded/undef shapes**: `Specified(n)`, `Specified(Cfunction(f))`,
`Specified(array_shift(p, ty, i))`, `Unspecified(ty)` — the last as a
STORE operand for every uninitialised local and aggregate
(`store('signed int', r, Unspecified('signed int'))` t5;
`store('struct P', p, Unspecified('struct P'))` t7;
`store('signed int[4]', a, Unspecified('signed int[4]'))` t8). UB arms
(DERIVED, `grep -o '<<[A-Za-z0-9_]*>>' | sort | uniq -c`): UB036 (44),
UB038 (28), UB041 (60), UB043 (56), UB088 (16 — the `save ret` default
initializer of every non-`main` procedure), UB_CERB004 unspecified
conditional (4) / pointer add (24). None is on the specified path of any
corpus run (§A table: all runs `Defined`).

**Patterns at binders**: wildcard (`let strong _: loaded integer`,
`let weak _: unit`, `let strong _: (unit,unit)`), plain symbol, pairs of
symbols (`let weak (a: loaded integer, b: loaded integer)`), and the
call protocol's nested tuple
`((fp: loaded pointer, (ret: ctype, params: [ctype], variadic: boolean, proto: boolean)), arg…)`.
`case` patterns: `(Specified(a: integer), Specified(b: integer))` with a
typed wildcard alternative `_: (loaded integer, loaded integer)`;
`Specified(a: integer)` / `Unspecified(_: ctype)`; the pointer form
`(Specified(a: pointer), Specified(b: integer))` (t8).

**`create`/`store`/`load`/`kill` operand shapes**: `create(Ivalignof(ty),
ty)` always (ctor operand, never a literal); `store(ty, x, conv_loaded_int(ty, a))`
(a `PEcall` operand) at declarations, `store(ty, p, Unspecified(ty))`,
`store('signed int*', p, a)` (a `loaded pointer` symbol); `load(ty, p)` at
a symbol bound by `let weak p: pointer = pure(x) in …`; `kill(ty, x)` at
a symbol (`Static0 ty`).

**Annotations seen** (DERIVED over `.annot.core`: `grep -o '{-# [^<#]*'`):
`Aloc` on 333 nodes (statement and expression nodes), `Astd` — `§6.5#2`
on every `bound` (51 of the printed `§` comments), `§6.5.16`/`§6.5.16.1`
(assignment), `§6.5.2.2` (calls), `§6.5.6`, `§6.5.3.2`, `§6.3.2.1`,
`§6.5.8`. Not visible: `Astmt`/`Aexpr` (added by the elaborator,
`translation.lem:3701`, `:1503`; never printed), `Aattrs` (none: no C2X
attributes in the corpus), `Abmc`/`Auid`/`Amarker`/`Alabel` (not
expected; not observable here). The authoritative annotation lists are
the Lean AST's; the slice reads them there.

## B. Engine semantics at the pin, per construct

Conventions: `one_step` (`core_reduction.lem:284`; `Core_reduction.lean:353`
as `one_step0`), `step_action` (`:638`; `Core_reduction.lean:424`),
`step_ctx` (`:1091`; `Core_reduction.lean:484`), `get_ctx` (`:524`;
`Core_reduction.lean:381`, fuelled), the driver's `can_advance`/
`advance_step`/`drive_nonmemory_steps_aux2`/`new_drive_core_threads`/
`process_core_step2`/`driver2` (`driver.lem:907`/`:940`/`:1062`/`:1275`/
`:1321`/`:1369`; `Driver.lean:310`/`:335`/`:351`/`:355`/`:377`/`:386`).
`step_ctx` maps `one_step`-or-arm over `get_ctx th_st.arena`
(`core_reduction.lem:1101`, `:1489`): ONE `core_step2` PER CONTEXT.

### B.1 `Ebound`

- Context: `get_ctx (Ebound e)` = `[(CTX, expr)]` if `e` is irreducible,
  else `Cbound annot ctx` over `get_ctx e` (`core_reduction.lem:563`–`:568`;
  `apply_ctx (Cbound annot ctx') e = Expr annot (Ebound …)`, `:618`–`:619`).
- Reduction (in `step_ctx`'s general arm, so `get_loc` fires first):
  `bound({A}v) → v` and `bound(v) → v`, both `Step_tau2 "CTX, Ebound …"
  TSK_Misc` with `wrap_expr expr'` (`:1214`–`:1226`, "reduction:
  REMOVE-BOUND"). The dynamic annotations `{A}` are DISCARDED — no
  `Eannot` residue passes a `bound`. Driver: `Step_tau2` is advanceable
  (`driver.lem:912`–`:913`) and `advance_step` writes the thread, ticks
  `dr_step_counter`, `NOWAKEUP` (`:960`–`:973`).
- Interactions: `is_unseq_with_ccall_aux` RESETS its accumulator at a
  `Cbound` (`:514`) — a `bound` is a full-expression boundary for the
  ccall/unseq rule; `break_at_bound_and_sseq` (`:868`–`:912`) locates the
  innermost `Cbound` above a negative action (B.9). `has_ccall` descends
  through `Ebound` (`:483`). `esize`/`pot` price it at the leaf default
  (`Soundness.lean:289`–`:296`: `| _ => 1`; `Potential.lean:43`–`:51`: `2`).
- Inert for our purposes: yes — it never changes env, memory or control.

### B.2 `Eunseq` in the sequential driver

- Context: if all components are irreducible, `[(CTX, expr)]`; else
  `get_ctx_unseq_aux annot [] [] es` (`:544`–`:548`), which for each
  REDUCIBLE component `e` maps `get_ctx e` under `Cunseq annot es1 ctx es2`
  and PREPENDS (`zs ++ acc`, `:590`–`:601`). Hence the step list is
  ordered LAST reducible component first, one entry per component's
  context (a nested `unseq` contributes its own components).
- At all-values: `one_step_unseq_aux` collects the values and combines
  the dynamic annotations of annotated components (`:258`–`:274`), racing
  by `do_race` (`:215`–`:242`: two `DA_neg`/`DA_pos` with overlapping
  footprints, unless one's id is in the other's exclusion list) →
  UNSEQUENCED-RACE (`Step_with_runstate2 (RSK_eval …)` returning
  `E.undef … UB035`, `:1480`–`:1484`) or `TAU "Eunseq" env (Expr annots
  (Eannot fps (tuple)))` (`:375`–`:386`) — note the EMPTY `Eannot []`
  when no component was annotated.
- Driver: `drive_nonmemory_steps_aux2` computes `step_ctx` and takes
  `find_can_advance steps` — the FIRST advanceable step (`driver.lem:1049`
  –`:1057`, `:1075`–`:1089`); the whole list is recomputed next round.
  Advanceability (`:907`–`:931`): `Step_tau2`, `Step_with_runstate2`,
  `Step_nd2` yes; `Step_action_request2`/`Step_memop_request2` iff NOT
  `is_unseq_with_ccall`; `Step_ccall2`, `Step_done2`, `Step_blocked2`,
  `Step_fs2` no. When nothing is advanceable the loop returns the list to
  `new_drive_core_threads`, which `ND.pick`s one step (`:1288`;
  `Driver.lean:359`, `nd_pick`) — a FORK iff the list has ≥ 2 entries —
  and `process_core_step2` performs it (`:1321`–`:1364`; action requests
  via `perform_action_request2`, `:747`).
- Consequence for the closed statements: for `unseq` whose components
  are pure evaluations and actions with `is_unseq_with_ccall = false`
  (every corpus `unseq` except t9's), every step is advanceable, the
  round is the first entry, and the outcome list stays a SINGLETON —
  measured (§A). `CerberusRound`'s "step list `= [s]`" (`Round.lean:195`
  –`:200`) is false at a reducible `unseq` with ≥ 2 reducible components
  even when deterministic: the certification statement must become "the
  first advanceable entry is `s`" (C.4). The outcome-LIST form is forced
  only by the ccall-sibling pattern (t9) and by `nd`/memory forks.

### B.3 Loaded values

- Types: `loaded_value = LVspecified object_value | LVunspecified ctype`,
  `value = … | Vloaded loaded_value` (`core.lem:185`–`:191`); ctors
  `Cspecified`/`Cunspecified` (`:213`–`:214`), evaluated by `PEctor`:
  `Cspecified [Vobject ov] → Vloaded (LVspecified ov)`, `Cunspecified
  [Vctype ty] → Vloaded (LVunspecified ty)` (`core_eval.lem:680`–`:683`).
- `load`: `CerbMem.loadM` returns `Footprint × MemValue`
  (`CerbMem.lean:1961`); the WRAP into `Vloaded` is `Caux.valueFromMemValue`
  in `step_action`'s Load continuation (`core_reduction.lem:738`–`:748`;
  `core_aux.lem:126`–`:146`: `MVunspecified ty ↦ Vloaded (LVunspecified ty)`,
  `MVinteger ↦ Vloaded (LVspecified (OVinteger _))`, …). The mirror already
  states this (`Step.load`, `Step.lean:1489`–`:1500`).
- `store`: `memValueFromValue ty cval` (`core_aux.lem:148`–`:200`) accepts
  `Vobject` AND `Vloaded (LVspecified …)` at matching type, and
  `Vloaded (LVunspecified ty')` at ANY `ty` (`:164`–`:165`, "TODO: check
  ty = ty'?") → `unspecified_mval ty'` → bytes `List.replicate sz
  paddingByte` (`CerbMem.lean:587`–`:589`, `paddingByte` `:569`). The
  mirror's `Step.store` premise is this function (`Step.lean:1476`).
  `allocateObject` at `initOpt = none` writes
  `{prov := Prov_none, copyOffset := none, value := none}` bytes
  (`CerbMem.lean:1870`–`:1871`); whether that equals `paddingByte` decides
  whether `store(ty, p, Unspecified(ty))` on a fresh cell is a byte no-op
  — to measure at E2 (`paddingByte`'s definition, `:569`).
- `conv_loaded_int` (`std.core:61`–`:67`): `case _n of Specified(n) ⇒
  Specified(conv_int(ty, n)) | Unspecified(_) ⇒ Unspecified(ty)`; a
  `PEcall` (B.4).
- `undef(<<UB036>>)`: `PEundef` in `step_eval_pexpr` returns
  `Undefined.undef loc' [ub]` (`core_eval.lem:596`–`:604`); through the
  EVAL step's monad and `liftCore_run` it is `ND.kill (Undef loc ubs)`
  (`driver.lem:171`–`:185`) — `ShippedRefusal.killed (Undef0 …)` in the
  demo's vocabulary; never on the specified path.

### B.4 Pure impl/std calls and the evaluator

- **Where callee bodies live.** `call_function file f_nm cvals`
  (`core_eval.lem:120`–`:165`; `Core_eval.lean:111`): `Sym f` → `file.stdlib`
  first, then `file.funs` (`Fun` declarations only); `Impl f` →
  `file.impl` (`IFun`). Substitution `foldl2 subst_sym_pexpr` into the
  body. The Lean pipeline populates `stdlib` by parsing
  `runtime/libcore/std.core` with `CoreParser` (`Main.lean:742`–`:754`,
  `loadCoreStdlib :44`) and `impl` from
  `impls/gcc_4.9.0_x86_64-apple-darwin10.8.0.impl` (`:757`–`:762`). The
  demo's `prodFile` has `stdlib := fmapEmpty, impl0 := fmapEmpty,
  funinfo := fmapEmpty` (`ProdEntry.lean:125`–`:137`): a `conv_loaded_int`
  call under it is the KILL `Illformed_program "calling an unknown
  function"` (`core_eval.lem:136`). The statement's file must be the
  pipeline's (C.9).
- **How `PEcall` evaluates** (`core_eval.lem:965`–`:994`): arguments
  first (`EU.mapM self pes`); at all-values, `call_function` yields the
  substituted body, `pull_constrained 0` normalises it, and the body is
  RETURNED UNEVALUATED ("we do not immediately call eval on the result …
  as that could lead to non-termination"); the enclosing loop
  `eval_pexpr_aux2` (`:1117`–`:1140`) re-runs `step_eval_pexpr` until
  `valueFromPexpr` succeeds. Fuel: `step_eval_pexpr` is
  `step_eval_pexpr_lemFuel lemDefaultFuel` (declared `:1221`;
  `Core_eval.lean:148`) — its `n` argument is a depth counter, the lem
  fuel bounds the recursion; `eval_pexpr_aux2` is a fuelled
  step-until-value loop (`:1220`; `Core_eval.lean:158`);
  `pull_constrained` fuelled (`:1219`; `Core_eval.lean:130`). Unfolding
  depth on the corpus: `conv_loaded_int` → `conv_int` →
  `is_representable_integer` (3 bodies; `conv_int`'s `_Bool`/unsigned arms
  are dead for `signed int`); `params_length` → `params_length_aux`
  (list length + 1 unfoldings); `params_nth` (index + 1). Each
  `eval_pexpr_aux2` iteration performs one full `step_eval_pexpr` pass;
  a `PEcall` inside costs one extra iteration per unfolding level.
- **Exact semantics (engine side, NOT std.core):**
  `PEconv_int ity pe` → `mk_conv_int ity ival` (`core_eval.lem:61`–`:81`):
  `_Bool` ↦ 0/1; in `[min_ival ity, max_ival ity]` ↦ unchanged; else
  `mk_wrapI ity n` (a TODO comment records that the std.core/ISO path
  would call `<Integer.conv_nonrepresentable_signed_integer>` for signed —
  which in the gcc impl IS `wrapI(ty, n)`, `…gcc_4.9.0….impl:18`–`:20`, so
  the two agree for this impl). `PEcatch_exceptional_condition ity iop
  pe1 pe2` → `mk_iop iop` (`IntAdd/Sub/Mul/Div/Rem_t`, shifts via
  `IntExp`, `:83`–`:91`) then range check → the value, or `Undefined.undef
  loc [UB036]` (`:99`–`:113`, `:839`–`:853`). `PEwrapI` → `mk_wrapI_op`
  (`:93`–`:96`, `:828`–`:837`). `mk_wrapI` (`:29`–`:49`): `dlt = max−min+1`,
  `r = n rem_f dlt`, `r ≤ max ? r : r − dlt`. All over
  `Mem.op_ival`/`eval_integer_value` (`CerbMem`). The std.core
  `catch_exceptional_condition`/`conv_int`/`wrapI` (`std.core:18`–`:56`,
  `:229`–`:242`) are reached only through `PEcall` — in the corpus via
  `conv_loaded_int`'s body and the relational operators' `conv_int(…)`
  arguments (t2, t4, t5, t9, t10).
- **Other pure arms the corpus needs** (all `step_eval_pexpr`):
  `PEctor` — `Ctuple`, `Cspecified`, `Cunspecified`, `Civalignof`
  (`Mem.alignof_ival ty`, `:651`), `Civsizeof` (`:649`) (`:607`–`:723`);
  `PEcase` — `select_case subst_sym_pexpr` at a value scrutinee (`:725`–
  `:745`); `PEnot`, `PEop OpEq/OpLt/OpLe/OpGt/OpGe/OpOr` (`step_eval_peop`,
  `:320`); `PEif`; `PElet` (`:996`); `PEundef`; `PEarray_shift`,
  `PEmember_shift` (`:747`–`:767`; the latter reads tagDefs);
  `PEcfunction` (`:899`–`:939`: `Vloaded (LVspecified (OVpointer pv))` →
  for `PVfunction s`, `file.funinfo` lookup → `Vtuple [Vctype ret; Vlist
  BTy_ctype params; variadic; has_proto]`; a concrete pointer consults
  `funptrmap`); `PEare_compatible` (`:305`, `Ctype_aux.are_compatible`);
  `PEsym` at an unbound `Proc` name → null pointer (`:570`–`:582`, the
  demo's `eval_uncovered` residual).
- The mirror's evaluator today: `evalPexpr` = `PEval | PEsym | PEop
  (mirrored binops) | PEarray_shift` (`Step.lean:921`–`:934`). Everything
  in the previous bullet is an extension.

### B.5 `Ivalignof`/`Ivsizeof`, ctor operands, `cfunction`

- `create(Ivalignof(ty), ty)`: `step_action`'s Create arm needs
  `act_valueFromPexpr pe1 = Just (Vobject (OVinteger _))`; a `PEctor`
  operand is not a value → `ACTION_EVAL "eval operands of Create"`
  (`core_reduction.lem:657`–`:661`), a `Step_with_runstate2 (RSK_eval …)`
  round that evaluates both operands with `full_eval_pexpr'` and rewrites
  the redex to values; the next round is the demo's `Frag.create`. The
  demo has `kill_op`/`alloc_op`/`load_op`/`store_op` rows but NO
  `create_op` (manifest; `Soundness.lean:4149`–`:4314`).
- Values of the ctors: `Civalignof [Vctype ty] ↦ Vobject (OVinteger
  (alignof_ival ty))` = `CerbMem.alignofIval tagDefs ty` (`CerbMem.lean:1300`,
  `alignofCtype :495`); `Civsizeof` ↦ `sizeofIval` (`:1299`). Both read
  tagDefs for aggregates — under KOI B4's `∅` they are correct for scalars
  and arrays of scalars only.
- `Specified(Cfunction(f))`: the value `Vloaded (LVspecified (OVpointer
  (PVfunction f)))` after `Cspecified`; `cfunction(fp)` is `PEcfunction`
  (B.4). The demo's `StorableAt`/`decIndep` exclude `PVfunction` images
  (design-2 §3.1) — irrelevant here: the function pointer is never
  STORED in the corpus (only passed through env and `ccall`).

### B.6 `Eccall` — the direct call

- `step_ctx` arm (`core_reduction.lem:1347`–`:1383`): wraps `Step_ccall2
  current_tid (…)`; evaluates the function operand with
  `full_eval_pexpr'`; requires `Vloaded (LVspecified (OVpointer pv))`
  (else `error "… Eccall illtyped first operand"`, a `failwithI` panic);
  evaluates the arguments; `Mem.case_ptrval pv`: null → panic;
  `PVfunction psym` → `case_funptrval (Just psym)` DIRECTLY (`:1370`–
  `:1372`); concrete → `case_funsym_opt mem_st pv` (the `funptrmap` read,
  `CerbMem.lean:1237`). `case_funptrval`: `Nothing` → `E.undef … [UB_CERB003]`;
  `Just psym` → `call_proc core_extern file psym cvals` (`core_run.lem:34`–
  `:60`: `stdlib` first, then extern-resolved `funs`; arity check) and
  the thread update `{arena := body, stack := Stack_cons2 current_proc ctx
  stack, exec_loc := push_exec_loc psym current_loc exec_loc, env :=
  proc_env :: env, current_proc_opt := Just psym}` — IDENTICAL to the
  `Eproc` PCALL update (`:1386`–`:1400`) except the wrapper constructor.
- Driver: `can_advance (Step_ccall2 _ _) = false` (`driver.lem:908`);
  `advance_step`'s arm is `ND.return NOWAKEUP` (`:942`–`:943`; unreachable
  from the loop since it is never selected). The per-thread loop returns
  `(tid, [Step_ccall2 …])` (when the ccall is the only step; see t9 for
  the two-step case); `new_drive_core_threads` picks it; `process_core_step2`
  runs `liftCore_run step_m`, writes the thread, ticks the counter, and
  RE-ENTERS `driver2` (`:1342`–`:1347`), whose next `new_drive_core_threads`
  restarts the per-thread loop from the FIXED wrapper budget
  (`driver.lem:1907`/`:1916`: `drive_nonmemory_steps_aux2 =
  100000000`; ARCHITECTURE §4, KOI A2). RETURN from a `ccall`ed procedure
  is the ordinary value-arm RETURN (`:1129`–`:1140`) — it does not know
  how it was called.
- The return value: `run ret_561(conv_loaded_int(…))` then `pure(a_570)`
  delivers a `Vloaded`; RETURN plugs `mk_value_pe cval` into the caller's
  context (`:1136`) → `let strong a_551: loaded integer = <value> in …`.
- What the demo's shapes become: `DriverSafeCtl`/`DriverDoneCtl`
  (`Adequacy.lean:932`, `ProdLoop.lean:456`) quantify ONE per-thread loop
  run and conclude PROGRAM-DONE or exhaustion; with a ccall the loop
  returns EARLY with `[Step_ccall2 …]` in the accumulator (a third
  outcome). `prod_run_eqJ_procs`/`prod_run_safe_procs` (`ProdEntry.lean:716`,
  `:768`) consume `driver2_done`/`driver2_killed` once; with k ccalls they
  need a `driver2` induction of k+1 rounds. Design-2 §3.2's
  `DriverSafeSeg`/`SchedulerSafe` is the shape; the measurement adds:
  the `Step_ccall2` round leaves the memory untouched and the scheduler
  pick is on a singleton list (deterministic) UNLESS an unsequenced
  sibling action is pending (t9), in which case `new_drive_core_threads`
  returns a two-element list and the run forks (§A: 16 = 2^4 for the four
  recursive calls; the top call `fact(5)` has no sibling).

### B.7 `nd`

- Emitted by `Caux.mk_nd_e` (`core_aux.lem:2117`) at exactly two
  elaborator sites: the `Unspecified` alternative of an `if` condition
  and of a loop condition (`translation.lem:3823`, `:3858`; a third site
  is commented out, `:3894`). Shape: `case a of | Specified(x) ⇒
  pure(if not(x = 1) then True else False) | Unspecified(_) ⇒
  nd(pure(True), pure(False)) end`.
- Reduction: `one_step`'s `End es → ND es` (`core_reduction.lem:447`–
  `:449`); `step_ctx` → `Step_nd2 (List.map wrap_expr es)` (`:1473`–`:1474`);
  advanceable; `advance_step` → `ND.pick (SK_misc ["nd"]) th_sts`
  (`driver.lem:1039`–`:1046`) — the sequential driver ENUMERATES: outcome
  list × |es|. Observable only when a condition's scalar is unspecified —
  a program outside the logic (reading an uninitialised local). Not
  reached in any corpus run (§A).
- Mirror consequence: none beyond admitting the alternative syntactically
  (`Frag.case_value` constrains the SELECTED branch only,
  `Soundness.lean:4290`–`:4300`); a manifest OUT-OF-SCOPE row ("`End` is a
  scheduler fork; a run reaching it is at an unspecified condition").

### B.8 Annotations

- Forms on the nodes (`annot.lem:66`–`:81`): `Aloc` and `Astmt` on every
  statement node, `Aloc`+`Aexpr` on expression nodes, `Astd` on `bound`s
  and on the arithmetic/assignment nodes (§A). Patterns bind with their
  own `List annot` (`Pattern annots _`, `core.lem:224`–`:225`), empty in the
  corpus as far as the printer shows.
- Engine reads: (i) `get_loc e_annots` in `step_ctx`'s general arm →
  `th_st with current_loc := loc` unless `is_library_location`
  (`core_reduction.lem:1155`–`:1164`); the value arms (`:1102`–`:1113`, `:1146`–`:1151`)
  and the `(CTX, {A}v)` REMOVE-ANNOT arm do NOT update it. `current_loc`
  is read by `Eccall`'s UB payload (`:1355`), `push_exec_loc` (`:1364`,
  `:1396` — so `Ctl.execLoc` carries locations), the action requests'
  `loc'` (`:1169`–`:1173`: the ACTION's own loc unless library), the memop
  request (`:1477`), the unsequenced-race UB (`:1483`), and the evaluator
  entry (`E.eval_pexpr2 … th_st.current_loc`, `:49`). (ii)
  `Cerb_attributes.get_with_address e_annots` at Create (`:648`) — an
  `Acerb` attribute; absent in the corpus.
- REMOVE-ANNOT rounds: the dynamic `Eannot` (`DA_pos`/`DA_neg` lists) is a
  different constructor; the demo mirrors it (`Step.annot_ctx`/
  `annot_merge`, `Step.lean:1751`, `:1763`). Static `List annot` on
  `Expr` nodes are what `Frag`/`BareHead`/`toVal` fix to `[]`
  (`Soundness.lean:4129`–`:4147`, `:3981`; `Step.lean:247`–`:251`).
- Cost of admitting located heads: design-2 §4.3 option (C) stands —
  `Ctl` gains `curLoc`, every `Step` rule threads `get_loc a` through the
  library test, `Frag`/redex spellings/`toVal`/`ofVal` generalise to
  `Expr a`, the exports' `hcl` disappears into the configuration. New
  from this measurement: `Ctl.execLoc`'s pushes read `curLoc` (already a
  `Ctl` field, so the PCALL rule composes); the certification's
  `M.thread` (`Step.lean:423`–`:426`) takes `current_loc` from the
  configuration instead of `M`.

### B.9 NEW — negative actions and the exclusion protocol

- Emission: every assignment whose value is not used at statement level,
  `let weak _: unit = neg(store(ty, p, conv_loaded_int(ty, v))) in
  pure(conv_loaded_int(ty, v))` under a `bound` (t2–t8: 60 occurrences).
- Engine (`core_reduction.lem:1290`–`:1338`): at `Eaction (Paction Neg act)`,
  `break_at_bound_and_sseq ctx` (`:868`–`:912`) splits the context at the
  innermost `Cbound` (and, if present, the innermost `Csseq` under it).
  `NO_BOUND` → `error` (panic). `BOUND_NO_SSEQ ctx_bound ctxA` (the corpus
  shape: the neg action sits under `Cwseq` frames only) →
  `Step_with_runstate2 (RSK_tau …)`: draws `E.fresh_excluded_id` and
  `E.fresh_symbol` (`core_run_aux.lem:237` `excluded_supply`;
  `core_run.lem:115`–`:119` `sym_supply`), rewrites the arena to
  `bound( let weak (_: unit, s: unit) = unseq( Eexcluded n act ;
  apply_ctx (add_exclusion n ctxA) (pure(Unit)) ) in pure(s) )`
  (`:1298`–`:1309`; `add_exclusion` pushes `n` onto every `DA_*` exclusion
  list in `Cannot` frames of `ctxA`, `:939`–`:958`). The `Eexcluded n act`
  redex then runs `process_action (Just n)` (`:1345`–`:1346`) → the store
  executes with continuation `{DA_neg n [] fp} Unit` (`:705`–`:709`); the
  other component reduces to a value; UNSEQ-ANNOT (B.2) merges (no race:
  one annotated component) → LETW-ANNOT at the pair pattern → `{A}
  pure(s)` → PURE → `{A}v` → REMOVE-BOUND drops `A`. About eight rounds
  per assignment statement.
- `BOUND_WITH_SSEQ … CTX …` → a plain `Step_tau2` re-polarising to `Pos`
  (`:1319`–`:1324`); `BOUND_WITH_SSEQ` with a non-empty inner context →
  the same exclusion rewrite via `Csseq` (`:1326`–`:1338`).
- Mirror impact: the successor TERM contains a fresh symbol and a fresh
  id drawn from `core_run_state` fields the mirror's configuration does
  not carry (`MachineCtx.runState` is immutable, `Step.lean:405`–`:413`;
  `Embeds.runState : dst.core_run_state0 = M.runState`, `Round.lean:172`–
  `:178`). Either the two supplies join the live configuration (as
  `current_loc` joins `Ctl` in E1) or the neg-action rule is stated with
  the supplies as explicit inputs/outputs. `CerberusRound` already allows
  the run state to change with `labeled` fixed (`Round.lean:201`–`:203`), so the
  round shape is fine; the mirror's STATE is what changes.

### B.10 NEW — `seq_rmw` (postfix increment)

- `Eaction (Paction Pos (Action loc _ (SeqRMW with_forward pe1 pe2 sym pe3)))`
  (`core_reduction.lem:1228`–`:1289`): `Step_action_request2 "SeqRMW"` with
  `SeqRMWRequest2 ty ptrval mk_mval' mk_th_st'` after drawing a fresh
  excluded id and a fresh symbol; the driver (`driver.lem:710`–`:719`)
  does `Mem.load`, evaluates `pe3` under a temporary env binding `sym` to
  the loaded value (`full_eval_pexpr th_st_tmp …`, `:1249`–`:1257` — the
  corpus body is `case a of Specified(x) ⇒ Specified(conv_int(ty,
  catch_exceptional_condition_add(ty, conv_int(ty, x), 1))) | Unspecified
  ⇒ Unspecified(ty)`), `Mem.store`s the result, and the continuation
  rewrites the arena through `break_at_bound_and_sseq` with a `DA_neg`
  annotation (`:1258`–`:1289`) — the B.9 machinery again. One corpus
  occurrence (t2's `i++`). `has_ccall`/`is_unseq_with_ccall` treat it as
  an action.

### B.11 NEW — `memop(PtrValidForDeref, ty, p)` (dereference check)

- Every `*p` (t3's `*p = 4`, t8's `a[i]`) elaborates to `let weak b:
  boolean = memop(PtrValidForDeref, ty, p) in pure(if b then p else
  undef(UB043))` inside the `Specified(p)` alternative. `Ememop` at
  non-value operands → EVAL round (`core_reduction.lem:310`–`:319`); at
  values → `MEMOP` → `Step_memop_request2 current_loc memop cvals tid
  (is_unseq_with_ccall ctx) k` (`:1475`–`:1479`); advanceable unless
  ccall-sibling; `advance_step` → `perform_memop_request2` (`driver.lem:1011`–
  `:1017`, `:762`–`:783`) → `liftMem (Mem.validForDeref_ptrval ref_ty ptr_val)`
  → `CerbMem.validForDerefPtrval tagDefs ty pv` (`CerbMem.lean:2242`–
  `:2262`): `Prov_some id` → `¬ dead id ∧ isWellAlignedPtrval` (`:2223`);
  null/function/`Prov_none` → false. A memory READ of liveness and
  alignment; the demo's memop rows are `PtrEq` only (manifest).

### B.12 NEW — `Ecase` at a non-value scrutinee, `Elet`, general patterns

- `Ecase pe pats` with `valueFromPexpr pe = Nothing` → `EVAL "Ecase"`
  with `eval_pexpr pe` (`core_reduction.lem:323`–`:339`; the STEP evaluator
  `eval_pexpr2`, `:49`–`:56`, which `step_ctx`'s closure turns into a value
  node) → next round the demo's `case_value` (`select_case subst_sym_expr`,
  `core_aux.lem:2049`–`:2062`; `match_pattern :2015`–`:2047` handles
  `CaseBase`, `Cspecified`, `Cunspecified`, `Ctuple`, lists). Corpus
  scrutinees: `(a, b)` tuples of symbols and single symbols.
- `Elet pat pe1 e2` (`:341`–`:357`): at a value, `TAU` with `update_env`;
  else `TAU_WITH_RUNSTATE "Elet"` with `full_eval_pexpr pe1` then
  `update_env` — ONE round. Corpus: `let a: ctype = params_nth(ps, i) in …`
  in every call.
- Binders: `update_env pat cval` (`core_aux.lem:2427`–`:2497`) binds
  `CaseBase (Just s)`, recurses through `Ctuple`, `Cspecified`
  (`Vobject oval` payload), `Cunspecified` (`Vctype ty`), lists; any other
  ctor/value pairing is `error` (panic). The mirror's binder rules are at
  three fixed patterns (`Step.lean:1593`–`:1672`; `symPat`/`specPat`,
  `:1092`/`:1106`).

## C. Design, per construct → slice

Standing shape for every slice: new `Frag` rows (fail-closed: exactly what
the mirror covers), mirror `Step` rules with engine cites, `complete_*`
lemmas so `frag_round_complete` (`Round.lean:5369`) dispatches, manifest
rows (RULE / NO-RULE / OUT-OF-SCOPE with the deciding record), rule faces
`wps_*`/`wpt_*` only where a program in the corpus needs them, an
exhibit taken from the corpus, a range audit. `pot`/`esize` gain
equations for new node kinds (they are total already, at the leaf
default). Sizes: S ≤ 2 worker-days, M ≤ 1 week, L > 1 week.

### C.1 — E1: annotations, `bound`, ctor constants (`create_op`) — L

- `Frag`: every constructor generalised from `Expr []` to `Expr a`; new
  rows `bound` (`Ebound e` with `Frag e`) and `create_op` (Create at
  `PePure` operands not all values). `PePure` gains `PEctor Civalignof
  [PEval (Vctype ty)]`/`Civsizeof` (values by `alignofIval`/`sizeofIval`
  at `M.tagDefs`).
- `Step`: `bound_pure`/`bound_annot` (REMOVE-BOUND, drops `ds`),
  `create_eval` (ACTION_EVAL, the `load_eval` template), `bound_ctx`
  (a `Cbound` frame in `Decomp`, `Soundness.lean:598`), and the threading
  of `curLoc` through every rule (design-2 §4.3 (C)): `Ctl` gains
  `curLoc : Loc`; rule successors carry `curLoc' = if isLibraryLocation
  (get_loc a) then curLoc else loc` at the redex node's list; the value
  arms and REMOVE-ANNOT leave it. `M.thread` reads `ctl.curLoc`.
- Classification: `complete_bound`, `complete_create_op`; no new refusal
  or residual arm.
- Faces: `wps_bound`/`wpt_bound` (a frame rule: `wps … e` entails `wps …
  bound(e)` with the same post — the annotation drop is invisible to the
  post since posts are stated at bare values), `wps_create_eval`/`wpt_…`.
- Adequacy impact: `hcl : th₀.current_loc = M.currentLoc` leaves every
  generic export (ARCHITECTURE §4 list); `ctlThread` takes the loc from
  `ctl`. Production statements: text unchanged except that `prodCtl`
  gains the cold-start loc `Loc.other "Driver.drive"` (`driver.lem:1876`).
- Exhibits: all sixteen re-elaborate (the `Expr []` → `Expr a`
  generalisation is a re-cut of `Soundness.lean` 5.3k and `Step.lean`
  3.4k lines — the grind tripwire is real; per-module, capped).
- Acceptance: no corpus program certifies yet (all need E2–E4);
  structural exhibit: `t1.core` parses as `Frag` (a `decide`/`rfl`
  membership check on the transcribed term, no run).
- Size: L (design-2 estimated 1–2 worker-weeks; `bound` + `create_op`
  add ≤ 2 days).

### C.2 — E2: loaded values, patterns, the pure core (`case`/`let`) — M–L

- `PePure` gains: `PEctor Ctuple/Cspecified/Cunspecified`, `PEcase` (over
  `match_pattern`'s pattern classes, substitution `subst_sym_pexpr`),
  `PEnot`, `PEif`, `PEundef` (evaluates to NO value — the mirror answers
  `none`; the engine's outcome is a classified UB kill, a new
  `evalClass` `.kill` arm), the binops `OpEq/OpLt/OpLe/OpGt/OpGe` already
  mirrored plus `OpOr`/`OpAnd` (check `evalBinop`). `PElet` if it occurs
  (not in the corpus; skip).
- `Frag`: `sseq_pat`/`wseq_pat` at ANY pattern with premise "the head
  delivers a value `v` with `matchPattern pat v = some binds`" replacing
  the three fixed-pattern rows (or added beside them — the old rows are
  instances; prefer replacement, one rule per engine arm); `case_op`
  (`Ecase` at a `PePure` non-value scrutinee — the EVAL round);
  `let_` (`Elet` at a `PePure` head — the one-round TAU_WITH_RUNSTATE).
  `BareHead` is subsumed once the binder rule is generic over patterns
  AND the LETS-ANNOT beta gets a rule (the engine has it,
  `core_reduction.lem:416`–`:423`; the demo excluded it by fiat — the
  emitted dialect reaches it: `let strong a: loaded integer = bound(…)`
  never delivers `{A}v` because `bound` drops it, but `let weak (_, s) =
  unseq(…)` in B.9 does). Add `sseq_pat_annot`/`wseq_pat_annot`.
- `Step`: `sseq_pat_pure/annot`, `wseq_pat_pure/annot` (successor env
  `update_env pat v ρ`; the engine's `update_env_aux` panics on mismatch —
  mirrored as absence, classified `panic`), `case_eval`, `let_eval`
  (premise: the certified evaluator on the head).
- Classification: `complete_sseq_pat` etc.; `evalClass` gains `.kill` at
  `PEundef` and `.uncovered` stays for the leaves it has.
- Faces: `wps_seq_pat`/`wpt_seq_pat` (binding rule with the pattern's
  bindings substituted into the continuation's precondition — the
  R/O'H "let" rule), `wps_case_eval`, `wps_let`.
- Loaded values in the rule faces: measure at E2 which `wps_store*`/
  `wpt_store*` fix `Vobject` in the stored value (the atomic
  `store_atomic` is over `memValueFromValue`, `Rules.lean:264`); state the
  store rules at `Vloaded (LVspecified ov)` too (same bytes,
  `core_aux.lem:168`–`:171`), and a NEW `store_unspecified` rule
  (`Vloaded (LVunspecified ty)` → the unspecified image `intUndefBytes`-
  class bytes; premise-free on the old contents) — every uninitialised
  local needs it (t5, t7, t8).
- Adequacy impact: none in shape. Exhibits: `CaseExhibit`, `WseqExhibit`
  are the natural hosts; the `BareHead` OUT-OF-SCOPE row retires.
- Acceptance: none end-to-end yet; `t5_ifelse.core` and `t6_switch.core`
  are `Frag` after E2 (their remaining need is E3's `conv_int` and E5's
  `neg`).
- Size: M–L (≈ 1 week).

### C.3 — E3: the impl-defined integer semantics and std.core unfolding — M–L

- `PePure` gains `PEconv_int`, `PEcatch_exceptional_condition`, `PEwrapI`
  (mirror evaluator = the engine's `mk_*` functions, called directly — no
  re-implementation: `evalPexpr … (PEconv_int ity pe) = mk_conv_int ity
  <$> …`; the UB arm of `catch` is `none` + an `evalClass` `.kill UB036`)
  and `PEcall (Sym f) pes` for `f ∈ file.stdlib` a `Fun`: the mirror
  evaluates the substituted body (`call_function` verbatim) — the
  measure `peDepth` becomes an UNFOLDING measure `peUnfold` bounding the
  `eval_pexpr_aux2` iterations (per B.4: one per call level; the corpus
  needs ≤ 3 + list length), and the `hdp : peDepth pe ≤ lemDefaultFuel`
  premises become `peUnfold pe ≤ lemDefaultFuel` (F2 later restates the
  right-hand side, C.10).
- Certification of the evaluator: `eval_pexpr_aux2` is a fuelled
  step-until-value loop over `step_eval_pexpr` (fuelled recursion). The
  demo's existing evaluator certification (`EvalClass.lean`, the
  `step_eval_pexpr`/`pull_constrained` bridge) extends arm by arm; the
  `PEcall` arm adds an induction on the unfolding depth. This is the
  slice with the largest evaluator proof.
- Rows: `pure_call_std` RULE (a std.core `Fun` at values), `pure_call_user`
  NO-RULE (user `Fun`s: none emitted for C), `pure_call_impl` OUT-OF-SCOPE
  (`Impl` names: none in the corpus).
- The FILE: `prodFileWith` cannot host this — `stdlib := fmapEmpty`. E3
  introduces the pipeline file object (C.9): the statement's file carries
  `stdlib := loadCoreStdlib (CoreParser.parseFile std.core)`'s map and
  `impl0 := loadCoreImpl …` — engine-side definitions (`Main.lean:44`,
  `:59`) over the pinned `std.core` text. Whether that text enters as a
  string literal in the statement, or as the parsed `Fmap` term, is §D Q3.
- Acceptance: with E4, **t1 certifies end to end** (`t1.core`: `bound`,
  one `unseq`, pair-pattern `let weak`, `PEcase`/`Cspecified`/`PEconv_int`/
  `PEcatch`/`conv_loaded_int`, `Ivalignof`, `save` with a `Cspecified`
  initializer, `run` with a `PEcall` argument, `kill`). This is the
  ruling's first acceptance test ("t1 after the arithmetic slice").
- Size: M–L (≈ 1 week; the file object question may add).

### C.4 — E4: `unseq` — M

- `Frag.unseq (es)` with every component `Frag`; `Decomp` gains the
  `Cunseq` frame; `Frag.wseq_pat`/`sseq_pat` (E2) take the `unseq` head.
- `Step.unseq_ctx`: the LAST reducible component steps (the engine's
  order, B.2) — the mirror is deterministic; `Step.unseq_vals`:
  UNSEQ-PURE/ANNOT with premise `do_race`-free (state as the engine's
  `one_step_unseq_aux … = Just (fps, cvals)`), successor `Expr a (Eannot
  fps (tuple))`.
- Certification: `CerberusRound` (`Round.lean:195`) restated from
  `step_ctx … = [s]` to `∃ pre post, step_ctx … = pre ++ s :: post ∧
  (∀ s' ∈ pre, can_advance s' = false) ∧ can_advance s = true`, with a
  lemma `find_can_advance (pre ++ s :: post) = some s`; the loop lemmas
  `loop_step_frag`/`loop_step_frag'` (`DriverCollapse.lean:2118`/`:2024`)
  take the same generalisation (they unfold `find_can_advance`). For
  the corpus's `unseq`s `pre = []` (every entry advanceable), so
  `engine_step_matchU` instances stay one-step. This is a TEXT change of
  two pinned certification statements, no production statement changes.
- Refusal: UNSEQUENCED-RACE is a `killed (Undef0 … UB035)` arm of
  `complete_unseq`; `one_step_unseq_aux`'s `error` (a non-value
  component when all are irreducible: impossible by `is_irreducible`) is
  the panic family.
- Faces: `wps_unseq`/`wpt_unseq` for the READ-ONLY case the corpus
  exercises (components: pure evaluations, loads, `create`/`store` of
  fresh argument cells) — the classical "unsequenced but disjoint" rule:
  ∗-separated footprints, sequential composition in the engine's order,
  post at the tuple. A general concurrent-style rule is out of scope
  (feature set closed).
- Adequacy impact: NONE to the closed forms' singleton equation for the
  corpus (measured, §A); the outcome-list shape is E7's.
- Acceptance: **t1** (with E1–E3).
- Size: M (3–5 days; the `CerberusRound` restatement is the risk item).

### C.5 — E5: negative actions, the exclusion protocol, `seq_rmw` — L

- State: the two supplies `sym_supply`/`excluded_supply` join the live
  configuration (a `RunSup` component of `Ctl`, or `Config` gains the
  `core_run_state`'s supply projection); `Embeds` ties them to
  `dst.core_run_state0`; `CerberusRound`'s `rs'` existential is replaced by
  the configuration's successor supplies with `labeled` and `aid_supply`
  existential as today.
- `Frag`: `neg_action` (an action at `Neg` polarity whose context has a
  `Cbound` — the `NO_BOUND` panic is classified), `excluded` (`Eexcluded n
  act`), `seq_rmw` (at `PePure` operands; body `pe3` in `PePure`).
- `Step`: `neg_rewrite` (B.9's arena rewrite, successor computed by
  `break_at_bound_and_sseq`/`add_exclusion` — call the engine's own
  functions in the rule, mirror doctrine), `excluded_store`/`excluded_load`
  (the `process_action (Just n)` variants delivering `{DA_neg n [] fp}`),
  `seq_rmw` (load + certified evaluation of `pe3` under the temporary
  binding + store + the B.9 rewrite; one round), and `unseq_vals`'s race
  premise now non-trivial (`Mem.overlapping` on footprints — the ∗ gives
  disjointness for free in the faces).
- Faces: `wps_assign` — the R/O'H assignment axiom for the emitted
  statement shape `bound(let weak (p, v) = unseq(pure(x), E) in let weak _
  = neg(store(ty, p, conv(v))) in pure(conv(v)))`: `{ x ↦ _ } ⟹ { x ↦ v }`
  with `E`'s post — ONE derived rule hiding the eight-round protocol;
  `wps_seq_rmw` likewise for `i++`.
- Adequacy impact: exports' `LabeledProcs`/`CtlTied` ties unchanged; the
  production entry supplies are `initial_core_run_state sup …`'s
  (`prodRS`, `ProdEntry.lean:587`) — the statement's `sup` already exists.
- Acceptance: **t5_ifelse, t6_switch, t4_while** certify (E1–E5, no
  calls; t4 needs `OpLt`/`conv_int` from E2/E3).
- Size: L (1–1.5 weeks: a configuration change touches Round/Soundness
  headers again; do it in the same design as E1's `curLoc` so the two
  "live state" changes share one shape — §D Q4).

### C.6 — E6: `Eccall` and the C-call protocol; `PtrValidForDeref` — L

- Pure additions: `PEcfunction` (reads `M.file.funinfo` — the file object
  must carry the pipeline's `funinfo`), `PEare_compatible`, `Vlist`/`Vtuple`
  values, `params_length`/`params_nth` (E3's std.core mechanism).
- `Frag.ccall` at `PePure` operands (function operand evaluating to
  `Vloaded (LVspecified (OVpointer (PVfunction f)))`; the concrete-pointer
  arm — a `funptrmap` read — is NO-RULE here, RefinedC arc), `Frag.memop_deref`
  (`PtrValidForDeref` at values and at operands).
- `Step.ccall`: the PCALL successor (`Step.call`'s, `Step.lean:2047`) at
  the callee resolved by `lookupProc M.file M.extern f`; certified NOT by
  `engine_step_matchU` but by a sibling `ccall_round`: "the per-thread
  loop returns `acc[tid ↦ [Step_ccall2 tid m]]`, `liftCore_run m` at the
  driver state yields the successor thread, and `process_core_step2`
  re-enters `driver2`" (design-2 §3.2/3.3, confirmed by `driver.lem:1342`–
  `:1347`). `Step.memop_deref`: `applyMemM (validForDerefPtrval …) σ =
  some (b, σ)`; atomic rule `deref_atomic` over `pointsToCell`: at a live
  cell whose base is aligned for `ty`, `b = true` (a MemWF-style fact:
  `alignedBase` is derivable from `allocateObject`'s `alignDown`,
  `CerbMem.lean:1851`–`:1852`).
- Adequacy: `DriverSafeCtl` → a segment form `DriverSafeSeg` (third
  outcome: `[Step_ccall2 …]` at a configuration the logic characterises);
  `SchedulerSafe`/`SchedulerDone`: induction on the OUTER fuel over
  `driver2` rounds (`driver2_lemFuel`, `Driver.lean:386`), each round a
  segment then PROGRAM-DONE or a ccall round; the total lane's budget
  `1 + m + k' ≤ k` gains the ccall's outer unit. The closed forms
  `prod_run_eqJ_procs`/`prod_run_safe_procs` are restated over both
  loops; the outer `fuel` does work (KOI A2 closes for programs with
  calls). TEXT changes: `DriverSafeCtl`/`DriverDoneCtl` (new), the two
  pipeline theorems, and every `*_certified_production` that calls
  (`fib_rec`, `even_odd`) — those keep `Eproc` and their old lane as
  authored-Core exhibits until retired (§D Q7).
- The argument-cell protocol needs no new rule: `create`/`store`/`kill`
  and `unseq(kill, kill)` are covered (E1/E4); the callee's
  pointer-typed parameters are ordinary `pointsToCell`s passed in the
  spec table's precondition — the spec of `add` is over the two CELLS,
  which the R/O'H reading handles verbatim.
- Acceptance: **t2** (with E1–E5; `seq_rmw` from E5), **t3**, **t10**;
  t9 blocked on E7.
- Size: L (design-2 §3.4 said 2–3 weeks incl. function-pointer coupling;
  without the `funptrmap` coupling ≈ 2 weeks).

### C.7 — E7: the outcome-list closed form (t9); `nd` row — M

- `nd`: OUT-OF-SCOPE manifest row + the `esize`/`pot` equations for
  `End` (already leaf-default). No rule.
- t9's fork (B.2/B.6): `new_drive_core_threads` picks among
  `[Step_ccall2 …; Step_action_request2 (load) …]`; the closed form for
  such a program is `∀ o ∈ runND …, o.1 = Killed _ fuelExhaustedKill ∨
  (∃ dres, o.1 = Active dres ∧ ψ …)` plus non-emptiness (design-2 §3.2
  item 4), proved by a `CerbND` lemma on `nd_pick` over a two-element
  list and the `SchedulerSafe` induction applied on each branch (the
  load branch performs the action in the scheduler via
  `process_core_step2`'s `Step_action_request2` arm, `driver.lem:1323`–
  `:1326`, then re-enters `driver2`). The mirror must ALSO step the
  ccall-sibling load as an excluded-from-the-loop action: a
  `Step.action_deferred` variant whose certification is a scheduler
  round, not a loop round.
- Acceptance: **t9** (16 executions, all `Specified(120)`, stated as
  the outcome-list theorem; the singleton equation is FALSE for t9 —
  the honest measurement).
- Size: M (≈ 1 week after E6).

### C.8 — Not an E slice: tagDefs (t7) and arrays (t8)

- t7 needs `M.tagDefs = file.tagDefs ≠ ∅` and `drive file.tagDefs …`
  (KOI B4's mover), `PEmember_shift` in the evaluator, `create` of a
  struct type and the whole-struct `Unspecified` store. The dialect
  slices do not move B4; t7 stays in the corpus as the B4 acceptance
  program (§D Q6).
- t8 needs E1–E6 plus the whole-array `Unspecified('signed int[4]')`
  store (E2's `store_unspecified` at an array type — `hinert` holds for
  integer arrays, ARCHITECTURE §2.1) and `array_shift` inside
  `Specified(…)` (E2). Acceptance after E6 with no extra slice; listed
  here because the array cell's sub-range view (`pointsToView`) is the
  face it uses.

### C.9 — The file object in the statement

Every production statement today names `prodFileWith procs e`
(`ProdEntry.lean:544`), a hand-built `file` with empty `stdlib`/`impl0`/
`funinfo`/`tagDefs`. From E3 on the statement needs the pipeline's file.
Options, all statement-admissible only if they name engine functions:
(a) `pipelineFile : translation_unit → file` = the Lean pipeline's
`desugar`/`annotate_program`/`translate`/`link`/`convert_file`
composed (pure functions under `CerberusFresh.forceIO`'s wrappers,
`Main.lean:519`, `:533`, `:560`, `:821`, `:862`, `:881`) applied to the Cabs AST of the C
file (produced by the OCaml parser as JSON and read by the pinned
`CabsImport` seam) — the truest "elaborated by the pinned pipeline",
but the proofs need the concrete Core, i.e. kernel reduction of the
whole frontend (fuel-indexed recursions, `Pmap`s — KOI A4 says closed
engine maps stop reducing at the next pin): a grind risk; (b) the Core
term transcribed from the verbatim `.core` (an authored Lean `file`
whose bodies are the emitted Core), with a committed EXECUTABLE check
(`#eval`-level, a speedbump, not kernel) that `pipelineFile json =
t1File`, and the theorem over `t1File` — honest gap disclosed
("unmodified, up to a checked-by-execution equality"); (c) `CoreParser.parseFile
t1CoreText` (the pinned seam) in the statement over the committed text
— names only engine functions, reduction cost far below (a), but
`CoreParser` interns symbols by name hash (`CoreParser.lean:2147`), so
the parsed file is symbol-renamed relative to the pipeline's; the
semantics is invariant under a consistent renaming but that theorem does
not exist. [AGENT] recommendation: (b) for the arc, with (c)'s parse as
a SECOND executable cross-check, and (a) recorded as the target once
the pin's maps reduce (A4's request). §D Q3.

### C.10 — Order, dependencies, and the two pending rebases

Order (measured, replacing the ruling's provisional list):
**E1 → E2 → E3 → E4 (t1 certifies) → E5 → E6 (t2, t3, t10, t4–t6, t8)
→ E7 (t9)**; `nd` is a row in E7, not a slice; `neg`/`seq_rmw` (E5) is
new and precedes `Eccall` because t2 needs both; `PtrValidForDeref` rides
E6. Dependencies: E2 needs E1 (patterns bind annotated heads); E3 needs
E2 (`PEcase`/ctors in the unfolded bodies) and introduces the file object
(C.9); E4 needs E2 (tuple binders) and E1 (`bound` frames around every
`unseq`); E5 needs E4 (the rewrite produces an `unseq`) and E1
(`Cbound`); E6 needs E3 (`params_*`) and E5 (t2's assignment); E7 needs E6.

Rebase over the LemLib re-pin (KOI A6; scout §6): the re-pin's 13
`lem*` rewrite sites and the `SymMap` law live in `Step`/`Soundness`/
`Round`/`DriverCollapse`/`EvalClass` — the same modules E1 re-cuts.
Rule: E branches are stacked on `main`; whichever of {re-pin, E1} lands
first, the other rebases; E1 should not start its `Soundness.lean`
re-cut until the re-pin's class (a)/(a′) decisions are made (or the
re-cut is done twice). E2–E7 add declarations rather than re-cutting
existing ones, so they rebase mechanically. The `Pmap.join`
non-reduction (A4 (a′)) matters to C.9's option (a) directly.

Rebase over the fuel restatement (F2, `docs/2026-09-04_fuel-restatement-design.md`
§3–4): F2 adds `[LemFuel]` to ≈ every public statement and turns `≤
lemDefaultFuel` premises into `≤ LemFuel.fuel`. E slices must (i) keep
stating their bounds as `≤ lemDefaultFuel` in the existing idiom so F2's
mechanical pass covers them, (ii) make E3's `peUnfold` measure a
per-evaluation potential (F2 §3: "the PER-EXPRESSION potential bound is
exactly right"), (iii) not introduce numerals. E6's outer-loop
induction is exactly F2's "closed partial forms over both loops" — if
F2 lands first, E6 states its scheduler lane over `LemFuel.fuel` from
birth; if E6 lands first, F2's restatement of `prod_run_safe_procs`
absorbs E6's new shape (one more site in its census).

## D. Open questions for the operator

1. **Which Core is "emitted Core"?** Measured: the pipeline executes the
   RAW elaborated Core (§0.1). `--sequentialise` yields the same values
   (t9: 1 execution vs 16) and removes `unseq` entirely (E4 disappears,
   E5 shrinks), but a theorem over `sequentialise_file file` is about a
   program the shipped pipeline does not run, and the pass is not on the
   Lean pipeline's path. [AGENT] treats the raw dialect as the referent
   and the `.seq.core` files as informational. Confirm.
2. **The acceptance programs.** t1 after E4 and t2 after E6 (the ruling's
   two), plus t3–t6, t8, t10 after E6 and t9 after E7 (outcome-list
   form). Is the whole corpus the arc's acceptance set, or the two?
3. **The file object in the statement** (C.9): transcribed term +
   executable pipeline-equality check (b), or the pipeline function in the
   statement with kernel reduction (a), or the `CoreParser` parse of the
   committed text (c)? (b) is recommended; it leaves an honest, disclosed
   gap between "the pipeline's output" and "the term in the theorem".
4. **Two "live state" changes** (B.8, B.9): `current_loc` (E1) and the
   two run-state supplies (E5). Designing both into the configuration in
   E1's shape (one `Ctl` change, one certification re-cut) versus two
   separate re-cuts — the first costs E1 more up front, the second re-cuts
   `Round`/`Soundness` twice. Recommendation: one shape in E1, fields
   populated when E5 uses them.
5. **`neg`/`seq_rmw` as a slice** was not in the approved list. It is
   forced (60 occurrences; every assignment statement). Approve E5 as
   stated, or fold it into E6?
6. **t7 (struct) needs KOI B4** (`tagDefs ≠ ∅`), not a dialect change.
   Keep t7 in the corpus as the B4 acceptance program, outside E?
7. **The sixteen authored exhibits**: keep them alive as the regression
   suite through the arc and retire each when its emitted-Core twin
   certifies (recommended), or convert them in place?
8. **The `hbsz` premise of `Frag.case_value`** (KOI B7) is now on the hot
   path (every `case` in every program). For transcribed terms it is
   `rfl`/`decide`; for the theorem `esize (subst_sym_expr x v e) = esize e`
   (a fuel-indexed induction over the generated AST) — do we request it
   from cerberus-lean as a lemma about `subst_sym_expr`, or carry it?
9. **`mk_conv_int`'s TODO** (B.4): the engine's signed non-representable
   conversion calls `mk_wrapI` directly rather than the impl-defined
   `<Integer.conv_nonrepresentable_signed_integer>`; for the pinned gcc
   impl the two coincide. Worth a note to the cerberus-lean team (a
   latent divergence from std.core's own definition for other impls), or
   out of our lane?
10. **Sizes**: E1 L, E2 M–L, E3 M–L, E4 M, E5 L, E6 L, E7 M — roughly
    8–10 worker-weeks serial, one worker, before t9. Acceptable while the
    pins are blocked, or should E stop at t1 (E1–E4, ≈ 4 weeks) and
    reassess?

## E. What was not measured

- The Lean pipeline was not run (no `lake`/`lean` per brief): the
  claim that the Lean-side `file` equals the OCaml `--pp=core` text is
  from the code (`Main.lean:499`–`:880`), not from a run; the annotation
  lists' full contents (`Astmt`/`Aexpr`) are from the elaborator source,
  not observed.
- Whether `paddingByte` equals `allocateObject`'s fresh byte (B.3) —
  a one-line read deferred to E2.
- `evalBinop`'s coverage of `OpOr`/`OpAnd` and the exact `Vlist`/`Vtuple`
  handling in the demo's `SpikeVal`/`toVal` — E2.
- The `is_library_location` verdict on the corpus's locations
  (`CerbLocation.isLibraryLocation`): the corpus files are user files, so
  `current_loc` IS rewritten at every located node — assumed, not run.
