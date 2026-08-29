# Caesium ↔ sequentialised-Core shape study (empirical recon)

Date: 2026-08-30. Provenance: [AGENT: arc-2 empirical recon worker],
dispatched under [USER 2026-08-29]'s directive to DERISK the
statement-view question (port map §4 agenda items 2 and 16)
empirically before any design. **Evidence only; no design.** All
quotes labeled verbatim are byte-faithful to the cited artifact
(modulo the LocInfo stripping declared in §1.3, applied only where
stated); everything else is a derived observation and labeled so.

---

## 1. Method

### 1.1 Their side (Caesium)

Read the banked frontend output only (no regeneration; the workspace
`.refinedc-ws/` treated read-only):

- `.refinedc-ws/examples/proofs/<name>/generated_code.v` for
  `wrapping_add`, `paper_example_2_1`, `paper_example_2_2`,
  `reverse`, `binary_search`, `spinlock`, `mpool`;
- `.refinedc-ws/tutorial/proofs/t10_loops/generated_code.v`;
- grammar ground truth from the donor source
  `deps/refinedc/theories/caesium/lang.v:28-86` and
  `notation.v`;
- frontend behavior for constructs the corpus misses (break/continue
  targets, goto, for-desugar) from
  `.refinedc-ws/frontend/ail_to_coq.ml` (cited by line).

Finding recorded en passant (verified in source): **RefinedC's
frontend consumes Cerberus Ail** (`ail_to_coq.ml` matches
`AilSyntax.AilS*` constructors) — their pipeline is
C →(Cerberus cabs→Ail)→ Caesium. Both sides of this study therefore
share Cerberus's cabs→Ail desugaring; the divergence point is
Ail→Caesium (their frontend) vs Ail→Core (Cerberus elaboration).

### 1.2 Our side (sequentialised Core)

Driver: the built OCaml driver at
`cerberus-lean/_build/default/backend/driver/main.exe`, with the
staged runtime (env sourced from `scripts/env.sh` for the opam
switch; the plain `cerberus` name is not on PATH in this sandbox).
Exact command per probe (from `/tmp/claude-1000/shape-study/`):

```
CERB=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_build/default/backend/driver/main.exe
RT=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_build/install/default
$CERB --runtime=$RT --pp=core --sequentialise --rewrite <file.c>
```

All probes exit 0 with empty stderr. Flag provenance:

- `--sequentialise` = `Core_sequentialise.sequentialise_file`
  (pipeline.ml:533-534; "Replace all unseq() with left to right
  wseq(s)" per `--help`). Verified empirically: the same file
  without the flag shows `let weak (a,b) = unseq(e1, e2) in …`
  where the sequentialised form shows `let weak a = e1 in
  let weak b = e2 in …` (diff on probe p01).
- `--rewrite` = the Core-to-Core rewrite pass (pipeline.ml:526).
- **This flag pair is exactly CN's configuration**:
  `deps/cn/lib/setup.ml:33-35` sets `typecheck_core = true;
  rewrite_core = true; sequentialise_core = true` (verbatim). So the
  quoted Core below is the same form the port map's "CN runs on
  sequentialised Core" note refers to. Where the un-rewritten form
  differs materially it is noted (§2 row 1 note; the rewrite only
  inlines some `let weak x = pure(v)` aliases and drops dead
  `pure(Unit)` fillers — no structural change observed).

### 1.3 Corpus and annotation stripping

RefinedC sources carry `[[rc::…]]` attributes and
`#include <refinedc.h>`; **plain-C twins were written by hand**
under `/tmp/claude-1000/shape-study/` (the shapes, not the specs,
are the object of study; recorded here as required). The
annotated originals were not fed to Cerberus.

- Hand probes: `p01_arith.c` (straight-line assign/arith),
  `p02_if.c` (if/else both-return + early return), `p03_while.c`
  (while + break + continue), `p04_for.c` (for with `i++`),
  `p05_goto.c` (goto loop/done), `p06_call.c` (void call + calls),
  `p07_decls.c` (decls with/without init), `p08_ptr.c`
  (deref/address-of), `p09_struct.c` (struct field read/write).
- Twins of donor examples: `t_wrapping_add.c`, `t_reverse.c`
  (the loop body copied verbatim from `examples/reverse.c`'s
  `reverse`), `t_binary_search.c` (loop copied from
  `examples/binary_search.c`, annotations dropped).

Caesium quotes below are from the banked `generated_code.v` with
`LocInfoE loc_N` / `locinfo: loc_N ;` wrappers stripped by sed
(declared here once; otherwise verbatim). Core quotes are verbatim
pretty-printer output, trimmed to the relevant chain with `…`
marking elisions.

### 1.4 Reading the Core pretty-printer (constructor key)

Verified against `ocaml_frontend/pprinters/pp_core.ml:646-651` and
`frontend/model/core.lem:319-343`:

| printed | constructor |
|---|---|
| `e1 ; e2` | `Esseq` with unit wildcard pattern |
| `let strong p = e1 in e2` | `Esseq` (value-binding pattern) |
| `let weak p = e1 in e2` | `Ewseq` |
| `let p = pe in e` | `Elet` (pure) |
| `pure(pe)` | `Epure` |
| `bound(e)` | `Ebound` |
| `save l: ty (x: ty := pe, …) in e` | `Esave` |
| `run l(pe, …)` | `Erun` |
| `nd(e1, e2)` | `End` |
| `if pe then e1 else e2` / `case pe of …` | `Eif` / `Ecase` |
| `create/store/load/kill/seq_rmw(…)` | `Eaction` (memory actions) |
| `neg(action)` | Neg *polarity* on an action (pp_core.ml:229-231 — "only sequenced by letstrong"), not a distinct construct |
| `memop(…)`, `ccall(…)` | `Ememop`, `Eccall` |

Grammar fact used in §3 (core.lem:319-343, verbatim constructor
signatures): every operand position of `Eaction`, `Ememop`,
`Eccall`, `Erun`, `Eif`'s condition, `Ecase`'s scrutinee, and
`Esave`'s parameter defaults is a **`pexpr` (syntactically pure)**;
effectful subterms occur only as the bodies/arms of
`Ewseq/Esseq/Eunseq/Ebound/End/Esave/Eif/Ecase`.

---

## 2. Shape correspondence table

Caesium stmt grammar for reference (lang.v:74-86, verbatim
constructor list): `Goto | Return | IfS | Switch | Assign | Free |
SkipS | StuckS | ExprS`; a `function` is `f_code : gmap label stmt`
with `f_init` (lang.v:90-95); every statement carries its successor
statement syntactically, so a block is a statement chain ending in
`Goto`/`Return`.

### Row 1 — straight-line assignment / arithmetic (`x = a + b;`)

**Caesium** (binary_search #0, verbatim, stripped):
```
"l" <-{ IntOp size_t } (UnOp (CastOp $ IntOp size_t) (IntOp i32) ((i2v 0 i32))) ;
"r" <-{ IntOp size_t } (use{IntOp size_t} (("n"))) ;
Goto "#1"
```
One C assignment = one `Assign` statement; the RHS (including reads
`use{ot}`) is a self-contained expression evaluated inside the
statement.

**Core** (p01_arith `x = a + b` twin; verbatim, seq+rewrite):
```
let strong a_511: loaded integer =
  bound(
    let weak a_512: loaded integer = load('signed int', a) in
    let weak a_513: loaded integer = load('signed int', b) in
    pure(
      case (a_512, a_513) of
        | (Specified(a_514: integer), Specified(a_515: integer)) =>
            Specified(catch_exceptional_condition_add('signed int', __conv_int__('signed int', a_514), __conv_int__('signed int', a_515)))
        | _: (loaded integer,loaded integer) =>
            undef(<<UB036_exceptional_condition>>)
      end
    )
  ) in
store('signed int', x, conv_loaded_int('signed int', a_511)) ;
```
Assignment *used as a statement* (later in the same proc, verbatim):
```
let strong _: loaded integer =
  bound(
    let weak a_519: pointer = pure(x) in
    …
    let weak _: unit =
      neg(store('signed int', a_519, conv_loaded_int('signed int', a_526))) in
    pure(conv_loaded_int('signed int', a_526))
  ) in
```

Notes (derived): one C **full expression** = one `Ebound(...)` node
whose result is `let strong`-bound (or `_`-discarded) on the
`Esseq` spine. Reads are `load` actions `let weak`-bound; operands
of every action are pure. UB checks (`case Specified/…`,
`catch_exceptional_condition_*`) are inline syntax; Caesium keeps
them in the opsem/WP lemmas. The C assignment-as-expression value
(`pure(conv_loaded_int …)` tail) is materialized even when
discarded. Statement boundary: **clean** — Caesium `Assign` ↔ Core
"one `Ebound` spine node + one `store`" (init-stores) or "one
`Ebound` containing the `neg(store…)`" (expression-statement
assignments); the two variants are systematic (declaration
initializers store outside the bound; assignment expressions store
inside it, negatively polarized).

### Row 2 — if/else and its condition

**Caesium** (t10_loops `loop_without_annot`, verbatim, stripped):
```
<[ "#1" :=
  if{IntOp i32, None}: (((use{IntOp i32} (("a")))) ={IntOp i32, IntOp i32, i32} ((i2v 1 i32)))
  then Goto "#2"
  else Goto "#3"
]> $
```
(`IfS` carries an *expression* condition and two statement
continuations; the optional label is an informational join marker —
`if{IntOp i32, Some "#4"}:` appears in paper_example_2_2's `free`.)

**Core** (p02_if `max2`; verbatim, trimmed):
```
let strong a_542: loaded integer =
  bound( …comparison, yielding Specified(1)/Specified(0)… ) in
let strong a_541: boolean =
  case a_542 of
    | Specified(a_543: integer) =>
        pure(if not(a_543 = 1) then True else False)
    | Unspecified(_: ctype) =>
        nd(pure(True), pure(False))
  end in
if a_541 then
  let strong a_557: loaded integer = bound(load('signed int', a)) in
  run ret_540(conv_loaded_int('signed int', a_557)) ;
  pure(Unit)
else
  let strong a_559: loaded integer = bound(load('signed int', b)) in
  run ret_540(conv_loaded_int('signed int', a_559)) ;
  pure(Unit) ;
save ret_540: loaded integer (a_560: loaded integer:= undef(<<UB088_reached_end_of_function>>)) in
  pure(a_560)
```

Notes (derived): Core pre-evaluates the condition **on the spine**
(one `Ebound` for the C expression + one `Ecase` truthiness
coercion, with `nd(True,False)` on Unspecified — nondeterminism in
statement position); `Eif`'s condition is grammar-forced pure. The
branches are spine segments; the code following the C `if` is the
`Esseq` continuation of the whole `Eif` (no join label is created —
contrast Caesium, where the frontend's block-splitting creates
`Goto` join blocks). Correspondence: identifiable but **not
node-to-node** — one Caesium `IfS` block ↔ a 3-segment Core pattern
(bound; truthiness-case; Eif).

### Row 3 — while loop (reverse.c, both sides from the same C)

**Caesium** (examples/proofs/reverse `impl_reverse`, verbatim,
stripped):
```
<[ "#0" := ("w") <-{ PtrOp } (NULL) ;
           ("v") <-{ PtrOp } (use{PtrOp} (("p"))) ;
           Goto "#1" ]> $
<[ "#1" := if{IntOp i32, None}: (((use{PtrOp} (("v")))) !={PtrOp, PtrOp, i32} ((NULL)))
           then Goto "#2" else Goto "#3" ]> $
<[ "#2" := ("t") <-{ PtrOp } (use{PtrOp} ((((!{PtrOp} (("v")))) at{struct_list} "tail"))) ;
           (((!{PtrOp} (("v")))) at{struct_list} "tail") <-{ PtrOp } (use{PtrOp} (("w"))) ;
           ("w") <-{ PtrOp } (use{PtrOp} (("v"))) ;
           ("v") <-{ PtrOp } (use{PtrOp} (("t"))) ;
           Goto "#1" ]> $
<[ "#3" := Return ((use{PtrOp} (("w")))) ]> $∅
```

**Core** (t_reverse twin, verbatim skeleton; bodies elided):
```
save while_524: unit (w: pointer:= w, t: pointer:= t, v: pointer:= v) in
  let strong a_531: loaded integer = bound( …v != NULL comparison… ) in
  let strong a_525: boolean = case a_531 of … end in
  if a_525 then
    …four assignment Ebound spine nodes…
    save continue_522: unit (w: pointer:= w, t: pointer:= t, v: pointer:= v) in
      pure(Unit) ;
    run while_524(w, t, v)
  else
    pure(Unit) ;
save break_523: unit (w: pointer:= w, t: pointer:= t, v: pointer:= v) in
  pure(Unit) ;
let strong a_565: loaded pointer = bound(load('struct list*', w)) in
…kills…
run ret_521(a_565) ;
```

Notes (derived): loop head = `Esave while_N` whose body is the
condition + `Eif`; back-edge = `Erun while_N(…)` *inside the save's
own body* (self-reference — Core loops are recursive saves).
Per C loop the elaborator emits a fixed label cluster:
`while_N` (head), `continue_M` (immediately before the back-edge;
emitted even when `continue` is unused, body `pure(Unit)`),
`break_K` (after the loop, body `pure(Unit)`). Save parameters
rebind the local pointer symbols (`w: pointer := w` — identity
defaults; `run` passes them back), i.e. saves are CFG blocks with
explicit block arguments. Correspondence to Caesium's #1/#2/#3
blocks is **direct**: while_N ↔ cond block #1, Eif-then segment ↔
body block #2, break_K ↔ exit block #3.

### Row 4 — for loop, break, continue

**Caesium**: no banked for/continue artifact; break artifact in
paper_example_2_2 `free` (C line 44 `if(sz <= (*cur)->size) break;`,
verbatim, stripped):
```
<[ "#2" := if{IntOp i32, Some "#4"}: (((use{IntOp size_t} (("sz")))) ≤{…} (…"size" field read…))
           then Goto "#5" else Goto "#6" ]> $
…
<[ "#5" := Goto "#3" ]> $        (* break → Goto loop-exit block *)
<[ "#6" := Goto "#4" ]> $        (* fallthrough → Goto rest-of-body *)
```
Frontend rules (ail_to_coq.ml, verbatim): `AilSbreak → (k_break ks, …)`
(:1082-1083), `AilScontinue → (k_continue ks, …)` (:1084-1085); a while's
translation sets `break = Some(goto_cont); continue =
Some(locate (Goto(id_cond)))` (:1257-1258). So break = `Goto`
exit-block, continue = `Goto` cond-block. C `for` is desugared
**before their frontend runs**: cabs_to_ail.lem:3954 rebuilds for
as `AilSwhile` (shared with our pipeline).

**Core** (p04_for, `for (int i = 0; i < n; i++)`, verbatim
skeleton):
```
save while_515: unit (i: pointer:= i, s: pointer:= s) in
  …cond bound + truthiness case… in
  if a_516 then
    …body assignment… in
    save __cerb_continue0: unit (i: pointer:= i, s: pointer:= s) in
      let strong _: loaded integer = bound( seq_rmw('signed int', i, a_543 => …) ) in
      pure(Unit) ;
    save continue_513: unit (i: pointer:= i, s: pointer:= s) in  pure(Unit) ;
    run while_515(i, s)
  else
    pure(Unit) ;
save break_514: unit (i: pointer:= i, s: pointer:= s) in  pure(Unit) ;
```
Core break/continue (p03_while, verbatim single lines):
```
run __cerb_continue0(s, i) ;        (* C continue *)
if a_533 then run break_514(s, i) else pure(Unit) ;   (* C break *)
```

Notes (derived): `__cerb_continueN` is a **cabs→Ail** label
(cabs_to_ail.lem:3787,3961 — freshified `__cerb_continue`
identifier planted at the body end; for-loops put the increment in
its block), distinct from the Ail→Core `continue_M`; both appear,
chained. `i++` becomes a dedicated `seq_rmw` action. C `break` in
statement position elaborates as `Eif(cond, Erun break_K, pure
Unit)` — the same run-to-forward-save shape as early return.
Correspondence: Caesium break/continue `Goto`s ↔ Core `Erun`s to
the same three-way label cluster; **uniform on both sides**.

### Row 5 — goto and labels

**Caesium** (mpool generated_code.v:1232,1283; C `goto exit;`):
```
Goto "exit"
…
<[ "exit" := … ]>
```
(C label names become block ids; frontend `AilSgoto(l) →
Goto(sym_to_str l)` ail_to_coq.ml:1076-1078.)

**Core** (p05_goto, verbatim skeleton):
```
save loop: unit (s: pointer:= s, i: pointer:= i) in
  …cond… ;
  if a_512 then run done(s, i) else pure(Unit) ;
  …body… ;
run loop(s, i) ;
save done: unit (s: pointer:= s, i: pointer:= i) in
  …load s; kills; run ret_511(…)… ;
```
Notes (derived): C label ↔ one `Esave` (name preserved); goto ↔
`Erun` — backward (into an enclosing/preceding save's body:
`run loop`) or forward (to a later spine save: `run done`) alike.
Exactly one save per C label; **clean 1:1 with Caesium's
block-map entries.**

### Row 6 — return / early return / fall-off-end

**Caesium**: `Return (expr)` statement; every generated block chain
ends in `Goto` or `Return`; void return is `Return (VOID)`
(paper_example_2_2 `free` #3, verbatim). No fall-through exists in
the block representation.

**Core**: one function-wide return label; value functions
(p01, verbatim):
```
run ret_510(conv_loaded_int('signed int', a_533)) ;
kill('signed int', x) ;
pure(Unit) ;
save ret_510: loaded integer (a_534: loaded integer:= undef(<<UB088_reached_end_of_function>>)) in
  pure(a_534)
```
void functions (p09 `setsnd`, verbatim):
```
save ret_513: unit (a_522: unit:= Unit) in  pure(a_522)
```
Early return (p02 `early`, verbatim):
`if a_512 then run ret_511(conv_loaded_int('signed int', Specified(0))) else pure(Unit) ;`

Notes (derived): `return e` ↔ `Erun ret_N(v)`; the proc tail is
`Esave ret_N` whose parameter default is `undef(UB088)` for value
functions (fall-off-end = UB via the default) and `Unit` for void.
The spine text after a `run ret_N` (duplicate `kill`s, `pure(Unit)`)
is unreachable elaboration residue — see §3(v). Correspondence:
clean, modulo the residue.

### Row 7 — function calls (incl. void call)

**Caesium**: `Call` is an **expression** (lang.v:36), usable in any
expression position — condition (binary_search #2, verbatim,
stripped):
```
if{BoolOp, None}: (Call ((use{PtrOp} (("comp")))) [@{expr} (use{PtrOp} ((((!{PtrOp} (("xs")))) at_offset{void*, PtrOp, IntOp size_t} ((use{IntOp size_t} (("k"))))))) ; (use{PtrOp} (("x"))) ])
then Goto "#4" else Goto "#5"
```
return position (reverse :422 `Return ((Call ((global_member_rec)) […]))`),
assignment RHS (reverse :541), and void-call statement via `ExprS`
(spinlock :226, verbatim, stripped):
`expr: ((Call ((global_sl_lock)) [@{expr} (use{PtrOp} (("a"))) ])) ;`

**Core** (p06_call `noop();` void call, verbatim):
```
bound(
  let (a_515: ctype, a_516: [ctype], _: boolean, _: boolean) =
    cfunction(Specified(Cfunction(noop))) in
  if params_length(a_516) = 0 then
    if are_compatible ('void', a_515) then
      ccall('void (*) (void)', Specified(Cfunction(noop)))
    else
      pure(undef(<<UB041_function_not_compatible>>))
  else
    pure(undef(<<UB038_number_of_args>>))
) ;
```
Value call with argument (p06 `inc(a)`, verbatim, trimmed):
```
let strong a_524: pointer =
  let a_527: ctype = params_nth(a_521, 0) in
  if not(are_compatible ('signed int', a_527)) then
    pure(undef(<<UB041_function_not_compatible>>))
  else
    let weak a_528: pointer = create(Ivalignof('signed int'), 'signed int') in
    let weak _: unit = store('signed int', a_528, conv_loaded_int('signed int', a_525)) in
    pure(a_528) in
let strong a_529: loaded integer = ccall('signed int (*) (signed int)', a_519, a_524) in
kill('signed int', a_524) ;
pure(a_529)
```

Notes (derived): one C call ↔ a Core pattern of
`cfunction`-metadata lookup + arity/compatibility UB checks +
**per-argument `create/store` of a fresh block** + `Eccall` +
per-argument `kill`. Caesium's `Call` is one node whose opsem does
argument allocation (`wp_call`, lifting.v:1046); Core spells it in
syntax. The call itself (`Eccall`) has pure operands — the function
and args are already values. Statement-boundary correspondence:
clean at the full-expression level (the whole call chain is inside
the statement's `Ebound`), but a Caesium `Call`-in-condition
(binary_search) corresponds to the call chain hoisted *before* the
Core `Eif`, inside the condition's own bound — expression-position
calls do not survive as expression-position in Core.

### Row 8 — local declarations (with and without initializer)

**Caesium**: no declaration statement exists. Locals appear as
`f_local_vars : list (var_name * layout)` (whole function, one
allocation lifetime, allocated by the opsem at call); an initializer
becomes an ordinary leading `Assign` (binary_search: `"l"`, `"r"`
initialized in #0; uninitialized `"k"` merely listed and assigned in
block #2).

**Core** (p07_decls, verbatim):
```
let strong a: pointer = create(Ivalignof('signed int'), 'signed int') in
let strong b: pointer = create(Ivalignof('signed int'), 'signed int') in
store('signed int', a, Unspecified('signed int')) ;
store('signed int', b, conv_loaded_int('signed int', Specified(5))) ;
…
kill('signed int', a) ;
kill('signed int', b) ;
```

Notes (derived): every C local ↔ `create` action binding a pointer
symbol + explicit `store` (initializer value, or literal
`Unspecified(τ)` when uninitialized) + `kill` at scope exit.
**Lifetimes diverge**: Caesium hoists all locals to function scope;
Core is block-scoped — in t_binary_search, loop-local `k` is
`create`d/`kill`ed *inside* the `while_530` save body (lines 49,
233 of the output), i.e. re-allocated per iteration. No clean
per-statement correspondence for the declaration itself (Caesium
side has no node at all for the uninitialized case).

### Row 9 — address-of / deref places

**Caesium** (reverse :635,:653, verbatim, stripped):
```
"prev" <-{ PtrOp } (&(("p"))) ;
… (&(((!{PtrOp} (("cur")))) at{struct_list} "tail")) …
```
Deref-as-place: `!{PtrOp} e`; a place is a first-class expression
subtree (`Var/Deref/GetMember` chains) consumed by
`Assign`/`use` — this is what `find_place_ctx` walks.

**Core** (p08_ptr, verbatim): address-of a local is just the
pointer value — `store('signed int*', r, Specified(t))` for
`int *r = &t;` (no operator at all); deref-for-read is a chain:
```
let weak a_513: loaded pointer = load('signed int*', p) in
let weak a_517: pointer =
  case a_513 of
    | Specified(a_514: pointer) =>
        let weak a_515: boolean = memop(PtrValidForDeref, 'signed int', a_514) in
        pure(if a_515 then a_514 else undef(<<UB043_indirection_invalid_value>>))
    | Unspecified(_: ctype) =>
        pure(undef(<<UB043_indirection_invalid_value>>))
  end in
load('signed int', a_517)
```

Notes (derived): Core has **no place syntax**. L-value evaluation is
ordinary value computation: loads of pointer variables, a
`PtrValidForDeref` memop guard, `member_shift`/`array_shift` pure
offset ops — ending in a pointer value fed to `load`/`store`. The
`&` of an l-value simply *stops before the final load*. Caesium's
syntactic place contexts (Deref/GetMember stacks) have no
counterpart object.

### Row 10 — struct field access

**Caesium** (reverse `push`, verbatim, stripped):
```
(((!{PtrOp} (("node")))) at{struct_list} "head") <-{ PtrOp } (use{PtrOp} (("e"))) ;
```
Array index: `at_offset{void*, PtrOp, IntOp size_t}` (binary_search
#2, quoted in row 7).

**Core** (p09_struct `getfst`, verbatim):
```
let weak a_530: pointer =
  let strong a_525: loaded pointer = load('struct pair*', p) in
  case a_525 of
    | Unspecified(_: ctype) =>
        pure(undef(<<UB_CERB004_unspecified__memberofptr>>))
    | Specified(a_526: pointer) =>
        pure(member_shift(a_526, pair, .fst))
  end in
load('signed int', a_530)
```
Array index (t_binary_search, verbatim, trimmed):
`pure(Specified(array_shift(a_591, 'void*', a_593)))` under a
`case (a_590, a_592) of (Specified…, Specified…)` guard.

Notes (derived): `e at{sl} f` ↔ `member_shift(v, tag, .f)` (pure,
after loading/guarding the base pointer); `at_offset` ↔
`array_shift`. Same shape as row 9: pure pointer arithmetic on
values, no syntactic place.

### Row 11 — expression-statements and skips

**Caesium**: `ExprS e s` (spinlock row 7); annotation statements are
`AnnotStmt = Nat.iter n SkipS` (notation.v:109) — `annot: (UnlockA)`
in paper_example_2_1 :291.

**Core**: an expression statement is a `let strong _ : τ =
bound(…) in` spine node (rows 1,7); discarded scalar statements can
leave a literal `pure(Unit) ;` filler (p01 un-rewritten; the
rewrite pass drops some). No annotation carrier exists in elaborated
plain-C Core (consistent with port map agenda item 15).

---

## 3. Findings (evidence only, addressed to the design question)

### (i) Is there an identifiable "statement position" grammar?

**Yes — sharply.** In every artifact, the proc body decomposes into
an `Esseq` spine (`;` / `let strong`) whose nodes are drawn from a
small closed set:

1. `create`/`store`/`kill` actions (declarations, initializers,
   scope exits);
2. `let strong x/_ = Ebound(…) in` — exactly one per C full
   expression (assignment, call, condition evaluation, returned
   expression);
3. truthiness coercion `let strong b: boolean = case … end in`
   (paired with every C condition);
4. `Eif b then <spine> else <spine>` with pure condition and spine
   segments as branches;
5. `Esave L(params) in <spine>` and `Erun L(args)`;
6. `pure(Unit)` fillers.

Statement boundaries in the Caesium output correspond to
identifiable spine segments in all 12 artifacts examined; no
counterexample was found. The one systematic wrinkle: the spine is
not purely unit-typed — `let strong` nodes bind values consumed by
later spine nodes (condition results, return values), so a
"statement view" targeting the spine must handle value-binding
spine nodes, not just unit `;` nodes. Second wrinkle: the mapping
is segment-to-statement, not node-to-statement (a C `if` costs
2 spine nodes of condition evaluation + the `Eif`).

### (ii) What do loops/goto/break/return map to?

**All control transfer is save/run — and only save/run.** Observed
label inventory, uniform across p03/p04/p05/t_reverse/
t_binary_search:

- per C loop: `while_N` (head; **back-edge = `run while_N` inside
  its own save body**, i.e. loops are self-referential saves — no
  fixpoint/rec construct appears), `continue_M` (just before the
  back-edge; emitted even when unused), `break_K` (loop exit),
  plus `__cerb_continueX` when the cabs→Ail desugar plants it (for
  loops: holds the increment; whiles with `continue`: an alias
  hop);
- per C label: exactly one `Esave` with the C name (`loop`, `done`,
  `exit`); `goto` = `Erun`, forward or backward identically;
- per function: exactly one `ret_N` save at the spine tail; every
  `return` = `Erun ret_N(v)`; fall-off-end = the save's default
  parameter (`undef(UB088)` value fns / `Unit` void fns);
- `break`/`continue` = `Erun` to the cluster labels.

So there is **one save per C join point** (loop head, loop exit,
continue point, label, return) — the same set of points at which
RefinedC's frontend cuts Caesium blocks. Saves carry explicit
parameter lists rebinding the live local pointers (identity
defaults, args passed back at `run` — block-argument style). The
Caesium `f_code : gmap label stmt` ↔ Core save-set correspondence
is essentially bijective on these artifacts, with two deltas:
Core's saves are nested in one expression tree (a save's body is
entered by fall-through as well as by `run`), and Caesium blocks
have no fall-through.

### (iii) Uniformity

**High.** The same C construct produced the same Core template in
every occurrence across all probes and twins (derived tally:
assignment template ×10+ occurrences over 6 files; condition
template ×8; loop cluster ×5; call template ×4): identical node
patterns, differing only in fresh names/types. Two sources of
variance, both systematic and predictable from the C: (a)
declaration-initializer stores vs expression-assignment stores (row
1 note); (b) presence of `__cerb_continueX` (cabs-level, keyed on
loop kind/continue usage). The `--rewrite` pass changes only alias
inlining and dead fillers; shapes are stable across
rewrite/no-rewrite.

### (iv) Bind-layer-dissolution hypothesis (agenda item 16)

The evidence is strongly supportive, and the strongest fact is
**grammatical, not empirical**: in Core's grammar itself
(core.lem:319-343) every operand of every action, memop, call,
run, if-condition, and case-scrutinee is a `pexpr` — syntactically
pure. Effects occur only as bodies of the sequencing constructs.
Sequentialised elaborated Core is thus already in monadic
normal form: **the redex position is always the head of the
let-chain**, and "evaluation contexts" degenerate to the sequencing
skeleton (`Ewseq`/`Esseq`/`Ebound` left-spines, descending into
right-nested RHS chains such as
`let weak a_549 = (let weak a_548 = …case… in load(…)) in …`,
t_reverse). Nothing like Caesium's `find_expr_fill` (searching an
arbitrary expression tree for the active subexpression, with
`W.ectx_item` stacks) is needed to locate a redex; the counterpart
obligation is at most "step through nested binds", plus `Ecase`
scrutiny of `Specified/Unspecified` values.

Corollary observed for the place machinery (the other half of item
16): Caesium's `find_place_ctx`/`IntoPlaceCtx` walk syntactic
l-value trees (`W.Deref`/`W.GetMember`…); Core has **no l-value
syntax to walk** — places are computed as pointer values by
ordinary spine steps (rows 9-10). Whatever plays `typed_place` over
Core cannot be syntax-directed over a place tree, because the tree
does not exist post-elaboration; the information is spread over
prior `load`/`member_shift` steps. (Evidence statement only; the
design consequence is for the attachment conversation.)

Caveats (evidence against over-claiming): (a) `Eunseq` is removed
only *by the `--sequentialise` pass* — the pass choice is a
semantic commitment (port map item 17), not a property of Core;
(b) `Ebound`, `End` (`nd(…)` in every condition on Unspecified),
and negative-polarity actions (`neg(store…)` — "only sequenced by
letstrong", pp_core.ml:230) remain in the sequentialised form and
sit exactly where a WP would bind; they are sequencing-adjacent
constructs Caesium has no analog of.

### (v) Surprises

1. **The two pipelines are cousins, not strangers.** RefinedC's
   frontend translates Cerberus **Ail** (ail_to_coq.ml matches
   `AilS*`); both sides inherit cabs→Ail desugaring (`for`→while at
   cabs_to_ail.lem:3954; the `__cerb_continue` label planted there
   surfaces verbatim as a Core save name). The near-bijection of
   join points in (ii) is partially explained: both lowerings cut
   the same Ail statements.
2. **CN's exact Core form is reproducible**: `deps/cn/lib/setup.ml:
   33-35` = `--rewrite --sequentialise` (+typecheck). The study's
   quoted form is that form.
3. **UB inflation is the dominant size asymmetry.** One Caesium
   `Assign`/`Call` node ↔ 10-40 Core nodes, almost all of it
   inline UB checking (Specified/Unspecified cases,
   `catch_exceptional_condition_*`, `PtrValidForDeref`,
   `params_length`/`are_compatible` at every call) that Caesium
   keeps inside its opsem and per-construct WP lemmas. A statement
   view over Core faces per-construct *patterns*, not
   per-construct *constructors*.
4. **Unreachable residue**: after every `run ret_N` the spine
   repeats the `kill`s (+`pure(Unit)`) unreachably
   (p01/p04/p07/p08); harmless but a view must not choke on dead
   spine tails.
5. **Local lifetimes genuinely diverge** (row 8): Caesium =
   function-scope allocation of all locals at call; Core =
   block-scope `create`/`kill`, re-created per loop iteration for
   loop-local variables (t_binary_search `k`).
6. **Nondeterminism in statement position**: every C condition
   carries `nd(pure(True), pure(False))` for the Unspecified case,
   and negative-polarity actions annotate stores inside
   full-expression bounds — ND/polarity artifacts survive
   sequentialisation.
7. `i++` elaborates to a dedicated `seq_rmw` read-modify-write
   action (p04) — an action species with no Caesium counterpart
   (their frontend emits a read + `Assign`).
8. Uninitialized C locals get an explicit
   `store(τ, x, Unspecified(τ))` (p07) — indeterminate value as a
   stored value, where Caesium leaves the fresh block's bytes
   `poison` with no statement at all.

---

## 4. Artifact index

- Probe sources + Core outputs: `/tmp/claude-1000/shape-study/`
  (`pNN_*.c`, `t_*.c`, `*.seq_rw.core`, plus `p01_seq.core` /
  `p01_noseq.core` for the sequentialise diff). Ephemeral per
  container doc practice; every quote needed by this doc is inline
  above.
- Caesium artifacts: banked `generated_code.v` files under
  `.refinedc-ws/examples/proofs/` and `tutorial/proofs/` (cited per
  row); nothing was regenerated, no writes to the workspace.
