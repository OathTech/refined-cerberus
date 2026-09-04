# Measurement: what Core the pinned Cerberus emits for two tiny C programs, against the fragment

Orchestrator [AGENT], 2026-09-04. Trigger: [USER 2026-09-04] "one question is whether the demo's list of constructs could actually support a compiled C program? … C programs just do a lot of stuff, even very simple C programs." Method: `cerberus-lean/_build/default/backend/driver/main.exe --nolibc --pp=core` (the pinned OCaml oracle build, `scripts/ce`), verbatim output below; construct tallies DERIVED by `grep -o … | wc -l` over the emitted `proc`/`fun` bodies (std/impl definitions excluded).

## t1.c
```c
int main(void) { int x = 3; int y = x + 1; return y; }
```
```
proc main (): eff loaded integer :=
  let strong x: pointer = create(Ivalignof('signed int'), 'signed int') in
  let strong y: pointer = create(Ivalignof('signed int'), 'signed int') in
  let strong a_508: loaded integer = bound(pure(Specified(3))) in
  store('signed int', x, conv_loaded_int('signed int', a_508)) ;
  let strong a_509: loaded integer =
    bound(
      let weak (a_510: loaded integer, a_511: loaded integer) =
        unseq(
          let weak a_515: pointer = pure(x) in
          load('signed int', a_515)
        ,
          pure(Specified(1))
        ) in
      pure(
        case (a_510, a_511) of
          | (Specified(a_512: integer), Specified(a_513: integer)) =>
              Specified(catch_exceptional_condition_add('signed int', __conv_int__('signed int', a_512), __conv_int__('signed int', a_513)))
          | _: (loaded integer,loaded integer) =>
              undef(<<UB036_exceptional_condition>>)
        end
      )
    ) in
  store('signed int', y, conv_loaded_int('signed int', a_509)) ;
  let strong a_517: loaded integer =
    bound(
      let weak a_516: pointer = pure(y) in
      load('signed int', a_516)
    ) in
  kill('signed int', x) ;
  kill('signed int', y) ;
  run ret_507(conv_loaded_int('signed int', a_517)) ;
  kill('signed int', x) ;
  kill('signed int', y) ;
  pure(Unit) ;
  save ret_507: loaded integer (a_518: loaded integer:= Specified(0)) in
    pure(a_518)

```

## t2.c
```c
int add(int a, int b) { return a + b; }
int main(void) { int s = 0; for (int i = 0; i < 3; i++) { s = add(s, i); } return s; }
```
Tally over the emitted bodies of t2 (DERIVED):
```
unseq=6
bound=7
save =6
run =3
ccall=1
pcall=0
create(=4
store(=5
load(=6
kill(=5
conv_int=8
wrapI=0
catch_exceptional_condition=2
is_representable=0
array_shift=0
member_shift=0
case =5
if =8
let weak=16
let strong=16
memop=0
annot=0
Specified=20
nd(=8
pure(=42
```

## Against the fragment (23 constructors: `alloc alloc_op annot call case_value create if_ kill kill_op load load_op memop_op memop_vals pure_sym run save sseq sseq_spec sseq_sym store store_op val_pure wseq`)

Already in the fragment (modulo operand grammar): `create`, `store`, `load`,
`kill`, `let strong` (sseq), `let weak` (wseq), `save`/`run`, `if`, `case`
at a value, `pure`.

NOT in the fragment, used by even t1 (`int x = 3; int y = x + 1; return y;`):
- `bound(…)` around every full expression;
- `unseq(…)` for operand evaluation (two-way here; n-way in general);
- PURE CALLS to std.core/impl Core functions for every arithmetic operation
  and conversion: `__conv_int__`, `catch_exceptional_condition_add`,
  `conv_loaded_int` (the fragment's `PePure` operand grammar has no
  `PEcall`);
- LOADED values (`loaded integer`, `Specified(_)`, `undef(UB…)` arms) as the
  currency of every load/store/arithmetic — the fragment's cells are stated
  at object values;
- `Ivalignof('signed int')` as the `create` alignment operand (a pure
  constant the mirror must evaluate);
- `case` on TUPLE patterns of loaded values with a wildcard `undef` arm.
Used by t2 in addition: `ccall` — the DIRECT C call `add(s, i)` elaborates
to `Eccall` (one occurrence, the one call), i.e. the scheduler-round path
the Lane C note assigns to function pointers is the path of EVERY C
function call; `nd(…)` (8 occurrences) in the loop/branch desugaring.

Conclusion [AGENT]: lifting the annotation restriction alone does not
reach "a compiled C program"; the gap is the emitted-Core dialect —
`Ebound`, `Eunseq`, pure impl/std calls with the impl-defined integer
semantics, loaded values, `Eccall` for calls, `nd`. That is the layer's
fragment-growing programme (the Lane C note's L-slices), not a demo
pre-v1 slice. The demo's version one stays authored Core; the emitted-Core
acceptance test ("a C program elaborated by the pinned pipeline,
unmodified, certified end to end") is the LAYER's, and each of the six
gaps above is one measured slice of it. The located-Core (annotation)
lifting is still the first of them, because every later slice needs it.
