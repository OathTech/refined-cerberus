# Eunseq census over elaborated C (empirical recon)

Date: 2026-08-30. Provenance: [AGENT: arc-2 empirical recon worker],
dispatched under [USER 2026-08-30]'s motivating question (verbatim):
"Do we actually need to sequentialize? I would have thought that for
C code, most of the unseq effects collapse locally." Hypothesis under
test (stated in the brief, not decided here): Eunseq can be handled
by a disjoint-footprint separation-logic rule (arms have separated
footprints ⇒ any interleaving; race-freedom as side condition)
instead of wiring the Core_sequentialise pass — provided elaborated
C's Eunseq nodes are locally small. **This document is evidence
only; no design.** Verbatim quotes are labeled; all tallies are
derived (mechanical classifier + hand spot-verification, method
below). Companion docs: `2026-08-30_caesium-core-shape-study.md`
(§1 method + pretty-printer key, reused here);
`2026-08-30_relational-semantics-candidates.md` §2.5/§6 (the α/β
sequentialisation decision this feeds).

---

## 1. Method

### 1.1 Pipeline

Same driver as the shape study, with `--sequentialise` DROPPED for
the census lane and kept for the comparison lane. Exact commands
(verbatim, run per probe from `/tmp/claude-1000/eunseq-census/`):

```
CERB=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_build/default/backend/driver/main.exe
RT=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_build/install/default
$CERB --runtime=$RT --pp=core --rewrite <file.c>                    # census lane
$CERB --runtime=$RT --pp=core --rewrite --sequentialise <file.c>    # comparison lane
```

All 23 probes × both lanes exit 0 with empty stderr.

### 1.2 Corpus

The shape study's scratch dir survived; its 12 sources were copied
unchanged (`p01_arith` … `p09_struct`, `t_wrapping_add`, `t_reverse`,
`t_binary_search` — described in that doc §1.3). Eleven new probes
were written for this census (verbatim sources, recorded here because
the scratch is ephemeral):

```c
/* u01_mularith_local.c */
int f(int x, int y, int z) { int r = x*y + y*z; return r; }
/* u02_mularith_global.c */
int gx, gy, gz;
int f(void) { int r = gx*gy + gy*gz; return r; }
/* u03_assign_multiread.c */
int f(int a, int b, int c) { int r; r = a + b - c * a; return r; }
/* u04_ptr_operands.c */
int f(int *p, int *q) { return *p + *q; }
/* u05_array_struct.c */
struct s { int x; int y; };
int g(struct s *sp) { return sp->x + sp->y; }
int f(int *a, int i, int j) { return a[i] + a[j]; }
/* u06_call_operands.c */
int f(int x); int g(int y);
int h(int x, int y) { return f(x) + g(y); }
/* u07_nested_calls.c */
int g(void); int h(void); int f(int a, int b);
int top(void) { return f(g(), h()); }
/* u08_compound_assign.c */
int f(int x, int *p) { x += *p; return x; }
/* u09_incr_index.c */
int f(int *a, int i) { return a[i++]; }
/* u10_everyday.c */
int max(int a, int b) { return a > b ? a : b; }
int sum_sq(int *a, int n) {
  int s = 0;
  for (int i = 0; i < n; i++) { s += a[i] * a[i]; }
  return s;
}
void swap(int *p, int *q) { int t = *p; *p = *q; *q = t; }
/* u11_multiarg_call.c */
int f3(int a, int b, int c);
int caller(int x, int y) { return f3(x + 1, y * 2, x - y); }
```

(u10's sources are multi-line in the scratch file; the semicolon
compression above is presentational only — bodies identical.)

### 1.3 Census tooling (derived-data disclosure)

Per-node data was extracted by a python pass over the census-lane
pretty-printer output: each `unseq(` occurrence was paren-matched to
find its top-level arms (arity), the nearest preceding
`let weak/strong` binder recorded, and each arm classified by
content markers (`ccall` ⇒ ccall-chain; `seq_rmw` ⇒ rmw; leading
`kill(` ⇒ kill; no `load`/`memop` ⇒ pure; one `load`, no nesting ⇒
single-load; otherwise load-chain; `+Nnested-unseq`/`+memop`/
`+cfn-lookup` annotations added). Every template class was verified
by eye against full pretty-printer output for at least two instances
(quoted in §3); classifications for structurally identical nodes are
mechanical. A second pass verified the inside-`bound(…)` property by
paren-tracking every `bound(` region. All scripts + outputs:
`/tmp/claude-1000/eunseq-census/` (ephemeral; everything load-bearing
is inline here).

---

## 2. The census

### 2.1 Headline numbers (derived)

- **98 Eunseq nodes** across 23 files; **201 arms** total.
- **Arity**: 94 nodes binary; 3 ternary (2-arg calls: designator +
  2 arms; and comp-call in t_binary_search); 1 quaternary
  (3-arg call u11). Maximum observed arity = 4 = 1 + #args of the
  widest call. Arithmetic/assignment unseqs are ALWAYS binary — wide
  C expressions elaborate as nested binary unseq trees mirroring the
  operator tree, not flat n-ary nodes.
- **Enclosing construct**: 98/98 nodes lie inside an `Ebound(…)`
  (checked mechanically) — i.e. within one C full expression's
  bound. **No Eunseq spans a statement boundary**, ever, in this
  corpus.
- **Binder position**: 98/98 nodes sit in `Ewseq`/`Esseq` HEAD
  position under a tuple pattern (`let weak (a,b,…) = unseq(…) in`
  ×88, `let strong (…) = unseq(…) in` ×10). Independent
  confirmation: the sequentialise pass rewrites exactly this shape
  and warns-and-skips anything else (§4), and the comparison lane
  has **zero residual unseq in all 23 files** — the pass's
  best-effort coverage is 100% on this corpus.
- **Arm classification** (201 arms, derived tally):

  | arm class | count | % |
  |---|---|---|
  | single load | 84 (+1 fn-ptr-load designator) | 42% |
  | pure (incl. 6 pure fn-designator lookups) | 50 | 25% |
  | load chain (loads + pure guards/shifts ± `memop` validity queries, incl. nested unseq) | 53 | 26% |
  | kill (post-call argument-slot cleanup) | 7 | 3.5% |
  | ccall chain (create/store/ccall/kill of fresh arg slots) | 5 | 2.5% |
  | seq_rmw (`i++` as operand) | 1 | 0.5% |
  | plain store | **0** | 0% |

  **185/201 arms (92%) are read-only + pure** (loads, pointer-
  validity memops, pure shifts/conversions/UB-cases). The write
  species inside arms are exactly: the 5 ccall chains (writes
  confined to freshly `create`d argument slots + whatever the callee
  does), the 7 kills (each of a distinct fresh argument slot), and
  the 1 `seq_rmw`. **A bare `store` never appears as arm content**:
  every C assignment's store is sequenced AFTER the unseq join
  (§3 T2).

### 2.2 Per-node listing (derived, mechanical; file:line of the census-lane output)

```
p01_arith:6    a2 weak  [single-load, single-load]
p01_arith:20   a2 weak  [pure(lvalue), load-chain+1u]          (assign)
p01_arith:24   a2 weak  [single-load, pure]
p01_arith:42   a2 weak  [single-load, pure]
p02_if:5       a2 weak  [load-chain+1u, pure]
p02_if:7       a2 weak  [single-load, single-load]
p02_if:57      a2 weak  [load-chain+1u, pure]
p02_if:59      a2 weak  [single-load, pure]
p02_if:101     a2 weak  [pure(lvalue), load-chain+1u]          (assign)
p02_if:105     a2 weak  [single-load, pure]
p03_while:10   a2 weak  [load-chain+1u, pure]
p03_while:12   a2 weak  [single-load, single-load]
p03_while:51   a2 weak  [load-chain+1u, pure]
p03_while:53   a2 weak  [single-load, pure]
p03_while:93   a2 weak  [pure(lvalue), load-chain+1u]          (assign)
p03_while:97   a2 weak  [single-load, pure]
p03_while:119  a2 weak  [load-chain+1u, pure]
p03_while:121  a2 weak  [single-load, pure]
p03_while:161  a2 weak  [pure(lvalue), load-chain+1u]          (assign)
p03_while:165  a2 weak  [single-load, single-load]
p03_while:182  a2 weak  [pure(lvalue), load-chain+1u]          (assign)
p03_while:186  a2 weak  [single-load, pure]
p04_for:10     a2 weak  [load-chain+1u, pure]
p04_for:12     a2 weak  [single-load, single-load]
p04_for:51     a2 weak  [pure(lvalue), load-chain+1u]          (assign)
p04_for:55     a2 weak  [single-load, single-load]
p05_goto:10    a2 weak  [load-chain+1u, pure]
p05_goto:12    a2 weak  [single-load, single-load]
p05_goto:51    a2 weak  [pure(lvalue), load-chain+1u]          (assign)
p05_goto:55    a2 weak  [single-load, single-load]
p05_goto:72    a2 weak  [pure(lvalue), load-chain+1u]          (assign)
p05_goto:76    a2 weak  [single-load, pure]
p06_call:8     a2 weak  [single-load, pure]
p06_call:40    a2 strong [pure+cfn, single-load]               (call args)
p06_call:74    a2 strong [pure+cfn, single-load]               (call args)
p07_decls:9    a2 weak  [pure(lvalue), single-load]            (assign)
p08_ptr:27     a2 weak  [load-chain+memop(lvalue), load-chain+memop] (assign)
p08_ptr:67     a2 weak  [load-chain+memop(lvalue), single-load]      (assign)
p09_struct:28  a2 weak  [single-load(lvalue chain), single-load]     (assign)
t_binary_search:15  a2 weak  [load-chain+1u, pure]
t_binary_search:17  a2 weak  [single-load, single-load]
t_binary_search:56  a2 weak  [single-load, load-chain+2u]
t_binary_search:60  a2 weak  [load-chain+1u, pure]
t_binary_search:62  a2 weak  [single-load, single-load]
t_binary_search:123 a2 weak  [ccall-chain+3u+memop+cfn, pure]  (call in condition)
t_binary_search:127 a3 strong [fnptr-load+cfn, load-chain+1u+memop, single-load] (call args)
t_binary_search:133 a2 weak  [single-load, single-load]
t_binary_search:186 a2 strong [kill, kill]                     (post-call kills)
t_binary_search:215 a2 weak  [pure(lvalue), load-chain+1u]     (assign)
t_binary_search:219 a2 weak  [single-load, pure]
t_binary_search:246 a2 weak  [pure(lvalue), single-load]       (assign)
t_reverse:25   a2 weak  [pure(lvalue), single-load]            (assign)
t_reverse:33   a2 weak  [load-chain+memop, pure]
t_reverse:69   a2 weak  [pure(lvalue), load-chain]             (assign)
t_reverse:88   a2 weak  [single-load(lvalue chain), single-load] (assign)
t_reverse:105  a2 weak  [pure(lvalue), single-load]            (assign)
t_reverse:112  a2 weak  [pure(lvalue), single-load]            (assign)
t_wrapping_add:9  a2 weak [single-load, load-chain+1u]
t_wrapping_add:13 a2 weak [single-load, single-load]
u01_mularith_local:6  a2 weak [load-chain+1u, load-chain+1u]
u01_mularith_local:8  a2 weak [single-load, single-load]
u01_mularith_local:20 a2 weak [single-load, single-load]
u02_mularith_global:23 a2 weak [load-chain+1u, load-chain+1u]
u02_mularith_global:25 a2 weak [single-load, single-load]
u02_mularith_global:37 a2 weak [single-load, single-load]
u03_assign_multiread:7  a2 weak [pure(lvalue), load-chain+3u]  (assign)
u03_assign_multiread:11 a2 weak [load-chain+1u, load-chain+1u]
u03_assign_multiread:13 a2 weak [single-load, single-load]
u03_assign_multiread:24 a2 weak [single-load, single-load]
u04_ptr_operands:5   a2 weak [load-chain+memop, load-chain+memop]
u05_array_struct:11  a2 weak [load-chain, load-chain]
u05_array_struct:49  a2 weak [load-chain+1u+memop, load-chain+1u+memop]
u05_array_struct:51  a2 weak [single-load, single-load]
u05_array_struct:76  a2 weak [single-load, single-load]
u06_call_operands:9  a2 weak [ccall-chain+1u+cfn, ccall-chain+1u+cfn]  (f(x)+g(y))
u06_call_operands:13 a2 strong [pure+cfn, single-load]         (call args)
u06_call_operands:45 a2 strong [pure+cfn, single-load]         (call args)
u07_nested_calls:13  a3 strong [pure+cfn, ccall-chain+cfn, ccall-chain+cfn] (f(g(),h()))
u07_nested_calls:65  a2 strong [kill, kill]                    (post-call kills)
u08_compound_assign:5 a2 weak [pure(lvalue), load-chain+1u+memop]  (x += *p)
u08_compound_assign:9 a2 weak [single-load, load-chain+memop]
u09_incr_index:5     a2 weak [single-load, rmw]                (a[i++])
u10_everyday:6   a2 weak [load-chain+1u, pure]
u10_everyday:8   a2 weak [single-load, single-load]
u10_everyday:60  a2 weak [load-chain+1u, pure]
u10_everyday:62  a2 weak [single-load, single-load]
u10_everyday:101 a2 weak [pure(lvalue), load-chain+4u+memop]   (assign s+=…)
u10_everyday:105 a2 weak [single-load, load-chain+3u+memop]
u10_everyday:109 a2 weak [load-chain+1u+memop, load-chain+1u+memop]
u10_everyday:111 a2 weak [single-load, single-load]
u10_everyday:141 a2 weak [single-load, single-load]
u10_everyday:244 a2 weak [load-chain+memop(lvalue), load-chain+memop] (assign *p=*q)
u10_everyday:284 a2 weak [load-chain+memop(lvalue), single-load]      (assign *q=t)
u11_multiarg_call:9  a4 strong [pure+cfn, load-chain+1u, load-chain+1u, load-chain+1u] (3-arg call)
u11_multiarg_call:13 a2 weak [single-load, pure]
u11_multiarg_call:24 a2 weak [single-load, pure]
u11_multiarg_call:36 a2 weak [single-load, single-load]
u11_multiarg_call:87 a3 strong [kill, kill, kill]              (post-call kills)
```

(`aN` = arity; `+Nu` = N nested unseq inside the arm; `(assign)` =
join consumed by `neg(store …)` — 24 such nodes, mechanically
counted; `(lvalue)` marks the lvalue-evaluation arm.)

### 2.3 The template taxonomy (derived; every node above is an instance)

- **T1 — operand unseq** (64 nodes, all binary, `let weak`): the two
  operands of a binary operator / comparison / truthiness test.
  Arms: loads, load chains (deref/member/array chains with
  `memop(PtrValidForDeref)` guards), pure constants (`pure(Specified(k))`
  arms appear even for literal operands), or nested T1 trees.
- **T2 — assignment unseq** (24 nodes, all binary, `let weak`):
  `unseq(lvalue-eval, rhs-eval)`, join consumed by
  `let weak _ = neg(store(τ, lv, rv))`. Lvalue arm is `pure(x)` for
  locals/globals, a load+guard chain for `*p`/`p->f`. **The store is
  always outside the unseq**, sequenced after the join. Compound
  assignment (`x += *p`) is the same template with the read of `x`
  inside the RHS arm's nested unseq — read inside, write after join.
- **T3 — call-argument unseq** (7 nodes, arity 1 + #args,
  `let strong`): arm 0 = function-designator evaluation
  (`pure((Specified(Cfunction(f)), cfunction(…)))` for direct calls;
  a `load` of the function pointer for indirect calls); arms 1..N =
  the argument full expressions. When an argument is itself a call
  (`f(g(),h())`, `f(x)+g(y)`), the arm CONTAINS the entire callee
  invocation chain: arity/compat UB checks, per-argument
  `create`/`store` of fresh slots, `ccall`, kill-unseq — the census's
  only heavyweight arms.
- **T4 — kill unseq** (3 nodes, arity = #args, `let strong _`):
  `unseq(kill(τ,slot1), …, kill(τ,slotN))` after the `ccall`,
  killing the freshly created argument slots (pairwise-distinct
  fresh blocks by construction).
- **rmw arm** (1): `a[i++]` puts a `seq_rmw('signed int', i, …)`
  action as an unseq arm beside the `load` of `a`.

Exemplar (T1 nested, u01 `x*y + y*z`, **verbatim**, trimmed):

```
let weak (a_514: loaded integer, a_515: loaded integer) =
  unseq(
    let weak (a_521: loaded integer, a_522: loaded integer) =
      unseq(load('signed int', x), load('signed int', y)) in
    pure( case (a_521, a_522) of … catch_exceptional_condition_mul … end )
  ,
    let weak (a_528: loaded integer, a_529: loaded integer) =
      unseq(load('signed int', y), load('signed int', z)) in
    pure( case (a_528, a_529) of … catch_exceptional_condition_mul … end )
  ) in
pure( case (a_514, a_515) of … catch_exceptional_condition_add … end )
```

Exemplar (T2, u08 `x += *p`, **verbatim**, trimmed):

```
let weak (a_510: pointer, a_522: loaded integer) =
  unseq(
    pure(x)
  ,
    let weak (a_511: loaded integer, a_512: loaded integer) =
      unseq(
        load('signed int', x)
      ,
        let weak a_517: loaded pointer = load('signed int*', p) in
        … PtrValidForDeref guard … in
        load('signed int', a_521)
      ) in
    pure( … catch_exceptional_condition_add … )
  ) in
let weak _: unit =
  neg(store('signed int', a_510, conv_loaded_int('signed int', a_522))) in
pure(conv_loaded_int('signed int', a_522))
```

Exemplar (T3 with call arms, u07 `f(g(), h())`, **verbatim**, trimmed):

```
let strong ((a_512: loaded pointer, (…ctype metadata…)),
a_519: loaded integer, a_523: loaded integer) =
  unseq(
    pure((Specified(Cfunction(f)), cfunction(Specified(Cfunction(f)))))
  ,
    … params_length/are_compatible checks …
      ccall('signed int (*) (void)', Specified(Cfunction(g)))
  ,
    … params_length/are_compatible checks …
      ccall('signed int (*) (void)', Specified(Cfunction(h)))
  ) in
… create/store per arg … ccall(…, a_512, a_518, a_517) …
let strong _: (unit,unit) =
  unseq(kill('signed int', a_518), kill('signed int', a_517)) in
pure(a_531)
```

---

## 3. What the pass actually does

Source ground truth (`CL/frontend/model/core_sequentialise.lem:26-49`,
read this session): the pass rewrites exactly
`Ewseq (tuple-pat) (Eunseq es) e2` → right-fold of `Ewseq` (one
binder per arm, left-to-right in arm order), and the same for
`Esseq` → `Esseq` chain (**binder kind preserved** — the `--help`
text "replace all unseq() with left to right wseq(s)" is imprecise
for the Esseq case); every other `Eunseq` position emits a debug
warning and is LEFT IN PLACE (`core_sequentialise.lem:23-25`,
comment verbatim: `"Core_sequentialise ==> missed an unseq"`).

Empirical confirmation, all 23 files: a token-multiset diff of the
two lanes shows the delta is EXACTLY {−98 `unseq`} ∪
{+`let`/`weak`/`strong`/`in` chains} (plus the `_`/`unit` tuple
pattern of the T4 kill-unseqs dissolving into `;` sseq sugar).
Every identifier, every fresh-symbol number, every other construct
is byte-identical between the lanes. Representative diff (u01,
**verbatim** head):

```
< let weak (a_514: …, a_515: …) =
<   unseq( <arm1> , <arm2> ) in
---
> let weak a_514: … = <arm1> in
> let weak a_515: … = <arm2> in
```

and for T4 under `let strong _`: `unseq(kill(a), kill(b))` →
`kill(a) ; kill(b) ;`. Nothing else changes — the pass is a pure
local unseq-to-binder-chain rewrite in evaluation (= textual
argument) order. Line-based `diff` shows some hunks not containing
`unseq`; inspection shows all of them are diff misalignment between
structurally similar guard chains (the token multiset settles it).

Corollary for the candidates memo's §6 open question: on this
corpus the pass's best-effort shape restriction is vacuous — 98/98
Eunseq nodes are in the handled `Ewseq/Esseq`-head tuple-pattern
position, zero residue in every sequentialised output. Realization
α's "unseq-free after handling" side condition would exclude
nothing here.

---

## 4. Skeleton invariance verdict

**CONFIRMED, no counterexample.** On all control-flow probes
(p02_if, p03_while, p04_for, p05_goto, t_reverse, t_binary_search,
u10_everyday): the extracted `save`/`run` sequence (labels
`while_N`/`continue_M`/`break_K`/`__cerb_continueN`/`ret_N`/C-named
labels, in file order, with `run` targets) is IDENTICAL between the
two lanes. The token-multiset result in §3 is the stronger form:
the pass changes nothing outside the unseq nodes themselves — same
saves, same runs, same symbol numbering, same `Ebound` structure,
same `nd(…)` truthiness arms, same `neg(store …)` polarity
annotations. The pass rewrites only inside expression positions.

---

## 5. The call-arguments species

Precisely, from the census plus one engine-source reading:

1. **Syntactically there is only Eunseq.** Multi-argument calls
   elaborate as ONE `Eunseq` of arity 1 + #args (function-designator
   arm first, then one arm per argument full expression), bound by
   `let strong`, followed by sequenced per-argument
   `create`/`store`, the `Eccall`, and a `let strong`-bound arity-N
   kill-`Eunseq` of the argument slots. Call OPERANDS
   (`f(x) + g(y)`) and call ARGUMENTS (`f(g(), h())`) both put the
   entire inner-call chain (checks + create/store + ccall + kills)
   inside an ordinary Eunseq arm. **No distinct
   indeterminate-sequencing construct exists in Core's grammar or
   appears in any output** (constructor set per the shape study
   §1.4; confirmed in every artifact here).
2. **The indeterminate sequencing of C11 6.5.2.2p10 is operational,
   not syntactic.** Engine source (`CL/frontend/model/
   core_reduction.lem:1347-1368`, read this session): when an
   `Eccall`/`Eproc` redex fires — anywhere, including inside an
   unseq arm — the step REPLACES THE WHOLE THREAD ARENA with the
   callee's body and pushes the entire current evaluation context
   (including the `Cunseq` context holding the sibling arms) onto
   the stack (`arena= expr; stack= Stack_cons2 … ctx …`). Sibling
   arms are therefore frozen until the callee returns: callee
   executions never interleave with sibling-arm effects; only the
   ORDER in which competing call redexes fire is nondeterministic.
   That is exactly indeterminate sequencing, delivered by the
   engine's call mechanics rather than by a dedicated construct.

Consequence stated as evidence (design is for the operator
conversation): a rule for call-bearing Eunseq arms cannot be the
same footprint-of-the-arm-syntax rule as for load arms — the arm's
footprint is the callee's footprint — but the engine's
arena-replacement fact means such arms behave as atomic units
relative to their siblings, which is a different (and stronger)
premise than arbitrary interleaving.

---

## 6. Conclusions addressed to the hypothesis (evidence only)

**Read: FAVORABLE, with two named qualifications.** The evidence for
"unseq effects collapse locally" is strong; the evidence says a
naive fully-disjoint-footprint rule is the wrong exact shape.

Favorable facts:

1. **Locality is total.** 98/98 Eunseq nodes sit inside one C full
   expression's `Ebound`, in `Ewseq/Esseq`-head position; none spans
   a statement, none crosses a save/run boundary, and the
   save/run/statement skeleton is bit-identical with and without the
   pass (§4). Whatever handles Eunseq faces a strictly
   expression-local obligation.
2. **Arms are overwhelmingly read-only.** 92% of arms (185/201) are
   loads + pure guards/conversions (plus read-only `memop` validity
   queries). Plain stores NEVER occur as arm content: every
   assignment's store is sequenced after the join (T2). The write
   species inside arms are rare and structured: fresh-slot
   create/store/kill inside call chains (disjoint by freshness),
   the 3 kill-unseqs (distinct fresh slots), and 1 `seq_rmw`.
3. **Arity is tiny and shapes are templates.** 94/98 binary; the
   4 wider nodes are call-argument unseqs (max arity 4 = 3-arg
   call). Everything observed is an instance of 4 templates + 1 rmw
   variant (§2.3), so per-shape rules cover the corpus with a
   handful of forms.
4. **Nothing here needs the pass.** Combined with the engine facts
   already on record (candidates memo §2.5: the pass is dead code in
   the Lean pipeline; the engine interprets Eunseq live with a
   join-only race check), no shape was found that a local rule could
   not in principle address — and equally, the pass's coverage is
   100% here, so neither realization is excluded by the data.

Qualifications (the shapes that stress a disjointness rule):

1. **Read-read overlap is ubiquitous — full disjointness is
   unsatisfiable on ordinary C.** `x*y + y*z` reads `y` in both
   arms (u01/u02); `a[i] + a[j]` reads `a` and `i`-vs-`j` in both
   arms and the loaded cells may alias (u05); `a + b - c*a` reads
   `a` twice (u03); `s += a[i]*a[i]` reads `a`,`i` in both nested
   arms (u10); f3's three argument arms share `x` and `y` reads
   (u11). A rule demanding pairwise-separated arm footprints
   excludes most census nodes. The rule the data supports must
   permit shared read-only footprint and require disjointness only
   between writes and anything else (the 16 write-bearing arms all
   have their writes on fresh blocks or, for the rmw, on a cell no
   sibling arm touches in the race-free programs). This is exactly
   the engine's own race criterion, verified at source this
   session: footprints are R/W-tagged and `overlapping` returns
   false for R/R pairs (`CL/memory/concrete/impl_mem.ml:527-532` —
   OCaml comment-free but the Lean mirror
   `CL/lean_frontend/CerbMem.lean:1186-1200 [cite corrected by orchestrator: overlapping is at :1186, mirroring impl_mem.ml:527-532 per the generated comment]` carries the verbatim
   comment "two reads never overlap"); `do_race` at the unseq join
   (`core_reduction.lem:214-240`) is `Mem.overlapping` over the
   accumulated action footprints, modulo the `neg(…)`-polarity
   exclusion lists. So "shared reads allowed, writes disjoint from
   everything" is not an invention the rule would add — it is the
   engine's own join-time UB test.
2. **Call arms are a genuine second species** — 5/201 arms whose
   footprint is a callee footprint, not readable off the arm syntax.
   The engine's arena-replacement mechanics (§5.2) make them
   atomic relative to siblings, so the evidence supports treating
   them by a sequenced/atomic-call rule rather than the interleaving
   rule — but that is a second rule shape, confirming the brief's
   "calls as a separate indeterminately-sequenced species" framing.

Minor observations for whoever writes the rule: nested unseq trees
reach depth 4 in one everyday-C line (u10:101), so the rule must
compose recursively; `pure(Specified(k))` constant arms are
routinely present (any rule needs a trivial-pure case); the
lvalue arm of T2 assignments can itself be a load chain (`*p = …`,
`p->f = …`), so "assignment" is not a pure-lvalue special case; and
condition unseqs against `pure(Specified(0))` occur at every C
`if`/`while` (p02/p03/p04/p05/t_*), making T1-with-one-pure-arm the
single most common shape in control-heavy code.
