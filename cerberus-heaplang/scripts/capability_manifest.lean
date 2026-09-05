/-
capability_manifest.lean — THE RULE-USE AND CLASSIFICATION MANIFEST
(a claim-point SPEEDBUMP, [USER 2026-09-02] — "speedbumps, not
adversarial gates"; P3.5 cut the 1,507-line dependency-certifying
generator down to a constructor-level report, docs/2026-09-02_p3.5-notes.md;
the ar5-manifest slice of 2026-09-04 replaced the constructor rows by
VARIANT rows after the external audit's Finding 1 — the constructor-level
"0 red" had been read as "every semantic form of every constructor has a
rule", which it never established:
docs/2026-09-04_reynolds-ohearn-separation-logic-audit.md;
record docs/2026-09-04_ar5-manifest-notes.md).

WHAT THE DATA IS. `variants` below is a HAND-MAINTAINED classification of
the engine-SUCCESS shapes of every `Frag` constructor (read off `Frag`,
`Step` and the engine's `CerbMem.storeM`/`loadM`/`allocateObject`/
`allocateRegion`/`killM`/`eqPtrval` arms), each shape in exactly one class:
  RULE p t          a partial rule `p` and a total rule `t`, both theorems,
                    each in the proof-term cone of at least one CONSUMER
                    module (below)
  RULE-TOTAL-UNDEMONSTRATED p t
                    a partial rule `p` consumed as above; a total rule `t`
                    that exists as a theorem but lies in NO consumer's cone
                    (stated with the mover: the exhibit that would consume
                    it); the row turns red when a consumer appears (then
                    reclassify as RULE) — [AGENT 2026-09-04], record §3
  RULE-PARTIAL-UNDEMONSTRATED p t
                    the symmetric case: the total rule is consumed; the
                    partial rule exists but has no consumer yet. A new
                    partial consumer makes the row red until reclassified.
  PARTIAL-ONLY p    a partial rule, no total rule exists (reason stated)
  NO-RULE           admitted by the fragment and the engine, covered by no
                    rule — reason and the record that decided it
  OUT-OF-SCOPE      excluded by the fragment/mirror boundary — reason and
                    record
Engine KILLS / UB / PANICS are not rows: they are not successes and are
classified in Round.lean (`complete_*`, `ShippedRefusal`).

WHAT THE GENERATOR CHECKS (red = nonzero exit):
1. the row set covers every constructor of `Frag` read out of the built
   environment (an unclassified constructor is a MISSING row), and every
   row names a real constructor (a stale row is red);
2. every theorem a row names exists and is a theorem;
3. every RULE / PARTIAL-ONLY rule lies in the proof-term dependency cone of
   at least one CONSUMER module — the modules classified `positive-client`
   or `declared-smoke` in scripts/module_classes.tsv (the one authoritative
   module classification, shared with parametric_inventory.lean and
   boundary_check.sh); a rule no consumer's proof flows through is red
   (the 2026-09-01 re-audit's R-01/R-04 overclaim class);
4. every RULE row has BOTH judgments consumed;
5. the module classification is complete and exact: every package module
   is classified, every classified module is in the environment, every
   class is in the vocabulary;
6. the claim matrix docs/CLAIMS.md names only existing declarations: the
   backticked names in the second cell, `Exported theorem(s)`, of every
   table row whose first cell begins `C<digits>` are theorems, definitions
   or inductives of the environment; and (E3 range audit D-2,
   docs/2026-09-05_audit-e3-range.md — a prose cell had named two DELETED
   theorems as the current state) EVERY declaration-shaped backticked span
   of EVERY cell of such a row (identifier characters, `.`, `'`, `?`, `!`)
   is a constant of the environment (under `CerberusHeapLang.`, at the root,
   or under `CerbND.`) or a word of `claimVocabulary` (Core/std.core
   keywords, hypothesis names and other prose tokens, listed in this file;
   a listed word no row uses is red — stale vocabulary). The check is
   PLANTED: a synthetic row naming a deleted theorem in a prose cell must
   come out red, or the run is red. RETIRED exports (`retiredNames`: former
   theorems, deleted) may be named as history only with the marker
   `(retired …)` directly after the span — unmarked is red, and a retired
   entry that resolves or that no row names is red (E4 range audit N-4);
   planted both ways (unmarked red, marked clean).

WHAT GREEN DOES NOT ESTABLISH: that the variant list is exhaustive over the
engine's success shapes (it is a reviewed reading of the engine, not a
theorem), that a rule is the STRONGEST statement of its variant, or that a
consumer's dependency on a rule is the load-bearing step of its headline
proof rather than incidental. Those are what the record and the audits are
for.

Output: markdown + one machine line per section. Deterministic.
Run (from cerberus-heaplang/):
  ../scripts/capped ~/.elan/bin/lake env lean scripts/capability_manifest.lean \
    > docs/CAPABILITY_MANIFEST.md
-/
import CerberusHeapLang

open Lean

namespace CapabilityManifest

/-! ## The classification data -/

inductive Class where
  | rule (p t : Name)
  | ruleTotalUndemonstrated (p t : Name) (mover : String)
  | rulePartialUndemonstrated (p t : Name) (mover : String)
  | partialOnly (p : Name) (why : String)
  | noRule (why : String)
  | outOfScope (why : String)

structure Variant where
  ctor : Name
  shape : String
  cls : Class
  /-- Companion faces of the same variant (other statements of the same
      rule): must exist as theorems; NOT consumption-checked. -/
  also : List Name := []

def N (s : String) : Name := (`CerberusHeapLang).append s.toName

def trim (s : String) : String := s.trimAscii.toString

/-- Records cited by the rows (short handles, expanded in the header). -/
def recK1N2 := "K1 range audit N-2 (docs/2026-09-03_k1-audit.md), `Frag.store` docstring"
def recK2N2 := "K2 range audit N-2 → the K3 decision (docs/2026-09-03_k3-notes.md §6; DECISIONS 2026-09-03 K3 entry)"
def recK3N2 := "K3 range audit N-2; docs/2026-09-03_k3-notes.md §4(c)/§6"
def recA3 := "docs/KNOWN-OPEN-ITEMS.md A3 (`dynamic_addrs`), K3 notes §6"
def recClosure := "fragment closure 2026-09-02 (docs/2026-09-02_fragment-closure-notes.md); ARCHITECTURE §7 Goal 2"
def recAr5 := "found at ar5-manifest 2026-09-04 by reading the engine arms; [AGENT] classified, docs/2026-09-04_ar5-manifest-notes.md §2"
def recE1 := "dialect arc E1 2026-09-05 (docs/2026-09-04_e1-notes.md)"
def recE2 := "dialect arc E2 2026-09-05 (docs/2026-09-05_e2-notes.md)"
def recE3 := "dialect arc E3 2026-09-05 (docs/2026-09-05_e3-notes.md)"
def recE4 := "dialect arc E4 2026-09-05 (docs/2026-09-05_e4-notes.md)"
def recE5 := "dialect arc E5 2026-09-05 (docs/2026-09-05_e5-notes.md)"

/-- THE VARIANT TABLE. Read the engine arms cited before editing. -/
def variants : List Variant := [
  -- pure values
  { ctor := `CerberusHeapLang.Frag.val_pure,
    shape := "`pure(v)` — the delivered value (the value protocol)",
    cls := .rule (N "wps_ofVal") (N "wpt_ofVal") },
  -- store
  { ctor := `CerberusHeapLang.Frag.store,
    shape := "`Store0 false` (non-locking) at a live writable OBJECT through its own pointer, whole cell at full ownership",
    cls := .rule (N "wps_store") (N "wpt_store"),
    also := [N "wps_store_plain", N "wpt_store_plain", N "store_atomic"] },
  { ctor := `CerberusHeapLang.Frag.store,
    shape := "`Store0 false` at a typed SUB-RANGE of an object (`pointsToView`: field/element at an offset)",
    cls := .rule (N "wps_store_at") (N "wpt_store_at"),
    also := [N "wps_store_cell_at", N "wpt_store_cell_at", N "storeAt_atomic"] },
  { ctor := `CerberusHeapLang.Frag.store,
    shape := "`Store0 false` at a typed sub-range of a live dynamic REGION (`typedRegionView`; K5)",
    cls := .rule (N "wps_store_region_at") (N "wpt_store_region_at"),
    also := [N "wps_store_regionOwn_at", N "wpt_store_regionOwn_at", N "regionStoreAt_atomic"] },
  { ctor := `CerberusHeapLang.Frag.store,
    shape := "`Store0 true` — the LOCKING store (engine success flips the allocation's `isReadonly`, CerbMem `storeM` `isLocking` arm)",
    cls := .noRule s!"every store rule is stated at `Store0 false`, so no derivation traverses a locking store and the coupling is never asserted across one; {recK1N2}" },
  { ctor := `CerberusHeapLang.Frag.store,
    shape := "store through a UNION-MEMBER pointer (`PVconcrete (some membr) addr`; the engine also updates `lastUsedUnionMembers`)",
    cls := .noRule s!"every bundle fixes the pointer shape `cellPtr id a = PVconcrete none a`; no union support in the logic; {recAr5}" },
  { ctor := `CerberusHeapLang.Frag.store,
    shape := "whole-object store at an ATOMIC-typed allocation (engine success: `isAtomicMemberAccess` is `false` for the whole object at the allocation's own type, CerbMem `storeM`)",
    cls := .noRule s!"no bundle describes an atomic-typed allocation (`CellCoh.nonAtomic`, `MetaCoh.nonAtomic`); the access shape is reachable only from a seeded memory or an authored pointer literal; found by the AR5 range audit (C-3b); {recAr5}" },
  -- load
  { ctor := `CerberusHeapLang.Frag.load,
    shape := "`Load0` at a live OBJECT through its own pointer, whole cell at any fraction, non-trap decode",
    cls := .rule (N "wps_load") (N "wpt_load"),
    also := [N "wps_load_plain", N "wpt_load_plain", N "load_atomic"] },
  { ctor := `CerberusHeapLang.Frag.load,
    shape := "`Load0` at a typed SUB-RANGE of an object (`pointsToView`)",
    cls := .rule (N "wps_load_at") (N "wpt_load_at"),
    also := [N "wps_load_cell_at", N "wpt_load_cell_at", N "loadAt_atomic"] },
  { ctor := `CerberusHeapLang.Frag.load,
    shape := "`Load0` at a typed sub-range of a live dynamic REGION (`typedRegionView`; K5)",
    cls := .rule (N "wps_load_region_at") (N "wpt_load_region_at"),
    also := [N "wps_load_regionOwn_at", N "wpt_load_regionOwn_at", N "regionLoadAt_atomic"] },
  { ctor := `CerberusHeapLang.Frag.load,
    shape := "`Load0` at a READ-ONLY object (`readonlyCell`, K1: string literals / const-qualified)",
    cls := .noRule s!"the atomic specification `load_atomic_readonly` exists (liftable by `wps_of_atomic`/`wpt_of_atomic`) but no statement-level rule is stated and no client consumes it; {recAr5}",
    also := [N "load_atomic_readonly"] },
  { ctor := `CerberusHeapLang.Frag.load,
    shape := "load through a UNION-MEMBER pointer (`PVconcrete (some membr) addr`)",
    cls := .noRule s!"as the store: the bundles fix `cellPtr`; {recAr5}" },
  { ctor := `CerberusHeapLang.Frag.load,
    shape := "whole-object load at an ATOMIC-typed allocation (engine success: `isAtomicMemberAccess` is `false` for the whole object at the allocation's own type, CerbMem `loadM`)",
    cls := .noRule s!"no bundle describes an atomic-typed allocation (`CellCoh.nonAtomic`, `MetaCoh.nonAtomic`); found by the AR5 range audit (C-3b); {recAr5}" },
  -- create
  { ctor := `CerberusHeapLang.Frag.create,
    shape := "`Create` of a positive-size NON-ATOMIC object type whose unspecified image is decode-inert (`hsz`/`hatom`/`hinert`; rfl for scalar and integer-array types), paid from `allocBudget (allocCost ty al)`",
    cls := .rule (N "wps_create") (N "wpt_create"),
    also := [N "wps_create_of_plan", N "wpt_create_of_plan", N "create_atomic"] },
  { ctor := `CerberusHeapLang.Frag.create,
    shape := "`Create` of a ZERO-size type (`sizeofCtype = 0`; the engine pads the allocation to size 1, `allocateObject` `.max 1`)",
    cls := .noRule s!"`create_atomic`'s `hsz : 0 < sizeofCtype` excludes it (the budget arithmetic is stated at the unpadded size); `create_atomic` docstring; {recAr5}" },
  { ctor := `CerberusHeapLang.Frag.create,
    shape := "`Create` of an ATOMIC object type (`Ctype _ (Atomic _)`)",
    cls := .noRule s!"`create_atomic`'s `hatom : atomicTy ty = false` (the atomic-member check `isAtomicMemberAccess` is unreachable only at a non-atomic root); `create_atomic` docstring; {recAr5}" },
  { ctor := `CerberusHeapLang.Frag.create,
    shape := "`Create` of a type whose unspecified image is NOT decode-inert at some address (`hinert` fails)",
    cls := .noRule s!"`create_atomic`'s `hinert` premise: the fresh cell must carry `decIndep` for the coupling; the premise is the rule's, not a syntactic shape — a type failing it has no rule; {recAr5}" },
  -- kill
  { ctor := `CerberusHeapLang.Frag.kill,
    shape := "STATIC kill (`is_dynamic kind = false`) of a live created OBJECT at full ownership (C's end of automatic storage)",
    cls := .rule (N "wps_kill") (N "wpt_kill"),
    also := [N "wps_kill_emp", N "wpt_kill_emp", N "kill_atomic"] },
  { ctor := `CerberusHeapLang.Frag.kill,
    shape := "DYNAMIC kill (`free`) of a live `alloc`ated REGION at full ownership",
    cls := .rule (N "wps_free") (N "wpt_free"),
    also := [N "wps_free_emp", N "wpt_free_emp", N "free_atomic"] },
  { ctor := `CerberusHeapLang.Frag.kill,
    shape := "STATIC kill of a live REGION (engine accepts: the `dynamicAddrs` check is short-circuited at `isDynamic = false`, CerbMem `killM`)",
    cls := .noRule s!"object bundle vs region bundle — `kill_atomic` consumes `pointsToCell`, `free_atomic` consumes `regionOwn`, and the metadata flag separates them; a program static-killing malloc'd storage is outside the logic by design; {recK2N2}" },
  { ctor := `CerberusHeapLang.Frag.kill,
    shape := "`free(NULL)` — dynamic kill at a null pointer (engine no-op success, `killM` `PVnull` arm at `isDynamic = true`)",
    cls := .noRule s!"nothing to consume or produce; no rule stated; {recK2N2}" },
  { ctor := `CerberusHeapLang.Frag.kill,
    shape := "`free` of a CREATED object whose base happens to sit in `dynamicAddrs` (the upstream `dynamic_addrs` collision after a zero-size `alloc`; otherwise UB179a)",
    cls := .noRule s!"the logic never reads `dynamicAddrs`; `free_atomic`'s `regionOwn` presupposes the region bundle; {recA3}" },
  { ctor := `CerberusHeapLang.Frag.kill,
    shape := "kill of either kind through a UNION-MEMBER pointer (`PVconcrete (some membr) addr`; CerbMem `killM` ignores the member, so the engine succeeds exactly as at `none`)",
    cls := .noRule s!"`kill_atomic` consumes `pointsToCell pv` and `free_atomic` is stated at `cellPtr id a`, both forcing `PVconcrete none a`; no union support in the logic; found by the AR5 range audit (C-3a); {recAr5}" },
  -- kill_op
  { ctor := `CerberusHeapLang.Frag.kill_op,
    shape := "kill of either kind at a `PePure` operand evaluating to a POINTER (the ACTION_EVAL round; the successor is the canonical kill redex — its variants above then apply)",
    cls := .rule (N "wps_kill_eval") (N "wpt_kill_eval") },
  -- alloc
  { ctor := `CerberusHeapLang.Frag.alloc,
    shape := "`Alloc0` at integer operands of POSITIVE cost `0 < regionCost al n` (every `n > 0`; also `n ≤ 0` at `al ≥ 2`), paid from `allocBudget (regionCost al n)`",
    cls := .rule (N "wps_alloc") (N "wpt_alloc"),
    also := [N "alloc_atomic", N "regionCost_pos"] },
  { ctor := `CerberusHeapLang.Frag.alloc,
    shape := "`Alloc0` of ZERO cost — `n ≤ 0 ∧ al ≤ 1` (the engine collapses every non-positive size to a size-0 region and succeeds)",
    cls := .noRule s!"`alloc_atomic`'s `hcost`: a zero-cost budget fragment is the unit and forces no cursor cell; {recK3N2}" },
  -- alloc_op
  { ctor := `CerberusHeapLang.Frag.alloc_op,
    shape := "`Alloc0` at `PePure` operands (not all values) evaluating to INTEGERS (the ACTION_EVAL round)",
    cls := .rule (N "wps_alloc_eval") (N "wpt_alloc_eval") },
  -- sequencing
  { ctor := `CerberusHeapLang.Frag.sseq,
    shape := "`lets _ = e1 in e2` — reduction under the frame, then LETS-PURE or LETS-ANNOT at the delivered value (either value shape, `mergeInto`)",
    cls := .rule (N "wps_seq") (N "wpt_seq") },
  { ctor := `CerberusHeapLang.Frag.annot,
    shape := "`{A} e` — reduction under a dyn-annotation frame and the ANNOTS merge",
    cls := .rule (N "wps_annot") (N "wpt_annot"),
    also := [N "wps_annot_reindex", N "wpt_annot_reindex"] },
  { ctor := `CerberusHeapLang.Frag.save,
    shape := "`save l(params := inits) in body` at `PePure` initializers within fuel — the TAU arm (value initializers) and the EVAL arm (an evaluating round first); one rule covers both",
    cls := .rule (N "wps_save") (N "wpt_save"),
    also := [N "wps_save_vals", N "wpt_save_vals", N "wps_save_eval", N "wpt_save_eval"] },
  { ctor := `CerberusHeapLang.Frag.if_,
    shape := "`if g then e2 else e3` at a `PePure` guard evaluating to `Vtrue`",
    cls := .rule (N "wps_if_true") (N "wpt_if_true"),
    also := [N "wps_if", N "wpt_if"] },
  { ctor := `CerberusHeapLang.Frag.if_,
    shape := "`if g then e2 else e3` at a `PePure` guard evaluating to `Vfalse`",
    cls := .rule (N "wps_if_false") (N "wpt_if_false") },
  { ctor := `CerberusHeapLang.Frag.run,
    shape := "`run l(args)` — the label resolves in the current procedure's map and every argument evaluates (surplus arguments included when they evaluate: `bindArgs` zips)",
    cls := .rule (N "wps_run") (N "wpt_run") },
  { ctor := `CerberusHeapLang.Frag.run,
    shape := "`run l(args)` with MORE arguments than parameters where a SURPLUS argument does not evaluate (the engine's fold truncates and succeeds; `Step.run` evaluates every argument)",
    cls := .outOfScope s!"the mirror has no step there — the characterized residual `OpenRound.run_surplus` (Round.lean); {recClosure}" },
  { ctor := `CerberusHeapLang.Frag.sseq_spec,
    shape := "`lets Specified(x) = e1 in e2` — the head delivers `Specified(ov)` (bare or annotated)",
    cls := .rule (N "wps_seq_spec") (N "wpt_seq_spec") },
  -- E2: pure at any covered non-value operand (subsumes E1's `pure_sym`)
  { ctor := `CerberusHeapLang.Frag.pure_op,
    shape := "`pure(e)` at a `PePure` non-value operand the mirror evaluator EVALUATES — a bound symbol, a mirrored binop/array-shift/ctor at evaluating operands (`Specified(e)`, `(e1, e2)`, `Ivalignof(ty)`, `Unspecified(ty)`), `case … end` selecting a branch that evaluates, `not`/`if` at boolean operands (the PURE round through the certified evaluator)",
    cls := .rule (N "wps_pure") (N "wpt_pure") },
  { ctor := `CerberusHeapLang.Frag.pure_op,
    shape := "`pure(e)` at a `PePure` operand the classifier does NOT decide (`evalClass` `.uncovered`) — either a LEAF the engine evaluates but the mirror does not: a symbol UNBOUND in the environment but naming a `Proc` of the file (the null function pointer), a mirrored binop at two floats (`OpEq` at two ctypes is MIRRORED since E3), a comparison at symbolic integers (`PEconstrained`), since E3 a std.core call whose body exceeds its static budget `stdBudget` (the engine unfolds and continues; reached by no transcribed std.core function); or, since E2, a shape the engine REFUSES but the classifier does not certify: a `case` matching no pattern (the engine's opaque `failwithI` PANIC), `undef(<<UB088>>)` (its location is the call-location parameter), a constructor dispatch failure (an engine KILL), a constructor operand list whose first failing operand is an undef followed by another failure (the engine's Exception-first `except_sequence`), a `case` whose selected branch the mirror's depth guard rejects",
    cls := .outOfScope s!"the mirror evaluator answers `none`; the characterized residual `OpenRound.eval_uncovered` (`evalClass` `.uncovered`, EvalClass.lean's header lists the members); {recE2}; the ctype-equality leaf and the budget arm: {recE3}; the E2 refusal members added to this row at the E4 range audit N-3 (KOI C16, docs/2026-09-05_audit-e4-range.md)" },
  -- E3: the emitted integer arithmetic and the standard-library calls
  { ctor := `CerberusHeapLang.Frag.pure_op,
    shape := "THE EMITTED C `+`: `pure(case (a, b) of | (Specified(a'), Specified(b')) => Specified(catch_exceptional_condition_add('signed int', __conv_int__('signed int', a'), __conv_int__('signed int', b'))) | _ => undef(<<UB036>>) end)` at `a ↦ Specified(n1)`, `b ↦ Specified(n2)` in `int`'s range with an IN-RANGE sum (the engine's `select_case`, `mk_conv_int`, `mk_call_catch_exceptional_condition`; the out-of-range sum is the `.undef` KILL, `evalClass_cAdd_overflow`, exhibited by OverflowExhibit)",
    cls := .rule (N "wps_c_add") (N "wpt_c_add"),
    also := [N "evalPexpr_cAdd", N "evalPexpr_cAdd_overflow", N "evalClass_cAdd_overflow"] },
  { ctor := `CerberusHeapLang.Frag.pure_op,
    shape := "`pure(conv_loaded_int('signed int', e))` at `e ↦ Specified(n)` in range, on a file whose `stdlib` is the transcribed fragment `stdlibE3` (`StdE3 M.file`): the std.core unfolding `conv_loaded_int → conv_int → is_representable_integer` through the FILE OBJECT (`call_function` on `file.stdlib`, core_eval.lem:120–163; the mirror's `callBody` under the static budget)",
    cls := .rule (N "wps_conv_loaded_int") (N "wpt_conv_loaded_int"),
    also := [N "evalPexpr_convLoadedInt_spec", N "evalPexpr_convLoadedInt_unspec"] },
  { ctor := `CerberusHeapLang.Frag.pure_op,
    shape := "`catch_exceptional_condition_sub/_mul('signed int', e1, e2)` at in-range integer operands with an in-range result (mirrored: `evalCatch` is the generated `mk_call_catch_exceptional_condition`; engine facts `mk_iop_sub_ival`/`mk_iop_mul_ival`)",
    cls := .noRule s!"E3 ruled the demo's `+` only; the `-`/`*` rules are the same shape (`wps_pure` at `evalPexpr_catch_*`) and pending an exhibit that reaches them; {recE3} §7" },
  { ctor := `CerberusHeapLang.Frag.pure_op,
    shape := "`catch_exceptional_condition_div/_rem_t/_shl/_shr('signed int', e1, e2)` (mirrored through the same generated `mk_iop`: `CerbMem.opIval IntDiv/IntRem_t/…`; the divisor-zero and shift-amount arms are the memory model's own)",
    cls := .noRule s!"no engine fact stated in E3 for these arms — the C elaborator guards `/` and `%` with an explicit zero check before this node; pending; {recE3} §7" },
  { ctor := `CerberusHeapLang.Frag.pure_op,
    shape := "`wrapI_<op>('unsigned …', e1, e2)` — the wrap-around arithmetic the elaborator emits for UNSIGNED types (mirrored: `evalWrapI` is the generated `mk_wrapI_op`, core_eval.lem:828–833)",
    cls := .noRule s!"no exhibit of E3 reaches it (the corpus is `int`); the mirror is total on it; {recE3} §7" },
  { ctor := `CerberusHeapLang.Frag.pure_op,
    shape := "`__conv_int__('signed int', e)` standalone at an integer (mirrored: `evalConvInt` is the generated `mk_conv_int`; representable → identity, `mk_conv_int_int_in_range`; NON-representable → whatever `mk_conv_int` computes, the impl-defined wrap)",
    cls := .noRule s!"the elaborator emits `__conv_int__` only under `catch_exceptional_condition`, where `wps_c_add` covers it; no standalone rule; the non-representable arm is not ruled; {recE3} §7" },
  { ctor := `CerberusHeapLang.Frag.pure_op,
    shape := "`conv_int('signed int', e)` / `is_representable_integer(e, 'signed int')` as STANDALONE std.core calls at in-range integers on a `StdE3` file (evaluator lemmas `evalPexpr_convInt_call_int`, `evalPexpr_isRepr_int`), and the leaves their bodies reach: `Ivmin(ty)`/`Ivmax(ty)`, `ty1 = ty2` at ctypes, `/\\`, `\\/`, `is_unsigned(ty)` at a LEAF operand (`peDepth = 1` — the engine rebuilds a non-value `is_unsigned` operand as `PEis_scalar`, core_eval.lem:1086)",
    cls := .noRule s!"mirrored (E3: `evalCtor` Civmin/Civmax, `evalBinop` OpEq at ctypes and OpAnd/OpOr, `evalIsUnsigned`, `callBody`); reached inside `conv_loaded_int`'s unfolding, which IS ruled; no standalone rule; {recE3} §7" },
  { ctor := `CerberusHeapLang.Frag.pure_op,
    shape := "a `PEcall` at an `Impl` name — `<Integer.conv_nonrepresentable_signed_integer>(ty, n)`, reached by `conv_int` at a NON-representable signed value — or at a `Sym` the file's `stdlib`/`funs` do not name (`wrapI`, `params_length`, `params_nth`, …)",
    cls := .outOfScope s!"the mirror unfolds a call only through the file's own maps (`callBody` = `call_function`'s success path); every file this package builds has an EMPTY `impl` map and the fragment `stdlibE3` names three functions, so these calls are the engine's `Illformed_program` KILL (`callOut`, classified `.kill`, never a default); the gcc impl body and the remaining std.core functions are not transcribed; {recE3} §7" },
  { ctor := `CerberusHeapLang.Frag.load_op,
    shape := "`Load0` at a `PePure` pointer operand evaluating to a POINTER (the ACTION_EVAL round)",
    cls := .rule (N "wps_load_eval") (N "wpt_load_eval") },
  { ctor := `CerberusHeapLang.Frag.sseq_sym,
    shape := "`lets x = e1 in e2` at any fragment head delivering a BARE value (LETS-PURE; a call head since C4, any head since E1)",
    cls := .rule (N "wps_seq_sym") (N "wpt_seq_sym") },
  { ctor := `CerberusHeapLang.Frag.sseq_sym,
    shape := "`lets x = e1 in e2` whose head delivers an ANNOTATED value `{A}v` (the engine's LETS-ANNOT at the symbol binder: `x ↦ v`, `{A}` re-wrapped around `e2`)",
    cls := .noRule s!"admitted by the fragment and MIRRORED since E1 (`Step.sseq_sym_annot`, classified by `complete_beta_sym`; the pre-E1 `BareHead` exclusion and its OUT-OF-SCOPE row are retired) but `wps_seq_sym`/`wpt_seq_sym` are stated at a BARE head value (`⌜w = SpikeVal.pure v⌝`); binder rules over annotated heads are E2's (patterns bind annotated heads); {recE1}" },
  -- E2: the tuple binders and the weak symbol binder
  { ctor := `CerberusHeapLang.Frag.sseq_tuple,
    shape := "`let strong (a, b, …) = e1 in e2` at any fragment head delivering a BARE tuple value (LETS-PURE at the flat tuple binder; `update_env`'s `Ctuple` arm zips leaves against components)",
    cls := .rule (N "wps_seq_tuple") (N "wpt_seq_tuple") },
  { ctor := `CerberusHeapLang.Frag.sseq_tuple,
    shape := "`let strong (a, b, …) = e1 in e2` whose head delivers an ANNOTATED tuple `{A}(v1, …)` (LETS-ANNOT at the tuple binder)",
    cls := .noRule s!"admitted by the fragment and MIRRORED (`Step.sseq_tuple_annot`, classified by `complete_beta_tuple`); no emitted shape of E2 reaches it — E4's `unseq` delivers annotated tuples at the WEAK binder; {recE2}" },
  { ctor := `CerberusHeapLang.Frag.wseq_tuple,
    shape := "`let weak (a, b, …) = e1 in e2` at any fragment head delivering a BARE tuple value (LETW-PURE at the flat tuple binder)",
    cls := .rule (N "wps_wseq_tuple") (N "wpt_wseq_tuple") },
  { ctor := `CerberusHeapLang.Frag.wseq_tuple,
    shape := "`let weak (a, b, …) = e1 in e2` whose head delivers an ANNOTATED tuple (LETW-ANNOT at the tuple binder — the shape every corpus `let weak (a, b) = unseq(…)` reaches: the unseq's annotated tuple; E4)",
    cls := .rule (N "wps_wseq_tuple_annot") (N "wpt_wseq_tuple_annot") },
  { ctor := `CerberusHeapLang.Frag.wseq_sym,
    shape := "`let weak x = e1 in e2` at any fragment head delivering a BARE value (LETW-PURE at the plain-symbol binder — the corpus's `let weak a_515: pointer = pure(x) in load(…)`)",
    cls := .rule (N "wps_wseq_sym") (N "wpt_wseq_sym") },
  { ctor := `CerberusHeapLang.Frag.wseq_sym,
    shape := "`let weak x = e1 in e2` whose head delivers an ANNOTATED value (LETW-ANNOT at the symbol binder)",
    cls := .noRule s!"admitted by the fragment and MIRRORED (`Step.wseq_sym_annot`, classified by `complete_wbeta_sym`); no emitted shape of E2 reaches it; {recE2}" },
  -- E4: unseq
  { ctor := `CerberusHeapLang.Frag.unseq,
    shape := "`unseq(e_1, …, e_n)` with a REDUCIBLE component: the sequential driver reduces the LAST reducible component (`get_ctx_unseq_aux` prepends each reducible component's contexts, core_reduction.lem:544–548/:590–601; the loop takes the head) under the `Cunseq` frame — every sibling ccall-free (`ccallFreeList`: no `Eccall`, and every nested `case`/`let`/`nd` branch ccall-free, so `is_unseq_with_ccall` is `false`, :501–519)",
    cls := .rule (N "wps_unseq_focus") (N "wpt_unseq_focus"),
    also := [N "wpt_jump_frame_unseq", N "wpt_unseq_pure_right"] },
  { ctor := `CerberusHeapLang.Frag.unseq,
    shape := "`unseq(v_1, …, v_n)` — every component a value: UNSEQ-PURE/UNSEQ-ANNOT completion into the annotated tuple `{A_1 ++ … ++ A_n}(v_1, …, v_n)` (`one_step_unseq_aux`, core_reduction.lem:375–386; the race-free case)",
    cls := .rule (N "wps_unseq_vals") (N "wpt_unseq_vals") },
  { ctor := `CerberusHeapLang.Frag.unseq,
    shape := "`unseq(v_1, …, v_n)` whose components' dynamic annotations RACE (`do_race`): the UB035_unsequenced_race kill",
    cls := .noRule s!"the engine kills the thread (`Step_with_runstate2 (RSK_eval \"unsequenced race\") (stExceptUndef_undef …)`), mirrored as the classification `complete_unseq_vals` (`.killed`); no rule delivers a value there and the total lane refuses (`wpt_unseq_vals` requires `collectUnseq … = some _`); {recE4}" },
  { ctor := `CerberusHeapLang.Frag.unseq,
    shape := "`unseq(…, run l(…), …)` / `unseq(…, pcall f(…), …)` — a jump or a call reaching the root THROUGH the `Cunseq` frame (the spine searches `jumpRedex?`/`callRedex?` descend into the last reducible component; `Step.run`/`Step.call` at the plugged context)",
    cls := .noRule s!"admitted by the fragment and MIRRORED (`Step.unseq_inv`'s run/call disjuncts; `wpt_jump_frame_unseq` carries the jump frame); no exhibit reaches a jump or a call under the frame yet, so no rule face is demonstrated (the corpus's calls are `Eccall`s — E6; its `run`s sit at the procedure spine); {recE4}" },
  -- E5: the negative-action protocol, the excluded store, the case EVAL round, nd
  { ctor := `CerberusHeapLang.Frag.neg_store,
    shape := "`neg(store(ty, p, v))` at canonical operands under a `bound` with no strong sequence between (`break_at_bound_and_sseq` = `BOUND_NO_SSEQ`): the engine's NEGATIVE-ACTION round draws an exclusion id and a fresh symbol from the run state and rewrites `bound(ctxA[neg(act)])` into `bound(let weak (_, s) = unseq(Eexcluded n act, ctxA'[pure(Unit)]) in pure(s))` (core_reduction.lem:1290–1338)",
    cls := .rulePartialUndemonstrated (N "wps_neg_round") (N "wpt_neg_round")
      "t5 consumes the total rules; a partial corpus derivation remains (docs/2026-09-05_e5-resume.md)",
    also := [N "wps_neg_bound", N "wpt_neg_bound", N "wps_bound_wseq_tuple", N "wpt_bound_wseq_tuple"] },
  { ctor := `CerberusHeapLang.Frag.neg_store_op,
    shape := "`neg(store(ty, p, v))` at `PePure` operands not all values — the same round (the rewrite fires before any operand evaluates; the operands evaluate inside the excluded node)",
    cls := .rulePartialUndemonstrated (N "wps_neg_round") (N "wpt_neg_round")
      "t5 consumes the total rules; a partial corpus derivation remains (docs/2026-09-05_e5-resume.md)",
    also := [N "wps_neg_bound", N "wpt_neg_bound"] },
  { ctor := `CerberusHeapLang.Frag.excluded_store,
    shape := "`Eexcluded n (store(ty, p, v))` at canonical operands — `process_action (Just n)` (core_reduction.lem:1345–1346, :694–711): the same `StoreRequest2` as the positive store, its continuation the NEGATIVE dynamic annotation `{DA_neg n [] fp}pure(Unit)`",
    cls := .rulePartialUndemonstrated (N "wps_excluded_store") (N "wpt_excluded_store")
      "t5 consumes the total rules; a partial corpus derivation remains (docs/2026-09-05_e5-resume.md)",
    also := [N "excluded_store_atomic"] },
  { ctor := `CerberusHeapLang.Frag.excluded_store_op,
    shape := "`Eexcluded n (store(ty, p, v))` at `PePure` operands not all values (the ACTION_EVAL round under `Eexcluded n`; the node is rebuilt at the evaluated operands, core_reduction.lem:721–727)",
    cls := .rulePartialUndemonstrated (N "wps_excluded_store_eval") (N "wpt_excluded_store_eval")
      "t5 consumes the total rules; a partial corpus derivation remains (docs/2026-09-05_e5-resume.md)" },
  { ctor := `CerberusHeapLang.Frag.case_op,
    shape := "`case pe of …` at a `PePure` NON-value scrutinee (one_step0's `Ecase` EVAL round: the scrutinee evaluates, the node is rebuilt at the value; the corpus's `case (a_512, a_513) of` tuple scrutinee)",
    cls := .rulePartialUndemonstrated (N "wps_case_eval") (N "wpt_case_eval")
      "t5 consumes the total rules; a partial corpus derivation remains (docs/2026-09-05_e5-resume.md)" },
  { ctor := `CerberusHeapLang.Frag.nd,
    shape := "`nd(e_1, …, e_n)` with at least two alternatives — one_step0's `End es => ND es` (core_reduction.lem:447–449) becomes the scheduler FORK `Step_nd2` (:1473–1474; `advance_step`'s `ND.pick`, driver.lem:1039–1046)",
    cls := .outOfScope s!"the mirror has NO rule for a fork (fail-closed: the choice is the driver's, and `CerbND.runND` explores every alternative — `ShippedRefusal.fork` via `complete_nd`/`nd_fork`, `pick` on a list of two or more); the corpus reaches `nd` only in the `Unspecified` arm of an `if` condition's case, which no certified run takes; {recE5}" },
  -- E1: the bound frame
  { ctor := `CerberusHeapLang.Frag.bound,
    shape := "`bound(e)` — reduction under the `Cbound` frame, then REMOVE-BOUND at the delivered value of either shape (the dynamic annotations of an annotated value are DROPPED); E5: the rule faces are stated for a NEGATIVE-FREE body within the fuel (`negFree e = true`, `pot e ≤ lemDefaultFuel`, both `rfl` on emitted programs) — the `bound` frame itself performs the negative-action round, so a body reaching one is `Frag.neg_store`'s row",
    cls := .rule (N "wps_bound") (N "wpt_bound"),
    also := [N "wpt_jump_frame_bound"] },
  -- E1: create at ctor-constant operands
  { ctor := `CerberusHeapLang.Frag.create_op,
    shape := "`Create` at `PePure` operands (not all values) evaluating to an INTEGER alignment and a CTYPE — the emitted `create(Ivalignof(ty), ty)` (the ACTION_EVAL round; the successor is the canonical create redex, whose variants above apply)",
    cls := .rule (N "wps_create_eval") (N "wpt_create_eval") },
  -- memop
  { ctor := `CerberusHeapLang.Frag.memop_vals,
    shape := "`PtrEq` at two POINTER values with a STATE-INDEPENDENT verdict: null/any, function/function, function (non-`SD_Id`-named)/concrete, same-provenance concrete pair (CerbMem `eqPtrval`)",
    cls := .rule (N "wps_memop_ptreq") (N "wpt_memop_ptreq") },
  { ctor := `CerberusHeapLang.Frag.memop_vals,
    shape := "`PtrEq` at two concrete pointers of DIFFERING provenance (the engine forks: `msum` \"using provenance\" / \"ignoring provenance\")",
    cls := .outOfScope s!"`applyMemM` answers `none` at an ND fork — the mirror is fail-closed there (`Step.memop_ptreq` docstring; Round.lean `memop_fork` classifies the round); {recClosure}" },
  { ctor := `CerberusHeapLang.Frag.memop_vals,
    shape := "`PtrEq` at an `SD_Id`-NAMED FUNCTION pointer against a CONCRETE pointer (the only arm that reads the state's `funptrmap`, CerbMem `eqPtrval`; sharpened by the AR5 range audit, C-4)",
    cls := .noRule s!"`wps_memop_ptreq`'s premise `∀ σ, applyMemM (eqPtrval …) σ = some (b, σ)` fixes one verdict at every state; no bundle exposes `funptrmap`; {recAr5}" },
  { ctor := `CerberusHeapLang.Frag.memop_op,
    shape := "`PtrEq` at `PePure` operands (not all values) — the evaluating round",
    cls := .rule (N "wps_memop_eval") (N "wpt_memop_eval") },
  { ctor := `CerberusHeapLang.Frag.store_op,
    shape := "`Store0` (either locking mode) at `PePure` operands (not all values) evaluating to a POINTER and a value — the ACTION_EVAL round; the successor's locking mode is then classified by the `store` rows",
    cls := .rule (N "wps_store_eval") (N "wpt_store_eval") },
  { ctor := `CerberusHeapLang.Frag.case_value,
    shape := "`case v of pats` at a VALUE scrutinee with a matching pattern (the substitution TAU)",
    cls := .rule (N "wps_case_value") (N "wpt_case_value") },
  { ctor := `CerberusHeapLang.Frag.wseq,
    shape := "`letw _ = e1 in e2` — reduction under the frame, then LETW-PURE / LETW-ANNOT",
    cls := .rule (N "wps_wseq") (N "wpt_wseq") },
  -- calls
  { ctor := `CerberusHeapLang.Frag.call,
    shape := "`Eproc` of a DECLARED procedure at matching arity, arguments evaluating, AT THE ROOT of the arena",
    cls := .rule (N "wps_call_root") (N "wpt_call_root") },
  { ctor := `CerberusHeapLang.Frag.call,
    shape := "`Eproc` of a declared procedure at matching arity IN AN EVALUATION CONTEXT (the context is captured on the call stack)",
    cls := .rule (N "wps_call") (N "wpt_call") },
  { ctor := `CerberusHeapLang.Frag.call,
    shape := "`Eproc _ (Impl _) _` — the implementation-constant call (`Step_fs2`)",
    cls := .outOfScope "`callRedex?` answers `none` (`Step.call` docstring); not a `Frag.call` redex; calls arc C2 (docs/2026-09-03_c2-notes.md)" }
]

/-! ## The module classification (scripts/module_classes.tsv) -/

structure ModRow where
  module : Name
  cls : String
  allow : String
  note : String

def classVocabulary : List String :=
  ["core", "production-core", "audit", "positive-client", "declared-smoke",
   "semantic-test", "engine-mirror-test", "production-wrapper", "negative-test",
   "example-support"]

def consumerClasses : List String := ["positive-client", "declared-smoke"]

def readModuleClasses (path : System.FilePath) : IO (Array ModRow) := do
  let txt ← IO.FS.readFile path
  let mut rows : Array ModRow := #[]
  for (line, i) in (txt.splitOn "\n").zipIdx do
    if (trim line).isEmpty || line.startsWith "#" then continue
    let cells := line.splitOn "\t"
    if cells.length != 4 then
      throw <| IO.userError s!"module_classes.tsv:{i+1}: expected 4 TAB-separated cells, got {cells.length}"
    let cls := cells[1]!
    unless classVocabulary.contains cls do
      throw <| IO.userError s!"module_classes.tsv:{i+1}: class `{cls}` not in the vocabulary"
    rows := rows.push { module := cells[0]!.toName, cls := cls, allow := cells[2]!, note := cells[3]! }
  if rows.isEmpty then throw <| IO.userError "module_classes.tsv: no rows"
  return rows

/-! ## Environment reflection -/

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => .anonymous

def isOurs (env : Environment) (n : Name) : Bool :=
  (modOf env n).getRoot == `CerberusHeapLang

def short (n : Name) : String :=
  let s := n.toString
  if s.startsWith "CerberusHeapLang." then (s.drop "CerberusHeapLang.".length).toString else s

/-- Statement + body constants of a constant (theorem bodies included:
    `ConstantInfo.value?` is `none` for theorems in this toolchain). -/
def usedConstants (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++
    (match ci with
     | .thmInfo t => t.value.getUsedConstants
     | .defnInfo d => d.value.getUsedConstants
     | .opaqueInfo o => o.value.getUsedConstants
     | _ => #[])

/-- Transitive import closure of a module (from the environment header). -/
def importClosure (env : Environment) (m : Name) : Std.HashSet Name := Id.run do
  let mods := env.header.moduleNames
  let data := env.header.moduleData
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[m]
  while h : stack.size > 0 do
    let c := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some i := mods.findIdx? (· == c) then
      for imp in data[i]!.imports do stack := stack.push imp.module
  return seen

/-- Memoized dependency table (one `getUsedConstants` per constant). -/
abbrev DepM := StateM (Std.HashMap Name (Array Name))

def depsOf (env : Environment) (n : Name) : DepM (Array Name) := do
  if let some d := (← get).get? n then return d
  let d := match env.find? n with | some ci => usedConstants ci | none => #[]
  modify (·.insert n d)
  return d

/-- The proof-term dependency cone of a set of seeds through OUR
    constants. A constant is expanded only if its module can reach a
    rule module at all (its import closure contains one) — a module
    that imports no rule module cannot lie on a path to a rule, so
    pruning there is sound and skips the relation/engine
    certification's large proof terms. -/
partial def cone (env : Environment) (canReach : Name → Bool) (seeds : Array Name) :
    DepM (Std.HashSet Name) := do
  let mut seen : Std.HashSet Name := {}
  let mut stack := seeds
  while h : stack.size > 0 do
    let c := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains c || !isOurs env c then continue
    seen := seen.insert c
    if !canReach (modOf env c) then continue
    for d in ← depsOf env c do
      if !seen.contains d then stack := stack.push d
  return seen

/-! ## The claim matrix's names (docs/CLAIMS.md) -/

/-- The backticked names in the SECOND cell of every `| C<digits> |` row. -/
def claimNames (txt : String) : Array (String × Array String) := Id.run do
  let mut out : Array (String × Array String) := #[]
  for line in txt.splitOn "\n" do
    let cells := (line.splitOn "|").map trim
    -- a table row `| C1 | … |` splits into ["", "C1", …, ""]
    if cells.length < 3 then continue
    -- the first cell is `C<digits>` optionally followed by prose (`C1 — …`)
    let idCell := cells[1]!
    let id := (idCell.takeWhile Char.isAlphanum).toString
    unless id.startsWith "C" && (id.drop 1).all Char.isDigit && id.length > 1 do continue
    let cell := cells[2]!
    let pieces := cell.splitOn "`"
    -- odd-indexed pieces are the backticked spans
    let mut names : Array String := #[]
    for (p, i) in pieces.zipIdx do
      if i % 2 == 1 then names := names.push p
    out := out.push (id, names)
  return out

/-- E3 range audit D-2: the backticked spans of EVERY cell (the claim cell
    included) of every `| C<digits> |` row, with the cell index. -/
def claimSpansAll (txt : String) : Array (String × Array (Nat × String × Bool)) := Id.run do
  let mut out : Array (String × Array (Nat × String × Bool)) := #[]
  for line in txt.splitOn "\n" do
    let cells := (line.splitOn "|").map trim
    if cells.length < 3 then continue
    let idCell := cells[1]!
    let id := (idCell.takeWhile Char.isAlphanum).toString
    unless id.startsWith "C" && (id.drop 1).all Char.isDigit && id.length > 1 do continue
    let mut spans : Array (Nat × String × Bool) := #[]
    for (cell, k) in cells.zipIdx do
      let pieces := cell.splitOn "`"
      for (p, i) in pieces.zipIdx do
        -- the Bool: the prose directly after the span opens with `(retired` —
        -- the marker a RETIRED export name must carry (E4 range audit N-4)
        if i % 2 == 1 then
          let after := (pieces.getD (i + 1) "").dropWhile Char.isWhitespace
          spans := spans.push (k, p, after.startsWith "(retired" || after.startsWith "(RETIRED")
    out := out.push (id, spans)
  return out

/-- A span that could be a declaration name: an identifier head, then
    identifier characters, `.`, `'`, `?`, `!` or a subscript digit. -/
def isDeclShaped (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs =>
    -- (`||` is Iris's disjointness notation in this environment: spelled out)
    Bool.and (Bool.or c.isAlpha (c == '_'))
      (cs.all fun d => [d.isAlphanum, d == '_', d == '.', d == '\'', d == '?', d == '!',
        Bool.and (decide (d.val ≥ 0x2080)) (decide (d.val ≤ 0x2089))].any id)

/-- The prose tokens of docs/CLAIMS.md that are declaration-shaped but are
    NOT declarations of this package: Core and std.core keywords and
    function names, the engine's names outside `CerberusHeapLang`/`CerbND`,
    hypothesis names quoted from statements, the banned proof methods.
    Extend deliberately (a stale entry — one no row uses — is red). -/
def claimVocabulary : List String :=
  ["Cunseq", "Ecase", "Eccall", "Elet", "End", "Impl", "Ivalignof", "PElet", "Specified", "Unspecified", "__conv_int__",
   "alloc", "bound", "bv_decide", "case", "catch_exceptional_condition",
   "catch_exceptional_condition_add", "conv_int", "conv_loaded_int", "create", "driver2",
   "dynamic_addrs", "eval_uncovered", "free", "hbsz", "hex", "hfuel", "hpost", "htd", "int",
   "is_representable_integer", "kill", "killM", "load", "main", "mk_call_catch_exceptional_condition",
   "mk_conv_int", "native_decide", "panic!", "run", "run_surplus", "stdlib", "store", "unseq",
   "wrapI"]

/-- Former exports RETIRED from the package (deleted; their statements became
    false or were superseded). A claim row may name one ONLY as history, with
    the marker `(retired …)` directly after the backticked span — the name
    check then sees it (E4 range audit N-4, docs/2026-09-05_audit-e4-range.md:
    C13 named two retired theorems unbackticked, invisible to the check). An
    entry that resolves in the environment, or that no row names, is red. -/
def retiredNames : List String :=
  ["t1_unseq_not_frag", "t1_uncovered_exactly_unseq"]

/-- A declaration-shaped span resolves if it is a constant of the environment
    under `CerberusHeapLang.`, at the root, or under `CerbND.`. -/
def resolvesAnywhere (env : Environment) (s : String) : Bool :=
  [N s, s.toName, (`CerbND).append s.toName].any env.contains

/-- The D-2 problems of one claim row: every declaration-shaped span of
    every cell that neither resolves nor is vocabulary. -/
def claimRowProblems (env : Environment) (id : String) (spans : Array (Nat × String × Bool)) :
    Array String := Id.run do
  let mut out : Array String := #[]
  for (k, sp, retiredMarked) in spans do
    unless isDeclShaped sp do continue
    if resolvesAnywhere env sp then
      if retiredNames.contains sp then
        out := out.push s!"docs/CLAIMS.md {id} (cell {k}): `{sp}` is listed in `retiredNames` but IS a constant of the environment — stale retired list"
    else if claimVocabulary.contains sp then pure ()
    else if retiredNames.contains sp then
      unless retiredMarked do
        out := out.push s!"docs/CLAIMS.md {id} (cell {k}): `{sp}` is a RETIRED export named without the `(retired …)` marker directly after it — spell the retirement or drop the name"
    else
      out := out.push s!"docs/CLAIMS.md {id} (cell {k}): `{sp}` is declaration-shaped but is neither a constant of the environment (`CerberusHeapLang.`/root/`CerbND.`), a `claimVocabulary` word, nor a marked `retiredNames` entry"
  return out

/-! ## The report -/

def classLabel : Class → String
  | .rule .. => "RULE"
  | .ruleTotalUndemonstrated .. => "RULE-TOTAL-UNDEMONSTRATED"
  | .rulePartialUndemonstrated .. => "RULE-PARTIAL-UNDEMONSTRATED"
  | .partialOnly .. => "PARTIAL-ONLY"
  | .noRule .. => "NO-RULE"
  | .outOfScope .. => "OUT-OF-SCOPE"

#eval show CoreM Unit from do
  let env ← getEnv
  let some (.inductInfo fragInfo) := env.find? `CerberusHeapLang.Frag
    | throwError "manifest FAIL: inductive CerberusHeapLang.Frag not found"
  let mut red : Nat := 0
  let mut problems : Array String := #[]
  -- ---- the module classification: complete and exact
  let modRows ← readModuleClasses "scripts/module_classes.tsv"
  let pkgMods : Array Name :=
    (env.header.moduleNames.filter fun m => m.getRoot == `CerberusHeapLang && m != `CerberusHeapLang)
    |>.qsort (fun a b => a.toString < b.toString)
  for m in pkgMods do
    unless modRows.any (·.module == m) do
      problems := problems.push s!"module `{short m}` is in the environment but NOT classified in scripts/module_classes.tsv"
      red := red + 1
  for r in modRows do
    unless pkgMods.contains r.module do
      problems := problems.push s!"module_classes.tsv lists `{short r.module}`, which is not a module of the built package"
      red := red + 1
  let consumers : Array Name :=
    (modRows.filter (fun r => consumerClasses.contains r.cls)).map (·.module)
    |>.qsort (fun a b => a.toString < b.toString)
  if consumers.isEmpty then throwError "manifest FAIL: no consumer module classified"
  -- ---- rows vs constructors
  for ctor in fragInfo.ctors do
    unless variants.any (·.ctor == ctor) do
      problems := problems.push s!"constructor `{short ctor}` has NO variant row (MISSING — classify it)"
      red := red + 1
  for v in variants do
    unless fragInfo.ctors.contains v.ctor do
      problems := problems.push s!"variant row names `{short v.ctor}`, not a constructor of `Frag` (stale row)"
      red := red + 1
  -- ---- the rule names and their consumers
  let ruleNames : Array Name := Id.run do
    let mut s : Array Name := #[]
    for v in variants do
      match v.cls with
      | .rule p t => s := s.push p |>.push t
      | .ruleTotalUndemonstrated p t _ => s := s.push p |>.push t
      | .partialOnly p _ => s := s.push p
      | _ => pure ()
    return s
  let ruleMods : Std.HashSet Name := Id.run do
    let mut s : Std.HashSet Name := {}
    for r in ruleNames do
      if env.contains r then s := s.insert (modOf env r)
    return s
  let closures : Std.HashMap Name (Std.HashSet Name) := Id.run do
    let mut m : Std.HashMap Name (Std.HashSet Name) := {}
    for mod in env.header.moduleNames do
      if mod.getRoot == `CerberusHeapLang then m := m.insert mod (importClosure env mod)
    return m
  let canReach (mod : Name) : Bool :=
    match closures.get? mod with
    | some cl => ruleMods.any (fun r => cl.contains r)
    | none => true  -- unknown module: never prune (fail-closed)
  let byModule : Std.HashMap Name (Array Name) := env.constants.fold
    (fun acc n _ =>
      if n.isInternalDetail then acc else
      let m := modOf env n
      if m.getRoot == `CerberusHeapLang then acc.insert m ((acc.getD m #[]).push n) else acc) {}
  let mut table : Std.HashMap Name (Array Name) := {}
  let mut cones : Array (Name × Std.HashSet Name) := #[]
  for c in consumers do
    let (cn, table') := (cone env canReach (byModule.getD c #[])).run table
    table := table'
    cones := cones.push (c, cn)
  let usersOf (r : Name) : List String :=
    (cones.filter (fun (_, c) => c.contains r) |>.map (fun (m, _) => short m)).toList
  -- a rule cell: the name, its status, its consumers; returns (cell, ok)
  let ruleCell (r : Name) : String × Bool :=
    match env.find? r with
    | some (.thmInfo _) =>
      let us := usersOf r
      if us.isEmpty then (s!"`{short r}` — **RED: consumed by no consumer module**", false)
      else (s!"`{short r}` — {", ".intercalate us}", true)
    | some _ => (s!"`{short r}` — **RED: exists but is not a theorem**", false)
    | none => (s!"`{short r}` — **RED: not in the environment**", false)
  let alsoCell (ns : List Name) : String × Bool := Id.run do
    let mut ok := true
    let mut parts : Array String := #[]
    for n in ns do
      match env.find? n with
      | some (.thmInfo _) => parts := parts.push s!"`{short n}`"
      | some _ => parts := parts.push s!"`{short n}` **RED: not a theorem**"; ok := false
      | none => parts := parts.push s!"`{short n}` **RED: missing**"; ok := false
    return (if parts.isEmpty then "" else " Also: " ++ ", ".intercalate parts.toList ++ ".", ok)
  let mut lines : Array String := #[]
  let mut nRule := 0; let mut nRuleU := 0; let mut nRuleP := 0; let mut nPartial := 0; let mut nNoRule := 0; let mut nOut := 0
  for v in variants do
    let (also, okA) := alsoCell v.also
    if !okA then red := red + 1
    match v.cls with
    | .rule p t =>
      nRule := nRule + 1
      let (cp, okP) := ruleCell p
      let (ct, okT) := ruleCell t
      if !okP then red := red + 1
      if !okT then red := red + 1
      lines := lines.push s!"| `{short v.ctor}` | {v.shape} | RULE | {cp} | {ct} |{also} |"
    | .ruleTotalUndemonstrated p t mover =>
      nRuleU := nRuleU + 1
      let (cp, okP) := ruleCell p
      if !okP then red := red + 1
      let (ct, okT) : String × Bool := match env.find? t with
        | some (.thmInfo _) =>
          let us := usersOf t
          if us.isEmpty then (s!"`{short t}` — exists, proved, consumed by NO consumer module", true)
          else (s!"`{short t}` — **RED: now consumed by {", ".intercalate us} — reclassify the row as RULE**", false)
        | some _ => (s!"`{short t}` — **RED: exists but is not a theorem**", false)
        | none => (s!"`{short t}` — **RED: not in the environment**", false)
      if !okT then red := red + 1
      lines := lines.push s!"| `{short v.ctor}` | {v.shape} | RULE-TOTAL-UNDEMONSTRATED | {cp} | {ct} | mover: {mover}{also} |"
    | .rulePartialUndemonstrated p t mover =>
      nRuleP := nRuleP + 1
      let (ct, okT) := ruleCell t
      if !okT then red := red + 1
      let (cp, okP) : String × Bool := match env.find? p with
        | some (.thmInfo _) =>
          let us := usersOf p
          if us.isEmpty then (s!"`{short p}` — exists, proved, consumed by NO consumer module", true)
          else (s!"`{short p}` — **RED: now consumed by {", ".intercalate us} — reclassify the row as RULE**", false)
        | some _ => (s!"`{short p}` — **RED: exists but is not a theorem**", false)
        | none => (s!"`{short p}` — **RED: not in the environment**", false)
      if !okP then red := red + 1
      lines := lines.push s!"| `{short v.ctor}` | {v.shape} | RULE-PARTIAL-UNDEMONSTRATED | {cp} | {ct} | mover: {mover}{also} |"
    | .partialOnly p why =>
      nPartial := nPartial + 1
      let (cp, okP) := ruleCell p
      if !okP then red := red + 1
      lines := lines.push s!"| `{short v.ctor}` | {v.shape} | PARTIAL-ONLY | {cp} | — | {why}{also} |"
    | .noRule why =>
      nNoRule := nNoRule + 1
      lines := lines.push s!"| `{short v.ctor}` | {v.shape} | NO-RULE | — | — | {why}{also} |"
    | .outOfScope why =>
      nOut := nOut + 1
      lines := lines.push s!"| `{short v.ctor}` | {v.shape} | OUT-OF-SCOPE | — | — | {why}{also} |"
  -- ---- the claim matrix's names
  let claimsTxt ← IO.FS.readFile "docs/CLAIMS.md"
  let claims := claimNames claimsTxt
  if claims.isEmpty then
    problems := problems.push "docs/CLAIMS.md: no `| C<n> |` claim rows found (the matrix is unparseable or empty)"
    red := red + 1
  let mut nClaimNames := 0
  for (id, names) in claims do
    if names.isEmpty then
      problems := problems.push s!"docs/CLAIMS.md {id}: no backticked declaration in the `Exported theorem(s)` cell"
      red := red + 1
    for s in names do
      nClaimNames := nClaimNames + 1
      let n := N s
      match env.find? n with
      | some (.thmInfo _) | some (.defnInfo _) | some (.inductInfo _) => pure ()
      | some _ =>
        problems := problems.push s!"docs/CLAIMS.md {id}: `{s}` exists but is neither a theorem, a definition nor an inductive"
        red := red + 1
      | none =>
        problems := problems.push s!"docs/CLAIMS.md {id}: `{s}` is not in the environment"
        red := red + 1
  -- ---- D-2: every declaration-shaped span of every cell (planted)
  let allSpans := claimSpansAll claimsTxt
  let mut nAllSpans := 0
  let mut usedVocab : Array String := #[]
  let mut usedRetired : Array String := #[]
  for (id, spans) in allSpans do
    for (_, sp, _) in spans do
      if isDeclShaped sp then
        nAllSpans := nAllSpans + 1
        if Bool.and (claimVocabulary.contains sp) (!usedVocab.contains sp) then usedVocab := usedVocab.push sp
        if Bool.and (retiredNames.contains sp) (!usedRetired.contains sp) then usedRetired := usedRetired.push sp
    for pr in claimRowProblems env id spans do
      problems := problems.push pr
      red := red + 1
  for w in claimVocabulary do
    unless usedVocab.contains w do
      problems := problems.push s!"docs/CLAIMS.md: `claimVocabulary` word `{w}` is used by no claim row — stale vocabulary (remove it)"
      red := red + 1
  for w in retiredNames do
    unless usedRetired.contains w do
      problems := problems.push s!"docs/CLAIMS.md: `retiredNames` entry `{w}` is named by no claim row — stale retired list (remove it)"
      red := red + 1
  -- the plant: a row naming a deleted theorem in its PROSE cell must be red
  let plantRow := "| C0 — plant: the E2 exclusion `t1_case_uncovered` (deleted at E3) named as current state | `engine_step_matchU` | semantic | — | — | — | — |"
  let plantSpans := claimSpansAll plantRow
  let plantProblems := plantSpans.foldl (fun acc (id, spans) => acc ++ claimRowProblems env id spans) #[]
  if plantProblems.isEmpty then
    problems := problems.push "docs/CLAIMS.md name check PLANT: a row naming the deleted `t1_case_uncovered` in its prose cell came out clean — the D-2 check is vacuous"
    red := red + 1
  -- plant 2 (E4 range audit N-4): a retired export named WITHOUT its marker must be
  -- red; the same span WITH the marker must be clean (else the marker path is broken)
  let plantRow2 := "| C0 — plant: E3's witness `t1_unseq_not_frag` named as if current | `engine_step_matchU` | semantic | — | — | — | — |"
  let plantProblems2 := (claimSpansAll plantRow2).foldl (fun acc (id, spans) => acc ++ claimRowProblems env id spans) #[]
  if plantProblems2.isEmpty then
    problems := problems.push "docs/CLAIMS.md name check PLANT 2: a row naming the retired `t1_unseq_not_frag` without the `(retired …)` marker came out clean — the retired-name check is vacuous"
    red := red + 1
  let controlRow2 := "| C0 — control: E3's witness `t1_unseq_not_frag` (retired at E4) named as history | `engine_step_matchU` | semantic | — | — | — | — |"
  let controlProblems2 := (claimSpansAll controlRow2).foldl (fun acc (id, spans) => acc ++ claimRowProblems env id spans) #[]
  unless controlProblems2.isEmpty do
    problems := problems.push s!"docs/CLAIMS.md name check CONTROL 2: a row naming the retired `t1_unseq_not_frag` WITH the `(retired …)` marker came out red — the marker path is broken: {controlProblems2}"
    red := red + 1
  -- ---- print
  IO.println "# The rule-use and classification manifest"
  IO.println ""
  IO.println "GENERATED by `scripts/capability_manifest.lean` — do not hand-edit; regenerate with"
  IO.println "`../scripts/capped ~/.elan/bin/lake env lean scripts/capability_manifest.lean > docs/CAPABILITY_MANIFEST.md`"
  IO.println "(from `cerberus-heaplang/`). A claim-point SPEEDBUMP report ([USER 2026-09-02]):"
  IO.println "`scripts/test_unit.sh` regenerates it and reports drift or a red row."
  IO.println ""
  IO.println "WHAT GREEN ESTABLISHES, EXACTLY. (1) The hand-maintained variant table below"
  IO.println "(`variants` in the generator: the engine-SUCCESS shapes of every `Frag`"
  IO.println "constructor, read off `Frag`, `Step` and the engine's memory-operation arms)"
  IO.println "covers every constructor of `Frag` in the built environment and names no stale"
  IO.println "constructor. (2) Every theorem a row names exists and is a theorem. (3) Every"
  IO.println "RULE row's partial AND total rule, and every PARTIAL-ONLY row's rule, lies in"
  IO.println "the proof-term dependency cone of at least one CONSUMER module — the modules"
  IO.println "classified `positive-client` or `declared-smoke` in `scripts/module_classes.tsv`"
  IO.println "— listed in the row. An UNDEMONSTRATED row instead checks that its named"
  IO.println "side has no consumer and the other side does; both rules must exist."
  IO.println "A new consumer on the missing side requires reclassification to RULE."
  IO.println "(4) The module classification is complete and exact"
  IO.println "(every package module classified; every classified module present; classes in"
  IO.println "the vocabulary). (5) Every declaration the claim matrix `docs/CLAIMS.md` names"
  IO.println "exists, and every declaration-shaped backticked span of every cell of a claim row"
  IO.println "is a constant of the environment or a listed vocabulary word (planted)."
  IO.println "GREEN DOES NOT ESTABLISH that the variant table is exhaustive over the"
  IO.println "engine's success shapes (it is a reviewed reading, not a theorem), that a rule is"
  IO.println "the strongest statement of its variant, or that a consumer's dependency on a rule"
  IO.println "is the load-bearing step of its headline proof rather than incidental. A"
  IO.println "NO-RULE or OUT-OF-SCOPE row is a stated absence, not coverage: programs"
  IO.println "exercising those shapes are outside the logic (the reason and the deciding"
  IO.println "record are in the row). Engine kills/UB/panics are not rows (not successes;"
  IO.println "classified in Round.lean)."
  IO.println ""
  IO.println "## Module classification (from `scripts/module_classes.tsv`; the one authoritative list)"
  IO.println ""
  IO.println "| Module | Class | Manifest consumer | Boundary-check internals allowance | Note |"
  IO.println "|---|---|---|---|---|"
  for r in modRows.qsort (fun a b => a.module.toString < b.module.toString) do
    let cons := if consumerClasses.contains r.cls then "yes" else "no"
    let allow := if r.allow == "-" then "—" else r.allow
    IO.println s!"| `{short r.module}` | {r.cls} | {cons} | {allow} | {r.note} |"
  IO.println ""
  IO.println s!"MODULES: {modRows.size} classified, {consumers.size} consumer modules ({", ".intercalate (consumers.toList.map short)})"
  IO.println ""
  IO.println "## Variant rows"
  IO.println ""
  IO.println "| Fragment constructor | Variant (an engine-success shape) | Class | Partial rule — consumers | Total rule — consumers | Reason / record |"
  IO.println "|---|---|---|---|---|---|"
  for l in lines do IO.println l
  IO.println ""
  IO.println s!"MANIFEST: {fragInfo.ctors.length} constructors, {variants.length} variant rows ({nRule} RULE, {nRuleU} RULE-TOTAL-UNDEMONSTRATED, {nRuleP} RULE-PARTIAL-UNDEMONSTRATED, {nPartial} PARTIAL-ONLY, {nNoRule} NO-RULE, {nOut} OUT-OF-SCOPE), {red} red, {consumers.size} consumer modules"
  IO.println s!"CLAIMS: {claims.size} claim rows, {nClaimNames} declaration names checked in the theorem cell, {nAllSpans} declaration-shaped spans checked across every cell ({claimVocabulary.length} vocabulary words, {retiredNames.length} retired names); plants (deleted name in a prose cell; retired name without its marker) red as expected"
  if !problems.isEmpty then
    IO.println ""
    IO.println "## PROBLEMS"
    IO.println ""
    for p in problems do IO.println s!"- **RED**: {p}"
  if red > 0 then
    throwError "capability manifest: {red} red finding(s) — see the table and PROBLEMS above"

end CapabilityManifest
