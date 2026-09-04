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
6. the claim matrix docs/CLAIMS.md names only existing declarations (the
   backticked names in the second cell, `Exported theorem(s)`, of every
   table row whose first cell begins `C<digits>`).

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
    cls := .ruleTotalUndemonstrated (N "wps_load") (N "wpt_load")
      "a total exhibit loading a WHOLE cell (every total client loads through a view, `wpt_load_at`)",
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
  { ctor := `CerberusHeapLang.Frag.pure_sym,
    shape := "`pure(x)` at a symbol BOUND in the environment (the PURE round through the certified evaluator)",
    cls := .rule (N "wps_pure") (N "wpt_pure") },
  { ctor := `CerberusHeapLang.Frag.pure_sym,
    shape := "`pure(x)` at a symbol UNBOUND in the environment but naming a `Proc` of the file (the engine evaluates it to the null function pointer)",
    cls := .outOfScope s!"the mirror evaluator answers `none`; the characterized residual `OpenRound.eval_uncovered` (`evalClass` `.uncovered` at the leaf); {recClosure}" },
  { ctor := `CerberusHeapLang.Frag.load_op,
    shape := "`Load0` at a `PePure` pointer operand evaluating to a POINTER (the ACTION_EVAL round)",
    cls := .rule (N "wps_load_eval") (N "wpt_load_eval") },
  { ctor := `CerberusHeapLang.Frag.sseq_sym,
    shape := "`lets x = e1 in e2` at a `BareHead` head delivering a BARE value (LETS-PURE; the head grammar admits a call since C4)",
    cls := .rule (N "wps_seq_sym") (N "wpt_seq_sym") },
  { ctor := `CerberusHeapLang.Frag.sseq_sym,
    shape := "`lets x = e1 in e2` whose head delivers an ANNOTATED value `{A}v` (the engine's LETS-ANNOT at the symbol binder)",
    cls := .outOfScope s!"excluded by the fragment: `Frag.sseq_sym` carries `hb : BareHead e1`, and every `BareHead` delivers a bare value (`BareHead.not_annot`); the mirror has no LETS-ANNOT rule at this binder (`Step.sseq_sym_pure` docstring); {recClosure}" },
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
    cls := .ruleTotalUndemonstrated (N "wps_case_value") (N "wpt_case_value")
      "a total twin of `CaseExhibit` (its consumer is partial-only)" },
  { ctor := `CerberusHeapLang.Frag.wseq,
    shape := "`letw _ = e1 in e2` — reduction under the frame, then LETW-PURE / LETW-ANNOT",
    cls := .ruleTotalUndemonstrated (N "wps_wseq") (N "wpt_wseq")
      "a total twin of `WseqExhibit` (its consumer is partial-only)" },
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

/-! ## The report -/

def classLabel : Class → String
  | .rule .. => "RULE"
  | .ruleTotalUndemonstrated .. => "RULE-TOTAL-UNDEMONSTRATED"
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
  let mut nRule := 0; let mut nRuleU := 0; let mut nPartial := 0; let mut nNoRule := 0; let mut nOut := 0
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
  IO.println "— listed in the row. (4) The module classification is complete and exact"
  IO.println "(every package module classified; every classified module present; classes in"
  IO.println "the vocabulary). (5) Every declaration the claim matrix `docs/CLAIMS.md` names"
  IO.println "exists. GREEN DOES NOT ESTABLISH that the variant table is exhaustive over the"
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
  IO.println s!"MANIFEST: {fragInfo.ctors.length} constructors, {variants.length} variant rows ({nRule} RULE, {nRuleU} RULE-TOTAL-UNDEMONSTRATED, {nPartial} PARTIAL-ONLY, {nNoRule} NO-RULE, {nOut} OUT-OF-SCOPE), {red} red, {consumers.size} consumer modules"
  IO.println s!"CLAIMS: {claims.size} claim rows, {nClaimNames} declaration names checked"
  if !problems.isEmpty then
    IO.println ""
    IO.println "## PROBLEMS"
    IO.println ""
    for p in problems do IO.println s!"- **RED**: {p}"
  if red > 0 then
    throwError "capability manifest: {red} red finding(s) — see the table and PROBLEMS above"

end CapabilityManifest
