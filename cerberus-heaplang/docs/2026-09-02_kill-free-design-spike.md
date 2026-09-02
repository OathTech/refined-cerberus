# KILL/FREE design spike — the dispose rule for cerberus-heaplang

READ-ONLY spike (no builds; grep and read only), 2026-09-02, branch
`design-kill-calls` @ 0395dba. Pinned semantics: `.cerberus-ws` primed
from cerberus-lean `ddcfc9199` (`.primed-from`, measured). Every
`file:line` below is MEASURED against that tree or this package at
0395dba unless labelled ESTIMATE. Provenance: every design choice here is
[AGENT]; nothing is adopted until a charter is [USER]-blessed.
Rulings answered: DECISIONS 2026-09-02 "THE DEMO IS CLASSICAL SEPARATION
LOGIC OVER CORE" (dispose = the post-audit kill arc), "THE DEMO'S ACCEPTANCE
GOALS" (goal 3, sequenced with this arc), the mirror-completeness charter
(every new constructor carries a completeness obligation), one-change-at-a-time.

## 0. Engine facts (measured, verbatim where load-bearing)

**The constructor.** `generated/Core.lean:974-979` `inductive kill_kind
| Dynamic0 | Static0 : ctype → kill_kind`; `:996` `is_dynamic : kill_kind →
Bool`; `:1008` `| Kill : kill_kind → (generic_pexpr bty sym) →
generic_action_ bty sym /- the boolean indicates whether the action is
dynamic (i.e. free()) -/`. Surface syntax (`CoreParser.lean:1442-1456`):
`free(pe)` parses to `Kill Dynamic0 pe`; `kill(ct, pe)` to `Kill (Static0
ct) pe`. The request payload (`Core_reduction.lean:149`): `KillRequest2 :
Bool → CerbMem.PointerValue → (aid → a) → action_request2 a`.

**Dispatch** — `step_action`'s Kill arm, `Core_reduction.lean:424` (col
7720), verbatim modulo whitespace:

```
| Kill kind1 pe => ( match act_valueFromPexpr pe with
  | some (Vobject (OVpointer ptrval)) =>
      ACTION_REQUEST "KillRequest" loc1
        (KillRequest2 (is_dynamic kind1) ptrval (fun (aid1 : Nat) => mk_value_e Vunit))
  | some _ => ACTION_ILLTYPED "Kill"
  | none => ACTION_EVAL "eval operand of Kill"
        (stExceptUndef_bind (full_eval_pexpr1 pe) (fun (cval : value) =>
          stExceptUndef_return (wrap (Kill kind1 (mk_value_pe cval))))) )
```

Three arms, exactly as store/load: value operand that is a pointer →
request; value operand of any other shape → ILLTYPED; non-value operand →
EVAL to `Kill kind1 (mk_value_pe cval)` for ANY `cval` (the pointer check
happens in the next round). The `Static0 ty` payload is DISCARDED — only
`is_dynamic kind1` reaches the request; the engine never compares the
kill type with the allocation type. `step_ctx`'s `process_action`
(`Core_reduction.lean:484`, col 5704) rewraps the continuation
`KillRequest2 is_dynamic1 ptrval (fun aid1 => wrap_expr (mk_expr' aid1))`
into `Step_action_request2`; ACTION_EVAL becomes `Step_with_runstate2
(RSK_eval …)`; ILLTYPED becomes `Step_error2 str`. Continuation value:
`mk_value_e Vunit` — a BARE unit, no `Eannot [DA_pos …]` residue (unlike
store/load, like create).

**Driver discharge** — `Driver.lean:273` (col 4288), verbatim modulo
whitespace: `| KillRequest2 is_dynamic1 ptr_val mk_th_st' => … nd_bind
(liftMem (CerbMem.killM loc1 is_dynamic1 ptr_val)) (fun (_ : Unit) =>
nd_update (fun dr_st => { { dr_st with trace := ME_kill loc1 is_dynamic1
ptr_val :: dr_st.trace } with core_state0 := update_thread_state tid1
(mk_th_st' aid1) dr_st.core_state0 }))`. Same protocol as create.

**`killM`** — `generated/CerbMem.lean:1555-1580` (hand-written seam,
mirrors impl_mem.ml:1464+). `ND fun st => …`, DETERMINISTIC: every arm is
`NDactive ()` or `NDkilled (failReason err loc)`; no `NDnd`/`msum`
(measured: the only `msum` in CerbMem.lean is `eqPtrval`, :1740-1788).
Arms:

| pointer | isDynamic | outcome | UB class (`Mem_common.lean:392`) |
|---|---|---|---|
| `PVnull` | true | `NDactive ()`, state unchanged (`free(NULL)`) | — |
| `PVnull` | false | `MerrUndefinedFree Free_non_matching` | UB179a |
| `PVfunction` | any | `Free_non_matching` | UB179a |
| `Prov_some id`, concrete, `deadAllocations.contains id` | any | `Free_dead_allocation` (:1567) | UB179b |
| … `allocations.get? id = none` | any | `Free_non_matching` (:1569) | UB179a |
| … `addr != alloc.base` | any | `Free_out_of_bound` (:1572) | **none → `kill_reason.Other`** (non-UB kill) |
| … `isDynamic && base ∉ dynamicAddrs` | true | `Free_non_matching` (:1574) | UB179a |
| … otherwise | any | `NDactive ()`, `st' = { st with deadAllocations := id :: …, allocations := allocations.erase id }` (:1577-1578) | — |
| `Prov_none`/`Prov_device`/`Prov_symbolic` concrete | any | `Free_non_matching` (:1580) | UB179a |

Consequences (measured): `lastAddress`, `nextAllocId`, `dynamicAddrs`,
`bytemap` are UNTOUCHED by kill — the bytes stay; the allocation RECORD
is ERASED (so base/size of a dead allocation are not recoverable from
`σ`); ids and addresses are never reused (the only writers of
`lastAddress`/`nextAllocId` are `allocateObject` :1522 and
`allocateRegion` :1546, both monotone; `allocations :=` writers: insert
:1523/:1547, erase :1578, `map` preserving base/size :1690 (store
`isLocking`), prefix-only update :2096). `allocateObject` (:1504-1531)
does NOT record `dynamicAddrs` (only `allocateRegion` :1548 does), so
`free(p)` of a `create`d object is UB179a: for this fragment the honest
dispose is `kill(static ty, p)`; `Kill Dynamic0` pairs with `Alloc0`
(malloc), which is not in the fragment.

**Deadness checks elsewhere**: `loadM` :1654-1655 fails `DeadPtr` (UB010)
on `deadAllocations.contains` before the record lookup; `storeM`
:1714-1720 has NO dead check — a killed id is caught by `allocations.get?
= none → MerrOutsideLifetime` (UB009), which is why the erasure matters.
`CellCoh`/`MetaCoh` (Heap.lean:325-345, :833-838) carry both `dead` and
`alloc`; `CohG` (Heap.lean:1464-1484) adds `cur_dead`/`cur_alloc` under
cursor presence. **The package's driver projection today**: `dischargeStep`
(Soundness.lean:153-190) has Store/Load/Create arms and `| _ =>
.offFragment` (:189) — a kill request is currently OFF-FRAGMENT. Adding
the arm changes a hand-written proof device that is the referent of every
PROVISIONAL (`driveU`) export: their texts do not change and their proofs
never reach that arm, but `outcomesU` at kill rounds changes from
off-fragment to the discharged `killM`. Named so the slice record says it.

## 1. THE RULE

Classical `{p ↦ _} dispose(p) {emp}`. Kill needs (i) a live record, (ii)
the pointer AT the base, (iii) a kind matching the allocation's origin;
nothing about bytes, type or size. The logic must consume the EXCLUSIVE
metadata cell (it proves (i)-(ii) through `MetaCoh` and makes `emp` sound:
no fraction may survive claiming liveness) and, classically, the whole
byte range; both live at one fraction inside `pointsToCell`, so the
precondition is the full cell. Proposed statements (ESTIMATE of exact
text; shapes mirror `wps_create`/`wps_store`):

```
def killExpr (loc : CerbLocation.Loc) (ann : core_run_annotation) (kind : kill_kind)
    (pv : CerbMem.PointerValue) : CoreExpr :=
  Expr [] (Eaction (Paction polarity.Pos (Action loc ann
    (Kill kind (Pexpr [] () (PEval (Vobject (OVpointer pv))))))))

theorem kill_atomic [SpikeGS hlc GF] {M : MachineCtx} (loc ann) (kind : kill_kind)
    (pv : CerbMem.PointerValue) (ty : ctype) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hstatic : is_dynamic kind = false) :
    AtomicStep M (killExpr loc ann kind pv) ρ 1
      (pointsToCell M.tagDefs pv (.own 1) ty bs)
      (fun w => iprop(⌜w = SpikeVal.pure Vunit⌝))

theorem wps_kill {Ψ} (loc ann) (kind : kill_kind) (pv) (ty) (bs) (ρ)
    (hstatic : is_dynamic kind = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗ Ψ (SpikeVal.pure Vunit) ρ) ⊢
      wps M Ls Ψ (killExpr loc ann kind pv) ρ

theorem wpt_kill {Ψ} … {k : Nat} (hk : 2 ≤ k) (hstatic : is_dynamic kind = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗ Ψ (SpikeVal.pure Vunit) ρ) ⊢
      wpt M Ls k Ψ (killExpr loc ann kind pv) ρ

theorem wps_kill_eval {Ψ} (loc ann) (kind) (pe : generic_pexpr Unit sym) (ρ) {pv}
    (hnv : valueFromPexpr pe = none)
    (hv : evalPexpr M.tagDefs M.extern ρ pe = some (Vobject (OVpointer pv))) :
    wps M Ls Ψ (killExpr loc ann kind pv) ρ ⊢ wps M Ls Ψ (killOpRedex loc ann kind pe) ρ
-- wpt_kill_eval: the same at budget k+1 ⊢ k, as wpt_load_eval.
```

Design points. (a) Generic in `kind` with the pure premise `is_dynamic kind
= false`, not specialised to `Static0 ty`: the engine ignores the type
payload (§0), so pinning `kty = ty` would be an invented obligation; the
dynamic form is excluded by a real Cerberus fact (no `dynamicAddrs` entry
for `create`d objects). When the malloc/free arc adds `Alloc0`, `MetaCell`
gains `dynamic : Bool` and the premise becomes `is_dynamic kind =
mc.dynamic`. (b) Bare `Vunit` post at `deliveryCost 1`, so `wpt_kill`'s
bound is `2 ≤ k` as `wpt_create`. (c) Nothing is handed back (§2 for the
optional dead-cell face). (d) Persistent stratum: `allocMeta`/`locInBounds`
are the cell at `.discard`; `pointsToCell … (.own 1)` carries `metaOwn id
(.own 1)`, and `.own 1 ∗ .discard` is invalid (`pointsTo_op_cmraValid`), so
holding the killable cell PROVES no persistent knowledge of it exists.
Persisting metadata = giving up the right to dispose — RefinedC's
`alloc_global := alloc_alive id DfracDiscarded true`
(`deps/refinedc/theories/caesium/ghost_state.v:104-105`); no `allocMeta`
rule needs an "alive" side condition. This is true of Cerberus only
because kill erases the record (§0): there is no fact about a dead
allocation's range to keep, so RefinedC's persistent-past-death
`alloc_meta` has no referent here — forcing fact, bin (b).

## 2. THE LIVENESS TOKEN

Constraint discovered (measured): iris-lean's GenHeap has
`genHeap_alloc/_alloc_big/_update/_valid` and `pointsTo_persist`
(`deps/iris-lean/Iris/Iris/BI/Lib/GenHeap.lean:398-458`, :194) but NO
delete — `genHeapInterp` couples the meta-token map's domain to the
heap's (`Hdom`, used at :470), the same reason Iris HeapLang has no free.
A "delete the metadata cell on kill" design is therefore not a local
wrapper; it would be an upstream request. Ruled out for this arc.

Alternatives weighed:
- (A) A fourth GenHeap `alive : Int ↦ Bool` (RefinedC's
  `heap_alloc_alive_map`, `ghost_state.v:90-95`), tokens outside the
  bundles: `CohG.metas` becomes conditional on the alive map, a fractional
  `pointsToCell` no longer implies `MetaCoh`, so every load/store
  statement, `wps_create`'s post, `launchResources` and the frame theorem
  gain an `alive` fragment. RefinedC avoids that churn only through
  "bytes mapped ⇒ alive" (`heap.v:564-567`), which Cerberus does not
  offer (bytes survive kill). Rejected: maximal statement churn.
- (B) Delete on kill — excluded above.
- (C) **CHOSEN.** `MetaCell` gains `alive : Bool` (RefinedC's `al_alive`;
  their `alloc_alive_kill` is exactly a `ghost_map_update` to `false`,
  `ghost_state.v:344-347`). The liveness/freeability TOKEN is `metaOwn id
  (.own 1) ⟨a, ty, n, true⟩`, which the bundles already carry at `dq`.
  Kill = `metaHeap_update` (existing op) to `alive := false`; the byte
  fragments are dropped (affine BI; stale auth byte entries are sound —
  `CohG.bytes` is about `σ.bytemap`, which kill does not touch, and
  addresses are never reused, so `CohG.create`'s `cur_byte_lo` argument
  is unaffected). `CohG.metas`: alive cells satisfy `MetaCoh`; dead cells
  satisfy `σ.deadAllocations.contains id = true ∧ σ.allocations.get? id =
  none`; `metas_disj` stays over all cells (dead ranges are never reused;
  preserved by kill trivially, by create via `cur_meta_lo` as today). This
  is RefinedC's `freeable l n k := alloc_meta … al_alive := true ∗
  alloc_alive id (own 1) true` (`ghost_state.v:167-169`) collapsed into
  one cell — forced by the erasure fact of §1(d).

How the three operations see it: `create` mints the cell with `alive :=
true` (`metaHeap_alloc`, `CohG.create` unchanged in shape); `kill`
requires `.own 1` and flips it; `load`/`store` today require
`pointsToCell dq` whose `MetaCoh` (via the alive branch) gives not-dead
and allocated — liveness already lives in that coupling, and it STAYS
there. So the token is not a new resource and NO existing public
statement changes: `pointsToCell/cellOwn/pointsToView/allocMeta/
locInBounds/allocCap` keep their signatures; every `wps_*`/`wpt_*` rule,
`AtomicStep`, `MemTripleU(_alloc)`, the projection theorems and the four
production statements are textually unchanged. The signature-snapshot
delta of the internals slice (ESTIMATE, from the `⟨a, aty, size⟩` literal
sites in Heap.lean): `MetaCell.mk` (ctor), `metaOf`, `pointsToView_iff`,
`cellOwn_iff`, `MetaCoh`/`CohG.mk` (ctors/fields), `CohG.create`,
`CohG.storeRange`, `MetaByteOf`, `LaunchCoh.cohG`, `metaHeap_alloc`'s
call sites — all below the API line (API.lean lists none of them).
Optional derived face, later: `deadMeta id a ty := metaOwn id .discard
⟨a,ty,n,false⟩` (persist the dead cell) — the "true fact about a dead
allocation" the prompt asks about, stated as ghost knowledge (`CohG`
gives `deadAllocations.contains id`); not in the classical rule.

The professor's `isReadonly` remark (review 1 §4, review 2 "Read-only
allocations") is the SAME mechanism (a `MetaCell` field with the store
rule alone demanding it); it is a separate spec slice, not folded in.

## 3. THE GLOBAL MEMORY WELL-FORMEDNESS INVARIANT (goal 3)

Definition (pure, Heap.lean, ESTIMATE of fields):

```
structure MemWF (σ : Mem) : Prop where
  live_lt  : ∀ id al, σ.allocations.get? id = some al → id < σ.nextAllocId
  dead_lt  : ∀ id, σ.deadAllocations.contains id = true → id < σ.nextAllocId
  live_dead : ∀ id al, σ.allocations.get? id = some al →
                σ.deadAllocations.contains id = false
  disj     : ∀ i j ai aj, i ≠ j → σ.allocations.get? i = some ai →
                σ.allocations.get? j = some aj →
                ai.base + ai.size ≤ aj.base ∨ aj.base + aj.size ≤ ai.base
  cursor_lo : ∀ id al, σ.allocations.get? id = some al → σ.lastAddress ≤ al.base
  size_pos : ∀ id al, σ.allocations.get? id = some al → 0 < al.size
  la_wf    : σ.lastAddress ≤ 2 ^ 64
```

No byte-range component: `readBytesFrom` (CerbMem.lean:1462-1466)
defaults a missing key to the unspecified byte, so "every allocated
address is mapped" (RefinedC's `heap_state_alloc_alive_in_heap`,
`heap.v:588-592`) has no Cerberus content — forcing fact, dropped.

Where it lives: `wf : MemWF σ` as a field of `CohG` (state
interpretation) AND of `LaunchCoh` (launch premise). Then
`LaunchCoh.fresh_alloc/fresh_dead` and `CohG.cur_dead/cur_alloc` become
consequences of `live_lt`/`dead_lt` and are retired (fewer fields, same
public statements). "Every live allocation is above the cursor" IS an
engine invariant by construction: the only cursor writers set
`lastAddress := alignedAddr` = the new base with `base + size ≤ old
lastAddress` (`freshBase_add_le`, Heap.lean:993, already proved), and
kill leaves the cursor alone (§0). Hence "fresh" for `create` becomes:
the new range is disjoint from EVERY live allocation of `σ` — provable
from `cursor_lo` + `freshBase_add_le`, closing the detailed audit's M-1
(`docs/2026-09-02_cerberus-heaplang-detailed-audit.md:279-318`). It does
not (cannot) speak about erased dead ranges.

Initialisation: `prodMem₀_memWF` from `prodMem₀_allocations` (`ProdEntry.lean:207-209`,
exactly `insert 0 errnoAllocRec`), `_deadAllocations = []` (:211),
`_nextAllocId = 1` (:203), `_lastAddress = errnoAddr` (:205) — one-allocation
case analysis, `decide`-class. Preservation, ranked: `allocateObject` —
MEDIUM (`TreeMap.get?_insert` split, `disj` via `cursor_lo` +
`freshBase_add_le`; folds into `CohG.create`); `killM` — SMALL (`erase`
shrinks `live_*`/`disj`/`cursor_lo`; `dead_lt` from `live_lt` of the
erased id; `Std.TreeMap.getElem?_erase`/`contains_erase` exist in the
4.32 Std); `loadM` — TRIVIAL (returns `σ`); `storeM` — TRIVIAL except the
`isLocking` `allocations.map` (base/size preserved; one lemma if the
rules stay at arbitrary `lk`).

## 4. MIRROR + COMPLETENESS OBLIGATION

Mirror the engine's dispatch generality from day one (the H-1 lesson,
`docs/2026-09-02_quality-audit.md:88`): two `Step` constructors, with
the eval form GENERAL in the evaluated value (the engine's EVAL arm wraps
ANY `cval`, §0; today's `load_eval`/`store_eval` pin a pointer result,
which is why their refusal rows are one-sided — Round.lean header):

```
| kill {a loc ann} {kind : kill_kind} {pe} {pv} {ρ} {σ σ'}
    (h1 : valueFromPexpr pe = some (Vobject (OVpointer pv)))
    (hmem : applyMemM (CerbMem.killM loc (is_dynamic kind) pv) σ = some ((), σ')) :
    Step M (Expr a (Eaction (Paction .Pos (Action loc ann (Kill kind pe)))), ρ, σ)
           (Expr [] (Epure (Pexpr [] () (PEval Vunit))), ρ, σ')
| kill_eval {a loc ann} {kind} {pe} {cv : value} {ρ σ}
    (hnv : valueFromPexpr pe = none) (hv : evalPexpr M.tagDefs M.extern ρ pe = some cv) :
    Step M (Expr a (Eaction (Paction .Pos (Action loc ann (Kill kind pe)))), ρ, σ)
           (Expr a (Eaction (Paction .Pos (Action loc ann (Kill kind (Pexpr [] () (PEval cv)))))), ρ, σ)
```

Supporting declarations (each mirrors its create twin, cited): `killRedex
loc ann kind cv` (ANY value, so the ILLTYPED redex is in the fragment),
`killOpRedex`; `Redex.kill`/`.kill_op`; `Frag.kill` and `Frag.kill_op`
(`hnv`/`PePure`/`peDepth` as `Frag.load_op`); `Decomp` via `get_ctx_action`
(Soundness.lean:688); `Step.kill_inv`/`kill_op_inv`; `killM_loc_irrel`
(killM reads `loc` only inside `fail_`; the `storeM_loc_irrel` proof,
Step.lean:985-994, transfers); `step_ctx_kill` (the `step_ctx_create`
shape :1118-1142, continuation `apply_ctx ctx (mk_value_e Vunit)`, `cases
ctx <;> rfl`) and `step_ctx_kill_illtyped` (`Step_error2 "Kill"`, as
:1050); `step_ctx_kill_eval_ws` (DriverCollapse:950 shape); the
`dischargeStep` `KillRequest2` arm (§0) with `dischargeStep_kill_active/
_refusal`; `ars_kill_active` (DriverCollapse:436-455 shape, trace `ME_kill`);
arms in `engine_step_matchU`, `loop_step_frag`, `Frag.decomp`,
`step_factor`, `esize`/`pot`, the exhaustive `Step` matches (Step.lean:1537
ff.); `stateInert` is already `false` at any `Eaction` (TotalAdequacy:75).

Completeness (Round.lean): `engine_complete_killU M aid (ρ σ) : ∃ o,
outcomesU M aid (killRedex loc ann kind cv) ρ σ = [o] ∧ EngineMatchU … o`
by cases on `cv`: non-pointer → the round is `[Step_error2 "Kill"]` →
`.error` (refusal); pointer → `killM` is a closed deterministic
computation, so `applyMemM … = some ((), σ')` gives `.step (Step.kill
rfl hmem)` and `= none` gives `.killed r` with `r` one of: `Undef0 loc
[UB179a_non_matching_allocation_free]` (null-static / function / no
record / non-dynamic origin / other provenance), `Undef0 loc
[UB179b_dead_allocation_free]` (dead), `kill_reason.Other
(MerrUndefinedFree Free_out_of_bound)` (interior pointer — the one
NON-UB kill, `Mem_common.lean:392` maps it to `none`). Then
`cerberusRound_refused_kill` as the `_create` instance (Round.lean:341).
The eval row: because `kill_eval` is general in `cv`, the mirror is stuck
at `killOpRedex` only when `evalPexpr = none` — the engine's pure
evaluator failure, the `failwithI`/fuel channel that keeps the other
operand rows one-sided; no worse than today, and the ILLTYPED case is now
two-sided (it lands on the `killRedex` non-pointer row). Rows:
`capability_manifest.lean` gains `Frag.kill → wps_kill`, `Frag.kill_op →
wps_kill_eval`; `Examples/MirrorCoverage.lean` gains one `kill_eval`
witness at a symbol operand.

## 5. THE CONSUMER

`DisposeExhibit.lean` (new): dispose-a-list — label `dl(p)`: `if
ptreq(p, NULL) then unit else lets n = load(next(p)) in kill(static nodeTy,
p); run dl(n)`; statement `isList head ns ⊢ wpt (procCtx …) Ls (c · |ns| +
d) (fun w _ => ⌜w = .pure Vunit⌝) (dlProg head) [fmapEmpty]` — post `emp`,
consuming `wpt_load_at` (the next field via `pointsToView`), `wpt_kill`
(the node cell reassembled at `.own 1`), ptreq/if/save/run with variant
`ns.length`; layout premises `rfl`-class as in ListRevExhibit. Plus
`kill_launch_smoke`: from `prodMem₀`, `lets p = create(4, int) in
kill(static int, p)` through `wpt_engine_boundU_alloc` delivers at drive
length 4 with readout `ψ v σ' := σ'.deadAllocations = [1]` — the
engine-visible effect of kill, Iris-free (`alloc_create_launch_smoke`
shape). Existing exhibits and all four production statements UNCHANGED:
their posts (`isList`/`SeedChain`/`Sat` at `.own 1`) are already killable
by a later client; no statement spells a `MetaCell`.

## 6. RISKS AND SIZE

Modules touched: Heap, Step, Soundness, Round, Potential, DriverCollapse,
Rules, Wps, Wpt, Adequacy (`LaunchCoh.wf`, retire `fresh_*`), ProdEntry
(`prodMem₀_memWF`), API/Audit/manifest/MirrorCoverage, new DisposeExhibit,
README/ARCHITECTURE/WALKTHROUGH rows. ESTIMATE: 55-75 new declarations
(create's evaluated-form footprint is ~26 declarations across
Step/Soundness/Round/Rules/Wps/Wpt/Heap/DriverCollapse, measured by grep;
kill adds the eval form ~10, MemWF ~12, exhibit ~10), ~15 modified,
1500-2200 lines; 4-5 slices.

Slicing (one change per slice): K0 SPEC — `MemWF` + `LaunchCoh.wf` +
`CohG.wf` + `prodMem₀_memWF` + preservation through `CohG.create`/
`storeRange` (goal 3, independent of kill; `fresh_*`/`cur_*` retired).
K1 INTERNALS — `MetaCell.alive` + the CohG alive branch; public statements
frozen, snapshot delta as §2. K2 INTERNALS — mirror + certification +
`dischargeStep` arm + the completeness pair (no rule yet). K3 SPEC —
`kill_atomic`, `wps_kill`/`wpt_kill`/`_eval`, manifest rows, MirrorCoverage
witness. K4 — DisposeExhibit + smoke + docs; FULL gate at K4, fast gates
before. K0 first so `CohG.kill` proves `MemWF` preservation from the start.

Grind watch: (1) `killM_success`/`dischargeStep_kill_*` — the
`PointerValue`/`Provenance` match and `TreeMap.erase` rewriting; the
`storeM_success` pattern should hold, ~40 lines each. (2) `CohG.create`'s
re-touch for the alive branch and `MemWF.disj` (the 256-line lemma,
Heap.lean:2399-2655) — the one place that could balloon; cap: if the alive
branch cannot be threaded by `simpa using hold.dead`-style edits, split a
`LiveCoh` predicate out of `MetaCoh` first. (3) The exhaustive `cases`
over `Step`/`Frag`/`Redex` — ~15 sites, mechanical. (4) The
`dischargeStep` arm ripples through the `rfl` proofs of the existing
`dischargeStep_*` lemmas; expected benign. Stop-and-report at ~1h per
slice per the tripwire.

## 7. RefinedC alignment

RefinedC: `freeable l n k` (ghost_state.v:167-169) is consumed by
`wps_free` (`lifting.v:1123-1127`: `l ↦|ly| -∗ freeable l (ly_size ly)
HeapAlloc -∗ ▷ WPs s -∗ WPs (Free ly (val_of_loc l) s)`) and produced by
`wp_alloc` (`lifting.v:979-981`); `alloc_alive_loc l` (`:157-159`) is the
fractional read face; `alloc_global` the discarded token. Each has a
literal definition over our one metadata cell: `freeable id := metaOwn id
(.own 1) ⟨a,ty,n,true⟩` (inside `pointsToCell (.own 1)`), `alloc_alive_loc
:= ∃ q, metaOwn id q ⟨…,true⟩` (inside any `pointsToCell dq`),
`alloc_global := allocMeta` (`.discard`). So `&own` types carry the cell at
`.own 1` (freeable), shared/fractional types carry fractions (alive, not
freeable), `type_free` consumes `.own 1`; the `dqm`/`dqb` split a type
layer may want already exists in `pointsToView`. The one structural
divergence, forced by Cerberus erasing the record: RefinedC keeps
`alloc_meta` (range) past death (`free_block` writes `al_dead` with the
same range, `heap.v:518-529`) so `loc_in_bounds` of a dangling pointer
survives; here `locInBounds` is immortal knowledge only. Dangling-pointer
bounds reasoning meets the PNVI provenance question anyway and belongs to
the extension package's pointer-operation family, not the demo. No
adaptation of the demo's public statements is forced later.
