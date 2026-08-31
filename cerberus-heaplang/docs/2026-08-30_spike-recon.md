# Spike-minilog artifact 0: recon of the pinned semantics

[AGENT 2026-08-30] Recon worker report. Semantics pin: `.cerberus-ws`
checkout `8fb380c9c` (verified: `git -C .cerberus-ws rev-parse HEAD` =
`8fb380c9c0338e881bebc353c40aee589384906a`). All file:line cites below
are into `.cerberus-ws/lean_frontend/generated/` unless prefixed;
iris cites are into `.lake/packages/iris/Iris/Iris/` (pin `34390a0`).
Two live probes were run through the worktree's primed Lake dep
(`lake env lean`, uncapped-loud in-sandbox per the recorded ruling);
transcripts below are verbatim. Probe sources (ephemeral, not
committed): `/tmp/claude-1000/SpikeReconProbe.lean`,
`/tmp/claude-1000/SpikeAstProbe.lean`.

Headline answers:
- **Fragment programs are literal Lean terms — YES**, typechecked and
  executed (§1, §3 probe).
- **memM load/store can be executed directly from Lean — YES** (§2
  probe: one execution, exact value round-trip).
- **Seam recommendation: (a) memM for the small axioms, with the
  expression judgments defined over a (b)-shaped minimal-context step
  loop that the probe executed end-to-end** (§3, §5).
- **Granularity recommendation: allocation-rooted MemValue-level ↦ for
  the spike, byte-encoding stated inside the value predicate** (§5).
- **WP route recommendation: iris-lean `Language` instance** — it fits;
  full mask/fupd structure is present in the pin (§4, §5).
- **Top artifact-4 risk: dyn-annotation residue** — even positive
  strong-sequenced actions wrap their results in `Eannot` nodes
  carrying action-ids and footprints; this whole-run bookkeeping enters
  the fragment's own TERMS, not just the judgments (§6 R-i).

---

## 1. The AST: exact generated types and constructors

### 1.1 The type tower

Everything lives in `Core.lean`. All AST types are parameterized by
`(a bty sym : Type)` where `a` = per-node annotation on effectful
nodes, `bty` = pure-expression type annotation, `sym` = symbol type.

| Type | Cite | Shape |
|---|---|---|
| `generic_expr a bty sym` | Core.lean:1244-1248 | `Expr : List annot → generic_expr_ a bty sym → generic_expr` |
| `generic_expr_ a bty sym` | Core.lean:1202-1243 | the 19 effectful constructors; fragment uses `Epure` (:1205), `Eaction` (:1209), `Esseq` (:1225); `Ewseq` (:1223) same shape; `Eannot : List dyn_annotation → generic_expr → _` (:1241) appears at RUN TIME (see §6 R-i) |
| `generic_paction a bty sym` | Core.lean:1119-1122 | `Paction : polarity → generic_action a bty sym → _` |
| `generic_action a bty sym` | Core.lean:1087-1090 | `Action : CerbLocation.Loc → a → generic_action_ bty sym → _` |
| `generic_action_ bty sym` | Core.lean:999-1031 | `Store0 : Bool → pe → pe → pe → memory_order → _` (:1010; Bool = is-locking, pe1 = ctype, pe2 = pointer, pe3 = value — argument roles pinned by the consumer, Core_run.lean:392 `Store0 is_locking pe1 pe2 pe3 mo1` matching `Vctype ty1 / Vobject (OVpointer ptr_val) / cval`); `Load0 : pe → pe → memory_order → _` (:1012; pe1 = ctype, pe2 = pointer); also `Create` (:1002), `Kill` (:1008) if seeding proves awkward |
| `polarity` | Core.lean:260-267 | `Pos`, `Neg0` |
| `generic_pattern sym` | Core.lean:547-550 | `Pattern : List annot → generic_pattern_ sym → _` |
| `generic_pattern_ sym` | Core.lean:541-546 | `CaseBase : (Option sym × core_base_type) → _`, `CaseCtor : ctor → List (generic_pattern sym) → _` |
| `generic_pexpr bty sym` | Core.lean:728-731 | `Pexpr : List annot → bty → generic_pexpr_ bty sym → _` |
| `generic_pexpr_ bty sym` | Core.lean:666-727 | fragment uses only `PEval : value → _` (:673) |
| `value` | Core.lean:452-470 | `Vobject`, `Vloaded`, `Vunit`, `Vtrue`, `Vfalse`, `Vctype`, `Vlist`, `Vtuple` |
| `object_value` | Core.lean:325-338 | `OVinteger : CerbMem.IntegerValue → _`, `OVpointer : CerbMem.PointerValue → _`, … |
| `loaded_value` | Core.lean:339-344 | `LVspecified : object_value → _`, `LVunspecified : ctype → _` |
| `core_base_type` | Core.lean:95-115 | `BTy_unit` etc. (export at :115 region; constructors listed Core.lean:95+) |
| `memory_order` | Cmm_csem.lean:233-250 | `NA`, `Seq_cst`, … — Core-generated sequential code uses `NA` |
| `sym` | Symbol.lean:184-186 | `Symbol : String → Nat → symbol_description → sym` (`SD_None` etc. Symbol.lean:129-145) |
| `annot` (static annotations) | Annot.lean:201 | fragment programs use `[]` throughout |

### 1.2 The run-time instantiation

The engine executes at `a := core_run_annotation`, `bty := Unit`,
`sym := sym`:

- `abbrev expr (a : Type) := generic_expr a Unit sym` — Core.lean:1697
  (likewise `pexpr` :1695, `pattern` :1693, `paction` :1701).
- `structure core_run_annotation` = `{sb_before : List (thread_id × aid),
  dd_before : List aid, asw_before : List aid}` — Core_run_aux.lean:82-88
  (C11 pre-execution relation fragments, incrementally added during
  evaluation). The empty value is `empty_annotation`
  (Core_run_aux.lean:399-400), also the `Default` instance (:402-404).

So the spike's program type is **`expr core_run_annotation`
(= `generic_expr core_run_annotation Unit sym`)**, with `()` at every
`bty` position and `empty_annotation` at every action's `a` position.

### 1.3 Verbatim term skeletons (typechecked and EXECUTED — §3 probe)

These compiled and ran exactly as written (SpikeAstProbe.lean):

```lean
def intTy : ctype := Ctype [] (.Basic (.Integer (.Signed .Int_)))
def loc0 : CerbLocation.Loc := CerbLocation.other "spike"

/- pure-expression leaves -/
def ctyPe : pexpr := Pexpr [] () (PEval (Vctype intTy))
def ptrPe (pv : CerbMem.PointerValue) : pexpr :=
  Pexpr [] () (PEval (Vobject (OVpointer pv)))
def sevenPe : pexpr :=
  Pexpr [] () (PEval (Vloaded (LVspecified (OVinteger (CerbMem.integerIval 7)))))

/- store(x, 7) -/
def storeE (pv : CerbMem.PointerValue) : expr core_run_annotation :=
  Expr [] (Eaction (Paction Pos (Action loc0 empty_annotation
    (Store0 false ctyPe (ptrPe pv) sevenPe NA))))

/- load(x) -/
def loadE (pv : CerbMem.PointerValue) : expr core_run_annotation :=
  Expr [] (Eaction (Paction Pos (Action loc0 empty_annotation
    (Load0 ctyPe (ptrPe pv) NA))))

/- let strong _ = store(x,7) in load(x) -/
def seqE (pv : CerbMem.PointerValue) : expr core_run_annotation :=
  Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit))) (storeE pv) (loadE pv))
```

The only runtime-constructed ingredient is `pv` — a real
`CerbMem.PointerValue` obtained by seeding through the engine's own
`allocateObject` (§2). Everything else is a closed literal.

Value-shape note: the stored operand is accepted in BOTH `Vobject
(OVinteger _)` and `Vloaded (LVspecified (OVinteger _))` forms —
`memValueFromValue` (Core_aux.lean:101-106) maps either, at
`Basic (Integer ity)`, to `CerbMem.integerValueMval ity ival`. The
`Vloaded/LVspecified` form is what elaborated Core uses for storable
values and what the load produces, so the skeletons use it.

Hairiest constructor: none is hard; the subtlety is entirely in the
INSTANTIATION (Unit vs core_base_type at `bty`; `core_run_annotation`
at `a`; `empty_annotation`, not `default`, at the action's annotation —
they happen to coincide via the `Default` instance but the engine
constructs `empty_annotation`).

## 2. The memory sub-machine (memM)

### 2.1 The monad

```
abbrev memM (a) := ndM a String mem_error (mem_constraint IntegerValue) MemState
```
CerbMem.lean:1394 (an identical root-level abbrev exists at Mem.lean:86
— the .lem interface module; qualify as `CerbMem.memM` in probes to
avoid the ambiguity, which is a name clash only, same type).

`ndM` is the generated nondeterminism monad — Nondeterminism.lean:116-134:

```
ndM a info err cs st  =  ND : (st → nd_action a info err cs st × st)
nd_action = NDactive a | NDkilled (kill_reason err)
          | NDnd info (List (info × ndM …)) | NDguard info cs (ndM …)
          | NDbranch info cs (ndM …) (ndM …) | NDstep info (List (info × ndM …))
```

i.e. a state function returning ONE tree layer. `kill_reason err` =
`Undef0 Loc (List undefined_behaviour) | Error0 Loc String | Other err`
(Nondeterminism.lean:54-61). `kill` (Nondeterminism.lean:231),
`nd_return`/`memReturn` (CerbMem.lean:1396), `nd_bind` = fuelled
`nd_bind_lemFuel lemDefaultFuel` (Nondeterminism.lean:190-192 — NOTE
the fuel, §6 R-v).

### 2.2 The state

`structure MemState` — CerbMem.lean:118-138 (mirrors impl_mem.ml:482-501),
14 fields; load-bearing for the fragment:
- `allocations : Std.TreeMap Int Allocation` (:126) — key = allocation
  id; `Allocation` = `{base : Address(=Int), size : Int, ty : Option ctype,
  isReadonly : ReadonlyStatus, taint, prefix_}` (CerbMem.lean:109-116);
- `bytemap : Std.TreeMap Int AbsByte` (:132) — key = byte address;
  `AbsByte = {prov : Provenance, copyOffset : Option Int,
  value : Option UInt8}` (CerbMem.lean:96-100);
- `deadAllocations : List StorageInstanceId` (:134);
- `nextAllocId`, `lastAddress` (:120,122) — allocation cursor
  (addresses grow DOWNWARD from 0xFFFFFFFFFFFF);
- the rest (iotaMap, funptrmap, varargs, lastUsedUnionMembers,
  dynamicAddrs, lastUsed, requested) is inert for the fragment.
`({} : MemState)` is a valid empty initial state (all fields have
defaults).

### 2.3 The operations

- `allocateObject (tid : Nat) (pref : prefix0) (alignIv : IntegerValue)
  (ty : ctype) (reqAddr : Option Int) (initOpt : Option MemValue) :
  memM PointerValue` — CerbMem.lean:1469-1496. One-level `ND fun st =>`:
  computes the aligned address below `lastAddress`, inserts a live
  writable `Allocation` under `nextAllocId`, pads the bytemap, and
  returns **`.PV (.Prov_some allocId) (.PVconcrete none alignedAddr)`**
  (:1496). Deterministic; fails only with "out of memory".
- `loadM (loc : CerbLocation.Loc) (ty : ctype) (pv : PointerValue) :
  memM (Footprint × MemValue)` — CerbMem.lean:1586-1630. One-level:
  reads `sizeofCtype ty` bytes (`readBytesFrom`, :1427-1431), rebuilds
  the value (`reconstructValue`, :774), returns `(.FP .R addr size, mv)`.
- `storeM (loc) (ty : ctype) (isLocking : Bool) (pv : PointerValue)
  (mv : MemValue) : memM Footprint` — CerbMem.lean:1632-1696. One-level:
  serializes (`memValueToBytes`, :639), writes the bytemap
  (`writeBytesTo`, :1420-1425), returns `.FP .W addr (sizeofCtype ty)`.
- `killM (loc) (isDynamic : Bool) (pv) : memM Unit` — CerbMem.lean:1520.
- `Footprint` = `FP (access : W|R) (base : Address) (size : Int)` —
  CerbMem.lean:81-87; `overlapping : Footprint → Footprint → Bool`
  at CerbMem.lean:1187.

KEY STRUCTURAL FACT for artifact 4: `allocateObject`, `loadM`, `storeM`,
`killM` are all **single-layer `ND fun st => (NDactive …/NDkilled …, st')`
state transformers** — no `NDnd`/`NDbranch` nodes anywhere in their
bodies (grepped; the only ND fork in CerbMem is `eqPtrval`'s msum,
:1731, outside the fragment). So a memM fragment op can be RUN — and
REASONED ABOUT — by one function application, no runner and no fuel:

```lean
def applyMemM (m : CerbMem.memM a) (st : MemState) : Option (a × MemState) :=
  match m with | ND f => match f st with
    | (NDactive x, st') => some (x, st') | _ => none
```

### 2.4 Running memM from Lean: the runners

- `CerbND.runND : ndM a info err cs st → st → List (nd_status a err st ×
  List String × st)` — CerbND.lean:136-138, wrapper over the
  fuel-totalized `runNDFuel` (:89-131, default fuel `ndDefaultFuel =
  lemDefaultFuel` = 10^6, :71; fuel-0 leaf is a loud proof-transparent
  `panic!`). `nd_status` = `Active a | Killed st (kill_reason err)` —
  Nondeterminism.lean:584-589.
- `runND1` (single-trace, :214-216), `runND1Trace` (labeled, :266-269).

### 2.5 PROBE (verbatim) — the memM runner answer

`/tmp/claude-1000/SpikeReconProbe.lean`: seed one signed-int object via
`allocateObject`, `storeM` the value 7, `loadM` it back, all chained
with `nd_bind` and run by `CerbND.runND` from the empty `MemState`;
plus a negative probe (`killM` then `loadM`). Command:
`LEAN_PATH+=<LemLib build> ~/.elan/bin/lake env lean <probe>`. Output:

```
1 execution. ptr = PV (Prov_some 0) (PVconcrete 281474976710648); load fp = FP R 281474976710648 4; load mv = MVinteger (Signed Int_) (IV (Prov_none) 7); allocations = 1; nextAllocId = 1
KILLED Undef0 with 1 UB(s)
```

So: direct execution WORKS; exactly one execution (determinism of the
fragment ops confirmed at runtime); the dead-pointer load kills with
`Undef0` carrying one UB (= UB010_pointer_to_dead_object per the
§2.6 table). 281474976710648 = 0xFFFFFFFFFFF8 (top-of-memory minus
aligned 4 bytes — the downward cursor).

### 2.6 The UB/error channel (coordinator add-on 1; feeds R4)

Failure enters as `NDkilled (failReason err loc)` where `failReason`
(CerbMem.lean:1404-1409, mirroring impl_mem.ml:540-546) maps the
`mem_error` through `undefinedFromMem_error` (Mem_common.lean:392):
UB-classed errors become `Undef0 loc [ub]`, everything else
`kill_reason.Other err`. `mem_error` inductive: Mem_common.lean:319-370;
`access_kind` = `LoadAccess | StoreAccess` (:77-83); `access_error` =
`NullPtr | FunctionPtr | DeadPtr | OutOfBoundPtr | NoProvPtr |
AtomicMemberof` (:99-113).

**loadM failure vocabulary** (CerbMem.lean:1606-1630, order = check order):

| condition | mem_error | via undefinedFromMem_error (Mem_common.lean:392) |
|---|---|---|
| null pointer | `MerrAccess LoadAccess NullPtr` (:1607) | `Undef0` UB019_lvalue_not_an_object |
| function pointer | `MerrAccess LoadAccess FunctionPtr` (:1608) | `Other` (no UB mapping) |
| empty provenance | `MerrAccess LoadAccess OutOfBoundPtr` (:1609) | `Undef0` UB_CERB002a_out_of_bound_load |
| device provenance | `MerrAccess LoadAccess OutOfBoundPtr` (:1610-1613) | same |
| symbolic provenance | `Other (MerrOther "loadM: Prov_symbolic …")` (:1614-1616) | `Other` (unreachable — concrete model never mints Prov_symbolic) |
| dead allocation | `MerrAccess LoadAccess DeadPtr` (:1619-1620) | `Undef0` UB010_pointer_to_dead_object |
| id not in allocations | `MerrOutsideLifetime …` (:1621-1624) | `Undef0` UB009_outside_lifetime |
| out of bounds | `MerrAccess LoadAccess OutOfBoundPtr` (:1626-1627) | `Undef0` UB_CERB002a |
| atomic member access | `MerrAccess LoadAccess AtomicMemberof` (:1628-1629) | `Undef0` UB042 |
| _Bool trap repr | `MerrTrapRepresentation LoadAccess` (:1598-1604) | `Undef0` UB012_lvalue_read_trap_representation |

**storeM failure vocabulary** (CerbMem.lean:1662-1696):

| condition | mem_error | classification |
|---|---|---|
| ill-typed store (`!ctypeMemCompatible ty (typeofMval mv)`) — checked FIRST, before pointer-kind | `MerrOther "store with an ill-typed memory value"` (:1666-1667) | **`Other`, NOT UB** |
| null / function / no-prov / device | `MerrAccess StoreAccess NullPtr|FunctionPtr|OutOfBoundPtr` (:1670-1675) | UB019 / Other / UB_CERB002b |
| id not in allocations (incl. dead — no separate dead check on store, :1680-1682) | `MerrOutsideLifetime` (:1683-1685) | `Undef0` UB009 |
| out of bounds | `MerrAccess StoreAccess OutOfBoundPtr` (:1687-1688) | `Undef0` UB_CERB002b_out_of_bound_store |
| read-only allocation | `MerrWriteOnReadOnly kind` (:1689-1690) | `Undef0` UB033/UB064/UB_modifying_temporary_lifetime by kind |
| atomic member | `MerrAccess LoadAccess AtomicMemberof` (:1692-1695 — LoadAccess is a mirrored upstream copy-paste, noted in-code) | `Undef0` UB042 |

R4 consequence: "no UB" is NOT the same as "no NDkilled" — the
ill-typed store and function-pointer arms kill with `Other`. The
UB-excluding WP should exclude ALL `NDkilled` outcomes (safety =
`loadM/storeM` returns `NDactive`), which also subsumes the non-UB
error arms; misalignment per se is NOT checked by loadM/storeM (no
alignment arm exists in either — alignment is enforced at allocation
and by the Ail/Core elaboration, not the concrete-model access path).

### 2.7 Provenance detail (coordinator add-on 2; feeds R5)

- `PointerValue = PV (prov : Provenance) (base : PointerValueBase)` —
  CerbMem.lean:53-57; `Provenance = Prov_none | Prov_some allocId |
  Prov_symbolic iota | Prov_device` (:39-44); `PointerValueBase =
  PVnull ty | PVfunction sym | PVconcrete (Option identifier) Address`
  (:47-51).
- A fragment `x` is exactly what `allocateObject` returns:
  **`PV (Prov_some allocId) (PVconcrete none addr)`** (CerbMem.lean:1496;
  probe: `PV (Prov_some 0) (PVconcrete 281474976710648)`). Both the id
  and the address are load-bearing: loadM/storeM dispatch on
  `Prov_some allocId` and check `allocations.get? allocId` + bounds at
  `addr` (§2.6). The honest `x ↦ v` therefore speaks about a
  PointerValue whose provenance id must be live-and-in-bounds — it
  cannot be an address-only abstraction (R5: the points-to must carry
  or imply the allocation-liveness fact keyed by `allocId`, §5.2).
- Distinct seeded objects get distinct ids AND disjoint address ranges
  (`nextAllocId + 1`, `lastAddress` decreasing — CerbMem.lean:1486-1488).

### 2.8 Integer round-trip (coordinator add-on 4; feeds S1)

Encode (store): Core value `Vloaded (LVspecified (OVinteger iv))` (or
`Vobject` form) → `memValueFromValue` (Core_aux.lean:101-106) →
`MVinteger ity iv` (`integerValueMval`, CerbMem.lean:1101; `IntegerValue
= IV (prov) (val : Int)`, CerbMem.lean:61-63; `integerIval n = IV
.Prov_none n`, :875) → `memValueToBytes` MVinteger arm
(CerbMem.lean:556-567): size = `CerberusImpl.sizeof_ity ity` (4 for
signed int), bytes = `intToBytes n sz` (:470-476 — little-endian,
two's-complement via `+ 2^bits` for negatives), each byte
`{prov := iv.prov, copyOffset := none, value := some b}`.

Decode (load): `readBytesFrom` (:1427) → `reconstructValue` integer arm
(CerbMem.lean:659-669): `signed := CerberusImpl.is_signed_ity ity`,
`bytesToInt bytes signed` (:478-494 — None if ANY byte value is None,
i.e. uninitialized ⇒ `MVunspecified ty`), provenance =
`provFromIntegerBytes` (:503-504, `combineProv` fold starting from
`Prov_none`).

So "`v` encodes `z`" for the miniature `intT z` is concretely EITHER
`v = MVinteger ity (IV p z)` at the MemValue level (with the caveat
that the loaded `p` is the byte-prov fold — for values written via
`integerIval` it is `Prov_none` and the round-trip is EXACT, probe
§2.5: stored `IV Prov_none 7`, loaded `IV Prov_none 7`), OR at byte
level `bytes = intToBytes z (sizeof_ity ity)`. Both endpoints are
executable functions with equations, so the S1 factorization can state
encoding by definitional unfolding on concrete `z`.

## 3. The expression-level stepping entry

### 3.1 The machinery

The engine's expression reducer is **`step_ctx`** (Core_reduction.lean:484):

```
step_ctx (_lemReader_tagDefs : Fmap sym (CerbLocation.Loc × tag_definition))
         (mem_st : CerbMem.MemState)
         (file1 : generic_file Unit core_run_annotation)
         (core_extern1 : Fmap sym sym)
         (current_tid : Nat)
         (p : Option Nat × thread_state)      -- (parent tid, thread)
         : List core_step2
```

It decomposes `th_st.arena` with `get_ctx` (Core_reduction.lean:373-375,
fuelled; evaluation contexts `context = CTX | Cunseq | Cwseq | Csseq |
Cannot | Cbound`, Core_run_aux.lean:105-118; `apply_ctx`
Core_reduction.lean:388), reduces each redex via `one_step0`
(Core_reduction.lean:353; outcome type `one_step = TAU_WITH_RUNSTATE |
TAU | EVAL | ND0 | MEMOP | UNSEQUENCED_RACE | ILLTYPED`,
Core_reduction.lean:309-317), and packages the results as `core_step2`
(Core_reduction.lean:224-254): fragment-relevant constructors
`Step_tau2 : String → core_tau_step_kind → thread_state → _`,
`Step_with_runstate2 : runstate_step_kind → core_runM thread_state → _`,
`Step_action_request2 : String → Loc → thread_id → Bool →
core_runM (action_request2 thread_state) → _`.

Memory actions do NOT touch memory inside step_ctx: they surface as
**requests** — `action_request2 a` (Core_reduction.lean:107-149):
`StoreRequest2 : memory_order → ctype → Bool → PointerValue → MemValue
→ (aid → Footprint → a) → _` (:124-129), `LoadRequest2 : memory_order
→ ctype → PointerValue → (aid → Footprint → MemValue → a) → _`
(:132-139), plus Alloc/Create/Kill/SeqRMW. The DRIVER discharges them
against memM: `action_request_sequential2` (Driver.lean:273) calls
`liftMem (CerbMem.storeM/loadM/allocateObject/allocateRegion/killM …)`
and feeds `(aid, footprint[, MemValue])` to the continuation, drawing
`aid` from `driver_state.core_run_state0.aid_supply`. The full driver
loop (`driver2`, Driver.lean:384) additionally owns `driver_state`
(Driver.lean:133-145: core_file, core_extern, core_state0 (thread
list), core_run_state0, layout_state (the MemState), concurrency_state,
fs_state0, trace, …).

The surrounding monad of the requests: `core_runM a =
stExceptUndefM a core_run_state core_run_cause` (Core_run_aux.lean:375-376)
`= core_run_state → exceptM (t0 a × core_run_state) core_run_cause`
(State_exception_undefined.lean:40; `t0 = Defined | Undef | Error`,
Undefined.lean:1341-1349; `exceptM = Result | Exception`,
Exception.lean:38-43) — a plain state-function, directly applicable.

### 3.2 The MINIMAL surrounding context (measured, not estimated)

The probe (§3.3) stepped the fragment with:
- tagDefs `:= fmapEmpty` (no structs in fragment);
- `mem_st` — the seeded MemState (step_ctx only reads it for pure
  memop evaluation; fragment: inert but must be supplied);
- `file1 := (default : file core_run_annotation)` (generic_file has an
  Inhabited instance, Core.lean:1665-1666; only proc/impl lookups read
  it — fragment has none);
- `core_extern1 := fmapEmpty`;
- `current_tid := 0`, parent `none`;
- `thread_state` (Core_run_aux.lean:291-298: arena, stack0, errno, env,
  current_proc_opt, exec_loc, current_loc): `default` with
  `arena := <program>` and `env := [fmapEmpty]` (env must be a nonempty
  stack only for binder-arms; with wildcard `CaseBase (none, _)`
  patterns nothing is ever looked up);
- a hand-built `core_run_state` (Core_run_aux.lean:353-358):
  `{tid_supply := 1, aid_supply := 0, excluded_supply := 0,
  sym_supply := 0, labeled := fmapEmpty}`. Do NOT use
  `initial_core_run_state` (Core_run_aux.lean:395-396) — it draws
  `sym_supply` from `runEffectful (CerberusFresh.freshIntIO ())`, an
  effectful never_extract seam.

### 3.3 PROBE (verbatim) — stepping + a complete minimal-context drive

`/tmp/claude-1000/SpikeAstProbe.lean` (terms of §1.3): classify
`step_ctx` output on `store(x,7)` and on the Esseq program; run the
request monad by hand; then a 20-fuel mini-driver that loops
{step_ctx → discharge Store/LoadRequest2 via one-level memM application
→ feed the continuation} from a seeded state. Output:

```
[Step_action_request2[StoreRequest]]
[Step_action_request2[StoreRequest]]
req[StoreRequest] = StoreRequest2 at 4096 val MVinteger _ 7; next arena = <core_expr>
DONE: loaded specified integer 7
Eannot-wrapped value, 2 dyn-annotation(s)
```

Readings:
1. Both programs yield EXACTLY ONE step, the store request (the Esseq
   context decomposes to the same redex under `Csseq`).
2. The request monad applied to the hand-built `core_run_state`
   returns `Result (Defined (StoreRequest2 …))` carrying the REAL
   PointerValue and `MVinteger _ 7`; its continuation yields the next
   thread_state.
3. The mini-drive reaches the final value **`loaded specified
   integer 7`** — `let strong _ = store(x,7) in load(x)` executes
   end-to-end against the engine with the §3.2 minimal context. The
   drive crossed only `Step_tau2` / `Step_with_runstate2` /
   `Step_action_request2` steps.
4. The final arena is `Expr _ (Eannot [d1, d2] (… PEval value …))` —
   TWO dyn_annotations of residue (§6 R-i).

## 4. iris-lean inventory (pin 34390a0)

- **GenHeap EXISTS**: `Iris/BI/Lib/GenHeap.lean` — `genHeapPreS`/
  `genHeapGS L V GF H` (:44-61, requires `Std.LawfulFiniteMap H L`),
  `genHeapInterp (σ : H V) : IProp GF` (:78-80), `pointsTo l dq v` with
  notation `l ↦{dq} v` / `l ↦ v` (:82-86), `genHeap_alloc` (:397-398),
  `genHeap_valid` (:450-451), `genHeap_update` (:457-458), init
  (:488-514), plus the meta-token machinery. Backing ghost state:
  `GhostMap` (Iris/Instances/Lib/GhostMap.lean), auth/agree/frac all
  present under Iris/Algebra (Auth.lean, Agree.lean, Frac.lean,
  DFrac.lean, HeapView.lean).
- **Language interface**: `Iris/ProgramLogic/Language.lean` —
  `class PrimStep Expr State Obs` with
  `primStep : Expr × State → Obs → Expr × State × List Expr → Prop`
  (:67-69); `class Language Expr State Obs Val extends
  PrimStep Expr State (List Obs), ToVal Expr Val` with the single law
  `val_stuck` (:110-113). `ToVal` = `toVal : Expr → Option Val` +
  `ofVal` section (:1-65). Thread-pool `Step`/`NSteps` (:127-154).
- **WP**: `Iris/ProgramLogic/WeakestPre.lean` — `StateInterp State Obs
  GF` (:35-40), `IrisGS_gen` (:44-59: invGS, numLatersPerStep,
  forkPost, stateInterp_mono), `wp.pre` (:73-83) and the fixpoint `Wp`
  instance (:117-119). Also `TotalWeakestPre.lean` (twp),
  `Adequacy.lean`/`TotalAdequacy.lean`, `Lifting.lean`,
  Ectx variants (EctxLanguage.lean, EctxiLanguage.lean).
- **Masks/fupd (coordinator add-on 3; feeds R3): PRESENT AND
  STRUCTURAL.** `wp.pre` is mask-indexed over `CoPset` with the full
  fancy-update discipline: `={E,∅}=∗` around reducibility, step-fupd
  `={∅}▷=∗^[n]`, `|={∅,E}=>` on re-establishment, later credits `£`
  (WeakestPre.lean:77-83). fupd itself: `Iris/Instances/Lib/FUpd`
  (imported at WeakestPre.lean:8); mask lemmas `fupd_mask_intro`/
  `fupd_mask_subseteq`/`fupd_mask_mono` used throughout
  (e.g. WeakestPre.lean:208,234; TotalWeakestPre.lean:182,429-430).
  The donor's typed_read_end E→∅ discipline is expressible as-is.
- **Hoare-triple notation**: `Iris/BI/WeakestPre.lean` — `class Wp`
  (:34) and `{{ P }} e @ s; E {{ RET v; Q }}` macros (:98-172).
- **The worked instantiation to MIRROR**: HeapLang.
  `Iris/HeapLang/Semantics.lean` (state + `HeapF := fun V =>
  Std.ExtTreeMap Loc V compare`, :127), `Instances.lean:22` (language
  instance via EctxItemLanguage), `PrimitiveLaws.lean`: `class
  HeapLangGS` bundling `genHeapGS Loc (Option Val) GF HeapF` (:59-64),
  `StateInterp` instance `stateInterp σ _ κs _ := genHeapInterp σ.heap
  ∗ …` (:69-70), `IrisGS_gen` instance (:82), and the small axioms in
  exactly the acceptance package's shape:
  `wp_load : {{ ▷ l ↦{q} some v }} !#l @ s; E {{ RET v; l ↦{q} some v }}`
  (:339) and `wp_store` (:382).
- LawfulFiniteMap instances for `ExtTreeMap K · compare`:
  Iris/Std/HeapInstances.lean:275 — an `Std.ExtTreeMap Int X compare`
  ghost carrier is available off the shelf (the engine's own
  `Std.TreeMap` is NOT the ghost carrier; the state interp bridges
  them by projection, as HeapLang's `σ.heap` does).

No gap found for artifacts 2/3: GenHeap fits directly; nothing forces
falling back to raw auth/ghost-map plumbing.

## 5. Proposed signatures for artifacts 1-3 (types only)

### 5.1 Artifact 1 — Step

Over the real types, with the §3.2 minimal context frozen out of the
judgment (fixed empty tagDefs/extern/default file, tid 0):

```lean
namespace RefinedCerberus.Spike

abbrev CoreExpr := expr core_run_annotation       -- Core.lean:1697/1244
abbrev Mem := CerbMem.MemState                     -- CerbMem.lean:119

/-- one engine step of the fragment: expression + memory to
    expression + memory. Mirror-cites: step_ctx Core_reduction.lean:484
    (context decomposition + one_step0), Driver.lean:273
    (request discharge against loadM/storeM). aid is the drive
    counter (enters only the inert Eannot payloads). -/
inductive Step : CoreExpr × Mem → CoreExpr × Mem → Prop
  -- rules: SeqTau (Esseq value-subst), StoreAct, LoadAct, AnnotMerge …

/-- UB/failure is ABSENCE of Step at a non-value (NotStuck-style);
    the killed outcomes are covered by artifact 4's statement relating
    Step-stuckness to NDkilled of loadM/storeM. -/
```

The plan's `Step : Expr → Mem → Outcome → Prop` shape works too; the
pair-relation form above is what the iris-lean `Language` instance
consumes directly (`primStep (e, σ) obs (e', σ', [])` with `Obs :=
Empty`-observations and no forks), so it is the full-build-forward
choice (R1, R3). Small-step, not big-step: the probe showed the
whole fragment reduces in `Step_tau2`/request steps with no
intra-step search.

`toVal : CoreExpr → Option value` peels `Expr _ (Epure (Pexpr _ _
(PEval v)))` and the one-layer `Eannot` variant — exactly
`is_irreducible`'s two value forms (Core_reduction.lean:293).

### 5.2 Artifact 2 — points-to (granularity RECOMMENDATION)

What loadM/storeM actually manipulate is the BYTE map plus the
ALLOCATION table (§2.3, §2.6): success needs (i) `Prov_some id` with
`id` live in `allocations` and not in `deadAllocations`, (ii) bounds,
(iii) writability (store), and reads/writes `sizeofCtype ty` bytes.

Recommendation: **allocation-rooted, MemValue-level carrier for the
spike**, concretely `genHeapGS Int SpikeCell GF (ExtTreeMap Int ·
compare)` keyed by allocation id, with

```lean
structure SpikeCell where
  addr  : CerbMem.Address     -- = Allocation.base
  ty    : ctype
  bytes : List CerbMem.AbsByte  -- length = sizeofCtype ty
```

and `x ↦ᵥ (τ, v) := ∃ id addr, ⌜x = .PV (.Prov_some id) (.PVconcrete
none addr)⌝ ∗ pointsTo id ⟨addr, τ, memValueToBytes-encoding of v⟩`;
`stateInterp mem := genHeapInterp (project mem) ∗ ⌜coherence mem⌝`
where `project` restricts `mem.allocations`+`mem.bytemap` to the
live-allocation cells.

Reasoning (R2, full-build-forward):
- vs BYTE-level (`genHeapGS Int AbsByte` over the bytemap alone): the
  byte map alone cannot make the small axioms true — loadM/storeM
  failure is decided by the ALLOCATION table (§2.6), so a byte-only ↦
  cannot entail access-success; the allocation facts would move into a
  second ghost heap anyway. The donor comparison actually LANDS on the
  recommended shape: Caesium's `l ↦ v` has `v : list mbyte` (byte
  list!) rooted at a location with allocation id — our `SpikeCell.bytes`
  IS the byte list; only the per-byte SPLITTING of one allocation is
  deferred. That splitting (needed for struct fields, far beyond the
  fragment) is the registered growth step: split `SpikeCell` into a
  per-byte ghost heap + a per-allocation metadata heap. Registered as
  CHANGED-SHAPE, not blocking.
- vs pure MemValue (no bytes): storing `MVinteger` and loading gives
  the RECONSTRUCTED value; equality holds for the fragment's integers
  (probe §2.5) but is decode∘encode-mediated in general (structs,
  padding, provenance folds). Keeping `bytes` as the carrier and
  stating `v ◁ᵥ intT z`-style encoding predicates OVER the bytes
  (§2.8) keeps the ghost state exactly mirror-true to `bytemap` while
  the S1 miniature gets its `l ↦ v ∗ v ◁ᵥ ty` factorization verbatim
  (ty_deref/ty_ref shape, deps/refinedc type.v:277-282).

### 5.3 Artifact 3 — WP route RECOMMENDATION

**Language-instance route.** Instantiate `Language CoreExpr Mem Empty
value` with artifact 1's Step (no observations, no forks — `List Expr`
component always `[]`), `StateInterp Mem Empty GF` via §5.2's
projection, `IrisGS_gen` with `numLatersPerStep := fun _ => 0`,
`forkPost := fun _ => True`, mirroring
HeapLang/PrimitiveLaws.lean:59-90 line-for-line. Then `wp`, frame,
`wp_wand`, consequence, and the bind rule come from
ProgramLogic/WeakestPre.lean + Lifting.lean for free, with the
mask/fupd structure R3 demands already in `wp.pre` (§4). The seq rule
is a lifted-step lemma over the `Esseq` tau-step (a `wp_pure`-style
lemma, cf. HeapLang DerivedLaws), not a monadic bind — this is the R6
"bind layer dissolves" test on live proofs.

Concrete blocker check performed: `Language` needs nothing the
fragment lacks (no fuel, no thread ids — the thread-pool layer sits
ABOVE `primStep` and is unused by wp itself beyond forkPost). The one
friction point: `wp.pre` quantifies over `List Obs` observations —
with `Obs := Empty` these collapse. If instantiation friction appears
anyway (K3 watch), the registered fallback is a direct-WP definition
over Step with the same statement shapes; nothing found in recon
forces it.

### 5.4 Artifact 4 — the soundness seam (R1 RECOMMENDATION)

Two-level, matching what the probes executed:
- **Small axioms couple at seam (a)**: `wp_store`/`wp_load` soundness
  obligations reduce to ONE-LEVEL facts about
  `applyMemM (storeM …)`/`applyMemM (loadM …)` (§2.3) — plain
  equational reasoning on a state function, no runner, no fuel, no
  driver. This is where `{x ↦ -} store(x,7) {x ↦ 7}` discharges into
  engine behavior.
- **The Step relation itself is certified at seam (b)**: each Step
  rule mirrors one `step_ctx` outcome + (for actions) the
  Driver.lean:273 discharge, under the §3.2 minimal context; the probe
  demonstrated this loop terminating with the correct value, so the
  mirror statement ("Step (e,m) (e',m') iff the minimal-context
  step_ctx/discharge composite produces (e',m')") is about a closed
  executable path.
- Seam (c) (whole-driver wrapper) is NOT needed and absorbs
  driver_state/fs/concurrency/trace — rejected (see §6 R-vii).

## 6. Risks for artifact 4 (whole-run machinery the judgments must not absorb)

- **R-i. Dyn-annotation residue in TERMS (top risk).** Positive,
  strong-sequenced actions return their results wrapped:
  the probe's final arena is `Eannot [d1,d2] (value)` — 2
  `dyn_annotation`s (type Core.lean:1151) carrying action-ids and
  footprints for race bookkeeping (`do_race`/`combine_dyn_annotations`,
  Core_reduction.lean:300-305; `is_irreducible` accepts one Eannot
  layer and force-reduces double layers, Core_reduction.lean:293).
  Consequence: Step's rules and `toVal` MUST mirror the exact wrapping
  (aid values threaded as inert data from the drive counter), or the
  soundness statement must be up-to-annotation. Mirror-exactly is
  recommended (mirror-OCaml doctrine); the aid counter then appears as
  a Step-relation index that the LOGIC's judgments existentially hide.
- **R-ii. `core_run_state` supplies** (tid/aid/excluded/sym,
  Core_run_aux.lean:353-358). The fragment's request monads thread it
  but (measured, §3.3) only the aid reaches the continuation. Keep it
  out of `Mem`; fix it or existentially quantify it in the seam-(b)
  statement. NEVER `initial_core_run_state` (effectful `runEffectful`
  seam, Core_run_aux.lean:395).
- **R-iii. thread_state ballast** (stack0, errno, current_proc_opt,
  exec_loc, current_loc — Core_run_aux.lean:291-298): inert on all
  fragment paths (probe ran on `default` fields); judgments should
  quantify over or fix them, not carry them.
- **R-iv. Runner fuel**: `runND`/`runNDFuel` (CerbND.lean:71,89-138)
  is fuel-bounded with a proof-transparent panic leaf. Judgments never
  mention runND (seam (a) applies the state function directly); if a
  whole-run corollary is ever wanted, it inherits the fuel equation.
- **R-v. Bind fuel**: `nd_bind = nd_bind_lemFuel lemDefaultFuel`
  (Nondeterminism.lean:190-192). memM COMPOSITIONS (e.g. seeding
  chains) unfold through fuelled binds; the judgments avoid this by
  stating per-operation facts (one-level application), seeding done
  by concrete evaluation.
- **R-vi. Fuelled AST/model functions in the unfold cone**: `get_ctx`
  (Core_reduction.lean:373), `full_eval_pexpr` (Core_reduction.lean:100),
  `sizeofCtype` (CerbMem.lean:348/457), `memValueToBytes` (:546/639),
  `reconstructValue` (:652/774), `memValueFromValue`
  (Core_aux.lean:101/106). All total with `lemDefaultFuel` wrappers
  (rfl-defeq to workers); on concrete fragment terms they reduce in a
  handful of steps, but simp-unfolding fuelled workers is the known
  arc-3 pathology — proofs should unfold the default-budget wrappers
  on CLOSED arguments only (decide/rfl-style evaluation), K2 watch.
- **R-vii. Driver-level state** (`driver_state`, Driver.lean:133-145:
  trace events, fs_state, concurrency symState, dr_step_counter;
  `driver2` loop Driver.lean:384): enters ONLY at seam (c). Rejecting
  (c) keeps all of it out.
- **R-viii. Non-UB kill arms** (§2.6, R4): the WP's safety must
  exclude `kill_reason.Other` arms too (ill-typed store!), so
  `wp_store`'s precondition carries the type-compatibility fact
  (`ctypeMemCompatible ty (typeofMval v)`, CerbMem.lean:1666) — in the
  S1 miniature this is exactly what `v ◁ᵥ intT z` supplies.
- **R-ix. Binder patterns pull in the evaluator.** With a real
  `CaseBase (some sym, _)` pattern, Esseq's continuation goes through
  env update + `full_eval_pexpr` lookup (one_step0's Esseq arm,
  Core_reduction.lean:353). The acceptance package needs only the
  wildcard form (probe used `CaseBase (none, BTy_unit)`); value-binding
  seq should enter, if at all, via the substitution-closed pexpr story,
  else the pexpr evaluator (and its `core_run_state` threading) enters
  the judgments.

## Unknowns (not guessed)

- Whether the two dyn_annotations on the final value are exactly
  `[DA_pos …]` markers from store and load respectively (their
  constructor identity was not discriminated — only count and
  position; pin down when writing Step's action rules).
- `mem_constraint` (Mem_common.lean:614) never fires on fragment paths
  (no NDguard/NDbranch encountered in the probes); asserted from body
  inspection of loadM/storeM/allocateObject only, not proved.
- iris-lean pin `34390a0` uses Lean `module`/`public import` headers
  (visible in GenHeap.lean:1-10) — interaction of that module system
  with our non-module RefinedCerberus package was not probed (the
  package already builds against this pin per Smoke.lean, so assumed
  fine).
- Perf regime of `step_ctx` UNFOLDING in proofs (as opposed to
  execution, which is instant) — untested; K2 watch under R-vi.

## Derisk-register stances after recon (derived tallies)

- R1 seam: CHANGED-SHAPE (two-level: memM small axioms + minimal-
  context step mirror; §5.4). R2 basis: recommendation made with donor
  cite; byte-splitting registered as growth step (§5.2) — OPEN until
  artifact 2 proves it. R3 WP: RETIRED as a risk (mask/fupd present,
  Language fits; §4, §5.3). R4 UB channel: vocabulary pinned (§2.6);
  the non-UB `Other` arms are the finding — statement duty on
  artifact 3. R5 provenance: RETIRED as an idealization risk — the
  honest `x` is `PV (Prov_some id) (PVconcrete none addr)` and the ↦
  carries the id (§2.7, §5.2). R6 bind: route chosen (lifted Esseq
  tau-step, no monadic bind layer; §5.3) — OPEN until proved on live
  exhibits.
