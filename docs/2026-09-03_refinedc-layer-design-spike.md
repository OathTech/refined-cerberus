# The RefinedC-style layer above the demo logic — design spike (Lane C)

**Status: DRAFT design note, [AGENT 2026-09-03], read-only spike.** No
builds were run; every "measured" fact is a file:line reading of the
worktree at `907399d`, the pinned semantics at `.cerberus-ws/lean_frontend`
(the `generated/` tree), or the donor at `deps/refinedc/theories`.
"Estimate" marks a sizing guess. Nothing here is a ruling; the port
ledger (§7) is for the operator to adjudicate.

Steer received mid-spike ([USER 2026-09-03], verbatim): "we only want to
adopt refinedC inasmuch as it supports our goal of agent-driven formal
verification for very large bits of software. We mostly want to support
an agent-driven verification workflow over core. So this doesn't literally
require refined-C, it requires the slice of refinedC which supports that
goal." The organizing test for every element below is therefore: **does
this make an agent more effective at verifying large Core programs?** —
not "does it match RefinedC". The ledger still records departures from the
donor, but the decision criterion in each row is that test.

## 0. The slice of RefinedC we take, and why

The agent's workflow over Core has five moves: (i) state a per-procedure
spec; (ii) drive every straight-line stretch mechanically; (iii) supply
loop invariants and the hard steps by hand; (iv) read a failed goal and
act on it; (v) re-run after a code change. RefinedC's architecture serves
(i)–(iv) through three things, and those three are the slice:

1. **Types as uniform spec vocabulary** (`v ◁ᵥ ty`, `l ◁ₗ ty`, type.v:437-439):
   a spec written as `p ◁ₗ &own (struct [int i32 @ n; …])` is shorter and
   more uniform than the byte-image assertions the demo's clients write
   today (`twoField tds p xb yb` indexed by BYTE IMAGES, ReadinessSmoke
   header, measured). Uniformity is what lets one rule table drive
   thousands of statements — the agent's leverage on large code. TAKEN,
   for the scalar/struct/array/pointer/existential/constraint formers
   (§1.3); NOT taken: the subtyping/coercion apparatus (`subsume_*`
   instance families, programs.v:756-922), `Copyable`/`Shr` sharing
   (type.v:367-375) for now, the annotation language.
2. **The judgment shape**: syntax-directed rules with a constructor-headed
   conclusion, ownership atoms as premises and a wand-continuation, pure
   side conditions last (programs.v `typed_*` definitions, §2). This is
   what makes a straight-line executor a table lookup and makes failed
   goals small and uniform (move iv). TAKEN in full. NOT taken: Lithium's
   engine (`find_in_context`/`simplify_*`/`li_tactic`, definitions.v:164,
   206, 211, 305) — the ruling [USER 2026-09-02] stands; its work is done
   by a Lean tactic with a hand-maintained rule table (§4).
3. **Per-procedure compositional specs with a persistent table** (`typed_function`,
   function.v:59-66; `fntbl_entry`, ghost_state.v:121-122; adequacy for
   `main`, adequacy.v:40-50). This is move (i) and the only route to "large":
   procedures verified once, called many times. TAKEN, but it WAITS for the
   calls arc (§3, §5).

What we do NOT take and why (goal test): RefinedC's push-button
completeness engineering (Lithium's committed-choice interpreter, evar
discipline, port-map §3.5-3.6) exists so a HUMAN annotates once and never
sees a goal; our agent reads goals, so a stopping executor that leaves
readable residue is enough and far cheaper. Its frontend/annotation layer
is out of scope by ruling. `mem_cast`/`op_type` generality (type.v:260,
283-296) exists for Caesium's untyped byte reads; Cerberus decodes at the
action's ctype (§1.2), so there is nothing to generalize over yet.

## 1. Types as predicates over the raw assertions (Q1)

### 1.1 The donor record, and the honest counterpart

Donor (type.v:249-296, verbatim excerpt):
```
Record type `{!typeG Σ} := {
  ty_has_op_type : op_type → memcast_compat_type → Prop;
  ty_own : own_state → loc → iProp Σ;
  ty_own_val : val → iProp Σ;
  ty_share l E : ↑shrN ⊆ E → ty_own Own l ={E}=∗ ty_own Shr l;
  ty_shr_pers l : Persistent (ty_own Shr l);
  ty_aligned ot mt l : ty_has_op_type ot mt → ty_own Own l -∗ ⌜l `has_layout_loc` ot_layout ot⌝;
  ty_size_eq ot mt v : ty_has_op_type ot mt → ty_own_val v -∗ ⌜v `has_layout_val` ot_layout ot⌝;
  ty_deref ot mt l : ty_has_op_type ot mt → ty_own Own l -∗ l↦: ty_own_val;
  ty_ref ot mt l v : ty_has_op_type ot mt → ⌜l `has_layout_loc` ot_layout ot⌝ -∗ l↦v -∗ ty_own_val v -∗ ty_own Own l;
  ty_memcast_compat v ot mt st: ty_has_op_type ot mt → ty_own_val v ⊢ match mt with … end;
}.
```
Our assertions (measured): `pointsToCell tds pv dq ty bs` (Heap.lean:1544 —
a real `PointerValue` with provenance, whole allocation, byte image `bs`),
`pointsToView tds id a aty off dqm dqb vty bs` (Heap.lean:1509 — a typed
sub-range), `cellOwn` (:1529), `allocMeta` (:1982, persistent), `locInBounds`
(:2007), `allocCap` (:2078); every one takes the tag environment `tds`
explicitly (DECISIONS 2026-09-02, tag environment as a parameter).
Ownership is `DFrac` (fractional laws `cellOwn_fractional`,
`pointsToView_fractional`, persistence by `.discard`).

Proposed counterpart (layer-level, imports `CerberusHeapLang.API` only):
```
structure CoreType (GF) [SpikeGS hlc GF] (tds : TagDefsMap) where
  cty    : ctype                                  -- the ONE C type the memory ops name (§1.2, ledger 2)
  ownVal : value → IProp GF                       -- v ◁ᵥ ty        (donor ty_own_val)
  ownLoc : PointerValue → DFrac → IProp GF        -- p ◁ₗ{dq} ty    (donor ty_own; β := DFrac, ledger 1)
  deref  : ∀ p, ownLoc p (.own 1) ⊢ ∃ bs mv, pointsToCell tds p (.own 1) cty bs ∗
             ⌜decIndep tds (addrOf p) cty bs ∧ decodeCell tds ⟨addrOf p, cty, bs⟩ = mv⌝ ∗
             ownVal (valueFromMemValue mv).2      -- donor ty_deref
  ref    : ∀ p v mv, ⌜memValueFromValue tds cty v = some mv ∧ StorableAt tds cty mv⌝ ∗
             pointsToCell tds p (.own 1) cty (memValueToBytes tds [] mv).2 ∗ ownVal v ⊢
             ownLoc p (.own 1)                    -- donor ty_ref
  fits   : ∀ v, ownVal v ⊢ ⌜∃ mv, memValueFromValue tds cty v = some mv ∧ StorableAt tds cty mv⌝
                                                  -- donor ty_size_eq: "the value fits the type"
```
Dropped fields and why: `ty_has_op_type`/`ty_aligned` collapse into `cty`
(ledger 2 — alignment is inside `allocateObject`'s metadata, `MetaCoh`
Heap.lean:833, and the load/store rules never ask for it); `ty_share`/
`ty_shr_pers` deferred with the read-only stratum (ledger 1, 16);
`ty_memcast_compat` becomes the round-trip law of §1.2 (ledger 3).
Refinements: `rtype A := A → CoreType` exactly as type.v:464-474
(`x @ r`); `int ity : rtype Int`, `ownPtr ty : rtype PointerValue`.

For scalar types `ownLoc` is DEFINED from `ownVal` (the `deref`/`ref`
pair is then definitional): `ownLoc p dq := ∃ bs mv, pointsToCell tds p dq
cty bs ∗ ⌜decode facts⌝ ∗ ownVal (loaded mv)`. Struct/array types define
`ownLoc` over `pointsToView`s and `ownVal` over `MVstruct`/`MVarray`
values; there `deref` is the view-join law (`pointsToView_join`,
`cellOwn_view`), not definitional — this is why the record keeps both
fields, as the donor does.

### 1.2 The value layer — measured, and the first identified gap

Cerberus values: `IntegerValue = IV prov n` (CerbMem.lean:61), `PointerValue
= PV prov (PVnull ty | PVfunction sym | PVconcrete um addr)` (:47-58),
`AbsByte = {prov, copyOffset : Option Int, value : Option UInt8}` (:96).
Core-level integers come in TWO spellings — `Vobject (OVinteger iv)` and
`Vloaded (LVspecified (OVinteger iv))` — both accepted by `memValueFromValue`
(Core_aux.lean:106, the `Basic (Integer ity)` arms), the second produced
by `valueFromMemValue` on loads (Rules.lean:91 `loadedVal`).

Serialization `memValueToBytes` (CerbMem.lean:580-673), measured:
- `MVinteger ity (IV prov n)` → `sizeof_ity ity` bytes, each `{prov, copyOffset
  := none, value := byte_i (n mod 2^(8·sz))}` via `intToBytes` (:504 — wraps
  negatives, truncates out-of-range).
- `MVpointer _ (PV prov (PVconcrete _ addr))` → 8 bytes (`targetPtrSize`,
  :273) `{prov, copyOffset := some i, value := byte_i addr}` (:633-640);
  `PVnull` → zero bytes, `Prov_none`, no copyOffset (:615-618); `PVfunction`
  → the symbol's nat AND a funptrmap registration (:620-632).

Decode `reconstructValue` (:686-808), measured: integer arm = `MVinteger
ity (IV (fold combineProv from Prov_none) (bytesToInt bytes signed))`
(:694-701); pointer arm = zero address ⇒ `PVnull pointeeCty` with
`Prov_none` (:723-725); nonzero ⇒ `PVconcrete none ptrAddr` with the
bytes' SHARED provenance (`splitBytesProv`, :551), union member dropped,
function pointee ⇒ funptrmap lookup, panic if absent (:730-737).

**Finding — does a clean `val_to_Z`-style round trip exist?** Partly, and
only concretely:
- INTEGERS: the round trip `decode (encode (IV p n)) = IV p n` holds
  exactly when `n` is in `ity`'s range (`intToBytes` wraps) — and
  provenance survives because `combineProv p Prov_none = p`,
  `combineProv p p = p` (:227-236). It is table- and address-independent
  (the arm reads neither `lum` nor `fpm`). NOT PROVED SYMBOLICALLY
  anywhere: the demo proves only concrete instances by `rfl`
  (`seven_encodes`/`seven_storable`, Layout.lean:68-73, measured) and
  has `intToBytes_length/nonneg`, `bytesToInt_go_*/of_all_some`
  (Heap.lean:738-763) as ingredients. GAP 1: a lemma
  `bytesToInt (intToBytes n sz) signed = some n` for in-range `n`, and its
  `reconstructValue`/`memValueToBytes` wrapper — the `int ity @ n` type's
  `deref`/`ref` laws need it.
- OBJECT POINTERS: the round trip for `cellPtr id a` (Heap.lean:133 —
  `PV (Prov_some id) (PVconcrete none a)`) at `0 < a < 2^64` IS proved
  symbolically — `reconstruct_ptrImg_cell` (ListRevExhibit.lean:249-252,
  with `bytesToInt_ptrImg_cell` :186, `splitBytesProv_ptrImg_cell_fst`
  :236) — but at one fixed pointee type inside an EXHIBIT module. GAP 2:
  promote it, generalized over the pointee ctype, to the value layer.
- NO clean round trip for: `PVnull ty` (retyped to the LOAD's pointee,
  ledger 13); pointers with a union member (dropped); `PVfunction`
  (funptrmap-coupled — violates `StorableAt.fpm`/`decIndep`, Heap.lean:179,
  1501; excluded from arc 1, ledger 10); any zero address (reads as null).
- There is no `val_to_Z : value → integerType → Option Int` on Core values.
  The layer defines `valToZ` normalizing the two spellings and checking
  range (`CerberusImpl.sizeof_ity`/`is_signed_ity`, CerberusImpl.lean:77,
  123); `int ity @ n` then has `ownVal v := ⌜valToZ ity v = some n⌝` — the
  donor's `int_inner_type` shape (int.v:10-14, verbatim:
  `ty_own_val v := ⌜val_to_Z v it = Some n⌝%I`).

Integer provenance: `int ity @ n` quantifies it away (`∃ p`) — ledger 12.

### 1.3 Which formers first, and what each needs

| Former (donor) | Over our assertions | Needs from the demo core (Lane A) | Layer-only |
|---|---|---|---|
| `int it @ n` (int.v:10-25) | `ownVal := valToZ`; `ownLoc` derived via `pointsToCell` at `Basic (Integer ity)` | GAP 1 lemma (belongs in Heap.lean's codec section) | `valToZ`, the type, its load/store corollaries of `wps_load_plain`/`wps_store_plain` (Wps.lean:1820, 1841) |
| `&own ty` (own.v:11-34, `frac_ptr Own`) | `ownVal v := ∃ p, ⌜v = ptrVal p⌝ ∗ p ◁ₗ ty`; a pointer CELL holding it: `ownLoc` via `pointsToCell` at `Pointer _ ty.cty` | GAP 2 promotion; `addrOf p ≠ 0` fact rides on `wps_create`'s bound (Wps.lean:2223) | the former; `ptr`/`null` (own.v:375, 451) as siblings |
| `struct` (struct.v:54) | `ownLoc p := ∃ id a, ⌜p = cellPtr id a⌝ ∗ [∗ fields] pointsToView … off_f …` — the ReadinessSmoke `twoField` generalized over a field list; `ownVal` over `MVstruct`/`OVstruct` | `memberShiftPtrval` law (CerbMem.lean:1183, twin of `cellPtr_arrayShift`); a `.Struct` ctype decode-inertness lemma for scalar-member structs (`offsetsof` reads `tds` only — measured :772) | the former, field focus (§2 place) |
| `array` (array.v:9, 158) | views at `i·sizeof elem` | none new (`pointsToView_split/join`) | the former, index focus |
| `∃ x. ty` (exist.v:18), `constrained` (constrained.v:14) | `ownVal v := ∃ x, (x @ r).ownVal v`; `ty ∗ ⌜P⌝` | none | trivial |
| `optional` (optional.v:44) | `if b then ty else null` — the null case is ledger 13 | none | after `null` |
| read-only / `Shr` | needs `CellCoh.alloc … isReadonly = .IsWritable` (Heap.lean:329) relaxed to a stratum | Lane A: a read-only cell stratum in the coupling invariant (with globals) | — |
| `value`, `place` (singleton.v:8, 172) | `ownVal v := ⌜v = v₀⌝`; `ownLoc p := ⌜p = p₀⌝` | none | trivial; the agent's "I know the exact value" escape hatch |

ADDED TO THE DEMO CORE (Lane A, small, spec-addition slices): GAP 1; the
generalized GAP 2; the `memberShiftPtrval` shift law; later the read-only
stratum. Everything else is layer-only.

## 2. The judgment shape for automation (Q2)

Donor judgments (programs.v, verbatim where relied on):
```
Definition typed_val_expr (e : expr) (T : val → type → iProp Σ) : iProp Σ :=
  (∀ Φ, (∀ v (ty : type), v ◁ᵥ ty -∗ T v ty -∗ Φ v) -∗ WP e {{ Φ }}).                 (:96-97)
Definition typed_stmt (s : stmt) (fn : function) (ls : list loc) (R : val → type → iProp Σ) (Q : gmap label stmt) : iProp Σ :=
  (⌜length ls = length (fn.(f_args) ++ fn.(f_local_vars))⌝ -∗ WPs s {{Q, typed_stmt_post_cond fn ls R}})%I.   (:68-69)
Definition typed_block (P : iProp Σ) (b : label) (fn : function) (ls : list loc) (R : val → type → iProp Σ) (Q : gmap label stmt) : iProp Σ :=
  (wps_block P b Q (typed_stmt_post_cond fn ls R)).                                     (:72-73)
```
plus `typed_read`/`typed_write` (:157, :146) dispatching to
`typed_read_end`/`typed_write_end` (:174-178, :186-188), `typed_place`
(:324-326), `typed_call` (:117-118), `typed_if` (:51), and Lithium's
`subsume P1 M P2 T := P1 -∗ ‖M‖ ∃ x, P2 x ∗ T x` (definitions.v:220).

What survives over Core, and how (goal test in brackets):

- `typed_val_expr` COLLAPSES to a pure judgment. Core operands of every
  action/memop/call/`if`/`run` are PURE expressions evaluated big-step
  (shape study §3(iv); measured in the rules: `wps_if`'s premise
  `⌜evalPexpr M.tagDefs M.extern ρ g = some (boolValue b)⌝`, Wps.lean:1037;
  `wps_pure` :1253; `wps_save`'s `evalPexprs`, :1187). So
  `typedPexpr M ρ pe T := ∃ v ty, ⌜evalPexpr M.tagDefs M.extern ρ pe = some v⌝ ∗ v ◁ᵥ ty ∗ T v ty`
  — no WP. [Agent leverage: operand typing becomes a pure goal `omega`/
  `decide` can close; the executor never enters a sub-WP.]
- `typed_place` COLLAPSES: Core has no lvalue expressions; a load is
  `loadExpr loc ann ty pv mo` on a pointer VALUE (Rules.lean:71) and field/
  element addressing is pure pointer arithmetic (`PEarray_shift`/
  `PEmember_shift` pexprs; `arrayShiftPtrval` CerbMem.lean:1165 keeps
  `prov`). What survives is the donor's FOCUS shape — "walk to the field,
  return its type and a type-transformer for the write-back" (`T l2 β2 ty2
  typ R`, :324-326) — as an assertion-level lemma per composite former:
  `focus_field : p ◁ₗ struct tys ⊢ (memberShift p f) ◁ₗ tys[f] ∗ (∀ ty', (memberShift p f) ◁ₗ ty' -∗ p ◁ₗ struct (tys[f := ty']))`.
  [Leverage: field writes stay compositional without re-splitting views by
  hand — the ReadinessSmoke `twoField_store_y` proof is 20 lines of view
  plumbing today (measured), the focus lemma makes it one rule.]
- `typed_read_end`/`typed_write_end` SURVIVE as the typed small axioms
  over `wps` (one per scalar former, corollaries of `wps_load_plain`/
  `wps_store_plain`/`wps_load_at`/`wps_store_at`).
- `typed_stmt` MAPS to `wps` at a typed post: `typedStmt M Ls R e ρ := wps M Ls
  (fun w ρ' => ∃ ty, w.val ◁ᵥ ty ∗ R w.val ty) e ρ` — minus the locals'
  points-to (ledger 6). `typed_block` MAPS DIRECTLY onto the label context,
  as the brief anticipated: donor `Q : gmap label stmt` is our
  `M.labels`/`lookupLabel` (Step.lean:276-282, the engine's own
  `labeled_continuations`), donor block precondition `P` is `Ls l`
  (Wps.lean:83, `LabelSpec := sym → List value → EnvStack → IProp`), donor
  `wps_block_rec`'s job is `blockSpecs_intro` (Wps.lean:2299 — no Löb at
  the rule). Two Core-forced differences: labels take ARGUMENTS (ledger 7)
  and blocks are also entered by fall-through (`wps_save`, ledger 8).
  [Leverage: loop invariants are label preconditions the agent writes
  once, in the same vocabulary as procedure pre/posts.]
- `typed_if` MAPS to `wps_if` with the verdict inside the logic (measured,
  Wps.lean:1037); the typed version adds evaluator laws turning
  `evalPexpr … (PEop OpLt x y)` into `⌜n < m⌝` under `x ◁ᵥ int _ @ n`.
- `subsume` SURVIVES, without the modality: `subsume P₁ P₂ T := P₁ -∗ ∃ x,
  P₂ x ∗ T x`. Used at exactly three places: jump (discharging `Ls l vs ρ`
  from the context), value exit (the typed post), call precondition
  (later). [Leverage: it is the ONE goal shape the agent sees when the
  executor stops.]
- `find_in_context`, `simplify_hyp/goal`, `li_tactic`: NOT judgments here
  — tactic behaviour (§4).
- `typed_call`/`typed_function`: WAIT for calls (§3).

MINIMAL SET FOR THE FIRST ARC (six): `◁ᵥ`, `◁ₗ`, `typedPexpr`, `typedStmt`
(= `wps` at the typed post), label entries in the typed shape (block
judgment), `subsume`. Rule-statement discipline (the contract the tactic
relies on): (R1) the conclusion is `wps M Ls Ψ (Expr a (K …)) ρ` with `K` a
fixed constructor and metavariables only in operand slots; (R2) premises in
order: the ownership atoms the rule CONSUMES (matched by pointer syntax),
then the wand-continuation `(atoms' -∗ Ψ w ρ')`, then pure side conditions
as separate hypotheses; (R3) side conditions are closed under a named
solver (`rfl`, `decide`, `omega`, `simp [codec]`); (R4) the post `Ψ` is
`AnnotInsensitive` (Wpt.lean:2147) so the `_plain` forms apply and no
footprint quantifier reaches the agent (ledger 15). Example, stated over
our `wps` (all names as in API.lean):
```
theorem typed_store_int {Ψ} (hΨ : AnnotInsensitive Ψ)
    (loc ann) (ity : integerType) (p : PointerValue) (cv : value) (mo) (n m : Int) (ρ : EnvStack)
    (hcv : valToZ ity cv = some m) :                        -- pure side condition (R3: `rfl`/`decide`)
    iprop(p ◁ₗ (n @ int ity) ∗                                -- consumed atom (R2)
      (p ◁ₗ (m @ int ity) -∗ Ψ (.pure Vunit) ρ)) ⊢          -- continuation
      wps M Ls Ψ (storeExpr loc ann (intCty ity) p cv mo) ρ  -- constructor-headed (R1)
```
Its proof is `wps_store_plain` (Wps.lean:1820) plus GAP 1. The operand
form (`Store0` with pexpr operands) is reached first by the separate
syntax-directed step `wps_store_eval`, then this rule — two table entries,
no rule does two jobs (one-change-at-a-time applied to rule design).

## 3. Spec attachment to compiled Core (Q3)

How Core calls work (measured): a procedure is `Proc loc marker bty params
body` in `file.funs : generic_fun_map` (Core.lean:1652 ff.; ProdEntry's
`mainDecl e := Proc CerbLocation.unknown none BTy_unit [] e`, :94-95).
`call_proc` (Core_run.lean:93) resolves `psym` through `file.stdlib`, then
the `extern` redirect, then `file.funs`; checks arity; binds `params` to
the evaluated argument values as a fresh env frame by `foldl2 … fmapAddBy`.
The PCALL arm of `step_ctx` (Core_reduction.lean:484, `Eproc _ (Sym psym)
pes`) evaluates the operands purely (`full_eval_pexpr'`), pushes the caller
context (`Stack_cons2 parent_proc_opt caller_ctx sk'`), sets
`current_proc_opt := some psym` and `env := proc_env :: …`; the return arm
pops it, converts the value through `funinfo`'s return type (`TSK_Return`)
and reinstates `apply_ctx caller_ctx (Epure (mk_value_pe cval))`. Return
inside a body is a LABEL: one `ret_N` save per procedure, every `return` an
`Erun ret_N(v)` (shape study §3(ii)).

Proposed attachment (Hoare's recursive-procedure rule in RefinedC's
`fn_params` shape, function.v:42-51 — `fp_atys`, `fp_Pa`, `fp_rtype`,
`fp_fr`):
```
structure ProcSpec (GF) where
  A    : Type                                       -- fp_rtype
  pre  : A → List value → IProp GF                  -- ⊢ [∗] vs ◁ᵥ atys x ∗ Pa x  (fp_atys + fp_Pa)
  post : A → value → IProp GF                       -- fn_ret_prop's ∃-free core (function.v:53-54)
abbrev SpecTable (GF) := sym → Option (ProcSpec GF)
def procOK (M : MachineCtx) (Σ : SpecTable GF) (f : sym) (sp : ProcSpec GF) : IProp GF :=
  □ ∀ x vs ρ, ⌜M.proc = some f ∧ lookup f M.file.funs = some (Proc _ _ _ params body)⌝ -∗
      sp.pre x vs -∗ wps M (retLs f (sp.post x)) (typedPost (sp.post x)) body (bindArgs params vs ρ)
```
where `retLs f Q` sets `Ls ret_N [v] _ := Q v` — the donor's `fn_ret_prop`
IS a label precondition for us (the return label), so no new judgment is
needed for return. The table `Σ` is the donor's `fntbl` (ghost_state.v:29,
`ghost_mapG Σ addr function`) keyed by `sym` instead of address (ledger
10); it enters `MachineCtx`-side as a persistent assumption the call rule
consults: `typed_call : Σ f = some sp → sp.pre x vs ∗ (∀ v, sp.post x v -∗ Ψ …)
⊢ wps M Ls Ψ (Expr a (Eproc _ (Sym f) pes)) ρ` — donor `type_call_fnptr`
(function.v:131) without the pointer. The ONE Löb: adequacy assumes
`∀ f sp, Σ f = some sp → procOK M Σ f sp` under `▷`, exactly where the
donor ties `fntbl_entry ∗ ▷ typed_function` in `function_ptr`
(function.v:106-121) and pays it in `refinedc_adequacy`. CANNOT START
until the calls arc lands a `wps` rule for `Eproc`/the stack (the mirror
has no PCALL/return step today — `Frag`, Soundness.lean:3058, measured).

`main` and globals (measured, Driver.lean `drive`): `driver_globals` runs
FIRST; `main` is looked up in `core_file.funs` (`Fun` and `Proc` arms;
`ProcDecl`/`BuiltinDecl` kill); with params `[argc, argv]` the driver
allocates and stores argc/argv objects (`prepare_main_args`); then `errno`
is allocated (`prodMem₀` accounts for it, ProdEntry.lean:189); the
entry is `initial_driver_state sup file fs` (Driver.lean:446-449). Today
the production statements wrap ONE authored body as `prodFile e`
(ProdEntry.lean:102-114: `main := some mainSym`, `globs := []`, `funs :=
{mainSym ↦ mainDecl e}`). Attachment for a COMPILED file: `file` is the
compiler's output (Lane B's compiled-Core exhibit), `Σ` is Lean-authored,
and the whole-program theorem generalizes `prod_run_eqJ` (ProdEntry.lean:332):
```
theorem program_adequate (file) (Σ) (hΣ : ∀ f sp, Σ f = some sp → ⊢ procOK (ctxOf file f) Σ f sp)
    (hmain : Σ mainSym = some ⟨Unit, fun _ _ => launchPre file, fun _ v => ψ v⟩) … :
    CerbND.runND (drive fmapEmpty false file args) (initial_driver_state sup file fs).1 ⟶ readout ψ
```
— donor `refinedc_adequacy` (adequacy.v:40-50: globals `[∗ list] l;v ∈ gls;gvs,
l ↦ v`, table `[∗ map] k↦qs ∈ fns, fntbl_entry …`, `main ◁ᵥ main @
function_ptr (main_type P) ∗ P`, conclusion `not_stuck`). Ours ends at the
shipped composite as the four production statements do (ARCHITECTURE §6);
until the fuel-exhaustion request lands, the generic partial form inherits
PROVISIONAL. Globals need the post-`driver_globals` memory as the launch
premise (arc 1 restricts to `globs = []`; ledger 1/16 for read-only
globals). Estimate for the attachment layer once calls exist: 1 week.

## 4. The automation stance, concretely (Q4)

The smallest proof-producing tactic that makes the ReadinessSmoke
derivations mechanical is a one-step symbolic executor `tstep` (and its
loop `texec`) over `wps`, in Lean 4 meta terms:

1. Precondition: the goal is an Iris proof-mode entailment whose
   conclusion is `wps M Ls Ψ e ρ`. `whnfR e` to `Expr a (K …)` — `K` is the
   dispatch key. (Core's syntax is a plain inductive; `Frag`'s redex shapes
   `storeRedex`/`loadRedex`/`saveRedex`… are already the normal forms.)
2. Rule table `K ↦ [rules]`, each rule obeying R1-R4 (§2): `Esseq` →
   `wps_seq`/`wps_seq_sym`/`wps_seq_spec` by pattern; `Eif` → `wps_if`;
   `Esave` → `wps_save`; `Erun` → `wps_run` then a `subsume` goal on `Ls`;
   `Eaction (Store0/Load0 …)` with pexpr operands → `wps_store_eval`/
   `wps_load_eval`, then the typed small axiom; `Epure` → `wps_pure`/
   `wps_ofVal`; `create` → `wps_create` + the former's `ref`.
3. Atom matching (the `find_in_context` replacement): for a memory rule,
   read the pointer operand `p` from the redex, normalize it (`simp only
   [cellPtr_arrayShift, fieldShift_cellPtr, …]` to `cellPtr id (a + off)`),
   then scan the proof-mode hypothesis telescope for `_ ◁ₗ _` /
   `pointsToCell _ p' …` with `p'` defeq to `p`; if `p` is a symbol,
   resolve it through the env laws (`envAdd_lookup`, EnvLaws) first.
4. Apply: `iapply rule <args>; isplitl [H]; · iexact H` — the frame is
   FREE: the rule consumes exactly the matched atom and the continuation
   wand keeps every other hypothesis in context (this is the whole reason
   for R2's wand-continuation shape; measured in every `wps_*` statement).
5. Side conditions: try, in order, `rfl`, `decide`, `omega`, `simp [valToZ,
   StorableAt, …]`; anything unsolved is LEFT as a goal tagged with the
   action's `loc` — the agent's feedback (move iv).
6. `texec` repeats until the redex is a jump/value/unmatched constructor,
   then reports why it stopped (constructor, missing atom, unsolved side
   goal). Replayability (move v): the proof script is `texec` + the
   hand-supplied invariants; a code change re-runs it and fails at the
   first changed statement.

Implementation: compose existing proof-mode tactics via `evalTactic` on
quoted syntax (the demo's proofs are exactly these five tactics); the
table is a `List (Name × Syntax)` per constructor, extended by hand.
Estimate 400-800 lines of meta code for the arc-1 fragment. What it needs
from §2: R1 (dispatch by constructor), R2 (atom-first premises, wand
continuation), R3 (named solvers), R4 (`_plain` rules only).

## 5. The first arc of the root package (Q5)

**Arc R1 — "scalar and struct types with a straight-line executor, over
`wps`".** Package: `RefinedCerberus/` (root). Dependency: the demo's
`CerberusHeapLang.API` — via a Lake path `require` on `cerberus-heaplang`
(today the root has none, lakefile.toml measured; the alternative, a COPY
per the derisking ruling, is wrong here: the root is the product and the
demo API its declared base — operator decision needed).

Slices (one change each; FAST-GATE between, FULL gate at the end):
- S0 wiring: the path require; a smoke import. (est. 0.5 d)
- S1 value layer: `valToZ`; GAP 1 (symbolic integer round trip) and GAP 2
  (pointer round trip, general pointee) — both landing in the DEMO as Lane
  A spec-addition slices, consumed here. (est. 2 d)
- S2 `CoreType`, `rtype`, `int`, `ownPtr`/`null`, `value`; typed load/store/
  create rules as corollaries; `subsume` + its five instances. (est. 2 d)
- S3 `typedPexpr`, `typedStmt`, typed label entries; evaluator laws for the
  eight mirrored binops on typed ints. (est. 2 d)
- S4 `struct`/`array` formers over views; `focus_field`/`focus_index`;
  needs the `memberShiftPtrval` law (Lane A). ReadinessSmoke's `twoField`
  becomes `struct [long @ x; long @ y]`. (est. 2-3 d)
- S5 `tstep`/`texec`; ReadinessSmoke re-derived mechanically as the
  regression exhibit; measurement: manual tactic lines per Core statement
  before (≈20/rule today) and after. (est. 3-5 d)
- S6 acceptance exhibit: an agent-driven verification of a never-seen
  program — hand-written Core if Lane B's compiled exhibit is not in yet
  (a loop over a two-field struct array, say), compiled Core if it is —
  with the WORKFLOW measured: spec lines, invariant lines, manual steps
  per statement, `texec` stop count, and the re-run after a one-line
  change. (est. 2-3 d)
Total estimate: 2.5-3.5 weeks, one worker.

Exports (the two trust claims, over the demo's): (1) closed-program
statements stay Iris-free over the shipped composite (inherited; the
generic form waits on the fuel request); (2) the layer adds NO axiom and NO
state interpretation — `◁ᵥ`/`◁ₗ` are definitions over `pointsToCell`/
`pointsToView`; the speedbump is the `parametric_inventory` client line
(zero internal references, as ReadinessSmoke measures today).

CAN start now: S0-S5 on hand-written fragment Core (integer/pointer types,
struct-as-views, the judgment shape over straight-line code, the tactic).
CANNOT start until calls land: `ProcSpec`/`procOK`/`typed_call`, the Löb,
`program_adequate` beyond a `main`-only file. CANNOT reach compiled Core
until Lane A extends `Frag` past its declared operand grammar: compiled
bodies use `Ebound` around every full expression, `let weak`, `Ecase`
truthiness, and stdlib pexpr calls (`conv_loaded_int`, `params_length`,
`are_compatible`; shape study rows 1, 7, 11), none in `Frag`
(Soundness.lean:3058-3120 measured), plus `kill` for every local (kill/free
arc). The layer itself is indifferent — its rules are per-constructor — but
the north-star exhibit on compiled code is gated on those two lanes.

## 6. Divergences from RefinedC — the opening port ledger (Q6)

Bins: (a) unnecessary invention → adopt theirs; (b) real Cerberus
constraint → forcing fact; (c) inherited pseudo-constraint → named and
priced. Decision criterion in every row: the agent-leverage test.

| # | Donor (cite) | Ours | Bin | Forcing fact / price |
|---|---|---|---|---|
| 1 | `own_state := Own \| Shr` (type.v:40, 264) | `DFrac` | (b) | the demo's ownership algebra is fractional (`cellOwn_fractional`, Heap.lean); `Shr`'s job (globals) needs Cerberus's `isReadonly` allocation flag, which `CellCoh` pins to `IsWritable` (:329) — a later stratum |
| 2 | `ty_has_op_type ot mt` + `ty_aligned` (type.v:260, 273) | one `cty` field | (b) | `loadM tagDefs loc ty pv` / `storeM … ty` (CerbMem.lean:1621, 1667) decode/encode at the action's ctype; no separate layout stratum exists. Price: no `UntypedOp` byte reads until a `bytes` former |
| 3 | `ty_memcast_compat`/`mem_cast` (type.v:283-296) | the codec round-trip law (`deref`∘`ref`) | (b) | Cerberus has no `mem_cast`; the load's value IS `reconstructValue` of the bytes; `MCId` = exact round trip (§1.2) |
| 4 | `typed_val_expr` over `WP e` (programs.v:96) | `typedPexpr`, pure | (b) | Core operands are pure pexprs evaluated big-step (`wps_if`/`wps_pure`/`wps_save` premises, Wps.lean:1037, 1253, 1187) |
| 5 | `typed_place` with `place_ectx_item` (programs.v:204-326) | focus lemmas per composite former | (b) | Core has no lvalues; field/index addressing is pure pointer arithmetic on values (`arrayShiftPtrval` :1165, `memberShiftPtrval` :1183, provenance-preserving) |
| 6 | `typed_stmt_post_cond` returns locals' `l ↦\|ly\|` (programs.v:66-67) | none | (b) | Core allocates/frees locals as explicit `create`/`kill` actions (shape study rows 7-8) |
| 7 | `wps_block P b Q`, unindexed `P` (programs.v:72) | `Ls : sym → List value → EnvStack → IProp` (Wps.lean:83) | (b) | `Esave` has parameters, `Erun` passes arguments; env-indexing is the recorded Core finite-map finding (Wps.lean:71-82) |
| 8 | blocks entered only by `Goto` | `wps_save` fall-through entry | (b) | Core saves are nested expressions (shape study §3(ii)) |
| 9 | `Forall2 ty_has_op_type … f_args` in `typed_function` (function.v:60) | dropped | (b) | procedure params are values in an env frame (`call_proc`, Core_run.lean:93), not stack slots |
| 10 | `fntbl_entry (fn_loc a) f` by address; `function_ptr` (ghost_state.v:121; function.v:106-121) | `SpecTable : sym → Option ProcSpec`; function pointers deferred | (b) | calls resolve by symbol (`Eproc _ (Sym psym)`, PCALL, Core_reduction.lean:484; `call_proc` order stdlib→extern→funs); `PVfunction` bytes are funptrmap-coupled (CerbMem.lean:620-632, 730-737) so no table-independent value type exists for them yet |
| 11 | Lithium (`find_in_context`, `simplify_*`, `li_tactic`; definitions.v:164-334) | tactic behaviour, hand-kept rule table | (c) | ruling [USER 2026-09-02]; price: no extension-by-instance, table maintained by hand — acceptable at arc scale; revisit if the table exceeds ~100 rules |
| 12 | `int it @ (n : Z)` (int.v:10-25) | `∃ p, IV p n` — provenance quantified away | (c) | Cerberus integers carry provenance (`IV prov n`, :61); price: `intfromptr`/`ptrfromint` round trips are unprovable through `int`; revisit with the pointer-op family |
| 13 | `null : type` (own.v:451) | `null` indexed by the load's pointee | (b) | zero bytes reconstruct to `PVnull pointeeCty` of the LOAD type with `Prov_none` (CerbMem.lean:723-725), and any zero address reads as null |
| 14 | `typed_read … memcast` flag (programs.v:157) | none | (b) | as 3 |
| 15 | raw post `Φ v` | `AnnotInsensitive` posts, `_plain` rules | (b) | Core actions deliver footprint-annotated values `{DA_pos fp} v` (Wps.lean:1776-1857); Caesium has no dynamic annotations |
| 16 | `ty_share`/`ty_shr_pers`, `Copyable` (type.v:268-270, 367-375) | deferred | (b)/(c) | as 1; price: no shared reads of globals in arc 1; `Copyable`'s `▷` protocol is unneeded — our loads at any `dq` already return the view (`wps_load_at`) |
| 17 | `typed_annot_expr/stmt`, `typed_assert`, `typed_switch`, `typed_macro_expr` (programs.v:41-92, 136) | not ported | (c) | annotation-language/frontend conveniences; price: none for an agent that writes Lean |

## 7. Risks (top three first)

1. **Compiled Core is outside today's fragment.** `Ebound`, `let weak`,
   `Ecase` truthiness, stdlib pexpr calls, and `kill` are all in every
   compiled body and none is in `Frag` or the mirror evaluator (mirror
   completeness gap (c), DECISIONS 2026-09-02). The type layer can be built
   and measured on hand-written Core, but the north-star exhibit on a
   compiled program is gated on Lane A/B extending the fragment. Mitigation:
   S6 is defined with both exhibits; the layer's rules are per-constructor
   so nothing is thrown away.
2. **Evaluator laws for typed arithmetic/comparison.** Typed `if` and
   arithmetic need `evalPexpr` laws over the operand grammar; only eight
   integer binops are mirrored (measured). Each missing law is a stop in
   `texec`. Mitigation: S3 lists the laws; gaps become Lane A requests.
3. **Pointer normal forms in atom matching.** `tstep` matches atoms by
   pointer syntax; shifts, env lookups and `Prov_some id` vs symbolic
   pointers can defeat defeq. Mitigation: fix `cellPtr id (a + off)` as the
   normal form and prove every shift law into it before S5.
Also: the PROVISIONAL inheritance until the fuel-exhaustion request lands;
the `.Struct` decode's OCaml addr-quirk (CerbMem.lean:765-782) if real
struct ctypes replace array stand-ins; the root↔demo Lake wiring decision.
