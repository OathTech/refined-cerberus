# Port map: RefinedC layer map, typing-rule inventory, Lithium algorithm

**REV2 — review folded; re-mark by the original reviewer pending**

Date: 2026-08-29. Provenance: [AGENT: arc-1 recon worker], read-only
survey of `deps/refinedc` (checkout `25f706d417df2b18b23c5cbadde46468c1b1262c`,
upstream date 2026-07-16). All file:line cites are into
`deps/refinedc/` at that checkout. Claims verified against source
unless marked UNVERIFIED. The predecessor lithium review
(`cerberus-lean` park branch `arc/segment-ladder`,
`lean_frontend/docs/reasoning-era/2026-08-21_lithium-source-review.md`)
was used as a LEAD; every claim reused from it was re-checked against
the present source and is marked **[prior review, re-verified]** where
the reading originated there.

Revision block: **rev2, 2026-08-29** — revision folding the fresh-eyes
review (`docs/2026-08-29_port-map-review.md`; all 4 MAJOR, 8 MINOR,
4 NOTE findings). Provenance: [AGENT: revision worker]. Every folded
review claim was re-verified against source before folding (the
review's wrapping_add proof-term probe was re-run; its tallies
reproduce), with one correction to the review's own recount: hooks.v
carries **16** `Ltac *_hook` declarations, not 17 (§3.3).

Method note (derived, labeled as such): the §1.3 interface list was
produced mechanically — all top-level `Definition/Lemma/Class/Record/
Inductive/Fixpoint` names in `theories/caesium/*.v` (614 declarations)
intersected with the word-token set of `theories/typing/*.v`, then
located. It therefore covers named identifiers; notation-only uses and
constructor names are covered separately in §1.4. Sub-claims from the
mechanical pass were spot-checked, not individually re-read.

---

## 1. Layer map

### 1.1 Actual structure vs ARCHITECTURE.md

`ARCHITECTURE.md:12-16` describes the stack as `theories/lang`
(Caesium + Iris instantiation), `theories/lithium`, `theories/typing`,
with the invariant (`ARCHITECTURE.md:35-38`) "lang depends on neither;
lithium depends only on lang/base.v". **The document is stale.** In
the code as it is:

- `theories/lang` has been renamed `theories/caesium` (dir listing).
- The lithium↔semantics dependency is **inverted**: Lithium is a
  standalone package (`coq-lithium.opam` at repo root;
  `theories/lithium/dune` depends only on
  `Stdlib stdpp iris RecordUpdate Ltac2`) and imports **nothing** from
  caesium (grep over `lithium/*.v`: zero `From caesium` hits).
  Caesium **depends on Lithium** (`theories/caesium/dune`:
  `(theories caesium.config lithium ...)`; `caesium/base.v:1`
  `From lithium Require Export base`; `caesium/bitfield.v:2`
  `From lithium Require Import simpl_classes definitions`).
- `theories/typing` depends on both (`typing/dune`).

So the true stack, bottom-up:

```
lithium            Lithium: goal grammar + interpreter + solvers.
                   Iris-generic; knows nothing about C or Caesium.
caesium.config     compile-time switch: enforce_alignment
                   (config/config.v:9-22, module-sealed bool)
caesium            the C semantics: syntax, small-step opsem,
                   c_lang : language (Iris), heap ghost state,
                   WP/WPs lifting lemmas, reflected syntax W,
                   wp-bind tactics
refinedc.typing    the type system: `type` record, ~25 judgments,
                   type formers, typing-rule instance library,
                   RefinedC's Lithium instantiation (automation.v),
                   adequacy
frontend/          OCaml C→Caesium+annotations compiler (OUT OF SCOPE)
```

Port mapping: **caesium is the layer we replace** (Core + attachment
layer plays its role); **lithium and typing are ported as-is** (the
normative spec) — with one structural caveat: typing's place machinery
(`find_place_ctx`, programs.v:257; `IntoPlaceCtx`, programs.v:278) and
the automation's statement/expression dispatch (`liRStmt`/`liRExpr`,
automation.v:145-247) are defined over caesium's reflected syntax
`W.expr`/`W.stmt`, so "as-is" presupposes a Core-side
reflected-syntax analog — attachment design work over *Core's*
constructor set, not a literal port (agenda item 16). The inversion
is good news for the port: Lithium's Lean reimplementation needs no
semantics input at all. What caesium takes from lithium is wider than
utilities, and is itself instructive: besides `base` and the
`SimplifyHyp/SimplifyGoal` classes used to register bitfield
simplification rules, `caesium/bitfield.v` consumes `li_tactic`,
registers a `LiEntails` Hint Extern (bitfield.v:300), a
`NormalizeBitfield` extern (:316), and `CanSolve`-guarded
simplification instances (:328-357) — the one existing example of a
*semantics-layer* package feeding the Lithium hook surface, i.e. the
exact pattern our attachment layer will use.

### 1.2 What each caesium file provides

| File | Contents |
|---|---|
| `caesium/base.v` | re-exports lithium/base + unification/opacity settings |
| `caesium/loc.v` | `alloc_id`, `prov` (= `ProvNull \| ProvAlloc (option alloc_id) \| ProvFnPtr`, loc.v:20-23), `loc := prov * addr` (loc.v:49), `NULL_loc`, `offset_loc`/`+ₗ`, `aligned_to`, `has_layout_loc` |
| `caesium/layout.v` | `layout` record (size+align, layout.v:5), `layout_wf`, `ly_offset`, `mk_array_layout`, `void_layout` |
| `caesium/int_type.v` | `int_type` record (int_type.v:7), `it_layout`, `min_int/max_int/int_modulus`, `u8…size_t` |
| `caesium/struct.v` | `struct_layout`/`union_layout` records (struct.v:38,203) with named+padding field lists, `offset_of`, `field_*` lookup lemmas, `pad_struct`, and **`op_type`** (struct.v:251: `BoolOp \| IntOp it \| PtrOp \| StructOp sl ots \| UntypedOp ly`; `ot_layout` struct.v:258) |
| `caesium/val.v` | `mbyte` (byte \| pointer-fragment \| poison, val.v:7), `val := list mbyte` (val.v:26), `val_of/to_loc`, `val_of/to_Z`, `val_to_bool`, `i2v`, `NULL` |
| `caesium/byte.v`, `bitfield.v` | 8-bit byte model; bit-vector ops + normalization lemmas for bitfield types |
| `caesium/heap.v` | `heap_cell` (alloc_id, lock_state, mbyte; heap.v:11), `heap := gmap addr heap_cell`, `allocation` (heap.v:193), `heap_state` (heap.v:229: heap + allocations map), `alloc_id_alive`, `heap_at`, **`mem_cast`** (heap.v:383) + `mem_cast_id` (heap.v:415), `alloc_new_block(s)` (heap.v:498,510) |
| `caesium/lang.v` | `expr` (lang.v:28-42), `stmt` (lang.v:74-86), `function` (lang.v:90: `f_args`, `f_local_vars` — name×layout lists, `f_code : gmap label stmt`, `f_init : label`), `state` (lang.v:99: `st_heap : heap_state`, `st_fntbl : gmap addr function`), `runtime_expr`/`runtime_function` (lang.v:109-145), substitution (lang.v:196-238), `eval_bin_op`/`eval_un_op` (lang.v:240,340), `expr_step`/`stmt_step`/`runtime_step` (lang.v:397,499,535), evaluation contexts, and the Iris language instance: `c_lang_mixin`/`c_ectxi_lang`/`c_lang` (lang.v:714-720) |
| `caesium/ghost_state.v` | the RA layer: `heapUR` (per-address `(frac, lock_state, agree(alloc_id×mbyte))`, ghost_state.v:13-19), `heapG` (ghost_state.v:22-31: heap auth + 3 ghost maps: alloc metadata, alloc liveness, fn table), assertions `heap_mapsto` (`l ↦{q} v`, byte-list points-to bundled with `loc_in_bounds`, ghost_state.v:141-152), `heap_mapsto_layout` (`l ↦\|ly\|`, :212), `alloc_meta`, `loc_in_bounds` (:80-93), `alloc_alive` (:95), `alloc_global` (:107), `fntbl_entry` (:124), `alloc_alive_loc` (:161), `freeable` (:171), authoritative `state_ctx` (:195) + update lemmas (e.g. `heap_alloc_new_blocks_upd` :878) |
| `caesium/lifting.v` | `refinedcG` (lifting.v:9-12: invGS + heapG), `c_irisG : irisGS c_lang` with `state_interp := state_ctx` (lifting.v:14-20), expression `Wp` instance (:26), `Atomic` instances (:39-50), **the per-construct WP lemma library** (~55 lemmas, :146-999 — the complete list is in §1.3), the sealed statement weakest-pre `stmt_wp`/`WPs` (:1002-1017: parametrized by `Q : gmap label stmt`), `wp_call` (:1046), `wps_goto/return/assign/if/switch/...` (:1108-1305), `wps_block`/`wps_block_rec` (:1306-1309) |
| `caesium/tactics.v` | module `W`: a reflected copy of expr/stmt (tactics.v:9,378) with `to_expr/of_expr`, evaluation-context finders `find_expr_fill`/`find_stmt_fill` + correctness lemmas — the substrate for syntax-directed bind |
| `caesium/proofmode.v` | `wp_bind`/`wps_bind` tactics via W (proofmode.v:9-31,34-...) |
| `caesium/builtins_specs.v` | pure specs for builtins (ffs/clz-style bit lemmas) |

### 1.3 The consumed interface: the named-identifier stratum

**247 named caesium identifiers are referenced by `theories/typing/`.**
This is the *named-identifier stratum* of the surface our Core+Iris
attachment layer must supply — NOT the whole surface: the mechanical
method (top-level declaration names ∩ typing/ word tokens) is blind
to record projections, data constructors, silently-resolved typeclass
instances, and Ltac/hint-database consumption; those strata are
enumerated in §1.3.1–§1.3.4 below. Scope note (per the ratified
"their proofs transfer" gauge): §1.3–§1.4 are **typing-scoped** —
what `theories/typing/` consumes; the acceptance-ladder obligation
set is a superset, because the generated example proofs import
caesium surface typing/ never touches (e.g. `From caesium Require
Import builtins_specs` in `generated_proof_wrapping_add.v`, with
`Z_least_significant_one` in the spec text of its
`generated_spec.v`; typing/*.v references `builtins_specs` zero
times). Grouped list, `name:line` within each file (derived per the
method note):

- **bitfield.v**: `bf_cons:9` `bf_nil:7` `bf_cons_bool_singleton_false_iff:45` `bf_cons_bool_singleton_true_iff:53` `normalize_bitfield:289`
- **byte.v**: `bits_per_byte:5` `byte0:16`
- **ghost_state.v**: `heapUR:19` `to_heapUR:39` `to_alloc_meta_map:45` `to_alloc_alive_map:48` `loc_in_bounds:80` `alloc_alive:95` `alloc_global:107` `fntbl_entry:124` `fntbl_entry_eq:125` `heap_mapsto_def:147` `heap_mapsto_eq:152` `alloc_alive_loc:161` `alloc_meta_ctx:180` `alloc_alive_ctx:183` `heap_state_ctx:189` `state_ctx:195` `loc_in_bounds_split:358` `loc_in_bounds_split_mul_S:373` `loc_in_bounds_shorten:380` `loc_in_bounds_offset:387` `loc_in_bounds_ptr_in_range:410` `loc_in_bounds_has_alloc_id:427` `heap_mapsto_loc_in_bounds:466` `heap_mapsto_loc_in_bounds_0:476` `heap_mapsto_nil:484` `heap_mapsto_cons:498` `heap_mapsto_app:506` `alloc_alive_loc_mono:807` `heap_mapsto_alive_strong:812` `heap_mapsto_alive:819` `alloc_global_alive:828` `heap_alloc_new_blocks_upd:878`
- **heap.v**: `heap:17` `alloc_kind:188` `min_alloc_start:213` `max_alloc_end:217` `heap_loc_eq:303` `heap_loc_eq_symmetric:330` `heap_loc_eq_NULL_NULL:337` `mem_cast:383` `mem_cast_id:415` `mem_cast_length:418` `mem_cast_id_loc:440` `mem_cast_id_int:444` `mem_cast_id_bool:449` `mem_cast_struct_reshape:454` `alloc_new_blocks:510`
- **int_type.v**: `int_type:7` `bytes_per_int:16` `bits_per_int:19` `int_modulus:22` `int_half_modulus:25` `min_int:29` `max_int:33` `it_layout:43` `u8:47` `i32:50` `bytes_per_addr:61` `size_t:66` `bytes_per_int_gt_0:78` `bits_per_int_gt_0:85`
- **lang.v**: `label:9` `bin_op:12` `un_op:21` `order:23` `expr:28` `stmt:74` `function:90` `state:99` `runtime_expr:117` `coerce_rtexpr:163` `subst:196` `subst_stmt:219` `eval_bin_op:240`
- **layout.v**: `layout:5` `ly_align:12` `ly_offset:36` `ly_set_size:44` `layout_wf:71` `void_layout:97` `mk_array_layout:99`
- **lifting.v**: `refinedcG:9` `wp_binop_det:162` `wp_binop_det_pure:174` `wp_unop_det_pure:212` `wp_deref:222` `wp_cas_fail:275` `wp_cas_suc:306` `wp_neg_int:337` `wp_cast_int:349` `wp_cast_loc:361` `wp_cast_bool_int:372` `wp_cast_ptr_int:384` `wp_cast_null_int:405` `wp_cast_int_ptr_weak:420` `wp_cast_int_ptr_alive:436` `wp_cast_int_null:457` `wp_cast_int_bool:473` `wp_copy_alloc_id:520` `int_arithop_result:540` `int_arithop_sidecond:555` `wp_int_arithop:632` `wp_ptr_relop:656` `wp_ptr_offset:697` `wp_ptr_neg_offset:716` `wp_ptr_diff:735` `wp_get_member:767` `wp_get_member_union:785` `wp_offset_of:798` `wp_if_int:817` `wp_if_bool:830` `wp_if_precond:842` `wp_if_precond_null:845` `wp_if_precond_alloc:849` `wp_if_precond_heap_loc_eq:857` `wp_if_ptr:869` `wp_skip:884` `wp_struct_init:932` `wp_call_bind:966` `wps_wand:1038` `wp_call:1046` `wps_return:1108` `wps_goto:1112` `wps_skip:1140` `wps_exprs:1152` `wps_annot:1164` `wps_assign:1171` `wps_switch:1209` `wps_if:1237` `wps_if_bool:1249` `wps_if_ptr:1261` `wps_assert_bool:1275` `wps_assert_int:1285` `wps_assert_ptr:1295` `wps_block:1306` `wps_block_rec:1309`
- **loc.v**: `addr:13` `alloc_id:16` `loc:49` `fn_loc:52` `NULL_loc:53` `offset_loc:63` `aligned_to:69` `has_layout_loc:75` `shift_loc_assoc:82` `shift_loc_0:85` `shift_loc_assoc_nat:88` `shift_loc_S:94` `offset_loc_0:108` `offset_loc_S:111` `offset_loc_1:114` `offset_loc_sz1:117` `offset_loc_offset_loc:120` `has_layout_loc_trans:134` `has_layout_loc_trans':143` `has_layout_ly_offset:159` `has_layout_loc_ly_mult_offset:169` `has_layout_loc_offset_loc:175`
- **notation.v** (derived expression/statement forms): `LogicalAnd:69` `LogicalOr:76` `Assert:83` `Use:89` `AddrOf:96` `LValue:102` `AnnotExpr:106` `AnnotStmt:109` `location_info:115` `LocInfo:118` `MacroE:125` `annot_expr_S_r:155` `StructInit:166` `GetMember:173` `OffsetOf:179` `GetMemberUnion:184`
- **proofmode.v**: `tac_wps_bind:9`
- **struct.v**: `var_name:6` `field_list:8` `field_members:10` `field_names:12` `offset_of_idx:13` `offset_of:17` `field_idx_of_idx:19` `field_index_of:21` `pad_struct:27` `struct_layout:38` `layout_of:45` `struct_layout_eq:52` `field_members_length:57` `field_members_idx_lookup:60` `field_idx_of_idx_bound:64` `field_index_of_leq:73` `field_index_of_to_index_of:81` `pad_struct_length:90` `pad_struct_lookup_Some:93` `pad_struct_lookup_field:103` `pad_struct_insert_field:115` `pad_struct_snoc_Some:127` `pad_struct_snoc_None:137` `offset_of_cons:145` `offset_of_from_in:154` `check_fields_aligned_alt_correct:182` `GetMemberLoc:196` `union_layout:203` `ul_layout:209` `index_of_union:215` `layout_of_union_member:218` `layout_of_union_member_in_ul:226` `index_of_union_lookup:234` `GetMemberUnionLoc:245` `op_type:251` `ot_layout:258`
- **tactics.v** (module `W`): `expr:9` `to_expr:90` `ectx_item:197` `stmt:378` `to_stmt:419` `subst_stmt:650` `to_stmt_subst:667`
- **val.v**: `mbyte:7` `val:26` `VOID:30` `has_layout_val:34` `val_of_loc:44` `val_to_loc:62` `NULL:65` `val_to_of_loc:83` `val_of_to_loc:97` `val_to_Z:137` `val_to_byte_prov:146` `val_of_Z:165` `i2v:172` `val_to_Z_length:206` `val_of_Z_is_Some:210` `val_to_Z_in_range:233` `val_to_of_Z:253` `val_of_Z_to_prov:290` `val_of_Z_bool_is_Some:318` `val_of_Z_bool:322` `val_of_bool:326` `val_to_bool:330` `val_to_bool_iff_val_to_Z:347` `i2v_bool_Some:363` `val_to_Z_ot_to_Z:383`

Reading of the list (derived): the interface has five strata —
(i) **pure data theory** (loc/layout/int_type/struct/val/bitfield
arithmetic — by far the widest, portable as ordinary Lean defs+lemmas;
must be re-derived against Cerberus's actual layouts/values);
(ii) **assertions** (`↦`, `loc_in_bounds`, `alloc_alive(_loc)`,
`alloc_global`, `fntbl_entry`, `freeable` — the attachment layer's RA
obligations); (iii) **the WP lemma library** (~55 `wp_*`/`wps_*`
lemmas — one per language construct/case; this is the exact set of
"lifting lemmas" the attachment layer must prove over Core's opsem);
(iv) **structural WP artifacts** (`Wp` instance, `stmt_wp`, `wps_block(_rec)`,
`wp_call_bind`/`wp_struct_init` n-ary binds, `tac_wps_bind`,
module `W` for reflective bind); (v) **adequacy plumbing**
(`state_ctx`, `to_heapUR`, `alloc_new_blocks`,
`heap_alloc_new_blocks_upd`, `typePreG` — used only by
`typing/adequacy.v`).

#### 1.3.1 Record projections consumed by typing/

The name scan catches record *names* (`layout:5`, `int_type:7`,
`function:90`, `state:99`) but not their fields, which typing/ uses
pervasively in the very statements of its judgments. Mechanical sweep
at this revision (all field names of caesium `Record`/`Class`
declarations, `grep -lw` against `typing/*.v`; counts = typing files,
derived):

- `ly_size` (layout.v:5) — **10** typing files; `sl_members`
  (struct.v:38) — 4; `f_args`/`f_local_vars` (lang.v:90) — 3 each;
  `it_signed` (int_type.v:7), `f_init`, `st_heap` — 2 each;
  `f_code`, `st_fntbl`, `ul_members` (struct.v:203), `sl_nodup`
  (struct.v:38) — 1 each; `hs_heap`/`hs_allocs` (heap.v:229) — 1
  each (adequacy.v).
- Class projections (the `heapG`/`refinedcG` fields,
  `caesium_config_enforce_alignment`) have zero direct word-token
  hits in typing/ — they are consumed via TC resolution only
  (§1.3.3).

An attachment layer built to the 247-name list alone would lack the
projections the typing layer's statements are written in.

#### 1.3.2 Data constructors beyond §1.4's expr/stmt list

- `MByte` (used in typing/bytes.v), `ProvAlloc` (typing/intptr.v),
  `ProvFnPtr` (typing/adequacy.v) — each used in exactly one typing
  file (`grep -lw`), none covered by §1.3 or §1.4.
- `typing/programs.v` itself (not just the automation)
  pattern-matches **W-module constructors**: `find_place_ctx`
  (programs.v:257) is a `Fixpoint` over `W.expr` matching `W.Loc`,
  `W.Deref`, `W.GetMember`, `W.GetMemberUnion`, `W.AnnotExpr`,
  `W.LocInfoE`, `W.BinOp`, `W.UnOp`, `W.LValue`
  (programs.v:257-276) — where the tactics.v row above lists only
  `expr/to_expr/ectx_item/stmt/to_stmt/subst_stmt/to_stmt_subst`.

#### 1.3.3 Silently-resolved typeclass instances

Typing proofs depend on caesium instances that never appear as word
tokens in typing/:

- `Atomic` instances (lifting.v:39-50: `cas_atomic`, `skipe_atomic`,
  `deref_atomic`, `use_atomic`) — consumed at programs.v:1389
  (`iApply wp_atomic`) via TC resolution; the word "Atomic" occurs
  **zero** times in typing/*.v.
- `Persistent`/`Timeless` instances on the assertion layer
  (ghost_state.v:65-131) and `Fractional`/`AsFractional`/`Timeless`
  on `↦` (ghost_state.v:440-463) — required for
  `iDestruct`/persistence/`iMod` moves to typecheck; typing/type.v's
  fraction machinery names `Fractional` (4 word hits) but the
  instances are caesium's.
- `EqDecision`/`Countable`/`Inhabited` instances on caesium data
  (loc.v:24-27, val.v:12, lang.v:724-732) — consumed silently by
  every gmap, `bool_decide`, and `inhabitant` use over those types.

These are attachment-layer proof obligations as real as the ~55 wp
lemmas, and they are invisible to the name-scan method.

#### 1.3.4 Ltac- and hint-database-level consumption

- `W.of_expr`/`W.of_stmt` (Ltac reflection) — used at
  typing/automation.v:159,226; Ltac, so no declaration-name hit.
- The `bitfield_rewrite` rewrite HintDb (caesium/bitfield.v:260-282),
  fed to Lithium's `normalize_hook` = `autorewrite` path.
- The `LiEntails` Hint Extern for `normalize_bitfield` registered
  **in caesium** (bitfield.v:300) but fired during typing's
  automation; likewise the `NormalizeBitfield` extern
  (bitfield.v:316).
- `CanSolve`-guarded `SimplAnd`/`SimplBoth` instances
  (bitfield.v:328-357) and the `CaesiumConfigEnforceAlignment` Hint
  Extern (config/config.v:25-26).

The projection/constructor strata (§1.3.1–§1.3.2) are mechanical to
re-sweep; the instance/Ltac strata (§1.3.3–§1.3.4) need a targeted
pass when the ledger rows are drawn.

### 1.4 Interface consumed via notation/constructors (not caught by the name scan)

- Expression constructors used in typing judgments/rules: `Val`,
  `UnOp`, `BinOp`, `CopyAllocId`, `Deref`, `CAS`, `Call`, `Concat`,
  `IfE`, `SkipE`, `Alloc` (lang.v:28-42); statement constructors
  `Goto`, `Return`, `IfS`, `Switch`, `Assign`, `Free`, `SkipS`,
  `ExprS` (lang.v:74-86); `op_type` constructors (struct.v:251);
  `order` constructors `ScOrd/Na1Ord/Na2Ord` (lang.v:23).
- Notations: `l ↦{q} v` / `l ↦ v` / `l ↦: P` / `l ↦{q}\|ly\|`
  (ghost_state.v:204-216); `WP e {{ Φ }}` (Iris `Wp` class via
  lifting.v:26); `WPs s {{ Q, Ψ }}` (lifting.v:1010-1016);
  `v \`has_layout_val\` ly`, `l \`has_layout_loc\` ly`,
  `l \`aligned_to\` n`, `l +ₗ n`; sugar `!{ot,o,mc} e`, `e at{sl} m`,
  `e at_union{ul} m`, `e {o, ot} := e'` etc. (notation.v).
- Imports: `typing/base.v:2`, `typing/type.v:4`,
  `typing/programs.v:3` import only `caesium/proofmode` (+`notation`,
  `bitfield`); everything else arrives through caesium's export
  chain (proofmode → tactics + lifting → ghost_state/lang/heap/...).
  `typing/adequacy.v:4` additionally imports `ghost_state` directly.

---

## 2. Typing-rule inventory

### 2.1 File-by-file (I = infrastructure, T = type-former library)

| File (lines) | Kind | Provides |
|---|---|---|
| `base.v` (9) | I | re-exports lithium+caesium proofmode; `CoPsetFact` mask solver hook |
| `type.v` (707) | I | **the `type` record** (type.v:249-297: `ty_own : own_state → loc → iProp`, `ty_own_val : val → iProp`, `ty_has_op_type`, sharing/alignment/size/deref/ref/memcast axioms), `own_state := Own \| Shr` (:122), `l ◁ₗ{β} ty` / `v ◁ᵥ ty` notations (:437-439), `heap_mapsto_own_state` `l ↦[β] v` (:129), refinement types `rtype`/`x @ r`/`ty_of_rty` (:464-506), `Copyable` (:367), `LocInBounds` (:377), `AllocAlive` (:399), type ⊑/≡ + `solve_type_proper` (:537-698) |
| `programs.v` (1621) | I | **all program judgments** (§2.2) + generic structural rules and the judgment→typeclass hook (:622-645); `FindLoc/FindVal/FindValP/FindValOrLoc/FindLocInBounds/FindAllocAlive` contexts (:607-618) with their `FindInContext` instances; generic subsumption rules (loc_in_bounds/alloc_alive :747-815); statement rules `type_goto/assign/if/switch/assert/exprs/skips` (:1082-1195), `typed_block_rec` (:1200); expression rules `type_val/bin_op/un_op/call_syn/ife/logical_and/or/skipe/annot/use/read/write/addr_of_place` (:1224-1525); read/write dispatch `type_read_copy`, `type_write_own_copy/move` (:1418-1505) |
| `function.v` (420) | I | `introduce_typed_stmt` (:5), `fn_ret`/`fn_params` records (:29,42), `typed_function fn fp` (:59), `function_ptr` type former (:106-121), `type_call_fnptr` (:131) — the call rule against an `A → fn_params` spec |
| `adequacy.v` (127) | I | `typePreG`/`typeΣ` (:10-25), `refinedc_adequacy` (:40) — see §5 |
| `automation.v` (368) + `automation/` (525) | I | RefinedC's Lithium instantiation: hook overrides, `liRStep` driver, `split_blocks`/`start_function`; loc-eq solver, RefinedC simplification instances, proof-state markers (§3.6) |
| `annotations.v` (27) | I | annotation payload types (`to_uninit_annot`, `stop_annot`, `share_annot`, `learn_annot`, `LockAnnot`, `reduce_annot`, …) consumed by `typed_annot_expr/stmt` rules |
| `type_options.v` (14) | I | `Typeclasses Opaque` bundle for type definitions |
| `naive_simpl.v` (338) | I | an alternative "naive" simplification engine (marked TODO/clean-up) |
| `axioms.v` (11) | I | **`Axiom eq_rect_eq`** — UIP, used by fixpoint machinery (trust note: RefinedC's own Coq development is not axiom-free) |
| `int.v` (470) | T | `int it` rtype over Z (:10-25), `offsetof` type (:407); constants, arith/relational/cast rules (31 `[instance]`s incl. `type_relop_int_int` :98, arith ops, if/switch/assert on ints) |
| `boolean.v` (276) | T | `generic_boolean`/`builtin_boolean` over bool with strictness (:52-81) |
| `own.v` (713) | T | `frac_ptr β ty` (`&own`/`&shr`/`&frac{β}` :11-34,364-366), `ptr n` (:375-390), `null` (:451), place/deref/write rules for pointers (39 instances) |
| `singleton.v` (258) | T | `value ot v` (exact-value type :8), `at_value`, `place l` (:172) |
| `bytes.v` (288) | T | `bytewise P ly` (:12), `uninit := bytewise (λ_,True)` (:175), `void` (:258) |
| `struct.v` (471) | T | `struct sl tys` (:54) + `padded` interplay, field place rules |
| `padded.v` (231) | T | `padded ty lyty ly` (:8) |
| `array.v` (1012) | T | `array ly tys` (:9), `array_ptr` (:138), `sized_array` (:158), index place rules |
| `union.v` (265) | T | `active_union` (:9), tagged `tunion`/`variant` via `tunion_info` (:56-225) |
| `optional.v` (476) | T | `Optionable` class (:9), `optional ty optty` (:44-83), `optionalO` with option-refinement (:269-299) — the null-or-value idiom |
| `constrained.v` (174) | T | `own_constrained P ty` (:14) + `OwnConstraint` (:5), persistent/nonshr constraints |
| `exist.v` (111) | T | `tyexists` — existential refinement type (:18-30) |
| `wand.v` (136) | T | `wand_ex`/`wand_val_ex` — magic-wand types (:11,66) |
| `intptr.v` (190) | T | `intptr it` — integer-with-provenance (:8-29) |
| `tagged_ptr.v` (~100) | T | `tagged_ptr β align ty` — low-bit tagging (:8-43) |
| `atomic_bool.v` (198) | T | `atomic_bool it PT PF` — invariant-backed bool (:9) |
| `locked.v` (192) | T | `tylocked_ex` + `lock_token`/`lockG` (:10-92) — lock ownership |
| `malloc.v` (~120) | T | `malloced` block type + `mallocG` (:6-41) |
| `immovable.v` (~40) | T | `immovable (ty : loc → type)` (:8) |
| `globals.v` (~110) | T/I | `global_type`, `globalG` (locs map), `initialized` (:7-34) |
| `fixpoint.v` (~110) | I | `type_fixpoint` — guarded fixpoint of `(A→type)→(A→type)` (:6-9), the recursion vehicle for linked structures |
| `tyfold.v` (~80) | T | `tyfold` — list-of-type-functions fold (:8-26) |
| `bitfield.v` (307) | T | `bitfield_raw it`, `bitfield R` via `BitfieldDesc` (:10-80) |

### 2.2 The judgment forms (the port ledger's row list)

Semantic base (in `type.v`): `l ◁ₗ{β} ty := ty_own ty β l`,
`v ◁ᵥ ty := ty_own_val ty v` (type.v:437-439).

All program judgments live in `programs.v` §`judgements`
(programs.v:7-330). Each `Definition` has a companion typeclass whose
single method is an `iProp_to_Prop` record (the Lithium rule hook,
§3.4); the `Definition→Class` map is registered at
programs.v:622-645. Signatures (Σ/typeG implicit):

Expressions:
- `typed_val_expr (e : expr) (T : val → type → iProp) := ∀ Φ, (∀ v ty, v ◁ᵥ ty -∗ T v ty -∗ Φ v) -∗ WP e {{Φ}}` — programs.v:96
- `typed_value (v : val) (T : type → iProp)` — :100 (class `TypedValue` :102)
- `typed_bin_op v1 P1 v2 P2 o ot1 ot2 T := P1 -∗ P2 -∗ typed_val_expr (BinOp ...) T` — :105 (`TypedBinOp` :108)
- `typed_un_op v P o ot T` — :111 (`TypedUnOp`)
- `typed_call v P vl tys T := P -∗ ([∗list] v;ty∈vl;tys, v◁ᵥty) -∗ typed_val_expr (Call v (Val<$>vl)) T` — :117 (`TypedCall`)
- `typed_copy_alloc_id v1 P1 v2 P2 ot T` — :122 (`TypedCopyAllocId`)
- `typed_cas ot v1 P1 v2 P2 v3 P3 T` — :128 (`TypedCas`)
- `typed_macro_expr m es T` — :136 (`TypedMacroExpr`)
- `typed_annot_expr n a v P T := P ={⊤}[∅]▷=∗^n |={⊤}=> T` — :41 (`TypedAnnotExpr`)
- `typed_if ot v P T1 T2` — :51 (case on `BoolOp`/`IntOp`/`PtrOp`; `TypedIf` :62)

Statements (all carry `fn ls R Q` — the enclosing function, its
arg+local locations, return postcondition `R : val → type → iProp`,
and the label map `Q : gmap label stmt`):
- `typed_stmt s fn ls R Q := ⌜length ls = ...⌝ -∗ WPs s {{Q, typed_stmt_post_cond fn ls R}}` — :68 (post_cond :66 returns the locals' points-to)
- `typed_block P b fn ls R Q := wps_block P b Q (...)` — :72
- `typed_switch v ty it m ss def fn ls R Q` — :75 (`TypedSwitch` :81)
- `typed_assert ot v P s fn ls R Q` — :84 (`TypedAssert` :92)
- `typed_annot_stmt a l P T` — :46 (`TypedAnnotStmt` :48)

Places (l-values):
- `place_ectx_item` (:204-213: `DerefPCtx`, `GetMemberPCtx`, `GetMemberUnionPCtx`, `AnnotExprPCtx`, `BinOpPCtx`, `UnOpPCtx`) with `place_to_wp` (:227) — a place-only evaluation-context stack, and `find_place_ctx`/`IntoPlaceCtx` (:257-285) reflecting a syntactic expr into it
- `typed_place (P : list place_ectx_item) l1 β1 ty1 (T : loc → own_state → type → (type→type) → (type→iProp) → iProp)` — :324 (`TypedPlace` :327): walk the place context to the target location, returning the target's type, a type-transformer `typ` for the root after write-back, and a closing viewshift
- `typed_write (atomic) e ot v ty T` — :146; `typed_read (atomic) e ot memcast T` — :157; `typed_addr_of e T` — :165 (front-ends: evaluate `e`, dispatch to the `_end` forms)
- `typed_read_end atomic E l β ty ot memcast (T : val → type → type → iProp)` — :174 (`TypedReadEnd` :180)
- `typed_write_end atomic E ot v1 ty1 l2 β2 ty2 (T : type → iProp)` — :186 (`TypedWriteEnd` :189)
- `typed_addr_of_end l β ty (T : own_state → type → type → iProp)` — :194 (`TypedAddrOfEnd` :196)
- `copy_as l β ty T` — :35 (`CopyAs` :37)

Functions:
- `typed_function fn (fp : A → fn_params)` — function.v:59: ∀ spec
  parameter `x`, given arg/local locations with `fp_atys`-typed args +
  `uninit` locals + precondition `fp_Pa`, the body typechecks against
  `fn_ret_prop` (∃-quantified return type + postcondition,
  function.v:54); `fn_params = {fp_atys; fp_Pa; fp_rtype; fp_fr}`
  (:42-52); `introduce_typed_stmt` substitutes locations into the
  code map and enters via `Goto f_init` (:5-8)
- `function_ptr fp` type former (:106-121) ties `fntbl_entry` + `▷ typed_function`; `type_call_fnptr` (:131) is the call-site rule

Auxiliary classes (rule-shaping, in programs.v/type.v):
`Learnable` (:10), `LearnAlignment` (:15), `SimpleSubsumePlace`/
`SimpleSubsumeVal` (:22-28), `TypedIf`-style trace-info variants in
type-former files, `Copyable`/`LocInBounds`/`AllocAlive` (type.v).

Lithium-level judgments consumed by all of the above (in
`lithium/definitions.v`): `subsume P1 M P2 T := P1 -∗ ‖M‖ ∃ x, P2 x ∗ T x`
(:220, class `Subsume` :222), `simplify_hyp P M T := P -∗ ‖M‖ T`
(:206), `simplify_goal M P T := ‖M‖ P ∗ T` (:211),
`find_in_context fic T := ∃ b, fic_Prop b ∗ T b` (:164).

Count for the ledger: **23 program judgments** (programs.v) + 2
semantic-base judgments (`◁ₗ`, `◁ᵥ`) + `typed_function` + 4
Lithium meta-judgments; **~30 type formers** (§2.1 T-rows); several
hundred `[instance]` rules across the T-files (e.g. own.v 39, int.v
31, array.v 32 — derived counts from `[instance]` grep). The row
list additionally carries the registered `li_tactic`-class
**operations** — each a rule-shaped extension point needing a ported
counterpart: `li_vm_compute` (lithium/definitions.v:311-325),
`normalize_bitfield` (caesium/bitfield.v:294-300),
`compute_map_lookup` (lithium/solvers.v:140; driven by the `Goto`
step via `unfold_code_marker_and_compute_map_lookup`,
typing/automation/proof_state.v:28-29), and the loc-eq solver ops
(`solve_loc_eq` plus the `FICLocSemantic` `FindHypEqual` Hint Extern
and semantic `FindInContext` instances,
typing/automation/loc_eq.v:46-70).

---

## 3. Lithium algorithm note

Everything below re-verified against `theories/lithium/` at this
checkout. Note this Lithium is **newer than the RefinedC paper** (and
newer than the predecessor review's checkout in some internals): goals
now carry a first-class modality (`limodal`, `‖M‖ P`), and `li_tactic`
dispatch runs through a `LiEntails` hint database. The prior review's
architectural picture still matches. **[prior review, re-verified]**
markers below indicate readings that originated there.

### 3.1 Goal grammar

A Lithium goal is an Iris proposition in continuation-passing style:
every connective carries the rest of the proof as an explicit
continuation. The grammar is thin definitional wrappers over Iris
connectives, module `li` (`syntax.v:6-70`):

- `exhale P T := P ∗ T` (:11) — prove/consume P, continue T
- `inhale P T := P -∗ T` (:14) — assume P
- `all`/`exist` := `bi_forall`/`bi_exist` (:17-19)
- `done := True`, `false := False` (:22-23)
- `and`, `and_map` (big ∧ over a gmap) (:25-29)
- `find_in_context fic T` (:31, from definitions.v:164)
- `case_if P T1 T2 := (⌜P⌝ -∗ T1) ∧ (⌜¬P⌝ -∗ T2)`; `case_destruct a T := ∃ b, T a b` (:34-37, definitions.v:227-231)
- `drop_spatial := □` (:39)
- `tactic` (= `li_tactic`, arbitrary registered goal transformer, definitions.v:305)
- `accu f := ∃ P, P ∗ □ f P` (capture the spatial context, definitions.v:328)
- `trace` (info marker), `modal M P := ‖M‖ P` (first-class modality with wand/intro/bind laws, definitions.v:10-23)
- `subsume` (definitions.v:220), `ret`, `iterate` (foldr — the loop form), `bind0..bind5` (:59-68)

Custom notation (`[{ ... }]`, `inhale x; ...`) makes rules readable;
the wrappers are definitionally transparent and the interpreter
dispatches on the underlying Iris term shapes (`liFromSyntax`/
`liToSyntax`, syntax.v:205-268). Goals are always of the form
`envs_entails Δ (‖M‖ G)` — the Iris proof-mode entailment under the
current modality.

### 3.2 Interpreter main loop and committed-choice discipline

The engine is one step tactic `liStep` (`interpreter.v:1177-1201`): a
`first [...]` over ~19 sub-tactics — `liTactic | liExtensible | liSep
| liAnd | liWand | liExist | liImpl | liForall | liSideCond |
liFindInContext | liCase | liTrace | liPersistent | liTrue | liFalse
| liModal | liAccu | liDoneEvar | liUnfoldLetGoal` — each guarded by
a `lazymatch goal` on the head connective. The driver is `repeat`
(RefinedC's `liRStep`, typing/automation.v:257-268, whose full shape
is `liEnsureInvariant; try liRIntroduceLetInGoal; first [...];
liSimpl` — mandatory invariant maintenance *before* every step and
simplification *after* it, with its own statement/expression dispatch
at the head of the `first`: `liRPopLocationInfo | liRStmt |
liRIntroduceTypedStmt | liRExpr | liRJudgement | liStep`; the donor's
own Lithium tutorial calls `liEnsureInvariant` explicitly before
single-stepping, tutorial/proofs/lithium/lithium_tutorial.v:30).

Step *selection* is structurally deterministic: the grammar's head
connectives are syntactically disjoint, so at most one guard fires;
each sub-tactic applies exactly one lemma
(`notypeclasses refine (tac_...)`) and continues. No backtracking
across steps. But the walk is **not solver-free**: several
sub-tactics invoke the registered solver/hook surface mid-walk
(§3.3), so step *outcomes* — which branches survive, which
existentials get instantiated — co-vary with that surface. The three
disciplined choice points **[prior review, re-verified]**:

1. **Rule choice** (`liExtensible`, interpreter.v:195-211): the goal's
   judgment is converted to a typeclass query (`_ : TypedBinOp ...`).
   `liExtensible_to_i2p` handles `subsume` **natively** before
   consulting the hook (built-in case, interpreter.v:195-200);
   everything else dispatches
   via `liExtensible_to_i2p_hook` (RefinedC's 16-case lazymatch,
   typing/automation.v:49-87), resolved by `solve [typeclasses eauto]`
   and applied through `tac_apply_i2p` (interpreter.v:187-192). TC
   resolution may backtrack internally, but the chosen rule is
   **committed** — a wrong choice is unrecoverable by design; the
   GUIDE's matching-rules discipline (GUIDE.md:6-16) exists to make
   wrong choices non-losing.
2. **Context search** (`liFindInContext`, interpreter.v:577-592):
   `FindInContext` instances tried in priority order by exploiting
   multi-success `typeclasses eauto`, wrapped in `once (...)` — the
   first instance whose **entire continuation** succeeds is
   committed. The continuation is `simpl; repeat liExist false;
   liFindHypOrTrue key` (:589-591) — i.e. it opens existentials
   *inside* the search — and `liFindHypOrTrue` (:571-575) tries
   `tac_sep_true` *before* the hypothesis scan (`liFindHyp`, a
   linear scan of the proof-mode environment unifying hypothesis vs
   pattern, :537-570): "prove it from True/emp" beats "find it in
   context". Both outcomes are trace-visible as
   `tac_find_hyp`/`tac_find_in_context` proof-term nodes (§3.8).
3. **Case splits** (`liCase`, interpreter.v:1101-1120): `case_if`/
   `case_destruct` produce both branches, then immediately prune with
   `repeat (liForall || liImpl); try by [exfalso; can_solve]` (an
   in-code comment marks the pruning as performance-critical) — note
   `can_solve` here is the *full registered solver* (§3.3): branch
   pruning is an in-walk solver call.

Stuck goals just survive (`repeat` stops); `liShow`
(interpreter.v:11) re-sugars them for the user — stop-with-goal
semantics, no failure state.

### 3.3 Side conditions and solvers (the in-walk solver surface)

The walk is **not** solver-free; drawing this boundary correctly is
load-bearing for the replay lane (§3.8). Three solver/heuristic
surfaces fire mid-walk:

- **`liCase` pruning runs the full solver mid-walk.** The pruning of
  §3.2(3) ends in `try by [exfalso; can_solve]`
  (interpreter.v:1120), and RefinedC sets `can_solve_hook ::=
  solve_goal` (typing/automation.v:45) — i.e. the complete
  `normalize_and_simpl_goal`/`refined_solver lia` pipeline
  (solvers.v:235-242) executes **during** the walk, and whether a
  branch exists in the residual proof depends on its strength.
- **`liSideCond` does more than `done` in-walk**
  (interpreter.v:458-478): the plain pure-conjunct case tries `done`
  then wraps the goal as `SHELVED_SIDECOND` and shelves it
  (`shelve_sidecond`, proof_state.v:8-24); but under the `∃ₗ`
  telescope it runs `normalize_hook` for progress, `liExInst`
  (unification), and `tac_simpl_and_unsafe_envs` via `SimplAndUnsafe`
  TC search — including *provability-losing* simplification,
  in-walk.
- **`li_tactic`/`LiEntails` goals run arbitrary registered Ltac
  mid-walk** (e.g. `li_vm_compute` — definitions.v:311-325;
  `normalize_bitfield` — bitfield.v:300; `compute_map_lookup` in the
  `Goto` path — typing/automation.v:170-176 +
  automation/proof_state.v:25-29), with results flowing into
  subsequent goals.

Consequence: the residual goal set is a function of the walk *and*
the in-walk solver/hook surface, not of the grammar walk alone; §3.8
gives the well-defined replacement notion of "same residual side
conditions".

After the walk, `unshelve_sidecond` restores the shelved batch and
`solve_goal` attacks it (solvers.v; pipeline:
`normalize_and_simpl_goal` — rewrite normalization via `normalize_hook`
= `autorewrite` (normalize.v:27-58) or the typeclass normalizer
(normalize.v:60-128), plus `SimplAndImpl`/`SimplAnd` typeclass
simplification (simpl_classes.v) — then `enrich_context`
(trigger-style saturation, solvers.v:153-186), then
`refined_solver lia` (a fail-fast `naive_solver` variant,
solvers.v:8-62)). Everything is behind 16 named Ltac hooks
(hooks.v:1-68: `can_solve_hook`, `normalize_hook`,
`enrich_context_hook`, `generate_i2p_instance_to_tc_hook`,
`liExtensible_to_i2p_hook`, `liTrace_hook`, …) that RefinedC overrides
in typing/automation.v (`::=` at :18,45,47,49).

Simplification is a two-class system: `SimplifyHyp P M (n : option N)`
/ `SimplifyGoal M P n` (definitions.v:206-217) with priority `Some 0`
= always-safe/eager; `Subsume` composes with simplification
generically. Unsafe (provability-losing) simplifications are a marked
category (`SimplAndUnsafe`, simpl_classes.v).

### 3.4 Rule registration

A rule is a lemma `grammar-term ⊢ J a₁…aₙ T`. `iProp_to_Prop P`
(definitions.v:146-152) packages `i2p_P : iProp` with a proof
`i2p_P ⊢ P`; per-judgment classes have one method of this type. The
`[instance lemma]` notation (proof_state.v:121-137, generator
:26-119) reflects the lemma's ∀-telescope into an instance of the
right class (target class inferred by
`generate_i2p_instance_to_tc_hook` — RefinedC's mapping at
programs.v:622-645). Priorities are ordinary TC priorities
(`Global Existing Instance foo_inst | 40`). Indexing is Coq's hint
mechanism disciplined by `Hint Mode` on every class
(definitions.v:169,182,188,216-217,224) + pervasive
`Typeclasses Opaque` — i.e. the "law table" is the typeclass instance
database with syntactic matching. **[prior review, re-verified]**

Escape hatch: `li_tactic t T` goals dispatch through the `LiEntails`
hint database (definitions.v:233-262) — one `Hint Extern` per
registered goal transformer, e.g. `li_vm_compute f x T` actually runs
`vm_compute` and continues with the result (definitions.v:311-325).

### 3.5 Existential/evar discipline

`liExist` (interpreter.v:303-401) does not create naked evars: pending
existentials are packed into a protected linear telescope `∃ₗ x`
(`li_prod`, pure_definitions.v) and instantiated only at pure
equations — `liSideCond` on `∃ₗ x, ⌜P x⌝ ∗ …` calls `liExInst`
(interpreter.v:106-158), which solves a controlled unification
(`solve_protected_eq`, client-hookable, typing/automation.v:25-40) and
re-quantifies undetermined components. `SimplExist` instances let
types provide instantiation shapes; named logical variables via
`lvar.v`. Evar sharing across `and` branches via `li_done_evar`
(interpreter.v:595-627). Hypothesis cancellation in `liSep` refuses to
fire when the goal side contains an evar. **[prior review,
re-verified at the definition sites; internals spot-checked]**

### 3.6 Performance discipline (relevant to the Lean port's shape)

- The proof-mode environment is let-bound (`let_bind_envs`,
  proof_state.v:158-187) so the context appears once as a variable;
  lookups via a dedicated cbv (`li_pm_reduce`).
- Judgment continuations are let-bound (`LET_ID`,
  proof_state.v:204-231; `liRIntroduceLetInGoal`,
  typing/automation.v:130-143) and unfolded only on arrival
  (`liUnfoldLetGoal`). RefinedC wraps the code map and return
  continuation in markers (`CODE_MARKER`/`RETURN_MARKER`,
  automation/proof_state.v) — `simpl` over the code map is called out
  in-source as exponential in block count.
- Closed computation goes to `vm_compute` (`li_vm_compute`,
  `reduce_closed_Z_hook`) — and NOT only in the solver layer: it
  sits in the **rule grammar** itself. `li_tactic (li_vm_compute …)`
  occurs inside registered typing rules (`annot_reduce_int`,
  int.v:386, carries it in the rule's continuation), and the `Goto`
  step runs `compute_map_lookup` over the CODE_MARKER-wrapped label
  map (typing/automation.v:170-176, automation/proof_state.v:25-29).
  **Port note:** in-Coq `vm_compute` is inside their TCB; the house
  ban therefore requires a kernel-legal computation story at the
  *rule/interpreter* level, not merely a solver swap — a known
  deviation to record in the ledger and priced accordingly (bin:
  real constraint, ours is a trust-policy constraint, not a
  Cerberus-semantics constraint — flag for operator).
- Proof terms are chains of `tac_*` nodes of which `tac_apply_i2p`
  marks the rule applications, with rules as named `*_inst`
  constants (probe evidence and exact tallies: §3.8).

### 3.7 Scoping a Lean reimplementation (facts only, no design)

What a port must provide, mechanically: (i) the goal-grammar
wrappers (trivial defs over iris-lean's BI); (ii) a step function
dispatching on head symbol of the goal under `envs_entails`-analog —
in Lean this is a MetaM tactic loop; (iii) an extensible
rule-registration mechanism keyed by judgment head — an open choice
for the attachment conversation, to be argued from the donor's actual
requirements (Hint-Mode-style input/output discipline, TC-priority
ordering, the pervasive `Typeclasses Opaque` boundary — all in §3.4),
not from any prior-era design lean; (iv) committed-choice semantics incl. an ordered
multi-candidate `FindInContext` with once-committed first success and
a linear context scan with unification per hypothesis; (v) the
protected-existential telescope + controlled unification; (vi)
shelved side conditions + a batch pure solver (their `lia`+saturation
pipeline maps onto Lean `omega`/simp-sets + custom extensions); (vii)
the hook surface (Ltac hooks → function/attribute parameters);
(viii) the let-binding discipline for environment and continuations.

### 3.8 Replay evidence model (probe-backed)

Probe (transcript-backed; the review's wrapping_add probe, re-run at
this revision: the generated wrapping_add typing proof recompiled
against the built donor `.refinedc-ws/_build` with a trailing
`Print`, exit 0, ~1.4 s; tallies below derived from the printed
term): **the compiled proof term of a real automation-closed donor
proof is a complete, machine-readable step trace.**

- Every interpreter step leaves a distinguishable `tac_*` node
  (wrapping_add: ~30 distinct species; top of the sorted count:
  14 `tac_ex_evar`, 13 `tac_sep_pure`, 13 `tac_apply_i2p`,
  12 `tac_do_intro`, 10 `tac_li_apply`, 9 `tac_find_hyp`,
  8 `tac_find_in_context`, …).
- Committed rule choices appear as named `*_inst` constants
  (`find_in_context_type_loc_id_inst` ×12, `type_read_copy_inst`,
  `type_place_id_inst`, `copy_as_id_inst`, `type_add_int_int_inst`,
  `macro_wrapping_add_inst`, `uninit_mono_inst`,
  `simple_subsume_val_to_subsume_inst`).
- FindInContext/hypothesis choices appear as
  `tac_find_hyp`/`tac_find_in_context` nodes with their
  instantiations (§3.2(2)).
- In-walk solver discharges (§3.3) appear as embedded pure
  subproofs.

Under this model, "same residual side conditions" is well-defined:
the `SHELVED_SIDECOND` set **plus** the recorded in-walk discharges,
both extractable from the term. `liTrace_hook` (hooks.v:62) is the
alternative instrumentation channel. **This is the basis the Lane L
(replay) harness should scope against**: replay from the proof-term
trace (or equivalently from `liTrace_hook` instrumentation), where
all in-walk nondeterminism/heuristic outcomes are already resolved
and recorded — never blind reproduction of Coq-side TC resolution,
unification, and `lia` behavior.

---

## 4. Attachment-layer conversation agenda

Each row: what Caesium provides (cite) → the open question our
Iris-over-Core instantiation must answer. Questions only; no designs.

1. **Language instance / WP.** Caesium provides
   `c_lang : language` via an ectxi-language mixin over
   `runtime_expr`/`state` with `Empty_set` observations
   (lang.v:397-720) and uses iris.program_logic's WP with
   `state_interp := state_ctx` (lifting.v:14-26). Over Core: what is
   the step relation the WP is defined against (Core's small-step
   as-exists? a derived relation over the executable semantics?),
   which iris-lean WP interface do we instantiate, and what plays
   `state_interp`? Do Core's I/O-capable actions (stdout in the
   differential lanes) force non-empty observations, or is the ported
   fragment observation-free like Caesium's?
2. **Expression/statement split + labels.** Caesium's WPs is a
   *derived* notion: `stmt_wp E Q Ψ s := ∀ Φ rf, ⌜Q = rf.(rf_fn).(f_code)⌝ -∗ (return-cont) -∗ WP to_rtstmt rf s {{Φ}}`
   (lifting.v:1002-1008), with `wps_goto` (:1112) reading the label
   map and `wps_block/wps_block_rec` (:1306-1309) giving Löb-style
   block preconditions (used by `typed_block`/`type_goto_precond`,
   programs.v:72,1091). Over Core: what plays
   `gmap label stmt`/`Goto` — Core's `save`/`run` continuations? —
   and can the typed_stmt/typed_block layer keep its exact shape?
3. **Byte-granular points-to.** `heap_mapsto l q v` is per-byte
   ownership over `val := list mbyte` bundled with `loc_in_bounds`
   (ghost_state.v:141-152; heapUR ghost_state.v:13-19 with
   lock_state for NA-access tracking). The whole type system rides
   `ty_deref/ty_ref` turning `l ◁ₗ ty` into `l ↦ v ∗ v ◁ᵥ ty`
   (type.v:277-282). Over Core/Cerberus memory: what is the byte
   story — does the attachment expose a byte-list points-to over
   Cerberus's memory model (footprints, provenance-carrying bytes),
   and what happens to `lock_state` in the sequential fragment?
4. **Provenance and pointer equality.** `loc := prov × addr` with
   `ProvNull/ProvAlloc/ProvFnPtr` (loc.v:20-49); pointer truth-tests
   need `wp_if_precond l` (lifting.v:842-880) resolving
   comparability via `heap_loc_eq` (heap.v:303); `copy_alloc_id` is
   a first-class expression + judgment (lang.v:33,
   programs.v:122). Over Core: Cerberus PNVI provenance is richer
   (the parent repo measured address observability); which PNVI
   variant is the port's fixed referent, and what are the Core
   counterparts of `heap_loc_eq`/`wp_if_precond` side conditions?
5. **Layouts and op_types.** All judgments dispatch on `op_type`
   (struct.v:251) and `layout`; `ty_has_op_type`/`ty_aligned`/
   `ty_size_eq` make layout facts type-record axioms (type.v:260-276);
   struct machinery is `struct_layout` with explicit padding fields
   (struct.v:38-52). Over Core: layouts come from Cerberus's
   implementation-defined environment and `tagDefs` — who computes
   the `struct_layout` analog, and is there an op_type-shaped
   classification of Core's typed memory ops (ctype-indexed loads/
   stores) that keeps the per-ot rule split intact?
6. **mem_cast on reads.** Typed reads apply `mem_cast`
   (representation re-normalization, heap.v:383-415) and every type
   declares its `memcast_compat` class (type.v:246-296). Over Core:
   Cerberus load/store already round-trips through byte
   representations (abst/repr) — does Core's load subsume mem_cast,
   is `mem_cast_id` the right analog for pointer/int loads, or does
   this component dissolve/change shape? (Forcing-fact candidate
   either way; must be stated about Cerberus's memory model.)
7. **Calls, stack locals, and substitution.** `wp_call`
   (lifting.v:1046-1058) allocates arg+local blocks, **substitutes
   the location values into the function body** (`subst_stmt`; there
   is no environment at runtime — locals are heap blocks named by
   substituted locations), and `typed_function`/
   `introduce_typed_stmt` (function.v:5-67) mirror that;
   `fntbl_entry` is a ghost fn-table (ghost_state.v:124). Over Core:
   Core procedures bind symbols in an environment — do we prove an
   environment≈substitution correspondence at the attachment layer,
   or expose an env-aware call rule and diverge (ledger row with a
   Cerberus forcing fact)? Note the reasoning-era DN-1 material on
   exactly this is LEAD ONLY. What plays `fntbl_entry` against
   Core's function map?
8. **Allocation failure = divergence.** Caesium makes every
   allocation nondeterministically fail into `AllocFailed`, which
   *loops forever* (lang.v:471-497 `CallFailS/AllocFailS`;
   `wp_alloc_failed` proved by Löb, lifting.v:52-59) — keeping
   `not_stuck` while dodging out-of-memory reasoning. Over Core:
   Cerberus `create/alloc` has its own failure/ND story (cf. the
   parent project's malloc-null model-refinement ledger entry) —
   what is the port's allocation-failure stance, and does it stay a
   statement-level precondition or a semantics-level trick?
9. **Liveness and free.** `alloc_alive`/`alloc_alive_loc`/`freeable`
   /`alloc_global` (ghost_state.v:95-178) track allocation lifetime;
   `wps_free` (lifting.v:1123) consumes freeable; `AllocAlive` is a
   per-type class (type.v:399). Over Core: what is the kill/liveness
   ghost story over Cerberus allocations (the oracle
   allocation-census line in the parent repo is adjacent evidence)?
10. **Atomics/orders and the mask discipline.** Orders
    `ScOrd/Na1Ord/Na2Ord` sit on Deref/Assign/CAS (lang.v:23);
    `Atomic` instances (lifting.v:39-50) license `typed_read_end`/
    `typed_write_end`'s `atomic`-flag mask dance (`E → ∅`,
    programs.v:174-190) and `atomic_bool`/CAS typing. Over Core
    (sequentialized, SC-elaborated fragment first): do we port the
    atomic variants now (needed for spinlock/latch examples) or
    stub the `atomic=false` fragment and record a temporal ledger
    row (cmm-arc mover)?
11. **Ghost-state bundle + initialization.** Adequacy needs
    `typePreG`/`typeΣ` + `heap_alloc_new_blocks_upd`-style init
    lemmas (adequacy.v:10-25, ghost_state.v:878). Over Core: the
    attachment layer owns the analogous RA bundle; which parts (fn
    table, alloc metadata, liveness, globals map `globalG`,
    `lockG`, `mallocG`) are needed for the first acceptance rungs?
12. **Alignment switch.** Caesium compile-time-selects
    `enforce_alignment` (caesium/config/config.v:9-30; there is a
    dedicated no-align opam package). Over Core: alignment
    enforcement is a Cerberus memory-model behavior — fixed by our
    semantics pin; record which Caesium configuration the port's
    rule statements correspond to.
13. **Non-determinism in eval_bin_op.** Pointer comparisons etc. are
    relations, not functions (`eval_bin_op`, lang.v:240-338;
    `wp_binop` :146 quantifies over all results, `wp_binop_det`
    :162 specializes). Over Core: Core's ops are also relational at
    UB/ND points — does the `wp_*`/`wp_*_det(_pure)` split port
    unchanged?
14. **Trust deltas** (for the ledger, flagged now): (a) their
    `vm_compute` reliance sits in the *rule grammar and interpreter*,
    not only the solver layer (`annot_reduce_int` int.v:386; the
    `Goto` `compute_map_lookup`; §3.6) — banned here, so the port
    owes a kernel-legal computation story at the rule/interpreter
    level, priced as such in the ledger; (b)
    `typing/axioms.v:5` assumes UIP (`eq_rect_eq`) — harmless in
    Lean (definitional proof irrelevance) but should be noted as a
    donor-side axiom our port does not need; (c) their adequacy
    concludes `not_stuck` (partial correctness + progress) — our
    acceptance statement shape at the adequacy boundary is an
    operator conversation (ties to the cerberus-lean differential
    ground truth).
15. **The annotation carrier.** RefinedC's `typed_annot_expr`/
    `typed_annot_stmt` rules (programs.v:41,46) fire on
    `AnnotExpr`/`AnnotStmt` **syntax nodes** the frontend plants in
    the program (notation.v:106-109), carrying the payloads of
    `annotations.v` (share, stop, learn, lock, reduce, …); several
    type formers' rules key on this channel (e.g. `annot_reduce_int`,
    int.v:386 — also a `li_vm_compute` carrier, cf. item 14(a)).
    Note the split: block/loop *invariants* survive without it —
    they arrive via the `split_blocks` proof-script argument (a
    `gmap label (iProp Σ)`, observed directly in the generated
    wrapping_add proof) — but the in-program hint channel (sharing,
    copy-to-uninit, lock annotations, reduce) has no Core story:
    with the frontend out of scope and Core produced by Cerberus
    elaboration of plain C, nothing plants these nodes. Over Core:
    what plays the annotation carrier — Core/Ail annotations? a side
    table keyed by location? magic calls? — and which
    annotation-fired rules are in the port's first fragment at all?
16. **Reflected syntax and syntax-directed dispatch.** Caesium ships
    module `W` (reflected expr/stmt, `to_expr/of_expr` correctness,
    context finders `find_expr_fill`/`find_stmt_fill`, tactics.v),
    and typing is written against it: `find_place_ctx`/`IntoPlaceCtx`
    (programs.v:257,278) are defined over `W.expr`, and
    `liRStmt`/`liRExpr` (automation.v:145-247) dispatch on W
    constructors after `W.of_stmt`/`W.of_expr` reflection (§1.1
    caveat, §1.3.2). Over Core: what plays `W`, `find_expr_fill`,
    and `find_place_ctx` over *Core's* constructor set — including
    whether Core's already-sequenced form dissolves the bind layer,
    shrinking the reflected-syntax obligation (to place contexts
    only, or to nothing)?
17. **Which Core, exactly — and Core's evaluation-order
    nondeterminism.** Item 13 covers relational per-op ND only. Core
    additionally has *unsequenced* composition (`Eunseq`, wseq/sseq)
    — evaluation-order ND with UB at races, a fundamentally
    different ND species than Caesium's per-op relational results
    (Caesium fixes evaluation order via its ectx discipline). The
    rules of engagement say "their evaluated/sequentialized fragment
    first"; concretely: is the port's referent sequentialised Core
    (which pass, pinned where), and what happens to the WP when
    `Eunseq` is present? This decision shapes the language-instance
    design (item 1).

---

## 5. Adequacy and the examples ladder

### 5.1 Adequacy mechanics

`refinedc_adequacy` (typing/adequacy.v:40-90): given (i) an initial
heap built by `alloc_new_blocks` for globals, (ii) a fn-table map,
(iii) for each thread main a proof of
`main ◁ᵥ main @ function_ptr (main_type P)` (where
`main_type P := fn(∀():(); P) → ∃():(), int i32; True`, adequacy.v:36),
it concludes: after any `nsteps` of `c_lang` from
`Call main []`, every thread expression is `not_stuck` — via Iris's
`wp_strong_adequacy`, allocating the heapG/ghost maps and framing
`state_ctx` as the state interpretation (adequacy.v:52-70). The
typed→WP direction is discharged by literally running the call typing
rules (`type_call`, `type_call_fnptr`) inside the proof
(adequacy.v:79-84). Helper tactics (`adequacy_solve_typed_function`,
:122-128) connect per-function typing lemmas produced by the frontend
to the fn-table assertion. Port-relevant summary: adequacy = Iris
adequacy over the language instance + ghost-state init + one
application of the call rule; everything else is the type system.

### 5.2 The acceptance ladder (examples/tutorial, BSD)

Annotated C sources; the frontend generates Coq which the automation
checks — for the port, the *Coq-level* content (specs as `fn_params`,
per-function `typed_function` lemmas discharged by `repeat liRStep`)
is the transfer target, authored natively in Lean. Manual auxiliary
proofs live in `examples/proofs/<name>/` and `tutorial/proofs/<name>/`.

Rough difficulty ordering (derived from file inspection + suite
structure; a precise per-file feature matrix is arc-2 work):

1. **Tutorial stem** `tutorial/`: `t00_intro.c`, `t01_basic.c`
   (int identity/add: int types, arith side conditions),
   `t02_evars.c` (existential instantiation), `t03_list.c` (own
   pointers + recursive type via `type_fixpoint`), `t04_alloc.c`
   (malloc/uninit), `t05_main.c` (globals + main/adequacy);
   proofs dirs also for `t07_arrays`, `t08_tree`,
   `quicksort_solution`, and `lithium/` (pure Lithium exercises).
2. **Small examples** `examples/`: `paper_example_2_1/2_2.c`,
   `talk_demo*.c`, `reverse.c` (linked list), `shift.c`,
   `wrapping_add.c`, `pointers.c`, `simple_union.c`, `flags.c`
   (bitfields), `intptr.c` (int↔ptr casts), `container_of.c`
   (struct offset arithmetic), `tagged_ptr.c` (low-bit tagging).
3. **Medium** : `binary_search.c`, `malloc1.c` (allocator),
   `quick_sort.c`, `queue.c`, `mutable_map.c`,
   `VerifyThis2021/challenge1-2.c`.
4. **Concurrency-flavored**: `spinlock.c`, `lock.c`, `latch.c`
   (atomic_bool/CAS; needs agenda item 10).
5. **Flagships**: `btree.c` (largest single file), `mpool.c`/
   `mpool_simpl.c` (Hafnium memory pool, 101 rc-annotations),
   `scheduler/` (multi-file project), `ocaml_runtime.c`.
6. **Out of BSD scope**: `linux/` (GPL-2.0: `pkvm/`, `casestudies/`)
   — per house rules GPL examples live elsewhere; noted only as the
   donor's own kernel-adjacent tier.

---

## 6. Surprises / deltas vs prior expectations (for the orchestrator)

1. **ARCHITECTURE.md is stale and the layering is inverted**: lithium
   is a standalone package with zero caesium imports; caesium depends
   on lithium (§1.1). Good for the port (Lithium can be built before
   any semantics work) but the doc should not be cited as authority.
2. **Caesium is not semantics-only**: it ships the ghost-state/RA
   layer, the full WP lemma library, and proof-mode bind tactics —
   i.e. much of what our "attachment layer" must build is, in the
   donor, *inside* the semantics package. The port boundary
   "replace Caesium" therefore means: replace lang+heap+opsem AND
   re-prove the ~55-lemma lifting interface (§1.3 stratum iii) over
   Core.
3. **Locals are substituted heap locations, no runtime environment**
   (lifting.v:1046, function.v:5) — the donor's answer to the
   env-vs-substitution question is substitution-everywhere.
4. **Allocation failure is modeled as divergence** via a Löb-proved
   WP for an infinite `AllocFailed` loop (lifting.v:52) — a
   partial-correctness dodge relevant to the malloc-null discussions.
5. **Donor trust surface**: `vm_compute` inside the rule grammar and
   solver path (§3.6) and a
   UIP axiom (`typing/axioms.v:5`) — both need ledger entries where
   our port deliberately differs.
6. **Lithium has evolved past the paper** (limodal goals, LiEntails
   hint-db dispatch, Ltac2 internals) — port from this source, not
   from the paper or the reasoning-era review.
