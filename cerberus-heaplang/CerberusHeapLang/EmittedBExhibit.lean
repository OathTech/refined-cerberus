/-
CerberusHeapLang.EmittedBExhibit — EXHIBIT B IN THE EMITTED-CORE SHAPE
(dialect arc E2; the acceptance exhibit of the slice, briefed from
docs/2026-09-04_emitted-core-dialect-design.md §C.2: the loaded-value
protocol).

E1 admitted the elaborator's annotations, `bound` and `Ivalignof`. E2
admits the LOADED-VALUE currency and the shapes the corpus builds it
with (docs/corpus-e0/t1.annot.core): `Specified(v)`/`Unspecified(ty)`
as pure constructor operands, the uninitialised local's
`store(ty, x, Unspecified(ty))`, pure `case` over a tuple of loaded
values with a `Specified(…)` pattern row and the wildcard `undef(UB…)`
arm, the flat tuple binders `let strong (a, b) = …`/`let weak (a, b) = …`
and the weak plain-symbol binder `let weak p = pure(y) in load(…)`.
This module is the second authored exhibit re-expressed in those
features — an E2 SYNTHETIC (the elaborator's own placements are t1Main's,
Examples/CorpusE0.lean; `unseq` and `conv_loaded_int` are E3/E4's):

```
{-# <exhibitB.c:1:2, exhibitB.c:1:30> #-} let strong y: pointer =
  create(Ivalignof('signed int'), 'signed int') in
{-# §6.5#2 #-} bound(store('signed int', y, Unspecified('signed int'))) ;
let strong a1: loaded integer = {-# §6.5#2 #-} bound(pure(Specified(3))) in
let strong a2: loaded integer = {-# §6.5#2 #-} bound(
  let weak (b1: loaded integer, b2: loaded integer) = pure((a1, Specified(1))) in
  pure(case (b1, b2) of
       | (Specified(v1: integer), Specified(v2: integer)) => Specified(v1 + v2)
       | _ => undef(<<UB036_exceptional_condition>>)
       end)) in
{-# §6.5#2 #-} bound(store('signed int', y, a2)) ;
let strong (c1: loaded integer, c2: loaded integer) = pure((Specified(0), a2)) in
{-# §6.5#2 #-} bound(let weak p: pointer = pure(y) in load('signed int', p))
```

The program's value is BARE `Specified(4)` and its one cell holds 4's byte
image; the undef arm is never selected — it is in the FRAGMENT (`PePure`
admits `undef`), and were it reached the classifier's `.undef` face makes
the round `ShippedRefusal.killed (Undef0 …)` (`complete_pure_op`), never a
default. The uninitialised store writes the engine's own byte image of
`MVunspecified int` (`memValueToBytes`: `sizeof int` padding bytes —
provenance-free, value-free — which is byte-for-byte the fresh cell's
`undefByte`s: `unspec_bytes`, by `rfl`; `unspec_storable` is the store's
`StorableAt` obligation and states nothing about the bytes).

What the re-expression exercises that exhibit A does not:
  * `Frag.pure_op` at constructor operands (`Specified(3)`, the tuple, the
    `case`) and `wps_pure`/`wpt_pure` at each (the evaluator's `PEctor`/
    `PEcase`/`PEop` arms — `specIntPe_eval`, `tuple_eval`, `casePe_eval`);
  * `Frag.wseq_tuple`/`Frag.sseq_tuple` (`wps_wseq_tuple`/`wpt_wseq_tuple`,
    `wps_seq_tuple`/`wpt_seq_tuple`: the binding is `update_env` at the
    tuple pattern — `update_env_tuple2`) and `Frag.wseq_sym`
    (`wps_wseq_sym`/`wpt_wseq_sym`);
  * the store of `Unspecified(int)` through the generic `wps_store` at
    `cv = Vloaded (LVunspecified int)` (`unspec_encodes`, `unspec_storable`;
    the image `unspec_bytes`).

A CLIENT of the logic: it reasons through the public rules only; the
production theorem is reached through the generic
`wpt_driver_done_alloc → prod_run_eqJ` route (exhibit A's).
-/
import CerberusHeapLang.Examples.Layout
import CerberusHeapLang.ProdEntry
import CerberusHeapLang.Exhibit
import CerberusHeapLang.AllocExhibit
import CerberusHeapLang.ProdExhibit
import CerberusHeapLang.EmittedAExhibit

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Maybe Lem_List
open scoped Iris.Std.PartialMap

variable {GF : BundledGFunctors}

/-! ## The program in the emitted shape -/

def ebFile : String := "exhibitB.c"
def ebPos (l c : Nat) : CerbLocation.Pos := ⟨ebFile, l, c⟩
def ebLoc (l1 c1 l2 c2 : Nat) : CerbLocation.Loc :=
  .region (ebPos l1 c1) (ebPos l2 c2) .noCursor

def ySymB : sym := Symbol "" 601 SD_None
def a1SymB : sym := Symbol "" 602 SD_None
def a2SymB : sym := Symbol "" 603 SD_None
def b1SymB : sym := Symbol "" 604 SD_None
def b2SymB : sym := Symbol "" 605 SD_None
def v1SymB : sym := Symbol "" 606 SD_None
def v2SymB : sym := Symbol "" 607 SD_None
def c1SymB : sym := Symbol "" 608 SD_None
def c2SymB : sym := Symbol "" 609 SD_None
def pSymB : sym := Symbol "" 610 SD_None

def lintB : core_base_type := BTy_loaded OTy_integer
def ointB : core_base_type := BTy_object OTy_integer
def ptrB : core_base_type := BTy_object OTy_pointer

def psymB (x : sym) : generic_pexpr Unit sym := Pexpr [] () (PEsym x)

/-- `Specified(n)` as a pure CONSTRUCTOR operand (the elaborator's
    spelling of a literal loaded value; `PEctor Cspecified`). -/
def specIntPe (n : Int) : generic_pexpr Unit sym :=
  Pexpr [] () (PEctor Cspecified [Pexpr [] () (PEval (Vobject (OVinteger (CerbMem.integerIval n))))])

/-- `Unspecified('signed int')` (`PEctor Cunspecified` at the ctype). -/
def unspecIntPe : generic_pexpr Unit sym :=
  Pexpr [] () (PEctor Cunspecified [Pexpr [] () (PEval (Vctype intTy))])

def tuplePe (p1 p2 : generic_pexpr Unit sym) : generic_pexpr Unit sym :=
  Pexpr [] () (PEctor Ctuple [p1, p2])

/-- The `case` alternatives: the `(Specified(v1), Specified(v2))` row and
    the wildcard `undef(UB036)` arm (t1.annot.core's shape). -/
def specSumPats : List (pattern × generic_pexpr Unit sym) :=
  [(Pattern [] (CaseCtor Ctuple
      [Pattern [] (CaseCtor Cspecified [Pattern [] (CaseBase (some v1SymB, ointB))]),
       Pattern [] (CaseCtor Cspecified [Pattern [] (CaseBase (some v2SymB, ointB))])]),
    Pexpr [] () (PEctor Cspecified [Pexpr [] () (PEop OpAdd (psymB v1SymB) (psymB v2SymB))])),
   (Pattern [] (CaseBase (none, BTy_tuple [lintB, lintB])),
    Pexpr [] () (PEundef (ebLoc 3 10 3 20) UB036_exceptional_condition))]

def casePe : generic_pexpr Unit sym :=
  Pexpr [] () (PEcase (tuplePe (psymB b1SymB) (psymB b2SymB)) specSumPats)

def leafB (x : sym) : TupleLeaf := ([], some x, lintB)

/-- The loaded integer `Specified(n)`. -/
def intVal (n : Int) : value := Vloaded (LVspecified (OVinteger (CerbMem.integerIval n)))

def fourMval : CerbMem.MemValue :=
  CerbMem.integerValueMval (.Signed .Int_) (CerbMem.integerIval 4)

abbrev fourBytes (tds : CerbTags.TagDefsMap) : List CerbMem.AbsByte :=
  (CerbMem.memValueToBytes tds [] fourMval).2

def unspecMval : CerbMem.MemValue := CerbMem.unspecifiedMval intTy

/-- Exhibit B (header). -/
def progBE2 : CoreExpr :=
  Expr [Aloc (ebLoc 1 2 1 30), Astmt] (Esseq (symPat [] ySymB ptrB)
    (createOpRedex [Aloc (ebLoc 1 11 1 30), Aexpr] (ebLoc 1 11 1 30) empty_annotation
      alignofIntPe intTyPe (PrefOther "spike-y"))
  (Expr [Aloc (ebLoc 2 2 2 40), Astmt] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
    (Expr [Astd "§6.5#2"] (Ebound
      (storeOpRedex [] (ebLoc 2 2 2 40) empty_annotation intTy (psymB ySymB) unspecIntPe NA)))
  (Expr [Aloc (ebLoc 3 2 3 30), Astmt] (Esseq (symPat [] a1SymB lintB)
    (Expr [Astd "§6.5#2"] (Ebound (Expr [] (Epure (specIntPe 3)))))
  (Expr [Aloc (ebLoc 4 2 4 60), Astmt] (Esseq (symPat [] a2SymB lintB)
    (Expr [Astd "§6.5#2"] (Ebound
      (Expr [Aloc (ebLoc 4 12 4 60), Aexpr] (Ewseq (tuplePat [] [leafB b1SymB, leafB b2SymB])
        (Expr [] (Epure (tuplePe (psymB a1SymB) (specIntPe 1))))
        (Expr [] (Epure casePe))))))
  (Expr [Aloc (ebLoc 5 2 5 30), Astmt] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
    (Expr [Astd "§6.5#2"] (Ebound
      (storeOpRedex [] (ebLoc 5 2 5 30) empty_annotation intTy (psymB ySymB) (psymB a2SymB) NA)))
  (Expr [Aloc (ebLoc 6 2 6 40), Astmt] (Esseq (tuplePat [] [leafB c1SymB, leafB c2SymB])
    (Expr [] (Epure (tuplePe (specIntPe 0) (psymB a2SymB))))
  (Expr [Astd "§6.5#2"] (Ebound
    (Expr [Aloc (ebLoc 7 8 7 30), Aexpr] (Ewseq (symPat [] pSymB ptrB)
      (Expr [] (Epure (psymB ySymB)))
      (loadOpRedex [] (ebLoc 7 20 7 30) empty_annotation intTy (psymB pSymB) NA))))))))))))))))

/-- The evaluator-fuel bound at an authored operand (its depth is tiny). -/
theorem depLeB {pe : generic_pexpr Unit sym} (h : peDepth pe ≤ 9) :
    peDepth pe ≤ lemDefaultFuel := by
  rw [show lemDefaultFuel = 999999 + 1 from rfl]; omega

/-- Cone membership. -/
theorem progBE2_frag : Frag progBE2 :=
  .sseq_sym
    (.create_op rfl (.ctorTy [] Civalignof rfl [] intTy) (.val [] (Vctype intTy))
      (depLeB (by decide)) (peDepth_val_le _ _))
    (.sseq
      (.bound (.store_op rfl (.sym [] ySymB) (.ctorTy [] Cunspecified rfl [] intTy)
        (depLeB (by decide)) (depLeB (by decide))))
      (.sseq_sym
        (.bound (.pure_op rfl (PePure.of_isPePure rfl) (depLeB (by decide))))
        (.sseq_sym
          (.bound (.wseq_tuple
            (.pure_op rfl (PePure.of_isPePure rfl) (depLeB (by decide)))
            (.pure_op rfl (PePure.of_isPePure rfl) (depLeB (by decide)))))
          (.sseq
            (.bound (.store_op rfl (.sym [] ySymB) (.sym [] a2SymB)
              (depLeB (by decide)) (depLeB (by decide))))
            (.sseq_tuple
              (.pure_op rfl (PePure.of_isPePure rfl) (depLeB (by decide)))
              (.bound (.wseq_sym
                (.pure_op rfl (.sym [] ySymB) (depLeB (by decide)))
                (.load_op rfl (.sym [] pSymB) (depLeB (by decide))))))))))

/-! ## The evaluator at the program's operands -/

theorem unspecIntPe_eval {tds : CerbTags.TagDefsMap} (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack) :
    evalPexpr tds ext file ρ unspecIntPe = some (Vloaded (LVunspecified intTy)) := by
  simp only [unspecIntPe, evalPexpr_tyctor, evalTyCtor_unspecified, isTyCtor]

theorem specIntPe_eval {tds : CerbTags.TagDefsMap} (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack) (n : Int) :
    evalPexpr tds ext file ρ (specIntPe n) = some (intVal n) := by
  rw [specIntPe, evalPexpr_ctor1, evalPexpr_val]
  rfl

theorem tuple_eval {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {file : generic_file Unit core_run_annotation} {ρ : EnvStack}
    {p1 p2 : generic_pexpr Unit sym} {v1 v2 : value}
    (h1 : evalPexpr tds ext file ρ p1 = some v1) (h2 : evalPexpr tds ext file ρ p2 = some v2) :
    evalPexpr tds ext file ρ (tuplePe p1 p2) = some (Vtuple [v1, v2]) := by
  rw [tuplePe, evalPexpr_ctor2, h1, h2]
  rfl

/-- The selected branch of the `case` at `(Specified(3), Specified(1))`:
    the engine's `select_case`/`subst_sym_pexpr` at the concrete row
    (computed). -/
def specSumBranch : generic_pexpr Unit sym :=
  Pexpr [] () (PEctor Cspecified [Pexpr [] () (PEop OpAdd
    (Pexpr [] () (PEval (Vobject (OVinteger (CerbMem.integerIval 3)))))
    (Pexpr [] () (PEval (Vobject (OVinteger (CerbMem.integerIval 1))))))])

theorem specSum_select :
    select_case subst_sym_pexpr (Vtuple [intVal 3, intVal 1]) specSumPats =
      some specSumBranch := rfl

theorem specSumBranch_eval {tds : CerbTags.TagDefsMap} (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack) :
    evalPexpr tds ext file ρ (reannot0 specSumBranch) = some (intVal 4) := by
  show evalPexpr tds ext file ρ (Pexpr [] () (PEctor Cspecified [Pexpr [] () (PEop OpAdd
    (Pexpr [] () (PEval (Vobject (OVinteger (CerbMem.integerIval 3)))))
    (Pexpr [] () (PEval (Vobject (OVinteger (CerbMem.integerIval 1))))))])) = _
  rw [evalPexpr_ctor1, evalPexpr_op, evalPexpr_val, evalPexpr_val]
  rfl

/-- THE CASE at loaded values: the scrutinee tuple evaluates at the
    tuple-bound frame, the `Specified` row is selected, the branch
    evaluates to `Specified(4)` (the mirror evaluator's `PEcase` arm —
    `evalPexpr_case`). -/
theorem casePe_eval {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {file : generic_file Unit core_run_annotation} {ρ : EnvStack}
    (hb1 : evalPexpr tds ext file ρ (psymB b1SymB) = some (intVal 3))
    (hb2 : evalPexpr tds ext file ρ (psymB b2SymB) = some (intVal 1)) :
    evalPexpr tds ext file ρ casePe = some (intVal 4) := by
  rw [casePe, evalPexpr_case, if_pos (show isPePureAlts specSumPats = true from rfl),
    tuple_eval hb1 hb2]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [specSum_select]
  simp only [Option.bind_some]
  rw [if_pos (by decide)]
  exact specSumBranch_eval ext ρ

/-! ## The values at the cell -/

theorem unspec_encodes :
    memValueFromValue fmapEmpty (Ctype [] (unatomic_ intTy)) (Vloaded (LVunspecified intTy)) =
      some unspecMval := rfl

/-- The uninitialised local's store is storable (`StorableAt`'s five
    fields, Heap.lean: `compat`, `fpm`, `len`, `bytes_fpm`, `stored_dec` —
    type compatibility, funptrmap inertness, the image's length, table
    independence of the image and of its decode). It states nothing about
    WHICH bytes the image holds — that is `unspec_bytes`. -/
theorem unspec_storable (tds : CerbTags.TagDefsMap) : StorableAt tds intTy unspecMval :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- The engine's byte image of `MVunspecified int` IS the fresh cell's
    image: `sizeof int` copies of `undefByte` (`memValueToBytes`'s
    `MVunspecified` arm replicates `paddingByte`, which is `undefByte`
    field for field — `unspec_paddingByte`). Stated, not assumed (E2 range
    audit R-2). -/
theorem unspec_bytes (tds : CerbTags.TagDefsMap) :
    (CerbMem.memValueToBytes tds [] unspecMval).2 = intUndefBytes tds := rfl

theorem unspec_paddingByte : CerbMem.paddingByte = undefByte := rfl

theorem four_encodes :
    memValueFromValue fmapEmpty (Ctype [] (unatomic_ intTy)) (intVal 4) = some fourMval := rfl

theorem four_storable (tds : CerbTags.TagDefsMap) : StorableAt tds intTy fourMval :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

theorem four_reconstruct {tds : CerbTags.TagDefsMap} (lum : List (Int × identifier))
    (fpm : CerbMem.Funptrmap) (ad : Int) :
    CerbMem.reconstructValue tds lum fpm ad intTy
      (((fourBytes tds).drop 0).take (CerbMem.sizeofCtype tds intTy)) = fourMval := rfl

theorem four_fromMemValue : (valueFromMemValue fourMval).2 = intVal 4 := rfl

theorem four_loadTrap : loadTrapV intTy fourMval = false := rfl

/-! ## The environment frames and their lookups -/

/-- The frame after `y` is bound. -/
abbrev frY (py : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd ySymB (Vobject (OVpointer py)) f
abbrev frA1 (py : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd a1SymB (intVal 3) (frY py f)
abbrev frB (py : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd b1SymB (intVal 3) (envAdd b2SymB (intVal 1) (frA1 py f))
abbrev frA2 (py : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd a2SymB (intVal 4) (frB py f)
abbrev frC (py : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd c1SymB (intVal 0) (envAdd c2SymB (intVal 4) (frA2 py f))
abbrev frP (py : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd pSymB (Vobject (OVpointer py)) (frC py f)

theorem frY_symFrame {f : Fmap sym value} (hf : SymFrame f) (py : CerbMem.PointerValue) :
    SymFrame (frY py f) := hf.add _ _
theorem frA1_symFrame {f : Fmap sym value} (hf : SymFrame f) (py : CerbMem.PointerValue) :
    SymFrame (frA1 py f) := (frY_symFrame hf py).add _ _
theorem frB_symFrame {f : Fmap sym value} (hf : SymFrame f) (py : CerbMem.PointerValue) :
    SymFrame (frB py f) := ((frA1_symFrame hf py).add _ _).add _ _
theorem frA2_symFrame {f : Fmap sym value} (hf : SymFrame f) (py : CerbMem.PointerValue) :
    SymFrame (frA2 py f) := (frB_symFrame hf py).add _ _
theorem frC_symFrame {f : Fmap sym value} (hf : SymFrame f) (py : CerbMem.PointerValue) :
    SymFrame (frC py f) := ((frA2_symFrame hf py).add _ _).add _ _

theorem frY_lookup_y {f : Fmap sym value} (hf : SymFrame f) (py : CerbMem.PointerValue) :
    fmapLookupBy symCmpK ySymB (frY py f) = some (Vobject (OVpointer py)) := by
  unfold frY
  rw [envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]

theorem frA1_lookup_a1 {f : Fmap sym value} (hf : SymFrame f) (py : CerbMem.PointerValue) :
    fmapLookupBy symCmpK a1SymB (frA1 py f) = some (intVal 3) := by
  unfold frA1
  rw [envAdd_lookup (frY_symFrame hf py) symCmpK, if_pos (by decide +kernel)]

theorem frB_lookup_b1 {f : Fmap sym value} (hf : SymFrame f) (py : CerbMem.PointerValue) :
    fmapLookupBy symCmpK b1SymB (frB py f) = some (intVal 3) := by
  unfold frB
  rw [envAdd_lookup ((frA1_symFrame hf py).add _ _) symCmpK, if_pos (by decide +kernel)]

theorem frB_lookup_b2 {f : Fmap sym value} (hf : SymFrame f) (py : CerbMem.PointerValue) :
    fmapLookupBy symCmpK b2SymB (frB py f) = some (intVal 1) := by
  unfold frB
  rw [envAdd_lookup ((frA1_symFrame hf py).add _ _) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (frA1_symFrame hf py) symCmpK, if_pos (by decide +kernel)]

theorem frA2_lookup_a2 {f : Fmap sym value} (hf : SymFrame f) (py : CerbMem.PointerValue) :
    fmapLookupBy symCmpK a2SymB (frA2 py f) = some (intVal 4) := by
  unfold frA2
  rw [envAdd_lookup (frB_symFrame hf py) symCmpK, if_pos (by decide +kernel)]

theorem frA2_lookup_y {f : Fmap sym value} (hf : SymFrame f) (py : CerbMem.PointerValue) :
    fmapLookupBy symCmpK ySymB (frA2 py f) = some (Vobject (OVpointer py)) := by
  unfold frA2 frB frA1
  rw [envAdd_lookup (frB_symFrame hf py) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup ((frA1_symFrame hf py).add _ _) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (frA1_symFrame hf py) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (frY_symFrame hf py) symCmpK, if_neg (by decide +kernel)]
  exact frY_lookup_y hf py

theorem frC_lookup_y {f : Fmap sym value} (hf : SymFrame f) (py : CerbMem.PointerValue) :
    fmapLookupBy symCmpK ySymB (frC py f) = some (Vobject (OVpointer py)) := by
  unfold frC
  rw [envAdd_lookup ((frA2_symFrame hf py).add _ _) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (frA2_symFrame hf py) symCmpK, if_neg (by decide +kernel)]
  exact frA2_lookup_y hf py

theorem frP_lookup_p {f : Fmap sym value} (hf : SymFrame f) (py : CerbMem.PointerValue) :
    fmapLookupBy symCmpK pSymB (frP py f) = some (Vobject (OVpointer py)) := by
  unfold frP
  rw [envAdd_lookup (frC_symFrame hf py) symCmpK, if_pos (by decide +kernel)]

/-- `update_env` at the two-leaf tuple binder: the two leaves bound
    right-to-left onto the head frame (the engine's `Ctuple` arm,
    `List.foldr` over the zipped leaves — Core_aux.lean:861). -/
theorem update_env_tuple2 (x1 x2 : sym) (bty : core_base_type) (v1 v2 : value)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    update_env (tuplePat [] [([], some x1, bty), ([], some x2, bty)]) (Vtuple [v1, v2])
        (ev0 :: evs) =
      envAdd x1 v1 (envAdd x2 v2 ev0) :: evs := by
  rw [update_env_cons]
  show update_env_aux_lemFuel lemDefaultFuel _ _ _ :: evs = _
  rw [show lemDefaultFuel = 999999 + 1 from rfl]
  rfl

/-- The symbol operand at a frame whose lookup is known (the extern map
    does not redirect the symbol). -/
theorem symB_eval {M : MachineCtx} (hex : ∀ x, resolveExtern M.extern x = x)
    {x : sym} {f : Fmap sym value} {v : value} (evs : List (Fmap sym value))
    (hl : fmapLookupBy symCmpK x f = some v) :
    evalPexpr M.tagDefs M.extern M.file (f :: evs) (psymB x) = some v := by
  rw [psymB, evalPexpr_sym_of_resolve _ _ _ (hex _)]
  exact lookup_env_head hl evs

/-! ## THE PARTIAL JUDGMENT: the value is BARE `Specified(4)` and the cell
holds 4 -/

theorem progBE2_wps [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpec GF} {Θ : ProcSpec GF}
    (hex : ∀ x, resolveExtern M.extern x = x)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (hf : SymFrame ev0) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs intTy 4)) ⊢
      wps M p Ls Θ (fun w _ => iprop(⌜w = SpikeVal.pure (intVal 4)⌝ ∗
          (∃ (id a : Int), cellOwn M.tagDefs (GF := GF) id (.own 1)
            ⟨a, intTy, fourBytes M.tagDefs⟩)))
        progBE2 (ev0 :: evs) := by
  iintro Hcap
  unfold progBE2
  -- y := create(Ivalignof(int), int)
  iapply wps_seq_sym
  iapply wps_create_eval _ _ empty_annotation alignofIntPe intTyPe (PrefOther "spike-y")
    (ev0 :: evs) (align := CerbMem.alignofIval M.tagDefs intTy) (ty := intTy) rfl
    (alignofIntPe_eval _ _) (evalPexpr_val _ _ _ _ _)
  rw [alignofIval_intTy]
  iapply wps_create _ _ empty_annotation .Prov_none 4 intTy (PrefOther "spike-y") (ev0 :: evs)
    intTy_size_pos intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [Hcap]
  · iexact Hcap
  iintro %py ⟨Hpt, -⟩
  iexists (Vobject (OVpointer py))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym ySymB ptrB]
  -- bound(store(int, y, Unspecified(int))) ; …
  iapply wps_seq
  iapply wps_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  iapply wps_store_eval _ _ empty_annotation intTy _ _ NA _ rfl
    (pv := py) (cv := Vloaded (LVunspecified intTy))
    (symB_eval hex evs (frY_lookup_y hf py)) (unspecIntPe_eval _ _)
  iapply wps_store _ _ empty_annotation intTy py (Vloaded (LVunspecified intTy)) NA unspecMval
    (intUndefBytes M.tagDefs) _ unspec_encodes (unspec_storable _)
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp1 Hpt
  simp only [SpikeVal.mergeInto]
  -- a1 := bound(pure(Specified(3)))
  iapply wps_seq_sym
  iapply wps_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  iapply wps_pure _ _ rfl (specIntPe_eval _ _ 3)
  simp only [SpikeVal.val]
  iexists (intVal 3)
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a1SymB lintB]
  -- a2 := bound(let weak (b1, b2) = pure((a1, Specified(1))) in pure(case …))
  iapply wps_seq_sym
  iapply wps_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  iapply wps_wseq_tuple
  iapply wps_pure _ _ rfl (tuple_eval (symB_eval hex evs (frA1_lookup_a1 hf py))
    (specIntPe_eval _ _ 1))
  iexists [intVal 3, intVal 1]
  isplit
  · ipureintro
    rfl
  rw [show tuplePat [] [leafB b1SymB, leafB b2SymB] =
    tuplePat [] [([], some b1SymB, lintB), ([], some b2SymB, lintB)] from rfl,
    update_env_tuple2 b1SymB b2SymB lintB]
  iapply wps_pure _ _ rfl (casePe_eval (symB_eval hex evs (frB_lookup_b1 hf py))
    (symB_eval hex evs (frB_lookup_b2 hf py)))
  simp only [SpikeVal.val]
  iexists (intVal 4)
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a2SymB lintB]
  -- bound(store(int, y, a2)) ; …
  iapply wps_seq
  iapply wps_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  iapply wps_store_eval _ _ empty_annotation intTy _ _ NA _ rfl
    (pv := py) (cv := intVal 4)
    (symB_eval hex evs (frA2_lookup_y hf py)) (symB_eval hex evs (frA2_lookup_a2 hf py))
  iapply wps_store _ _ empty_annotation intTy py (intVal 4) NA fourMval _ _
    four_encodes (four_storable _)
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp2 Hpt
  simp only [SpikeVal.mergeInto]
  -- let strong (c1, c2) = pure((Specified(0), a2)) in …
  iapply wps_seq_tuple
  iapply wps_pure _ _ rfl (tuple_eval (specIntPe_eval _ _ 0)
    (symB_eval hex evs (frA2_lookup_a2 hf py)))
  iexists [intVal 0, intVal 4]
  isplit
  · ipureintro
    rfl
  rw [show tuplePat [] [leafB c1SymB, leafB c2SymB] =
    tuplePat [] [([], some c1SymB, lintB), ([], some c2SymB, lintB)] from rfl,
    update_env_tuple2 c1SymB c2SymB lintB]
  -- bound(let weak p = pure(y) in load(int, p))
  iapply wps_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  iapply wps_wseq_sym
  iapply wps_pure _ _ rfl (symB_eval hex evs (frC_lookup_y hf py))
  iexists (Vobject (OVpointer py))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym pSymB ptrB]
  icases (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mp $$ Hpt
    with ⟨%id, %a, %hpv, Hcell⟩
  iapply wps_load_eval _ _ empty_annotation intTy _ NA _ rfl (pv := py)
    (symB_eval hex evs (frP_lookup_p hf py))
  rw [hpv, show (cellPtr id a) = cellPtr id (a + ((0 : Nat) : Int))
    from congrArg (cellPtr id) (by omega)]
  iapply wps_load_cell_at _ _ empty_annotation id a intTy 0 intTy NA
    (.own 1) (fourBytes M.tagDefs) _ (mv := fourMval) (by omega)
    (fun lum fpm => four_reconstruct lum fpm _) four_loadTrap
  isplitl [Hcell]
  · iexact Hcell
  iintro %fp3 Hcell
  simp only [SpikeVal.val]
  isplit
  · ipureintro
    rw [four_fromMemValue]
  iexists id, a
  iexact Hcell

/-! ## THE TOTAL JUDGMENT, budget 30 (derived: create-operand eval 1 +
create 2 + [bound 1 + store-operand eval 1 + store 3] + [bound 1 + pure 2]
+ [bound 1 + pure 2 + pure 2] + [bound 1 + store-operand eval 1 + store 3]
+ pure 2 + [bound 1 + pure 2 + load-operand eval 1 + load 3]) -/

/-- The engine-facing postcondition: `Specified(4)` delivered, the final
    memory holding 4's image at the program's own fresh cell. -/
def ψB (tds : CerbTags.TagDefsMap) : value → Mem → Prop := fun v σ' =>
  v = intVal 4 ∧ ∃ i a : Int, CellCoh tds σ' i ⟨a, intTy, fourBytes tds⟩

theorem progBE2_wpt [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    (hex : ∀ x, resolveExtern M.extern x = x)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (hf : SymFrame ev0) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs intTy 4)) ⊢
      wpt M p Ls Θ 30 (readoutPost (ψB M.tagDefs)) progBE2 (ev0 :: evs) := by
  iintro Hcap
  unfold progBE2
  rw [show (30 : Nat) = 3 + 27 from rfl]
  iapply wpt_seq_sym
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_create_eval _ _ empty_annotation alignofIntPe intTyPe (PrefOther "spike-y")
    (ev0 :: evs) (align := CerbMem.alignofIval M.tagDefs intTy) (ty := intTy) rfl
    (alignofIntPe_eval _ _) (evalPexpr_val _ _ _ _ _)
  rw [alignofIval_intTy]
  iapply wpt_create _ _ empty_annotation .Prov_none 4 intTy (PrefOther "spike-y") (ev0 :: evs)
    (Nat.le_refl 2) intTy_size_pos intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [Hcap]
  · iexact Hcap
  iintro %py ⟨Hpt, -⟩
  iexists (Vobject (OVpointer py))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym ySymB ptrB, show (27 : Nat) = 5 + 22 from rfl]
  -- bound(store(int, y, Unspecified(int))) ; …
  iapply wpt_seq
  rw [show (5 : Nat) = 4 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_store_eval _ _ empty_annotation intTy _ _ NA _ rfl
    (pv := py) (cv := Vloaded (LVunspecified intTy))
    (symB_eval hex evs (frY_lookup_y hf py)) (unspecIntPe_eval _ _)
  iapply wpt_store _ _ empty_annotation intTy py (Vloaded (LVunspecified intTy)) NA unspecMval
    (intUndefBytes M.tagDefs) _ (Nat.le_refl 3) unspec_encodes (unspec_storable _)
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp1 Hpt
  simp only [SpikeVal.mergeInto]
  -- a1 := bound(pure(Specified(3)))
  rw [show (22 : Nat) = 3 + 19 from rfl]
  iapply wpt_seq_sym
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  iapply wpt_pure _ _ (Nat.le_refl 2) rfl (specIntPe_eval _ _ 3)
  simp only [SpikeVal.val]
  iexists (intVal 3)
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a1SymB lintB]
  -- a2 := bound(let weak (b1, b2) = pure((a1, Specified(1))) in pure(case …))
  rw [show (19 : Nat) = 5 + 14 from rfl]
  iapply wpt_seq_sym
  rw [show (5 : Nat) = 4 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  rw [show (4 : Nat) = 2 + 2 from rfl]
  iapply wpt_wseq_tuple
  iapply wpt_pure _ _ (Nat.le_refl 2) rfl (tuple_eval (symB_eval hex evs (frA1_lookup_a1 hf py))
    (specIntPe_eval _ _ 1))
  iexists [intVal 3, intVal 1]
  isplit
  · ipureintro
    rfl
  rw [show tuplePat [] [leafB b1SymB, leafB b2SymB] =
    tuplePat [] [([], some b1SymB, lintB), ([], some b2SymB, lintB)] from rfl,
    update_env_tuple2 b1SymB b2SymB lintB]
  iapply wpt_pure _ _ (Nat.le_refl 2) rfl (casePe_eval (symB_eval hex evs (frB_lookup_b1 hf py))
    (symB_eval hex evs (frB_lookup_b2 hf py)))
  simp only [SpikeVal.val]
  iexists (intVal 4)
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a2SymB lintB]
  -- bound(store(int, y, a2)) ; …
  rw [show (14 : Nat) = 5 + 9 from rfl]
  iapply wpt_seq
  rw [show (5 : Nat) = 4 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_store_eval _ _ empty_annotation intTy _ _ NA _ rfl
    (pv := py) (cv := intVal 4)
    (symB_eval hex evs (frA2_lookup_y hf py)) (symB_eval hex evs (frA2_lookup_a2 hf py))
  iapply wpt_store _ _ empty_annotation intTy py (intVal 4) NA fourMval _ _
    (Nat.le_refl 3) four_encodes (four_storable _)
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp2 Hpt
  simp only [SpikeVal.mergeInto]
  -- let strong (c1, c2) = pure((Specified(0), a2)) in …
  rw [show (9 : Nat) = 2 + 7 from rfl]
  iapply wpt_seq_tuple
  iapply wpt_pure _ _ (Nat.le_refl 2) rfl (tuple_eval (specIntPe_eval _ _ 0)
    (symB_eval hex evs (frA2_lookup_a2 hf py)))
  iexists [intVal 0, intVal 4]
  isplit
  · ipureintro
    rfl
  rw [show tuplePat [] [leafB c1SymB, leafB c2SymB] =
    tuplePat [] [([], some c1SymB, lintB), ([], some c2SymB, lintB)] from rfl,
    update_env_tuple2 c1SymB c2SymB lintB]
  -- bound(let weak p = pure(y) in load(int, p))
  rw [show (7 : Nat) = 6 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  rw [show (6 : Nat) = 2 + 4 from rfl]
  iapply wpt_wseq_sym
  iapply wpt_pure _ _ (Nat.le_refl 2) rfl (symB_eval hex evs (frC_lookup_y hf py))
  iexists (Vobject (OVpointer py))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym pSymB ptrB]
  icases (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mp $$ Hpt
    with ⟨%id, %a, %hpv, Hcell⟩
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_load_eval _ _ empty_annotation intTy _ NA _ rfl (pv := py)
    (symB_eval hex evs (frP_lookup_p hf py))
  rw [hpv, show (cellPtr id a) = cellPtr id (a + ((0 : Nat) : Int))
    from congrArg (cellPtr id) (by omega)]
  iapply wpt_load_cell_at _ _ empty_annotation id a intTy 0 intTy NA
    (.own 1) (fourBytes M.tagDefs) _ (mv := fourMval) (Nat.le_refl 3) (by omega)
    (fun lum fpm => four_reconstruct lum fpm _) four_loadTrap
  isplitl [Hcell]
  · iexact Hcell
  iintro %fp3 Hcell
  simp only [SpikeVal.val]
  iintro %σ' %ns %κs %nt Hσ
  ihave H := cellOwn_readout M.tagDefs id (.own 1) _ $$ Hcell
  imod H $$ %σ' %ns %κs %nt Hσ with %hcc
  ipureintro
  exact ⟨four_fromMemValue, id, a, hcc⟩

/-! ## THE PRODUCTION ENTRY (the generic route, as exhibit A's) -/

theorem progBE2_labeledAt (sup : Nat) :
    LabeledAt ((initial_core_run_state sup (collect_labeled_continuations_NEW
        (prodFile progBE2))).1)
      mainSym fmapEmpty := by
  unfold LabeledAt
  rw [show ((initial_core_run_state sup (collect_labeled_continuations_NEW
      (prodFile progBE2))).1).labeled =
    collect_labeled_continuations_NEW (prodFile progBE2) from rfl]
  rw [show collect_labeled_continuations_NEW (prodFile progBE2) =
    fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym
      fmapEmpty fmapEmpty from rfl]
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

/-- EXHIBIT B IN THE EMITTED SHAPE, PRODUCTION-ENTRY FORM: the shipped
    pipeline on the synthetic one-procedure file wrapping `progBE2` is
    EXACTLY ONE Active execution; its result value is `Specified(4)` and
    the final memory holds 4's byte image at the program's own fresh cell.
    The statement is exhibit A's (`exhibitA_prod_e1`) verbatim but for the
    program, the value and the budget; the chain is `progBE2_wpt` →
    `wpt_driver_done_alloc` → `prod_run_eqJ`. -/
theorem exhibitB_prod_e2 (sup : Nat) (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFile progBE2) args)
          ((initial_driver_state sup (prodFile progBE2) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = intVal 4 ∧
      (∃ i a : Int, CellCoh fmapEmpty dst'.layout_state i ⟨a, intTy, fourBytes fmapEmpty⟩) ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  have hQe := progBE2_labeledAt sup
  have hnolabel : ∀ (l : sym) (params : List (sym × core_base_type))
      (cont : CoreExpr),
      lookupLabel ((prodCtx (prodFile progBE2) ((initial_core_run_state sup
        (collect_labeled_continuations_NEW (prodFile progBE2))).1)).labelsAt (procCtl mainSym).proc) l =
        some (params, cont) → False := by
    intro l params cont hl
    rw [prodCtx_labels hQe, lookupLabel_empty] at hl
    cases hl
  obtain ⟨dres, dst', heq, hψ, hbl, hout, herr⟩ :=
    prod_run_eqJ sup progBE2 hQe (ψB fmapEmpty) 30
      (wpt_driver_done_alloc (GF := SpikeGF) (ctl := prodCtl sup)
        (M₀ := prodCtx (prodFile progBE2) ((initial_core_run_state sup
          (collect_labeled_continuations_NEW (prodFile progBE2))).1))
        rfl rfl (prodCtx_labels hQe) rfl rfl rfl rfl
        (fun l params cont hl => (hnolabel l params cont hl).elim)
        (fun l params cont hl => (hnolabel l params cont hl).elim)
        (fun _ _ _ _ => iprop(False))
        progBE2 fmapEmpty [] prodMem₀ (∅ : SpikeHeapF SpikeCell)
        (allocCost fmapEmpty intTy 4) progBE2_frag
        (by rw [show lemDefaultFuel = 999999 + 1 from rfl]; decide)
        (prodMem₀_launchCoh _ prod_one_int_budget_fits)
        (ψB fmapEmpty) 30
        (by
          intro inst
          iintro ⟨-, Hcap⟩
          isplitr [Hcap]
          · iapply blockSpecsT_intro fun l params cont _ _ _ _ hl =>
              (hnolabel l params cont hl).elim
          · iapply progBE2_wpt (resolveExtern_id_of_empty (prodCtx_extern _ _)) fmapEmpty []
              symFrame_empty $$ Hcap))
      (by rw [show CerbFuel.driverFuel = 99999999 + 1 from rfl]; omega)
      fs args
  exact ⟨dres, dst', heq, hψ.1, hψ.2, hbl, hout, herr⟩

end CerberusHeapLang
