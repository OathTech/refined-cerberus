/-
CerberusHeapLang.EmittedCExhibit — `x + 1` IN THE EMITTED-CORE SHAPE
(dialect arc E3; the acceptance exhibit of the slice, briefed from
docs/2026-09-04_emitted-core-dialect-design.md §C.3: the impl-defined
integer semantics and the std.core unfolding).

E1 admitted the elaborator's annotations, `bound` and `Ivalignof`; E2 the
loaded-value currency, the pure `case` and the tuple/weak binders; E3 the
arithmetic the elaborator emits for C `int`s — `__conv_int__`,
`catch_exceptional_condition_add` — and the standard-library calls every C
conversion is (`conv_loaded_int` → `conv_int` → `is_representable_integer`,
unfolded through the FILE's `stdlib`, StdCore.lean). This module is t1
(docs/corpus-e0/t1.core: `int x = 3; int y = x + 1; return y;`) in those
features, WITHOUT the one construct E4 owes — the `unseq` that reads `x`
beside `Specified(1)` is a `let weak` read here — and with t1's return
protocol verbatim (`run ret_507(conv_loaded_int(…))`, `save ret_507 …`).
The program is a FAMILY `progCE3 n` over the literal stored into `x`:

```
{-# <exhibitC.c> #-} let strong x: pointer = create(Ivalignof('signed int'), 'signed int') in
let strong a1: loaded integer = {-# §6.5#2 #-} bound(pure(Specified(n))) in
store('signed int', x, conv_loaded_int('signed int', a1)) ;
let strong a2: loaded integer = {-# §6.5#2 #-} bound(let weak p: pointer = pure(x) in load('signed int', p)) in
let strong a3: loaded integer = {-# §6.5#2 #-} bound(
  let weak (b1: loaded integer, b2: loaded integer) = pure((a2, Specified(1))) in
  pure(case (b1, b2) of
       | (Specified(v1: integer), Specified(v2: integer)) =>
           Specified(catch_exceptional_condition_add('signed int',
             __conv_int__('signed int', v1), __conv_int__('signed int', v2)))
       | _: (loaded integer, loaded integer) => undef(<<UB036_exceptional_condition>>)
       end)) in
kill('signed int', x) ;
run ret(conv_loaded_int('signed int', a3)) ;
kill('signed int', x) ;
pure(Unit) ;
save ret: loaded integer (r: loaded integer := Specified(0)) in pure(r)
```

THE POSITIVE RESULT (`exhibitC_prod_e3`): at `n = 3` (t1's literal) the
shipped pipeline on the library-carrying file `prodFileLib stdlibE3 []
(progCE3 3)` is EXACTLY ONE Active execution delivering `Specified(4)`.
Certified through the production lane (`progCE3_wpt → wpt_driver_done_alloc
→ prod_run_eqJ_lib1`); the arithmetic node is discharged by the E3 rule
`wpt_c_add` (IntRules.lean) — the client's obligations are the RANGE
conditions of `int` (3, 1 and 4 are representable) and the selected-branch
equation, all `decide`/`rfl` — and the three conversions by the evaluator
lemma `evalPexpr_convLoadedInt_spec` as operand premises of the generic
ACTION_EVAL/`run` rules (the store's operand, the `run`'s argument).
THE NEGATIVE RESULT is `OverflowExhibit.lean`: the same family at
`n = 2147483647`.

The literal is fixed at 3 because the stored image of a symbolic `int`
has no storability lemma yet (`StorableAt` at `integerValueMval (Signed
Int_) (integerIval n)` is `rfl` at a literal only; docs/2026-09-05_e3-notes.md
§7) — every other step of the derivation is stated at the family.

The production equation requires `30 ≤ LemFuel.fuel`: cost 28 plus two
shipped driver iterations, at the same caller instance. The declared
fragment needs operand depth at most 26, including library unfolding.
This authored E3 regression uses a three-function library fragment; it is not the raw emitted t1
acceptance certificate or the full-file connection required by A7.

A CLIENT of the logic: it reasons through the public rules only.
-/
import CerberusHeapLang.Examples.Layout
import CerberusHeapLang.ProdEntry
import CerberusHeapLang.IntRules
import CerberusHeapLang.AllocExhibit
import CerberusHeapLang.EmittedAExhibit
import CerberusHeapLang.EmittedBExhibit

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Maybe Lem_List

variable {GF : BundledGFunctors}

/-! ## The program -/

def ecFile : String := "exhibitC.c"
def ecPos (l c : Nat) : CerbLocation.Pos := ⟨ecFile, l, c⟩
def ecLoc (l1 c1 l2 c2 : Nat) : CerbLocation.Loc :=
  .region (ecPos l1 c1) (ecPos l2 c2) .noCursor

def xSymC : sym := Symbol "" 701 (SD_ObjectAddress "x")
def a1SymC : sym := Symbol "" 702 (SD_Id "a")
def pSymC : sym := Symbol "" 703 (SD_Id "a")
def a2SymC : sym := Symbol "" 704 (SD_Id "a")
def b1SymC : sym := Symbol "" 705 (SD_Id "a")
def b2SymC : sym := Symbol "" 706 (SD_Id "a")
def v1SymC : sym := Symbol "" 707 (SD_Id "a")
def v2SymC : sym := Symbol "" 708 (SD_Id "a")
def a3SymC : sym := Symbol "" 709 (SD_Id "a")
def retSymC : sym := Symbol "" 710 (SD_Id "ret")
def rSymC : sym := Symbol "" 711 (SD_Id "a")

def lintC : core_base_type := BTy_loaded OTy_integer
def ptrC : core_base_type := BTy_object OTy_pointer
def psymC (x : sym) : generic_pexpr Unit sym := Pexpr [] () (PEsym x)

/-- `Specified(n)` as a pure constructor operand. -/
def lintPe (n : Int) : generic_pexpr Unit sym := Pexpr [] () (PEctor Cspecified [ointPe n])
/-- `conv_loaded_int('signed int', a)` at a bound symbol. -/
def convLoadedIntC (a : sym) : generic_pexpr Unit sym :=
  Pexpr [] () (PEcall (Sym convLoadedIntSym) [Pexpr [] () (PEval (Vctype sintTy)), psymC a])
def leafC (x : sym) : TupleLeaf := ([], some x, lintC)

/-- The location the elaborator puts on the `+` node's `undef` arm (t1's is
    the addition's source range). -/
def ecAddLoc : CerbLocation.Loc := ecLoc 2 36 2 41

/-- The family (the header's program). -/
def progCE3 (n : Int) : CoreExpr :=
  Expr [Aloc (ecLoc 1 15 1 54), Astmt] (Esseq (symPat [] xSymC ptrC)
    (createOpRedex [Aloc (ecLoc 1 15 1 54), Aexpr] (ecLoc 1 15 1 54) empty_annotation
      alignofIntPe intTyPe (PrefSource (ecLoc 1 15 1 54) [xSymC]))
  (Expr [Aloc (ecLoc 1 17 1 27), Astmt] (Esseq (symPat [] a1SymC lintC)
    (Expr [Astd "§6.5#2"] (Ebound (Expr [] (Epure (lintPe n)))))
  (Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
    (storeOpRedex [] (ecLoc 1 17 1 27) empty_annotation intTy (psymC xSymC) (convLoadedIntC a1SymC) NA)
  (Expr [Aloc (ecLoc 1 28 1 42), Astmt] (Esseq (symPat [] a2SymC lintC)
    (Expr [Astd "§6.5#2"] (Ebound
      (Expr [Aloc (ecLoc 1 36 1 37), Aexpr] (Ewseq (symPat [] pSymC ptrC)
        (Expr [] (Epure (psymC xSymC)))
        (loadOpRedex [] (ecLoc 1 36 1 37) empty_annotation intTy (psymC pSymC) NA)))))
  (Expr [Aloc (ecLoc 1 28 1 42), Astmt] (Esseq (symPat [] a3SymC lintC)
    (Expr [Astd "§6.5#2"] (Ebound
      (Expr [Astd "§6.5.6", Aloc (ecLoc 1 36 1 41), Aexpr] (Ewseq (tuplePat [] [leafC b1SymC, leafC b2SymC])
        (Expr [] (Epure (Pexpr [] () (PEctor Ctuple [psymC a2SymC, lintPe 1]))))
        (Expr [] (Epure (cAddPe b1SymC b2SymC v1SymC v2SymC ecAddLoc)))))))
  (Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
    (killOpRedex [] (ecLoc 1 0 1 54) empty_annotation (Static0 intTy) (psymC xSymC))
  (Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
    (Expr [] (Erun empty_annotation retSymC [convLoadedIntC a3SymC]))
  (Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
    (killOpRedex [] (ecLoc 1 0 1 54) empty_annotation (Static0 intTy) (psymC xSymC))
  (Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
    (Expr [] (Epure (Pexpr [] () (PEval Vunit))))
  (Expr [Aloc (ecLoc 1 0 1 54), Astmt]
    (Esave (retSymC, lintC) [(rSymC, ((lintC, none), lintPe 0))]
      (Expr [] (Epure (psymC rSymC))))))))))))))))))))))

/-- The evaluator-fuel bound at an authored operand (its depth is tiny). -/
theorem depLeC [LemFuel] (hfuel : 26 ≤ LemFuel.fuel)
    {pe : generic_pexpr Unit sym} (h : peDepth pe ≤ 26) :
    peDepth pe ≤ LemFuel.fuel := Nat.le_trans h hfuel

theorem peDepth_lintPe (n : Int) : peDepth (lintPe n) = 2 := rfl

/-- Two depth-one arguments plus the loaded conversion's library budget. -/
theorem peDepth_convLoadedIntC (a : sym) : peDepth (convLoadedIntC a) = 26 := rfl

/-- The label body's registration: `save ret … in pure(r)` registers
    `ret ↦ ([(r, loaded integer)], pure(r))`. -/
def retQ : LabelMap :=
  fmapAddBy symCmpL retSymC ([(rSymC, lintC)], Expr [] (Epure (psymC rSymC))) fmapEmpty

theorem retQ_lookup : lookupLabel retQ retSymC = some ([(rSymC, lintC)], Expr [] (Epure (psymC rSymC))) := by
  unfold lookupLabel retQ
  rw [fmapLookupBy_addBy_empty, if_pos (by decide +kernel)]

theorem retQ_inv {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel retQ l = some (params, cont)) :
    params = [(rSymC, lintC)] ∧ cont = Expr [] (Epure (psymC rSymC)) := by
  unfold lookupLabel retQ at h
  rw [fmapLookupBy_addBy_empty] at h
  split at h
  · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    exact ⟨h1.symm ▸ rfl, h2.symm ▸ rfl⟩
  · cases h

/-! ## Cone membership (the whole family) -/

theorem progCE3_frag [LemFuel] (hfuel : 26 ≤ LemFuel.fuel) (n : Int) : Frag (progCE3 n) :=
  .sseq_sym
    (.create_op rfl (.ctorTy [] Civalignof rfl [] intTy) (.val [] (Vctype intTy))
      (depLeC (by omega) (by decide)) (peDepth_val_le _ _ (by omega)))
    (.sseq_sym
      (.bound (.pure_op rfl (PePure.of_isPePure rfl) (depLeC (by omega) (by rw [peDepth_lintPe]; decide))))
      (.sseq
        (.store_op rfl (.sym [] xSymC) (PePure.of_isPePure rfl) (depLeC (by omega) (by decide)) (depLeC (by omega) (by decide)))
        (.sseq_sym
          (.bound (.wseq_sym
            (.pure_op rfl (.sym [] xSymC) (depLeC (by omega) (by decide)))
            (.load_op rfl (.sym [] pSymC) (depLeC (by omega) (by decide)))))
          (.sseq_sym
            (.bound (.wseq_tuple
              (.pure_op rfl (PePure.of_isPePure rfl) (depLeC (by omega) (by decide)))
              (.pure_op rfl (PePure.of_isPePure rfl) (depLeC (by omega) (by decide)))))
            (.sseq
              (.kill_op rfl (.sym [] xSymC) (depLeC (by omega) (by decide)))
              (.sseq
                (.run (fun pe h => by rcases List.mem_singleton.mp h with rfl; exact PePure.of_isPePure rfl)
                  (fun pe h => by rcases List.mem_singleton.mp h with rfl; exact depLeC (by omega) (by decide)))
                (.sseq
                  (.kill_op rfl (.sym [] xSymC) (depLeC (by omega) (by decide)))
                  (.sseq (.val_pure Vunit)
                    (.save (fun pe h => by rcases List.mem_singleton.mp h with rfl; exact PePure.of_isPePure rfl)
                      (fun pe h => by rcases List.mem_singleton.mp h with rfl; exact depLeC (by omega) (by decide))
                      (.pure_op rfl (.sym [] rSymC) (depLeC (by omega) (by decide))))))))))))

/-! ## The evaluator at the program's operands -/

theorem lintPe_eval [LemFuel] {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym}
    {file : generic_file Unit core_run_annotation} (ρ : EnvStack) (n : Int) :
    evalPexpr tds ext file ρ (lintPe n) = some (lint n) := by
  rw [lintPe, evalPexpr_ctor1, ointPe, evalPexpr_val]
  rfl

/-- The ctype operand of every conversion. -/
theorem sintTyPeC_eval [LemFuel] {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym}
    {file : generic_file Unit core_run_annotation} (ρ : EnvStack) :
    evalPexpr tds ext file ρ (Pexpr [] () (PEval (Vctype sintTy))) = some (Vctype sintTy) := by
  rw [evalPexpr_val]

/-- `conv_loaded_int('signed int', a)` at a bound in-range `Specified(n)`:
    the identity (the E3 evaluator lemma at the program's operand shape). -/
theorem convLoadedIntC_eval [LemFuel] {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym}
    {file : generic_file Unit core_run_annotation} (hstd : StdE3 file) {ρ : EnvStack}
    {a : sym} {n : Int} (hv : evalPexpr tds ext file ρ (psymC a) = some (lint n))
    (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    evalPexpr tds ext file ρ (convLoadedIntC a) = some (lint n) :=
  evalPexpr_convLoadedInt_spec [] hstd (sintTyPeC_eval ρ) hv h1 h2

/-- The symbol operand at a frame whose lookup is known. -/
theorem symC_eval [LemFuel] {M : MachineCtx} (hex : ∀ x, resolveExtern M.extern x = x)
    {x : sym} {f : Fmap sym value} {v : value} (evs : List (Fmap sym value))
    (hl : fmapLookupBy symCmpK x f = some v) :
    evalPexpr M.tagDefs M.extern M.file (f :: evs) (psymC x) = some v := by
  rw [psymC, evalPexpr_sym_of_resolve _ _ _ (hex _)]
  exact lookup_env_head hl evs

/-- The selected branch of the `+` at `(Specified(3), Specified(1))`: the
    engine's `select_case`/`subst_sym_pexpr` at the concrete row (computed,
    the obligation `wpt_c_add` leaves to the client). -/
theorem cAdd_select_31 :
    select_case subst_sym_pexpr (Vtuple [lint 3, lint 1]) (cAddPats v1SymC v2SymC ecAddLoc) =
      some (cAddBranch 3 1) := rfl

/-! ## The values at the cell -/

def threeMval : CerbMem.MemValue :=
  CerbMem.integerValueMval (.Signed .Int_) (CerbMem.integerIval 3)

abbrev threeBytes (tds : CerbTags.TagDefsMap) : List CerbMem.AbsByte :=
  (CerbMem.memValueToBytes tds [] threeMval).2

theorem three_encodes [LemFuel] :
    memValueFromValue fmapEmpty (Ctype [] (unatomic_ intTy)) (lint 3) = some threeMval := rfl

theorem three_storable (tds : CerbTags.TagDefsMap) : StorableAt tds intTy threeMval :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

theorem three_reconstruct {tds : CerbTags.TagDefsMap} (lum : List (Int × identifier))
    (fpm : CerbMem.Funptrmap) (a : Int) :
    CerbMem.reconstructValue tds lum fpm (a + ((0 : Nat) : Int)) intTy
      (((threeBytes tds).drop 0).take (CerbMem.sizeofCtype tds intTy)) = threeMval := by
  rw [show a + ((0 : Nat) : Int) = a by omega]
  rfl

theorem three_fromMemValue : (valueFromMemValue threeMval).2 = lint 3 := rfl

theorem three_loadTrap : loadTrapV intTy threeMval = false := rfl

/-! ## The environment frames and their lookups -/

abbrev frXC (px : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd xSymC (Vobject (OVpointer px)) f
abbrev frA1C (px : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd a1SymC (lint 3) (frXC px f)
abbrev frPC (px : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd pSymC (Vobject (OVpointer px)) (frA1C px f)
abbrev frA2C (px : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd a2SymC (lint 3) (frPC px f)
abbrev frBC (px : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd b1SymC (lint 3) (envAdd b2SymC (lint 1) (frA2C px f))
abbrev frA3C (px : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd a3SymC (lint 4) (frBC px f)

theorem frXC_symFrame {f : Fmap sym value} (hf : SymFrame f) (px : CerbMem.PointerValue) :
    SymFrame (frXC px f) := hf.add _ _
theorem frA1C_symFrame {f : Fmap sym value} (hf : SymFrame f) (px : CerbMem.PointerValue) :
    SymFrame (frA1C px f) := (frXC_symFrame hf px).add _ _
theorem frPC_symFrame {f : Fmap sym value} (hf : SymFrame f) (px : CerbMem.PointerValue) :
    SymFrame (frPC px f) := (frA1C_symFrame hf px).add _ _
theorem frA2C_symFrame {f : Fmap sym value} (hf : SymFrame f) (px : CerbMem.PointerValue) :
    SymFrame (frA2C px f) := (frPC_symFrame hf px).add _ _
theorem frBC_symFrame {f : Fmap sym value} (hf : SymFrame f) (px : CerbMem.PointerValue) :
    SymFrame (frBC px f) := ((frA2C_symFrame hf px).add _ _).add _ _

theorem frXC_lookup_x {f : Fmap sym value} (hf : SymFrame f) (px : CerbMem.PointerValue) :
    fmapLookupBy symCmpK xSymC (frXC px f) = some (Vobject (OVpointer px)) := by
  unfold frXC
  rw [envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]
theorem frA1C_lookup_a1 {f : Fmap sym value} (hf : SymFrame f) (px : CerbMem.PointerValue) :
    fmapLookupBy symCmpK a1SymC (frA1C px f) = some (lint 3) := by
  unfold frA1C
  rw [envAdd_lookup (frXC_symFrame hf px) symCmpK, if_pos (by decide +kernel)]
theorem frA1C_lookup_x {f : Fmap sym value} (hf : SymFrame f) (px : CerbMem.PointerValue) :
    fmapLookupBy symCmpK xSymC (frA1C px f) = some (Vobject (OVpointer px)) := by
  unfold frA1C
  rw [envAdd_lookup (frXC_symFrame hf px) symCmpK, if_neg (by decide +kernel), frXC_lookup_x hf px]
theorem frPC_lookup_p {f : Fmap sym value} (hf : SymFrame f) (px : CerbMem.PointerValue) :
    fmapLookupBy symCmpK pSymC (frPC px f) = some (Vobject (OVpointer px)) := by
  unfold frPC
  rw [envAdd_lookup (frA1C_symFrame hf px) symCmpK, if_pos (by decide +kernel)]
theorem frA2C_lookup_a2 {f : Fmap sym value} (hf : SymFrame f) (px : CerbMem.PointerValue) :
    fmapLookupBy symCmpK a2SymC (frA2C px f) = some (lint 3) := by
  unfold frA2C
  rw [envAdd_lookup (frPC_symFrame hf px) symCmpK, if_pos (by decide +kernel)]
theorem frBC_lookup_b1 {f : Fmap sym value} (hf : SymFrame f) (px : CerbMem.PointerValue) :
    fmapLookupBy symCmpK b1SymC (frBC px f) = some (lint 3) := by
  unfold frBC
  rw [envAdd_lookup ((frA2C_symFrame hf px).add _ _) symCmpK, if_pos (by decide +kernel)]
theorem frBC_lookup_b2 {f : Fmap sym value} (hf : SymFrame f) (px : CerbMem.PointerValue) :
    fmapLookupBy symCmpK b2SymC (frBC px f) = some (lint 1) := by
  unfold frBC
  rw [envAdd_lookup ((frA2C_symFrame hf px).add _ _) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (frA2C_symFrame hf px) symCmpK, if_pos (by decide +kernel)]
theorem frA3C_lookup_a3 {f : Fmap sym value} (hf : SymFrame f) (px : CerbMem.PointerValue) :
    fmapLookupBy symCmpK a3SymC (frA3C px f) = some (lint 4) := by
  unfold frA3C
  rw [envAdd_lookup (frBC_symFrame hf px) symCmpK, if_pos (by decide +kernel)]
theorem frA3C_lookup_x {f : Fmap sym value} (hf : SymFrame f) (px : CerbMem.PointerValue) :
    fmapLookupBy symCmpK xSymC (frA3C px f) = some (Vobject (OVpointer px)) := by
  unfold frA3C frBC frA2C frPC
  rw [envAdd_lookup (frBC_symFrame hf px) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup ((frA2C_symFrame hf px).add _ _) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (frA2C_symFrame hf px) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (frPC_symFrame hf px) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (frA1C_symFrame hf px) symCmpK, if_neg (by decide +kernel), frA1C_lookup_x hf px]

/-- `bindArgs` at the label's one parameter. -/
theorem retQ_bindArgs (v : value) (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindArgs [(rSymC, lintC)] [v] (f :: rest) = envAdd rSymC v f :: rest := by
  show update_env (mk_sym_pat rSymC lintC) v (f :: rest) = _
  rw [update_env_cons, update_env_aux_sym]

theorem frR_lookup_r {f : Fmap sym value} (hf : SymFrame f) (v : value) :
    fmapLookupBy symCmpK rSymC (envAdd rSymC v f) = some v := by
  rw [envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]

/-! ## THE PARTIAL JUDGMENT: the label specification and the whole program -/

/-- The partial-lane label specification of `ret`: entered with the
    delivered value `Specified(4)` at a symbol-keyed frame. -/
def cLs (GF : BundledGFunctors) [SpikeGS .hasLC GF] : LabelSpec GF := fun l vs ρ =>
  iprop(⌜symOrd l retSymC = .eq ∧ vs = [lint 4] ∧ ∃ f rest, ρ = f :: rest ∧ SymFrame f⌝)

/-- The partial post: the delivered value is BARE `Specified(4)` (the cell
    was killed before the jump, so no heap resource is delivered). -/
def ψCE3s (GF : BundledGFunctors) [SpikeGS .hasLC GF] : SpikeVal → EnvStack → IProp GF :=
  fun w _ => iprop(⌜w = SpikeVal.pure (lint 4)⌝)

/-- The partial block specification of `ret`: its body `pure(r)` delivers
    the bound value. -/
theorem progCE3_blockSpecs [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} (hex : ∀ x, resolveExtern M.extern x = x)
    (hQ : M.labelsAt p = retQ) :
    ⊢ blockSpecs (GF := GF) M p (cLs GF) emptyProcSpec (ψCE3s GF) := by
  refine blockSpecs_intro fun l params cont vs ev0 evs hl => ?_
  rw [hQ] at hl
  obtain ⟨rfl, rfl⟩ := retQ_inv hl
  dsimp only [cLs]
  iintro %hpure
  obtain ⟨-, rfl, f, rest, hρ, hf⟩ := hpure
  cases hρ
  rw [retQ_bindArgs]
  iapply wps_pure _ _ rfl (symC_eval hex _ (frR_lookup_r hf (lint 4)))
  dsimp only [ψCE3s]
  ipureintro
  rfl

/-- THE WHOLE PROGRAM at `n = 3`, PARTIAL judgment (the same derivation
    as `progCE3_wpt` without the budget arithmetic; the `+` by `wps_c_add`). -/
theorem progCE3_wps [LemFuel] (hfuel : 0 < LemFuel.fuel) [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} (hstd : StdE3 M.file)
    (hex : ∀ x, resolveExtern M.extern x = x) (hQ : M.labelsAt p = retQ)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (hf : SymFrame ev0) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs intTy 4)) ⊢
      wps M p (cLs GF) emptyProcSpec (ψCE3s GF) (progCE3 3) (ev0 :: evs) := by
  iintro Hcap
  unfold progCE3
  -- x := create(Ivalignof(int), int)
  iapply wps_seq_sym
  iapply wps_create_eval _ _ empty_annotation alignofIntPe intTyPe (PrefSource (ecLoc 1 15 1 54) [xSymC])
    (ev0 :: evs) (align := CerbMem.alignofIval M.tagDefs intTy) (ty := intTy) rfl
    (alignofIntPe_eval _ _) (evalPexpr_val _ _ _ _ _)
  rw [alignofIval_intTy]
  iapply wps_create (hfuel := hfuel) (halign := by decide) (haddr := rfl) _ _ empty_annotation .Prov_none 4 intTy (PrefSource (ecLoc 1 15 1 54) [xSymC])
    (ev0 :: evs) intTy_size_pos intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [Hcap]
  · iexact Hcap
  iintro %px ⟨Hpt, -⟩
  iexists (Vobject (OVpointer px))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym xSymC ptrC]
  -- a1 := bound(pure(Specified(3)))
  iapply wps_seq_sym
  iapply wps_bound _ _ _ rfl
  iapply wps_pure _ _ rfl (lintPe_eval _ 3)
  simp only [SpikeVal.val]
  iexists (lint 3)
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a1SymC lintC]
  -- store(int, x, conv_loaded_int(int, a1)) ; …
  iapply wps_seq
  iapply wps_store_eval _ _ empty_annotation intTy _ _ NA _ rfl
    (pv := px) (cv := lint 3)
    (symC_eval hex evs (frA1C_lookup_x hf px))
    (convLoadedIntC_eval hstd (symC_eval hex evs (frA1C_lookup_a1 hf px)) (by decide) (by decide))
  iapply wps_store _ _ empty_annotation intTy px (lint 3) NA threeMval
    (List.replicate (CerbMem.sizeofCtype M.tagDefs intTy) undefByte) _
    three_encodes (three_storable _)
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp1 Hpt
  simp only [SpikeVal.mergeInto]
  -- a2 := bound(let weak p = pure(x) in load(int, p))
  iapply wps_seq_sym
  iapply wps_bound _ _ _ rfl
  iapply wps_wseq_sym
  iapply wps_pure _ _ rfl (symC_eval hex evs (frA1C_lookup_x hf px))
  iexists (Vobject (OVpointer px))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym pSymC ptrC]
  icases (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mp $$ Hpt
    with ⟨%id, %a, %hpv, Hcell⟩
  iapply wps_load_eval _ _ empty_annotation intTy _ NA _ rfl (pv := px)
    (symC_eval hex evs (frPC_lookup_p hf px))
  rw [hpv, show (cellPtr id a) = cellPtr id (a + ((0 : Nat) : Int))
    from congrArg (cellPtr id) (by omega)]
  iapply wps_load_cell_at _ _ empty_annotation id a intTy 0 intTy NA
    (.own 1) (threeBytes M.tagDefs) _ (mv := threeMval) (by omega)
    (fun lum fpm => three_reconstruct lum fpm _) three_loadTrap
  isplitl [Hcell]
  · iexact Hcell
  iintro %fp2 Hcell
  simp only [SpikeVal.val]
  rw [three_fromMemValue,
    show cellPtr id (a + ((0 : Nat) : Int)) = cellPtr id a from congrArg (cellPtr id) (by omega), ← hpv]
  iexists (lint 3)
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a2SymC lintC]
  -- a3 := bound(let weak (b1, b2) = pure((a2, Specified(1))) in pure(x + y))
  iapply wps_seq_sym
  iapply wps_bound _ _ _ rfl
  iapply wps_wseq_tuple
  iapply wps_pure _ _ rfl
    (by rw [evalPexpr_ctor2, symC_eval hex evs (frA2C_lookup_a2 hf px), lintPe_eval _ 1]; rfl)
  iexists [lint 3, lint 1]
  isplit
  · ipureintro
    rfl
  rw [show tuplePat [] [leafC b1SymC, leafC b2SymC] =
    tuplePat [] [([], some b1SymC, lintC), ([], some b2SymC, lintC)] from rfl,
    update_env_tuple2 b1SymC b2SymC lintC]
  -- THE C `+`: the E3 rule at the frame (partial stratum)
  iapply wps_c_add b1SymC b2SymC v1SymC v2SymC ecAddLoc _
    (symC_eval hex evs (frBC_lookup_b1 hf px)) (symC_eval hex evs (frBC_lookup_b2 hf px))
    cAdd_select_31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [SpikeVal.val]
  iexists (lint 4)
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a3SymC lintC]
  -- kill(int, x) ; run ret(conv_loaded_int(int, a3)) ; …
  iapply wps_seq
  iapply wps_kill_eval _ _ empty_annotation (Static0 intTy) _ _ rfl (pv := px)
    (symC_eval hex evs (frA3C_lookup_x hf px))
  rw [hpv]
  iapply wps_kill_emp _ _ empty_annotation (Static0 intTy) (cellPtr id a) intTy
    (threeBytes M.tagDefs) _ rfl
  isplitl [Hcell]
  · iapply (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mpr
    iexists id, a
    isplit
    · ipureintro
      rfl
    · iexact Hcell
  simp only [SpikeVal.mergeInto]
  rw [← hpv]
  iapply wps_seq
  iapply wps_run [] empty_annotation retSymC [convLoadedIntC a3SymC] _ _
    (by rw [hQ]; exact retQ_lookup)
    (by rw [evalPexprs_cons, convLoadedIntC_eval hstd (symC_eval hex evs (frA3C_lookup_a3 hf px))
          (by decide) (by decide), evalPexprs_nil]; rfl)
  dsimp only [cLs]
  ipureintro
  exact ⟨by decide +kernel, rfl, _, _, rfl, (frBC_symFrame hf px).add _ _⟩

/-! ## The `conv_loaded_int` PURE node at both strata (the rules
`wps_conv_loaded_int`/`wpt_conv_loaded_int` as a client uses them: the
elaborator emits `pure(conv_loaded_int(ty, a))` where a C conversion is a
full expression of its own — e.g. `return (int)x;` — a node the exhibit's
program does not contain; these two lemmas are the structurally-forcing
consumers at a frame binding `a ↦ Specified(n)`). -/

theorem convLoadedInt_pure_wps [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpec GF} {Θ : ProcSpec GF}
    {Ψ : SpikeVal → EnvStack → IProp GF} (hstd : StdE3 M.file)
    (hex : ∀ x, resolveExtern M.extern x = x) {a : sym} {n : Int}
    (f : Fmap sym value) (evs : List (Fmap sym value))
    (hl : fmapLookupBy symCmpK a f = some (lint n))
    (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    Ψ (.pure (lint n)) (f :: evs) ⊢
      wps M p Ls Θ Ψ (Expr [] (Epure (convLoadedIntC a))) (f :: evs) :=
  wps_conv_loaded_int _ _ _ hstd (sintTyPeC_eval _) (symC_eval hex evs hl) h1 h2

theorem convLoadedInt_pure_wpt [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF} (hstd : StdE3 M.file)
    (hex : ∀ x, resolveExtern M.extern x = x) {a : sym} {n : Int} {k : Nat} (hk : 2 ≤ k)
    (f : Fmap sym value) (evs : List (Fmap sym value))
    (hl : fmapLookupBy symCmpK a f = some (lint n))
    (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    Ψ (.pure (lint n)) (f :: evs) ⊢
      wpt M p Ls Θ k Ψ (Expr [] (Epure (convLoadedIntC a))) (f :: evs) :=
  wpt_conv_loaded_int _ _ _ hk hstd (sintTyPeC_eval _) (symC_eval hex evs hl) h1 h2

/-! ## THE TOTAL JUDGMENT: the label specification and the whole program -/

/-- The label specification of `ret`: entered with the delivered value
    `Specified(4)` at budget 2 (its body is one PURE round and a delivery). -/
def cLsT (GF : BundledGFunctors) [SpikeGS .hasLC GF] : LabelSpecT GF := fun l m vs ρ =>
  iprop(⌜symOrd l retSymC = .eq ∧ m = 2 ∧ vs = [lint 4] ∧ ∃ f rest, ρ = f :: rest ∧ SymFrame f⌝)

/-- The post: the delivered value is `Specified(4)`. -/
def ψCE3 : value → Mem → Prop := fun v _ => v = lint 4

theorem cLsT_readout [LemFuel] [SpikeGS .hasLC GF] :
    ∀ w ρ', iprop(⌜w = SpikeVal.pure (lint 4)⌝) ⊢ readoutPost (GF := GF) ψCE3 w ρ' := by
  intro w ρ'
  iintro %hw
  iintro %σ' %ns %κs %nt -
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  subst hw
  rfl

/-- THE BLOCK SPECIFICATION of `ret`: its body `pure(r)` delivers the
    bound value within budget 2. -/
theorem progCE3_blockSpecsT [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} (hex : ∀ x, resolveExtern M.extern x = x)
    (hQ : M.labelsAt p = retQ) :
    ⊢ blockSpecsT (GF := GF) M p (cLsT GF) emptyProcSpecT (readoutPost ψCE3) := by
  refine blockSpecsT_intro fun l params cont vs ev0 evs m hl => ?_
  rw [hQ] at hl
  obtain ⟨rfl, rfl⟩ := retQ_inv hl
  dsimp only [cLsT]
  iintro %hpure
  obtain ⟨-, rfl, rfl, f, rest, hρ, hf⟩ := hpure
  cases hρ
  rw [retQ_bindArgs]
  iapply wpt_pure _ _ (Nat.le_refl 2) rfl
    (symC_eval hex _ (frR_lookup_r hf (lint 4)))
  iapply cLsT_readout
  ipureintro
  rfl

/-- THE WHOLE PROGRAM at `n = 3`, total judgment, budget 28: from the
    allocation budget of one `int` cell to the readout `Specified(4)`. -/
theorem progCE3_wpt [LemFuel] (hfuel : 0 < LemFuel.fuel) [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} (hstd : StdE3 M.file)
    (hex : ∀ x, resolveExtern M.extern x = x) (hQ : M.labelsAt p = retQ)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (hf : SymFrame ev0) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs intTy 4)) ⊢
      wpt M p (cLsT GF) emptyProcSpecT 28 (readoutPost ψCE3) (progCE3 3) (ev0 :: evs) := by
  iintro Hcap
  unfold progCE3
  -- x := create(Ivalignof(int), int)
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 25
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_create_eval _ _ empty_annotation alignofIntPe intTyPe (PrefSource (ecLoc 1 15 1 54) [xSymC])
    (ev0 :: evs) (align := CerbMem.alignofIval M.tagDefs intTy) (ty := intTy) rfl
    (alignofIntPe_eval _ _) (evalPexpr_val _ _ _ _ _)
  rw [alignofIval_intTy]
  iapply wpt_create (hfuel := hfuel) (halign := by decide) (haddr := rfl) _ _ empty_annotation .Prov_none 4 intTy (PrefSource (ecLoc 1 15 1 54) [xSymC])
    (ev0 :: evs) (Nat.le_refl 2) intTy_size_pos intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [Hcap]
  · iexact Hcap
  iintro %px ⟨Hpt, -⟩
  iexists (Vobject (OVpointer px))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym xSymC ptrC]
  -- a1 := bound(pure(Specified(3)))
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 22
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl
  iapply wpt_pure _ _ (Nat.le_refl 2) rfl (lintPe_eval _ 3)
  simp only [SpikeVal.val]
  iexists (lint 3)
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a1SymC lintC]
  -- store(int, x, conv_loaded_int(int, a1)) ; …
  iapply wpt_seq _ _ _ _ _ _ _ 4 18
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_store_eval _ _ empty_annotation intTy _ _ NA _ rfl
    (pv := px) (cv := lint 3)
    (symC_eval hex evs (frA1C_lookup_x hf px))
    (convLoadedIntC_eval hstd (symC_eval hex evs (frA1C_lookup_a1 hf px)) (by decide) (by decide))
  iapply wpt_store _ _ empty_annotation intTy px (lint 3) NA threeMval
    (List.replicate (CerbMem.sizeofCtype M.tagDefs intTy) undefByte) _ (Nat.le_refl 3)
    three_encodes (three_storable _)
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp1 Hpt
  simp only [SpikeVal.mergeInto]
  -- a2 := bound(let weak p = pure(x) in load(int, p))
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 7 11
  rw [show (7 : Nat) = 6 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl
  iapply wpt_wseq_sym _ _ _ _ _ _ _ _ 2 4
  iapply wpt_pure _ _ (Nat.le_refl 2) rfl (symC_eval hex evs (frA1C_lookup_x hf px))
  iexists (Vobject (OVpointer px))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym pSymC ptrC]
  icases (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mp $$ Hpt
    with ⟨%id, %a, %hpv, Hcell⟩
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_load_eval _ _ empty_annotation intTy _ NA _ rfl (pv := px)
    (symC_eval hex evs (frPC_lookup_p hf px))
  rw [hpv, show (cellPtr id a) = cellPtr id (a + ((0 : Nat) : Int))
    from congrArg (cellPtr id) (by omega)]
  iapply wpt_load_cell_at _ _ empty_annotation id a intTy 0 intTy NA
    (.own 1) (threeBytes M.tagDefs) _ (mv := threeMval) (Nat.le_refl 3) (by omega)
    (fun lum fpm => three_reconstruct lum fpm _) three_loadTrap
  isplitl [Hcell]
  · iexact Hcell
  iintro %fp2 Hcell
  simp only [SpikeVal.val]
  rw [three_fromMemValue,
    show cellPtr id (a + ((0 : Nat) : Int)) = cellPtr id a from congrArg (cellPtr id) (by omega), ← hpv]
  iexists (lint 3)
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a2SymC lintC]
  -- a3 := bound(let weak (b1, b2) = pure((a2, Specified(1))) in pure(x + y))
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 5 6
  rw [show (5 : Nat) = 4 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl
  iapply wpt_wseq_tuple _ _ _ _ _ _ _ 2 2
  iapply wpt_pure _ _ (Nat.le_refl 2) rfl
    (by rw [evalPexpr_ctor2, symC_eval hex evs (frA2C_lookup_a2 hf px), lintPe_eval _ 1]; rfl)
  iexists [lint 3, lint 1]
  isplit
  · ipureintro
    rfl
  rw [show tuplePat [] [leafC b1SymC, leafC b2SymC] =
    tuplePat [] [([], some b1SymC, lintC), ([], some b2SymC, lintC)] from rfl,
    update_env_tuple2 b1SymC b2SymC lintC]
  -- THE C `+`: the E3 rule at the frame
  iapply wpt_c_add b1SymC b2SymC v1SymC v2SymC ecAddLoc _ (Nat.le_refl 2)
    (symC_eval hex evs (frBC_lookup_b1 hf px)) (symC_eval hex evs (frBC_lookup_b2 hf px))
    cAdd_select_31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [SpikeVal.val]
  iexists (lint 4)
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a3SymC lintC]
  -- kill(int, x) ; run ret(conv_loaded_int(int, a3)) ; …
  iapply wpt_seq _ _ _ _ _ _ _ 3 3
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_kill_eval _ _ empty_annotation (Static0 intTy) _ _ rfl (pv := px)
    (symC_eval hex evs (frA3C_lookup_x hf px))
  rw [hpv]
  iapply wpt_kill_emp _ _ empty_annotation (Static0 intTy) (cellPtr id a) intTy
    (threeBytes M.tagDefs) _ (Nat.le_refl 2) rfl
  isplitl [Hcell]
  · iapply (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mpr
    iexists id, a
    isplit
    · ipureintro
      rfl
    · iexact Hcell
  simp only [SpikeVal.mergeInto]
  rw [← hpv]
  iapply wpt_seq _ _ _ _ _ _ _ 3 0
  iapply wpt_run [] empty_annotation retSymC [convLoadedIntC a3SymC] _ _ 2
    (by rw [hQ]; exact retQ_lookup)
    (by rw [evalPexprs_cons, convLoadedIntC_eval hstd (symC_eval hex evs (frA3C_lookup_a3 hf px))
          (by decide) (by decide), evalPexprs_nil]; rfl)
    (Nat.le_refl 3)
  dsimp only [cLsT]
  ipureintro
  exact ⟨by decide +kernel, rfl, rfl, _, _, rfl, (frBC_symFrame hf px).add _ _⟩

/-! ## THE PRODUCTION ENTRY (the generic route over the library-carrying file) -/

/-- The whole-file registration at the production initial run state: the
    shipped `collect_labeled_continuations_NEW` on `prodFileLib stdlibE3 []
    (progCE3 3)` registers exactly `ret` for `main` (the library's `Fun`s
    register nothing). -/
theorem collect_new_progCE3 :
    collect_labeled_continuations_NEW (prodFileLib stdlibE3 [] (progCE3 3)) =
      fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym retQ fmapEmpty := rfl

theorem progCE3_labeledAt (sup : Nat) :
    LabeledAt (prodRSLib stdlibE3 [] sup (progCE3 3)) mainSym retQ := by
  unfold LabeledAt
  rw [prodRSLib_labeled, collect_new_progCE3, fmapLookupBy_addBy_empty, if_pos (by decide +kernel)]

/-- `main` is not a name of the transcribed library. -/
theorem stdlibE3_no_main :
    fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) mainSym stdlibE3 =
      none := by
  unfold stdlibE3
  rw [symAdd_lookup ((symMap_empty.add _ _).add _ _), if_neg (by decide +kernel),
    symAdd_lookup (symMap_empty.add _ _), if_neg (by decide +kernel),
    symAdd_lookup symMap_empty, if_neg (by decide +kernel)]
  rfl

/-- `x + 1` IN THE EMITTED SHAPE, PRODUCTION-ENTRY FORM (E3's acceptance
    exhibit): the shipped pipeline on the library-carrying one-procedure
    file wrapping `progCE3 3` is EXACTLY ONE Active execution; its result
    value is `Specified(4)`. The statement is exhibit B's
    (`exhibitB_prod_e2`) but for the file (it carries the transcribed
    std.core fragment `stdlibE3`), the program and the value; the chain is
    `progCE3_wpt → wpt_driver_done_alloc → prod_run_eqJ_lib1`. -/
theorem exhibitC_prod_e3 [LemFuel] (hfuel : 30 ≤ LemFuel.fuel) (sup : Nat) (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFileLib stdlibE3 [] (progCE3 3)) args)
          ((initial_driver_state sup (prodFileLib stdlibE3 [] (progCE3 3)) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = lint 4 ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  have hQe := progCE3_labeledAt sup
  have hlbl := prodCtx_labels (f := prodFileLib stdlibE3 [] (progCE3 3)) hQe
  obtain ⟨dres, dst', heq, hψ, hbl, hout, herr⟩ :=
    prod_run_eqJ_lib1 sup stdlibE3 (progCE3 3) hQe ψCE3 28
      (wpt_driver_done_alloc (hfuel := by omega) (GF := SpikeGF) (ctl := prodCtl sup)
        (M₀ := prodCtx (prodFileLib stdlibE3 [] (progCE3 3)) (prodRSLib stdlibE3 [] sup (progCE3 3)))
        rfl rfl hlbl rfl rfl rfl rfl (Nat.le_refl _)
        (fun l params cont hl => by
          rw [hlbl] at hl
          obtain ⟨-, rfl⟩ := retQ_inv hl
          exact .pure_op rfl (.sym [] rSymC) (depLeC (by omega) (by decide)))
        (cLsT SpikeGF)
        (progCE3 3) fmapEmpty [] prodMem₀ (∅ : SpikeHeapF SpikeCell)
        (allocCost fmapEmpty intTy 4) (progCE3_frag (by omega) 3)
        (prodMem₀_launchCoh _ prod_one_int_budget_fits)
        ψCE3 28
        (by
          intro inst
          iintro ⟨-, Hcap⟩
          isplitr [Hcap]
          · iapply progCE3_blockSpecsT (resolveExtern_id_of_empty (prodCtx_extern _ _)) hlbl
          · iapply progCE3_wpt (hfuel := by omega) (M := prodCtx (prodFileLib stdlibE3 [] (progCE3 3)) (prodRSLib stdlibE3 [] sup (progCE3 3))) rfl (resolveExtern_id_of_empty (prodCtx_extern _ _)) hlbl fmapEmpty []
              symFrame_empty $$ Hcap))
      (by omega)
      fs args
  exact ⟨dres, dst', heq, hψ, hbl, hout, herr⟩

end CerberusHeapLang
