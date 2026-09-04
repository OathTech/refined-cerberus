/-
CerberusHeapLang.TwoLabelExhibit — TWO `save` LABELS IN ONE PROCEDURE BODY
(hygiene slice H1b, 2026-09-04, docs/2026-09-04_h1-notes.md; the item
KNOWN-OPEN-ITEMS B8 / ARCHITECTURE §7 carried since the K5 range audit:
every loop exhibit was single-label — the malloc'd list merges its two C
loops into one Core label with two phases — and the two-entry lookup law
the two-label form needs, `symAdd_lookup_two`, landed at C4 with no
exhibit).

THE PROGRAM (authored Core, all metadata quantified): two sequential
counted loops over ONE cell, the second entered from the first's exit —

    save l1: (x : integer := n₁) in
      if (x > 0) then lets _ = store(int, c, 5) in run l1(x - 1)
      else save l2: (y : integer := n₂) in
             if (y > 0) then lets _ = store(int, c, 6) in run l2(y - 1)
             else pure(Unit)

- Core `save` labels are procedure-scoped: the second loop's `save` sits in
  the first's exit branch, so the procedure's label map has TWO entries,
  `l1 ↦ ([(x, xbty)], body1)` and `l2 ↦ ([(y, ybty)], body2)` — the
  two-entry `symAdd` chain `tlQ` whose lookups are `symAdd_lookup_two`
  (EnvLaws; the `LabeledAt` tie of the run state is `symAdd_lookup`).
- THE LABEL SPECIFICATION IS LABEL-DEPENDENT for the first time (`tlLs`,
  `tlLsT`: a Lean `if` on `symOrd l tlL2Sym = .eq` selects the second
  loop's invariant, else the first's); `wps_run`/`wps_save` and
  `wpt_run`/`wpt_save` are label-generic — NO RULE OR JUDGMENT CHANGE.
- The final cell image is data-dependent across BOTH loops: 6's image if
  `0 < n₂`, else 5's if `0 < n₁`, else the entry bytes — a nested `if`,
  spelled out in the engine statement (no package definition there).
- PARTIAL: `tl_body2_wps`/`tl_body1_wps` (the two bodies at any reachable
  frame), `tl_blockSpecs` (both labels, by `blockSpecs_intro` — no Löb),
  `tl_wps`, `tl_wp_readout`, and THE ENGINE FACT `two_label_certified`
  (`DriverSafeCtl` at `procCtx …`, exactly the counter loop's shape).
- TOTAL: `tl_body2_wpt`/`tl_body1_wpt`, `tl_blockSpecsT`, `tl_wpt`
  (budget `5 * n₁.toNat + 5 * n₂.toNat + 5`: per iteration guard 1 +
  store 3 + jump 1; the first loop's exit guard 1 + the second `save`'s
  entry 1; the second loop's exit guard 1 + delivery 1; the outer `save`
  1) and `tl_wpt_readout` at the engine readout `readoutPost`. Like every
  seeded exhibit it has no shipped-loop total form (KNOWN-OPEN-ITEMS B1:
  the total statements over seeded memories are the deferred class).

THE ENVIRONMENT: the invariants carry the reachable-frame predicate
`SymFrame` and every lookup goes through THE LOOKUP LAW `envAdd_lookup`,
as LoopExhibit does; the second loop's counter `y` is bound ON TOP of the
first's exhausted `x` frame (the engine's `update_env`), and every later
lookup of `y` reads the bucket head.
-/
import CerberusHeapLang.API
import CerberusHeapLang.Examples.Layout
import CerberusHeapLang.LoopExhibit

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Map

/-! ## The program -/

/-- The first loop's label. -/
def tlL1Sym : sym := Symbol "" 111 SD_None
/-- The second loop's label. -/
def tlL2Sym : sym := Symbol "" 112 SD_None
/-- The first loop's counter `x`. -/
def tlXSym : sym := Symbol "" 113 SD_None
/-- The second loop's counter `y`. -/
def tlYSym : sym := Symbol "" 114 SD_None
/-- The procedure the labels belong to. -/
def tlProcSym : sym := Symbol "" 115 SD_None

/-- `x > 0`. -/
def tlGuard1 : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpGt (Pexpr [] () (PEsym tlXSym)) (Pexpr [] () (PEval (ivVal 0))))
/-- `x - 1`. -/
def tlDec1 : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpSub (Pexpr [] () (PEsym tlXSym)) (Pexpr [] () (PEval (ivVal 1))))
/-- `y > 0`. -/
def tlGuard2 : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpGt (Pexpr [] () (PEsym tlYSym)) (Pexpr [] () (PEval (ivVal 0))))
/-- `y - 1`. -/
def tlDec2 : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpSub (Pexpr [] () (PEsym tlYSym)) (Pexpr [] () (PEval (ivVal 1))))

/-- The first `save`'s parameters `(x : xbty := n₁)`. -/
def tlParams1 (xbty : core_base_type) (n₁ : Int) :
    List (sym × ((core_base_type × Option (ctype × pass_by_value_or_pointer)) ×
      generic_pexpr Unit sym)) :=
  [(tlXSym, ((xbty, none), Pexpr [] () (PEval (ivVal n₁))))]

/-- The second `save`'s parameters `(y : ybty := n₂)`. -/
def tlParams2 (ybty : core_base_type) (n₂ : Int) :
    List (sym × ((core_base_type × Option (ctype × pass_by_value_or_pointer)) ×
      generic_pexpr Unit sym)) :=
  [(tlYSym, ((ybty, none), Pexpr [] () (PEval (ivVal n₂))))]

/-- The second loop's body (the registered continuation of `l2`). -/
def tlBody2 (loc : CerbLocation.Loc) (ann ra : core_run_annotation) (mo : memory_order)
    (bty : core_base_type) (c : CerbMem.PointerValue) : CoreExpr :=
  Expr [] (Eif tlGuard2
    (sseqExpr bty (storeExpr loc ann intTy c sixVal mo) (Expr [] (Erun ra tlL2Sym [tlDec2])))
    (ofVal (.pure Vunit)))

/-- The first loop's body (the registered continuation of `l1`): its exit
    ENTERS the second loop through the second `save`. -/
def tlBody1 (loc : CerbLocation.Loc) (ann ra : core_run_annotation) (mo : memory_order)
    (bty ybty sbty₂ : core_base_type) (c : CerbMem.PointerValue) (n₂ : Int) : CoreExpr :=
  Expr [] (Eif tlGuard1
    (sseqExpr bty (storeExpr loc ann intTy c fiveVal mo) (Expr [] (Erun ra tlL1Sym [tlDec1])))
    (Expr [] (Esave (tlL2Sym, sbty₂) (tlParams2 ybty n₂) (tlBody2 loc ann ra mo bty c))))

/-- The whole program: the first `save` binding `x := n₁`. -/
def tlProg (loc : CerbLocation.Loc) (ann ra : core_run_annotation) (mo : memory_order)
    (bty xbty ybty sbty₁ sbty₂ : core_base_type) (c : CerbMem.PointerValue) (n₁ n₂ : Int) :
    CoreExpr :=
  Expr [] (Esave (tlL1Sym, sbty₁) (tlParams1 xbty n₁)
    (tlBody1 loc ann ra mo bty ybty sbty₂ c n₂))

/-- THE TWO-ENTRY LABEL MAP of the procedure. -/
def tlQ (loc : CerbLocation.Loc) (ann ra : core_run_annotation) (mo : memory_order)
    (bty xbty ybty sbty₂ : core_base_type) (c : CerbMem.PointerValue) (n₂ : Int) : LabelMap :=
  symAdd tlL2Sym ([(tlYSym, ybty)], tlBody2 loc ann ra mo bty c)
    (symAdd tlL1Sym ([(tlXSym, xbty)], tlBody1 loc ann ra mo bty ybty sbty₂ c n₂) fmapEmpty)

/-- The run state carrying the two-level `labeled` tie at the procedure. -/
def tlRS (loc : CerbLocation.Loc) (ann ra : core_run_annotation) (mo : memory_order)
    (bty xbty ybty sbty₂ : core_base_type) (c : CerbMem.PointerValue) (n₂ : Int) :
    core_run_state :=
  { spikeRunState with
      labeled := symAdd tlProcSym (tlQ loc ann ra mo bty xbty ybty sbty₂ c n₂) fmapEmpty }

section TlFacts

variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation) (mo : memory_order)
  (bty xbty ybty sbty₂ : core_base_type) (c : CerbMem.PointerValue) (n₂ : Int)

/-- `l1` resolves (the INNER entry of the two-entry chain). -/
theorem tlQ_lookup_l1 :
    lookupLabel (tlQ loc ann ra mo bty xbty ybty sbty₂ c n₂) tlL1Sym =
      some ([(tlXSym, xbty)], tlBody1 loc ann ra mo bty ybty sbty₂ c n₂) := by
  unfold lookupLabel tlQ
  rw [symAdd_lookup_two, if_neg (by decide +kernel), if_pos (by decide +kernel)]

/-- `l2` resolves (the OUTER entry). -/
theorem tlQ_lookup_l2 :
    lookupLabel (tlQ loc ann ra mo bty xbty ybty sbty₂ c n₂) tlL2Sym =
      some ([(tlYSym, ybty)], tlBody2 loc ann ra mo bty c) := by
  unfold lookupLabel tlQ
  rw [symAdd_lookup_two, if_pos (by decide +kernel)]

/-- Every successful lookup is one of the two entries, with the comparator
    verdict that selected it (what the label-dependent specification reads). -/
theorem tlQ_inv {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel (tlQ loc ann ra mo bty xbty ybty sbty₂ c n₂) l = some (params, cont)) :
    (symOrd l tlL2Sym = .eq ∧ params = [(tlYSym, ybty)] ∧ cont = tlBody2 loc ann ra mo bty c) ∨
    (symOrd l tlL2Sym ≠ .eq ∧ params = [(tlXSym, xbty)] ∧
      cont = tlBody1 loc ann ra mo bty ybty sbty₂ c n₂) := by
  unfold lookupLabel tlQ at h
  rw [symAdd_lookup_two] at h
  by_cases h2 : symOrd l tlL2Sym = .eq
  · rw [if_pos h2] at h
    obtain ⟨hp, hb⟩ := Prod.mk.inj (Option.some.inj h)
    exact .inl ⟨h2, hp.symm, hb.symm⟩
  · rw [if_neg h2] at h
    by_cases h1 : symOrd l tlL1Sym = .eq
    · rw [if_pos h1] at h
      obtain ⟨hp, hb⟩ := Prod.mk.inj (Option.some.inj h)
      exact .inr ⟨h2, hp.symm, hb.symm⟩
    · rw [if_neg h1] at h
      cases h

/-- The Q↔labeled tie holds of the exhibit's run state. -/
theorem tlRS_labeledAt :
    LabeledAt (tlRS loc ann ra mo bty xbty ybty sbty₂ c n₂) tlProcSym
      (tlQ loc ann ra mo bty xbty ybty sbty₂ c n₂) := by
  unfold LabeledAt tlRS
  show fmapLookupBy _ _ (symAdd tlProcSym _ fmapEmpty) = _
  rw [symAdd_lookup symMap_empty, if_pos (by decide +kernel)]

end TlFacts

/-! ## The env frames: any reachable frame, through THE LOOKUP LAW -/

theorem tl_lookup_x {f : Fmap sym value} (hf : SymFrame f) (v : value)
    (rest : List (Fmap sym value)) :
    lookup_env (a := value) tlXSym (envAdd tlXSym v f :: rest) = some v :=
  lookup_env_head (by rw [envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]) rest

theorem tl_lookup_y {f : Fmap sym value} (hf : SymFrame f) (v : value)
    (rest : List (Fmap sym value)) :
    lookup_env (a := value) tlYSym (envAdd tlYSym v f :: rest) = some v :=
  lookup_env_head (by rw [envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]) rest

theorem tl_guard1_eval {f : Fmap sym value} (hf : SymFrame f) (i : Int)
    (rest : List (Fmap sym value)) :
    evalPexpr fmapEmpty fmapEmpty (envAdd tlXSym (ivVal i) f :: rest) tlGuard1 =
      some (boolValue (decide (0 < i))) := by
  unfold tlGuard1
  rw [evalPexpr_op]
  rw [show evalPexpr fmapEmpty fmapEmpty (envAdd tlXSym (ivVal i) f :: rest)
      (Pexpr [] () (PEsym tlXSym)) = some (ivVal i) from by
      rw [evalPexpr_sym_empty]; exact tl_lookup_x hf (ivVal i) rest]
  show evalBinop binop.OpGt (ivVal i) (ivVal 0) = _
  unfold evalBinop ivVal
  show (CerbMem.ltIval (CerbMem.integerIval 0)
    (CerbMem.integerIval i)).map boolValue = _
  rfl

theorem tl_guard2_eval {f : Fmap sym value} (hf : SymFrame f) (j : Int)
    (rest : List (Fmap sym value)) :
    evalPexpr fmapEmpty fmapEmpty (envAdd tlYSym (ivVal j) f :: rest) tlGuard2 =
      some (boolValue (decide (0 < j))) := by
  unfold tlGuard2
  rw [evalPexpr_op]
  rw [show evalPexpr fmapEmpty fmapEmpty (envAdd tlYSym (ivVal j) f :: rest)
      (Pexpr [] () (PEsym tlYSym)) = some (ivVal j) from by
      rw [evalPexpr_sym_empty]; exact tl_lookup_y hf (ivVal j) rest]
  show evalBinop binop.OpGt (ivVal j) (ivVal 0) = _
  unfold evalBinop ivVal
  show (CerbMem.ltIval (CerbMem.integerIval 0)
    (CerbMem.integerIval j)).map boolValue = _
  rfl

theorem tl_dec1_eval {f : Fmap sym value} (hf : SymFrame f) (i : Int)
    (rest : List (Fmap sym value)) :
    evalPexprs fmapEmpty fmapEmpty (envAdd tlXSym (ivVal i) f :: rest) [tlDec1] =
      some [ivVal (i - 1)] := by
  rw [evalPexprs_cons]
  rw [show evalPexpr fmapEmpty fmapEmpty (envAdd tlXSym (ivVal i) f :: rest) tlDec1 =
      some (ivVal (i - 1)) from by
    unfold tlDec1
    rw [evalPexpr_op]
    rw [show evalPexpr fmapEmpty fmapEmpty (envAdd tlXSym (ivVal i) f :: rest)
        (Pexpr [] () (PEsym tlXSym)) = some (ivVal i) from by
        rw [evalPexpr_sym_empty]; exact tl_lookup_x hf (ivVal i) rest]
    rfl]
  rfl

theorem tl_dec2_eval {f : Fmap sym value} (hf : SymFrame f) (j : Int)
    (rest : List (Fmap sym value)) :
    evalPexprs fmapEmpty fmapEmpty (envAdd tlYSym (ivVal j) f :: rest) [tlDec2] =
      some [ivVal (j - 1)] := by
  rw [evalPexprs_cons]
  rw [show evalPexpr fmapEmpty fmapEmpty (envAdd tlYSym (ivVal j) f :: rest) tlDec2 =
      some (ivVal (j - 1)) from by
    unfold tlDec2
    rw [evalPexpr_op]
    rw [show evalPexpr fmapEmpty fmapEmpty (envAdd tlYSym (ivVal j) f :: rest)
        (Pexpr [] () (PEsym tlYSym)) = some (ivVal j) from by
        rw [evalPexpr_sym_empty]; exact tl_lookup_y hf (ivVal j) rest]
    rfl]
  rfl

/-! ## The binding computations -/

theorem tl_bindArgs_x (b : core_base_type) (v : value) (f : Fmap sym value)
    (rest : List (Fmap sym value)) :
    bindArgs [(tlXSym, b)] [v] (f :: rest) = envAdd tlXSym v f :: rest := by
  show update_env (mk_sym_pat tlXSym b) v (f :: rest) = _
  rw [update_env_cons, update_env_aux_sym]

theorem tl_bindArgs_y (b : core_base_type) (v : value) (f : Fmap sym value)
    (rest : List (Fmap sym value)) :
    bindArgs [(tlYSym, b)] [v] (f :: rest) = envAdd tlYSym v f :: rest := by
  show update_env (mk_sym_pat tlYSym b) v (f :: rest) = _
  rw [update_env_cons, update_env_aux_sym]

theorem tl_bindSave1 (xbty : core_base_type) (n₁ : Int) (f : Fmap sym value)
    (rest : List (Fmap sym value)) :
    bindSaveParams (tlParams1 xbty n₁) [ivVal n₁] (f :: rest) =
      envAdd tlXSym (ivVal n₁) f :: rest := by
  show update_env (mk_sym_pat tlXSym xbty) (ivVal n₁) (f :: rest) = _
  rw [update_env_cons, update_env_aux_sym]

theorem tl_bindSave2 (ybty : core_base_type) (n₂ : Int) (f : Fmap sym value)
    (rest : List (Fmap sym value)) :
    bindSaveParams (tlParams2 ybty n₂) [ivVal n₂] (f :: rest) =
      envAdd tlYSym (ivVal n₂) f :: rest := by
  show update_env (mk_sym_pat tlYSym ybty) (ivVal n₂) (f :: rest) = _
  rw [update_env_cons, update_env_aux_sym]

/-! ## The Iris layer: the two invariants, the label-dependent
specification, the bodies, the block specifications, the entry -/

section TlIris

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation) (mo : memory_order)
  (bty xbty ybty sbty₂ : core_base_type) (c : CerbMem.PointerValue) (n₁ n₂ : Int)
  (bs0 : List CerbMem.AbsByte)

/-- The final image, decided by both loops' data. -/
abbrev tlFinal : List CerbMem.AbsByte :=
  if 0 < n₂ then sixBytes fmapEmpty else if 0 < n₁ then fiveBytes fmapEmpty else bs0

/-- The postcondition: unit, the cell at its final image. -/
abbrev tlPost : SpikeVal → EnvStack → IProp GF := fun w _ =>
  iprop(⌜w.val = Vunit⌝ ∗ pointsToCell fmapEmpty c (.own 1) intTy (tlFinal n₁ n₂ bs0))

/-- The first loop's invariant at its counter `i ∈ [0, n₁]`: the entry
    bytes before the first store, 5's image after. -/
abbrev tlInv1 (vs : List value) (ρ : EnvStack) : IProp GF :=
  iprop(∃ (i : Int) (f : Fmap sym value) (rest : List (Fmap sym value)),
    ⌜vs = [ivVal i] ∧ 0 ≤ i ∧ i ≤ n₁ ∧ ρ = f :: rest ∧ SymFrame f⌝ ∗
    ((⌜i = n₁⌝ ∗ pointsToCell fmapEmpty c (.own 1) intTy bs0) ∨
     (⌜i < n₁⌝ ∗ pointsToCell fmapEmpty c (.own 1) intTy (fiveBytes fmapEmpty))))

/-- The second loop's invariant at its counter `j ∈ [0, n₂]`: the first
    loop's final image before the first store, 6's image after. -/
abbrev tlInv2 (vs : List value) (ρ : EnvStack) : IProp GF :=
  iprop(∃ (j : Int) (f : Fmap sym value) (rest : List (Fmap sym value)),
    ⌜vs = [ivVal j] ∧ 0 ≤ j ∧ j ≤ n₂ ∧ ρ = f :: rest ∧ SymFrame f⌝ ∗
    ((⌜j = n₂⌝ ∗ pointsToCell fmapEmpty c (.own 1) intTy
        (if 0 < n₁ then fiveBytes fmapEmpty else bs0)) ∨
     (⌜j < n₂⌝ ∗ pointsToCell fmapEmpty c (.own 1) intTy (sixBytes fmapEmpty))))

/-- THE LABEL-DEPENDENT SPECIFICATION: `l2`'s invariant at `l2`, the first
    loop's at every other label (`l1` is the only other registered one). -/
abbrev tlLs : LabelSpec GF := fun l vs ρ =>
  if symOrd l tlL2Sym = .eq then tlInv2 c n₁ n₂ bs0 vs ρ else tlInv1 c n₁ bs0 vs ρ

variable (p : sym) (rs : core_run_state)
  (hQ : LabeledAt rs p (tlQ loc ann ra mo bty xbty ybty sbty₂ c n₂))

include hQ

/-- The second loop's body at any reachable counter frame. -/
theorem tl_body2_wps (j : Int) (f : Fmap sym value) (rest : List (Fmap sym value))
    (hf : SymFrame f) (h0 : 0 ≤ j) (hin : j ≤ n₂) (bs : List CerbMem.AbsByte)
    (hbs : (j = n₂ ∧ bs = (if 0 < n₁ then fiveBytes fmapEmpty else bs0)) ∨
      (j < n₂ ∧ bs = sixBytes fmapEmpty)) :
    pointsToCell (procCtx rs).tagDefs (GF := GF) c (.own 1) intTy bs ⊢
      wps (procCtx rs) (some p) (tlLs c n₁ n₂ bs0) emptyProcSpec (tlPost c n₁ n₂ bs0)
        (tlBody2 loc ann ra mo bty c) (envAdd tlYSym (ivVal j) f :: rest) := by
  rw [show tlBody2 loc ann ra mo bty c =
    Expr [] (Eif tlGuard2
      (Expr [] (Esseq (Pattern [] (CaseBase (none, bty)))
        (storeExpr loc ann intTy c sixVal mo)
        (Expr [] (Erun ra tlL2Sym [tlDec2]))))
      (ofVal (.pure Vunit))) from rfl]
  iintro Hc
  by_cases hpos : 0 < j
  · -- guard TRUE: store 6, jump at j - 1
    iapply wps_if_true [] tlGuard2 _ _ _
      (by rw [procCtx_extern, tl_guard2_eval hf j rest, decide_eq_true hpos]; rfl)
    iapply wps_seq
    iapply wps_store loc ann intTy c sixVal mo sixMval bs _ six_encodes (six_storable _)
    isplitl [Hc]
    · iexact Hc
    iintro %fp Hc
    iapply wps_run [] ra tlL2Sym [tlDec2] _ _
      (by rw [procCtx_labels hQ]
          exact tlQ_lookup_l2 loc ann ra mo bty xbty ybty sbty₂ c n₂)
      (tl_dec2_eval hf j rest)
    dsimp only [tlLs]
    rw [if_pos (by decide +kernel)]
    iexists (j - 1), (envAdd tlYSym (ivVal j) f), rest
    isplit
    · ipureintro
      exact ⟨rfl, by omega, by omega, rfl, hf.add _ _⟩
    iright
    isplit
    · ipureintro; omega
    rw [show (sixBytes (procCtx rs).tagDefs) =
      (CerbMem.memValueToBytes (procCtx rs).tagDefs [] sixMval).2 from rfl]
    iexact Hc
  · -- guard FALSE (j = 0): deliver unit at the final image
    have hz : j = 0 := by omega
    subst hz
    iapply wps_if_false [] tlGuard2 _ _ _
      (by rw [procCtx_extern, tl_guard2_eval hf 0 rest, decide_eq_false hpos]; rfl)
    iapply wps_ofVal (.pure Vunit)
    dsimp only [tlPost]
    isplit
    · ipureintro; rfl
    rcases hbs with ⟨heq, rfl⟩ | ⟨hlt, rfl⟩
    · rw [show tlFinal n₁ n₂ bs0 = (if 0 < n₁ then fiveBytes fmapEmpty else bs0) from
        if_neg (by omega)]
      iexact Hc
    · rw [show tlFinal n₁ n₂ bs0 = sixBytes fmapEmpty from if_pos hlt]
      iexact Hc

/-- The first loop's body at any reachable counter frame; its exit enters
    the second loop (`wps_save`, then `tl_body2_wps` at `j = n₂`). -/
theorem tl_body1_wps (hn₂ : 0 ≤ n₂) (i : Int) (f : Fmap sym value)
    (rest : List (Fmap sym value)) (hf : SymFrame f) (h0 : 0 ≤ i) (hin : i ≤ n₁) :
    iprop(((⌜i = n₁⌝ ∗ pointsToCell (procCtx rs).tagDefs (GF := GF) c (.own 1) intTy bs0) ∨
      (⌜i < n₁⌝ ∗ pointsToCell (procCtx rs).tagDefs c (.own 1) intTy
        (fiveBytes (procCtx rs).tagDefs)))) ⊢
      wps (procCtx rs) (some p) (tlLs c n₁ n₂ bs0) emptyProcSpec (tlPost c n₁ n₂ bs0)
        (tlBody1 loc ann ra mo bty ybty sbty₂ c n₂) (envAdd tlXSym (ivVal i) f :: rest) := by
  rw [show tlBody1 loc ann ra mo bty ybty sbty₂ c n₂ =
    Expr [] (Eif tlGuard1
      (Expr [] (Esseq (Pattern [] (CaseBase (none, bty)))
        (storeExpr loc ann intTy c fiveVal mo)
        (Expr [] (Erun ra tlL1Sym [tlDec1]))))
      (Expr [] (Esave (tlL2Sym, sbty₂) (tlParams2 ybty n₂)
        (tlBody2 loc ann ra mo bty c)))) from rfl]
  by_cases hpos : 0 < i
  · -- guard TRUE: store 5, jump at i - 1
    iintro Hcell
    iapply wps_if_true [] tlGuard1 _ _ _
      (by rw [procCtx_extern, tl_guard1_eval hf i rest, decide_eq_true hpos]; rfl)
    iapply wps_seq
    icases Hcell with (⟨%hieq, Hc⟩ | ⟨%hlt, Hc⟩) <;>
      (iapply wps_store loc ann intTy c fiveVal mo fiveMval _ _
        five_encodes (five_storable _)
       isplitl [Hc]
       · iexact Hc
       iintro %fp Hc
       iapply wps_run [] ra tlL1Sym [tlDec1] _ _
         (by rw [procCtx_labels hQ]
             exact tlQ_lookup_l1 loc ann ra mo bty xbty ybty sbty₂ c n₂)
         (tl_dec1_eval hf i rest)
       dsimp only [tlLs]
       rw [if_neg (by decide +kernel)]
       iexists (i - 1), (envAdd tlXSym (ivVal i) f), rest
       isplit
       · ipureintro
         exact ⟨rfl, by omega, by omega, rfl, hf.add _ _⟩
       iright
       isplit
       · ipureintro; omega
       rw [show (fiveBytes (procCtx rs).tagDefs) =
         (CerbMem.memValueToBytes (procCtx rs).tagDefs [] fiveMval).2 from rfl]
       iexact Hc)
  · -- guard FALSE (i = 0): enter the second loop at j = n₂
    have hz : i = 0 := by omega
    subst hz
    iintro Hcell
    iapply wps_if_false [] tlGuard1 _ _ _
      (by rw [procCtx_extern, tl_guard1_eval hf 0 rest, decide_eq_false hpos]; rfl)
    iapply wps_save [] (tlL2Sym, sbty₂) (tlParams2 ybty n₂) _ (envAdd tlXSym (ivVal 0) f) rest
      (cvals := [ivVal n₂]) rfl
    rw [tl_bindSave2]
    icases Hcell with (⟨%hieq, Hc⟩ | ⟨%hlt, Hc⟩)
    · iapply tl_body2_wps loc ann ra mo bty xbty ybty sbty₂ c n₁ n₂ bs0 p rs hQ n₂
        (envAdd tlXSym (ivVal 0) f) rest (hf.add _ _) hn₂ (Int.le_refl n₂) bs0
        (.inl ⟨rfl, (if_neg (by omega)).symm⟩) $$ Hc
    · iapply tl_body2_wps loc ann ra mo bty xbty ybty sbty₂ c n₁ n₂ bs0 p rs hQ n₂
        (envAdd tlXSym (ivVal 0) f) rest (hf.add _ _) hn₂ (Int.le_refl n₂) _
        (.inl ⟨rfl, (if_pos hlt).symm⟩) $$ Hc

/-- THE BLOCK SPECIFICATION FOR BOTH LABELS (`blockSpecs_intro` — no Löb;
    each label's back edge is discharged against ITS invariant at the
    smaller counter, the comparator verdict of the lookup selecting the
    invariant). -/
theorem tl_blockSpecs (hn₂ : 0 ≤ n₂) :
    ⊢ blockSpecs (GF := GF) (procCtx rs) (some p) (tlLs c n₁ n₂ bs0) emptyProcSpec
      (tlPost c n₁ n₂ bs0) := by
  refine blockSpecs_intro fun l params cont vs ev0 evs hl => ?_
  rw [procCtx_labels hQ] at hl
  rcases tlQ_inv loc ann ra mo bty xbty ybty sbty₂ c n₂ hl with ⟨h2, rfl, rfl⟩ | ⟨h2, rfl, rfl⟩
  · dsimp only [tlLs]
    rw [if_pos h2]
    iintro ⟨%j, %f, %rest, %hpure, Hcell⟩
    obtain ⟨rfl, h0, hin, hρ, hf⟩ := hpure
    obtain ⟨rfl, rfl⟩ : f = ev0 ∧ rest = evs := by
      have h1 := congrArg (fun l => l.head?) hρ
      have h2 := congrArg (fun l => l.tail) hρ
      simp at h1 h2
      exact ⟨h1.symm, h2.symm⟩
    rw [tl_bindArgs_y]
    icases Hcell with (⟨%heq, Hc⟩ | ⟨%hlt, Hc⟩)
    · iapply tl_body2_wps loc ann ra mo bty xbty ybty sbty₂ c n₁ n₂ bs0 p rs hQ j f rest hf
        h0 hin _ (.inl ⟨heq, rfl⟩) $$ Hc
    · iapply tl_body2_wps loc ann ra mo bty xbty ybty sbty₂ c n₁ n₂ bs0 p rs hQ j f rest hf
        h0 hin _ (.inr ⟨hlt, rfl⟩) $$ Hc
  · dsimp only [tlLs]
    rw [if_neg h2]
    iintro ⟨%i, %f, %rest, %hpure, Hcell⟩
    obtain ⟨rfl, h0, hin, hρ, hf⟩ := hpure
    obtain ⟨rfl, rfl⟩ : f = ev0 ∧ rest = evs := by
      have h1 := congrArg (fun l => l.head?) hρ
      have h2 := congrArg (fun l => l.tail) hρ
      simp at h1 h2
      exact ⟨h1.symm, h2.symm⟩
    rw [tl_bindArgs_x]
    iapply tl_body1_wps loc ann ra mo bty xbty ybty sbty₂ c n₁ n₂ bs0 p rs hQ hn₂ i f rest hf
      h0 hin $$ Hcell

/-- The whole program's statement WP from any reachable entry frame. -/
theorem tl_wps (hn₁ : 0 ≤ n₁) (hn₂ : 0 ≤ n₂) (sbty₁ : core_base_type)
    (f : Fmap sym value) (hf : SymFrame f) (rest : List (Fmap sym value)) :
    pointsToCell (procCtx rs).tagDefs (GF := GF) c (.own 1) intTy bs0 ⊢
      wps (procCtx rs) (some p) (tlLs c n₁ n₂ bs0) emptyProcSpec (tlPost c n₁ n₂ bs0)
        (tlProg loc ann ra mo bty xbty ybty sbty₁ sbty₂ c n₁ n₂) (f :: rest) := by
  iintro Hc
  rw [show tlProg loc ann ra mo bty xbty ybty sbty₁ sbty₂ c n₁ n₂ =
    Expr [] (Esave (tlL1Sym, sbty₁) (tlParams1 xbty n₁)
      (tlBody1 loc ann ra mo bty ybty sbty₂ c n₂)) from rfl]
  iapply wps_save [] (tlL1Sym, sbty₁) _ _ f rest (cvals := [ivVal n₁]) rfl
  rw [tl_bindSave1]
  iapply tl_body1_wps loc ann ra mo bty xbty ybty sbty₂ c n₁ n₂ bs0 p rs hQ hn₂ n₁ f rest hf
    hn₁ (Int.le_refl n₁)
  ileft
  isplit
  · ipureintro; rfl
  · iexact Hc

omit hQ in
/-- The per-value readout of the postcondition, through the public
    projection layer only (`sep_consequence` over `pure_consequence` and
    `pointsToCell_consequence`, under `stateInterp_readout`). -/
theorem tl_readout_val (w : CoreRVal) :
    tlPost (GF := GF) c n₁ n₂ bs0 w.w w.ρ ⊢
      iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
        stateInterp σ' ns κs nt ={⊤, ∅}=∗
          ⌜w.val = Vunit ∧ ∃ i a, c = cellPtr i a ∧
            CellCoh fmapEmpty σ' i ⟨a, intTy, tlFinal n₁ n₂ bs0⟩⌝) :=
  stateInterp_readout fun _ _ _ _ hG =>
    sep_consequence (pure_consequence _)
      (pointsToCell_consequence hG fmapEmpty c (.own 1) intTy _)

/-- The base-WP face with the engine readout (what `engine_adequacy`
    consumes), from any reachable entry frame. -/
theorem tl_wp_readout (hn₁ : 0 ≤ n₁) (hn₂ : 0 ≤ n₂) (sbty₁ : core_base_type)
    (f : Fmap sym value) (hf : SymFrame f) (rest : List (Fmap sym value)) :
    pointsToCell (procCtx rs).tagDefs (GF := GF) c (.own 1) intTy bs0 ⊢
      WP (⟨tlProg loc ann ra mo bty xbty ybty sbty₁ sbty₂ c n₁ n₂, f :: rest,
          procCtl p, procCtx rs⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
        {{ w, iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
          stateInterp σ' ns κs nt ={⊤, ∅}=∗
            ⌜w.val = Vunit ∧ ∃ i a, c = cellPtr i a ∧
              CellCoh (procCtx rs).tagDefs σ' i ⟨a, intTy, tlFinal n₁ n₂ bs0⟩⌝) }} := by
  refine ((tl_wps loc ann ra mo bty xbty ybty sbty₂ c n₁ n₂ bs0 p rs hQ hn₁ hn₂ sbty₁ f hf
    rest).trans ?_)
  refine (BI.emp_sep.2.trans (BI.sep_mono
    ((tl_blockSpecs loc ann ra mo bty xbty ybty sbty₂ c n₁ n₂ bs0 p rs hQ hn₂).trans
      (wps_sound_empty (ctl := procCtl p) rfl
        (tlProg loc ann ra mo bty xbty ybty sbty₁ sbty₂ c n₁ n₂) (f :: rest)))
    .rfl)).trans ?_
  refine BI.wand_elim_left.trans ?_
  exact wp_mono fun w => tl_readout_val c n₁ n₂ bs0 w

/-! ### The total twins -/

/-- THE VARIANT-INDEXED SPECIFICATION: the two invariants with their
    per-entry budgets — `5 * j + 2` at `l2` (five per iteration, the exit's
    guard and delivery), `5 * i + 5 * n₂ + 4` at `l1` (its exit pays the
    guard, the second `save`'s entry and the whole second loop). -/
abbrev tlInv1T (m : Nat) (vs : List value) (ρ : EnvStack) : IProp GF :=
  iprop(∃ (i : Int) (f : Fmap sym value) (rest : List (Fmap sym value)),
    ⌜vs = [ivVal i] ∧ 0 ≤ i ∧ i ≤ n₁ ∧ m = 5 * i.toNat + 5 * n₂.toNat + 4 ∧
      ρ = f :: rest ∧ SymFrame f⌝ ∗
    ((⌜i = n₁⌝ ∗ pointsToCell fmapEmpty c (.own 1) intTy bs0) ∨
     (⌜i < n₁⌝ ∗ pointsToCell fmapEmpty c (.own 1) intTy (fiveBytes fmapEmpty))))

abbrev tlInv2T (m : Nat) (vs : List value) (ρ : EnvStack) : IProp GF :=
  iprop(∃ (j : Int) (f : Fmap sym value) (rest : List (Fmap sym value)),
    ⌜vs = [ivVal j] ∧ 0 ≤ j ∧ j ≤ n₂ ∧ m = 5 * j.toNat + 2 ∧ ρ = f :: rest ∧ SymFrame f⌝ ∗
    ((⌜j = n₂⌝ ∗ pointsToCell fmapEmpty c (.own 1) intTy
        (if 0 < n₁ then fiveBytes fmapEmpty else bs0)) ∨
     (⌜j < n₂⌝ ∗ pointsToCell fmapEmpty c (.own 1) intTy (sixBytes fmapEmpty))))

abbrev tlLsT : LabelSpecT GF := fun l m vs ρ =>
  if symOrd l tlL2Sym = .eq then tlInv2T c n₁ n₂ bs0 m vs ρ else tlInv1T c n₁ n₂ bs0 m vs ρ

/-- The second loop's body within its budget. -/
theorem tl_body2_wpt (j : Int) (f : Fmap sym value) (rest : List (Fmap sym value))
    (hf : SymFrame f) (h0 : 0 ≤ j) (hin : j ≤ n₂) (bs : List CerbMem.AbsByte)
    (hbs : (j = n₂ ∧ bs = (if 0 < n₁ then fiveBytes fmapEmpty else bs0)) ∨
      (j < n₂ ∧ bs = sixBytes fmapEmpty)) :
    pointsToCell (procCtx rs).tagDefs (GF := GF) c (.own 1) intTy bs ⊢
      wpt (procCtx rs) (some p) (tlLsT c n₁ n₂ bs0) emptyProcSpecT (5 * j.toNat + 2)
        (tlPost c n₁ n₂ bs0) (tlBody2 loc ann ra mo bty c) (envAdd tlYSym (ivVal j) f :: rest) := by
  rw [show tlBody2 loc ann ra mo bty c =
    Expr [] (Eif tlGuard2
      (Expr [] (Esseq (Pattern [] (CaseBase (none, bty)))
        (storeExpr loc ann intTy c sixVal mo)
        (Expr [] (Erun ra tlL2Sym [tlDec2]))))
      (ofVal (.pure Vunit))) from rfl]
  iintro Hc
  by_cases hpos : 0 < j
  · rw [show 5 * j.toNat + 2 = (3 + (1 + (5 * (j - 1).toNat + 2))) + 1 by omega]
    iapply wpt_if_true [] tlGuard2 _ _ _
      (by rw [procCtx_extern, tl_guard2_eval hf j rest, decide_eq_true hpos]; rfl)
    iapply wpt_seq
    iapply wpt_store loc ann intTy c sixVal mo sixMval bs _ (Nat.le_refl 3)
      six_encodes (six_storable _)
    isplitl [Hc]
    · iexact Hc
    iintro %fp Hc
    iapply wpt_run [] ra tlL2Sym [tlDec2] _ _ (5 * (j - 1).toNat + 2)
      (by rw [procCtx_labels hQ]
          exact tlQ_lookup_l2 loc ann ra mo bty xbty ybty sbty₂ c n₂)
      (tl_dec2_eval hf j rest) (Nat.le_refl _)
    dsimp only [tlLsT]
    rw [if_pos (by decide +kernel)]
    iexists (j - 1), (envAdd tlYSym (ivVal j) f), rest
    isplit
    · ipureintro
      exact ⟨rfl, by omega, by omega, rfl, rfl, hf.add _ _⟩
    iright
    isplit
    · ipureintro; omega
    rw [show (sixBytes (procCtx rs).tagDefs) =
      (CerbMem.memValueToBytes (procCtx rs).tagDefs [] sixMval).2 from rfl]
    iexact Hc
  · have hz : j = 0 := by omega
    subst hz
    rw [show 5 * (0 : Int).toNat + 2 = 1 + 1 from rfl]
    iapply wpt_if_false [] tlGuard2 _ _ _
      (by rw [procCtx_extern, tl_guard2_eval hf 0 rest, decide_eq_false hpos]; rfl)
    iapply wpt_ofVal (.pure Vunit) _ (Nat.le_refl 1)
    dsimp only [tlPost]
    isplit
    · ipureintro; rfl
    rcases hbs with ⟨heq, rfl⟩ | ⟨hlt, rfl⟩
    · rw [show tlFinal n₁ n₂ bs0 = (if 0 < n₁ then fiveBytes fmapEmpty else bs0) from
        if_neg (by omega)]
      iexact Hc
    · rw [show tlFinal n₁ n₂ bs0 = sixBytes fmapEmpty from if_pos hlt]
      iexact Hc

/-- The first loop's body within its budget. -/
theorem tl_body1_wpt (hn₂ : 0 ≤ n₂) (i : Int) (f : Fmap sym value)
    (rest : List (Fmap sym value)) (hf : SymFrame f) (h0 : 0 ≤ i) (hin : i ≤ n₁) :
    iprop(((⌜i = n₁⌝ ∗ pointsToCell (procCtx rs).tagDefs (GF := GF) c (.own 1) intTy bs0) ∨
      (⌜i < n₁⌝ ∗ pointsToCell (procCtx rs).tagDefs c (.own 1) intTy
        (fiveBytes (procCtx rs).tagDefs)))) ⊢
      wpt (procCtx rs) (some p) (tlLsT c n₁ n₂ bs0) emptyProcSpecT
        (5 * i.toNat + 5 * n₂.toNat + 4) (tlPost c n₁ n₂ bs0)
        (tlBody1 loc ann ra mo bty ybty sbty₂ c n₂) (envAdd tlXSym (ivVal i) f :: rest) := by
  rw [show tlBody1 loc ann ra mo bty ybty sbty₂ c n₂ =
    Expr [] (Eif tlGuard1
      (Expr [] (Esseq (Pattern [] (CaseBase (none, bty)))
        (storeExpr loc ann intTy c fiveVal mo)
        (Expr [] (Erun ra tlL1Sym [tlDec1]))))
      (Expr [] (Esave (tlL2Sym, sbty₂) (tlParams2 ybty n₂)
        (tlBody2 loc ann ra mo bty c)))) from rfl]
  by_cases hpos : 0 < i
  · rw [show 5 * i.toNat + 5 * n₂.toNat + 4 =
      (3 + (1 + (5 * (i - 1).toNat + 5 * n₂.toNat + 4))) + 1 by omega]
    iintro Hcell
    iapply wpt_if_true [] tlGuard1 _ _ _
      (by rw [procCtx_extern, tl_guard1_eval hf i rest, decide_eq_true hpos]; rfl)
    iapply wpt_seq
    icases Hcell with (⟨%hieq, Hc⟩ | ⟨%hlt, Hc⟩) <;>
      (iapply wpt_store loc ann intTy c fiveVal mo fiveMval _ _ (Nat.le_refl 3)
        five_encodes (five_storable _)
       isplitl [Hc]
       · iexact Hc
       iintro %fp Hc
       iapply wpt_run [] ra tlL1Sym [tlDec1] _ _ (5 * (i - 1).toNat + 5 * n₂.toNat + 4)
         (by rw [procCtx_labels hQ]
             exact tlQ_lookup_l1 loc ann ra mo bty xbty ybty sbty₂ c n₂)
         (tl_dec1_eval hf i rest) (Nat.le_refl _)
       dsimp only [tlLsT]
       rw [if_neg (by decide +kernel)]
       iexists (i - 1), (envAdd tlXSym (ivVal i) f), rest
       isplit
       · ipureintro
         exact ⟨rfl, by omega, by omega, rfl, rfl, hf.add _ _⟩
       iright
       isplit
       · ipureintro; omega
       rw [show (fiveBytes (procCtx rs).tagDefs) =
         (CerbMem.memValueToBytes (procCtx rs).tagDefs [] fiveMval).2 from rfl]
       iexact Hc)
  · have hz : i = 0 := by omega
    subst hz
    rw [show 5 * (0 : Int).toNat + 5 * n₂.toNat + 4 =
      ((5 * n₂.toNat + 2) + saveEntryCost (tlParams2 ybty n₂)) + 1 by
      rw [show saveEntryCost (tlParams2 ybty n₂) = 1 from rfl]; omega]
    iintro Hcell
    iapply wpt_if_false [] tlGuard1 _ _ _
      (by rw [procCtx_extern, tl_guard1_eval hf 0 rest, decide_eq_false hpos]; rfl)
    iapply wpt_save [] (tlL2Sym, sbty₂) (tlParams2 ybty n₂) _ (envAdd tlXSym (ivVal 0) f) rest
      (cvals := [ivVal n₂]) rfl
    rw [tl_bindSave2]
    icases Hcell with (⟨%hieq, Hc⟩ | ⟨%hlt, Hc⟩)
    · iapply tl_body2_wpt loc ann ra mo bty xbty ybty sbty₂ c n₁ n₂ bs0 p rs hQ n₂
        (envAdd tlXSym (ivVal 0) f) rest (hf.add _ _) hn₂ (Int.le_refl n₂) bs0
        (.inl ⟨rfl, (if_neg (by omega)).symm⟩) $$ Hc
    · iapply tl_body2_wpt loc ann ra mo bty xbty ybty sbty₂ c n₁ n₂ bs0 p rs hQ n₂
        (envAdd tlXSym (ivVal 0) f) rest (hf.add _ _) hn₂ (Int.le_refl n₂) _
        (.inl ⟨rfl, (if_pos hlt).symm⟩) $$ Hc

/-- THE TOTAL BLOCK SPECIFICATION for both labels. -/
theorem tl_blockSpecsT (hn₂ : 0 ≤ n₂) :
    ⊢ blockSpecsT (GF := GF) (procCtx rs) (some p) (tlLsT c n₁ n₂ bs0) emptyProcSpecT
      (tlPost c n₁ n₂ bs0) := by
  refine blockSpecsT_intro fun l params cont vs ev0 evs m hl => ?_
  rw [procCtx_labels hQ] at hl
  rcases tlQ_inv loc ann ra mo bty xbty ybty sbty₂ c n₂ hl with ⟨h2, rfl, rfl⟩ | ⟨h2, rfl, rfl⟩
  · dsimp only [tlLsT]
    rw [if_pos h2]
    iintro ⟨%j, %f, %rest, %hpure, Hcell⟩
    obtain ⟨rfl, h0, hin, rfl, hρ, hf⟩ := hpure
    obtain ⟨rfl, rfl⟩ : f = ev0 ∧ rest = evs := by
      have h1 := congrArg (fun l => l.head?) hρ
      have h2 := congrArg (fun l => l.tail) hρ
      simp at h1 h2
      exact ⟨h1.symm, h2.symm⟩
    rw [tl_bindArgs_y]
    icases Hcell with (⟨%heq, Hc⟩ | ⟨%hlt, Hc⟩)
    · iapply tl_body2_wpt loc ann ra mo bty xbty ybty sbty₂ c n₁ n₂ bs0 p rs hQ j f rest hf
        h0 hin _ (.inl ⟨heq, rfl⟩) $$ Hc
    · iapply tl_body2_wpt loc ann ra mo bty xbty ybty sbty₂ c n₁ n₂ bs0 p rs hQ j f rest hf
        h0 hin _ (.inr ⟨hlt, rfl⟩) $$ Hc
  · dsimp only [tlLsT]
    rw [if_neg h2]
    iintro ⟨%i, %f, %rest, %hpure, Hcell⟩
    obtain ⟨rfl, h0, hin, rfl, hρ, hf⟩ := hpure
    obtain ⟨rfl, rfl⟩ : f = ev0 ∧ rest = evs := by
      have h1 := congrArg (fun l => l.head?) hρ
      have h2 := congrArg (fun l => l.tail) hρ
      simp at h1 h2
      exact ⟨h1.symm, h2.symm⟩
    rw [tl_bindArgs_x]
    iapply tl_body1_wpt loc ann ra mo bty xbty ybty sbty₂ c n₁ n₂ bs0 p rs hQ hn₂ i f rest hf
      h0 hin $$ Hcell

/-- THE WHOLE PROGRAM at the total judgment: budget `5 * n₁ + 5 * n₂ + 5`
    (the outer `save`'s entry, `saveEntryCost = 1` at a value initializer,
    then the first loop's budget at `i = n₁`). -/
theorem tl_wpt (hn₁ : 0 ≤ n₁) (hn₂ : 0 ≤ n₂) (sbty₁ : core_base_type)
    (f : Fmap sym value) (hf : SymFrame f) (rest : List (Fmap sym value)) :
    pointsToCell (procCtx rs).tagDefs (GF := GF) c (.own 1) intTy bs0 ⊢
      wpt (procCtx rs) (some p) (tlLsT c n₁ n₂ bs0) emptyProcSpecT
        (5 * n₁.toNat + 5 * n₂.toNat + 5) (tlPost c n₁ n₂ bs0)
        (tlProg loc ann ra mo bty xbty ybty sbty₁ sbty₂ c n₁ n₂) (f :: rest) := by
  iintro Hc
  rw [show tlProg loc ann ra mo bty xbty ybty sbty₁ sbty₂ c n₁ n₂ =
    Expr [] (Esave (tlL1Sym, sbty₁) (tlParams1 xbty n₁)
      (tlBody1 loc ann ra mo bty ybty sbty₂ c n₂)) from rfl,
    show 5 * n₁.toNat + 5 * n₂.toNat + 5 =
      (5 * n₁.toNat + 5 * n₂.toNat + 4) + saveEntryCost (tlParams1 xbty n₁) by
      rw [show saveEntryCost (tlParams1 xbty n₁) = 1 from rfl]]
  iapply wpt_save [] (tlL1Sym, sbty₁) _ _ f rest (cvals := [ivVal n₁]) rfl
  rw [tl_bindSave1]
  iapply tl_body1_wpt loc ann ra mo bty xbty ybty sbty₂ c n₁ n₂ bs0 p rs hQ hn₂ n₁ f rest hf
    hn₁ (Int.le_refl n₁)
  ileft
  isplit
  · ipureintro; rfl
  · iexact Hc

omit hQ in
/-- The postcondition entails the engine readout (the total lane's shape). -/
theorem tlPost_to_readout :
    ∀ w ρ', tlPost (GF := GF) c n₁ n₂ bs0 w ρ' ⊢
      readoutPost (fun v σ' => v = Vunit ∧ ∃ i a, c = cellPtr i a ∧
        CellCoh fmapEmpty σ' i ⟨a, intTy, tlFinal n₁ n₂ bs0⟩) w ρ' :=
  fun _ _ => stateInterp_readout fun _ _ _ _ hG =>
    sep_consequence (pure_consequence _)
      (pointsToCell_consequence hG fmapEmpty c (.own 1) intTy _)

/-- The total derivation at the engine readout — the shape the driver lane
    consumes (`wpt_driver_done`'s `hwp`), left as the loop-level fact
    (KNOWN-OPEN-ITEMS B1: no shipped-loop total form for seeded exhibits). -/
theorem tl_wpt_readout (hn₁ : 0 ≤ n₁) (hn₂ : 0 ≤ n₂) (sbty₁ : core_base_type)
    (f : Fmap sym value) (hf : SymFrame f) (rest : List (Fmap sym value)) :
    pointsToCell (procCtx rs).tagDefs (GF := GF) c (.own 1) intTy bs0 ⊢
      wpt (procCtx rs) (some p) (tlLsT c n₁ n₂ bs0) emptyProcSpecT
        (5 * n₁.toNat + 5 * n₂.toNat + 5)
        (readoutPost (fun v σ' => v = Vunit ∧ ∃ i a, c = cellPtr i a ∧
          CellCoh fmapEmpty σ' i ⟨a, intTy, tlFinal n₁ n₂ bs0⟩))
        (tlProg loc ann ra mo bty xbty ybty sbty₁ sbty₂ c n₁ n₂) (f :: rest) :=
  (tl_wpt loc ann ra mo bty xbty ybty sbty₂ c n₁ n₂ bs0 p rs hQ hn₁ hn₂ sbty₁ f hf rest).trans
    (wpt_mono (tlPost_to_readout c n₁ n₂ bs0) _ _ _)

end TlIris

/-! ## THE END-TO-END CERTIFIED THEOREM (engine vocabulary only in the
conclusion) -/

section TlDrive

variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation) (mo : memory_order)
  (bty xbty ybty sbty₂ : core_base_type) (c : CerbMem.PointerValue) (n₂ : Int)

/-- The second loop's body is in the certified cone. -/
theorem tlBody2_frag : Frag (tlBody2 loc ann ra mo bty c) := by
  refine .if_ (PePure.of_isPePure rfl) (by decide +kernel)
    (.sseq (.store) (.run (PePure.all_of_isPePure rfl) ?_))
    (.val_pure Vunit)
  intro pe hpe
  simp at hpe
  subst hpe
  exact (by decide +kernel : peDepth tlDec2 ≤ lemDefaultFuel)

/-- The first loop's body is in the cone: the second loop's `save` is its
    exit branch (`Frag.save` at value initializers). -/
theorem tlBody1_frag : Frag (tlBody1 loc ann ra mo bty ybty sbty₂ c n₂) := by
  refine .if_ (PePure.of_isPePure rfl) (by decide +kernel)
    (.sseq (.store) (.run (PePure.all_of_isPePure rfl) ?_))
    (.save (saveParams_pure_of_vals rfl) (saveParams_depth_of_vals rfl)
      (tlBody2_frag loc ann ra mo bty c))
  intro pe hpe
  simp at hpe
  subst hpe
  exact (by decide +kernel : peDepth tlDec1 ≤ lemDefaultFuel)

theorem tlBody2_esize : esize (tlBody2 loc ann ra mo bty c) = 3 := rfl
theorem tlBody1_esize : esize (tlBody1 loc ann ra mo bty ybty sbty₂ c n₂) = 5 := rfl

/-- THE EXHIBIT (partial, engine vocabulary): driving the SHIPPED loop
    from any driver state holding the proc-carrying thread (the TWO-ENTRY
    label map tied through `core_run_state.labeled`) on the two-loop
    program, from ANY memory whose seeded cell footprint is satisfied: at
    every fuel the loop exhausts or delivers `Vunit` with the cell's final
    bytes decided by BOTH loops' data — 6's image if the second loop ran,
    else 5's if the first did, else untouched; it never kills otherwise
    and never derails. -/
theorem two_label_certified (sbty₁ : core_base_type) (idx addr : Int)
    (bs0 : List CerbMem.AbsByte) (n₁ n₂ : Int) (hn₁ : 0 ≤ n₁) (hn₂ : 0 ≤ n₂)
    (σ₀ : Mem)
    (hcoh : Coh fmapEmpty σ₀ ((Iris.Std.PartialMap.singleton idx
      (SpikeCell.mk addr intTy bs0)) : SpikeHeapF SpikeCell)) :
    let prog := tlProg loc ann ra mo bty xbty ybty sbty₁ sbty₂ (cellPtr idx addr) n₁ n₂
    let rs := tlRS loc ann ra mo bty xbty ybty sbty₂ (cellPtr idx addr) n₂
    DriverSafeCtl (procCtx rs) (procThread tlProcSym prog [fmapEmpty]) prog [fmapEmpty]
      (procCtl tlProcSym) σ₀ (fun v σ' =>
        v = Vunit ∧ CellCoh fmapEmpty σ' idx ⟨addr, intTy,
          if 0 < n₂ then sixBytes fmapEmpty
          else if 0 < n₁ then fiveBytes fmapEmpty else bs0⟩) := by
  intro prog rs
  have hlbl : (procCtx rs).labelsAt (procCtl tlProcSym).proc = _ :=
    procCtx_labels (tlRS_labeledAt loc ann ra mo bty xbty ybty sbty₂ (cellPtr idx addr) n₂)
  refine (engine_adequacy (GF := SpikeGF)
    (M := procCtx rs) rfl rfl (ctl := procCtl tlProcSym) rfl
    (fun l params cont hl => by
      rw [hlbl] at hl
      rcases tlQ_inv loc ann ra mo bty xbty ybty sbty₂ _ n₂ hl with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
      · exact tlBody2_frag loc ann ra mo bty _
      · exact tlBody1_frag loc ann ra mo bty ybty sbty₂ _ n₂)
    (fun l params cont hl => by
      rw [hlbl] at hl
      rcases tlQ_inv loc ann ra mo bty xbty ybty sbty₂ _ n₂ hl with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
      · exact Nat.le_trans (tlBody2_frag loc ann ra mo bty _).pot_le_two
          (by rw [tlBody2_esize, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      · exact Nat.le_trans (tlBody1_frag loc ann ra mo bty ybty sbty₂ _ n₂).pot_le_two
          (by rw [tlBody1_esize, show lemDefaultFuel = 999999 + 1 from rfl]; omega))
    (procCtx_fragProcs _)
    prog fmapEmpty [] σ₀ _
    (.save (saveParams_pure_of_vals rfl) (saveParams_depth_of_vals rfl)
      (tlBody1_frag loc ann ra mo bty ybty sbty₂ _ n₂))
    (Nat.le_trans (Frag.pot_le_two (e := prog) (.save (saveParams_pure_of_vals rfl)
        (saveParams_depth_of_vals rfl) (tlBody1_frag loc ann ra mo bty ybty sbty₂ _ n₂)))
      (by rw [show esize prog = 6 from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega))
    hcoh
    (fun v σ' => v = Vunit ∧ ∃ i a, cellPtr idx addr = cellPtr i a ∧
      CellCoh fmapEmpty σ' i ⟨a, intTy, tlFinal n₁ n₂ bs0⟩)
    (by
      intro inst
      refine .trans ?_ (tl_wp_readout loc ann ra mo bty xbty ybty sbty₂ (cellPtr idx addr)
        n₁ n₂ bs0 tlProcSym rs
        (tlRS_labeledAt loc ann ra mo bty xbty ybty sbty₂ (cellPtr idx addr) n₂) hn₁ hn₂ sbty₁
        fmapEmpty symFrame_empty [])
      refine (BigSepM.bigSepM_singleton).1.trans ?_
      iintro Hpt
      iapply (pointsToCell_cellOwn_iff fmapEmpty _ _ _ _).mpr
      iexists idx, addr
      isplit
      · ipureintro; rfl
      · iexact Hpt)
    (th₀ := procThread tlProcSym prog [fmapEmpty]) rfl).mono ?_
  intro v σ' ⟨hv, i, a, heq, hc⟩
  obtain ⟨rfl, rfl⟩ := cellPtr_inj heq
  exact ⟨hv, hc⟩

end TlDrive

end CerberusHeapLang
