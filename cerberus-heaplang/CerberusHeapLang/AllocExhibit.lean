/-
CerberusHeapLang.AllocExhibit — the PUBLIC allocation rules' local
consumers, and the smallest allocating program driven to the engine
from the production cold-start memory.

Contents:

- `alloc_two_creates_wps` — partial-judgment local consumer: TWO
  creates from ONE summed budget, split across ∗ (`allocBudget_split`,
  K2.5) — each create spends its own `allocCost`; no order is imposed.
- `alloc_create_wpt` — total-judgment local consumer at the minimal
  budget `k = 2` (the rule `wpt_create`'s cost bound `2 ≤ k`, applied
  at exactly 2).
- `alloc_create_launch_smoke` — from the production cold-start memory
  `prodMem₀` (empty footprint, one errno allocation, budget `allocCost
  int 4`),
  a single `create` driven through `wpt_engine_boundU_alloc` DELIVERS
  at drive length exactly 2 — an unconditional engine `.done` equation
  whose proof consumes `wpt_create` and `launchResources` (deleting
  either breaks it). The delivered value is a pointer. Engine
  vocabulary only in the statement (GF discharged at the
  satisfiability witness `SpikeGF`).
- KILL/FREE ARC K2, the dispose rule's smoke: `createKillProg` is
  `lets p = create(al, int) in kill(static int, p)` — allocate, then
  dispose through the bound symbol (so both `wps_kill_eval`/`wpt_kill_eval`
  and `wps_kill`/`wpt_kill` are consumed). `alloc_create_kill_wps` is the
  partial-judgment consumer (post: the unit value, the persistent dead
  cell of SOME id/base; the budget is spent); `kill_launch_smoke` drives
  it from `prodMem₀` through `wpt_engine_boundU_alloc` at drive length
  exactly 5 with the ENGINE-FACING readout `∃ id, σ'.deadAllocations.contains
  id = true ∧ σ'.allocations.get? id = none` — the effect `killM` has on
  the tables (CerbMem.lean:1576-1578), read off `deadObj_dead`. (The
  design note's readout `σ'.deadAllocations = [1]` is not derivable from
  the logic's resources — the public `wps_create` abstracts the id and no
  resource speaks for the WHOLE dead list — so the honest engine-facing
  readout is the `contains`/erased pair at the existential id.)

- KILL/FREE ARC K3, the alloc/free rules' smoke: `allocFreeProg` is
  `lets p = alloc(al, n) in free(p)` — the classical cons/dispose pair —
  through the public `wps_alloc`/`wpt_alloc`, `wps_kill_eval`/`wpt_kill_eval`
  (kind-generic, here at `Dynamic0`) and `wps_free`/`wpt_free`.
  `alloc_free_wps` is the partial-judgment consumer (post: the unit value,
  the persistent dead REGION of SOME id/base; the budget `regionCost al n`
  is spent); `free_launch_smoke` drives `lets p = alloc(4, 8) in free(p)`
  from `prodMem₀` through `wpt_engine_boundU_alloc` at drive length exactly
  5 with the ENGINE-FACING readout `∃ id, σ'.deadAllocations.contains id =
  true ∧ σ'.allocations.get? id = none`, read off `deadRegion_dead`.
  PROVISIONAL over `driveU`, as its siblings. `wps_alloc_lit_sym`/
  `wpt_alloc_lit_sym` are the alloc operand-evaluation forms' client
  instances (`alloc(al, n)` at a symbol size), through the public
  `wps_alloc_eval`/`wpt_alloc_eval`.

The whole-program allocating exports — `struct_create_store_adequacy`
(StructExhibit.lean) at the drive, `exhibitA_prod`,
`counter_loop_certified_production` and
`list_reverse_certified_production` (ProdExhibit.lean,
ProdLoopExhibit.lean) on the shipped pipeline — go through the same
public rules (`wps_create`/`wpt_create`) and launchers.

Every create premise here is a closed layout fact of `intTy` (4-byte
scalar int; decode-inertness is `rfl` at every address). NO
operational proof terms: no `Step.*`, no per-step drive equations in
any proof body of this module.
-/
import CerberusHeapLang.API
import CerberusHeapLang.Examples.Layout
import CerberusHeapLang.ProdEntry
import CerberusHeapLang.Exhibit

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic

/-! ## intTy layout facts (closed, rfl) -/

theorem intTy_size {tds : CerbTags.TagDefsMap} : CerbMem.sizeofCtype tds intTy = 4 := rfl

theorem intTy_nonatomic : atomicTy intTy = false := rfl

/-- `int` has positive size (the public create rules' `hsz`). -/
theorem intTy_size_pos {tds : CerbTags.TagDefsMap} : 0 < CerbMem.sizeofCtype tds intTy := by
  rw [intTy_size]
  decide

/-- The scalar-int decode never consults the union-member or
    function-pointer tables — at ANY address and image (the
    address-independent inertness shape the public create rules
    take). -/
theorem intTy_decIndep {tds : CerbTags.TagDefsMap} (a : Int) (bs : List CerbMem.AbsByte) :
    decIndep tds a intTy bs := fun _ _ => rfl

/-- The unspecified fresh image of one int cell. -/
abbrev intUndefBytes (tds : CerbTags.TagDefsMap) : List CerbMem.AbsByte :=
  List.replicate (CerbMem.sizeofCtype tds intTy) undefByte

/-! ## Local consumers (partial and total lanes) -/

section AllocIris

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]

/-- TWO CREATES FROM ONE BUDGET (partial judgment; K2.5): from the
    summed budget `allocCost int al₁ + allocCost int al₂` alone, the
    sequenced pair of creates delivers TWO separately-owned fresh cells.
    The budget is SPLIT across ∗ (`allocBudget_split`) and each create
    spends its own share — the classical additive capacity; the former
    plan `[⟨al₁,int⟩, ⟨al₂,int⟩]` had to be consumed head-first. -/
theorem alloc_two_creates_wps {M : MachineCtx} {p : Option sym} {Ls : LabelSpec GF} {Θ : ProcSpec GF}
    (al₁ al₂ : Int) (pref₁ pref₂ : prefix0) (bty : core_base_type)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    iprop(allocBudget (GF := GF)
        (allocCost M.tagDefs intTy al₁ + allocCost M.tagDefs intTy al₂)) ⊢
      wps M p Ls Θ
        (fun _ _ => iprop(∃ p₁ p₂ : CerbMem.PointerValue,
          pointsToCell M.tagDefs p₁ (.own 1) intTy (intUndefBytes M.tagDefs) ∗
          pointsToCell M.tagDefs p₂ (.own 1) intTy (intUndefBytes M.tagDefs)))
        (sseqExpr bty
          (createExpr loc0 empty_annotation (.IV .Prov_none al₁) intTy pref₁)
          (createExpr loc0 empty_annotation (.IV .Prov_none al₂) intTy pref₂))
        (ev0 :: evs) := by
  iintro Hcap
  rw [show sseqExpr bty
      (createExpr loc0 empty_annotation (.IV .Prov_none al₁) intTy pref₁)
      (createExpr loc0 empty_annotation (.IV .Prov_none al₂) intTy pref₂) =
    Expr [] (Esseq (Pattern [] (CaseBase (none, bty)))
      (createExpr loc0 empty_annotation (.IV .Prov_none al₁) intTy pref₁)
      (createExpr loc0 empty_annotation (.IV .Prov_none al₂) intTy pref₂))
    from rfl]
  icases (allocBudget_split _ _).1 $$ Hcap with ⟨Hcap₁, Hcap₂⟩
  iapply wps_seq
  iapply wps_create loc0 empty_annotation .Prov_none al₁ intTy pref₁ (ev0 :: evs)
    intTy_size_pos intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [Hcap₁]
  · iexact Hcap₁
  iintro %p₁ ⟨Hpt₁, -⟩
  iapply wps_create loc0 empty_annotation .Prov_none al₂ intTy pref₂ (ev0 :: evs)
    intTy_size_pos intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [Hcap₂]
  · iexact Hcap₂
  iintro %p₂ ⟨Hpt₂, -⟩
  iexists p₁, p₂
  isplitl [Hpt₁]
  · iexact Hpt₁
  · iexact Hpt₂

/-- Total-judgment local consumer at the minimal step budget: one create
    from the allocation budget `allocCost int al`, at `k = 2` exactly (1
    create step + 1 pure-value delivery — `wpt_create`'s cost bound). -/
theorem alloc_create_wpt {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    (al : Int) (pref : prefix0) (ρ : EnvStack) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs intTy al)) ⊢
      wpt M p Ls Θ 2
        (fun _ _ => iprop(∃ p : CerbMem.PointerValue,
          pointsToCell M.tagDefs p (.own 1) intTy (intUndefBytes M.tagDefs)))
        (createExpr loc0 empty_annotation (.IV .Prov_none al) intTy pref)
        ρ := by
  iintro Hcap
  iapply wpt_create loc0 empty_annotation .Prov_none al intTy pref ρ
    (Nat.le_refl 2) intTy_size_pos intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [Hcap]
  · iexact Hcap
  iintro %p ⟨Hpt, -⟩
  iexists p
  iexact Hpt

end AllocIris

/-! ## Kill/free arc K2: allocate, then dispose (the static kill's
local consumer) -/

/-- The bound fresh-pointer symbol of the kill smoke. -/
def pKSym : sym := Symbol "" 513 SD_None

/-- `lets p = create(al, int) in kill(static int, p)`. -/
def createKillProg (al : Int) (pref : prefix0) : CoreExpr :=
  Expr [] (Esseq (symPat [] pKSym BTy_unit)
    (createExpr loc0 empty_annotation (.IV .Prov_none al) intTy pref)
    (killOpRedex loc0 empty_annotation (Static0 intTy) (Pexpr [] () (PEsym pKSym))))

/-- Cone membership: `create` is a `BareHead`; the kill is the static
    kill at a symbol operand. -/
theorem createKillProg_frag (al : Int) (pref : prefix0) : Frag (createKillProg al pref) :=
  .sseq_sym .create .create
    (.kill_op rfl (.sym [] pKSym)
      (by rw [show peDepth (Pexpr ([] : List annot) () (PEsym pKSym)) = 1 from rfl,
        show lemDefaultFuel = 999999 + 1 from rfl]; omega))

/-- The head frame after `p` is bound looks `p` up. -/
theorem createKill_lookup_p {f : Fmap sym value} (hf : SymFrame f)
    (p : CerbMem.PointerValue) :
    fmapLookupBy symCmpK pKSym (envAdd pKSym (Vobject (OVpointer p)) f) =
      some (Vobject (OVpointer p)) := by
  rw [envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]

section KillIris

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]

/-- ALLOCATE THEN DISPOSE (partial judgment): from the budget of one int
    alone, `lets p = create(al, int) in kill(static int, p)` delivers
    the unit value and the persistent DEAD cell of the disposed object
    (at some id and base); the budget is spent — `wps_create`, then
    `wps_kill_eval` at the bound symbol, then `wps_kill`. -/
theorem alloc_create_kill_wps {M : MachineCtx} {p : Option sym} {Ls : LabelSpec GF} {Θ : ProcSpec GF}
    (hex : ∀ x, resolveExtern M.extern x = x)
    (al : Int) (pref : prefix0)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (hf : SymFrame ev0) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs intTy al)) ⊢
      wps M p Ls Θ
        (fun w _ => iprop(⌜w = SpikeVal.pure Vunit⌝ ∗
          (∃ (id a : Int), deadObj M.tagDefs id a intTy)))
        (createKillProg al pref) (ev0 :: evs) := by
  iintro Hcap
  rw [show createKillProg al pref =
    Expr [] (Esseq (symPat [] pKSym BTy_unit)
      (createExpr loc0 empty_annotation (.IV .Prov_none al) intTy pref)
      (killOpRedex loc0 empty_annotation (Static0 intTy) (Pexpr [] () (PEsym pKSym))))
    from rfl]
  iapply wps_seq_sym
  iapply wps_create loc0 empty_annotation .Prov_none al intTy pref (ev0 :: evs)
    intTy_size_pos intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [Hcap]
  · iexact Hcap
  iintro %p ⟨Hpt, -⟩
  iexists (Vobject (OVpointer p))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym pKSym BTy_unit]
  iapply wps_kill_eval loc0 empty_annotation (Static0 intTy) _ _ rfl (pv := p)
    (by rw [evalPexpr_sym_of_resolve _ _ _ (hex _)]
        exact lookup_env_head (createKill_lookup_p hf p) evs)
  iapply wps_kill loc0 empty_annotation (Static0 intTy) p intTy _ _ rfl
  isplitl [Hpt]
  · iexact Hpt
  iintro ⟨%id, %a, %hpv, Hd⟩
  isplit
  · ipureintro
    rfl
  iexists id, a
  iexact Hd

end KillIris

/-! ## Kill/free arc K3: allocate a region, then free it (the alloc and
free rules' local consumer) -/

/-- The bound fresh-region-pointer symbol of the alloc/free smoke. -/
def pFSym : sym := Symbol "" 514 SD_None

/-- `lets p = alloc(al, n) in free(p)`. -/
def allocFreeProg (al n : Int) (pref : prefix0) : CoreExpr :=
  Expr [] (Esseq (symPat [] pFSym BTy_unit)
    (allocExpr loc0 empty_annotation (.IV .Prov_none al) (.IV .Prov_none n) pref)
    (killOpRedex loc0 empty_annotation Dynamic0 (Pexpr [] () (PEsym pFSym))))

/-- Cone membership: `alloc` is a `BareHead`; the free is the kill at a
    symbol operand (any kind since K3). -/
theorem allocFreeProg_frag (al n : Int) (pref : prefix0) : Frag (allocFreeProg al n pref) :=
  .sseq_sym .alloc .alloc
    (.kill_op rfl (.sym [] pFSym)
      (by rw [show peDepth (Pexpr ([] : List annot) () (PEsym pFSym)) = 1 from rfl,
        show lemDefaultFuel = 999999 + 1 from rfl]; omega))

/-- The head frame after `p` is bound looks `p` up. -/
theorem allocFree_lookup_p {f : Fmap sym value} (hf : SymFrame f)
    (p : CerbMem.PointerValue) :
    fmapLookupBy symCmpK pFSym (envAdd pFSym (Vobject (OVpointer p)) f) =
      some (Vobject (OVpointer p)) := by
  rw [envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]

section FreeIris

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]

/-- ALLOCATE A REGION, THEN FREE IT (partial judgment): from the budget
    `regionCost al n` alone, `lets p = alloc(al, n) in free(p)` delivers
    the unit value and the persistent DEAD region of the freed allocation
    (at some id and base); the budget is spent — `wps_alloc`, then
    `wps_kill_eval` at the bound symbol (dynamic kind), then `wps_free`. -/
theorem alloc_free_wps {M : MachineCtx} {p : Option sym} {Ls : LabelSpec GF} {Θ : ProcSpec GF}
    (hex : ∀ x, resolveExtern M.extern x = x)
    (al n : Int) (pref : prefix0) (hcost : 0 < regionCost al n)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (hf : SymFrame ev0) :
    iprop(allocBudget (GF := GF) (regionCost al n)) ⊢
      wps M p Ls Θ
        (fun w _ => iprop(⌜w = SpikeVal.pure Vunit⌝ ∗
          (∃ (id a : Int), deadRegion id a n.toNat)))
        (allocFreeProg al n pref) (ev0 :: evs) := by
  iintro Hcap
  rw [show allocFreeProg al n pref =
    Expr [] (Esseq (symPat [] pFSym BTy_unit)
      (allocExpr loc0 empty_annotation (.IV .Prov_none al) (.IV .Prov_none n) pref)
      (killOpRedex loc0 empty_annotation Dynamic0 (Pexpr [] () (PEsym pFSym))))
    from rfl]
  iapply wps_seq_sym
  iapply wps_alloc loc0 empty_annotation .Prov_none .Prov_none al n pref (ev0 :: evs) hcost
  isplitl [Hcap]
  · iexact Hcap
  iintro %id %a ⟨Hr, -⟩
  iexists (Vobject (OVpointer (cellPtr id a)))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym pFSym BTy_unit]
  iapply wps_kill_eval loc0 empty_annotation Dynamic0 _ _ rfl (pv := cellPtr id a)
    (by rw [evalPexpr_sym_of_resolve _ _ _ (hex _)]
        exact lookup_env_head (allocFree_lookup_p hf _) evs)
  iapply wps_free loc0 empty_annotation Dynamic0 id a n.toNat _ _ rfl
  isplitl [Hr]
  · iexact Hr
  iintro Hd
  isplit
  · ipureintro
    rfl
  iexists id, a
  iexact Hd

/-- `alloc(al, n)` at a LITERAL alignment and a SYMBOL size — the
    operand-evaluation form's client instance (the `wps_store_sym_lit`
    shape): verified through the public `wps_alloc_eval`. -/
theorem wps_alloc_lit_sym {M : MachineCtx} {p : Option sym} {Ls : LabelSpec GF} {Θ : ProcSpec GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (align : CerbMem.IntegerValue) (n : sym) (pref : prefix0) (ρ : EnvStack)
    {size : CerbMem.IntegerValue}
    (hn : evalPexpr M.tagDefs M.extern ρ (Pexpr [] () (PEsym n)) =
      some (Vobject (OVinteger size))) :
    wps M p Ls Θ Ψ (allocExpr loc ann align size pref) ρ ⊢
      wps M p Ls Θ Ψ (allocOpRedex loc ann (Pexpr [] () (PEval (Vobject (OVinteger align))))
        (Pexpr [] () (PEsym n)) pref) ρ :=
  wps_alloc_eval loc ann _ _ pref ρ rfl rfl hn

/-- The total twin, through the public `wpt_alloc_eval` (one tau). -/
theorem wpt_alloc_lit_sym {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (align : CerbMem.IntegerValue) (n : sym) (pref : prefix0) (ρ : EnvStack)
    {size : CerbMem.IntegerValue} {k : Nat}
    (hn : evalPexpr M.tagDefs M.extern ρ (Pexpr [] () (PEsym n)) =
      some (Vobject (OVinteger size))) :
    wpt M p Ls Θ k Ψ (allocExpr loc ann align size pref) ρ ⊢
      wpt M p Ls Θ (k + 1) Ψ (allocOpRedex loc ann (Pexpr [] () (PEval (Vobject (OVinteger align))))
        (Pexpr [] () (PEsym n)) pref) ρ :=
  wpt_alloc_eval loc ann _ _ pref ρ rfl rfl hn

end FreeIris

/-! ## The launcher smoke: the chain closes at the engine -/

/-- The one-int budget fits the production cold-start cursor's headroom
    (`errnoAddr − 1`; closed arithmetic — the boundary evaluation of the
    concrete budget). -/
theorem prod_one_int_budget_fits :
    allocCost fmapEmpty intTy 4 ≤ headroom prodMem₀.lastAddress := by
  rw [prodMem₀_lastAddress]
  decide

/-- The 8-byte region at alignment 4 fits the production cold-start
    cursor's headroom (closed arithmetic). -/
theorem prod_region_budget_fits :
    regionCost 4 8 ≤ headroom prodMem₀.lastAddress := by
  rw [prodMem₀_lastAddress]
  decide

/-- THE SMALLEST ALLOCATING PROGRAM AT THE ENGINE: a bare `create`
    at the production cold-start memory (budget `allocCost int 4`),
    proved ONLY through the
    public `wpt_create` and launched ONLY through
    `wpt_engine_boundU_alloc`/`launchResources`, DELIVERS at drive
    length exactly 2 — the engine's own `driveU` returns `.done` with
    a pointer value. Engine vocabulary only. -/
theorem alloc_create_launch_smoke (pref : prefix0) (aids : Nat → Nat) :
    ∃ v σ', driveU spikeCtx aids 2
        (spikeCtx.thread
          (createExpr loc0 empty_annotation (.IV .Prov_none 4) intTy pref)
          (fmapEmpty :: []) spikeCtl)
        prodMem₀ = .done v σ' ∧
      ∃ pv : CerbMem.PointerValue, v = Vobject (OVpointer pv) := by
  obtain ⟨v, σ', h1, h2, -⟩ :=
    wpt_engine_boundU_alloc (GF := SpikeGF) (M := spikeCtx) (ctl := spikeCtl) spikeCtx_wf rfl
      (fun l params cont hl => (spikeCtx_labels_none l hl).elim)
      (fun l params cont hl => (spikeCtx_labels_none l hl).elim)
      (fun _ _ _ _ => iprop(False))
      (createExpr loc0 empty_annotation (.IV .Prov_none 4) intTy pref)
      fmapEmpty [] prodMem₀ (∅ : SpikeHeapF SpikeCell) (allocCost fmapEmpty intTy 4)
      (Frag.create)
      (by rw [show pot (createExpr loc0 empty_annotation (.IV .Prov_none 4)
          intTy pref) = 2 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]
          omega)
      (prodMem₀_launchCoh _ prod_one_int_budget_fits)
      (fun v _ => ∃ pv : CerbMem.PointerValue, v = Vobject (OVpointer pv))
      2
      (by
        intro inst
        iintro ⟨-, Hcap⟩
        isplitr [Hcap]
        · iapply blockSpecsT_intro fun l _ _ _ _ _ _ hl =>
            (spikeCtx_labels_none l hl).elim
        · iapply wpt_create loc0 empty_annotation .Prov_none 4 intTy
            pref (fmapEmpty :: []) (Nat.le_refl 2) intTy_size_pos intTy_nonatomic
            (fun a => intTy_decIndep a _)
          isplitl [Hcap]
          · iexact Hcap
          iintro %p ⟨-, -⟩
          iintro %σ' %ns %κs %nt Hσ
          iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
          ipureintro
          exact ⟨p, rfl⟩)
      aids
  exact ⟨v, σ', h1, h2⟩

/-- ALLOCATE THEN DISPOSE AT THE ENGINE (kill/free arc K2): from the
    production cold-start memory, `lets p = create(4, int) in
    kill(static int, p)`, proved ONLY through the public `wpt_create`,
    `wpt_kill_eval` and `wpt_kill` and launched through
    `wpt_engine_boundU_alloc`, DELIVERS at drive length exactly 5
    (create 2, operand evaluation 1, kill 2) the unit value, and the
    final memory has SOME id dead with its record erased — the
    engine-visible effect of `killM` (CerbMem.lean:1576-1578), read off
    the dead cell (`deadObj_dead`). Engine vocabulary only. PROVISIONAL:
    stated over `driveU` (Adequacy.lean header). -/
theorem kill_launch_smoke (pref : prefix0) (aids : Nat → Nat) :
    ∃ v σ', driveU spikeCtx aids 5
        (spikeCtx.thread (createKillProg 4 pref) (fmapEmpty :: []) spikeCtl)
        prodMem₀ = .done v σ' ∧
      v = Vunit ∧
      ∃ id : Int, σ'.deadAllocations.contains id = true ∧
        σ'.allocations.get? id = none := by
  obtain ⟨v, σ', h1, h2, -⟩ :=
    wpt_engine_boundU_alloc (GF := SpikeGF) (M := spikeCtx) (ctl := spikeCtl) spikeCtx_wf rfl
      (fun l params cont hl => (spikeCtx_labels_none l hl).elim)
      (fun l params cont hl => (spikeCtx_labels_none l hl).elim)
      (fun _ _ _ _ => iprop(False))
      (createKillProg 4 pref)
      fmapEmpty [] prodMem₀ (∅ : SpikeHeapF SpikeCell) (allocCost fmapEmpty intTy 4)
      (createKillProg_frag 4 pref)
      (by rw [show pot (createKillProg 4 pref) = 3 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]
          omega)
      (prodMem₀_launchCoh _ prod_one_int_budget_fits)
      (fun v σ' => v = Vunit ∧ ∃ id : Int, σ'.deadAllocations.contains id = true ∧
        σ'.allocations.get? id = none)
      5
      (by
        intro inst
        iintro ⟨-, Hcap⟩
        isplitr [Hcap]
        · iapply blockSpecsT_intro fun l _ _ _ _ _ _ hl =>
            (spikeCtx_labels_none l hl).elim
        · rw [show createKillProg 4 pref =
            Expr [] (Esseq (symPat [] pKSym BTy_unit)
              (createExpr loc0 empty_annotation (.IV .Prov_none 4) intTy pref)
              (killOpRedex loc0 empty_annotation (Static0 intTy)
                (Pexpr [] () (PEsym pKSym)))) from rfl,
            show (5 : Nat) = 2 + 3 from rfl]
          iapply wpt_seq_sym
          iapply wpt_create loc0 empty_annotation .Prov_none 4 intTy
            pref (fmapEmpty :: []) (Nat.le_refl 2) intTy_size_pos intTy_nonatomic
            (fun a => intTy_decIndep a _)
          isplitl [Hcap]
          · iexact Hcap
          iintro %p ⟨Hpt, -⟩
          iexists (Vobject (OVpointer p))
          isplit
          · ipureintro
            rfl
          rw [update_env_sym pKSym BTy_unit, show (3 : Nat) = 2 + 1 from rfl]
          iapply wpt_kill_eval loc0 empty_annotation (Static0 intTy) _ _ rfl (pv := p)
            (by rw [evalPexpr_sym_of_resolve _ _ _ (resolveExtern_id_of_empty rfl _)]
                exact lookup_env_head (createKill_lookup_p symFrame_empty p) [])
          iapply wpt_kill loc0 empty_annotation (Static0 intTy) p intTy _ _
            (Nat.le_refl 2) rfl
          isplitl [Hpt]
          · iexact Hpt
          iintro ⟨%id, %a, %hpv, Hd⟩
          iintro %σ' %ns %κs %nt Hσ
          icases (stateInterp_iff σ' ns κs nt).mp $$ Hσ
            with ⟨%mm, %mb, %mk, %HG, Hmi, -, -⟩
          ihave %hdead : ⌜σ'.deadAllocations.contains id = true ∧
              σ'.allocations.get? id = none⌝ $$ [Hmi Hd]
          · iapply deadObj_dead spikeCtx.tagDefs HG id a intTy $$ [$Hmi $Hd]
          iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
          ipureintro
          exact ⟨rfl, id, hdead⟩)
      aids
  exact ⟨v, σ', h1, h2⟩

/-- ALLOCATE A REGION THEN FREE IT AT THE ENGINE (kill/free arc K3): from
    the production cold-start memory, `lets p = alloc(4, 8) in free(p)`,
    proved ONLY through the public `wpt_alloc`, `wpt_kill_eval` and
    `wpt_free` and launched through `wpt_engine_boundU_alloc`, DELIVERS at
    drive length exactly 5 (alloc 2, operand evaluation 1, free 2) the unit
    value, and the final memory has SOME id dead with its record erased —
    the engine-visible effect of `killM` (CerbMem.lean:1576-1578), read off
    the dead region (`deadRegion_dead`). Engine vocabulary only.
    PROVISIONAL: stated over `driveU` (Adequacy.lean header). -/
theorem free_launch_smoke (pref : prefix0) (aids : Nat → Nat) :
    ∃ v σ', driveU spikeCtx aids 5
        (spikeCtx.thread (allocFreeProg 4 8 pref) (fmapEmpty :: []) spikeCtl)
        prodMem₀ = .done v σ' ∧
      v = Vunit ∧
      ∃ id : Int, σ'.deadAllocations.contains id = true ∧
        σ'.allocations.get? id = none := by
  obtain ⟨v, σ', h1, h2, -⟩ :=
    wpt_engine_boundU_alloc (GF := SpikeGF) (M := spikeCtx) (ctl := spikeCtl) spikeCtx_wf rfl
      (fun l params cont hl => (spikeCtx_labels_none l hl).elim)
      (fun l params cont hl => (spikeCtx_labels_none l hl).elim)
      (fun _ _ _ _ => iprop(False))
      (allocFreeProg 4 8 pref)
      fmapEmpty [] prodMem₀ (∅ : SpikeHeapF SpikeCell) (regionCost 4 8)
      (allocFreeProg_frag 4 8 pref)
      (by rw [show pot (allocFreeProg 4 8 pref) = 3 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]
          omega)
      (prodMem₀_launchCoh _ prod_region_budget_fits)
      (fun v σ' => v = Vunit ∧ ∃ id : Int, σ'.deadAllocations.contains id = true ∧
        σ'.allocations.get? id = none)
      5
      (by
        intro inst
        iintro ⟨-, Hcap⟩
        isplitr [Hcap]
        · iapply blockSpecsT_intro fun l _ _ _ _ _ _ hl =>
            (spikeCtx_labels_none l hl).elim
        · rw [show allocFreeProg 4 8 pref =
            Expr [] (Esseq (symPat [] pFSym BTy_unit)
              (allocExpr loc0 empty_annotation (.IV .Prov_none 4) (.IV .Prov_none 8) pref)
              (killOpRedex loc0 empty_annotation Dynamic0
                (Pexpr [] () (PEsym pFSym)))) from rfl,
            show (5 : Nat) = 2 + 3 from rfl]
          iapply wpt_seq_sym
          iapply wpt_alloc loc0 empty_annotation .Prov_none .Prov_none 4 8
            pref (fmapEmpty :: []) (Nat.le_refl 2) (by decide)
          isplitl [Hcap]
          · iexact Hcap
          iintro %id %a ⟨Hr, -⟩
          iexists (Vobject (OVpointer (cellPtr id a)))
          isplit
          · ipureintro
            rfl
          rw [update_env_sym pFSym BTy_unit, show (3 : Nat) = 2 + 1 from rfl]
          iapply wpt_kill_eval loc0 empty_annotation Dynamic0 _ _ rfl (pv := cellPtr id a)
            (by rw [evalPexpr_sym_of_resolve _ _ _ (resolveExtern_id_of_empty rfl _)]
                exact lookup_env_head (allocFree_lookup_p symFrame_empty _) [])
          iapply wpt_free loc0 empty_annotation Dynamic0 id a _ _ _
            (Nat.le_refl 2) rfl
          isplitl [Hr]
          · iexact Hr
          iintro Hd
          iintro %σ' %ns %κs %nt Hσ
          icases (stateInterp_iff σ' ns κs nt).mp $$ Hσ
            with ⟨%mm, %mb, %mk, %HG, Hmi, -, -⟩
          ihave %hdead : ⌜σ'.deadAllocations.contains id = true ∧
              σ'.allocations.get? id = none⌝ $$ [Hmi Hd]
          · iapply deadRegion_dead HG id a _ $$ [$Hmi $Hd]
          iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
          ipureintro
          exact ⟨rfl, id, hdead⟩)
      aids
  exact ⟨v, σ', h1, h2⟩

end CerberusHeapLang
