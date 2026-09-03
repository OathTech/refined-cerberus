/-
CerberusHeapLang.RegionLoopExhibit — N REGIONS FROM ONE LINEAR BUDGET:
the allocation budget as a LOOP INVARIANT, spent one `alloc` per
iteration through the split law and returned by `free` (kill/free arc
K4, the second exhibit).

THE PROGRAM (authored Core — `n` times: allocate a region, free it):

    save rl: (i : int := n) in
      if i > 0 then
        lets p = alloc(al, sz) in
        lets _ = free(p) in
        run rl(i - 1)
      else unit

WHY THIS SHAPE, HONESTLY. The K4 charter's second exhibit was a
MALLOC'D LINKED LIST — `alloc` `n` region nodes, LINK them by stores
through region views, walk and `free` each. It is NOT statable through
the public rules of this tree: K3 delivered `alloc` (`regionOwn`, untyped
bytes) and `free`, but NO load or store rule over `regionOwn`/`regionView`
exists — every typed access rule (`store_atomic`, `storeAt_atomic`,
`wps_store_cell_at`, …) is stated over the OBJECT bundles (`pointsToCell`/
`cellOwn`/`pointsToView`, metadata `ty := some ty`, `dynamic := false`),
and a coercion `regionOwn ↔ pointsToCell` is unsupported by the coupling
BY DESIGN (`MetaCoh` pins a region's `ty := none` and `dynamic := true`
to the engine's own record, K1). The memM seams (`loadM_live`/
`storeM_live`, Heap.lean) ARE stated at any metadata cell, so region
access rules are a rule-addition follow-up, not a coupling redesign;
this is recorded as the arc's finding (the K4 record) and the gap is
NOT worked around here. What IS statable is the budget's first real
loop client: `n` allocations from ONE budget `n * regionCost al sz`,
split per iteration by `allocBudget_split` (K2.5 — the ∗-splittable
capacity the professor asked for), each region freed by `free`
(`wps_free_emp`/`wpt_free_emp`, the textbook `{p ↦ region} free(p)
{emp}`), termination at a budget linear in `n`.

THE RULES CONSUMED (all public, API.lean): `wps_alloc`/`wpt_alloc`
(K3), `wps_kill_eval`/`wpt_kill_eval` at `Dynamic0` (the operand form),
`wps_free_emp`/`wpt_free_emp` (K3), `allocBudget_split` (K2.5),
`wps_if_true`/`wps_if_false` at the `PEop OpGt` guard, `wps_seq_sym`
(the bound region pointer), `wps_seq` (the free's unit), `wps_run` at
the `PEop OpSub` argument, `wps_ofVal`, `wps_save_vals`, the
label-context rules; total twins. No `Step.*`, no per-step drive
equations.

THE STATEMENTS. `rl_wps`: `allocBudget (n.toNat * regionCost al sz) ⊢
wps … (fun w _ => ⌜w = .pure Vunit⌝) (rlProg … n) [fmapEmpty]` (partial;
the invariant `allocBudget (i.toNat * regionCost al sz)` at loop counter
`i ≥ 0`); `rl_wpt` at the DERIVED budget `rlCost n.toNat + 1 = 7·n.toNat
+ 3` (7 per iteration: guard 1 + alloc 2 + free 3 + jump 1; exit 2:
guard 1 + unit delivery 1; entry 1). Engine-facing:
`region_loop_certified_total` (the `driveU` lane, PROVISIONAL as every
`driveU` export): from any memory launching the empty footprint with the
budget (`LaunchCoh … ∅ (n.toNat * regionCost al sz)`), the engine
DELIVERS `Vunit` at exactly `7·n.toNat + 3` drive steps — `n` regions
allocated and freed, no out-of-memory kill, because the budget fits.
PRODUCTION: `region_loop_certified_production` — the shipped pipeline on
the self-contained file is EXACTLY ONE Active execution delivering
`Vunit`, under the budget-fits-the-cold-start premise `n.toNat *
regionCost al sz ≤ headroom prodMem₀.lastAddress` (the boundary
evaluation of the concrete budget, as the fib/counter productions carry
their `hfuel`).
-/
import CerberusHeapLang.API
import CerberusHeapLang.Exhibit
import CerberusHeapLang.ProdEntry

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Map

/-! ## THE PROGRAM (authored Core) -/

def rlISym : sym := Symbol "" 611 SD_None
def rlPSym : sym := Symbol "" 612 SD_None
def rlLoopSym : sym := Symbol "" 613 SD_None
def rlProcSym : sym := Symbol "" 614 SD_None

/-- The guard `i > 0`. -/
def rlGuardPe : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpGt (Pexpr [] () (PEsym rlISym))
    (Pexpr [] () (PEval (ivVal 0))))

/-- The back-edge argument `i - 1`. -/
def rlDecPe : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpSub (Pexpr [] () (PEsym rlISym))
    (Pexpr [] () (PEval (ivVal 1))))

/-- `free(p)` at the bound region pointer — `Kill Dynamic0` at the symbol. -/
def rlFreeE (loc : CerbLocation.Loc) (ann : core_run_annotation) : CoreExpr :=
  killOpRedex loc ann Dynamic0 (Pexpr [] () (PEsym rlPSym))

/-- The registered loop body. -/
def rlBody (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (al sz : Int) (pref : prefix0) (pbty ubty : core_base_type) : CoreExpr :=
  Expr [] (Eif rlGuardPe
    (Expr [] (Esseq (symPat [] rlPSym pbty)
      (allocExpr loc ann (.IV .Prov_none al) (.IV .Prov_none sz) pref)
      (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty)))
        (rlFreeE loc ann)
        (Expr [] (Erun ra rlLoopSym [rlDecPe]))))))
    (ofVal (.pure Vunit)))

/-- The save parameter (`i := n`, the literal count). -/
def rlParams (ibty : core_base_type) (n : Int) :
    List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)) :=
  [(rlISym, ((ibty, none), Pexpr [] () (PEval (ivVal n))))]

/-- The whole program. -/
def rlProg (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (al sz : Int) (pref : prefix0) (sbty ibty pbty ubty : core_base_type)
    (n : Int) : CoreExpr :=
  Expr [] (Esave (rlLoopSym, sbty) (rlParams ibty n)
    (rlBody loc ann ra al sz pref pbty ubty))

/-- The label map. -/
def rlQ (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (al sz : Int) (pref : prefix0) (ibty pbty ubty : core_base_type) : LabelMap :=
  fmapAddBy symCmpL rlLoopSym
    ([(rlISym, ibty)], rlBody loc ann ra al sz pref pbty ubty)
    fmapEmpty

/-- The run state carrying the two-level `labeled` tie. -/
def rlRS (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (al sz : Int) (pref : prefix0) (ibty pbty ubty : core_base_type) :
    core_run_state :=
  { spikeRunState with
      labeled := fmapAddBy symCmpL rlProcSym
        (rlQ loc ann ra al sz pref ibty pbty ubty) fmapEmpty }

section RlFacts

variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (al sz : Int) (pref : prefix0) (ibty pbty ubty : core_base_type)

theorem rlQ_lookup :
    lookupLabel (rlQ loc ann ra al sz pref ibty pbty ubty) rlLoopSym =
      some ([(rlISym, ibty)], rlBody loc ann ra al sz pref pbty ubty) := by
  unfold lookupLabel rlQ
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

theorem rlQ_inv {l : sym} {params : List (sym × core_base_type)}
    {cont : CoreExpr}
    (h : lookupLabel (rlQ loc ann ra al sz pref ibty pbty ubty) l =
      some (params, cont)) :
    params = [(rlISym, ibty)] ∧ cont = rlBody loc ann ra al sz pref pbty ubty := by
  unfold lookupLabel rlQ at h
  rw [fmapLookupBy_addBy_empty] at h
  split at h
  · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    exact ⟨h1.symm ▸ rfl, h2.symm ▸ rfl⟩
  · cases h

theorem rlRS_labeledAt :
    LabeledAt (rlRS loc ann ra al sz pref ibty pbty ubty) rlProcSym
      (rlQ loc ann ra al sz pref ibty pbty ubty) := by
  unfold LabeledAt rlRS
  show fmapLookupBy _ _ (fmapAddBy symCmpL rlProcSym _ fmapEmpty) = _
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

end RlFacts

/-! ## Frames, lookups, bindings, evaluation -/

/-- The frame after the loop binding (i). -/
def rlFrame (vi : value) (f : Fmap sym value) : Fmap sym value :=
  envAdd rlISym vi f

/-- ... after additionally binding the region pointer. -/
def rlFrameP (vp vi : value) (f : Fmap sym value) : Fmap sym value :=
  envAdd rlPSym vp (rlFrame vi f)

theorem rlFrame_symFrame {f : Fmap sym value} (hf : SymFrame f) (vi : value) :
    SymFrame (rlFrame vi f) :=
  hf.add _ _

theorem rlFrameP_symFrame {f : Fmap sym value} (hf : SymFrame f) (vp vi : value) :
    SymFrame (rlFrameP vp vi f) :=
  (rlFrame_symFrame hf _).add _ _

section RlLookups

variable {f : Fmap sym value} (hf : SymFrame f) (vp vi : value)

include hf

theorem rlFrame_lookup_i :
    fmapLookupBy symCmpK rlISym (rlFrame vi f) = some vi := by
  unfold rlFrame
  rw [envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]

theorem rlFrameP_lookup_p :
    fmapLookupBy symCmpK rlPSym (rlFrameP vp vi f) = some vp := by
  unfold rlFrameP
  rw [envAdd_lookup (rlFrame_symFrame hf _) symCmpK, if_pos (by decide +kernel)]

theorem rlFrameP_lookup_i :
    fmapLookupBy symCmpK rlISym (rlFrameP vp vi f) = some vi := by
  unfold rlFrameP
  rw [envAdd_lookup (rlFrame_symFrame hf _) symCmpK,
    if_neg (by decide +kernel), rlFrame_lookup_i hf]

end RlLookups

theorem bindSave_rl (ibty : core_base_type) (n : Int)
    (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindSaveParams (rlParams ibty n) [ivVal n] (f :: rest) =
      rlFrame (ivVal n) f :: rest := by
  show update_env (mk_sym_pat rlISym ibty) (ivVal n) (f :: rest) = _
  rw [update_env_cons, update_env_aux_sym]
  rfl

theorem bindArgs_rl (ibty : core_base_type) (v : value) (f : Fmap sym value)
    (rest : List (Fmap sym value)) :
    bindArgs [(rlISym, ibty)] [v] (f :: rest) = rlFrame v f :: rest := by
  show update_env (mk_sym_pat rlISym ibty) v (f :: rest) = _
  rw [update_env_cons, update_env_aux_sym]
  rfl

section RlEval

variable {f : Fmap sym value} (hf : SymFrame f) (rest : List (Fmap sym value))

include hf

/-- The guard at the counter `i`: the engine's own `OpGt` on integer
    values, delivering the boolean `0 < i`. -/
theorem rl_guard_eval (i : Int) :
    evalPexpr fmapEmpty fmapEmpty (rlFrame (ivVal i) f :: rest) rlGuardPe =
      some (boolValue (decide (0 < i))) := by
  unfold rlGuardPe
  rw [evalPexpr_op]
  rw [show evalPexpr fmapEmpty fmapEmpty (rlFrame (ivVal i) f :: rest)
      (Pexpr [] () (PEsym rlISym)) = some (ivVal i) from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (rlFrame_lookup_i hf _) rest]
  show evalBinop binop.OpGt (ivVal i) (ivVal 0) = _
  unfold evalBinop ivVal
  show (CerbMem.ltIval (CerbMem.integerIval 0)
    (CerbMem.integerIval i)).map boolValue = _
  rfl

/-- The free's operand: the bound region pointer. -/
theorem rl_p_eval (vp vi : value) :
    evalPexpr fmapEmpty fmapEmpty (rlFrameP vp vi f :: rest)
      (Pexpr [] () (PEsym rlPSym)) = some vp := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (rlFrameP_lookup_p hf _ _) rest

/-- The back-edge argument `i - 1` at the frame after the pointer is bound. -/
theorem rl_args_eval (vp : value) (i : Int) :
    evalPexprs fmapEmpty fmapEmpty (rlFrameP vp (ivVal i) f :: rest) [rlDecPe] =
      some [ivVal (i - 1)] := by
  rw [evalPexprs_cons]
  rw [show evalPexpr fmapEmpty fmapEmpty (rlFrameP vp (ivVal i) f :: rest)
      rlDecPe = some (ivVal (i - 1)) from by
    unfold rlDecPe
    rw [evalPexpr_op]
    rw [show evalPexpr fmapEmpty fmapEmpty (rlFrameP vp (ivVal i) f :: rest)
        (Pexpr [] () (PEsym rlISym)) = some (ivVal i) from by
      rw [evalPexpr_sym_empty]
      exact lookup_env_head (rlFrameP_lookup_i hf _ _) rest]
    rfl]
  rfl

end RlEval

/-! ## The certified cone membership -/

section RlFrag

variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (al sz : Int) (pref : prefix0) (pbty ubty : core_base_type)

/-- The label body is in the certified cone: `alloc` is a `BareHead`
    (the bound region pointer), the free is `Frag.kill_op` at the symbol
    (dynamic kind), the guard and the jump argument are `PePure` binops. -/
theorem rlBody_frag : Frag (rlBody loc ann ra al sz pref pbty ubty) :=
  .if_ (PePure.of_isPePure rfl)
    (by rw [show peDepth rlGuardPe = 2 from rfl,
      show lemDefaultFuel = 999999 + 1 from rfl]; omega)
    (.sseq_sym .alloc .alloc
      (.sseq
        (.kill_op rfl (.sym [] rlPSym)
          (by rw [show peDepth (Pexpr ([] : List annot) () (PEsym rlPSym)) = 1
              from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega))
        (.run (PePure.all_of_isPePure rfl) (by
          intro pe hpe
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
          subst hpe
          rw [show peDepth rlDecPe = 2 from rfl,
            show lemDefaultFuel = 999999 + 1 from rfl]
          omega))))
    (frag_ofVal (.pure Vunit))

theorem rlBody_pot : pot (rlBody loc ann ra al sz pref pbty ubty) = 5 := rfl

theorem rlProg_pot (sbty ibty : core_base_type) (n : Int) :
    pot (rlProg loc ann ra al sz pref sbty ibty pbty ubty n) = 6 := rfl

theorem rlParams_depth (ibty : core_base_type) (n : Int) :
    ∀ pe ∈ saveParamPexprs (rlParams ibty n), peDepth pe ≤ lemDefaultFuel := by
  intro pe hpe
  simp only [rlParams, saveParamPexprs, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hpe
  subst hpe
  exact peDepth_val_le _ _

end RlFrag

/-! ## THE INVARIANT: the remaining budget, linear in the counter -/

section RlIris

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (al sz : Int) (pref : prefix0) (ibty pbty ubty : core_base_type)
  (hcost : 0 < regionCost al sz)
variable (p : sym) (rs : core_run_state)
  (hQ : LabeledAt rs p (rlQ loc ann ra al sz pref ibty pbty ubty))

/-- The postcondition: the unit value (the budget is spent, nothing else
    is owned — the textbook `emp`). -/
abbrev rlPost : SpikeVal → EnvStack → IProp GF := fun w _ =>
  iprop(⌜w = SpikeVal.pure Vunit⌝)

/-- THE LOOP INVARIANT: the counter `i ≥ 0` and the budget for `i` more
    regions, `allocBudget (i.toNat * regionCost al sz)`. UNFRAMED. -/
abbrev rlLs : LabelSpec GF := fun _ args ρ =>
  iprop(∃ (i : Int) (f : Fmap sym value) (renv : List (Fmap sym value)),
    ⌜args = [ivVal i] ∧ 0 ≤ i ∧ ρ = f :: renv ∧ SymFrame f⌝ ∗
    allocBudget (i.toNat * regionCost al sz))

include hcost hQ

/-- The loop body at any invariant frame: the guard decides; on the
    taken branch the budget is SPLIT (`allocBudget_split`) into this
    iteration's `regionCost` and the rest, `wps_alloc` spends the head,
    `wps_free_emp` returns the region, the jump re-establishes the
    invariant at `i - 1`. -/
theorem rl_body_wps (i : Int) (f : Fmap sym value)
    (renv : List (Fmap sym value)) (hf : SymFrame f) :
    allocBudget (GF := GF) (i.toNat * regionCost al sz) ⊢
      wps (procCtx rs) (some p) (rlLs al sz) emptyProcSpec rlPost (rlBody loc ann ra al sz pref pbty ubty)
        (rlFrame (ivVal i) f :: renv) := by
  rw [show rlBody loc ann ra al sz pref pbty ubty =
    Expr [] (Eif rlGuardPe
      (Expr [] (Esseq (symPat [] rlPSym pbty)
        (allocExpr loc ann (.IV .Prov_none al) (.IV .Prov_none sz) pref)
        (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty)))
          (rlFreeE loc ann)
          (Expr [] (Erun ra rlLoopSym [rlDecPe]))))))
      (ofVal (.pure Vunit))) from rfl]
  iintro Hcap
  by_cases hpos : 0 < i
  · -- i > 0: one more region
    iapply wps_if_true [] rlGuardPe _ _ _
      (by rw [procCtx_extern, rl_guard_eval hf renv i, decide_eq_true hpos]; rfl)
    rw [show i.toNat * regionCost al sz =
      regionCost al sz + (i - 1).toNat * regionCost al sz from by
        have : i.toNat = (i - 1).toNat + 1 := by omega
        rw [this, Nat.add_mul, Nat.one_mul, Nat.add_comm]]
    icases (allocBudget_split _ _).1 $$ Hcap with ⟨Hc, Hrest⟩
    iapply wps_seq_sym
    iapply wps_alloc loc ann .Prov_none .Prov_none al sz pref _ hcost
    isplitl [Hc]
    · iexact Hc
    iintro %id %a ⟨Hr, -⟩
    iexists (Vobject (OVpointer (cellPtr id a)))
    isplit
    · ipureintro
      rfl
    rw [update_env_sym rlPSym pbty]
    rw [show envAdd rlPSym (Vobject (OVpointer (cellPtr id a))) (rlFrame (ivVal i) f) =
      rlFrameP (Vobject (OVpointer (cellPtr id a))) (ivVal i) f from rfl]
    iapply wps_seq
    rw [show rlFreeE loc ann = killOpRedex loc ann Dynamic0 (Pexpr [] () (PEsym rlPSym))
      from rfl]
    iapply wps_kill_eval loc ann Dynamic0 _ _ rfl (pv := cellPtr id a)
      (by rw [procCtx_extern]; exact rl_p_eval hf renv _ _)
    iapply wps_free_emp loc ann Dynamic0 id a _ _ _ rfl
    isplitl [Hr]
    · iexact Hr
    iapply wps_run [] ra rlLoopSym [rlDecPe] _ _
      (by rw [procCtx_labels hQ]
          exact rlQ_lookup loc ann ra al sz pref ibty pbty ubty)
      (rl_args_eval hf renv _ i)
    iexists (i - 1), (rlFrameP (Vobject (OVpointer (cellPtr id a))) (ivVal i) f), renv
    isplit
    · ipureintro
      exact ⟨rfl, by omega, rfl, rlFrameP_symFrame hf _ _⟩
    · iexact Hrest
  · -- i = 0: exit with the unit value
    iapply wps_if_false [] rlGuardPe _ _ _
      (by rw [procCtx_extern, rl_guard_eval hf renv i, decide_eq_false hpos]; rfl)
    iapply wps_ofVal (SpikeVal.pure Vunit) _
    ipureintro
    rfl

/-- THE BLOCK SPECIFICATION. -/
theorem rl_blockSpecs :
    ⊢ blockSpecs (GF := GF) (procCtx rs) (some p) (rlLs al sz) emptyProcSpec rlPost := by
  refine blockSpecs_intro fun l params cont args env0 envs hl => ?_
  rw [procCtx_labels hQ] at hl
  obtain ⟨rfl, rfl⟩ := rlQ_inv loc ann ra al sz pref ibty pbty ubty hl
  iintro ⟨%i, %f, %renv, %hpure, Hcap⟩
  obtain ⟨rfl, -, hρ, hf⟩ := hpure
  obtain ⟨rfl, rfl⟩ : f = env0 ∧ renv = envs := by
    have h1 := congrArg (fun l => l.head?) hρ
    have h2 := congrArg (fun l => l.tail) hρ
    simp at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  rw [bindArgs_rl]
  iapply rl_body_wps loc ann ra al sz pref ibty pbty ubty hcost p rs hQ i f renv hf
  iexact Hcap

/-- N REGIONS FROM ONE BUDGET (partial): `{allocBudget (n · regionCost al
    sz)} rl(n) {ret unit. emp}`. -/
theorem rl_wps (sbty : core_base_type) (n : Int) :
    allocBudget (GF := GF) (n.toNat * regionCost al sz) ⊢
      wps (procCtx rs) (some p) (rlLs al sz) emptyProcSpec rlPost
        (rlProg loc ann ra al sz pref sbty ibty pbty ubty n) [fmapEmpty] := by
  rw [show rlProg loc ann ra al sz pref sbty ibty pbty ubty n =
    Expr [] (Esave (rlLoopSym, sbty) (rlParams ibty n)
      (rlBody loc ann ra al sz pref pbty ubty)) from rfl]
  iintro Hcap
  iapply wps_save [] (rlLoopSym, sbty) _ _ fmapEmpty [] (cvals := [ivVal n]) rfl
  rw [bindSave_rl]
  iapply rl_body_wps loc ann ra al sz pref ibty pbty ubty hcost p rs hQ n
    fmapEmpty [] symFrame_empty
  iexact Hcap

end RlIris

/-! ## The readout: the unit post as an engine fact -/

section RlReadout

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]

/-- The unit post reads out as the engine fact `v = Vunit`. -/
theorem rlPost_readout (w : SpikeVal) (ρ' : EnvStack) :
    rlPost (GF := GF) w ρ' ⊢ readoutPost (fun v _ => v = Vunit) w ρ' := by
  iintro %hw
  subst hw
  iintro %σ' %ns %κs %nt Hσ
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  rfl

end RlReadout

/-! ## THE TOTAL LANE: the variant is the counter -/

/-- The derived per-label-entry step budget at counter `k`: 7 per
    iteration (guard 1 + alloc 2 + free 3 + jump 1), exit 2 (guard 1 +
    unit delivery 1). -/
def rlCost (k : Nat) : Nat := 7 * k + 2

section RlTotal

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (al sz : Int) (pref : prefix0) (ibty pbty ubty : core_base_type)
  (hcost : 0 < regionCost al sz)
variable (p : sym) (rs : core_run_state)
  (hQ : LabeledAt rs p (rlQ loc ann ra al sz pref ibty pbty ubty))

/-- The variant-indexed label context: the invariant plus the variant
    pin `m = rlCost i.toNat`. -/
abbrev rlLsT : LabelSpecT GF := fun _ m args ρ =>
  iprop(∃ (i : Int) (f : Fmap sym value) (renv : List (Fmap sym value)),
    ⌜args = [ivVal i] ∧ 0 ≤ i ∧ m = rlCost i.toNat ∧ ρ = f :: renv ∧ SymFrame f⌝ ∗
    allocBudget (i.toNat * regionCost al sz))

include hcost hQ

theorem rl_body_wpt (i : Int) (hi : 0 ≤ i) (f : Fmap sym value)
    (renv : List (Fmap sym value)) (hf : SymFrame f) :
    allocBudget (GF := GF) (i.toNat * regionCost al sz) ⊢
      wpt (procCtx rs) (some p) (rlLsT al sz) emptyProcSpecT (rlCost i.toNat) rlPost
        (rlBody loc ann ra al sz pref pbty ubty) (rlFrame (ivVal i) f :: renv) := by
  rw [show rlBody loc ann ra al sz pref pbty ubty =
    Expr [] (Eif rlGuardPe
      (Expr [] (Esseq (symPat [] rlPSym pbty)
        (allocExpr loc ann (.IV .Prov_none al) (.IV .Prov_none sz) pref)
        (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty)))
          (rlFreeE loc ann)
          (Expr [] (Erun ra rlLoopSym [rlDecPe]))))))
      (ofVal (.pure Vunit))) from rfl]
  iintro Hcap
  by_cases hpos : 0 < i
  · rw [show rlCost i.toNat = (2 + (3 + (1 + rlCost (i - 1).toNat))) + 1 from by
      unfold rlCost; omega]
    iapply wpt_if_true [] rlGuardPe _ _ _
      (by rw [procCtx_extern, rl_guard_eval hf renv i, decide_eq_true hpos]; rfl)
    rw [show i.toNat * regionCost al sz =
      regionCost al sz + (i - 1).toNat * regionCost al sz from by
        have : i.toNat = (i - 1).toNat + 1 := by omega
        rw [this, Nat.add_mul, Nat.one_mul, Nat.add_comm]]
    icases (allocBudget_split _ _).1 $$ Hcap with ⟨Hc, Hrest⟩
    iapply wpt_seq_sym
    iapply wpt_alloc loc ann .Prov_none .Prov_none al sz pref _ (Nat.le_refl 2) hcost
    isplitl [Hc]
    · iexact Hc
    iintro %id %a ⟨Hr, -⟩
    iexists (Vobject (OVpointer (cellPtr id a)))
    isplit
    · ipureintro
      rfl
    rw [update_env_sym rlPSym pbty]
    rw [show envAdd rlPSym (Vobject (OVpointer (cellPtr id a))) (rlFrame (ivVal i) f) =
      rlFrameP (Vobject (OVpointer (cellPtr id a))) (ivVal i) f from rfl]
    iapply wpt_seq
    rw [show rlFreeE loc ann = killOpRedex loc ann Dynamic0 (Pexpr [] () (PEsym rlPSym))
      from rfl, show (3 : Nat) = 2 + 1 from rfl]
    iapply wpt_kill_eval loc ann Dynamic0 _ _ rfl (pv := cellPtr id a)
      (by rw [procCtx_extern]; exact rl_p_eval hf renv _ _)
    iapply wpt_free_emp loc ann Dynamic0 id a _ _ _ (Nat.le_refl 2) rfl
    isplitl [Hr]
    · iexact Hr
    iapply wpt_run [] ra rlLoopSym [rlDecPe] _ _ (rlCost (i - 1).toNat)
      (by rw [procCtx_labels hQ]
          exact rlQ_lookup loc ann ra al sz pref ibty pbty ubty)
      (rl_args_eval hf renv _ i)
      (Nat.le_refl _)
    iexists (i - 1), (rlFrameP (Vobject (OVpointer (cellPtr id a))) (ivVal i) f), renv
    isplit
    · ipureintro
      exact ⟨rfl, by omega, rfl, rfl, rlFrameP_symFrame hf _ _⟩
    · iexact Hrest
  · rw [show rlCost i.toNat = 1 + 1 from by
      unfold rlCost; omega]
    iapply wpt_if_false [] rlGuardPe _ _ _
      (by rw [procCtx_extern, rl_guard_eval hf renv i, decide_eq_false hpos]; rfl)
    iapply wpt_ofVal (SpikeVal.pure Vunit) _ (Nat.le_refl 1)
    ipureintro
    rfl

/-- THE TOTAL BLOCK SPECIFICATION. -/
theorem rl_blockSpecsT :
    ⊢ blockSpecsT (GF := GF) (procCtx rs) (some p) (rlLsT al sz) emptyProcSpecT rlPost := by
  refine blockSpecsT_intro fun l params cont args env0 envs m hl => ?_
  rw [procCtx_labels hQ] at hl
  obtain ⟨rfl, rfl⟩ := rlQ_inv loc ann ra al sz pref ibty pbty ubty hl
  iintro ⟨%i, %f, %renv, %hpure, Hcap⟩
  obtain ⟨rfl, hi, rfl, hρ, hf⟩ := hpure
  obtain ⟨rfl, rfl⟩ : f = env0 ∧ renv = envs := by
    have h1 := congrArg (fun l => l.head?) hρ
    have h2 := congrArg (fun l => l.tail) hρ
    simp at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  rw [bindArgs_rl]
  iapply rl_body_wpt loc ann ra al sz pref ibty pbty ubty hcost p rs hQ i hi f renv hf
  iexact Hcap

/-- N REGIONS FROM ONE BUDGET (total), at budget `rlCost n.toNat + 1`. -/
theorem rl_wpt (sbty : core_base_type) (n : Int) (hn : 0 ≤ n) :
    allocBudget (GF := GF) (n.toNat * regionCost al sz) ⊢
      wpt (procCtx rs) (some p) (rlLsT al sz) emptyProcSpecT (rlCost n.toNat + 1) rlPost
        (rlProg loc ann ra al sz pref sbty ibty pbty ubty n) [fmapEmpty] := by
  rw [show rlProg loc ann ra al sz pref sbty ibty pbty ubty n =
    Expr [] (Esave (rlLoopSym, sbty) (rlParams ibty n)
      (rlBody loc ann ra al sz pref pbty ubty)) from rfl]
  iintro Hcap
  iapply wpt_save_vals [] (rlLoopSym, sbty) _ _ fmapEmpty [] (cvals := [ivVal n]) rfl
  rw [bindSave_rl]
  iapply rl_body_wpt loc ann ra al sz pref ibty pbty ubty hcost p rs hQ n hn
    fmapEmpty [] symFrame_empty
  iexact Hcap

/-- The block specifications at the engine readout (what the launches consume). -/
theorem rl_blockSpecsT_readout :
    ⊢ blockSpecsT (GF := GF) (procCtx rs) (some p) (rlLsT al sz) emptyProcSpecT
      (readoutPost (fun v _ => v = Vunit)) :=
  (rl_blockSpecsT loc ann ra al sz pref ibty pbty ubty hcost p rs hQ).trans
    (blockSpecsT_mono rlPost_readout)

/-- The whole program at the engine readout. -/
theorem rl_wpt_readout (sbty : core_base_type) (n : Int) (hn : 0 ≤ n) :
    allocBudget (GF := GF) (n.toNat * regionCost al sz) ⊢
      wpt (procCtx rs) (some p) (rlLsT al sz) emptyProcSpecT (rlCost n.toNat + 1)
        (readoutPost (fun v _ => v = Vunit))
        (rlProg loc ann ra al sz pref sbty ibty pbty ubty n) [fmapEmpty] :=
  (rl_wpt loc ann ra al sz pref ibty pbty ubty hcost p rs hQ sbty n hn).trans
    (wpt_mono rlPost_readout _ _ _)

end RlTotal

section RlExport

variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (al sz : Int) (pref : prefix0) (sbty ibty pbty ubty : core_base_type)

/-- N REGIONS FROM ONE BUDGET, THE UNCONDITIONAL TOTAL ENGINE EQUATION:
    from any memory that launches the empty footprint with the budget
    `n.toNat * regionCost al sz` (`LaunchCoh`: the invariant holds and the
    budget fits below the cursor), the engine's `driveU` at the DERIVED
    bound `7·n.toNat + 3` DELIVERS `Vunit` — `n` regions allocated and
    freed, no out-of-memory kill. A corollary of the total judgment through
    the generic simulation (`wpt_engine_boundU_alloc`). PROVISIONAL: stated
    over `driveU`. -/
theorem region_loop_certified_total (hcost : 0 < regionCost al sz)
    (n : Int) (hn : 0 ≤ n) (σ₀ : Mem)
    (hl : LaunchCoh fmapEmpty σ₀ (∅ : SpikeHeapF SpikeCell) (n.toNat * regionCost al sz))
    (aids : Nat → Nat) :
    ∃ σ' : Mem,
      driveU (procCtx (rlRS loc ann ra al sz pref ibty pbty ubty)) aids
        (7 * n.toNat + 3)
        (procThread rlProcSym
          (rlProg loc ann ra al sz pref sbty ibty pbty ubty n) [fmapEmpty]) σ₀ =
        .done Vunit σ' := by
  have hQ := rlRS_labeledAt loc ann ra al sz pref ibty pbty ubty
  have hk : rlCost n.toNat + 1 = 7 * n.toNat + 3 := by
    unfold rlCost
    omega
  rw [← hk]
  have hlbl := procCtx_labels hQ
  obtain ⟨v, σ', hdone, rfl, -⟩ :=
    wpt_engine_boundU_alloc (GF := SpikeGF)
      (M := procCtx (rlRS loc ann ra al sz pref ibty pbty ubty)) (ctl := procCtl rlProcSym)
      (procCtx_wf _) rfl
      (fun l params cont hl => by
        rw [hlbl] at hl
        obtain ⟨-, rfl⟩ := rlQ_inv loc ann ra al sz pref ibty pbty ubty hl
        exact rlBody_frag loc ann ra al sz pref pbty ubty)
      (fun l params cont hl => by
        rw [hlbl] at hl
        obtain ⟨-, rfl⟩ := rlQ_inv loc ann ra al sz pref ibty pbty ubty hl
        rw [rlBody_pot, show lemDefaultFuel = 999999 + 1 from rfl]
        omega)
      (rlLsT al sz)
      (rlProg loc ann ra al sz pref sbty ibty pbty ubty n)
      fmapEmpty [] σ₀ (∅ : SpikeHeapF SpikeCell) (n.toNat * regionCost al sz)
      (.save (saveParams_pure_of_vals rfl) (saveParams_depth_of_vals rfl)
        (rlBody_frag loc ann ra al sz pref pbty ubty))
      (by rw [rlProg_pot, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      hl
      (fun v _ => v = Vunit)
      (rlCost n.toNat + 1)
      (by
        intro inst
        iintro ⟨-, Hcap⟩
        isplitr [Hcap]
        · iapply rl_blockSpecsT_readout loc ann ra al sz pref ibty pbty ubty hcost rlProcSym
            (rlRS loc ann ra al sz pref ibty pbty ubty) hQ
        · iapply rl_wpt_readout loc ann ra al sz pref ibty pbty ubty hcost rlProcSym
            (rlRS loc ann ra al sz pref ibty pbty ubty) hQ sbty n hn $$ Hcap)
      aids
  exact ⟨σ', hdone⟩

/-! ### Registration and the production statement -/

/-- The shipped registration computes the loop's label map (the save is
    the registration site and the entry). -/
theorem collect_new_rl (n : Int) :
    collect_labeled_continuations_NEW
        (prodFile (rlProg loc0 empty_annotation ra al sz pref sbty ibty pbty ubty n)) =
      fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym
        (rlQ loc0 empty_annotation ra al sz pref ibty pbty ubty) fmapEmpty := rfl

theorem rl_labeledAt (sup : Nat) (n : Int) :
    LabeledAt ((initial_core_run_state sup (collect_labeled_continuations_NEW
        (prodFile (rlProg loc0 empty_annotation ra al sz pref sbty ibty pbty ubty n)))).1)
      mainSym (rlQ loc0 empty_annotation ra al sz pref ibty pbty ubty) := by
  unfold LabeledAt
  rw [show ((initial_core_run_state sup (collect_labeled_continuations_NEW
      (prodFile (rlProg loc0 empty_annotation ra al sz pref sbty ibty pbty ubty n)))).1).labeled =
    collect_labeled_continuations_NEW
      (prodFile (rlProg loc0 empty_annotation ra al sz pref sbty ibty pbty ubty n))
    from rfl]
  rw [collect_new_rl]
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

/-- N REGIONS FROM ONE BUDGET, PRODUCTION FORM: running the SHIPPED
    pipeline cold on the self-contained file is EXACTLY ONE Active
    execution delivering `Vunit` — `n` `alloc`/`free` pairs, every `alloc`
    through the PUBLIC `wpt_alloc` from the split budget, every `free`
    through the PUBLIC `wpt_free_emp` — under the budget-fits-the-cold-
    start premise `hB` (the boundary evaluation of the concrete budget,
    as fib's/the counter's `hfuel`) and the in-budget bound on the
    certified step count. Cold start, shipped registration, termination
    from the total judgment; the pipeline arrows are `wpt_driver_done_alloc`
    → `prod_run_eqJ`. -/
theorem region_loop_certified_production (sup : Nat) (hcost : 0 < regionCost al sz)
    (n : Int) (hn : 0 ≤ n)
    (hB : n.toNat * regionCost al sz ≤ headroom prodMem₀.lastAddress)
    (hfuel : 7 * n.toNat + 5 ≤ CerbFuel.driverFuel)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND
          (_root_.drive fmapEmpty false
            (prodFile (rlProg loc0 empty_annotation ra al sz pref sbty ibty pbty ubty n))
            args)
          ((initial_driver_state sup
            (prodFile (rlProg loc0 empty_annotation ra al sz pref sbty ibty pbty ubty n))
            fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = Vunit ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  have hQprod := rl_labeledAt ra al sz pref sbty ibty pbty ubty sup n
  obtain ⟨dres, dst', heq, hψ, hbl, hout, herr⟩ :=
    prod_run_eqJ sup (rlProg loc0 empty_annotation ra al sz pref sbty ibty pbty ubty n)
      hQprod (fun v _ => v = Vunit) (rlCost n.toNat + 1)
      (wpt_driver_done_alloc (GF := SpikeGF)
        (M₀ := procCtx ((initial_core_run_state sup
          (collect_labeled_continuations_NEW
            (prodFile (rlProg loc0 empty_annotation ra al sz pref sbty ibty pbty ubty n)))).1))
        rfl rfl (procCtx_labels hQprod) rfl rfl rfl rfl
        (fun l params cont hl => by
          rw [procCtx_labels hQprod] at hl
          obtain ⟨-, rfl⟩ := rlQ_inv loc0 empty_annotation ra al sz pref ibty pbty ubty hl
          exact rlBody_frag loc0 empty_annotation ra al sz pref pbty ubty)
        (fun l params cont hl => by
          rw [procCtx_labels hQprod] at hl
          obtain ⟨-, rfl⟩ := rlQ_inv loc0 empty_annotation ra al sz pref ibty pbty ubty hl
          rw [rlBody_pot, show lemDefaultFuel = 999999 + 1 from rfl]
          omega)
        (rlLsT al sz)
        (rlProg loc0 empty_annotation ra al sz pref sbty ibty pbty ubty n) fmapEmpty []
        prodMem₀ (∅ : SpikeHeapF SpikeCell) (n.toNat * regionCost al sz)
        (.save (saveParams_pure_of_vals rfl) (saveParams_depth_of_vals rfl)
          (rlBody_frag loc0 empty_annotation ra al sz pref pbty ubty))
        (by rw [rlProg_pot, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
        (prodMem₀_launchCoh _ hB)
        (fun v _ => v = Vunit)
        (rlCost n.toNat + 1)
        (by
          intro inst
          iintro ⟨-, Hcap⟩
          isplitr [Hcap]
          · iapply rl_blockSpecsT_readout loc0 empty_annotation ra al sz pref ibty pbty ubty
              hcost mainSym _ hQprod
          · iapply rl_wpt_readout loc0 empty_annotation ra al sz pref ibty pbty ubty hcost
              mainSym _ hQprod sbty n hn $$ Hcap))
      (by unfold rlCost; omega)
      fs args
  exact ⟨dres, dst', heq, hψ, hbl, hout, herr⟩

end RlExport

end CerberusHeapLang
