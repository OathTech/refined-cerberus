/-
CerberusHeapLang.ProdLoop — the total judgment drives THE PRODUCTION
DRIVER'S OWN per-thread loop.

`wpt_driver_aux` is the driver-level analogue of the engine simulation
`wpt_drive_aux` (TotalAdequacy.lean): strong induction on the total
judgment's budget, ONE production round (`loop_step_frag`,
DriverCollapse.lean) per budget unit, the delivery protocol prepaid by
the value clause. Where the drive simulation concludes a `driveU
.done` equation, this one concludes `DriverDoneAt`: the driver's
per-thread loop (`drive_nonmemory_steps_aux2`) from ANY driver state
holding the thread — quantified over the accumulator, the loop fuel
and the whole driver-state context, with the run-state tie `LabeledAt`
as the only run-state condition — returns the PROGRAM-DONE singleton
step map with the postcondition's value, and the final driver state is
pinned field by field. `wpt_driver_done` and `wpt_driver_done_alloc`
(the allocation-aware form, from `LaunchCoh`) are the faces ProdEntry's
`prod_run_eqJ` consumes.

No statement here mentions `initial_driver_state`: the cold start is
ProdEntry.lean's business.

Fuel: the loop budget `fl` needs `k + 2` rounds (k certified steps +
the done-recording and drain iterations), hence the production
statements' `k + 2 ≤ CerbFuel.driverFuel` (the drive cone's budget since
the cerberus-lean fuel arc; `fl` is instantiated at it by
`prod_run_eqJ`); the judgment's own `esize`/`pot`
side conditions bound get_ctx's budget exactly as in the drive
statements.
-/
import CerberusHeapLang.DriverCollapse
import CerberusHeapLang.TotalAdequacy

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Maybe Lem_List

/-! ## The driver-delivery fact (pure) -/

/-- The production driver's per-thread loop DELIVERS: from any driver
    state whose singleton thread holds `(e, ρ)` over `th₀`'s
    immutables at layout state `σ`, with empty extern and the
    run-state `labeled` tie at the current procedure, the loop
    returns the PROGRAM-DONE singleton step map for a value
    satisfying ψ with the final memory, the final driver state pinned
    (run state / trace / counter existential — the driver's own
    bookkeeping; `labeled` preservation is INSIDE the run, used per
    round, and not re-exported). -/
def DriverDoneAt (p : sym) (Q : LabelMap) (th₀ : thread_state)
    (e : CoreExpr) (ρ : EnvStack) (σ : Mem) (ψ : value → Mem → Prop)
    (k : Nat) : Prop :=
  ∀ (dst : driver_state) (acc : Fmap thread_id (List core_step2)) (fl : Nat),
    dst.core_state0.thread_states =
      [(0, (none, { th₀ with arena := e, env := ρ }))] →
    dst.layout_state = σ →
    dst.core_extern = fmapEmpty →
    LabeledAt dst.core_run_state0 p Q →
    k + 2 ≤ fl →
    ∃ (v : value) (σfin : Mem) (ρfin : EnvStack) (rs' : core_run_state)
      (tr : List trace_event) (ctr : Nat),
      ψ v σfin ∧
      runOne (drive_nonmemory_steps_aux2_lemFuel fl fmapEmpty acc [0]) dst =
        (NDactive (fmapAddBy defaultCompare 0 [Step_done2 v] acc),
         { dst with
            core_state0 := { dst.core_state0 with thread_states :=
              [(0, (none,
                { th₀ with arena := ofVal (.pure v), env := ρfin }))] },
            layout_state := σfin,
            core_run_state0 := rs', trace := tr, dr_step_counter := ctr })

/-- Value delivery, bare form: PROGRAM-DONE recorded and drained. -/
theorem driverDone_value (p : sym) (Q : LabelMap) (th₀ : thread_state)
    (hstack : th₀.stack0 = Stack_empty)
    (v : value) (ρ : EnvStack) (σ : Mem) (ψ : value → Mem → Prop)
    (hψ : ψ v σ) (k : Nat) :
    DriverDoneAt p Q th₀ (ofVal (.pure v)) ρ σ ψ k := by
  intro dst acc fl hth hσ hext hQd hfl
  subst hσ
  obtain ⟨f, rfl⟩ : ∃ f, fl = f + 2 := ⟨fl - 2, by omega⟩
  refine ⟨v, dst.layout_state, ρ, dst.core_run_state0, dst.trace,
    dst.dr_step_counter, hψ, ?_⟩
  rw [loop_step_done f fmapEmpty acc hth
    (step_ctx_done v fmapEmpty dst.layout_state dst.core_file
      dst.core_extern 0 { th₀ with arena := ofVal (.pure v), env := ρ }
      rfl hstack)]
  rw [← hth]

/-- Value delivery, annotated form: the REMOVE-ANNOT tau then
    PROGRAM-DONE (the D20 value protocol at the driver). -/
theorem driverDone_annot (p : sym) (Q : LabelMap) (th₀ : thread_state)
    (hstack : th₀.stack0 = Stack_empty)
    (ds : List dyn_annotation) (v : value) (ρ : EnvStack) (σ : Mem)
    (ψ : value → Mem → Prop) (hψ : ψ v σ) (k : Nat) (hk : 1 ≤ k) :
    DriverDoneAt p Q th₀ (ofVal (.annot ds v)) ρ σ ψ k := by
  intro dst acc fl hth hσ hext hQd hfl
  subst hσ
  obtain ⟨f, rfl⟩ : ∃ f, fl = f + 1 := ⟨fl - 1, by omega⟩
  rw [loop_step_tau f fmapEmpty acc hth
    (step_ctx_remove_annot ds v fmapEmpty dst.layout_state dst.core_file
      dst.core_extern 0 none
      { th₀ with arena := ofVal (.annot ds v), env := ρ } rfl)]
  have hth' : (update_thread_state 0
      { { th₀ with arena := ofVal (.annot ds v), env := ρ }
          with arena := ofVal (.pure v) }
      dst.core_state0).thread_states =
      [(0, (none, { th₀ with arena := ofVal (.pure v), env := ρ }))] := by
    rw [update_thread_state_single _ _ _ hth]
  obtain ⟨v', σf, ρf, rs', tr', ctr', hψ', hrun'⟩ :=
    driverDone_value p Q th₀ hstack v ρ dst.layout_state ψ hψ (k - 1)
      ({ { dst with dr_step_counter := dst.dr_step_counter + 1 }
          with core_state0 := (update_thread_state 0
            { { th₀ with arena := ofVal (.annot ds v), env := ρ }
                with arena := ofVal (.pure v) } dst.core_state0) })
      acc f hth' rfl hext hQd (by omega)
  refine ⟨v', σf, ρf, rs', tr', ctr', hψ', ?_⟩
  rw [hrun']
  rcases dst with ⟨cf, ce, cs, crs, ls, cc, fs, tr0, sa, bl, ctr0⟩
  rcases cs with ⟨ths, io⟩
  rfl

/-- The round composition: one certified mirror step in front of a
    delivering continuation — `loop_step_frag_same` (the control-preserving
    core of the live-control `loop_step_frag`; the production lane runs at
    `κ = []` and the total judgment admits no call, calls arc C2) plus the field
    transport of the final record. -/
theorem driverDone_step {M₀ : MachineCtx} {ctl : Ctl}
    (htd : M₀.tagDefs = fmapEmpty) (hex : M₀.extern = fmapEmpty)
    {Q : LabelMap} (hlb : M₀.labelsAt ctl.proc = Q)
    {p : sym} (hp : ctl.proc = some p)
    {th₀ : thread_state} (hproc : th₀.current_proc_opt = ctl.proc)
    {e e' : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    {ρ' : EnvStack} {σ σ' : Mem} {ψ : value → Mem → Prop} {k : Nat}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M₀ (e, ev0 :: evs, ctl, σ) (e', ρ', ctl, σ'))
    (hnext : DriverDoneAt p Q th₀ e' ρ' σ' ψ k) :
    DriverDoneAt p Q th₀ e (ev0 :: evs) σ ψ (k + 1) := by
  intro dst acc fl hth hσ hext hQd hfl
  subst hσ
  obtain ⟨f, rfl⟩ : ∃ f, fl = f + 1 := ⟨fl - 1, by omega⟩
  obtain ⟨rs2, tr2, ctr2, hlbl2, hrun⟩ :=
    loop_step_frag_same htd hex hlb (hproc.trans hp) f acc hth hext hQd hf hsz hs
  rw [hrun]
  have hth' : (update_thread_state 0 { th₀ with arena := e', env := ρ' }
      dst.core_state0).thread_states =
      [(0, (none, { th₀ with arena := e', env := ρ' }))] := by
    rw [update_thread_state_single _ _ _ hth]
  obtain ⟨v, σfin, ρfin, rs3, tr3, ctr3, hψ, hrun'⟩ :=
    hnext { dst with
        core_state0 := update_thread_state 0
          { th₀ with arena := e', env := ρ' } dst.core_state0,
        layout_state := σ',
        core_run_state0 := rs2, trace := tr2, dr_step_counter := ctr2 }
      acc f hth' rfl hext
      (by show LabeledAt rs2 p Q
          unfold LabeledAt
          rw [hlbl2]
          exact hQd)
      (by omega)
  refine ⟨v, σfin, ρfin, rs3, tr3, ctr3, hψ, ?_⟩
  rw [hrun']
  rcases dst with ⟨cf, ce, cs, crs, ls, cc, fs, tr0, sa, bl, ctr0⟩
  rcases cs with ⟨ths, io⟩
  rfl

/-! ## THE SIMULATION: the total judgment drives the production
driver's loop (the `wpt_drive_aux` clone at the driver level). -/

theorem wpt_driver_aux {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
    {M₀ : MachineCtx} {ctl : Ctl}
    (htd : M₀.tagDefs = fmapEmpty) (hex : M₀.extern = fmapEmpty)
    {Q : LabelMap} (hlb : M₀.labelsAt ctl.proc = Q)
    {p : sym} (hp : ctl.proc = some p) {th₀ : thread_state}
    (hstack : th₀.stack0 = ctl.toStack) (hproc : th₀.current_proc_opt = ctl.proc)
    (hκ : ctl.κ = [])
    (hQf : ∀ l params cont, lookupLabel (M₀.labelsAt ctl.proc) l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel (M₀.labelsAt ctl.proc) l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    (Ls : LabelSpecT GF) (ψ : value → Mem → Prop) :
    ∀ (k : Nat) (e : CoreExpr) (ev0 : Fmap sym value)
      (evs : List (Fmap sym value)) (σ : Mem) (ns nt : Nat),
      Frag e → pot e ≤ lemDefaultFuel →
      iprop(stateInterp (GF := GF) σ ns ([] : List Empty) nt ∗
          blockSpecsT M₀ ctl.proc Ls emptyProcSpecT (readoutPost ψ) ∗
          wpt M₀ ctl.proc Ls emptyProcSpecT k (readoutPost ψ) e (ev0 :: evs)) ⊢
        iprop(|={⊤|}=> ⌜DriverDoneAt p Q th₀ e (ev0 :: evs) σ ψ k⌝) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
  intro e ev0 evs σ ns nt hfrag hpot
  cases htv : toVal e with
  | some w =>
    have he := ofVal_of_toVal htv
    subst he
    rw [wpt_val_eq k (toVal_ofVal w)]
    iintro ⟨Hσ, -, ⟨%hc, Hpost⟩⟩
    imod Hpost with Hpost
    imod Hpost $$ %σ %ns %([] : List Empty) %nt Hσ with %hψ
    ipureintro
    cases w with
    | pure v => exact driverDone_value p Q th₀ (hstack.trans (Ctl.toStack_of_κ_nil hκ)) v (ev0 :: evs) σ ψ hψ k
    | annot ds v =>
      exact driverDone_annot p Q th₀ (hstack.trans (Ctl.toStack_of_κ_nil hκ)) ds v (ev0 :: evs) σ ψ hψ k
        (by have hc' : 2 ≤ k := by simpa [deliveryCost] using hc
            omega)
  | none =>
    cases hjr : jumpRedex? e with
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      rw [wpt_jump_eq k htv hjr]
      iintro ⟨Hσ, #HB, HJ⟩
      imod HJ with ⟨%params, %cont, %vs, %ev0', %evs', %m, %hρ, %hl, %hvs,
        %hμ, HLs⟩
      obtain ⟨rfl, rfl⟩ : ev0 = ev0' ∧ evs = evs' := by
        injection hρ with h1 h2
        exact ⟨h1, h2⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hs : Step M₀ (e, ev0 :: evs, ctl, σ)
          (cont, bindArgs params vs (ev0 :: evs), ctl, σ) :=
        Step.run_of_jumpRedex hjr hl hvs
      obtain ⟨ev0'', hbind⟩ := Step.env_cons hs
      ihave Hwpt := HB $$ %l %params %cont %vs %ev0 %evs %m %hl HLs
      ihave Hwpt' : wpt M₀ ctl.proc Ls emptyProcSpecT k' (readoutPost ψ) cont
          (bindArgs params vs (ev0 :: evs)) $$ [Hwpt]
      · iapply wpt_mono_k (show m ≤ k' by omega) cont _ $$ Hwpt
      have hf : DriverDoneAt p Q th₀ cont (bindArgs params vs (ev0 :: evs))
            σ ψ k' →
          DriverDoneAt p Q th₀ e (ev0 :: evs) σ ψ (k' + 1) :=
        fun h => driverDone_step htd hex hlb hp hproc hfrag
          (Nat.le_trans hfrag.esize_le_pot hpot) hs h
      iapply fupd_finally_mono (pure_mono hf)
      rw [hbind]
      iapply IH k' (Nat.lt_succ_self k') cont ev0'' evs σ ns nt
        (hQf l params cont hl) (hQpot l params cont hl) $$ [$Hσ $HB $Hwpt']
    | none =>
      cases hcr : callRedex? e with
      | some q =>
        iintro ⟨-, -, H⟩
        ihave H := wpt_empty_call_false htv hjr hcr $$ H
        imod H with %hf
        exact hf.elim
      | none =>
      cases k with
      | zero =>
        rw [wpt_zero_step_eq htv hjr hcr]
        iintro ⟨-, -, %hf⟩
        exact hf.elim
      | succ k' =>
        rw [wpt_step_eq k' htv hjr hcr]
        iintro ⟨Hσ, #HB, H⟩
        imod H $$ %(ctl.κ) %(ctl.execLoc) %σ %ns %([] : List Empty) %nt Hσ with ⟨%hred, Hwand⟩
        obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
        obtain ⟨hs, hM, hnil⟩ := hps
        subst hnil
        obtain ⟨re, rρ, rctl, rM⟩ := r'
        simp only at hs hM
        obtain rfl : M₀ = rM := hM.symm
        obtain rfl : ctl = rctl := (Step.ctl_eq hs hcr htv).symm
        obtain ⟨ev0', rfl⟩ := Step.env_cons hs
        imod Hwand $$ %(⟨re, ev0' :: evs, ctl, M₀⟩ : CoreRt) %σ' %([] : List CoreRt)
          %(⟨hs, rfl, rfl⟩ :
            ((⟨e, ev0 :: evs, ctl, M₀⟩ : CoreRt), σ) -<([] : List Empty)>->
              ((⟨re, ev0' :: evs, ctl, M₀⟩ : CoreRt), σ', []))
          with ⟨Hσ', Hwpt⟩
        have hfrag' : Frag re := hfrag.step hQf hs
        have hpot' : pot re ≤ lemDefaultFuel := by
          rcases Frag.pot_step_bound hfrag hs with hle |
              ⟨l0, pes0, params0, cont0, hj0, hl0, rfl⟩
          · omega
          · rw [hjr] at hj0
            cases hj0
        have hf : DriverDoneAt p Q th₀ re (ev0' :: evs) σ' ψ k' →
            DriverDoneAt p Q th₀ e (ev0 :: evs) σ ψ (k' + 1) :=
          fun h => driverDone_step htd hex hlb hp hproc hfrag
            (Nat.le_trans hfrag.esize_le_pot hpot) hs h
        iapply fupd_finally_mono (pure_mono hf)
        iapply IH k' (Nat.lt_succ_self k') re ev0' evs σ' (ns + 1) nt
          hfrag' hpot' $$ [$Hσ' $HB $Hwpt]

/-! ## The launch: the pure driver-delivery fact from a SpikeGpreS
functor list (the `wpt_engine_boundU` clone). -/

theorem wpt_driver_done {GF : BundledGFunctors} [SpikeGpreS GF]
    {M₀ : MachineCtx} {ctl : Ctl}
    (htd : M₀.tagDefs = fmapEmpty) (hex : M₀.extern = fmapEmpty)
    {Q : LabelMap} (hlb : M₀.labelsAt ctl.proc = Q)
    {p : sym} (hp : ctl.proc = some p) {th₀ : thread_state}
    (hstack : th₀.stack0 = ctl.toStack) (hproc : th₀.current_proc_opt = ctl.proc)
    (hκ : ctl.κ = [])
    (hQf : ∀ l params cont, lookupLabel (M₀.labelsAt ctl.proc) l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel (M₀.labelsAt ctl.proc) l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    (Ls : ∀ [SpikeGS .hasLC GF], LabelSpecT GF)
    (e₀ : CoreExpr) (ev00 : Fmap sym value) (evs0 : List (Fmap sym value))
    (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell)
    (hfrag : Frag e₀) (hpot : pot e₀ ≤ lemDefaultFuel) (hcoh : Coh M₀.tagDefs σ₀ m₀)
    (ψ : value → Mem → Prop) (k : Nat)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn M₀.tagDefs (hlc := .hasLC) (GF := GF) i
          (.own 1) c)) ⊢
        iprop(blockSpecsT M₀ ctl.proc Ls emptyProcSpecT (readoutPost ψ) ∗
          wpt M₀ ctl.proc Ls emptyProcSpecT k (readoutPost ψ) e₀ (ev00 :: evs0))) :
    DriverDoneAt p Q th₀ e₀ (ev00 :: evs0) σ₀ ψ k := by
  refine pure_soundness (PROP := IProp GF) ?_
  refine (fupd_finally_soundness .hasLC 0 ⊤ _ ?_)
  iintro %Hinv Hcred
  letI : InvGS_gen .hasLC GF := Hinv
  icases Hcred with -
  imod (genHeap_init (L := Int) (V := MetaCell) (H := SpikeHeapF)
    (∅ : SpikeHeapF MetaCell)) with ⟨%Gm, Hmi, -, -⟩
  imod (genHeap_init (L := Int) (V := CerbMem.AbsByte) (H := SpikeHeapF)
    (∅ : SpikeHeapF CerbMem.AbsByte)) with ⟨%Gb, Hbi, -, -⟩
  imod (genHeap_init (L := Int) (V := AllocCursor) (H := SpikeHeapF)
    (∅ : SpikeHeapF AllocCursor)) with ⟨%Gk, Hki, -, -⟩
  imod budgetInit with ⟨%Gc, HBa⟩
  letI instGS : SpikeGS .hasLC GF :=
    { byteGS := Gb, metaGS := Gm, cursorGS := Gk, budgetGS := Gc }
  ihave HB0 := budgetAuth_of_init (hlc := .hasLC) (GF := GF) $$ HBa
  imod (spikeCells_alloc M₀.tagDefs σ₀ m₀ hcoh) $$ [$Hmi $Hbi]
    with ⟨%mm, %mb, %hmbo, Hmi, Hbi, Hcells⟩
  ihave HW := hwp $$ Hcells
  icases HW with ⟨HB, Hwpt⟩
  ihave Hσ : stateInterp (GF := GF) σ₀ 0 ([] : List Empty) 0 $$ [Hmi Hbi Hki HB0]
  · rw [stateInterp_eq]
    iexists mm, mb, (∅ : SpikeHeapF AllocCursor)
    isplit
    · ipureintro
      exact hmbo.cohG hcoh
    isplitl [Hmi]
    · iexact Hmi
    isplitl [Hbi]
    · iexact Hbi
    isplitl [Hki]
    · iexact Hki
    · iapply budgetInterp_zero
      iexact HB0
  iapply wpt_driver_aux htd hex hlb hp hstack hproc hκ hQf hQpot Ls ψ k e₀
    ev00 evs0 σ₀ 0 0 hfrag hpot $$ [$Hσ $HB $Hwpt]

/-- ALLOCATION-AWARE driver delivery (alloc arc P2 — the production
    lane's missing launcher variant): as `wpt_driver_done`, but
    launched through the one shared `launchResources` helper — the
    client's total proof receives the footprint cells AND
    the budget `allocBudget B` (K2.5), so a whole program may allocate through the
    PUBLIC `wpt_create` and still conclude the driver-delivery fact
    `prod_run_eqJ` consumes. This is the arrow that replaces the
    example-specific `driverDone_step` create prefixes (charter P2:
    "no arrow may be supplied by an example-specific engine
    trace"). -/
theorem wpt_driver_done_alloc {GF : BundledGFunctors} [SpikeGpreS GF]
    {M₀ : MachineCtx} {ctl : Ctl}
    (htd : M₀.tagDefs = fmapEmpty) (hex : M₀.extern = fmapEmpty)
    {Q : LabelMap} (hlb : M₀.labelsAt ctl.proc = Q)
    {p : sym} (hp : ctl.proc = some p) {th₀ : thread_state}
    (hstack : th₀.stack0 = ctl.toStack) (hproc : th₀.current_proc_opt = ctl.proc)
    (hκ : ctl.κ = [])
    (hQf : ∀ l params cont, lookupLabel (M₀.labelsAt ctl.proc) l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel (M₀.labelsAt ctl.proc) l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    (Ls : ∀ [SpikeGS .hasLC GF], LabelSpecT GF)
    (e₀ : CoreExpr) (ev00 : Fmap sym value) (evs0 : List (Fmap sym value))
    (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell) (B : Nat)
    (hfrag : Frag e₀) (hpot : pot e₀ ≤ lemDefaultFuel)
    (hl : LaunchCoh M₀.tagDefs σ₀ m₀ B)
    (ψ : value → Mem → Prop) (k : Nat)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn M₀.tagDefs (hlc := .hasLC) (GF := GF) i
          (.own 1) c) ∗ allocBudget B) ⊢
        iprop(blockSpecsT M₀ ctl.proc Ls emptyProcSpecT (readoutPost ψ) ∗
          wpt M₀ ctl.proc Ls emptyProcSpecT k (readoutPost ψ) e₀ (ev00 :: evs0))) :
    DriverDoneAt p Q th₀ e₀ (ev00 :: evs0) σ₀ ψ k := by
  refine pure_soundness (PROP := IProp GF) ?_
  refine (fupd_finally_soundness .hasLC 0 ⊤ _ ?_)
  iintro %Hinv Hcred
  letI : InvGS_gen .hasLC GF := Hinv
  icases Hcred with -
  imod (genHeap_init (L := Int) (V := MetaCell) (H := SpikeHeapF)
    (∅ : SpikeHeapF MetaCell)) with ⟨%Gm, Hmi, -, -⟩
  imod (genHeap_init (L := Int) (V := CerbMem.AbsByte) (H := SpikeHeapF)
    (∅ : SpikeHeapF CerbMem.AbsByte)) with ⟨%Gb, Hbi, -, -⟩
  imod (genHeap_init (L := Int) (V := AllocCursor) (H := SpikeHeapF)
    (∅ : SpikeHeapF AllocCursor)) with ⟨%Gk, Hki, -, -⟩
  imod budgetInit with ⟨%Gc, HBa⟩
  letI instGS : SpikeGS .hasLC GF :=
    { byteGS := Gb, metaGS := Gm, cursorGS := Gk, budgetGS := Gc }
  ihave HB0 := budgetAuth_of_init (hlc := .hasLC) (GF := GF) $$ HBa
  imod (launchResources M₀.tagDefs σ₀ m₀ B hl) $$ [$Hmi $Hbi $Hki $HB0]
    with ⟨Hσ, Hcells, Hcap⟩
  ihave HW := hwp $$ [$Hcells $Hcap]
  icases HW with ⟨HB, Hwpt⟩
  iapply wpt_driver_aux htd hex hlb hp hstack hproc hκ hQf hQpot Ls ψ k e₀
    ev00 evs0 σ₀ 0 0 hfrag hpot $$ [$Hσ $HB $Hwpt]

/-! ## THE TOTAL DRIVER LANE THROUGH CALLS (calls arc C4)

The single-procedure lane above (`DriverDoneAt`, `wpt_driver_aux`,
`wpt_driver_done(_alloc)`) drives the loop through CONTROL-PRESERVING
rounds only (`loop_step_frag_same`) at the empty table `emptyProcSpecT`,
where the call clause is unsatisfiable (`wpt_empty_call_false`). The lane
below drives it through the PCALL and RETURN rounds too (`loop_step_frag`
at the live control) under a populated table: `wpt_driver_cps` is the
budget induction in CONTINUATION-PASSING form over the ambient control —
the driver-level twin of the collapse `wpt_sound_cps` (Wpt.lean) — and
`wpt_driver_done_procs` is its launcher. The pure delivery fact
`DriverDoneCtl` is stated at a LIVE control (a call stack, the current
procedure, the execution location) and ties the driver state to the
context by the file (`dst.core_file = M₀.file`, what `call_proc` reads)
and the whole-file registration `LabeledProcs` (every DECLARED
procedure's `labeled` fiber is the context's derived fiber — the callee's
labels come into scope purely because PCALL writes `current_proc_opt`,
Core_reduction.lean:484 col 18133). The single-procedure lane is left as
it is: its statements are the seven earlier production exports' route,
at a context profile (`procCtx`, the default file) where the file tie of
this lane is not available.

THE EXEC_LOC/CURRENT_LOC TIE (the C2 record §3(f), the C1 audit's M-1,
closed here): `ctlThread th₀ e ρ ctl` carries the control's `exec_loc`
(`ctl.execLoc`) and `th₀`'s `current_loc`; the PCALL round writes
`exec_loc := push_exec_loc psym th_st.current_loc th_st.exec_loc`
(Core_reduction.lean:484 col 18133) and the mirror `Step.call` writes
`push_exec_loc f M.currentLoc ctl.execLoc`, so the premise `hcl :
th₀.current_loc = M₀.currentLoc` is exactly what makes the driver's and
the mirror's successors agree (`loop_step_frag`'s `hel`/`hcl`, discharged
by `rfl`/`hcl` at `ctlThread`); RETURN leaves `exec_loc` untouched (col
2276), so the final thread's `exec_loc` is existential in
`DriverDoneCtl` — the pushed locations are never popped. The production
entry control is `prodCtl` (ProdEntry.lean): `⟨[], some mainSym,
ELoc_normal [(mainSym, CerbLocation.other "Driver.drive")]⟩`, the parked
thread literal of `Driver.drive` (Driver.lean:530), and `prodCtx` fixes
`currentLoc := CerbLocation.other "Driver.drive"`, the same literal. -/

/-- The driver thread at a LIVE control over the immutables of `th₀`:
    the arena, the env and the three control fields PCALL/RETURN write
    (`stack0 := ctl.toStack`, `current_proc_opt := ctl.proc`, `exec_loc
    := ctl.execLoc`); `errno` and `current_loc` are `th₀`'s.
    `loop_step_frag`'s successor record IS this shape. -/
def ctlThread (th₀ : thread_state) (e : CoreExpr) (ρ : EnvStack) (ctl : Ctl) : thread_state :=
  { th₀ with
    arena := e
    env := ρ
    stack0 := ctl.toStack
    current_proc_opt := ctl.proc
    exec_loc := ctl.execLoc }

@[simp] theorem ctlThread_current_loc (th₀ : thread_state) (e : CoreExpr) (ρ : EnvStack)
    (ctl : Ctl) : (ctlThread th₀ e ρ ctl).current_loc = th₀.current_loc := rfl

/-- THE WHOLE-FILE REGISTRATION TIE: the run state's two-level `labeled`
    map has, at every DECLARED procedure (`lookupProc`, the stdlib-first
    read `call_proc` makes), exactly the context's derived fiber
    `M₀.labelsAt (some f)`. The single-procedure lane's `LabeledAt` is
    this at one procedure. -/
def LabeledProcs (M₀ : MachineCtx) (lab : Fmap sym LabelMap) : Prop :=
  ∀ f params body, lookupProc M₀.file M₀.extern f = some (params, body) →
    fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) f lab =
      some (M₀.labelsAt (some f))

/-- The tie holds at the context's OWN run state as soon as every
    declared procedure has SOME fiber there (the registration installs
    one per `Proc` of the file): the derived fiber is that fiber. -/
theorem LabeledProcs.of_fibers {M₀ : MachineCtx} (hex : M₀.extern = fmapEmpty)
    (h : ∀ f params body, lookupProc M₀.file M₀.extern f = some (params, body) →
      ∃ Q : LabelMap, fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
        Lem_Basic_classes.ordCompare s1 s2) f M₀.runState.labeled = some Q) :
    LabeledProcs M₀ M₀.runState.labeled := by
  intro f params body hf
  obtain ⟨Q, hQ⟩ := h f params body hf
  rw [hQ, MachineCtx.labelsAt_some, MachineCtx.resolveProc_of_extern_empty hex, hQ]

/-- THE DRIVER-DELIVERY FACT AT A LIVE CONTROL: from any driver state
    whose singleton thread holds `(e, ρ)` at the control `ctl` over
    `th₀`'s immutables, at layout state `σ`, with empty extern, the
    context's file, and the whole-file registration tie, the loop with
    `k + 2` iterations available returns the PROGRAM-DONE singleton step
    map for a value satisfying `ψ` — the final thread at the EMPTY call
    stack (the last RETURN popped to it), at SOME current procedure and
    SOME execution location (RETURN never pops `exec_loc`), with SOME
    final env; run state / trace / counter existential (driver
    bookkeeping). -/
def DriverDoneCtl (M₀ : MachineCtx) (th₀ : thread_state) (e : CoreExpr) (ρ : EnvStack)
    (ctl : Ctl) (σ : Mem) (ψ : value → Mem → Prop) (k : Nat) : Prop :=
  ∀ (dst : driver_state) (acc : Fmap thread_id (List core_step2)) (fl : Nat),
    dst.core_state0.thread_states = [(0, (none, ctlThread th₀ e ρ ctl))] →
    dst.layout_state = σ →
    dst.core_extern = fmapEmpty →
    dst.core_file = M₀.file →
    LabeledProcs M₀ dst.core_run_state0.labeled →
    k + 2 ≤ fl →
    ∃ (v : value) (σfin : Mem) (ρfin : EnvStack) (pfin : Option sym) (ℓfin : exec_location)
      (rs' : core_run_state) (tr : List trace_event) (ctr : Nat),
      ψ v σfin ∧
      runOne (drive_nonmemory_steps_aux2_lemFuel fl fmapEmpty acc [0]) dst =
        (NDactive (fmapAddBy defaultCompare 0 [Step_done2 v] acc),
         { dst with
            core_state0 := { dst.core_state0 with thread_states :=
              [(0, (none, ctlThread th₀ (ofVal (.pure v)) ρfin ⟨[], pfin, ℓfin⟩))] },
            layout_state := σfin,
            core_run_state0 := rs', trace := tr, dr_step_counter := ctr })

/-- The budget is an upper bound. -/
theorem DriverDoneCtl.mono {M₀ : MachineCtx} {th₀ : thread_state} {e : CoreExpr}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {ψ : value → Mem → Prop} {k k' : Nat}
    (hk : k ≤ k') (h : DriverDoneCtl M₀ th₀ e ρ ctl σ ψ k) :
    DriverDoneCtl M₀ th₀ e ρ ctl σ ψ k' :=
  fun dst acc fl h1 h2 h3 h4 h5 hfl => h dst acc fl h1 h2 h3 h4 h5 (by omega)

/-- Value delivery at the EMPTY call stack, bare form: PROGRAM-DONE
    recorded and drained (`driverDone_value` at a live control). -/
theorem driverDoneCtl_value (M₀ : MachineCtx) (th₀ : thread_state) (v : value)
    (ρ : EnvStack) (p : Option sym) (ℓ : exec_location) (σ : Mem)
    (ψ : value → Mem → Prop) (hψ : ψ v σ) (k : Nat) :
    DriverDoneCtl M₀ th₀ (ofVal (.pure v)) ρ ⟨[], p, ℓ⟩ σ ψ k := by
  intro dst acc fl hth hσ hext hfile hlab hfl
  subst hσ
  obtain ⟨f, rfl⟩ : ∃ f, fl = f + 2 := ⟨fl - 2, by omega⟩
  refine ⟨v, dst.layout_state, ρ, p, ℓ, dst.core_run_state0, dst.trace,
    dst.dr_step_counter, hψ, ?_⟩
  rw [loop_step_done f fmapEmpty acc hth
    (step_ctx_done v fmapEmpty dst.layout_state dst.core_file
      dst.core_extern 0 (ctlThread th₀ (ofVal (.pure v)) ρ ⟨[], p, ℓ⟩) rfl rfl)]
  rw [← hth]

/-- Value delivery at the EMPTY call stack, annotated form: REMOVE-ANNOT
    then PROGRAM-DONE. -/
theorem driverDoneCtl_annot (M₀ : MachineCtx) (th₀ : thread_state)
    (ds : List dyn_annotation) (v : value) (ρ : EnvStack) (p : Option sym)
    (ℓ : exec_location) (σ : Mem) (ψ : value → Mem → Prop) (hψ : ψ v σ) (k : Nat)
    (hk : 1 ≤ k) :
    DriverDoneCtl M₀ th₀ (ofVal (.annot ds v)) ρ ⟨[], p, ℓ⟩ σ ψ k := by
  intro dst acc fl hth hσ hext hfile hlab hfl
  subst hσ
  obtain ⟨f, rfl⟩ : ∃ f, fl = f + 1 := ⟨fl - 1, by omega⟩
  rw [loop_step_tau f fmapEmpty acc hth
    (step_ctx_remove_annot ds v fmapEmpty dst.layout_state dst.core_file
      dst.core_extern 0 none (ctlThread th₀ (ofVal (.annot ds v)) ρ ⟨[], p, ℓ⟩) rfl)]
  have hth' : (update_thread_state 0
      { ctlThread th₀ (ofVal (.annot ds v)) ρ ⟨[], p, ℓ⟩ with arena := ofVal (.pure v) }
      dst.core_state0).thread_states =
      [(0, (none, ctlThread th₀ (ofVal (.pure v)) ρ ⟨[], p, ℓ⟩))] := by
    rw [update_thread_state_single _ _ _ hth]
    rfl
  obtain ⟨v', σf, ρf, pf, ℓf, rs', tr', ctr', hψ', hrun'⟩ :=
    driverDoneCtl_value M₀ th₀ v ρ p ℓ dst.layout_state ψ hψ (k - 1)
      ({ { dst with dr_step_counter := dst.dr_step_counter + 1 }
          with core_state0 := (update_thread_state 0
            { ctlThread th₀ (ofVal (.annot ds v)) ρ ⟨[], p, ℓ⟩ with arena := ofVal (.pure v) }
            dst.core_state0) })
      acc f hth' rfl hext hfile hlab (by omega)
  refine ⟨v', σf, ρf, pf, ℓf, rs', tr', ctr', hψ', ?_⟩
  rw [hrun']
  rcases dst with ⟨cf, ce, cs, crs, ls, cc, fs, tr0, sa, bl, ctr0⟩
  rcases cs with ⟨ths, io⟩
  rfl

/-- The general round composition: ONE certified mirror step — at ANY
    successor control: the control-preserving rounds, PCALL and RETURN
    (`loop_step_frag` at the live control) — in front of a delivering
    continuation. The current procedure must be DECLARED (`hq`), so the
    whole-file tie yields the round's `LabeledAt`; `hcl` is the
    `current_loc` tie PCALL's `push_exec_loc` reads. -/
theorem driverDoneCtl_step {M₀ : MachineCtx}
    (htd : M₀.tagDefs = fmapEmpty) (hex : M₀.extern = fmapEmpty)
    {ctl ctl' : Ctl} {p : sym} (hp : ctl.proc = some p)
    (hq : ∃ params body, lookupProc M₀.file M₀.extern p = some (params, body))
    {th₀ : thread_state} (hcl : th₀.current_loc = M₀.currentLoc)
    {e e' : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    {ρ' : EnvStack} {σ σ' : Mem} {ψ : value → Mem → Prop} {k : Nat}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M₀ (e, ev0 :: evs, ctl, σ) (e', ρ', ctl', σ'))
    (hnext : DriverDoneCtl M₀ th₀ e' ρ' ctl' σ' ψ k) :
    DriverDoneCtl M₀ th₀ e (ev0 :: evs) ctl σ ψ (k + 1) := by
  intro dst acc fl hth hσ hext hfile hlab hfl
  subst hσ
  obtain ⟨f, rfl⟩ : ∃ f, fl = f + 1 := ⟨fl - 1, by omega⟩
  obtain ⟨params, body, hq⟩ := hq
  have hQd : LabeledAt dst.core_run_state0 p (M₀.labelsAt (some p)) := hlab p params body hq
  obtain ⟨rs2, tr2, ctr2, hlbl2, hrun⟩ :=
    loop_step_frag (th₀ := ctlThread th₀ e (ev0 :: evs) ctl) htd hex
      (Q := M₀.labelsAt (some p)) (by rw [hp]) hp rfl rfl rfl hcl f acc hth hext hfile hQd hf hsz hs
  rw [hrun]
  have hth' : (update_thread_state 0
      { ctlThread th₀ e (ev0 :: evs) ctl with
        arena := e'
        env := ρ'
        stack0 := ctl'.toStack
        current_proc_opt := ctl'.proc
        exec_loc := ctl'.execLoc } dst.core_state0).thread_states =
      [(0, (none, ctlThread th₀ e' ρ' ctl'))] := by
    rw [update_thread_state_single _ _ _ hth]
    rfl
  obtain ⟨v, σfin, ρfin, pfin, ℓfin, rs3, tr3, ctr3, hψ, hrun'⟩ :=
    hnext { dst with
        core_state0 := update_thread_state 0
          { ctlThread th₀ e (ev0 :: evs) ctl with
            arena := e'
            env := ρ'
            stack0 := ctl'.toStack
            current_proc_opt := ctl'.proc
            exec_loc := ctl'.execLoc } dst.core_state0,
        layout_state := σ',
        core_run_state0 := rs2, trace := tr2, dr_step_counter := ctr2 }
      acc f hth' rfl hext hfile
      (by show LabeledProcs M₀ rs2.labeled
          rw [hlbl2]
          exact hlab)
      (by omega)
  refine ⟨v, σfin, ρfin, pfin, ℓfin, rs3, tr3, ctr3, hψ, ?_⟩
  rw [hrun']
  rcases dst with ⟨cf, ce, cs, crs, ls, cc, fs, tr0, sa, bl, ctr0⟩
  rcases cs with ⟨ths, io⟩
  rfl

/-- The two value shapes are small fragment terms within the fuel. -/
theorem esize_ofVal_le (w : SpikeVal) : esize (ofVal w) ≤ lemDefaultFuel := by
  refine Nat.le_trans (frag_ofVal w).esize_le_pot ?_
  cases w <;> simp only [pot_ofVal_pure, pot_ofVal_annot] <;>
    (rw [show lemDefaultFuel = 999999 + 1 from rfl]; omega)

/-! ## THE SIMULATION THROUGH CALLS: the total judgment drives the
production driver's loop at a live control, in continuation-passing form. -/

/-- THE CPS DRIVER INDUCTION (calls arc C4; the driver-level twin of
    `wpt_sound_cps`): at the current procedure `p` (declared), control
    `⟨κ, some p, ℓ⟩`, the total judgment at budget `k` under
    `procSpecsT`/`blockSpecsT`, and a CONTINUATION `K` that delivers from
    any value the statement reaches — at the same stack and procedure,
    any execution location (RETURN does not restore it), a final env with
    the frames below the head preserved (`SameTail`), a remaining budget
    covering the value's delivery cost — with the CONTINUATION BUDGET `kc`
    ADDED: the driver delivers from `e` within `k + kc`. Strong induction
    on `k`; the call case applies the IH twice: to the callee's body at
    the pushed control with continuation budget `k' + kc` (its
    continuation performs the RETURN round(s) — `Step.ret`, after
    `Step.ret_annot` — into the caller's continuation `apply_ctx ctx
    (pure v)` at the popped env, which is in the cone by the plug lemmas
    — and applies the IH to it at `k'` with `K`), and the budget split
    `1 + m + k' ≤ k` pays for the call round. Every round is
    `loop_step_frag`. -/
theorem wpt_driver_cps {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
    {M₀ : MachineCtx} (htd : M₀.tagDefs = fmapEmpty) (hex : M₀.extern = fmapEmpty)
    (hPf : M₀.FragProcs) {th₀ : thread_state} (hcl : th₀.current_loc = M₀.currentLoc)
    (Θ : ProcSpecT GF) (ψ : value → Mem → Prop) :
    ∀ (k : Nat) (p : sym) (Ls : LabelSpecT GF) (Ψ : SpikeVal → EnvStack → IProp GF)
      (κ : List (Option sym × context)) (ℓ : exec_location)
      (e : CoreExpr) (ev0 : Fmap sym value) (evs : List (Fmap sym value))
      (σ : Mem) (ns nt : Nat) (kc : Nat),
      (∃ params body, lookupProc M₀.file M₀.extern p = some (params, body)) →
      Frag e → pot e ≤ lemDefaultFuel →
      iprop(stateInterp (GF := GF) σ ns ([] : List Empty) nt ∗
          procSpecsT M₀ Θ ∗ blockSpecsT M₀ (some p) Ls Θ Ψ ∗
          wpt M₀ (some p) Ls Θ k Ψ e (ev0 :: evs)) ⊢
        iprop((∀ (w : SpikeVal) (ρ' : EnvStack) (ℓ' : exec_location) (σ' : Mem) (ns' k' : Nat),
            ⌜SameTail (ev0 :: evs) ρ'⌝ -∗ ⌜deliveryCost w ≤ k'⌝ -∗
            stateInterp σ' ns' ([] : List Empty) nt -∗ Ψ w ρ' -∗
            |={⊤|}=> ⌜DriverDoneCtl M₀ th₀ (ofVal w) ρ' ⟨κ, some p, ℓ'⟩ σ' ψ (k' + kc)⌝) -∗
          |={⊤|}=> ⌜DriverDoneCtl M₀ th₀ e (ev0 :: evs) ⟨κ, some p, ℓ⟩ σ ψ (k + kc)⌝) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
  intro p Ls Ψ κ ℓ e ev0 evs σ ns nt kc hq hfrag hpot
  obtain ⟨params₀, body₀, hq₀⟩ := hq
  have hQf : ∀ l params cont, lookupLabel (M₀.labelsAt (some p)) l = some (params, cont) →
      Frag cont := fun l params cont hl => (hPf.labels p params₀ body₀ hq₀ l params cont hl).1
  have hQpot : ∀ l params cont, lookupLabel (M₀.labelsAt (some p)) l = some (params, cont) →
      pot cont ≤ lemDefaultFuel :=
    fun l params cont hl => (hPf.labels p params₀ body₀ hq₀ l params cont hl).2
  cases htv : toVal e with
  | some w =>
    have he := ofVal_of_toVal htv
    subst he
    rw [wpt_val_eq k (toVal_ofVal w)]
    iintro ⟨Hσ, -, -, ⟨%hc, Hpost⟩⟩ HK
    imod Hpost with Hpost
    iapply HK $$ %w %(ev0 :: evs) %ℓ %σ %ns %k %(SameTail.refl _) %hc Hσ Hpost
  | none =>
    cases hjr : jumpRedex? e with
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      rw [wpt_jump_eq k htv hjr]
      iintro ⟨Hσ, #HP, #HB, HJ⟩ HK
      imod HJ with ⟨%params, %cont, %vs, %ev0', %evs', %m, %hρ, %hl, %hvs,
        %hμ, HLs⟩
      obtain ⟨rfl, rfl⟩ : ev0 = ev0' ∧ evs = evs' := by
        injection hρ with h1 h2
        exact ⟨h1, h2⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hs : Step M₀ (e, ev0 :: evs, ⟨κ, some p, ℓ⟩, σ)
          (cont, bindArgs params vs (ev0 :: evs), ⟨κ, some p, ℓ⟩, σ) :=
        Step.run_of_jumpRedex hjr hl hvs
      have hst0 : SameTail (ev0 :: evs) (bindArgs params vs (ev0 :: evs)) := hs.sameTail
      obtain ⟨ev0'', hbind⟩ := Step.env_cons hs
      ihave Hwpt := HB $$ %l %params %cont %vs %ev0 %evs %m %hl HLs
      ihave Hwpt' : wpt M₀ (some p) Ls Θ k' Ψ cont
          (bindArgs params vs (ev0 :: evs)) $$ [Hwpt]
      · iapply wpt_mono_k (show m ≤ k' by omega) cont _ $$ Hwpt
      have hf : DriverDoneCtl M₀ th₀ cont (bindArgs params vs (ev0 :: evs))
            ⟨κ, some p, ℓ⟩ σ ψ (k' + kc) →
          DriverDoneCtl M₀ th₀ e (ev0 :: evs) ⟨κ, some p, ℓ⟩ σ ψ (k' + 1 + kc) := fun h => by
        rw [show k' + 1 + kc = (k' + kc) + 1 by omega]
        exact driverDoneCtl_step htd hex rfl ⟨_, _, hq₀⟩ hcl hfrag
          (Nat.le_trans hfrag.esize_le_pot hpot) hs h
      iapply fupd_finally_mono (pure_mono hf)
      rw [hbind] at hst0 ⊢
      iapply IH k' (Nat.lt_succ_self k') p Ls Ψ κ ℓ cont ev0'' evs σ ns nt kc
        ⟨_, _, hq₀⟩ (hQf l params cont hl) (hQpot l params cont hl) $$ [$Hσ $HP $HB $Hwpt']
      iintro %w %ρ' %ℓ' %σ' %ns' %k'' %hst %hc Hσ' HΨ
      iapply HK $$ %w %ρ' %ℓ' %σ' %ns' %k'' %(hst0.trans hst) %hc Hσ' HΨ
    | none =>
      cases hcr : callRedex? e with
      | some q =>
        obtain ⟨ctx, f, pes⟩ := q
        rw [wpt_call_eq htv hjr hcr]
        iintro ⟨Hσ, #HP, #HB, H⟩ HK
        imod H with ⟨%params, %body, %vs, %m, %k', %hb, %hf, %hlen, %hvs, Hpre, Hcont⟩
        have hs : Step M₀ (e, ev0 :: evs, ⟨κ, some p, ℓ⟩, σ)
            (body, procEnv params vs :: ev0 :: evs,
             ⟨(some p, ctx) :: κ, some f, push_exec_loc f M₀.currentLoc ℓ⟩, σ) :=
          Step.call hcr hvs hf hlen
        -- the caller's continuation after the RETURN is in the cone (the plug lemmas)
        obtain ⟨ctx', r, hd, hfr⟩ := hfrag.decomp htv
        obtain ⟨rfl, ra, rfl⟩ := hd.callRedex?_inv hcr
        have hfplug : ∀ v : value, Frag (apply_ctx ctx (Expr [] (Epure (Pexpr [] () (PEval v))))) :=
          fun v => hd.frag_plug_call hfrag v
        have hpplug : ∀ v : value,
            pot (apply_ctx ctx (Expr [] (Epure (Pexpr [] () (PEval v))))) ≤ lemDefaultFuel :=
          fun v => Nat.le_trans (hd.pot_plug_call_le v) hpot
        have hfstep : DriverDoneCtl M₀ th₀ body (procEnv params vs :: ev0 :: evs)
              ⟨(some p, ctx) :: κ, some f, push_exec_loc f M₀.currentLoc ℓ⟩ σ ψ (m + (k' + kc)) →
            DriverDoneCtl M₀ th₀ e (ev0 :: evs) ⟨κ, some p, ℓ⟩ σ ψ (k + kc) := fun h =>
          (driverDoneCtl_step htd hex rfl ⟨_, _, hq₀⟩ hcl hfrag
            (Nat.le_trans hfrag.esize_le_pot hpot) hs h).mono (by omega)
        iapply fupd_finally_mono (pure_mono hfstep)
        ihave HS := HP $$ %f %params %body %m %vs %(ev0 :: evs) %hf %hlen
        icases HS with ⟨%Ls', #HB', Hbody⟩
        ihave Hbody := Hbody $$ Hpre
        iapply IH m (by omega) f Ls' (fun w _ => (Θ f m vs).2 w.val) ((some p, ctx) :: κ)
          (push_exec_loc f M₀.currentLoc ℓ) body (procEnv params vs) (ev0 :: evs) σ ns nt
          (k' + kc) ⟨_, _, hf⟩ (hPf.body f params body hf) (hPf.potBound f params body hf)
          $$ [$Hσ $HP $HB' $Hbody]
        -- K': the RETURN round(s) into the caller's continuation at budget k', then the IH
        iintro %w %ρ' %ℓ' %σ' %ns' %krem %hst %hc Hσ'
        obtain ⟨ev0', rfl⟩ := hst.cons_inv
        cases w with
        | pure v =>
          rw [show (SpikeVal.pure v).val = v from rfl]
          iintro Hpost
          ihave Hw := Hcont $$ %v Hpost
          have hret : DriverDoneCtl M₀ th₀ (apply_ctx ctx (Expr [] (Epure (Pexpr [] () (PEval v)))))
                (ev0 :: evs) ⟨κ, some p, ℓ'⟩ σ' ψ (k' + kc) →
              DriverDoneCtl M₀ th₀ (ofVal (.pure v)) (ev0' :: ev0 :: evs)
                ⟨(some p, ctx) :: κ, some f, ℓ'⟩ σ' ψ (krem + (k' + kc)) := fun h =>
            (driverDoneCtl_step htd hex (ctl := ⟨(some p, ctx) :: κ, some f, ℓ'⟩) rfl ⟨_, _, hf⟩
              hcl (.val_pure v) (esize_ofVal_le (.pure v)) Step.ret h).mono
              (by simp only [deliveryCost_pure] at hc; omega)
          iapply fupd_finally_mono (pure_mono hret)
          iapply IH k' (by omega) p Ls Ψ κ ℓ' (apply_ctx ctx (Expr [] (Epure (Pexpr [] () (PEval v)))))
            ev0 evs σ' ns' nt kc ⟨_, _, hq₀⟩ (hfplug v) (hpplug v) $$ [$Hσ' $HP $HB $Hw]
          iexact HK
        | annot ds v =>
          rw [show (SpikeVal.annot ds v).val = v from rfl]
          iintro Hpost
          ihave Hw := Hcont $$ %v Hpost
          have hret : DriverDoneCtl M₀ th₀ (apply_ctx ctx (Expr [] (Epure (Pexpr [] () (PEval v)))))
                (ev0 :: evs) ⟨κ, some p, ℓ'⟩ σ' ψ (k' + kc) →
              DriverDoneCtl M₀ th₀ (ofVal (.annot ds v)) (ev0' :: ev0 :: evs)
                ⟨(some p, ctx) :: κ, some f, ℓ'⟩ σ' ψ (krem + (k' + kc)) := fun h =>
            (driverDoneCtl_step htd hex (ctl := ⟨(some p, ctx) :: κ, some f, ℓ'⟩) rfl ⟨_, _, hf⟩
              hcl (.annot (.val_pure v)) (esize_ofVal_le (.annot ds v)) Step.ret_annot
              (driverDoneCtl_step htd hex (ctl := ⟨(some p, ctx) :: κ, some f, ℓ'⟩) rfl ⟨_, _, hf⟩
                hcl (.val_pure v) (esize_ofVal_le (.pure v)) Step.ret h)).mono
              (by simp only [deliveryCost_annot] at hc; omega)
          iapply fupd_finally_mono (pure_mono hret)
          iapply IH k' (by omega) p Ls Ψ κ ℓ' (apply_ctx ctx (Expr [] (Epure (Pexpr [] () (PEval v)))))
            ev0 evs σ' ns' nt kc ⟨_, _, hq₀⟩ (hfplug v) (hpplug v) $$ [$Hσ' $HP $HB $Hw]
          iexact HK
      | none =>
      cases k with
      | zero =>
        rw [wpt_zero_step_eq htv hjr hcr]
        iintro ⟨-, -, -, %hf⟩ -
        exact hf.elim
      | succ k' =>
        rw [wpt_step_eq k' htv hjr hcr]
        iintro ⟨Hσ, #HP, #HB, H⟩ HK
        imod H $$ %κ %ℓ %σ %ns %([] : List Empty) %nt Hσ with ⟨%hred, Hwand⟩
        obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
        obtain ⟨hs, hM, hnil⟩ := hps
        subst hnil
        obtain ⟨re, rρ, rctl, rM⟩ := r'
        simp only at hs hM
        obtain rfl : M₀ = rM := hM.symm
        obtain rfl : (⟨κ, some p, ℓ⟩ : Ctl) = rctl := (Step.ctl_eq hs hcr htv).symm
        obtain ⟨ev0', rfl⟩ := Step.env_cons hs
        imod Hwand $$ %(⟨re, ev0' :: evs, ⟨κ, some p, ℓ⟩, M₀⟩ : CoreRt) %σ' %([] : List CoreRt)
          %(⟨hs, rfl, rfl⟩ :
            ((⟨e, ev0 :: evs, ⟨κ, some p, ℓ⟩, M₀⟩ : CoreRt), σ) -<([] : List Empty)>->
              ((⟨re, ev0' :: evs, ⟨κ, some p, ℓ⟩, M₀⟩ : CoreRt), σ', []))
          with ⟨Hσ', Hwpt⟩
        have hfrag' : Frag re := hfrag.step (ctl := ⟨κ, some p, ℓ⟩) hQf hs
        have hpot' : pot re ≤ lemDefaultFuel := by
          rcases Frag.pot_step_bound hfrag hs with hle |
              ⟨l0, pes0, params0, cont0, hj0, hl0, rfl⟩
          · omega
          · rw [hjr] at hj0
            cases hj0
        have hf : DriverDoneCtl M₀ th₀ re (ev0' :: evs) ⟨κ, some p, ℓ⟩ σ' ψ (k' + kc) →
            DriverDoneCtl M₀ th₀ e (ev0 :: evs) ⟨κ, some p, ℓ⟩ σ ψ (k' + 1 + kc) := fun h => by
          rw [show k' + 1 + kc = (k' + kc) + 1 by omega]
          exact driverDoneCtl_step htd hex rfl ⟨_, _, hq₀⟩ hcl hfrag
            (Nat.le_trans hfrag.esize_le_pot hpot) hs h
        iapply fupd_finally_mono (pure_mono hf)
        iapply IH k' (Nat.lt_succ_self k') p Ls Ψ κ ℓ re ev0' evs σ' (ns + 1) nt kc
          ⟨_, _, hq₀⟩ hfrag' hpot' $$ [$Hσ' $HP $HB $Hwpt]
        iintro %w %ρ' %ℓ' %σ'' %ns' %k'' %hst %hc Hσ'' HΨ
        iapply HK $$ %w %ρ' %ℓ' %σ'' %ns' %k'' %(hs.sameTail.trans hst) %hc Hσ'' HΨ

/-! ## The launch through calls: the pure driver-delivery fact at the
production entry control from a SpikeGpreS functor list, with the
procedure specification table (the `wpt_driver_done_alloc` twin). -/

/-- ALLOCATION-AWARE driver delivery THROUGH CALLS (calls arc C4): as
    `wpt_driver_done_alloc`, at a populated table — the client's total
    proof receives the footprint cells and the budget and returns the
    procedure specifications `procSpecsT`, the entry procedure's block
    specifications and its total judgment; the conclusion is the delivery
    fact at the entry control `⟨[], some p, ℓ⟩` for the declared entry
    procedure `p`. `wpt_driver_cps` at the empty stack with the PROGRAM-DONE
    continuation (`driverDoneCtl_value`/`_annot`, budget `kc = 0`). -/
theorem wpt_driver_done_procs {GF : BundledGFunctors} [SpikeGpreS GF]
    {M₀ : MachineCtx} (htd : M₀.tagDefs = fmapEmpty) (hex : M₀.extern = fmapEmpty)
    (hPf : M₀.FragProcs) {th₀ : thread_state} (hcl : th₀.current_loc = M₀.currentLoc)
    {p : sym} {params : List (sym × core_base_type)} {body : CoreExpr}
    (hq : lookupProc M₀.file M₀.extern p = some (params, body)) (ℓ : exec_location)
    (Θ : ∀ [SpikeGS .hasLC GF], ProcSpecT GF) (Ls : ∀ [SpikeGS .hasLC GF], LabelSpecT GF)
    (e₀ : CoreExpr) (ev00 : Fmap sym value) (evs0 : List (Fmap sym value))
    (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell) (B : Nat)
    (hfrag : Frag e₀) (hpot : pot e₀ ≤ lemDefaultFuel)
    (hl : LaunchCoh M₀.tagDefs σ₀ m₀ B)
    (ψ : value → Mem → Prop) (k : Nat)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn M₀.tagDefs (hlc := .hasLC) (GF := GF) i
          (.own 1) c) ∗ allocBudget B) ⊢
        iprop(procSpecsT M₀ Θ ∗ blockSpecsT M₀ (some p) Ls Θ (readoutPost ψ) ∗
          wpt M₀ (some p) Ls Θ k (readoutPost ψ) e₀ (ev00 :: evs0))) :
    DriverDoneCtl M₀ th₀ e₀ (ev00 :: evs0) ⟨[], some p, ℓ⟩ σ₀ ψ k := by
  refine pure_soundness (PROP := IProp GF) ?_
  refine (fupd_finally_soundness .hasLC 0 ⊤ _ ?_)
  iintro %Hinv Hcred
  letI : InvGS_gen .hasLC GF := Hinv
  icases Hcred with -
  imod (genHeap_init (L := Int) (V := MetaCell) (H := SpikeHeapF)
    (∅ : SpikeHeapF MetaCell)) with ⟨%Gm, Hmi, -, -⟩
  imod (genHeap_init (L := Int) (V := CerbMem.AbsByte) (H := SpikeHeapF)
    (∅ : SpikeHeapF CerbMem.AbsByte)) with ⟨%Gb, Hbi, -, -⟩
  imod (genHeap_init (L := Int) (V := AllocCursor) (H := SpikeHeapF)
    (∅ : SpikeHeapF AllocCursor)) with ⟨%Gk, Hki, -, -⟩
  imod budgetInit with ⟨%Gc, HBa⟩
  letI instGS : SpikeGS .hasLC GF :=
    { byteGS := Gb, metaGS := Gm, cursorGS := Gk, budgetGS := Gc }
  ihave HB0 := budgetAuth_of_init (hlc := .hasLC) (GF := GF) $$ HBa
  imod (launchResources M₀.tagDefs σ₀ m₀ B hl) $$ [$Hmi $Hbi $Hki $HB0]
    with ⟨Hσ, Hcells, Hcap⟩
  ihave HW := hwp $$ [$Hcells $Hcap]
  icases HW with ⟨HP, HB, Hwpt⟩
  iapply wpt_driver_cps htd hex hPf hcl Θ ψ k p Ls (readoutPost ψ) [] ℓ e₀ ev00 evs0 σ₀ 0 0 0
    ⟨_, _, hq⟩ hfrag hpot $$ [$Hσ $HP $HB $Hwpt]
  iintro %w %ρ' %ℓ' %σ' %ns' %k' %hst %hc Hσ' HΨ
  imod HΨ $$ %σ' %ns' %([] : List Empty) %0 Hσ' with %hψ
  ipureintro
  cases w with
  | pure v => exact driverDoneCtl_value M₀ th₀ v ρ' (some p) ℓ' σ' ψ hψ (k' + 0)
  | annot ds v =>
    exact driverDoneCtl_annot M₀ th₀ ds v ρ' (some p) ℓ' σ' ψ hψ (k' + 0)
      (by simp only [deliveryCost_annot] at hc; omega)

end CerberusHeapLang
