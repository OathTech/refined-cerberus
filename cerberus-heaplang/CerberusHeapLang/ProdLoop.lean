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
statements' `k + 2 ≤ lemDefaultFuel`; the judgment's own `esize`/`pot`
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
    delivering continuation — `loop_step_frag` plus the field
    transport of the final record. -/
theorem driverDone_step {M₀ : MachineCtx}
    (htd : M₀.tagDefs = fmapEmpty) (hex : M₀.extern = fmapEmpty)
    {Q : LabelMap} (hlb : M₀.labels = Q)
    {p : sym} {th₀ : thread_state} (hproc : th₀.current_proc_opt = some p)
    {e e' : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    {ρ' : EnvStack} {σ σ' : Mem} {ψ : value → Mem → Prop} {k : Nat}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M₀ (e, ev0 :: evs, σ) (e', ρ', σ'))
    (hnext : DriverDoneAt p Q th₀ e' ρ' σ' ψ k) :
    DriverDoneAt p Q th₀ e (ev0 :: evs) σ ψ (k + 1) := by
  intro dst acc fl hth hσ hext hQd hfl
  subst hσ
  obtain ⟨f, rfl⟩ : ∃ f, fl = f + 1 := ⟨fl - 1, by omega⟩
  obtain ⟨rs2, tr2, ctr2, hlbl2, hrun⟩ :=
    loop_step_frag htd hex hlb hproc f acc hth hext hQd hf hsz hs
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
    {M₀ : MachineCtx}
    (htd : M₀.tagDefs = fmapEmpty) (hex : M₀.extern = fmapEmpty)
    {Q : LabelMap} (hlb : M₀.labels = Q)
    {p : sym} {th₀ : thread_state}
    (hproc : th₀.current_proc_opt = some p)
    (hstack : th₀.stack0 = Stack_empty)
    (hQf : ∀ l params cont, lookupLabel M₀.labels l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel M₀.labels l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    (Ls : LabelSpecT GF) (ψ : value → Mem → Prop) :
    ∀ (k : Nat) (e : CoreExpr) (ev0 : Fmap sym value)
      (evs : List (Fmap sym value)) (σ : Mem) (ns nt : Nat),
      Frag e → pot e ≤ lemDefaultFuel →
      iprop(stateInterp (GF := GF) σ ns ([] : List Empty) nt ∗
          blockSpecsT M₀ Ls (readoutPost ψ) ∗
          wpt M₀ Ls k (readoutPost ψ) e (ev0 :: evs)) ⊢
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
    | pure v => exact driverDone_value p Q th₀ hstack v (ev0 :: evs) σ ψ hψ k
    | annot ds v =>
      exact driverDone_annot p Q th₀ hstack ds v (ev0 :: evs) σ ψ hψ k
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
      have hs : Step M₀ (e, ev0 :: evs, σ)
          (cont, bindArgs params vs (ev0 :: evs), σ) :=
        Step.run_of_jumpRedex hjr hl hvs
      obtain ⟨ev0'', hbind⟩ := Step.env_cons hs
      ihave Hwpt := HB $$ %l %params %cont %vs %ev0 %evs %m %hl HLs
      ihave Hwpt' : wpt M₀ Ls k' (readoutPost ψ) cont
          (bindArgs params vs (ev0 :: evs)) $$ [Hwpt]
      · iapply wpt_mono_k (show m ≤ k' by omega) cont _ $$ Hwpt
      have hf : DriverDoneAt p Q th₀ cont (bindArgs params vs (ev0 :: evs))
            σ ψ k' →
          DriverDoneAt p Q th₀ e (ev0 :: evs) σ ψ (k' + 1) :=
        fun h => driverDone_step htd hex hlb hproc hfrag
          (Nat.le_trans hfrag.esize_le_pot hpot) hs h
      iapply fupd_finally_mono (pure_mono hf)
      rw [hbind]
      iapply IH k' (Nat.lt_succ_self k') cont ev0'' evs σ ns nt
        (hQf l params cont hl) (hQpot l params cont hl) $$ [$Hσ $HB $Hwpt']
    | none =>
      cases k with
      | zero =>
        rw [wpt_zero_step_eq htv hjr]
        iintro ⟨-, -, %hf⟩
        exact hf.elim
      | succ k' =>
        rw [wpt_step_eq k' htv hjr]
        iintro ⟨Hσ, #HB, H⟩
        imod H $$ %σ %ns %([] : List Empty) %nt Hσ with ⟨%hred, Hwand⟩
        obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
        obtain ⟨hs, hM, hnil⟩ := hps
        subst hnil
        obtain ⟨re, rρ, rM⟩ := r'
        simp only at hs hM
        obtain rfl : M₀ = rM := hM.symm
        obtain ⟨ev0', rfl⟩ := Step.env_cons hs
        imod Hwand $$ %(⟨re, ev0' :: evs, M₀⟩ : CoreRt) %σ' %([] : List CoreRt)
          %(⟨hs, rfl, rfl⟩ :
            ((⟨e, ev0 :: evs, M₀⟩ : CoreRt), σ) -<([] : List Empty)>->
              ((⟨re, ev0' :: evs, M₀⟩ : CoreRt), σ', []))
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
          fun h => driverDone_step htd hex hlb hproc hfrag
            (Nat.le_trans hfrag.esize_le_pot hpot) hs h
        iapply fupd_finally_mono (pure_mono hf)
        iapply IH k' (Nat.lt_succ_self k') re ev0' evs σ' (ns + 1) nt
          hfrag' hpot' $$ [$Hσ' $HB $Hwpt]

/-! ## The launch: the pure driver-delivery fact from a SpikeGpreS
functor list (the `wpt_engine_boundU` clone). -/

theorem wpt_driver_done {GF : BundledGFunctors} [SpikeGpreS GF]
    {M₀ : MachineCtx}
    (htd : M₀.tagDefs = fmapEmpty) (hex : M₀.extern = fmapEmpty)
    {Q : LabelMap} (hlb : M₀.labels = Q)
    {p : sym} {th₀ : thread_state}
    (hproc : th₀.current_proc_opt = some p)
    (hstack : th₀.stack0 = Stack_empty)
    (hQf : ∀ l params cont, lookupLabel M₀.labels l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel M₀.labels l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    (Ls : ∀ [SpikeGS .hasLC GF], LabelSpecT GF)
    (e₀ : CoreExpr) (ev00 : Fmap sym value) (evs0 : List (Fmap sym value))
    (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell)
    (hfrag : Frag e₀) (hpot : pot e₀ ≤ lemDefaultFuel) (hcoh : Coh M₀.tagDefs σ₀ m₀)
    (ψ : value → Mem → Prop) (k : Nat)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn M₀.tagDefs (hlc := .hasLC) (GF := GF) i
          (.own 1) c)) ⊢
        iprop(blockSpecsT M₀ Ls (readoutPost ψ) ∗
          wpt M₀ Ls k (readoutPost ψ) e₀ (ev00 :: evs0))) :
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
  letI instGS : SpikeGS .hasLC GF :=
    { byteGS := Gb, metaGS := Gm, cursorGS := Gk }
  imod (spikeCells_alloc M₀.tagDefs σ₀ m₀ hcoh) $$ [$Hmi $Hbi]
    with ⟨%mm, %mb, %hmbo, Hmi, Hbi, Hcells⟩
  ihave HW := hwp $$ Hcells
  icases HW with ⟨HB, Hwpt⟩
  ihave Hσ : stateInterp (GF := GF) σ₀ 0 ([] : List Empty) 0 $$ [Hmi Hbi Hki]
  · rw [stateInterp_eq]
    iexists mm, mb, (∅ : SpikeHeapF AllocCursor)
    isplit
    · ipureintro
      exact hmbo.cohG hcoh
    isplitl [Hmi]
    · iexact Hmi
    isplitl [Hbi]
    · iexact Hbi
    · iexact Hki
  iapply wpt_driver_aux htd hex hlb hproc hstack hQf hQpot Ls ψ k e₀
    ev00 evs0 σ₀ 0 0 hfrag hpot $$ [$Hσ $HB $Hwpt]

/-- ALLOCATION-AWARE driver delivery (alloc arc P2 — the production
    lane's missing launcher variant): as `wpt_driver_done`, but
    launched through the one shared `launchResources` helper — the
    client's total proof receives the footprint cells AND
    `allocCap reqs`, so a whole program may allocate through the
    PUBLIC `wpt_create` and still conclude the driver-delivery fact
    `prod_run_eqJ` consumes. This is the arrow that replaces the
    example-specific `driverDone_step` create prefixes (charter P2:
    "no arrow may be supplied by an example-specific engine
    trace"). -/
theorem wpt_driver_done_alloc {GF : BundledGFunctors} [SpikeGpreS GF]
    {M₀ : MachineCtx}
    (htd : M₀.tagDefs = fmapEmpty) (hex : M₀.extern = fmapEmpty)
    {Q : LabelMap} (hlb : M₀.labels = Q)
    {p : sym} {th₀ : thread_state}
    (hproc : th₀.current_proc_opt = some p)
    (hstack : th₀.stack0 = Stack_empty)
    (hQf : ∀ l params cont, lookupLabel M₀.labels l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel M₀.labels l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    (Ls : ∀ [SpikeGS .hasLC GF], LabelSpecT GF)
    (e₀ : CoreExpr) (ev00 : Fmap sym value) (evs0 : List (Fmap sym value))
    (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell) (reqs : List AllocReq)
    (hfrag : Frag e₀) (hpot : pot e₀ ≤ lemDefaultFuel)
    (hl : LaunchCoh M₀.tagDefs σ₀ m₀ reqs)
    (ψ : value → Mem → Prop) (k : Nat)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn M₀.tagDefs (hlc := .hasLC) (GF := GF) i
          (.own 1) c) ∗ allocCap M₀.tagDefs reqs) ⊢
        iprop(blockSpecsT M₀ Ls (readoutPost ψ) ∗
          wpt M₀ Ls k (readoutPost ψ) e₀ (ev00 :: evs0))) :
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
  letI instGS : SpikeGS .hasLC GF :=
    { byteGS := Gb, metaGS := Gm, cursorGS := Gk }
  imod (launchResources M₀.tagDefs σ₀ m₀ reqs hl) $$ [$Hmi $Hbi $Hki]
    with ⟨Hσ, Hcells, Hcap⟩
  ihave HW := hwp $$ [$Hcells $Hcap]
  icases HW with ⟨HB, Hwpt⟩
  iapply wpt_driver_aux htd hex hlb hproc hstack hQf hQpot Ls ψ k e₀
    ev00 evs0 σ₀ 0 0 hfrag hpot $$ [$Hσ $HB $Hwpt]

end CerberusHeapLang
