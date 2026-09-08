/-
CerberusHeapLang.Shipped — THE SHIPPED-CONSTANT COROLLARIES (L2, 2026-09-07;
the F2 design docs/2026-09-04_fuel-restatement-design.md §3, the landing
charter docs/2026-09-07_landing-charter.md §2 L2 (b)).

Every production export of this package is stated at a QUANTIFIED ambient
fuel `[LemFuel]` with an arithmetic side condition (`k + 2 ≤ LemFuel.fuel`,
the loop's round count plus the delivery protocol). The binary's default is
`--fuel 100000000` (cerberus-lean `Main.lean`; the ONLY numeral of the fuel
arc, [USER 2026-09-03]: every other fuel value is a quantified position, and
the no-numeral gate `scripts/fuel_numeral_check.sh` reds any numeral outside
this file's `*_shipped` theorems). The corollaries below are the statements
ABOUT THE SHIPPED BINARY: each instantiates its export at `⟨100000000⟩`
(`letI`, in the statement so the numeral is visible in the type) and
discharges the side condition by `omega` on the closed form — never by
`decide` on the numeral (the design's heartbeat hazard).

For the six parametric programs the side condition becomes a bound on the
program parameter (`n ≤ 49999997` for `2·n + 6`, …): the largest parameter the
shipped default certifies; for the recursive fib the bound is `n ≤ 33` through
the closed form `fibRounds_closed` and `fibRounds_mono` (below) — `fibRounds`
and `fibSpec` are doubly recursive and are never evaluated at the kernel.

These are corollaries, not new capability: nothing here is proved about the
engine beyond the quantified export it instantiates.
-/
import CerberusHeapLang.ProdExhibit
import CerberusHeapLang.ProdLoopExhibit
import CerberusHeapLang.RegionLoopExhibit
import CerberusHeapLang.MallocListExhibit
import CerberusHeapLang.DisposeExhibit
import CerberusHeapLang.FibRecExhibit
import CerberusHeapLang.EvenOddExhibit
import CerberusHeapLang.CorpusT1Exhibit
import CerberusHeapLang.EmittedT1Exhibit
import CerberusHeapLang.EmittedT5Exhibit
import CerberusHeapLang.EmittedT6Exhibit
import CerberusHeapLang.CorpusT4Exhibit
import CerberusHeapLang.CorpusT5Exhibit
import CerberusHeapLang.CorpusT6Exhibit

set_option autoImplicit false
namespace CerberusHeapLang

/-! ## The fib round count in closed form (for the shipped bound) -/

/-- A linear pair recursion for `fibSpec`: `fibPair n = (fibSpec n, fibSpec (n+1))`. -/
def fibPair : Nat → Int × Int
  | 0 => (0, 1)
  | n + 1 => ((fibPair n).2, (fibPair n).1 + (fibPair n).2)

theorem fibPair_spec (n : Nat) : fibPair n = (fibSpec n, fibSpec (n + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [fibPair, ih, fibSpec_add_two]

/-- `fibSpec 34 = 5702887`, computed LINEARLY through `fibPair` (kernel-checked;
    `fibSpec` itself is doubly recursive). -/
theorem fibSpec_34 : fibSpec 34 = 5702887 := by
  have h := fibPair_spec 33
  rw [show fibPair 33 = (3524578, 5702887) from by decide] at h
  exact (Prod.mk.inj h).2.symm

theorem fibRounds_33 : fibRounds 33 = 68434635 := by
  have h := fibRounds_closed 33
  rw [fibSpec_34] at h
  omega

theorem fibRounds_le_succ (n : Nat) : fibRounds n ≤ fibRounds (n + 1) := by
  cases n with
  | zero => exact Nat.le_refl _
  | succ k => rw [fibRounds_add_two]; omega

theorem fibRounds_mono {m n : Nat} (h : m ≤ n) : fibRounds m ≤ fibRounds n := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (fibRounds_le_succ _)

/-! ## Closed statements at the shipped default -/

/-- Exhibit A on the shipped pipeline at the binary's default fuel (`--fuel 100000000`). -/
theorem exhibitA_prod_shipped :
    letI : LemFuel := ⟨100000000⟩
    ∀ (sup : Nat) (fs : CerbFS.FsState) (args : List String),
          ∃ dres dst',
            CerbND.runND (drive fmapEmpty false (prodFile progAProd) args)
                  (Prod.fst (initial_driver_state sup (prodFile progAProd) fs)) =
                [(Active dres, [], dst')] ∧
              driver_result.dres_core_value dres = sevenVal ∧
                (∃ i a,
                    CellCoh fmapEmpty (driver_state.layout_state dst') i
                      { addr := a, ty := intTy, bytes := sevenBytes fmapEmpty }) ∧
                  driver_result.dres_blocked dres = false ∧
                    driver_result.dres_stdout dres = "" ∧ driver_result.dres_stderr dres = "" := by
  letI : LemFuel := ⟨100000000⟩
  intro sup fs args
  exact exhibitA_prod (by show _ ≤ 100000000; omega) sup fs args

/-- The iterative fib at the shipped default fuel: every `n ≤ 49999997` (the largest
    `n` with `2·n + 6 ≤ 100000000`); the side condition is `omega`. -/
theorem fib_certified_production_shipped :
    letI : LemFuel := ⟨100000000⟩
    ∀ (sup : Nat) (ra : core_run_annotation) (n : Int)
      (sbty ibty abty bbty : core_base_type),
      0 ≤ n →
        Int.toNat n ≤ 49999997 →
          ∀ (fs : CerbFS.FsState) (args : List String),
            ∃ dres dst',
              CerbND.runND (drive fmapEmpty false (prodFile (fibProg ra n sbty ibty abty bbty)) args)
                    (Prod.fst (initial_driver_state sup (prodFile (fibProg ra n sbty ibty abty bbty)) fs)) =
                  [(Active dres, [], dst')] ∧
                driver_result.dres_core_value dres = ivVal (fibSpec (Int.toNat n)) ∧
                  driver_result.dres_blocked dres = false ∧
                    driver_result.dres_stdout dres = "" ∧ driver_result.dres_stderr dres = "" := by
  letI : LemFuel := ⟨100000000⟩
  intro sup ra n sbty ibty abty bbty hn hn' fs args
  exact fib_certified_production sup ra n sbty ibty abty bbty hn (by show _ ≤ 100000000; omega) fs args

/-- The counter loop at the shipped default fuel: every `n ≤ 16666665` (`6·n + 8 ≤ 100000000`). -/
theorem counter_loop_certified_production_shipped :
    letI : LemFuel := ⟨100000000⟩
    ∀ (sup : Nat) (ra : core_run_annotation) (mo : memory_order)
      (bty xbty cbty sbty : core_base_type) (n : Int),
      0 ≤ n →
        Int.toNat n ≤ 16666665 →
          ∀ (fs : CerbFS.FsState) (args : List String),
            ∃ dres dst',
              CerbND.runND (drive fmapEmpty false (prodFile (counterProdProg ra mo bty xbty cbty sbty n)) args)
                    (Prod.fst (initial_driver_state sup (prodFile (counterProdProg ra mo bty xbty cbty sbty n)) fs)) =
                  [(Active dres, [], dst')] ∧
                driver_result.dres_core_value dres = Vunit ∧
                  (∃ i a bs',
                      (n = 0 ∧ bs' = intUndefBytes fmapEmpty ∨ 0 < n ∧ bs' = sevenBytes fmapEmpty) ∧
                        CellCoh fmapEmpty (driver_state.layout_state dst') i { addr := a, ty := intTy, bytes := bs' }) ∧
                    driver_result.dres_blocked dres = false ∧
                      driver_result.dres_stdout dres = "" ∧ driver_result.dres_stderr dres = "" := by
  letI : LemFuel := ⟨100000000⟩
  intro sup ra mo bty xbty cbty sbty n hn hn' fs args
  exact counter_loop_certified_production sup ra mo bty xbty cbty sbty n hn (by show _ ≤ 100000000; omega) fs args

/-- List reversal at the shipped default fuel (56 ≤ 100000000, `omega`). -/
theorem list_reverse_certified_production_shipped :
    letI : LemFuel := ⟨100000000⟩
    ∀ (sup : Nat) (ra : core_run_annotation) (mo : memory_order) (bty sbty pbty cbty bbty nbty ubty : core_base_type)
          (fs : CerbFS.FsState) (args : List String),
          ∃ dres dst',
            CerbND.runND (drive fmapEmpty false (prodFile (lrProdProg ra mo bty sbty pbty cbty bbty nbty ubty)) args)
                  (Prod.fst (initial_driver_state sup (prodFile (lrProdProg ra mo bty sbty pbty cbty bbty nbty ubty)) fs)) =
                [(Active dres, [], dst')] ∧
              (∃ i₁ i₂ Q p',
                  driver_result.dres_core_value dres = ptrVal p' ∧
                    SeedChain Q p' [(i₂, 2), (i₁, 1)] ∧ Sat fmapEmpty (driver_state.layout_state dst') Q) ∧
                driver_result.dres_blocked dres = false ∧
                  driver_result.dres_stdout dres = "" ∧ driver_result.dres_stderr dres = "" := by
  letI : LemFuel := ⟨100000000⟩
  intro sup ra mo bty sbty pbty cbty bbty nbty ubty fs args
  exact list_reverse_certified_production (by show _ ≤ 100000000; omega) sup ra mo bty sbty pbty cbty bbty nbty ubty fs args

/-- List disposal at the shipped default fuel (53 ≤ 100000000, `omega`). -/
theorem dispose_list_certified_production_shipped :
    letI : LemFuel := ⟨100000000⟩
    ∀ (sup : Nat) (ra : core_run_annotation) (mo : memory_order) (bty sbty cbty bbty nbty ubty : core_base_type)
          (fs : CerbFS.FsState) (args : List String),
          ∃ dres dst',
            CerbND.runND (drive fmapEmpty false (prodFile (dlProdProg ra mo bty sbty cbty bbty nbty ubty)) args)
                  (Prod.fst (initial_driver_state sup (prodFile (dlProdProg ra mo bty sbty cbty bbty nbty ubty)) fs)) =
                [(Active dres, [], dst')] ∧
              driver_result.dres_core_value dres = Vunit ∧
                (∃ i₁ i₂,
                    i₁ ≠ i₂ ∧
                      (List.contains (CerbMem.MemState.deadAllocations (driver_state.layout_state dst')) i₁ = true ∧
                          Std.TreeMap.get? (CerbMem.MemState.allocations (driver_state.layout_state dst')) i₁ = none) ∧
                        List.contains (CerbMem.MemState.deadAllocations (driver_state.layout_state dst')) i₂ = true ∧
                          Std.TreeMap.get? (CerbMem.MemState.allocations (driver_state.layout_state dst')) i₂ = none) ∧
                  driver_result.dres_blocked dres = false ∧
                    driver_result.dres_stdout dres = "" ∧ driver_result.dres_stderr dres = "" := by
  letI : LemFuel := ⟨100000000⟩
  intro sup ra mo bty sbty cbty bbty nbty ubty fs args
  exact dispose_list_certified_production (by show _ ≤ 100000000; omega) sup ra mo bty sbty cbty bbty nbty ubty fs args

/-- The region loop at the shipped default fuel: every `n ≤ 14285713` (`7·n + 5 ≤ 100000000`). -/
theorem region_loop_certified_production_shipped :
    letI : LemFuel := ⟨100000000⟩
    ∀ (ra : core_run_annotation) (al sz : Int) (pref : prefix0)
      (sbty ibty pbty ubty : core_base_type) (sup : Nat),
      0 < al →
        0 ≤ sz →
          0 < regionCost al sz →
            ∀ (n : Int),
              0 ≤ n →
                Int.toNat n * regionCost al sz ≤ headroom (CerbMem.MemState.lastAddress prodMem₀) →
                  Int.toNat n ≤ 14285713 →
                    ∀ (fs : CerbFS.FsState) (args : List String),
                      ∃ dres dst',
                        CerbND.runND
                              (drive fmapEmpty false
                                (prodFile (rlProg loc0 empty_annotation ra al sz pref sbty ibty pbty ubty n)) args)
                              (Prod.fst
                                (initial_driver_state sup
                                  (prodFile (rlProg loc0 empty_annotation ra al sz pref sbty ibty pbty ubty n)) fs)) =
                            [(Active dres, [], dst')] ∧
                          driver_result.dres_core_value dres = Vunit ∧
                            driver_result.dres_blocked dres = false ∧
                              driver_result.dres_stdout dres = "" ∧ driver_result.dres_stderr dres = "" := by
  letI : LemFuel := ⟨100000000⟩
  intro ra al sz pref sbty ibty pbty ubty sup halign hsize hcost n hn hB hn' fs args
  exact region_loop_certified_production ra al sz pref sbty ibty pbty ubty sup halign hsize hcost n hn hB (by show _ ≤ 100000000; omega) fs args

/-- The malloc'd list at the shipped default fuel: every `n ≤ 3999999` (`25·n + 9 ≤ 100000000`). -/
theorem malloc_list_certified_production_shipped :
    letI : LemFuel := ⟨100000000⟩
    ∀ (ra : core_run_annotation) (mo : memory_order) (al : Int) (pref : prefix0)
      (sbty ibty pbty qbty bbty nbty ubty : core_base_type),
      0 < al →
        ∀ (sup : Nat) (n : Int),
          0 ≤ n →
            Int.toNat n * (15 + max (Int.toNat al) 1) ≤ 281474976710647 →
              Int.toNat n ≤ 3999999 →
                ∀ (fs : CerbFS.FsState) (args : List String),
                  ∃ dres dst',
                    CerbND.runND
                          (drive fmapEmpty false
                            (prodFile (mlProg loc0 empty_annotation ra mo al pref sbty ibty pbty qbty bbty nbty ubty n))
                            args)
                          (Prod.fst
                            (initial_driver_state sup
                              (prodFile (mlProg loc0 empty_annotation ra mo al pref sbty ibty pbty qbty bbty nbty ubty n))
                              fs)) =
                        [(Active dres, [], dst')] ∧
                      driver_result.dres_core_value dres = Vunit ∧
                        (∃ ids,
                            List.length ids = Int.toNat n ∧
                              List.Nodup ids ∧
                                ∀ (id : Int),
                                  id ∈ ids →
                                    List.contains (CerbMem.MemState.deadAllocations (driver_state.layout_state dst')) id =
                                        true ∧
                                      Std.TreeMap.get? (CerbMem.MemState.allocations (driver_state.layout_state dst')) id =
                                        none) ∧
                          driver_result.dres_blocked dres = false ∧
                            driver_result.dres_stdout dres = "" ∧ driver_result.dres_stderr dres = "" := by
  letI : LemFuel := ⟨100000000⟩
  intro ra mo al pref sbty ibty pbty qbty bbty nbty ubty halign sup n hn hB hn' fs args
  exact malloc_list_certified_production ra mo al pref sbty ibty pbty qbty bbty nbty ubty halign sup n hn hB (by show _ ≤ 100000000; omega) fs args

/-- THE FLAGSHIP at the shipped default fuel: recursive fib for every `n ≤ 33` — the
    largest `n` whose round count fits (`fibRounds 33 + 4 = 68434639 ≤ 100000000`, while
    `fibRounds 34 + 4 = 110729575` does not); the bound comes from the closed form
    `fibRounds_closed` and the monotonicity `fibRounds_mono`, never from evaluating the
    doubly recursive `fibRounds`/`fibSpec` at the kernel. -/
theorem fib_rec_certified_production_shipped :
    letI : LemFuel := ⟨100000000⟩
    ∀ (sup : Nat) (ra : core_run_annotation) (n : Int)
      (nbty xbty ybty sbty zbty : core_base_type),
      0 ≤ n →
        Int.toNat n ≤ 33 →
          ∀ (fs : CerbFS.FsState) (args : List String),
            ∃ dres dst',
              CerbND.runND (drive fmapEmpty false (prodFileWith (frProcs ra nbty xbty ybty sbty zbty) (frMain ra n)) args)
                    (Prod.fst
                      (initial_driver_state sup (prodFileWith (frProcs ra nbty xbty ybty sbty zbty) (frMain ra n)) fs)) =
                  [(Active dres, [], dst')] ∧
                driver_result.dres_core_value dres = ivVal (fibSpec (Int.toNat n)) ∧
                  driver_result.dres_blocked dres = false ∧
                    driver_result.dres_stdout dres = "" ∧ driver_result.dres_stderr dres = "" := by
  letI : LemFuel := ⟨100000000⟩
  intro sup ra n nbty xbty ybty sbty zbty hn hn' fs args
  exact fib_rec_certified_production sup ra n nbty xbty ybty sbty zbty hn
    (by show _ ≤ 100000000; have := fibRounds_mono hn'; have := fibRounds_33; omega) fs args

/-- Mutual recursion (even/odd) at the shipped default fuel: every `n ≤ 33333331` (`3·n + 6 ≤ 100000000`). -/
theorem even_odd_certified_production_shipped :
    letI : LemFuel := ⟨100000000⟩
    ∀ (sup : Nat) (ra : core_run_annotation) (n : Int) (nbty : core_base_type)
     ,
      0 ≤ n →
        Int.toNat n ≤ 33333331 →
          ∀ (fs : CerbFS.FsState) (args : List String),
            ∃ dres dst',
              CerbND.runND (drive fmapEmpty false (prodFileWith (eoProcs ra nbty) (eoMain ra n)) args)
                    (Prod.fst (initial_driver_state sup (prodFileWith (eoProcs ra nbty) (eoMain ra n)) fs)) =
                  [(Active dres, [], dst')] ∧
                driver_result.dres_core_value dres = ivVal (1 - n % 2) ∧
                  driver_result.dres_blocked dres = false ∧
                    driver_result.dres_stdout dres = "" ∧ driver_result.dres_stderr dres = "" := by
  letI : LemFuel := ⟨100000000⟩
  intro sup ra n nbty hn hn' fs args
  exact even_odd_certified_production sup ra n nbty hn (by show _ ≤ 100000000; omega) fs args

/-- Retained t1 wrapper regression at the shipped default fuel. The advertised
    complete-file corollary is `CorpusA7.T1.certified_production_shipped`. -/
theorem t1_certified_production_shipped :
    letI : LemFuel := ⟨100000000⟩
    ∀ (sup : Nat) (fs : CerbFS.FsState) (args : List String),
          ∃ dres dst',
            CerbND.runND (drive fmapEmpty false (prodFileLib stdlibE3 [] CorpusE0.t1Main) args)
                  (Prod.fst (initial_driver_state sup (prodFileLib stdlibE3 [] CorpusE0.t1Main) fs)) =
                [(Active dres, [], dst')] ∧
              driver_result.dres_core_value dres = lint 4 ∧
                driver_result.dres_blocked dres = false ∧
                  driver_result.dres_stdout dres = "" ∧ driver_result.dres_stderr dres = "" := by
  letI : LemFuel := ⟨100000000⟩
  intro sup fs args
  exact t1_certified_production (by show _ ≤ 100000000; omega) sup fs args

/-- The complete captured t1 file at the shipped execution fuel, frontend
    supply 36 and the original comparator checks. The C/frontend connection
    remains the explicitly documented executable comparison boundary. -/
theorem CorpusA7.T1.certified_production_shipped :
    letI : LemFuel := ⟨100000000⟩
    ∀ (cmp : EmittedFile.Comparators),
      EmittedStdCore.intLibraryCheck cmp.stdlib = true →
      CorpusA7.T1.mainLookupCheck cmp.funs = true →
      CorpusA7.T1.labelUnionCheck cmp = true →
      ∀ (fs : CerbFS.FsState) (args : List String),
        ∃ (dres : driver_result) (dst' : driver_state),
          CerbND.runND (drive (CorpusA7.T1.restoredFile cmp).tagDefs false
              (CorpusA7.T1.restoredFile cmp) args)
            ((initial_driver_state CorpusA7.T1.frontendSupply
              (CorpusA7.T1.restoredFile cmp) fs).1) = [(Active dres, [], dst')] ∧
          dres.dres_core_value = lint 4 ∧ dres.dres_blocked = false ∧
          dres.dres_stdout = "" ∧ dres.dres_stderr = "" := by
  letI : LemFuel := ⟨100000000⟩
  intro cmp hstd hmain hlabels fs args
  exact CorpusA7.T1.certified_production (by show _ ≤ 100000000; omega)
    cmp hstd hmain hlabels fs args

/-- The complete captured t5 file at the shipped execution fuel, frontend
    supply 47 and the original comparator checks. The C/frontend connection
    remains the explicitly documented executable comparison boundary. -/
theorem CorpusA7.T5.certified_production_shipped :
    letI : LemFuel := ⟨100000000⟩
    ∀ (cmp : EmittedFile.Comparators),
      EmittedStdCore.intLibraryCheck cmp.stdlib = true →
      CorpusA7.T5.mainLookupCheck cmp.funs = true →
      CorpusA7.T5.labelUnionCheck cmp = true →
      ∀ (fs : CerbFS.FsState) (args : List String),
        ∃ (dres : driver_result) (dst' : driver_state),
          CerbND.runND (drive (CorpusA7.T5.restoredFile cmp).tagDefs false
              (CorpusA7.T5.restoredFile cmp) args)
            ((initial_driver_state CorpusA7.T5.frontendSupply
              (CorpusA7.T5.restoredFile cmp) fs).1) = [(Active dres, [], dst')] ∧
          dres.dres_core_value = lint 1 ∧ dres.dres_blocked = false ∧
          dres.dres_stdout = "" ∧ dres.dres_stderr = "" := by
  letI : LemFuel := ⟨100000000⟩
  intro cmp hstd hmain hlabels fs args
  exact CorpusA7.T5.certified_production (by show _ ≤ 100000000; omega)
    cmp hstd hmain hlabels fs args

/-- The complete captured t6 file at the shipped execution fuel, frontend
    supply 51 and the original comparator checks. The C/frontend connection
    remains the explicitly documented executable comparison boundary. -/
theorem CorpusA7.T6.certified_production_shipped :
    letI : LemFuel := ⟨100000000⟩
    ∀ (cmp : EmittedFile.Comparators),
      EmittedStdCore.intLibraryCheck cmp.stdlib = true →
      CorpusA7.T6.mainLookupCheck cmp.funs = true →
      CorpusA7.T6.labelUnionCheck cmp = true →
      ∀ (fs : CerbFS.FsState) (args : List String),
        ∃ (dres : driver_result) (dst' : driver_state),
          CerbND.runND (drive (CorpusA7.T6.restoredFile cmp).tagDefs false
              (CorpusA7.T6.restoredFile cmp) args)
            ((initial_driver_state CorpusA7.T6.frontendSupply
              (CorpusA7.T6.restoredFile cmp) fs).1) = [(Active dres, [], dst')] ∧
          dres.dres_core_value = lint 20 ∧ dres.dres_blocked = false ∧
          dres.dres_stdout = "" ∧ dres.dres_stderr = "" := by
  letI : LemFuel := ⟨100000000⟩
  intro cmp hstd hmain hlabels fs args
  exact CorpusA7.T6.certified_production (by show _ ≤ 100000000; omega)
    cmp hstd hmain hlabels fs args

/-- Retained t4_while wrapper regression at the shipped default fuel: `Specified(10)`. -/
theorem t4_certified_production_shipped :
    letI : LemFuel := ⟨100000000⟩
    ∀ (sup : Nat),
          600 ≤ sup →
            ∀ (fs : CerbFS.FsState) (args : List String),
              ∃ dres dst',
                CerbND.runND (drive fmapEmpty false (prodFileLib stdlibE3 [] CorpusE0.t4Main) args)
                      (Prod.fst (initial_driver_state sup (prodFileLib stdlibE3 [] CorpusE0.t4Main) fs)) =
                    [(Active dres, [], dst')] ∧
                  driver_result.dres_core_value dres = lint 10 ∧
                    driver_result.dres_blocked dres = false ∧
                      driver_result.dres_stdout dres = "" ∧ driver_result.dres_stderr dres = "" := by
  letI : LemFuel := ⟨100000000⟩
  intro sup hsup fs args
  exact t4_certified_production (by show _ ≤ 100000000; omega) sup hsup fs args

/-- Retained t5_ifelse wrapper regression; the complete-file corollary is
    `CorpusA7.T5.certified_production_shipped`. -/
theorem t5_certified_production_shipped :
    letI : LemFuel := ⟨100000000⟩
    ∀ (sup : Nat),
          600 ≤ sup →
            ∀ (fs : CerbFS.FsState) (args : List String),
              ∃ dres dst',
                CerbND.runND (drive fmapEmpty false (prodFileLib stdlibE3 [] CorpusE0.t5Main) args)
                      (Prod.fst (initial_driver_state sup (prodFileLib stdlibE3 [] CorpusE0.t5Main) fs)) =
                    [(Active dres, [], dst')] ∧
                  driver_result.dres_core_value dres = lint 1 ∧
                    driver_result.dres_blocked dres = false ∧
                      driver_result.dres_stdout dres = "" ∧ driver_result.dres_stderr dres = "" := by
  letI : LemFuel := ⟨100000000⟩
  intro sup hsup fs args
  exact t5_certified_production (by show _ ≤ 100000000; omega) sup hsup fs args

/-- Retained t6_switch wrapper regression; the complete-file corollary is
    `CorpusA7.T6.certified_production_shipped`. -/
theorem t6_certified_production_shipped :
    letI : LemFuel := ⟨100000000⟩
    ∀ (sup : Nat),
          600 ≤ sup →
            ∀ (fs : CerbFS.FsState) (args : List String),
              ∃ dres dst',
                CerbND.runND (drive fmapEmpty false (prodFileLib stdlibE3 [] CorpusE0.t6Main) args)
                      (Prod.fst (initial_driver_state sup (prodFileLib stdlibE3 [] CorpusE0.t6Main) fs)) =
                    [(Active dres, [], dst')] ∧
                  driver_result.dres_core_value dres = lint 20 ∧
                    driver_result.dres_blocked dres = false ∧
                      driver_result.dres_stdout dres = "" ∧ driver_result.dres_stderr dres = "" := by
  letI : LemFuel := ⟨100000000⟩
  intro sup hsup fs args
  exact t6_certified_production (by show _ ≤ 100000000; omega) sup hsup fs args

end CerberusHeapLang
