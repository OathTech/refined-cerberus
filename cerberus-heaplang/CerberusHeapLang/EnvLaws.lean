/-
CerberusHeapLang.EnvLaws — lawfulness of the engine's environment
maps: the lookup-after-add law the loop exhibits' invariants stand
on.

The gap this closes: the engine's env frames are LemLib `Fmap`s
(Std.TreeMap-backed), and lookup-after-add on an ARBITRARY frame
needs comparator lawfulness for the symbol order, which the engine
does not ship as an instance. (Without it, exhibits must pin
concrete frame SHAPES, which does not scale past one binding per
frame.) The contents:

1. `Std.TransCmp symOrd` — LAWFULNESS OF THE SYMBOL ORDER. The
   engine's env-map comparator (`mapKeyCompare` at `sym` =
   `setElemCompare` = `ordCompare` over the Symbol Eq0/Ord0
   instances, Symbol.lean:219-244) is proved EQUAL to the
   lexicographic composite of the CORE String order and the Nat
   order on the symbol's (digest, number) key — `digest_compare`
   (CerberusFresh.lean:43) is `if x < y then -1 else if x == y
   then 0 else 1` on the digest strings, and core ships
   `TransOrd String` (Init.Data.Ord.String). The instance transports
   along that equation. NOTE the order is NOT `LawfulEqCmp`:
   comparator-EQ symbols may differ in their symbol_description —
   exactly the bucket subtlety LemLib's Fmap representation records.
2. `SymFrame` — the reachable-frame predicate: empty, or built over
   the captured symbol comparator (what every engine `update_env`
   chain from an entry frame produces). Closed under `envAdd`.
3. `envAdd_lookup` — THE LAW: lookup after add on any `SymFrame` is
   a one-comparison case split (`Std.TreeMap.getElem?_insert` under
   the TransCmp instance). Frame-shape pins disappear from loop
   invariants: an invariant carries `SymFrame f` plus the lookups it
   needs.
4. The binding-pattern computations (`update_env_aux_sym`,
   `update_env_aux_spec`) and the singleton-map facts — shared by
   every exhibit.
-/
import CerberusHeapLang.Step

set_option autoImplicit false

namespace CerberusHeapLang

open Lem_Basic_classes Lem_Map

/-! ## Singleton-map facts (concrete-structure reductions — no
comparator lawfulness needed) -/

/-- `get?` after insert-into-empty, characterized for ANY key: the
    tree is one node, so lookup is a single comparison. -/
theorem treeMap_get?_insert_empty {α β : Type} (cmp : α → α → Ordering)
    (k : α) (v : β) (l : α) :
    (((Std.TreeMap.empty (cmp := cmp)).insert k v).get? l) =
      (if cmp l k = .eq then some v else none) := by
  cases hc : cmp l k <;>
    simp [Std.TreeMap.get?, Std.TreeMap.insert, Std.TreeMap.empty,
      Std.DTreeMap.Internal.Impl.insert,
      Std.DTreeMap.Const.get?, Std.DTreeMap.insert, Std.DTreeMap.empty,
      Std.DTreeMap.Internal.Impl.Const.get?,
      Std.DTreeMap.Internal.Impl.empty,
      EmptyCollection.emptyCollection, Std.TreeMap.instEmptyCollection,
      Std.DTreeMap.instEmptyCollection, hc]

/-- Lookup in a one-entry `Fmap` built by `fmapAddBy` on empty. -/
theorem fmapLookupBy_addBy_empty {β : Type}
    (cmpL cmpL' : sym → sym → LemOrdering) (k : sym) (v : β) (l : sym) :
    fmapLookupBy cmpL' l (fmapAddBy cmpL k v fmapEmpty) =
      (if lemCmpToOrd cmpL l k = .eq then some v else none) := by
  unfold fmapAddBy fmapEmpty fmapLookupBy
  dsimp only
  rw [treeMap_get?_insert_empty]
  by_cases hc : lemCmpToOrd cmpL l k = .eq
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc]

/-! ## The comparators -/

/-- The engine's LABEL-map comparator spelling (`lookupLabel`'s /
    `collect_labeled_continuations`'s). -/
def symCmpL : sym → sym → LemOrdering :=
  fun s1 s2 => Lem_Basic_classes.ordCompare s1 s2

/-- The env-update comparator (update_env's `mapKeyCompare`
    instance). -/
def symCmpK : sym → sym → LemOrdering := @mapKeyCompare sym _

/-- The head-frame add in the ENGINE's exact elaboration
    (update_env_aux's comparator AND its MapKeyType-derived BEq —
    the derived structural `BEq sym` is a DIFFERENT instance and
    must not leak in). -/
abbrev envAdd (x : sym) (v : value) (m : Fmap sym value) : Fmap sym value :=
  @fmapAddBy sym value instBEqOfMapKeyType symCmpK x v m

/-- The symbol order in `Ordering` form — the comparator every env
    frame's tree is captured at. -/
abbrev symOrd : sym → sym → Ordering := lemCmpToOrd symCmpK

/-! ## Lawfulness of the symbol order -/

/-- The symbol's comparison key. -/
def symKey : sym → String × Nat
  | Symbol d n _ => (d, n)

/-- The comparator at the constructor, in its own instances'
    spelling (the `mapKeyCompare` → `setElemCompare` → `ordCompare`
    instance chain reduces definitionally). -/
theorem symCmpK_eq (d1 : String) (n1 : Nat) (sd1 : symbol_description)
    (d2 : String) (n2 : Nat) (sd2 : symbol_description) :
    symCmpK (Symbol d1 n1 sd1) (Symbol d2 n2 sd2) =
      (if (intLtb (CerberusFresh.digest_compare d1 d2) 0 ||
          (CerberusFresh.digest_compare d1 d2 == 0 && natLtb n1 n2)) then
        LemOrdering.LT
       else if symbolEquality (Symbol d1 n1 sd1) (Symbol d2 n2 sd2) then
        LemOrdering.EQ
       else LemOrdering.GT) := rfl

theorem symbolEquality_eq (d1 : String) (n1 : Nat) (sd1 : symbol_description)
    (d2 : String) (n2 : Nat) (sd2 : symbol_description) :
    symbolEquality (Symbol d1 n1 sd1) (Symbol d2 n2 sd2) =
      ((CerberusFresh.digest_compare d1 d2 == 0) && (n1 == n2)) := by
  cases hc : ((CerberusFresh.digest_compare d1 d2 == 0) && (n1 == n2)) <;>
    (unfold symbolEquality; dsimp only; rw [hc]; rfl)

/-- `digest_compare` against the CORE String comparison: the three
    Int answers line up with the three `Ordering` answers
    (CerberusFresh.lean:43 is `if x < y then -1 else if x == y then
    0 else 1`; `String.compare` is `compareOfLessAndEq`). -/
theorem digest_compare_lt {d1 d2 : String} (h : d1 < d2) :
    CerberusFresh.digest_compare d1 d2 = -1 := by
  unfold CerberusFresh.digest_compare
  rw [if_pos h]

theorem digest_compare_self (d : String) :
    CerberusFresh.digest_compare d d = 0 := by
  unfold CerberusFresh.digest_compare
  rw [if_neg (String.lt_irrefl d)]
  split
  · rfl
  · rename_i hb
    exfalso
    apply hb
    exact decide_eq_true rfl

theorem digest_compare_gt {d1 d2 : String} (hnlt : ¬ d1 < d2)
    (hne : d1 ≠ d2) :
    CerberusFresh.digest_compare d1 d2 = 1 := by
  unfold CerberusFresh.digest_compare
  rw [if_neg hnlt]
  split
  · rename_i hb
    exact absurd (eq_of_beq hb) hne
  · rfl

theorem string_compare_lt {d1 d2 : String} (h : d1 < d2) :
    compare d1 d2 = .lt := by
  show compareOfLessAndEq d1 d2 = .lt
  unfold compareOfLessAndEq
  rw [if_pos h]

theorem string_compare_self (d : String) : compare d d = .eq := by
  show compareOfLessAndEq d d = .eq
  unfold compareOfLessAndEq
  rw [if_neg (String.lt_irrefl d), if_pos rfl]

theorem string_compare_gt {d1 d2 : String} (hnlt : ¬ d1 < d2)
    (hne : d1 ≠ d2) : compare d1 d2 = .gt := by
  show compareOfLessAndEq d1 d2 = .gt
  unfold compareOfLessAndEq
  rw [if_neg hnlt, if_neg hne]

/-- The Nat equality test the Symbol instances bottom out in (the
    `instBEqOfEq0 → Eq0 → SetType-of-Ord → defaultCompare` chain),
    characterized. -/
theorem lemNatBeq_iff (n1 n2 : Nat) :
    ((@BEq.beq Nat (@instBEqOfEq0 Nat Lem_Num.instEq0Nat_1) n1 n2) = true) ↔
      n1 = n2 := by
  show ((match defaultCompare n1 n2 with
    | LemOrdering.EQ => true
    | _ => false) = true) ↔ _
  unfold defaultCompare
  cases hcmp : compare n1 n2 with
  | lt =>
    have := Nat.compare_eq_lt.mp hcmp
    simp
    omega
  | eq =>
    have := Nat.compare_eq_eq.mp hcmp
    simp [this]
  | gt =>
    have := Nat.compare_eq_gt.mp hcmp
    simp
    omega

/-- THE CHARACTERIZATION: the engine's symbol order is the
    lexicographic composite of the core String order on digests and
    the Nat order on symbol numbers (`digest_compare`'s real
    definition, CerberusFresh.lean:43 — NOT extern-opaque). -/
theorem symOrd_eq_compareOn :
    symOrd = compareLex (compareOn (fun s => (symKey s).1))
      (compareOn (fun s => (symKey s).2)) := by
  funext s1 s2
  obtain ⟨d1, n1, sd1⟩ := s1
  obtain ⟨d2, n2, sd2⟩ := s2
  show lemCmpToOrd symCmpK _ _ = _
  unfold lemCmpToOrd
  rw [symCmpK_eq, symbolEquality_eq]
  simp only [compareLex, compareOn, symKey]
  by_cases hlt : d1 < d2
  · rw [digest_compare_lt hlt, string_compare_lt hlt]
    rfl
  · by_cases heq : d1 = d2
    · subst heq
      rw [digest_compare_self, string_compare_self]
      split
      · rename_i hcond
        split at hcond
        · rename_i hc1
          have hn : n1 < n2 := of_decide_eq_true (by exact hc1)
          rw [show compare n1 n2 = .lt from Nat.compare_eq_lt.mpr hn]
          rfl
        · split at hcond <;> cases hcond
      · rename_i hcond
        split at hcond
        · cases hcond
        · split at hcond
          · rename_i hc1 hc2
            obtain rfl : n1 = n2 :=
              (lemNatBeq_iff n1 n2).mp (Bool.and_eq_true_iff.mp hc2).2
            rw [show compare n1 n1 = .eq from Nat.compare_eq_eq.mpr rfl]
            rfl
          · cases hcond
      · rename_i hcond
        split at hcond
        · cases hcond
        · split at hcond
          · cases hcond
          · rename_i hc1 hc2
            have hnlt : ¬ n1 < n2 :=
              fun h => hc1 (by exact decide_eq_true h)
            have hne : n1 ≠ n2 := by
              intro h
              subst h
              exact hc2 (Bool.and_eq_true_iff.mpr
                ⟨rfl, (lemNatBeq_iff n1 n1).mpr rfl⟩)
            rw [show compare n1 n2 = .gt from
              Nat.compare_eq_gt.mpr (by omega)]
            rfl
    · rw [digest_compare_gt hlt heq, string_compare_gt hlt heq]
      rfl

/-- THE SEAM, CLOSED: the symbol order is a lawful (oriented,
    transitive) comparison — Std's map laws apply to the env
    frames. -/
instance : Std.TransCmp symOrd := by
  rw [symOrd_eq_compareOn]
  infer_instance

/-! ## The reachable-frame predicate and THE LOOKUP LAW -/

/-- Frames reachable by engine `update_env` chains: empty, or a tree
    captured at the symbol comparator. -/
def SymFrame (f : Fmap sym value) : Prop :=
  f = Fmap.empty ∨
  ∃ (bk : Std.TreeMap sym (List (Nat × sym × value)) symOrd)
    (bs : Std.TreeMap Nat (sym × value)) (n : Nat),
    f = Fmap.mk symOrd bk bs n

theorem symFrame_empty : SymFrame fmapEmpty := .inl rfl

theorem SymFrame.add {f : Fmap sym value} (h : SymFrame f)
    (k : sym) (v : value) : SymFrame (envAdd k v f) := by
  rcases h with rfl | ⟨bk, bs, n, rfl⟩
  · exact .inr ⟨_, _, _, rfl⟩
  · exact .inr ⟨_, _, _, rfl⟩

/-- THE LOOKUP LAW: lookup after add on any reachable frame is a
    single comparator case split (the Std.TreeMap insert law under
    `Std.TransCmp symOrd`). The lookup's own comparator argument is
    irrelevant (the representation searches with the CAPTURED
    comparator). -/
theorem envAdd_lookup {f : Fmap sym value} (h : SymFrame f)
    (cmp' : sym → sym → LemOrdering) (l k : sym) (v : value) :
    fmapLookupBy cmp' l (envAdd k v f) =
      (if symOrd l k = .eq then some v else fmapLookupBy cmp' l f) := by
  rcases h with rfl | ⟨bk, bs, n, rfl⟩
  · rw [show fmapLookupBy cmp' l (Fmap.empty : Fmap sym value) = none from rfl]
    exact fmapLookupBy_addBy_empty symCmpK cmp' k v l
  · dsimp only [envAdd]
    unfold fmapAddBy fmapLookupBy
    dsimp only
    rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.get?_eq_getElem?,
      Std.TreeMap.getElem?_insert]
    have hswap : (symOrd k l = .eq) ↔ (symOrd l k = .eq) := by
      rw [Std.OrientedCmp.eq_swap (cmp := symOrd) (a := k) (b := l)]
      cases symOrd l k <;> simp [Ordering.swap]
    by_cases hc : symOrd l k = .eq
    · rw [if_pos (hswap.mpr hc), if_pos hc]
    · rw [if_neg (fun h => hc (hswap.mp h)), if_neg hc]
      rfl

/-! ## The binding-pattern computations (engine `update_env_aux`
computed at the authored pattern shapes) -/

/-- `update_env_aux` at the sym-binder pattern is the head-frame
    add (Core_aux.lean:861 arm 2; the fuelled matcher needs the
    value's constructor exposed). Moved from LoopExhibit (S3). -/
theorem update_env_aux_sym (x : sym) (b : core_base_type) (v : value)
    (m : Fmap sym value) :
    update_env_aux (a := sym) (mk_sym_pat x b) v m = envAdd x v m := by
  show update_env_aux_lemFuel lemDefaultFuel _ _ _ = _
  rw [show lemDefaultFuel = 999999 + 1 from rfl]
  unfold update_env_aux_lemFuel
  dsimp only [mk_sym_pat, mk_sym_pat_]
  rfl

/-- `update_env_aux` at the SPECIFIED-binder pattern binds the
    payload OBJECT value (Core_aux.lean:861, the `CaseCtor
    Cspecified` arm followed by the sym arm — two fuel levels). -/
theorem update_env_aux_spec (pa pb : List annot) (x : sym)
    (bty : core_base_type) (ov : object_value) (m : Fmap sym value) :
    update_env_aux (a := sym) (specPat pa pb x bty)
        (Vloaded (LVspecified ov)) m = envAdd x (Vobject ov) m := by
  show update_env_aux_lemFuel lemDefaultFuel _ _ _ = _
  rw [show lemDefaultFuel = 999998 + 1 + 1 from rfl]
  unfold update_env_aux_lemFuel
  dsimp only [specPat]
  unfold update_env_aux_lemFuel
  rfl

/-- The whole-stack form at the Specified pattern. -/
theorem update_env_spec (pa pb : List annot) (x : sym)
    (bty : core_base_type) (ov : object_value) (ev0 : Fmap sym value)
    (evs : List (Fmap sym value)) :
    update_env (specPat pa pb x bty) (Vloaded (LVspecified ov)) (ev0 :: evs) =
      envAdd x (Vobject ov) ev0 :: evs := by
  rw [update_env_cons, update_env_aux_spec]

/-- The whole-stack form at the plain sym-binder pattern (alloc arc
    P2 — the binding step of `lets x = create(...) in ...`). -/
theorem update_env_sym (x : sym) (bty : core_base_type) (v : value)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    update_env (symPat [] x bty) v (ev0 :: evs) =
      envAdd x v ev0 :: evs := by
  rw [update_env_cons]
  show update_env_aux (mk_sym_pat x bty) v ev0 :: evs = _
  rw [update_env_aux_sym]

/-! ## Head-frame lookups through `lookup_env` -/

/-- A hit in the head frame decides the stack lookup. -/
theorem lookup_env_head {x : sym} {f : Fmap sym value} {v : value}
    (h : fmapLookupBy symCmpK x f = some v)
    (rest : List (Fmap sym value)) :
    lookup_env (a := value) x (f :: rest) = some v := by
  unfold lookup_env
  rw [show (fmapLookupBy (@mapKeyCompare sym _) x f) =
    fmapLookupBy symCmpK x f from rfl, h]

end CerberusHeapLang
