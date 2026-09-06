/-
CerberusHeapLang.EnvLaws — lookup-after-add for the engine's environment,
procedure and label maps.

The engine uses LemLib's Pmap representation. The symbol comparator is
proved equal to the lexicographic order on (digest, number), transported
to Pmap.CmpLaws. Comparator equality deliberately ignores descriptions;
it does not imply Lean equality of symbols.

SymMap carries the captured comparator and Pmap's binary-search ordering
invariant through Fmap.WF. Empty maps satisfy it and insertion preserves
it. The public lookup law is a single comparison; clients carry this
invariant without specifying a concrete tree shape. Binding-pattern
computations use the engine's measured traversal, with no ambient fuel.
-/
import CerberusHeapLang.Step
import LemLibPmapLaws

set_option autoImplicit false

namespace CerberusHeapLang

open Lem_Basic_classes Lem_Map

/-! ## Singleton-map facts (concrete-structure reductions — no
comparator lawfulness needed) -/

/-- Lookup in a one-entry `Fmap` built by `fmapAddBy` on empty. -/
theorem fmapLookupBy_addBy_empty {β : Type}
    (cmpL cmpL' : sym → sym → LemOrdering) (k : sym) (v : β) (l : sym) :
    fmapLookupBy cmpL' l (fmapAddBy cmpL k v fmapEmpty) =
      (if cmpL l k = .EQ then some v else none) := by
  cases hc : cmpL l k <;>
    simp [fmapAddBy, fmapEmpty, fmapLookupBy, Pmap.add, Pmap.find?, hc]

/-! ## The comparators -/

/-- The engine's LABEL-map comparator spelling (`lookupLabel`'s /
    `collect_labeled_continuations`'s). -/
def symCmpL : sym → sym → LemOrdering :=
  fun s1 s2 => Lem_Basic_classes.ordCompare s1 s2

/-- The env-update comparator (update_env's `mapKeyCompare`
    instance). -/
def symCmpK : sym → sym → LemOrdering := @mapKeyCompare sym _

/-- The engine's map insertion at the symbol comparator. -/
abbrev symAdd {β : Type} (k : sym) (v : β) (m : Fmap sym β) : Fmap sym β :=
  fmapAddBy symCmpK k v m

/-- The head-frame insertion used by `update_env_aux`. -/
abbrev envAdd (x : sym) (v : value) (m : Fmap sym value) : Fmap sym value :=
  symAdd x v m

/-- The engine's symbol comparison in Lean's `Ordering` spelling.
    This conversion is only a proof interface; maps retain `symCmpK`. -/
abbrev symOrd (x y : sym) : Ordering :=
  match symCmpK x y with
  | .LT => .lt
  | .EQ => .eq
  | .GT => .gt

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
  unfold symOrd
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

/-- The engine's symbol comparison is oriented and transitive. -/
instance : Std.TransCmp symOrd := by
  rw [symOrd_eq_compareOn]
  infer_instance

/-- Translate the established order into the Pmap law interface. -/
theorem symCmpK_laws : Pmap.CmpLaws symCmpK := by
  letI : Ord sym := ⟨symOrd⟩
  letI : Std.TransOrd sym := inferInstanceAs (Std.TransCmp symOrd)
  have hc : symCmpK = (defaultCompare : sym → sym → LemOrdering) := by
    funext x y
    change symCmpK x y = (match symOrd x y with
      | .lt => .LT | .eq => .EQ | .gt => .GT)
    unfold symOrd
    cases symCmpK x y <;> rfl
  rw [hc]
  exact Pmap.cmpLaws_of_transOrd

/-- The two comparator spellings agree on comparator equality. -/
theorem symOrd_eq_iff (x y : sym) : symOrd x y = .eq ↔ symCmpK x y = .EQ := by
  unfold symOrd
  cases symCmpK x y <;> simp

/-! ## Reachable maps and lookup after insertion -/

/-- The captured symbol comparator and the Pmap ordering invariant.
    This holds for all maps constructed by symbol insertion from empty. -/
def SymMap {β : Type} (m : Fmap sym β) : Prop := Fmap.WF symCmpK m

theorem symMap_empty {β : Type} : SymMap (fmapEmpty : Fmap sym β) :=
  Fmap.WF_empty symCmpK

theorem SymMap.add {β : Type} {m : Fmap sym β} (h : SymMap m)
    (k : sym) (v : β) : SymMap (symAdd k v m) :=
  Fmap.WF_fmapAddBy symCmpK_laws k v m h

/-- Comparator-equal keys have identical tree lookups, even when their
    Lean values differ. No tree invariant is required for this fact. -/
theorem pmap_find?_congr_key {α β : Type} {cmp : α → α → LemOrdering}
    (h : Pmap.CmpLaws cmp) {a b : α} (hab : cmp a b = .EQ) (m : Pmap α β) :
    Pmap.find? cmp a m = Pmap.find? cmp b m := by
  induction m with
  | Empty => rfl
  | Node l k v r height ihl ihr =>
    simp only [Pmap.find?, h.eq_congr a b k hab]
    cases cmp b k <;> first | assumption | rfl

/-- Lookup after insertion on any reachable map. The lookup's comparator
    argument is ignored by the engine in favor of the captured one. -/
theorem symAdd_lookup {β : Type} {m : Fmap sym β} (h : SymMap m)
    (cmp' : sym → sym → LemOrdering) (l k : sym) (v : β) :
    fmapLookupBy cmp' l (symAdd k v m) =
      (if symOrd l k = .eq then some v else fmapLookupBy cmp' l m) := by
  by_cases hc : symOrd l k = .eq
  · rw [if_pos hc]
    have heq := (symOrd_eq_iff l k).mp hc
    cases m with
    | empty =>
      change fmapLookupBy cmp' l (fmapAddBy symCmpK k v fmapEmpty) = some v
      rw [fmapLookupBy_addBy_empty, if_pos heq]
    | mk c m =>
      obtain ⟨rfl, hm⟩ := h
      change Pmap.find? symCmpK l (Pmap.add symCmpK k v m) = some v
      rw [pmap_find?_congr_key symCmpK_laws heq]
      exact Pmap.find?_add_same symCmpK_laws k v m hm
  · rw [if_neg hc]
    exact Fmap.fmapLookupBy_fmapAddBy_other symCmpK_laws cmp' l k v m h
      (fun heq => hc ((symOrd_eq_iff l k).mpr heq))

/-- Label insertion uses the same comparator as environment insertion. -/
theorem SymMap.addLabel {β : Type} {m : Fmap sym β} (h : SymMap m)
    (k : sym) (v : β) : SymMap (fmapAddBy symCmpL k v m) :=
  h.add k v

/-- Lookup after the collector's label-map insertion. -/
theorem labelAdd_lookup {β : Type} {m : Fmap sym β} (h : SymMap m)
    (cmp' : sym → sym → LemOrdering) (l k : sym) (v : β) :
    fmapLookupBy cmp' l (fmapAddBy symCmpL k v m) =
      (if symOrd l k = .eq then some v else fmapLookupBy cmp' l m) :=
  symAdd_lookup h cmp' l k v

/-- The two-entry instance (a file's `main`-plus-one procedure map, a
    two-label map): the smoke's former local `csAdd_lookup_two`, here
    once (H-2). -/
theorem symAdd_lookup_two {β : Type} (cmp' : sym → sym → LemOrdering) (k2 k1 l : sym)
    (v2 v1 : β) :
    fmapLookupBy cmp' l (symAdd k2 v2 (symAdd k1 v1 fmapEmpty)) =
      (if symOrd l k2 = .eq then some v2
       else if symOrd l k1 = .eq then some v1 else none) := by
  rw [symAdd_lookup (symMap_empty.add _ _), symAdd_lookup symMap_empty]
  rfl

/-- Frames reachable by engine `update_env` chains: empty, or a tree
    captured at the symbol comparator — `SymMap` at `value`. -/
def SymFrame (f : Fmap sym value) : Prop := SymMap f

theorem symFrame_empty : SymFrame fmapEmpty := symMap_empty

theorem SymFrame.add {f : Fmap sym value} (h : SymFrame f)
    (k : sym) (v : value) : SymFrame (envAdd k v f) := SymMap.add h k v

/-- The callee's parameter frame at ONE parameter is the one-entry head
    frame `envAdd x v ∅` (`call_proc`'s fold at one step, Core_run.lean:93;
    the comparator instances agree definitionally). Moved here from the C3
    smoke (calls arc C4). -/
theorem procEnv_single (x : sym) (bty : core_base_type) (v : value) :
    procEnv [(x, bty)] [v] = envAdd x v fmapEmpty := rfl

/-- THE LOOKUP LAW at the env frame (the `value` instance of
    `symAdd_lookup`). -/
theorem envAdd_lookup {f : Fmap sym value} (h : SymFrame f)
    (cmp' : sym → sym → LemOrdering) (l k : sym) (v : value) :
    fmapLookupBy cmp' l (envAdd k v f) =
      (if symOrd l k = .eq then some v else fmapLookupBy cmp' l f) :=
  symAdd_lookup h cmp' l k v

/-- E5 (slice 2): the symbol order is reflexive at `.eq` — for a SYMBOLIC
    symbol (the negative-action round's fresh binder), where the exhibits'
    `decide +kernel` at concrete symbols does not apply. Through
    `symOrd_eq_compareOn`: both `compare` components are reflexive. -/
theorem symOrd_self (x : sym) : symOrd x x = .eq := by
  obtain ⟨d, n, sd⟩ := x
  rw [symOrd_eq_compareOn]
  simp only [compareLex, compareOn, symKey]
  rw [string_compare_self, Nat.compare_eq_eq.mpr rfl]
  rfl

/-- E5 (slice 2): a symbol with a DIFFERENT symbol NUMBER is never `.eq`
    (`symbolEquality` demands equal digests AND equal numbers): the fresh
    binder `fresh_given_int k` at `k` above every program symbol's number
    collides with none of them, whatever the opaque `digest ()` is. -/
theorem symOrd_ne_eq_of_num_ne {d1 d2 : String} {n1 n2 : Nat} {sd1 sd2 : symbol_description}
    (h : n1 ≠ n2) : symOrd (Symbol d1 n1 sd1) (Symbol d2 n2 sd2) ≠ .eq := by
  rw [symOrd_eq_compareOn]
  simp only [compareLex, compareOn, symKey]
  intro hc
  cases hd : compare d1 d2 <;> simp only [hd, Ordering.then] at hc
  · cases hc
  · exact h (Nat.compare_eq_eq.mp hc)
  · cases hc

/-! ## The binding-pattern computations (engine `update_env_aux`
computed at the authored pattern shapes) -/

/-- `update_env_aux` at the sym-binder pattern is the head-frame
    add (Core_aux.lean:861 arm 2; the fuelled matcher needs the
    value's constructor exposed). Moved from LoopExhibit (S3). -/
theorem update_env_aux_sym (x : sym) (b : core_base_type) (v : value)
    (m : Fmap sym value) :
    update_env_aux (a := sym) (mk_sym_pat x b) v m = envAdd x v m := rfl

/-- `update_env_aux` at the SPECIFIED-binder pattern binds the
    payload OBJECT value (Core_aux.lean:861, the `CaseCtor
    Cspecified` arm followed by the sym arm — two fuel levels). -/
theorem update_env_aux_spec (pa pb : List annot) (x : sym)
    (bty : core_base_type) (ov : object_value) (m : Fmap sym value) :
    update_env_aux (a := sym) (specPat pa pb x bty)
        (Vloaded (LVspecified ov)) m = envAdd x (Vobject ov) m := rfl

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

/-- A two-leaf tuple binder with independently typed leaves. -/
theorem update_env_tuple2_mixed (x y : sym) (tx ty : core_base_type) (vx vy : value)
    (f : Fmap sym value) (rest : List (Fmap sym value)) :
    update_env (tuplePat [] [([], some x, tx), ([], some y, ty)]) (Vtuple [vx, vy]) (f :: rest) =
      envAdd x vx (envAdd y vy f) :: rest := by
  rw [update_env_cons]
  rfl

/-- E5 (slice 2): `update_env` at the negative-action rewrite's binder
    `let weak (_: unit, s: unit) = …` (`negRewrite`'s `mk_tuple_pat
    [mk_empty_pat BTy_unit, mk_sym_pat s BTy_unit]`) at the completed
    `unseq`'s tuple `(Unit, v)`: the wildcard leaf binds nothing, the symbol
    leaf binds `s ↦ v` onto the head frame (the `Ctuple` arm's `foldr` over
    the zipped leaves, Core_aux.lean:861). -/
theorem update_env_tuple_wild_sym (s : sym) (v : value) (u : value)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    update_env (tuplePat [] [([], none, BTy_unit), ([], some s, BTy_unit)]) (Vtuple [u, v])
        (ev0 :: evs) =
      envAdd s v ev0 :: evs := by
  rw [update_env_cons]
  rfl

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
