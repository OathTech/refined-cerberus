/-
Finite comparator checks for the actual map operations used by emitted-file
label collection. Checks follow reference operations, including their
intermediate trees; their correctness theorems equate the shipped operations.
No comparator function equality, tree validity or fuel-limit change is needed.
These are equality results, not success or well-formedness results: identical
opaque exhaustion terms remain identical, without being equated to a fallback.
-/
import CerberusHeapLang.EmittedFile

set_option autoImplicit false

namespace CerberusHeapLang.EmittedMapChecks

variable {α β : Type}

theorem add_eq_of_check (cmp reference : α → α → LemOrdering)
    (key : α) (value : β) (tree : Pmap α β)
    (h : EmittedFile.lookupPathAgrees cmp reference key tree = true) :
    Pmap.add cmp key value tree = Pmap.add reference key value tree := by
  induction tree with
  | Empty => rfl
  | Node left node datum right height ihl ihr =>
    cases hc : cmp key node <;> cases hr : reference key node <;>
      simp_all [EmittedFile.lookupPathAgrees, Pmap.add]

/-- Only insertion inspects the comparator in a join. Recursive joins
otherwise branch on the actual tree constructors and stored heights. -/
def joinGoCheck (cmp reference : α → α → LemOrdering) :
    Nat → Pmap α β → α → β → Pmap α β → Bool
  | 0, _, _, _, _ => true
  | n + 1, left, key, value, right =>
    match left, right with
    | .Empty, _ => EmittedFile.lookupPathAgrees cmp reference key right
    | _, .Empty => EmittedFile.lookupPathAgrees cmp reference key left
    | .Node ll lk lv lr lh, .Node rl rk rv rr rh =>
      if lh > rh + 2 then joinGoCheck cmp reference n lr key value (.Node rl rk rv rr rh)
      else if rh > lh + 2 then joinGoCheck cmp reference n (.Node ll lk lv lr lh) key value rl
      else true

theorem joinGo_eq_of_check (cmp reference : α → α → LemOrdering)
    (n : Nat) (left : Pmap α β) (key : α) (value : β) (right : Pmap α β)
    (h : joinGoCheck cmp reference n left key value right = true) :
    Pmap.joinGo cmp n left key value right = Pmap.joinGo reference n left key value right := by
  induction n generalizing left right with
  | zero => rfl
  | succ n ih =>
    cases left with
    | Empty => exact add_eq_of_check cmp reference key value right h
    | Node ll lk lv lr lh =>
      cases right with
      | Empty => exact add_eq_of_check cmp reference key value (.Node ll lk lv lr lh) h
      | Node rl rk rv rr rh =>
        simp only [joinGoCheck, Pmap.joinGo] at h ⊢
        split at h
        · rename_i hh
          simp only [if_pos hh]
          rw [ih _ _ h]
        · rename_i hh
          simp only [if_neg hh]
          split at h
          · rename_i hh'
            simp only [if_pos hh']
            rw [ih _ _ h]
          · rename_i hh'
            simp only [if_neg hh']

def joinCheck (cmp reference : α → α → LemOrdering)
    (left : Pmap α β) (key : α) (value : β) (right : Pmap α β) : Bool :=
  joinGoCheck cmp reference (Pmap.height left + Pmap.height right + 1) left key value right

theorem join_eq_of_check (cmp reference : α → α → LemOrdering)
    (left : Pmap α β) (key : α) (value : β) (right : Pmap α β)
    (h : joinCheck cmp reference left key value right = true) :
    Pmap.join cmp left key value right = Pmap.join reference left key value right :=
  joinGo_eq_of_check cmp reference _ left key value right h

/-- Split's rebuilding joins inspect reference intermediate trees. -/
def splitCheck (cmp reference : α → α → LemOrdering) (key : α) : Pmap α β → Bool
  | .Empty => true
  | .Node left node value right _ =>
    decide (cmp key node = reference key node) &&
      match reference key node with
      | .EQ => true
      | .LT => splitCheck cmp reference key left &&
          joinCheck cmp reference (Pmap.split reference key left).2.2 node value right
      | .GT => splitCheck cmp reference key right &&
          joinCheck cmp reference left node value (Pmap.split reference key right).1

theorem split_eq_of_check (cmp reference : α → α → LemOrdering)
    (key : α) (tree : Pmap α β) (h : splitCheck cmp reference key tree = true) :
    Pmap.split cmp key tree = Pmap.split reference key tree := by
  induction tree with
  | Empty => rfl
  | Node left node value right height ihl ihr =>
    simp only [splitCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hc, h⟩ := h
    rw [Pmap.split, Pmap.split, hc]
    cases hr : reference key node with
    | EQ => rfl
    | LT =>
      simp only [hr, Bool.and_eq_true] at h
      obtain ⟨hs, hj⟩ := h
      rw [ihl hs]
      rcases he : Pmap.split reference key left with ⟨ll, present, rl⟩
      simp only [he] at hj ⊢
      rw [join_eq_of_check cmp reference rl node value right hj]
    | GT =>
      simp only [hr, Bool.and_eq_true] at h
      obtain ⟨hs, hj⟩ := h
      rw [ihr hs]
      rcases he : Pmap.split reference key right with ⟨lr, present, rr⟩
      simp only [he] at hj ⊢
      rw [join_eq_of_check cmp reference left node value lr hj]

/-- Concatenation finds and removes a minimum without a comparator;
only its subsequent join requires comparison agreement. -/
def concatCheck (cmp reference : α → α → LemOrdering) (left right : Pmap α β) : Bool :=
  match left, right with
  | .Empty, _ => true
  | _, .Empty => true
  | _, _ => match Pmap.minBinding? right with
    | some (key, value) => joinCheck cmp reference left key value (Pmap.removeMinBinding right)
    | none => true

theorem concat_eq_of_check (cmp reference : α → α → LemOrdering)
    (left right : Pmap α β) (h : concatCheck cmp reference left right = true) :
    Pmap.concat cmp left right = Pmap.concat reference left right := by
  cases left with
  | Empty => rfl
  | Node ll lk lv lr lh =>
    cases right with
    | Empty => rfl
    | Node rl rk rv rr rh =>
      simp only [concatCheck, Pmap.concat] at h ⊢
      cases hm : Pmap.minBinding? (.Node rl rk rv rr rh) with
      | none => rfl
      | some pair =>
        obtain ⟨key, value⟩ := pair
        simp only [hm] at h ⊢
        exact join_eq_of_check cmp reference _ key value _ h

def concatOrJoinCheck (cmp reference : α → α → LemOrdering)
    (left : Pmap α β) (key : α) (value : Option β) (right : Pmap α β) : Bool :=
  match value with
  | some value => joinCheck cmp reference left key value right
  | none => concatCheck cmp reference left right

theorem concatOrJoin_eq_of_check (cmp reference : α → α → LemOrdering)
    (left : Pmap α β) (key : α) (value : Option β) (right : Pmap α β)
    (h : concatOrJoinCheck cmp reference left key value right = true) :
    Pmap.concatOrJoin cmp left key value right =
      Pmap.concatOrJoin reference left key value right := by
  cases value with
  | none => exact concat_eq_of_check cmp reference left right h
  | some value => exact join_eq_of_check cmp reference left key value right h

/-- Check split, recursive merge and rebuilding decisions against their
reference inputs. The callback and fuel are the same on both sides. -/
def mergeGoCheck (cmp reference : α → α → LemOrdering)
    (f : α → Option β → Option β → Option β) : Nat → Pmap α β → Pmap α β → Bool
  | 0, _, _ => true
  | n + 1, left, right =>
    match left, right with
    | .Empty, .Empty => true
    | .Node ll lk lv lr lh, _ =>
      if lh >= Pmap.height right then
        let (rl, rv, rr) := Pmap.split reference lk right
        splitCheck cmp reference lk right &&
          mergeGoCheck cmp reference f n ll rl && mergeGoCheck cmp reference f n lr rr &&
          concatOrJoinCheck cmp reference (Pmap.mergeGo reference f n ll rl)
            lk (f lk (some lv) rv) (Pmap.mergeGo reference f n lr rr)
      else match right with
        | .Node rl rk rv rr _ =>
          let (ll, lv, lr) := Pmap.split reference rk left
          splitCheck cmp reference rk left &&
            mergeGoCheck cmp reference f n ll rl && mergeGoCheck cmp reference f n lr rr &&
            concatOrJoinCheck cmp reference (Pmap.mergeGo reference f n ll rl)
              rk (f rk lv (some rv)) (Pmap.mergeGo reference f n lr rr)
        | .Empty => true
    | .Empty, .Node rl rk rv rr _ =>
      let (ll, lv, lr) := Pmap.split reference rk left
      splitCheck cmp reference rk left &&
        mergeGoCheck cmp reference f n ll rl && mergeGoCheck cmp reference f n lr rr &&
        concatOrJoinCheck cmp reference (Pmap.mergeGo reference f n ll rl)
          rk (f rk lv (some rv)) (Pmap.mergeGo reference f n lr rr)

theorem mergeGo_eq_of_check (cmp reference : α → α → LemOrdering)
    (f : α → Option β → Option β → Option β) (n : Nat) (left right : Pmap α β)
    (h : mergeGoCheck cmp reference f n left right = true) :
    Pmap.mergeGo cmp f n left right = Pmap.mergeGo reference f n left right := by
  induction n generalizing left right with
  | zero => rfl
  | succ n ih =>
    cases left with
    | Empty =>
      cases right with
      | Empty => rfl
      | Node rl rk rv rr rh =>
        simp only [mergeGoCheck, Pmap.mergeGo, Pmap.split, Bool.and_eq_true] at h ⊢
        obtain ⟨⟨⟨_, hl⟩, hr⟩, hj⟩ := h
        rw [ih _ _ hl, ih _ _ hr]
        exact concatOrJoin_eq_of_check cmp reference _ rk _ _ hj
    | Node ll lk lv lr lh =>
      simp only [mergeGoCheck, Pmap.mergeGo] at h ⊢
      split at h
      · rename_i hh
        simp only [if_pos hh]
        rcases he : Pmap.split reference lk right with ⟨rl, rv, rr⟩
        simp only [he, Bool.and_eq_true] at h
        obtain ⟨⟨⟨hs, hl⟩, hr⟩, hj⟩ := h
        rw [split_eq_of_check cmp reference lk right hs, he]
        rw [ih _ _ hl, ih _ _ hr]
        exact concatOrJoin_eq_of_check cmp reference _ lk _ _ hj
      · rename_i hh
        simp only [if_neg hh]
        cases right with
        | Empty => rfl
        | Node rl rk rv rr rh =>
          dsimp only
          rcases he : Pmap.split reference rk (.Node ll lk lv lr lh) with ⟨ll', lv', lr'⟩
          simp only [he, Bool.and_eq_true] at h
          obtain ⟨⟨⟨hs, hl⟩, hr⟩, hj⟩ := h
          rw [split_eq_of_check cmp reference rk (.Node ll lk lv lr lh) hs, he]
          rw [ih _ _ hl, ih _ _ hr]
          exact concatOrJoin_eq_of_check cmp reference _ rk _ _ hj

def mergeCheck (cmp reference : α → α → LemOrdering)
    (f : α → Option β → Option β → Option β) (left right : Pmap α β) : Bool :=
  mergeGoCheck cmp reference f (Pmap.height left + Pmap.height right + 1) left right

theorem merge_eq_of_check (cmp reference : α → α → LemOrdering)
    (f : α → Option β → Option β → Option β) (left right : Pmap α β)
    (h : mergeCheck cmp reference f left right = true) :
    Pmap.merge cmp f left right = Pmap.merge reference f left right :=
  mergeGo_eq_of_check cmp reference f _ left right h

def unionCheck (cmp reference : α → α → LemOrdering) (left right : Pmap α β) : Bool :=
  mergeCheck cmp reference (fun _ a b => match a, b with
    | _, some value => some value
    | some value, _ => some value
    | _, _ => none) left right

theorem union_eq_of_check (cmp reference : α → α → LemOrdering) (left right : Pmap α β)
    (h : unionCheck cmp reference left right = true) :
    Pmap.union cmp left right = Pmap.union reference left right :=
  merge_eq_of_check cmp reference _ left right h

/-- Fmap union uses the first stored comparator, or the second when
only that map exists. The static argument does not select the comparator. -/
def mapUnionCheck (leftCmp rightCmp reference : α → α → LemOrdering)
    (left right : EmittedFile.MapData α β) : Bool :=
  match left, right with
  | none, none => true
  | some left, right => unionCheck leftCmp reference left (right.getD .Empty)
  | none, some right => unionCheck rightCmp reference .Empty right

/-- Equal result data suffices for comparator-independent consumers such
as the shipped fold; the original result map still retains its comparator. -/
theorem mapData_union_of_check (leftCmp rightCmp reference static : α → α → LemOrdering)
    (left right : EmittedFile.MapData α β)
    (h : mapUnionCheck leftCmp rightCmp reference left right = true) :
    EmittedFile.mapData (fmapUnionBy static
      (EmittedFile.restoreMap leftCmp left) (EmittedFile.restoreMap rightCmp right)) =
    EmittedFile.mapData (fmapUnionBy static
      (EmittedFile.restoreMap reference left) (EmittedFile.restoreMap reference right)) := by
  cases left with
  | none =>
    cases right with
    | none => rfl
    | some right =>
      exact congrArg some (union_eq_of_check rightCmp reference .Empty right h)
  | some left =>
    cases right with
    | none => exact congrArg some (union_eq_of_check leftCmp reference left .Empty h)
    | some right => exact congrArg some (union_eq_of_check leftCmp reference left right h)

/-- Lem_Map_extra.fold converts the bindings to a set and folds that set.
Its behavior depends on map data, not the captured map comparator. This
preserves the shipped binding-to-set conversion and its own comparisons. -/
theorem fold_eq_of_mapData_eq [Lem_Map.MapKeyType α] [Lem_Basic_classes.SetType α]
    [Lem_Basic_classes.SetType β] {γ : Type} (f : α → β → γ → γ)
    (left right : Fmap α β) (initial : γ)
    (h : EmittedFile.mapData left = EmittedFile.mapData right) :
    Lem_Map_extra.fold f left initial = Lem_Map_extra.fold f right initial := by
  cases left with
  | empty =>
    cases right with
    | empty => rfl
    | mk cmp tree => cases h
  | mk cmp tree =>
    cases right with
    | empty => cases h
    | mk cmp' tree' =>
      have ht := Option.some.inj h
      cases ht
      rfl

end CerberusHeapLang.EmittedMapChecks
