/-
Data projection for a complete emitted file, retaining map trees exactly.
Captured map comparators are separate parameters, never compared or
replaced. `restore_capture` proves reconstruction of the original file.
This is representation support for A7, not an execution certificate.
-/
import Core_run_aux

set_option autoImplicit false

namespace CerberusHeapLang.EmittedFile

/-- `none` preserves `Fmap.empty`; `some tree` preserves `Fmap.mk`,
including the distinct case of a captured comparator with an empty tree. -/
abbrev MapData (α β : Type) := Option (Pmap α β)

def mapData {α β : Type} : Fmap α β → MapData α β
  | .empty => none
  | .mk _ tree => some tree

/-- The fallback is unused when restoring an empty map. -/
def mapComparator {α β : Type} (fallback : α → α → LemOrdering) :
    Fmap α β → α → α → LemOrdering
  | .empty => fallback
  | .mk cmp _ => cmp

def restoreMap {α β : Type} (cmp : α → α → LemOrdering) : MapData α β → Fmap α β
  | none => .empty
  | some tree => .mk cmp tree

theorem restoreMap_capture {α β : Type} (fallback : α → α → LemOrdering)
    (m : Fmap α β) : restoreMap (mapComparator fallback m) (mapData m) = m := by
  cases m <;> rfl

theorem mapData_restoreMap {α β : Type} (cmp : α → α → LemOrdering)
    (d : MapData α β) : mapData (restoreMap cmp d) = d := by
  cases d <;> rfl

/-- All eleven file fields, with exact finite-map representation data.
Tree heights, source locations, symbols, annotations and metadata remain.
The data excludes only the eight top-level map comparator functions. -/
structure Data where
  main : Option sym
  callingConvention : calling_convention
  tagDefs : MapData sym (CerbLocation.Loc × tag_definition)
  stdlib : MapData sym (generic_fun_map_decl Unit core_run_annotation)
  impl : MapData implementation_constant (generic_impl_decl Unit)
  globs : List (sym × generic_globs core_run_annotation Unit)
  funs : MapData sym (generic_fun_map_decl Unit core_run_annotation)
  extern : MapData identifier (List sym × linking_kind)
  funinfo : MapData sym
    (CerbLocation.Loc × attributes × ctype × List (Option sym × ctype) × Bool × Bool)
  loopAttributes : MapData loop_id loop_attribute
  visibleObjects : MapData Nat (List (sym × ctype))

structure Comparators where
  tagDefs : sym → sym → LemOrdering
  stdlib : sym → sym → LemOrdering
  impl : implementation_constant → implementation_constant → LemOrdering
  funs : sym → sym → LemOrdering
  extern : identifier → identifier → LemOrdering
  funinfo : sym → sym → LemOrdering
  loopAttributes : loop_id → loop_id → LemOrdering
  visibleObjects : Nat → Nat → LemOrdering

def captureData (f : file core_run_annotation) : Data :=
  ⟨f.main, f.calling_convention0, mapData f.tagDefs, mapData f.stdlib,
    mapData f.impl0, f.globs, mapData f.funs, mapData f.extern,
    mapData f.funinfo, mapData f.loop_attributes1, mapData f.visible_objects_env0⟩

def captureComparators (fallback : Comparators) (f : file core_run_annotation) : Comparators :=
  ⟨mapComparator fallback.tagDefs f.tagDefs,
    mapComparator fallback.stdlib f.stdlib,
    mapComparator fallback.impl f.impl0,
    mapComparator fallback.funs f.funs,
    mapComparator fallback.extern f.extern,
    mapComparator fallback.funinfo f.funinfo,
    mapComparator fallback.loopAttributes f.loop_attributes1,
    mapComparator fallback.visibleObjects f.visible_objects_env0⟩

def restore (cmp : Comparators) (d : Data) : file core_run_annotation :=
  { main := d.main
    calling_convention0 := d.callingConvention
    tagDefs := restoreMap cmp.tagDefs d.tagDefs
    stdlib := restoreMap cmp.stdlib d.stdlib
    impl0 := restoreMap cmp.impl d.impl
    globs := d.globs
    funs := restoreMap cmp.funs d.funs
    extern := restoreMap cmp.extern d.extern
    funinfo := restoreMap cmp.funinfo d.funinfo
    loop_attributes1 := restoreMap cmp.loopAttributes d.loopAttributes
    visible_objects_env0 := restoreMap cmp.visibleObjects d.visibleObjects }

theorem restore_capture (fallback : Comparators) (f : file core_run_annotation) :
    restore (captureComparators fallback f) (captureData f) = f := by
  cases f
  simp only [restore, captureData, captureComparators, restoreMap_capture]

theorem captureData_restore (cmp : Comparators) (d : Data) :
    captureData (restore cmp d) = d := by
  cases d
  simp only [captureData, restore, mapData_restoreMap]

/-- A data equality plus the original comparators gives actual file
equality. This does not assume comparators agree with a canonical order. -/
theorem restore_eq_of_data_eq (fallback : Comparators) (f : file core_run_annotation)
    (d : Data) (h : captureData f = d) :
    restore (captureComparators fallback f) d = f := by
  rw [← h, restore_capture]

/-- Check only the comparator decisions visited by a reference lookup.
No ordering law or agreement outside this finite path is required. -/
def lookupPathAgrees {α β : Type} (cmp reference : α → α → LemOrdering)
    (key : α) : Pmap α β → Bool
  | .Empty => true
  | .Node left node _value right _height =>
    decide (cmp key node = reference key node) &&
      match reference key node with
      | .EQ => true
      | .LT => lookupPathAgrees cmp reference key left
      | .GT => lookupPathAgrees cmp reference key right

theorem lookupPathAgrees_correct {α β : Type} (cmp reference : α → α → LemOrdering)
    (key : α) (tree : Pmap α β) (h : lookupPathAgrees cmp reference key tree = true) :
    Pmap.find? cmp key tree = Pmap.find? reference key tree := by
  induction tree with
  | Empty => rfl
  | Node left node value right height ihl ihr =>
    cases hc : cmp key node <;> cases hr : reference key node <;>
      simp_all [lookupPathAgrees, Pmap.find?]

def mapLookupCheck {α β : Type} (cmp reference : α → α → LemOrdering)
    (key : α) : MapData α β → Bool
  | none => true
  | some tree => lookupPathAgrees cmp reference key tree

theorem restoreMap_lookup_of_check {α β : Type}
    (cmp reference static : α → α → LemOrdering) (key : α) (d : MapData α β)
    (h : mapLookupCheck cmp reference key d = true) :
    fmapLookupBy static key (restoreMap cmp d) =
      fmapLookupBy static key (restoreMap reference d) := by
  cases d with
  | none => rfl
  | some tree => exact lookupPathAgrees_correct cmp reference key tree h

end CerberusHeapLang.EmittedFile
