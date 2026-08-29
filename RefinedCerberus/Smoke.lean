/-
Arc-0 smoke test: the iris-lean dependency builds and its BI proof
mode is usable from this package. A trivial separation-logic lemma,
proved in the Iris proof mode — plumbing check only, no content.
-/
import Iris

namespace RefinedCerberus

open Iris

theorem smoke {PROP : Type _} [BI PROP] (P Q : PROP) : P ∗ Q ⊢ Q ∗ P := by
  iintro ⟨HP, HQ⟩
  isplitl [HQ]
  · iexact HQ
  · iexact HP

end RefinedCerberus
