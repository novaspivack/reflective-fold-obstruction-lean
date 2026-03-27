/-
  **Universal fold pattern** over bundled architecture data (`SPEC_017`).

  Theorems are definitionally identical to `Obstruction.Fold` — this module exists so papers can
  cite **`architecture_class_*`** without re-expanding records at each instance.
-/

import Mathlib.Logic.Relation

import ReflectiveFoldObstruction.Obstruction.Fold
import ReflectiveFoldObstruction.Reachability.ArchitectureClasses
import ReflectiveFoldObstruction.Reachability.ClosureHull
import ReflectiveFoldObstruction.Reachability.InternalOps

universe u

namespace ReflectiveFoldObstruction.Obstruction.ArchitectureUniversality

open Set Relation
open ReflectiveFoldObstruction.Obstruction.Fold
open ReflectiveFoldObstruction.Reachability.ArchitectureClasses
open ReflectiveFoldObstruction.Reachability.ClosureHull
open ReflectiveFoldObstruction.Reachability.InternalOps

variable {α : Type u}

/-- Mismatch ⇒ pairwise non-reachability (`SPEC_017`). -/
theorem architecture_class_preserved_invariant_obstruction (A : FoldObstructionBundle α)
    (hp : PreservedBy A.rel A.Inv) (hS : A.Inv A.S) (hT : ¬ A.Inv A.T) :
    ¬ ReflTransGen A.rel A.S A.T :=
  fold_obstruction_of_invariant_mismatch hp hS hT

/-- Mismatch ⇒ seed hull exclusion (`SPEC_017`). -/
theorem architecture_class_hull_exclusion (A : FoldObstructionBundle α)
    (hp : PreservedBy A.rel A.Inv) {S₀ : Set α} (h₀ : ∀ s ∈ S₀, A.Inv s) (hT : ¬ A.Inv A.T) :
    A.T ∉ reachableFrom A.rel S₀ :=
  not_mem_reachableFrom_of_preserved_invariant_mismatch hp h₀ hT

/-- Stable alias: universal fold pattern = `fold_obstruction_of_invariant_mismatch` on the bundle (`SPEC_017`). -/
theorem universal_fold_pattern_for_architecture_class (A : FoldObstructionBundle α)
    (hp : PreservedBy A.rel A.Inv) (hS : A.Inv A.S) (hT : ¬ A.Inv A.T) :
    ¬ ReflTransGen A.rel A.S A.T :=
  architecture_class_preserved_invariant_obstruction A hp hS hT

end ReflectiveFoldObstruction.Obstruction.ArchitectureUniversality
