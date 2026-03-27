/-
  **Lightweight architecture obstruction packaging** — stable `architecture_*` spellings for
  `Obstruction.Fold` (`SPEC_012`).

  No new mathematics: uniform names for papers citing the internal-reachability + mismatch
  pattern without duplicating `α → Prop` bookkeeping.
-/

import Mathlib.Logic.Relation

import Mathlib.Data.Set.Defs

import ReflectiveFoldObstruction.Obstruction.Fold
import ReflectiveFoldObstruction.Reachability.ClosureHull
import ReflectiveFoldObstruction.Reachability.InternalOps

universe u

namespace ReflectiveFoldObstruction.Core.ArchitectureObstruction

open Set Relation
open ReflectiveFoldObstruction.Obstruction.Fold
open ReflectiveFoldObstruction.Reachability.ClosureHull
open ReflectiveFoldObstruction.Reachability.InternalOps

variable {α : Type u} {r : α → α → Prop} {I : α → Prop}

theorem architecture_internal_reachability_preserves_invariant (h : PreservedBy r I) ⦃a b : α⦄
    (hab : ReflTransGen r a b) : I a → I b :=
  internal_reachability_preserves_invariant h hab

theorem architecture_fold_obstruction_of_invariant_mismatch (h : PreservedBy r I) {S T : α}
    (hS : I S) (hT : ¬ I T) : ¬ ReflTransGen r S T :=
  fold_obstruction_of_invariant_mismatch h hS hT

theorem architecture_seed_hull_preserves_invariant {S₀ : Set α} (h : PreservedBy r I) (h₀ : ∀ s ∈ S₀, I s)
    ⦃x : α⦄ (hx : x ∈ reachableFrom r S₀) : I x :=
  reachableFrom_hull_preserves_invariant h h₀ hx

theorem architecture_not_mem_hull_of_mismatch {S₀ : Set α} {T : α} (h : PreservedBy r I)
    (h₀ : ∀ s ∈ S₀, I s) (hT : ¬ I T) : T ∉ reachableFrom r S₀ :=
  not_mem_reachableFrom_of_preserved_invariant_mismatch h h₀ hT

theorem architecture_not_reachable_of_mismatch (h : PreservedBy r I) {S T : α} (hS : I S)
    (hT : ¬ I T) : ¬ ReflTransGen r S T :=
  architecture_fold_obstruction_of_invariant_mismatch h hS hT

end ReflectiveFoldObstruction.Core.ArchitectureObstruction
