/-
  **Lightweight architecture obstruction packaging** — stable `architecture_*` spellings for
  `Obstruction.Fold` (`SPEC_012`) + **bundled** architecture class consumers (`SPEC_017`).

  `ArchitectureClasses` / `ArchitectureUniversality` carry the record layer; this file keeps the
  stable **re-export surface** for `import ReflectiveFoldObstruction.Core.ArchitectureObstruction`.
-/

import Mathlib.Logic.Relation

import Mathlib.Data.Set.Defs

import ReflectiveFoldObstruction.Obstruction.ArchitectureUniversality
import ReflectiveFoldObstruction.Obstruction.Fold
import ReflectiveFoldObstruction.Reachability.ArchitectureClasses
import ReflectiveFoldObstruction.Reachability.ClosureHull
import ReflectiveFoldObstruction.Reachability.InternalOps

universe u

namespace ReflectiveFoldObstruction.Core.ArchitectureObstruction

open Set Relation
open ReflectiveFoldObstruction.Obstruction.Fold
open ReflectiveFoldObstruction.Reachability.ArchitectureClasses
open ReflectiveFoldObstruction.Reachability.ClosureHull
open ReflectiveFoldObstruction.Reachability.InternalOps

-- Stable **`Core`** names for **`SPEC_017`** (proofs live in `Obstruction/ArchitectureUniversality.lean`).
theorem architecture_class_preserved_invariant_obstruction {α : Type u} (A : FoldObstructionBundle α)
    (hp : PreservedBy A.rel A.Inv) (hS : A.Inv A.S) (hT : ¬ A.Inv A.T) :
    ¬ ReflTransGen A.rel A.S A.T :=
  Obstruction.ArchitectureUniversality.architecture_class_preserved_invariant_obstruction A hp hS hT

theorem architecture_class_hull_exclusion {α : Type u} (A : FoldObstructionBundle α)
    (hp : PreservedBy A.rel A.Inv) {S₀ : Set α} (h₀ : ∀ s ∈ S₀, A.Inv s) (hT : ¬ A.Inv A.T) :
    A.T ∉ reachableFrom A.rel S₀ :=
  Obstruction.ArchitectureUniversality.architecture_class_hull_exclusion A hp h₀ hT

theorem universal_fold_pattern_for_architecture_class {α : Type u} (A : FoldObstructionBundle α)
    (hp : PreservedBy A.rel A.Inv) (hS : A.Inv A.S) (hT : ¬ A.Inv A.T) :
    ¬ ReflTransGen A.rel A.S A.T :=
  Obstruction.ArchitectureUniversality.universal_fold_pattern_for_architecture_class A hp hS hT

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
