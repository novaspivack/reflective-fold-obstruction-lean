/-
  **Reachability invariants** — predicates stable under saturation.

  Bundles `InternalOps.ForwardClosed` with `ClosureHull.reachableFrom` so later reflective
  layers can speak about “properties preserved inside the regressive hull”.

  **`SPEC_005` / `SPEC_006`:** stable aliases for obstruction consumers (`preserved_mem_reachableFrom`,
  subset / mismatch lemmas).

  See `specs/NOTES/PROJECT_VISION.md` — Reachability/Invariants.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation

import ReflectiveFoldObstruction.Reachability.ClosureHull
import ReflectiveFoldObstruction.Reachability.InternalOps

universe u

namespace ReflectiveFoldObstruction.Reachability.Invariants

open Set Relation

variable {α : Type u} {r : α → α → Prop} {P : α → Prop}

/-- Forward-closed predicates hold on the entire `reachableFrom` hull of any seed satisfying `P`. -/
theorem ForwardClosed.mem_reachableFrom {S : Set α} (hP : InternalOps.ForwardClosed r P)
    (hS : ∀ x ∈ S, P x) ⦃y : α⦄ (hy : y ∈ ClosureHull.reachableFrom r S) : P y :=
  ClosureHull.mem_reachableFrom_induction r hS hP hy

/-- Stable citation name: membership in the hull inherits `P` from a `P`-seed (`SPEC_006`). -/
theorem preserved_mem_reachableFrom {S : Set α} (hP : InternalOps.ForwardClosed r P)
    (hS : ∀ x ∈ S, P x) ⦃y : α⦄ (hy : y ∈ ClosureHull.reachableFrom r S) : P y :=
  ForwardClosed.mem_reachableFrom hP hS hy

theorem reachableFrom_subset_of_preserved {S : Set α} (hseed : ∀ x ∈ S, P x)
    (hP : InternalOps.ForwardClosed r P) : ClosureHull.reachableFrom r S ⊆ { y | P y } :=
  ClosureHull.reachableFrom_subset_setOf r hseed hP

theorem not_mem_reachableFrom_of_preserved_mismatch {S : Set α} {T : α}
    (hP : InternalOps.ForwardClosed r P) (hseed : ∀ x ∈ S, P x) (hT : ¬ P T) :
    T ∉ ClosureHull.reachableFrom r S :=
  ClosureHull.not_mem_reachableFrom_of_preserved_mismatch r hP hseed hT

theorem reachableFrom_eq_of_seed_univ [Nonempty α] (h : ∀ x y : α, ReflTransGen r x y) (S : Set α)
    (hne : S.Nonempty) : ClosureHull.reachableFrom r S = Set.univ := by
  ext y
  rcases hne with ⟨x₀, hx₀⟩
  simp only [mem_univ, iff_true, ClosureHull.mem_reachableFrom]
  exact ⟨x₀, hx₀, h x₀ y⟩

end ReflectiveFoldObstruction.Reachability.Invariants
