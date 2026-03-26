/-
  **Reachability invariants** — predicates stable under saturation.

  Bundles `InternalOps.ForwardClosed` with `ClosureHull.reachableFrom` so later reflective
  layers can speak about “properties preserved inside the regressive hull”.

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
    (hS : ∀ x ∈ S, P x) ⦃y : α⦄ (hy : y ∈ ClosureHull.reachableFrom r S) : P y := by
  rcases hy with ⟨x, hxS, hxy⟩
  exact InternalOps.ReflTransGen.forwardClosed hP hxy (hS x hxS)

theorem reachableFrom_eq_of_seed_univ [Nonempty α] (h : ∀ x y : α, ReflTransGen r x y) (S : Set α)
    (hne : S.Nonempty) : ClosureHull.reachableFrom r S = Set.univ := by
  ext y
  rcases hne with ⟨x₀, hx₀⟩
  simp only [mem_univ, iff_true, ClosureHull.mem_reachableFrom]
  exact ⟨x₀, hx₀, h x₀ y⟩

end ReflectiveFoldObstruction.Reachability.Invariants
