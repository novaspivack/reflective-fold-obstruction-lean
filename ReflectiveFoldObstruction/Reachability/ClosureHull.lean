/-
  **Reachability hulls** — points attainable from a seed set along `ReflTransGen`.

  This is the thin set-theoretic hull used before importing heavier `Topology` convergence
  notions.  Idempotence mirrors “saturation = closure” for reflexive transitive closure.

  See `specs/NOTES/PROJECT_VISION.md` — Reachability/ClosureHull.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation

universe u

namespace ReflectiveFoldObstruction.Reachability.ClosureHull

open Relation Set

variable {α : Type u} (r : α → α → Prop)

/-- Elements reachable from the seed set `S` along `r⋆` (`ReflTransGen`). -/
def reachableFrom (S : Set α) : Set α :=
  { y | ∃ x ∈ S, ReflTransGen r x y }

@[simp] theorem mem_reachableFrom {S : Set α} {y : α} :
    y ∈ reachableFrom r S ↔ ∃ x ∈ S, ReflTransGen r x y :=
  Iff.rfl

theorem subset_reachableFrom (S : Set α) : S ⊆ reachableFrom r S := by
  intro x hx
  exact ⟨x, hx, ReflTransGen.refl⟩

theorem reachableFrom_mono {S T : Set α} (h : S ⊆ T) : reachableFrom r S ⊆ reachableFrom r T := by
  rintro y ⟨x, hx, hxy⟩
  exact ⟨x, h hx, hxy⟩

theorem reachableFrom_union (S T : Set α) :
    reachableFrom r (S ∪ T) = reachableFrom r S ∪ reachableFrom r T := by
  ext y
  simp only [mem_reachableFrom, mem_union]
  constructor
  · rintro ⟨x, hx, hxy⟩
    rcases hx with hxS | hxT
    · left; exact ⟨x, hxS, hxy⟩
    · right; exact ⟨x, hxT, hxy⟩
  · rintro (⟨x, hxS, hxy⟩ | ⟨x, hxT, hxy⟩)
    · exact ⟨x, Or.inl hxS, hxy⟩
    · exact ⟨x, Or.inr hxT, hxy⟩

/-- Saturation is idempotent: reaching twice does not enlarge the hull. -/
theorem reachableFrom_idem (S : Set α) :
    reachableFrom r (reachableFrom r S) = reachableFrom r S := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, hxz⟩, hzy⟩
    exact ⟨x, hx, hxz.trans hzy⟩
  · intro h
    rcases h with ⟨x, hx, hxy⟩
    refine ⟨x, ?_, hxy⟩
    exact subset_reachableFrom r S hx

end ReflectiveFoldObstruction.Reachability.ClosureHull
