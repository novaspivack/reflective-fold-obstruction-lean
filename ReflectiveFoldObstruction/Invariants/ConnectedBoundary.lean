/-
  **Relative boundary separation** — disconnectedness witnesses for a distinguished subset.

  Models the situation “the boundary falls into two disjoint relative clopens” without yet
  assuming a `TopologicalSpace`.  A refinement to genuine **clopen separation in a
  subspace topology** comes from `Topology/` once chart models carry `TopologicalSpace`
  instances.

  - **`RelBoundarySep`:** classical cover/disjoint witness on a set `B` relative to
    ambient sets `U` and `V`.
  - **Equiv-invariance:** images under an equivalence preserve and reflect separation.
  - **Connectivity predicate:** `IsRelBoundaryConnected B := ¬ HasRelBoundarySep B`.

  See `specs/NOTES/PROJECT_VISION.md` — Invariants/ConnectedBoundary.
-/

import Mathlib.Data.Set.Image
import Mathlib.Logic.Equiv.Set

import ReflectiveFoldObstruction.Invariants.BoundaryType

universe u

namespace ReflectiveFoldObstruction.Invariants.ConnectedBoundary

open Set Equiv Function

variable {α β : Type u}

/-- Relative separation witness for `B` along a cover by `U` and `V` (set-level chart halves). -/
structure RelBoundarySep (B U V : Set α) : Prop where
  /-- `B` is covered by `U ∪ V`. -/
  cov : B ⊆ U ∪ V
  /-- Some boundary point lies in `U`. -/
  left : (B ∩ U).Nonempty
  /-- Some boundary point lies in `V`. -/
  right : (B ∩ V).Nonempty
  /-- The two sides are disjoint *within* `B`. -/
  disjoint : Disjoint (B ∩ U) (B ∩ V)

/-- There exist sets exhibiting relative boundary separation of `B`. -/
def HasRelBoundarySep (B : Set α) : Prop :=
  ∃ U V : Set α, RelBoundarySep B U V

/-- `B` admits **no** binary relative separation — a set-theoretic stand-in for “one piece.” -/
def IsRelBoundaryConnected (B : Set α) : Prop :=
  ¬HasRelBoundarySep B

namespace RelBoundarySep

theorem boundary_nonempty {B U V : Set α} (h : RelBoundarySep B U V) : B.Nonempty := by
  rcases h.left with ⟨x, hx⟩
  rw [mem_inter_iff] at hx
  exact ⟨x, hx.1⟩

/-- Equivariant transport of a separation witness. -/
theorem image_equiv (e : α ≃ β) {B U V : Set α} (h : RelBoundarySep B U V) :
    RelBoundarySep (e '' B) (e '' U) (e '' V) where
  cov := by
    rintro y ⟨x, hxB, rfl⟩
    rcases h.cov hxB with (hxU | hxV)
    · left; exact ⟨x, hxU, rfl⟩
    · right; exact ⟨x, hxV, rfl⟩
  left := by
    rcases h.left with ⟨x, hx⟩
    rw [mem_inter_iff] at hx
    refine ⟨e x, ?_⟩
    rw [mem_inter_iff]
    exact ⟨mem_image_of_mem e hx.1, mem_image_of_mem e hx.2⟩
  right := by
    rcases h.right with ⟨x, hx⟩
    rw [mem_inter_iff] at hx
    refine ⟨e x, ?_⟩
    rw [mem_inter_iff]
    exact ⟨mem_image_of_mem e hx.1, mem_image_of_mem e hx.2⟩
  disjoint := by
    rw [← Set.image_inter e.injective, ← Set.image_inter e.injective]
    exact disjoint_image_of_injective e.injective h.disjoint

end RelBoundarySep

theorem HasRelBoundarySep.iff_image_equiv (e : α ≃ β) (B : Set α) :
    HasRelBoundarySep B ↔ HasRelBoundarySep (e '' B) := by
  constructor
  · rintro ⟨U, V, h⟩
    exact ⟨e '' U, e '' V, h.image_equiv e⟩
  · rintro ⟨U', V', h⟩
    refine ⟨e.symm '' U', e.symm '' V', ?_⟩
    simpa only [Equiv.symm_image_image] using h.image_equiv e.symm

theorem IsRelBoundaryConnected.iff_image_equiv (e : α ≃ β) (B : Set α) :
    IsRelBoundaryConnected B ↔ IsRelBoundaryConnected (e '' B) := by
  simp only [IsRelBoundaryConnected, HasRelBoundarySep.iff_image_equiv e]

/-- A chart typing’s boundary fiber cannot be separated if the typing is globally interior. -/
theorem not_HasRelBoundarySep_of_AllInterior {α : Type u} (τ : α → BoundaryType.LocalModelKind)
    (hτ : BoundaryType.AllInterior τ) :
    ¬HasRelBoundarySep (BoundaryType.boundaryFiber τ) := by
  rintro ⟨U, V, h⟩
  rcases h.left with ⟨x, hx⟩
  rw [mem_inter_iff, BoundaryType.mem_boundaryFiber] at hx
  exact BoundaryType.not_interior_and_boundary τ x (hτ x) hx.1

/-- If the boundary fiber admits separation then the typing is not all-interior. -/
theorem ExistsBoundaryPoint.of_boundaryFiber_HasRelBoundarySep {α : Type u}
    (τ : α → BoundaryType.LocalModelKind) (h : HasRelBoundarySep (BoundaryType.boundaryFiber τ)) :
    BoundaryType.ExistsBoundaryPoint τ := by
  rcases h with ⟨U, V, hsep⟩
  rcases hsep.left with ⟨x, hx⟩
  rw [mem_inter_iff, BoundaryType.mem_boundaryFiber] at hx
  exact ⟨x, hx.1⟩

end ReflectiveFoldObstruction.Invariants.ConnectedBoundary
