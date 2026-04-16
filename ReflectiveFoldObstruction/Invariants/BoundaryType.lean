/-
  **Boundary typing** — abstract interior vs boundary local model tags.

  This layer does *not* build smooth manifolds yet; it packages the bookkeeping the
  vision calls “half-line vs line / half-plane vs plane” at the level of **typing
  functions** `α → LocalModelKind`.

  - **Transport:** push a typing along `Equiv` (same pattern as `Transport.transportPred`).
  - **Pullback:** precompose with any map (local model induced from a chart domain).
  - **Incompatibility:** a point cannot be tagged both interior and boundary; global
    “all interior” contradicts “somewhere boundary”.

  Homeomorphisms: compose `Homeomorph.toEquiv` with these definitions.

  Module context: Invariants/BoundaryType.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Equiv.Defs

universe u

namespace ReflectiveFoldObstruction.Invariants.BoundaryType

open Function Equiv

/-- Abstract tag for an interior-like vs boundary-like local model (chart typing). -/
inductive LocalModelKind : Type
  | interior
  | boundary
  deriving DecidableEq, Repr

variable {α β γ : Type u}

/-- Pull back a typing along `f : α → β`. -/
def pullbackTyping (f : α → β) (τ : β → LocalModelKind) : α → LocalModelKind :=
  τ ∘ f

@[simp] theorem pullbackTyping_apply (f : α → β) (τ : β → LocalModelKind) (a : α) :
    pullbackTyping f τ a = τ (f a) :=
  rfl

/-- Push a typing on `α` forward to `β` along `e : α ≃ β`. -/
def transportTyping (e : α ≃ β) (τ : α → LocalModelKind) : β → LocalModelKind :=
  τ ∘ e.symm

@[simp] theorem transportTyping_apply (e : α ≃ β) (τ : α → LocalModelKind) (b : β) :
    transportTyping e τ b = τ (e.symm b) :=
  rfl

theorem transportTyping_rfl (τ : α → LocalModelKind) :
    transportTyping (Equiv.refl α) τ = τ := by
  funext x
  simp [transportTyping]

theorem transportTyping_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) (τ : α → LocalModelKind) :
    transportTyping (e₁.trans e₂) τ = transportTyping e₂ (transportTyping e₁ τ) := by
  funext x
  simp [transportTyping]

/-- `transportTyping` is functorial in the equivalence. -/
theorem transportTyping_map_symm (e : α ≃ β) (τ : α → LocalModelKind) :
    transportTyping e.symm (transportTyping e τ) = τ := by
  funext x
  simp [transportTyping, Equiv.symm_symm, Equiv.symm_apply_apply]

theorem transportTyping_map (e : α ≃ β) (τ : β → LocalModelKind) :
    transportTyping e (transportTyping e.symm τ) = τ := by
  funext x
  simp [transportTyping, Equiv.symm_symm, Equiv.apply_symm_apply]

@[simp] theorem transportTyping_eq_iff (e : α ≃ β) (τ : α → LocalModelKind) (a : α)
    (k : LocalModelKind) :
    transportTyping e τ (e a) = k ↔ τ a = k := by
  simp [transportTyping]

/-- Classical: some point is boundary-tagged. -/
def ExistsBoundaryPoint (τ : α → LocalModelKind) : Prop :=
  ∃ x, τ x = LocalModelKind.boundary

/-- Classical: some point is interior-tagged. -/
def ExistsInteriorPoint (τ : α → LocalModelKind) : Prop :=
  ∃ x, τ x = LocalModelKind.interior

/-- Every point is interior-tagged (“global interior chart” / boundary empty). -/
def AllInterior (τ : α → LocalModelKind) : Prop :=
  ∀ x, τ x = LocalModelKind.interior

/-- Every point is boundary-tagged (degenerate border case; useful for contradictions). -/
def AllBoundary (τ : α → LocalModelKind) : Prop :=
  ∀ x, τ x = LocalModelKind.boundary

theorem ExistsBoundaryPoint.iff_transport (e : α ≃ β) (τ : α → LocalModelKind) :
    ExistsBoundaryPoint τ ↔ ExistsBoundaryPoint (transportTyping e τ) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨e x, by simp [transportTyping, hx]⟩
  · rintro ⟨y, hy⟩
    exact ⟨e.symm y, by simp [transportTyping] at hy; exact hy⟩

theorem ExistsInteriorPoint.iff_transport (e : α ≃ β) (τ : α → LocalModelKind) :
    ExistsInteriorPoint τ ↔ ExistsInteriorPoint (transportTyping e τ) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨e x, by simp [transportTyping, hx]⟩
  · rintro ⟨y, hy⟩
    exact ⟨e.symm y, by simp [transportTyping] at hy; exact hy⟩

theorem AllInterior.iff_transport (e : α ≃ β) (τ : α → LocalModelKind) :
    AllInterior τ ↔ AllInterior (transportTyping e τ) := by
  constructor
  · intro h b
    rw [transportTyping_apply]
    exact h (e.symm b)
  · intro h a
    simpa [transportTyping, Equiv.apply_symm_apply] using h (e a)

theorem AllBoundary.iff_transport (e : α ≃ β) (τ : α → LocalModelKind) :
    AllBoundary τ ↔ AllBoundary (transportTyping e τ) := by
  constructor
  · intro h b
    rw [transportTyping_apply]
    exact h (e.symm b)
  · intro h a
    simpa [transportTyping, Equiv.apply_symm_apply] using h (e a)

/-- Same point cannot be both interior- and boundary-tagged. -/
theorem not_interior_and_boundary (τ : α → LocalModelKind) (x : α)
    (hi : τ x = LocalModelKind.interior) (hb : τ x = LocalModelKind.boundary) :
    False := by
  rw [hi] at hb
  cases hb

/-- Global “all interior” forbids any boundary-tagged point. -/
theorem AllInterior.not_ExistsBoundaryPoint {τ : α → LocalModelKind}
    (h : AllInterior τ) : ¬ExistsBoundaryPoint τ := by
  rintro ⟨x, hx⟩
  exact not_interior_and_boundary τ x (h x) hx

/-- Any boundary-tagged point refutes “all interior”. -/
theorem ExistsBoundaryPoint.not_AllInterior {τ : α → LocalModelKind}
    (h : ExistsBoundaryPoint τ) : ¬AllInterior τ := fun hI =>
  hI.not_ExistsBoundaryPoint h

/-- Dual: all boundary forbids an interior-tagged point. -/
theorem AllBoundary.not_ExistsInteriorPoint {τ : α → LocalModelKind}
    (h : AllBoundary τ) : ¬ExistsInteriorPoint τ := by
  rintro ⟨x, hx⟩
  rw [h x] at hx
  cases hx

theorem ExistsInteriorPoint.not_AllBoundary {τ : α → LocalModelKind}
    (h : ExistsInteriorPoint τ) : ¬AllBoundary τ := fun hB =>
  hB.not_ExistsInteriorPoint h

theorem pullbackTyping_comp (f : β → γ) (g : α → β) (τ : γ → LocalModelKind) :
    pullbackTyping (f ∘ g) τ = pullbackTyping g (pullbackTyping f τ) :=
  rfl

theorem ExistsBoundaryPoint.of_pullback {f : α → β} {τ : β → LocalModelKind}
    (h : ExistsBoundaryPoint (pullbackTyping f τ)) : ExistsBoundaryPoint τ := by
  rcases h with ⟨a, ha⟩
  exact ⟨f a, ha⟩

theorem ExistsInteriorPoint.of_pullback {f : α → β} {τ : β → LocalModelKind}
    (h : ExistsInteriorPoint (pullbackTyping f τ)) : ExistsInteriorPoint τ := by
  rcases h with ⟨a, ha⟩
  exact ⟨f a, ha⟩

theorem AllInterior.of_pullback_surjective {f : α → β} {τ : β → LocalModelKind}
    (hf : Function.Surjective f) (h : AllInterior (pullbackTyping f τ)) : AllInterior τ := by
  intro b
  rcases hf b with ⟨a, rfl⟩
  exact h a

theorem AllBoundary.of_pullback_surjective {f : α → β} {τ : β → LocalModelKind}
    (hf : Function.Surjective f) (h : AllBoundary (pullbackTyping f τ)) : AllBoundary τ := by
  intro b
  rcases hf b with ⟨a, rfl⟩
  exact h a

section Fibers

variable {α : Type u}

/-- Set of points tagged as boundary. -/
def boundaryFiber (τ : α → LocalModelKind) : Set α :=
  { x | τ x = LocalModelKind.boundary }

/-- Set of points tagged as interior. -/
def interiorFiber (τ : α → LocalModelKind) : Set α :=
  { x | τ x = LocalModelKind.interior }

@[simp] theorem mem_boundaryFiber (τ : α → LocalModelKind) (x : α) :
    x ∈ boundaryFiber τ ↔ τ x = LocalModelKind.boundary :=
  Iff.rfl

@[simp] theorem mem_interiorFiber (τ : α → LocalModelKind) (x : α) :
    x ∈ interiorFiber τ ↔ τ x = LocalModelKind.interior :=
  Iff.rfl

theorem ExistsBoundaryPoint.iff_boundaryFiber_nonempty (τ : α → LocalModelKind) :
    ExistsBoundaryPoint τ ↔ (boundaryFiber τ).Nonempty := by
  simp [ExistsBoundaryPoint, Set.Nonempty]

theorem ExistsInteriorPoint.iff_interiorFiber_nonempty (τ : α → LocalModelKind) :
    ExistsInteriorPoint τ ↔ (interiorFiber τ).Nonempty := by
  simp [ExistsInteriorPoint, Set.Nonempty]

theorem AllInterior.iff_eq_univ_interiorFiber (τ : α → LocalModelKind) :
    AllInterior τ ↔ interiorFiber τ = Set.univ := by
  simp [AllInterior, interiorFiber, Set.eq_univ_iff_forall, Set.mem_setOf_eq]

theorem AllBoundary.iff_eq_univ_boundaryFiber (τ : α → LocalModelKind) :
    AllBoundary τ ↔ boundaryFiber τ = Set.univ := by
  simp [AllBoundary, boundaryFiber, Set.eq_univ_iff_forall]

end Fibers

end ReflectiveFoldObstruction.Invariants.BoundaryType
