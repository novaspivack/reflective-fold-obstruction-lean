/-
  **Canonical invariant mismatch corollaries** — all factor through `Obstruction/Fold` (`SPEC_007`).

  Each lemma fixes a standard predicate on an existing **RFO** type family and instantiates
  `fold_obstruction_of_invariant_mismatch` with the reflexive **equality** step relation
  (identity-only internal navigation).  Richer step relations ship in **`Reachability/ReflectiveSteps`**.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation

import ReflectiveFoldObstruction.Core.Basic
import ReflectiveFoldObstruction.Core.Slots
import ReflectiveFoldObstruction.Invariants.BoundaryType
import ReflectiveFoldObstruction.Invariants.ConnectedBoundary
import ReflectiveFoldObstruction.Invariants.OrientabilityLike
import ReflectiveFoldObstruction.Obstruction.Fold
import ReflectiveFoldObstruction.Reachability.InternalOps
import ReflectiveFoldObstruction.Reachability.ReflectiveSteps
import ReflectiveFoldObstruction.Topology.MobiusCylinder

universe u

namespace ReflectiveFoldObstruction.Obstruction.CanonicalInstances

open Relation
open ReflectiveFoldObstruction.Invariants.BoundaryType
open ReflectiveFoldObstruction.Invariants.ConnectedBoundary
open ReflectiveFoldObstruction.Invariants.OrientabilityLike
open ReflectiveFoldObstruction.Reachability.InternalOps
open ReflectiveFoldObstruction.Reachability.ReflectiveSteps
open ReflectiveFoldObstruction.Topology.MobiusCylinder

variable {α : Type u}

/-- Typings are compared as bare functions; **internal reachability** is logical equality. -/
theorem forwardClosed_AllInterior :
    ForwardClosed (@Eq (α → LocalModelKind)) AllInterior := by
  rintro τ₁ τ₂ hτ hAll
  subst hτ
  exact hAll

theorem fold_obstruction_of_boundary_type_mismatch (τ₁ τ₂ : α → LocalModelKind)
    (h₁ : AllInterior τ₁) (h₂ : ¬ AllInterior τ₂) :
    ¬ ReflTransGen (@Eq (α → LocalModelKind)) τ₁ τ₂ :=
  Fold.fold_obstruction_of_invariant_mismatch forwardClosed_AllInterior h₁ h₂

theorem forwardClosed_IsRelBoundaryConnected :
    ForwardClosed (@Eq (Set α)) IsRelBoundaryConnected := by
  rintro B₁ B₂ hB hConn
  subst hB
  exact hConn

theorem fold_obstruction_of_connected_boundary_mismatch (B₁ B₂ : Set α)
    (h₁ : IsRelBoundaryConnected B₁)
    (h₂ : ¬ IsRelBoundaryConnected B₂) :
    ¬ ReflTransGen (@Eq (Set α)) B₁ B₂ :=
  Fold.fold_obstruction_of_invariant_mismatch forwardClosed_IsRelBoundaryConnected h₁ h₂

theorem forwardClosed_parity_false (p : ParityGauge α) :
    ForwardClosed (@Eq α) (fun z => p z = false) := by
  rintro x y rfl hPx
  exact hPx

theorem fold_obstruction_of_orientability_mismatch (p : ParityGauge α) (x y : α)
    (hx : p x = false) (hy : p y = true) : ¬ ReflTransGen (@Eq α) x y :=
  Fold.fold_obstruction_of_invariant_mismatch (forwardClosed_parity_false p) hx (by
    intro hPy
    exact (Bool.false_ne_true : false ≠ true) (hPy.symm.trans hy))

/-- Homeomorph-compatible phrasing: same lemma as `fold_obstruction_of_boundary_type_mismatch`
    (see `Invariants/HomeomorphTransport` for equivariance of `AllInterior`). -/
theorem fold_obstruction_of_homeomorph_invariant_mismatch (τ₁ τ₂ : α → LocalModelKind)
    (h₁ : AllInterior τ₁) (h₂ : ¬ AllInterior τ₂) :
    ¬ ReflTransGen (@Eq (α → LocalModelKind)) τ₁ τ₂ :=
  fold_obstruction_of_boundary_type_mismatch τ₁ τ₂ h₁ h₂

def isTrivialHolonomy (t : HolonomyTag) : Prop :=
  t = HolonomyTag.trivial

theorem forwardClosed_isTrivialHolonomy :
    ForwardClosed (@Eq HolonomyTag) isTrivialHolonomy := by
  rintro t₁ t₂ rfl ht
  exact ht

theorem mobius_cylinder_fold_obstruction :
    ¬ ReflTransGen (@Eq HolonomyTag) HolonomyTag.trivial HolonomyTag.twistOne :=
  Fold.fold_obstruction_of_invariant_mismatch forwardClosed_isTrivialHolonomy rfl (by
    intro h
    exact holonomyTag_trivial_ne_twist h.symm)

theorem fold_obstruction_of_sort_separation_mismatch (R : Core.ReflectiveSystem) :
    ¬ ReflTransGen (reflectiveSlotStep R) (Core.Slots.OntologicalSlot.obj R.A)
      (Core.Slots.OntologicalSlot.mor R.represent) :=
  Fold.fold_obstruction_of_invariant_mismatch (reflective_step_preserves_sort_separation R)
    ⟨R.A, rfl⟩ (not_IsObjReflectiveSlot_mor_represent R)

end ReflectiveFoldObstruction.Obstruction.CanonicalInstances
