/-
  **Homeomorph transport** — reap `Equiv` invariant lemmas via `Homeomorph.toEquiv`.

  `BoundaryType`, `OrientabilityLike`, and `ConnectedBoundary` are purposefully largely
  `TopologicalSpace`-free; this module is the **intended glue** once charts carry genuine
  topology: every `X ≃ₜ Y` induces the same set-theoretic images and typing transports as the
  underlying equivalence.

  Module context: Invariants/Transport (“homeomorphism” bullet).
-/

import Mathlib.Topology.Homeomorph.Defs

import ReflectiveFoldObstruction.Invariants.BoundaryType
import ReflectiveFoldObstruction.Invariants.ConnectedBoundary
import ReflectiveFoldObstruction.Invariants.OrientabilityLike

universe u

namespace ReflectiveFoldObstruction.Invariants.HomeomorphTransport

open Set

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-! ## Boundary typing -/

@[simp] theorem transportTyping_homeomorph_apply (h : X ≃ₜ Y) (τ : X → BoundaryType.LocalModelKind)
    (y : Y) :
    BoundaryType.transportTyping h.toEquiv τ y = τ (h.symm y) :=
  rfl

theorem BoundaryType.ExistsBoundaryPoint.iff_homeomorph (h : X ≃ₜ Y)
    (τ : X → BoundaryType.LocalModelKind) :
    BoundaryType.ExistsBoundaryPoint τ ↔
      BoundaryType.ExistsBoundaryPoint (BoundaryType.transportTyping h.toEquiv τ) :=
  BoundaryType.ExistsBoundaryPoint.iff_transport h.toEquiv τ

theorem BoundaryType.AllInterior.iff_homeomorph (h : X ≃ₜ Y) (τ : X → BoundaryType.LocalModelKind) :
    BoundaryType.AllInterior τ ↔
      BoundaryType.AllInterior (BoundaryType.transportTyping h.toEquiv τ) :=
  BoundaryType.AllInterior.iff_transport h.toEquiv τ

/-! ## Parity gauges -/

theorem OrientabilityLike.IsLocallyConstant.iff_homeomorph (h : X ≃ₜ Y) (p : OrientabilityLike.ParityGauge X) :
    OrientabilityLike.IsLocallyConstant p ↔
      OrientabilityLike.IsLocallyConstant (OrientabilityLike.transportGauge h.toEquiv p) :=
  OrientabilityLike.IsLocallyConstant.transport_iff h.toEquiv p

theorem OrientabilityLike.HasTwistWitness.iff_homeomorph (h : X ≃ₜ Y) (p : OrientabilityLike.ParityGauge X) :
    OrientabilityLike.HasTwistWitness p ↔
      OrientabilityLike.HasTwistWitness (OrientabilityLike.transportGauge h.toEquiv p) :=
  OrientabilityLike.HasTwistWitness.transport_iff h.toEquiv p

/-! ## Relative boundary separation -/

theorem ConnectedBoundary.HasRelBoundarySep.iff_image_homeomorph (h : X ≃ₜ Y) (B : Set X) :
    ConnectedBoundary.HasRelBoundarySep B ↔
      ConnectedBoundary.HasRelBoundarySep (h '' B) := by
  simpa using ConnectedBoundary.HasRelBoundarySep.iff_image_equiv h.toEquiv B

theorem ConnectedBoundary.IsRelBoundaryConnected.iff_image_homeomorph (h : X ≃ₜ Y) (B : Set X) :
    ConnectedBoundary.IsRelBoundaryConnected B ↔
      ConnectedBoundary.IsRelBoundaryConnected (h '' B) := by
  simpa using ConnectedBoundary.IsRelBoundaryConnected.iff_image_equiv h.toEquiv B

end ReflectiveFoldObstruction.Invariants.HomeomorphTransport
