/-
  **Corner / product-with-boundary models** — Euclidean anchors for boundary gluing.

  Cells such as `Models.closedUnitSquare` serve as concrete stratified domains for half-plane
  charts and edge identifications (delegate isomorphisms to `Mathlib` homeomorphisms later).

  Module context: Topology/Boundary.
-/

import ReflectiveFoldObstruction.Topology.Models

namespace ReflectiveFoldObstruction.Topology.Boundary

open Set

/-- Product chart with corner data (the unit square — edges form a stratified boundary story). -/
def corneredUnitSquare : Set (ℝ × ℝ) :=
  Models.closedUnitSquare

theorem corneredUnitSquare_eq : corneredUnitSquare = Models.closedUnitSquare :=
  rfl

end ReflectiveFoldObstruction.Topology.Boundary
