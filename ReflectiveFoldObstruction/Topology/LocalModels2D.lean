/-
  **Two-dimensional local models** — closed half-plane vs full plane subsets of \(\mathbb{R}^2\).

  See `specs/NOTES/PROJECT_VISION.md` — Topology/LocalModels2D.
-/

import Mathlib.Data.Real.Basic

namespace ReflectiveFoldObstruction.Topology.LocalModels2D

open Set

/-- Closed upper half-plane \(\{ (x,y) \mid 0 \le y \}\). -/
def closedUpperHalfPlane : Set (ℝ × ℝ) :=
  { p | 0 ≤ p.2 }

/-- Full plane chart domain. -/
def euclideanPlane : Set (ℝ × ℝ) :=
  univ

theorem origin_mem_halfPlane : ((0 : ℝ), (0 : ℝ)) ∈ closedUpperHalfPlane := by
  simp [closedUpperHalfPlane]

theorem halfPlane_subset_plane : closedUpperHalfPlane ⊆ euclideanPlane := fun _ _ => trivial

end ReflectiveFoldObstruction.Topology.LocalModels2D
