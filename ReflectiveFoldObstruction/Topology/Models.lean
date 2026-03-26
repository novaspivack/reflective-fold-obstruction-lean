/-
  **Concrete Euclidean model sets** — charts used in local obstruction stories.

  These are *sets in ℝⁿ*, not yet manifold-with-boundary instances (that stays in Topology/Boundary
  glue + mathlib smooth scaffolding).  Flagship twist geometry refers to these shapes by name.

  See `specs/NOTES/PROJECT_VISION.md` — Topology/Models.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic

universe u

namespace ReflectiveFoldObstruction.Topology.Models

open Set

/-- Closed unit interval \([0,1] \subset \mathbb{R}\). -/
def closedUnitInterval : Set ℝ :=
  Icc (0 : ℝ) 1

/-- Open unit interval \((0,1) \subset \mathbb{R}\). -/
def openUnitInterval : Set ℝ :=
  Ioo (0 : ℝ) 1

/-- Closed unit square \([0,1]^2\). -/
def closedUnitSquare : Set (ℝ × ℝ) :=
  closedUnitInterval ×ˢ closedUnitInterval

@[simp] theorem mem_closedUnitInterval {x : ℝ} : x ∈ closedUnitInterval ↔ 0 ≤ x ∧ x ≤ 1 := by
  simp [closedUnitInterval]

@[simp] theorem mem_openUnitInterval {x : ℝ} : x ∈ openUnitInterval ↔ 0 < x ∧ x < 1 := by
  simp [openUnitInterval]

end ReflectiveFoldObstruction.Topology.Models
