/-
  **Punctured models** — deleted points / infinitesimal circle models at the set level.

  Full “`\(\pi_1 \neq 1\)” or simple-connectivity obstructions need paths and fundamental groups;
  this file only pins the **carrier sets** used in neighborhood arguments.

  See `specs/NOTES/PROJECT_VISION.md` — Topology/PuncturedNeighborhoods.
-/

import Mathlib.Data.Real.Basic

namespace ReflectiveFoldObstruction.Topology.PuncturedNeighborhoods

open Set

/-- The punctured line \(\mathbb{R} \setminus \{0\}\) as a subtype-targeting set. -/
def puncturedReals : Set ℝ :=
  { x | x ≠ 0 }

@[simp] theorem mem_puncturedReals {x : ℝ} : x ∈ puncturedReals ↔ x ≠ 0 := Iff.rfl

theorem zero_notMem_punctured : (0 : ℝ) ∉ puncturedReals := fun h => h rfl

end ReflectiveFoldObstruction.Topology.PuncturedNeighborhoods
