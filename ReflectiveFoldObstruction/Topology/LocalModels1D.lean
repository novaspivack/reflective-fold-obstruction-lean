/-
  **One-dimensional local models** — half-line vs full line shapes in \(\mathbb{R}\).

  Compare `Invariants/BoundaryType` tags with these concrete sets when building chart lemmas.

  Module context: Topology/LocalModels1D.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic

namespace ReflectiveFoldObstruction.Topology.LocalModels1D

open Set

/-- Closed half-line \([0,\infty)\). -/
def halfLine : Set ℝ :=
  Ici (0 : ℝ)

/-- Entire line as a maximal chart domain. -/
def fullLine : Set ℝ :=
  univ

theorem zero_mem_halfLine : (0 : ℝ) ∈ halfLine :=
  mem_Ici.mpr le_rfl

theorem halfLine_subset_line : halfLine ⊆ fullLine := fun _ _ => trivial

theorem neg_one_not_mem_halfLine : (-1 : ℝ) ∉ halfLine := by
  dsimp [halfLine]
  rw [mem_Ici]
  norm_num

/-- `[0,∞)` is not the full line: missing a negative witness. -/
theorem halfLine_ne_univ : halfLine ≠ (univ : Set ℝ) := by
  intro h
  have hn := neg_one_not_mem_halfLine
  rw [h] at hn
  simp at hn

end ReflectiveFoldObstruction.Topology.LocalModels1D
