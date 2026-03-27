/-
  **Discrete open–compact witness line** (`SPEC_011` Part A).

  Carrier **`ℕ`**: a cheap “chart-count” phase; the primitive step adds **one** witnessed patch
  while the counter stays **strictly below** a fixed budget. This is **not** `@Eq`; it is a
  disciplined one-successor relation gated below `bound`.

  Full chart compactness / smooth geometry stays out of scope per **`SPEC_002`** / workspace
  charter; this is the flagship **discrete** obstruction pattern.
-/

import Mathlib.Logic.Relation

import ReflectiveFoldObstruction.Core.ArchitectureObstruction
import ReflectiveFoldObstruction.Obstruction.Fold
import ReflectiveFoldObstruction.Reachability.InternalOps

universe u

namespace ReflectiveFoldObstruction.Obstruction.OpenCompactWitness

open Relation
open ReflectiveFoldObstruction.Obstruction.Fold
open ReflectiveFoldObstruction.Reachability.InternalOps

/-- Add one witnessed patch, permitted only while still **below** the budget `bound`. -/
def openCompactWitnessStep (bound : ℕ) (a b : ℕ) : Prop :=
  b = a + 1 ∧ a < bound

/-- “Finite-cover witness” — counter within the discrete budget. -/
def WitnessedFinite (bound a : ℕ) : Prop :=
  a ≤ bound

variable {bound : ℕ}

theorem openCompactWitness_step_preserves_WitnessedFinite ⦃a b : ℕ⦄
    (h : openCompactWitnessStep bound a b) (_ : WitnessedFinite bound a) : WitnessedFinite bound b := by
  rcases h with ⟨rfl, hlt⟩
  simp only [WitnessedFinite]
  exact Nat.succ_le_iff.mpr hlt

theorem openCompactWitness_forwardClosed :
    PreservedBy (openCompactWitnessStep bound) (WitnessedFinite bound) := by
  intro a b hab ha
  exact openCompactWitness_step_preserves_WitnessedFinite hab ha

theorem openCompactWitness_fold_obstruction :
    ¬ ReflTransGen (openCompactWitnessStep bound) 0 (bound + 1) :=
  Core.ArchitectureObstruction.architecture_fold_obstruction_of_invariant_mismatch
    openCompactWitness_forwardClosed
    (by simp [WitnessedFinite])
    (by intro h; exact Nat.not_succ_le_self bound h)

end ReflectiveFoldObstruction.Obstruction.OpenCompactWitness
