/-
  **Reflective fold obstruction** — **`SPEC_008`** surface over the abstract summit (`Obstruction/Fold`).

  - **Summit reuse:** sort / slot mismatch along `Reachability/ReflectiveSteps.reflectiveSlotStep`.
  - **Iterative channel:** still records **unbounded tower** facts under `IterInjective` (certificates optional).

  See `specs/NOTES/PROJECT_VISION.md` — Obstruction/ReflectiveFold.
-/

import Mathlib.Logic.Relation

import ReflectiveFoldObstruction.Core.Basic
import ReflectiveFoldObstruction.Obstruction.CanonicalInstances
import ReflectiveFoldObstruction.Obstruction.Fold
import ReflectiveFoldObstruction.Reachability.ReflectiveSteps
import ReflectiveFoldObstruction.Reflection.Towers

universe u

namespace ReflectiveFoldObstruction.Obstruction.ReflectiveFold

open Relation
open ReflectiveFoldObstruction.Reachability.ReflectiveSteps

/-- Certificate tagging purely iterative unboundedness (contraposes any “finite witness” fold). -/
def certificateOfIterativeUnbounded (C : Type u) : Fold.ObstructionCertificate C where
  kind := Fold.ObstructionKind.diagonal
  description := "Iterative regression has no global bound under `IterInjective` (`regress_iterates_unbounded`)."

variable (R : Core.ReflectiveSystem)

/-- Under `IterInjective`, tower depth is unbounded — obstruction to any **finite** iterative pipeline. -/
theorem iterative_unbounded (hij : Core.IterInjective R) :
    ∀ n : ℕ, ∃ m : ℕ, n < m ∧ Core.metaRegressArrow R m ≠ Core.metaRegressArrow R n := by
  intro n
  rcases ReflectiveFoldObstruction.Reflection.Towers.regress_iterates_unbounded R hij n with
    ⟨m, hmgt, hmne⟩
  exact ⟨m, hmgt, hmne⟩

/-- **Slot mismatch** cannot be bridged by reflective **internal** steps alone (**fold ≠ iterate**). -/
theorem reflective_fold_obstruction_slot_mismatch :
    ¬ ReflTransGen (reflectiveSlotStep R)
      (Core.Slots.OntologicalSlot.obj R.A) (Core.Slots.OntologicalSlot.mor R.represent) :=
  CanonicalInstances.fold_obstruction_of_sort_separation_mismatch R

/-- Stable flagship name (`SPEC_009`). -/
theorem reflective_architecture_fold_obstruction :
    ¬ ReflTransGen (reflectiveSlotStep R)
      (Core.Slots.OntologicalSlot.obj R.A) (Core.Slots.OntologicalSlot.mor R.represent) :=
  reflective_fold_obstruction_slot_mismatch R

end ReflectiveFoldObstruction.Obstruction.ReflectiveFold
