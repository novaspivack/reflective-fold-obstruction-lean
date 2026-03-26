/-
  **Reflective fold obstruction** — links the regressive spine to obstruction certificates.

  Iterative reflection already forbids silent termination under `IterInjective` (`Reflection/Towers`).
  Here we package that fact beside the generic obstruction taxonomy from `Obstruction/Fold`.

  See `specs/NOTES/PROJECT_VISION.md` — Obstruction/ReflectiveFold.
-/

import ReflectiveFoldObstruction.Core.Basic
import ReflectiveFoldObstruction.Obstruction.Fold
import ReflectiveFoldObstruction.Reflection.Towers

universe u

namespace ReflectiveFoldObstruction.Obstruction.ReflectiveFold

/-- Certificate tagging purely iterative unboundedness (contraposes any “finite witness” fold). -/
def certificateOfIterativeUnbounded (C : Type u) : Fold.ObstructionCertificate C where
  kind := Fold.ObstructionKind.diagonal
  description := "Iterative regression has no global bound under `IterInjective` (`regress_iterates_unbounded`)."

variable (R : Core.ReflectiveSystem)

/-- Under `IterInjective`, tower depth is unbounded — a basic internal obstruction to finite pipelines. -/
theorem iterative_unbounded (hij : Core.IterInjective R) :
    ∀ n : ℕ, ∃ m : ℕ, n < m ∧ Core.metaRegressArrow R m ≠ Core.metaRegressArrow R n := by
  intro n
  rcases ReflectiveFoldObstruction.Reflection.Towers.regress_iterates_unbounded R hij n with
    ⟨m, hmgt, hmne⟩
  exact ⟨m, hmgt, hmne⟩

end ReflectiveFoldObstruction.Obstruction.ReflectiveFold
