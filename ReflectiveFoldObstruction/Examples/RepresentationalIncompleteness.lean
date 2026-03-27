/-
  Bridge toward **`representational-incompleteness-lean`** without importing that repository.

  **Governance:** `specs/IN-PROCESS/SPEC_002_RFO_TWO_REPOSITORY_GOVERNANCE.md` — do **not** add
  `lake require representational-incompleteness-lean` until SPEC_004 import-timeline step 2.
  Keep RFO **Mathlib-only** until promotion rules and stable interfaces on the RI side are met.

  This file defines the **minimal portable host** this layer tree uses — a `ReflectiveSystem` with
  `IterInjective` — and records consequences any future **RFO ↔ RI** port must preserve.

  (Legacy path name: this module superseded `Examples/RepresentationalRegress.lean` when the
  flagship Lean repo was renamed to **representational-incompleteness-lean**.)

  See `specs/NOTES/PROJECT_VISION.md` — Examples layer.
-/

import ReflectiveFoldObstruction.Core.Basic
import ReflectiveFoldObstruction.Reflection.Towers
import ReflectiveFoldObstruction.Obstruction.Fold
import ReflectiveFoldObstruction.Obstruction.ReflectiveFold

namespace ReflectiveFoldObstruction.Examples.RepresentationalIncompleteness

open ReflectiveFoldObstruction

/-- Working bundle for “architecture supports internal iteration with injective tower”. -/
structure PackagedReflectiveHost where
  system : Core.ReflectiveSystem
  injectiveTower : Core.IterInjective system

/-- Tower ascent is unbounded for every packaged host (internal corollary of `IterInjective`). -/
theorem iterative_unbounded (H : PackagedReflectiveHost) (n : ℕ) :
    ∃ m : ℕ, n < m ∧
      Core.metaRegressArrow H.system m ≠ Core.metaRegressArrow H.system n := by
  rcases Reflection.Towers.regress_iterates_unbounded H.system H.injectiveTower n with ⟨m, hlt, hne⟩
  exact ⟨m, hlt, hne⟩

/-- Same conclusion repackaged via `Obstruction/ReflectiveFold` (one spine, two access paths). -/
theorem iterative_unbounded_obstruction (H : PackagedReflectiveHost) (n : ℕ) :
    ∃ m : ℕ, n < m ∧
      Core.metaRegressArrow H.system m ≠ Core.metaRegressArrow H.system n :=
  Obstruction.ReflectiveFold.iterative_unbounded H.system H.injectiveTower n

/-- A canonical diagonal certificate tagging this host class (metadata). -/
def diagonalCertificate (H : PackagedReflectiveHost) :
    Obstruction.Fold.ObstructionCertificate H.system.C where
  kind := Obstruction.Fold.ObstructionKind.diagonal
  description :=
    "Packaged reflective host: see `iterative_unbounded` / `Reflection.Towers.regress_iterates_unbounded`."

/-- Human-readable blocker for automation: RI `lake require` not yet authorized. -/
def riLakeRequireBlockedNote : String :=
  "SPEC_002 + SPEC_004: `lake require representational-incompleteness-lean` remains off until promotion."

end ReflectiveFoldObstruction.Examples.RepresentationalIncompleteness
