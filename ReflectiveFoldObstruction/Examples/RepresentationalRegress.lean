/-
  Bridge toward the **representational-regress** corpus without importing that repository.

  **Governance:** `specs/IN-PROCESS/SPEC_002_RFO_TWO_REPOSITORY_GOVERNANCE.md` — do **not** add
  `lake require representational-regress-lean` until SPEC_004 import-timeline step 2. The RR
  Lean repo is still finishing a full green `lake build`; keep this dependency off until both
  governance and build health are satisfied.

  This file defines the **minimal portable host** our layer tree actually uses — a
  `ReflectiveSystem` together with `IterInjective` — and records proved consequences that any
  future RR-to-RFO port must preserve.

  See `specs/NOTES/PROJECT_VISION.md` — Examples/RepresentationalRegress.
-/

import ReflectiveFoldObstruction.Core.Basic
import ReflectiveFoldObstruction.Reflection.Towers
import ReflectiveFoldObstruction.Obstruction.Fold
import ReflectiveFoldObstruction.Obstruction.ReflectiveFold

namespace ReflectiveFoldObstruction.Examples.RepresentationalRegress

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

/-- Human-readable blocker for automation: dependency not yet authorized. -/
def rrLakeRequireBlockedNote : String :=
  "SPEC_002 + SPEC_004: `lake require representational-regress-lean` remains off until promotion."

end ReflectiveFoldObstruction.Examples.RepresentationalRegress
