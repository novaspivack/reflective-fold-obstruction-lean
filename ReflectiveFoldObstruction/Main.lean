/-
  **Master assembly surface** — human-oriented index for shipped layers.

  Consumers should usually `import ReflectiveFoldObstruction` (the package root); this file
  summarizes the spine in one place without creating redundant import cycles.

  | Layer | Role |
  |-------|------|
  | Core / Reflection | Structure + regress |
  | Diagonal | Lawvere pressure |
  | Invariants | Slots, transport, boundary data |
  | Reachability | Reflexive-transitive hull |
  | Obstruction | Certificates + reflective packaging |
  | Topology / Examples | Euclidean anchors + bridges |

  See `specs/NOTES/PROJECT_VISION.md` — Main.
-/

import ReflectiveFoldObstruction.Obstruction.Fold
import ReflectiveFoldObstruction.Obstruction.ReflectiveFold
import ReflectiveFoldObstruction.Reachability.Invariants

namespace ReflectiveFoldObstruction

/-- Marker that the assembly module imported successfully. -/
def assemblySurface : Unit :=
  ()

end ReflectiveFoldObstruction
