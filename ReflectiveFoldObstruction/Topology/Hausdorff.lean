/-
  **Separation convenience** — products inherit `T2` (Hausdorff) from factors.

  Used when disjoint separating neighborhoods in chart targets must be lifted through products.

  See `specs/NOTES/PROJECT_VISION.md` — Topology/Hausdorff.
-/

import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Hausdorff

universe u

namespace ReflectiveFoldObstruction.Topology.Hausdorff

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Binary products of Hausdorff spaces are Hausdorff (`mathlib` instance alias). -/
theorem prod_t2space [T2Space X] [T2Space Y] : T2Space (X × Y) :=
  inferInstance

end ReflectiveFoldObstruction.Topology.Hausdorff
