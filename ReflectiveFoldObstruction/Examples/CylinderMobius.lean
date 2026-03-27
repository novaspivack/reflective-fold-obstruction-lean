/-
  **Cylinder / Möbius narrative hook** — relates tag-level data to parity gauges.

  Full quotient models arrive with SPEC_004 promotion from `representational-incompleteness-lean`;
  here we only combine `Topology/MobiusCylinder` with `OrientabilityLike`.

  See `specs/NOTES/PROJECT_VISION.md` — Examples/CylinderMobius.
-/

import ReflectiveFoldObstruction.Invariants.OrientabilityLike
import ReflectiveFoldObstruction.Topology.MobiusCylinder

namespace ReflectiveFoldObstruction.Examples.CylinderMobius

open Invariants.OrientabilityLike Topology.MobiusCylinder

/-- Map a holonomy tag to the `Bool` gauge that is `false` on the trivial sheet, `true` on twist. -/
def parityOfHolonomy : HolonomyTag → Bool
  | .trivial => false
  | .twistOne => true

theorem parity_reflects_twist (t : HolonomyTag) :
    parityOfHolonomy t = true ↔ t = HolonomyTag.twistOne := by
  cases t <;> simp [parityOfHolonomy]

end ReflectiveFoldObstruction.Examples.CylinderMobius
