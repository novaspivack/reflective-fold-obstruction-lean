/-
  **Cylinder / Möbius narrative hook** — relates tag-level data to parity gauges.

  **Flagship (`SPEC_009`):** `mobius_cylinder_fold_obstruction` is an instantiation of the abstract
  **`Obstruction/Fold`** summit (holonomy tag mismatch + equality internal reachability).

  Module context: Examples/CylinderMobius.
-/

import Mathlib.Logic.Relation

import ReflectiveFoldObstruction.Invariants.OrientabilityLike
import ReflectiveFoldObstruction.Obstruction.CanonicalInstances
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

/-- **Example A** — discrete holonomy classes are not equality-reachable across the twist wall. -/
abbrev mobius_cylinder_fold_obstruction :=
  Obstruction.CanonicalInstances.mobius_cylinder_fold_obstruction

end ReflectiveFoldObstruction.Examples.CylinderMobius
