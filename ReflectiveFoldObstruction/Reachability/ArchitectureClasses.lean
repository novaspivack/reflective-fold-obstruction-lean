/-
  **Architecture-shaped parameters** (`SPEC_017`) — minimal records for uniform fold/hull statements.

  Reuse sites (no heavy imports here): reflective calculi (`ReflectiveCalculus`), holonomy phase
  (`Topology/HolonomyPhase`), open–compact witness (`Obstruction/OpenCompactWitness`), observer
  routes (`Examples/ObserverBridge`).
-/

import Mathlib.Data.Set.Defs

universe u

namespace ReflectiveFoldObstruction.Reachability.ArchitectureClasses

/-- Carrier + primitive internal step + invariant (`SPEC_017`). -/
structure Architecture (α : Type u) where
  rel : α → α → Prop
  Inv : α → Prop

/-- Adds seed / target for packaged mismatch theorems. -/
structure FoldObstructionBundle (α : Type u) extends Architecture α where
  S : α
  T : α

end ReflectiveFoldObstruction.Reachability.ArchitectureClasses
