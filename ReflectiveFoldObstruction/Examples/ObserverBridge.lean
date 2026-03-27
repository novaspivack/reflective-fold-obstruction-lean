/-
  **RFO → Observer Exhaustion schematic bridge** (`SPEC_013`).

  Parameterized over a synthetic **route** type `α`, one-step **mechanistic** transition
  `routeStep`, and a preserved **observer-side** invariant `I`. The exported theorem is
  definitionally the abstract fold pattern — the synthesis layer can import this name without
  restating `ReflTransGen` bookkeeping.

  No dependency on any external Observer Exhaustion package.
-/

import Mathlib.Logic.Relation

import ReflectiveFoldObstruction.Obstruction.Fold
import ReflectiveFoldObstruction.Reachability.InternalOps

universe u

namespace ReflectiveFoldObstruction.Examples.ObserverBridge

open Relation
open ReflectiveFoldObstruction.Obstruction.Fold
open ReflectiveFoldObstruction.Reachability.InternalOps

variable {α : Type u} (routeStep : α → α → Prop) (I : α → Prop)

/-- Mechanistic internal routes cannot cross a preserved invariant mismatch (**`SPEC_013`**). -/
theorem mechanistic_observer_route_blocked_by_preserved_mismatch ⦃S T : α⦄ (h : PreservedBy routeStep I)
    (hS : I S) (hT : ¬ I T) : ¬ ReflTransGen routeStep S T :=
  fold_obstruction_of_invariant_mismatch h hS hT

/-- Same fold pattern under stable export naming (**`SPEC_013`**). -/
theorem rfo_fold_pattern_of_preserved_mismatch ⦃S T : α⦄ (h : PreservedBy routeStep I)
    (hS : I S) (hT : ¬ I T) : ¬ ReflTransGen routeStep S T :=
  mechanistic_observer_route_blocked_by_preserved_mismatch routeStep I h hS hT

end ReflectiveFoldObstruction.Examples.ObserverBridge
