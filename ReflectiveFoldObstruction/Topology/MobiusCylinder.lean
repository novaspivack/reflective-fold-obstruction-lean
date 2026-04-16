/-
  **Cylinder vs Möbius tags** — discrete holonomy classification for examples.

  These tags are *not* commutative with parity gauges from `OrientabilityLike`, but bridge
  narratively: a trivial tag pairs with constant parity gauges in toy models, whereas a
  twist tag pairs with nontrivial parity witnesses when charts are globalized.

  Module context: Topology/MobiusCylinder.
-/

import Mathlib.Logic.Equiv.Defs

namespace ReflectiveFoldObstruction.Topology.MobiusCylinder

/-- Holonomy profile for strip/cylinder examples (`trivial` = orientable product story). -/
inductive HolonomyTag : Type
  | trivial
  | twistOne
  deriving DecidableEq, Repr

theorem holonomyTag_trivial_ne_twist : HolonomyTag.trivial ≠ HolonomyTag.twistOne := by
  intro h
  cases h

/-- Parity transport across the tag-level `Equiv` that swaps the two constructors (abstract). -/
def tagEquiv : HolonomyTag ≃ HolonomyTag where
  toFun
    | .trivial => .twistOne
    | .twistOne => .trivial
  invFun
    | .trivial => .twistOne
    | .twistOne => .trivial
  left_inv := by rintro ⟨⟩ <;> rfl
  right_inv := by rintro ⟨⟩ <;> rfl

end ReflectiveFoldObstruction.Topology.MobiusCylinder
