/-
  **Internal reachability** — one-step transitions and monotone predicates.

  The natural graph closure is `Relation.ReflTransGen`, i.e. reflexive transitive reachability
  along a relation `r : α → α → Prop` (“one internal step” from the vision).

  See `specs/NOTES/PROJECT_VISION.md` — Reachability/InternalOps.
-/

import Mathlib.Logic.Relation

universe u

namespace ReflectiveFoldObstruction.Reachability.InternalOps

open Relation

variable {α : Type u} (r : α → α → Prop)

/-- A predicate is **forward-closed** for `r` if it persists along one positive step. -/
def ForwardClosed {α : Type u} (r : α → α → Prop) (P : α → Prop) : Prop :=
  ∀ ⦃a b : α⦄, r a b → P a → P b

variable {P : α → Prop}

/-- Forward-closed predicates survive arbitrary iterated reachability. -/
theorem ReflTransGen.forwardClosed {r : α → α → Prop} {P : α → Prop}
    (h : ForwardClosed r P) ⦃a b : α⦄ (hab : ReflTransGen r a b) : P a → P b := by
  intro ha
  induction hab generalizing ha with
  | refl => exact ha
  | tail _ hbc ih => exact h hbc (ih ha)

theorem ReflTransGen.backward_closed_of_symm {r : α → α → Prop} {P : α → Prop}
    (h : Symmetric r) (hP : ForwardClosed r P) ⦃a b : α⦄ (hab : ReflTransGen r a b) :
    P b → P a := by
  intro hb
  exact ReflTransGen.forwardClosed hP (ReflTransGen.symmetric h hab) hb

end ReflectiveFoldObstruction.Reachability.InternalOps
