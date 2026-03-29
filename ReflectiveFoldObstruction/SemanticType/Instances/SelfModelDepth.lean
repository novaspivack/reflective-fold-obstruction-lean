/-
  **Instance 1 — self-modeling depth** (`SPEC_020`).

  Independent dynamics + an **exact depth** predicate; primitive steps preserve depth.
  Advancing `n ↦ n+1` is then a fold obstruction by `fold_obstruction_of_invariant_mismatch`.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Relation

import ReflectiveFoldObstruction.Obstruction.Fold
import ReflectiveFoldObstruction.Reachability.InternalOps
import ReflectiveFoldObstruction.SemanticType.Core

universe u

namespace ReflectiveFoldObstruction.SemanticType.Instances.SelfModelDepth

open Nat Relation
open Reachability.InternalOps
open Obstruction.Fold

variable {α : Type u}

/-- Data for depth-classified systems: exact depth + dynamics + coherence axioms. -/
structure SelfModelDepthDynamics (α : Type u) where
  ExactDepth : α → Nat → Prop
  primitiveStep : α → α → Prop
  depth_unique : ∀ ⦃x n m⦄, ExactDepth x n → ExactDepth x m → n = m
  step_preserves_depth :
    ∀ ⦃s s' n⦄, primitiveStep s s' → ExactDepth s n → ExactDepth s' n

variable (D : SelfModelDepthDynamics α)

/-- Tag = `Nat` reads **exact self-modeling depth**. -/
def toTyping : Typing α where
  Tag := Nat
  InstantiatesType := D.ExactDepth
  primitiveStep := D.primitiveStep
  typePreservedByStep := D.step_preserves_depth

theorem selfModelDepth_typePreserved (n : Nat) :
    PreservedBy D.primitiveStep (fun x => D.ExactDepth x n) :=
  fun _ _ hstep => D.step_preserves_depth hstep

theorem exactDepth_at_succ_not_at_pred {x : α} {n : Nat}
    (hx : D.ExactDepth x (n + 1)) : ¬ D.ExactDepth x n := by
  intro hn
  exact absurd (D.depth_unique hx hn) (Nat.succ_ne_self n)

theorem selfModelDepth_obstruction (n : Nat) (s s' : α) (hs : D.ExactDepth s n)
    (hs' : D.ExactDepth s' (n + 1)) :
    ¬ ReflTransGen D.primitiveStep s s' :=
  fold_obstruction_of_invariant_mismatch (selfModelDepth_typePreserved D n) hs
    (exactDepth_at_succ_not_at_pred D hs')

theorem selfModelDepth_typeGap (n : Nat) :
    typeGap (toTyping D) n (n + 1) := by
  rintro ⟨s, s', hs, hs', hreach⟩
  exact selfModelDepth_obstruction D n s s' hs hs' hreach

theorem selfModelDepth_semantic_obstruction (n : Nat) :
    SemanticTypeObstruction (toTyping D) n (n + 1) :=
  ⟨selfModelDepth_typeGap D n⟩

end ReflectiveFoldObstruction.SemanticType.Instances.SelfModelDepth
