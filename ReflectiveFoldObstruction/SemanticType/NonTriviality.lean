/-
  **Global non-triviality** of semantic-type reachability (`SPEC_020`).

  Witness: **self-modeling depth** tags on `Nat` with identity dynamics (`SPEC_020` proof sketch).
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Relation

import ReflectiveFoldObstruction.Reachability.InternalOps
import ReflectiveFoldObstruction.SemanticType.Core

namespace ReflectiveFoldObstruction.SemanticType

open Nat Relation
open Reachability.InternalOps

/-- Named class tags for presentation (depth — primary witness family). -/
inductive SemanticTypeClass : Type
  | selfModelDepth (n : Nat)

/-- Canonical bundle: system states are depth labels; primitive steps **do not** change depth. -/
def depthLabelTyping : Typing Nat where
  Tag := SemanticTypeClass
  InstantiatesType
  | s, .selfModelDepth n => s = n
  primitiveStep := Eq
  typePreservedByStep := by
    intro s s' t h ht
    cases t
    rename_i n
    rcases h with rfl
    exact ht

theorem depth_zero_one_typeGap : typeGap depthLabelTyping
    (SemanticTypeClass.selfModelDepth 0) (SemanticTypeClass.selfModelDepth 1) := by
  rintro ⟨s, s', h₁, h₂, hreach⟩
  have hs : s = s' := ReflTransGen.eq_of_eq hreach
  subst h₁
  subst h₂
  exact absurd hs.symm (Nat.succ_ne_self 0)

/-- The semantic-type preorder is **not** total: some pairs are not reachable. -/
theorem semanticType_preorder_nontrivial :
    ∃ T T' : SemanticTypeClass, typeGap depthLabelTyping T T' :=
  ⟨SemanticTypeClass.selfModelDepth 0, SemanticTypeClass.selfModelDepth 1, depth_zero_one_typeGap⟩


end ReflectiveFoldObstruction.SemanticType
