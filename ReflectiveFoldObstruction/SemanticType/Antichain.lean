/-
  **Large families of incomparable semantic tags** (within one typing).

  Pairwise `typeGap` — an **antichain** in the induced preorder on tags.
-/

import ReflectiveFoldObstruction.Reachability.InternalOps
import ReflectiveFoldObstruction.SemanticType.Core
import ReflectiveFoldObstruction.SemanticType.NonTriviality

universe u v

namespace ReflectiveFoldObstruction.SemanticType

open Reachability.InternalOps

variable {System : Type u} {ι : Type v}

/-- Tags `f i` are pairwise unreachable (antichain under type reachability). -/
def PairwiseTypeGap (T : Typing System) (f : ι → T.Tag) : Prop :=
  ∀ ⦃i j : ι⦄, i ≠ j → typeGap T (f i) (f j)

theorem pairwiseTypeGap_depthLabels :
    PairwiseTypeGap depthLabelTyping SemanticTypeClass.selfModelDepth := by
  intro i j hij
  rintro ⟨s, s', h₁, h₂, hreach⟩
  rw [h₁, h₂] at hreach
  have heq : i = j := ReflTransGen.eq_of_eq hreach
  subst heq
  exact hij rfl

theorem typeGap_depthLabels_ne {n m : Nat} (h : n ≠ m) :
    typeGap depthLabelTyping (SemanticTypeClass.selfModelDepth n) (SemanticTypeClass.selfModelDepth m) :=
  pairwiseTypeGap_depthLabels h

end ReflectiveFoldObstruction.SemanticType
