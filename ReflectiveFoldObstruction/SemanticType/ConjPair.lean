/-
  **Simultaneous tags** as product-tag typing — conjunction / multi-tag obstruction.

  If either coordinate has a type gap, the pair tag cannot increase along internal dynamics.
-/

import ReflectiveFoldObstruction.SemanticType.Core

universe u v

namespace ReflectiveFoldObstruction.SemanticType

variable {System : Type u}

/-- Pair-tag typing: a state instantiates `(t₁, t₂)` iff it instantiates **both** tags. -/
def conjPairTyping (T : Typing System) : Typing System where
  Tag := T.Tag × T.Tag
  InstantiatesType s := fun p => T.InstantiatesType s p.1 ∧ T.InstantiatesType s p.2
  primitiveStep := T.primitiveStep
  typePreservedByStep := by
    rintro s s' ⟨t₁, t₂⟩ h ⟨ht₁, ht₂⟩
    exact ⟨T.typePreservedByStep h ht₁, T.typePreservedByStep h ht₂⟩

theorem typeReachable_conj_pair {T : Typing System} {t₁ t₂ u₁ u₂ : T.Tag}
    (h : typeReachable (conjPairTyping T) (t₁, t₂) (u₁, u₂)) :
    typeReachable T t₁ u₁ ∧ typeReachable T t₂ u₂ := by
  rcases h with ⟨s, s', ⟨ha₁, ha₂⟩, ⟨hb₁, hb₂⟩, hreach⟩
  exact ⟨⟨s, s', ha₁, hb₁, hreach⟩, ⟨s, s', ha₂, hb₂, hreach⟩⟩

theorem typeGap_of_coord {T : Typing System} {t₁ t₂ u₁ u₂ : T.Tag}
    (h : typeGap T t₁ u₁ ∨ typeGap T t₂ u₂) :
    typeGap (conjPairTyping T) (t₁, t₂) (u₁, u₂) := by
  intro hbad
  rcases typeReachable_conj_pair hbad with ⟨hbad₁, _⟩
  rcases h with h₁ | h₂
  · exact h₁ hbad₁
  · exact h₂ (typeReachable_conj_pair hbad |>.2)

theorem SemanticTypeObstruction_conj_pair {T : Typing System} {t₁ t₂ u₁ u₂ : T.Tag}
    (h : typeGap T t₁ u₁ ∨ typeGap T t₂ u₂) :
    SemanticTypeObstruction (conjPairTyping T) (t₁, t₂) (u₁, u₂) :=
  ⟨typeGap_of_coord h⟩

end ReflectiveFoldObstruction.SemanticType
