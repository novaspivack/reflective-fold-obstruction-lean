/-
  **Semantic typing / type reachability** — `SPEC_020_H3T`.

  A bundled semantics packages **tags** (semantic types), **instantiation**, and **primitive
  dynamics**. Primitive preservation matches `ForwardClosed` / `PreservedBy` from `SPEC_005`.

  (SPEC prose refers to this data as a `SemanticType`; `Typing` avoids the `SemanticType.SemanticType`
  name duplicate in Lean.)

  
-/

import Mathlib.Logic.Relation

import ReflectiveFoldObstruction.Reachability.InternalOps

universe u v

namespace ReflectiveFoldObstruction.SemanticType

open Relation
open Reachability.InternalOps

/--
A **semantic typing** over `System`: tags classify states; primitive steps must preserve
every tag’s extension (so each tag names a forward-closed predicate).
-/
structure Typing (System : Type u) : Type (max u v + 1) where
  Tag : Type v
  InstantiatesType : System → Tag → Prop
  primitiveStep : System → System → Prop
  typePreservedByStep :
    ∀ ⦃s s' : System⦄ ⦃t : Tag⦄,
      primitiveStep s s' → InstantiatesType s t → InstantiatesType s' t

variable {System : Type u}

/-- Semantic-type **reachability**: some `t`-state connects to some `t'`-state by `ReflTransGen`. -/
def typeReachable (T : Typing System) (t t' : T.Tag) : Prop :=
  ∃ s s' : System,
    T.InstantiatesType s t ∧ T.InstantiatesType s' t' ∧ ReflTransGen T.primitiveStep s s'

/-- A **type gap** / **sort-level mismatch**: `t'` is not reachable from `t` at the typing layer. -/
abbrev typeGap (T : Typing System) (t t' : T.Tag) : Prop :=
  ¬ typeReachable T t t'

/-- Packaged obstruction sentence at the typing layer (`SPEC_020`). -/
structure SemanticTypeObstruction (T : Typing System) (t t' : T.Tag) : Prop where
  gap : typeGap T t t'

/-- Re-label the primitive relation while keeping tags + instantiation (`SPEC_020` extensions). -/
def Typing.withPrimitiveStep (T : Typing System) (r' : System → System → Prop)
    (_hsub : ∀ ⦃s s'⦄, T.primitiveStep s s' → r' s s')
    (hpres :
      ∀ ⦃s s' : System⦄ ⦃t : T.Tag⦄, r' s s' → T.InstantiatesType s t → T.InstantiatesType s' t) :
    Typing System where
  Tag := T.Tag
  InstantiatesType := T.InstantiatesType
  primitiveStep := r'
  typePreservedByStep := hpres

theorem not_reflTransGen_of_typeGap (T : Typing System) {t t' : T.Tag}
    (hgap : typeGap T t t') {s s' : System}
    (hs : T.InstantiatesType s t) (hs' : T.InstantiatesType s' t') :
    ¬ ReflTransGen T.primitiveStep s s' :=
  fun hreach => hgap ⟨s, s', hs, hs', hreach⟩

theorem typeReachable_mono_primitive {T : Typing System} (r' : System → System → Prop)
    (hsub : ∀ ⦃s s'⦄, T.primitiveStep s s' → r' s s')
    (hpres :
      ∀ ⦃s s' : System⦄ ⦃t : T.Tag⦄, r' s s' → T.InstantiatesType s t → T.InstantiatesType s' t)
    {t t'} (h : typeReachable T t t') :
    typeReachable (T.withPrimitiveStep r' hsub hpres) t t' := by
  rcases h with ⟨s, s', ht, ht', hab⟩
  exact ⟨s, s', ht, ht', reflTransGen_mono_of_subrelation hsub hab⟩

theorem typeGap_antitone_primitive {T : Typing System} (r' : System → System → Prop)
    (hsub : ∀ ⦃s s'⦄, T.primitiveStep s s' → r' s s')
    (hpres :
      ∀ ⦃s s' : System⦄ ⦃t : T.Tag⦄, r' s s' → T.InstantiatesType s t → T.InstantiatesType s' t)
    {t t' : T.Tag} (h : typeGap (T.withPrimitiveStep r' hsub hpres) t t') : typeGap T t t' :=
  fun hsmall => h (typeReachable_mono_primitive (T := T) r' hsub hpres hsmall)

end ReflectiveFoldObstruction.SemanticType
