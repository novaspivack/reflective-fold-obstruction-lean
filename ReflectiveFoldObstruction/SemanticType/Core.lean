/-
  **Semantic typing / type reachability** — `SPEC_020_H3T`.

  A bundled semantics packages **tags** (semantic types), **instantiation**, and **primitive
  dynamics**. Primitive preservation matches `ForwardClosed` / `PreservedBy` from `SPEC_005`.

  (SPEC prose refers to this data as a `SemanticType`; `Typing` avoids the `SemanticType.SemanticType`
  name duplicate in Lean.)

  See `specs/IN-PROCESS/SPEC_020_H3T_RFO_SEMANTIC_TYPE_OBSTRUCTION.md`.
-/

import Mathlib.Logic.Relation

universe u v

namespace ReflectiveFoldObstruction.SemanticType

open Relation

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

end ReflectiveFoldObstruction.SemanticType
