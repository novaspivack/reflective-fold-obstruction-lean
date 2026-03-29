/-
  **Scope note:** Rice-style theorems vs semantic type reachability (`SPEC_020`).

  Rice’s theorem talks about **recursive index sets** (non-trivial semantic properties of codes).
  `typeReachable` / `typeGap` quantify over **states** of a fixed dynamics and **tag predicates**
  subject to **forward closure**.  A faithful Rice formalisation would require a model of
  computation + Gödel numbering in Lean; that is **outside** this layer.

  This module exists so the library has an explicit **named checkpoint** for that distinction.
-/

namespace ReflectiveFoldObstruction.SemanticType

def computabilityComparisonNote : String :=
  "RFO semantic-type obstruction is dynamical (PreservedBy + ReflTransGen on states), not " ++
  "a Rice / index-set statement about r.e. degrees of program codes."

end ReflectiveFoldObstruction.SemanticType
