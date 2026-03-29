/-
  **Complementary tags / one-sided hull facts** (`SPEC_020` extension).

  If `τ_lo` classifies `P` and `τ_hi` classifies `¬ P`, then **forward-closure of `P` alone**
  forbids typed reachability `τ_lo → τ_hi` --- no global `Typing` obligation for `¬ P` to be
  step-closed.

  This separates the **reachable hull from `P`-seeds** (which stays in `P`) from any tag that
  classifies `¬ P`.
-/

import Mathlib.Logic.Relation

import ReflectiveFoldObstruction.Reachability.InternalOps
import ReflectiveFoldObstruction.SemanticType.Core

universe u v

namespace ReflectiveFoldObstruction.SemanticType

open Relation
open Reachability.InternalOps

variable {System : Type u}

/-- Convenient alias: “complementary-tag reach” is just `typeReachable` at two distinguished tags. -/
abbrev complementaryTagReach (T : Typing System) (τ τ' : T.Tag) : Prop :=
  typeReachable T τ τ'

theorem typeGap_of_complementary_tags {T : Typing System} {τ_lo τ_hi : T.Tag}
    {P : System → Prop}
    (hlo : ∀ s, T.InstantiatesType s τ_lo ↔ P s)
    (hhi : ∀ s, T.InstantiatesType s τ_hi ↔ ¬ P s)
    (hP : ForwardClosed T.primitiveStep P) :
    typeGap T τ_lo τ_hi := by
  rintro ⟨s, s', hts, hts', hres⟩
  have hPs : P s := (hlo s).1 hts
  have hnP : ¬ P s' := (hhi s').1 hts'
  exact hnP (ReflTransGen.forwardClosed hP hres hPs)

theorem SemanticTypeObstruction_of_complementary_tags {T : Typing System} {τ_lo τ_hi : T.Tag}
    {P : System → Prop}
    (hlo : ∀ s, T.InstantiatesType s τ_lo ↔ P s)
    (hhi : ∀ s, T.InstantiatesType s τ_hi ↔ ¬ P s)
    (hP : ForwardClosed T.primitiveStep P) :
    SemanticTypeObstruction T τ_lo τ_hi :=
  ⟨typeGap_of_complementary_tags hlo hhi hP⟩

end ReflectiveFoldObstruction.SemanticType
