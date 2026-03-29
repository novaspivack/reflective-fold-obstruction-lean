/-
  **Simulation / pullback typing** (`SPEC_020` extension).

  A **typed primitive simulation** maps `r₁`-steps to **the** primitive relation of a codomain
  `Typing`.  Pulled-back tags inherit forward closure; reachable types in the domain project onto
  the codomain, so **codomain type gaps pull back** to domain gaps.
-/

import Mathlib.Logic.Relation

import ReflectiveFoldObstruction.Reachability.InternalOps
import ReflectiveFoldObstruction.SemanticType.Core

universe u

namespace ReflectiveFoldObstruction.SemanticType

open Relation
open Reachability.InternalOps

variable {S₁ S₂ : Type u}

/-- Simulation into the primitive step of a fixed typing on `S₂`. -/
structure TypedPrimitiveSimulation (T₂ : Typing S₂) (S₁ : Type u) where
  r₁ : S₁ → S₁ → Prop
  π : S₁ → S₂
  sim : ∀ ⦃x y : S₁⦄, r₁ x y → T₂.primitiveStep (π x) (π y)

variable {T₂ : Typing S₂}

def pullbackAlongSimulation (sim : TypedPrimitiveSimulation T₂ S₁) : Typing S₁ where
  Tag := T₂.Tag
  InstantiatesType s t := T₂.InstantiatesType (sim.π s) t
  primitiveStep := sim.r₁
  typePreservedByStep := fun _ _ _ h hs => T₂.typePreservedByStep (sim.sim h) hs

theorem typeReachable_simulation_forward (sim : TypedPrimitiveSimulation T₂ S₁) {t t' : T₂.Tag}
    (h : typeReachable (pullbackAlongSimulation sim) t t') : typeReachable T₂ t t' := by
  rcases h with ⟨s, s', ht, ht', hreach⟩
  refine ⟨sim.π s, sim.π s', ht, ht', ?_⟩
  exact reflTransGen_map sim.π (fun _ _ hxy => sim.sim hxy) hreach

theorem typeGap_simulation_pullback (sim : TypedPrimitiveSimulation T₂ S₁) {t t' : T₂.Tag}
    (h : typeGap T₂ t t') : typeGap (pullbackAlongSimulation sim) t t' :=
  fun hpb => h (typeReachable_simulation_forward sim hpb)

theorem SemanticTypeObstruction_simulation_pullback (sim : TypedPrimitiveSimulation T₂ S₁)
    {t t' : T₂.Tag} (H : SemanticTypeObstruction T₂ t t') :
    SemanticTypeObstruction (pullbackAlongSimulation sim) t t' :=
  ⟨typeGap_simulation_pullback sim H.gap⟩

end ReflectiveFoldObstruction.SemanticType
