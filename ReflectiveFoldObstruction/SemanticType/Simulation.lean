/-
  **Simulation / pullback typing** (`SPEC_020` extension).

  A **typed primitive simulation** maps `r₁`-steps to **the** primitive relation of a codomain
  `Typing`.  Pulled-back tags inherit forward closure; reachable types in the domain project onto
  the codomain, so **codomain type gaps pull back** to domain gaps.

  A **section** `σ : S₂ → S₁` with `π ∘ σ = id` that **lifts primitive steps backward** is the
  categorical witness that the codomain dynamics is *realised* inside the domain (not merely
  forwarded).  Then **type reachability agrees** between `T₂` and the pullback --- a conditional
  converse to forward simulation.
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

/-- A simulation **with section**: right inverse on states + primitive steps lift from `S₂` to `S₁`.

This is the data needed for a **conditional converse** to `typeReachable_simulation_forward`. -/
structure TypedPrimitiveSimulationSection (T₂ : Typing S₂) (S₁ : Type u)
    extends TypedPrimitiveSimulation T₂ S₁ where
  σ : S₂ → S₁
  section_rightInv : ∀ x, π (σ x) = x
  section_liftsPrimitive : ∀ ⦃x y : S₂⦄, T₂.primitiveStep x y → r₁ (σ x) (σ y)

theorem reflTransGen_section_lift (sec : TypedPrimitiveSimulationSection T₂ S₁) ⦃s s' : S₂⦄
    (h : ReflTransGen T₂.primitiveStep s s') :
    ReflTransGen sec.r₁ (sec.σ s) (sec.σ s') := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ReflTransGen.tail ih (sec.section_liftsPrimitive hbc)

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

theorem typeReachable_simulation_section_backward (sec : TypedPrimitiveSimulationSection T₂ S₁)
    {t t' : T₂.Tag} (h : typeReachable T₂ t t') :
    typeReachable (pullbackAlongSimulation sec.toTypedPrimitiveSimulation) t t' := by
  rcases h with ⟨s, s', ht, ht', hreach⟩
  refine ⟨sec.σ s, sec.σ s', ?_, ?_, ?_⟩
  · simpa [pullbackAlongSimulation, TypedPrimitiveSimulation.mk] using
      show T₂.InstantiatesType (sec.π (sec.σ s)) t by rw [sec.section_rightInv]; exact ht
  · simpa [pullbackAlongSimulation, TypedPrimitiveSimulation.mk] using
      show T₂.InstantiatesType (sec.π (sec.σ s')) t' by rw [sec.section_rightInv]; exact ht'
  · exact reflTransGen_section_lift sec hreach

theorem typeReachable_pullback_iff_of_section (sec : TypedPrimitiveSimulationSection T₂ S₁)
    (t t' : T₂.Tag) :
    typeReachable (pullbackAlongSimulation sec.toTypedPrimitiveSimulation) t t' ↔
      typeReachable T₂ t t' :=
  ⟨typeReachable_simulation_forward sec.toTypedPrimitiveSimulation,
   typeReachable_simulation_section_backward sec⟩

theorem SemanticTypeObstruction_pullback_iff_of_section (sec : TypedPrimitiveSimulationSection T₂ S₁)
    (t t' : T₂.Tag) :
    SemanticTypeObstruction (pullbackAlongSimulation sec.toTypedPrimitiveSimulation) t t' ↔
      SemanticTypeObstruction T₂ t t' := by
  have hrr := typeReachable_pullback_iff_of_section sec t t'
  constructor
  · rintro ⟨hgap⟩; exact ⟨mt (hrr.mpr) hgap⟩
  · rintro ⟨hgap⟩; exact ⟨mt (hrr.mp) hgap⟩

theorem typeGap_simulation_pullback (sim : TypedPrimitiveSimulation T₂ S₁) {t t' : T₂.Tag}
    (h : typeGap T₂ t t') : typeGap (pullbackAlongSimulation sim) t t' :=
  fun hpb => h (typeReachable_simulation_forward sim hpb)

theorem SemanticTypeObstruction_simulation_pullback (sim : TypedPrimitiveSimulation T₂ S₁)
    {t t' : T₂.Tag} (H : SemanticTypeObstruction T₂ t t') :
    SemanticTypeObstruction (pullbackAlongSimulation sim) t t' :=
  ⟨typeGap_simulation_pullback sim H.gap⟩

end ReflectiveFoldObstruction.SemanticType
