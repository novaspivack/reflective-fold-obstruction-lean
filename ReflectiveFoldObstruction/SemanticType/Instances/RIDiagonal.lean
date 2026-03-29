/-
  **Instance 3 — RI / sort mismatch on reflective slots** (`SPEC_020`).

  Tags: **parametric self** (object branch) vs **morphism-carrier** slot (any `mor f`).
  `reflectiveSlotStep` preserves both, yet no object-tagged state reaches a morphism-carrier
  state — the RI diagonal witness `mor R.represent` lives in the morphism-carrier tag.

  This file depends only on RFO core + reachability (no `representational-incompleteness` import).
-/

import Mathlib.Logic.Relation

import ReflectiveFoldObstruction.Core.Basic
import ReflectiveFoldObstruction.Core.Slots
import ReflectiveFoldObstruction.SemanticType.Core
import ReflectiveFoldObstruction.Reachability.ReflectiveSteps

universe u

namespace ReflectiveFoldObstruction.SemanticType.Instances.RIDiagonal

open CategoryTheory Relation
open Core Core.Slots
open Reachability.ReflectiveSteps

variable {R : Core.ReflectiveSystem.{u}}

inductive RISemanticTag : Type
  /-- Parametric / **obj-branch** self-representation (`SPEC_020` wording). -/
  | parametricSelf
  /-- Some endomorphism tag on the **mor** branch (includes the diagonal witness `represent`). -/
  | morCarrier

/-- Predicate: `s` lies on the morphism branch. -/
def IsMorReflectiveSlot (s : ReflectiveSlot R) : Prop :=
  ∃ f : R.A ⟶ R.A, s = .mor f

theorem reflective_step_preserves_morCarrier :
    Reachability.InternalOps.ForwardClosed (reflectiveSlotStep R) IsMorReflectiveSlot := by
  rintro s t h ⟨f, hf⟩
  rcases h with rfl | ⟨_, g, _, ht', _⟩
  · exact ⟨f, hf⟩
  · exact ⟨g, ht'⟩

def riSemanticTyping (R : Core.ReflectiveSystem.{u}) : Typing (ReflectiveSlot R) where
  Tag := RISemanticTag
  InstantiatesType
  | s, .parametricSelf => IsObjReflectiveSlot R s
  | s, .morCarrier => IsMorReflectiveSlot s
  primitiveStep := reflectiveSlotStep R
  typePreservedByStep := by
    intro s s' t hstep ht
    cases t
    · exact reflective_step_preserves_sort_separation R hstep ht
    · exact reflective_step_preserves_morCarrier hstep ht

theorem RI_carrier_typeGap {R : Core.ReflectiveSystem.{u}} :
    typeGap (riSemanticTyping R) .parametricSelf .morCarrier := by
  rintro ⟨s, s', hp, hm, hreach⟩
  rcases hm with ⟨f, hf⟩
  have hs' : IsObjReflectiveSlot R s' :=
    reflective_reachable_preserves_sort_separation R hreach hp
  rcases hs' with ⟨c, hc⟩
  rw [hc] at hf
  exact absurd hf (obj_ne_mor c f)

/-- Packaged semantic obstruction — morphism-carrier tag (hence also the `represent` diagonal witness). -/
theorem RI_semantic_type_mismatch (R : Core.ReflectiveSystem.{u}) :
    SemanticTypeObstruction (riSemanticTyping R)
      RISemanticTag.parametricSelf RISemanticTag.morCarrier :=
  ⟨RI_carrier_typeGap (R := R)⟩

/-- Same content as reflective sort-separation / fold mismatch on one `obj` seed. -/
theorem RI_slot_fold_obstruction {R : Core.ReflectiveSystem.{u}} (c : R.C) :
    ¬ Relation.ReflTransGen (reflectiveSlotStep R)
      (.obj c) (.mor R.represent) := by
  intro hbad
  have : typeReachable (riSemanticTyping R) .parametricSelf .morCarrier :=
    ⟨.obj c, .mor R.represent, ⟨c, rfl⟩, ⟨R.represent, rfl⟩, hbad⟩
  exact RI_carrier_typeGap this

end ReflectiveFoldObstruction.SemanticType.Instances.RIDiagonal
