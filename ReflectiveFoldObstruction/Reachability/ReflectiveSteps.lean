/-
  **Reflective internal steps** — a canonical primitive relation on `ReflectiveSlot`.

  Mor-only advancement composes one more copy of `represent`; object slots can only idle
  (equality).  This is the **`SPEC_008`** hook for “internal reachability” on reflective
  hosts without importing **RI** generically here.

  See `specs/IN-PROCESS/SPEC_008_T9U_RFO_REFLECTIVE_HOST_REACHABILITY_AND_RI_BRIDGE.md`.
-/

import Mathlib.CategoryTheory.Category.Basic

import ReflectiveFoldObstruction.Core.Basic
import ReflectiveFoldObstruction.Core.Slots
import ReflectiveFoldObstruction.Reachability.InternalOps

universe u

namespace ReflectiveFoldObstruction.Reachability.ReflectiveSteps

open CategoryTheory Core Slots
open ReflectiveFoldObstruction.Reachability.InternalOps

variable (R : Core.ReflectiveSystem)

/-- One-step morphism advancement along `represent`. -/
def morAdvances (f g : R.A ⟶ R.A) : Prop :=
  g = f ≫ R.represent

/-- Primitive internal step: reflexivity, or mor-branch composition with `represent`. -/
def reflectiveSlotStep (s t : ReflectiveSlot R) : Prop :=
  s = t ∨ (∃ f g : R.A ⟶ R.A, s = OntologicalSlot.mor f ∧ t = OntologicalSlot.mor g ∧ morAdvances R f g)

/-- **Object-branch** predicate: some `obj` tag. -/
def IsObjReflectiveSlot (s : ReflectiveSlot R) : Prop :=
  ∃ c : R.C, s = OntologicalSlot.obj c

theorem reflective_step_preserves_sort_separation :
    ForwardClosed (reflectiveSlotStep R) (IsObjReflectiveSlot R) := by
  rintro s t h ⟨c, hc⟩
  subst hc
  rcases h with rfl | ⟨f, g, hs, _, _⟩
  · exact ⟨c, rfl⟩
  · cases hs

/-- Same lemma; naming aligned with older “object branch” wording (`SPEC_008`). -/
theorem reflective_step_preserves_objBranch :
    ForwardClosed (reflectiveSlotStep R) (IsObjReflectiveSlot R) :=
  reflective_step_preserves_sort_separation R

/-- The represent mor tag is **not** on the object branch. -/
theorem not_IsObjReflectiveSlot_mor_represent :
    ¬ IsObjReflectiveSlot R (OntologicalSlot.mor R.represent) := by
  rintro ⟨c, hc⟩
  exact (obj_ne_mor c R.represent) (Eq.symm hc)

theorem reflective_reachable_preserves_sort_separation ⦃s t : ReflectiveSlot R⦄
    (hreach : Relation.ReflTransGen (reflectiveSlotStep R) s t) (hs : IsObjReflectiveSlot R s) :
    IsObjReflectiveSlot R t :=
  ReflTransGen.forwardClosed (reflective_step_preserves_sort_separation R) hreach hs

end ReflectiveFoldObstruction.Reachability.ReflectiveSteps
