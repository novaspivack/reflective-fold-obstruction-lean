/-
  **Sort separation** — invariants that survive tagging into `OntologicalSlot`.

  Builds on `Core.Slots`. Intended for reuse from `Transport.lean`: functorial `mapSlot`
  preserves **injectivity** when both branch maps are injective (“closure does not
  collapse” at the level of sort witnesses).

  Module context: Invariants/SortSeparation.
-/

import ReflectiveFoldObstruction.Core.Basic
import ReflectiveFoldObstruction.Core.Slots

universe u

namespace ReflectiveFoldObstruction.Invariants.SortSeparation

open Core Slots

section Generic

variable {Obj Mor Obj' Mor' : Type u}

/-- Functorial action on slots (covariant in both branches). -/
def mapSlot (fObj : Obj → Obj') (fMor : Mor → Mor') : OntologicalSlot Obj Mor → OntologicalSlot Obj' Mor'
  | .obj o => .obj (fObj o)
  | .mor m => .mor (fMor m)

@[simp] theorem mapSlot_obj (fObj : Obj → Obj') (fMor : Mor → Mor') (o : Obj) :
    mapSlot fObj fMor (.obj o) = .obj (fObj o) :=
  rfl

@[simp] theorem mapSlot_mor (fObj : Obj → Obj') (fMor : Mor → Mor') (m : Mor) :
    mapSlot fObj fMor (.mor m) = .mor (fMor m) :=
  rfl

/--
  **Transport core lemma:** injective branch maps induce an injective map on slots.

  This is the main entry point for later equivalence / homeomorphism transport: compose
  `mapSlot` with equalities of `fObj` / `fMor`.
-/
theorem mapSlot_injective {fObj : Obj → Obj'} {fMor : Mor → Mor'}
    (hObj : Function.Injective fObj) (hMor : Function.Injective fMor) :
    Function.Injective (mapSlot fObj fMor) := by
  intro s t h
  cases s <;> cases t <;> simp only [mapSlot] at h
  · exact congr_arg OntologicalSlot.obj (hObj (obj_injective h))
  · cases h
  · cases h
  · exact congr_arg OntologicalSlot.mor (hMor (mor_injective h))

/-- Disjoint branches are preserved by any `mapSlot`. -/
theorem mapSlot_preserves_branch_disjoint (fObj : Obj → Obj') (fMor : Mor → Mor')
    (o : Obj) (m : Mor) :
    mapSlot fObj fMor (.obj o) ≠ mapSlot fObj fMor (.mor m) := by
  intro h
  simp only [mapSlot] at h
  exact absurd h (obj_ne_mor (fObj o) (fMor m))

end Generic

section Reflective

variable (R : Core.ReflectiveSystem)

/-- Distinct tower indices give distinct **morphism** slots once `IterInjective` holds. -/
theorem tower_slots_injective (hij : Core.IterInjective R) ⦃n m : ℕ⦄ (h : n ≠ m) :
    @OntologicalSlot.mor R.C (R.A ⟶ R.A) (Core.metaRegressArrow R n) ≠
      @OntologicalSlot.mor R.C (R.A ⟶ R.A) (Core.metaRegressArrow R m) :=
  reflectiveSlot_tower_preserves_mor R hij h

/-- The self-representation morphism is never in the **object** slot of the `A` tag. -/
theorem represent_slot_disjoint_from_obj_A :
    @OntologicalSlot.mor R.C (R.A ⟶ R.A) R.represent ≠
      @OntologicalSlot.obj R.C (R.A ⟶ R.A) R.A :=
  reflectiveSlot_represent_mor_ne_obj_A R

/-- For any global object `c`, `mor represent` is not `obj c`. -/
theorem represent_mor_ne_obj (c : R.C) :
    @OntologicalSlot.mor R.C (R.A ⟶ R.A) R.represent ≠
      @OntologicalSlot.obj R.C (R.A ⟶ R.A) c :=
  reflectiveSlot_no_mor_is_obj R R.represent c

end Reflective

end ReflectiveFoldObstruction.Invariants.SortSeparation
