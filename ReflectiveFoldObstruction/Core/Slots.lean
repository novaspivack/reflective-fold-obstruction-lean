/-
  **General** sort-separation tag: objects vs morphisms in arbitrary types `Obj`, `Mor`.

  Instantiating `Obj := R.C` and `Mor := (R.A ⟶ R.A)` recovers the representational-regress
  `OntologicalSlot` pattern without depending on `representational-regress-lean`
  (`specs/IN-PROCESS/SPEC_002_RFO_TWO_REPOSITORY_GOVERNANCE.md`).

  See `specs/NOTES/PROJECT_VISION.md` — Core/Slots.
-/

import ReflectiveFoldObstruction.Core.Basic

universe u

namespace ReflectiveFoldObstruction.Core.Slots

inductive OntologicalSlot (Obj Mor : Type u) : Type u
  | obj : Obj → OntologicalSlot Obj Mor
  | mor : Mor → OntologicalSlot Obj Mor

theorem obj_ne_mor {Obj Mor : Type u} (o : Obj) (m : Mor) :
    OntologicalSlot.obj o ≠ OntologicalSlot.mor m := by
  intro h
  cases h

theorem obj_injective {Obj Mor : Type u} ⦃x y : Obj⦄
    (h : @OntologicalSlot.obj Obj Mor x = @OntologicalSlot.obj Obj Mor y) : x = y := by
  cases h
  rfl

theorem mor_injective {Obj Mor : Type u} :
    Function.Injective (@OntologicalSlot.mor Obj Mor) := by
  intro _ _ h
  cases h
  rfl

/-- Type alias: slots for a reflective system (objects vs `A`-endomorphisms). -/
abbrev ReflectiveSlot (R : Core.ReflectiveSystem) : Type _ :=
  OntologicalSlot R.C (R.A ⟶ R.A)

theorem reflectiveSlot_obj_ne_mor (R : Core.ReflectiveSystem) (c : R.C) (f : R.A ⟶ R.A) :
    OntologicalSlot.obj c ≠ OntologicalSlot.mor f :=
  @obj_ne_mor R.C (R.A ⟶ R.A) c f

theorem reflectiveSlot_tower_preserves_mor (R : Core.ReflectiveSystem) (hij : Core.IterInjective R)
    ⦃n m : ℕ⦄ (h : n ≠ m) :
    @OntologicalSlot.mor R.C (R.A ⟶ R.A) (Core.metaRegressArrow R n) ≠
      @OntologicalSlot.mor R.C (R.A ⟶ R.A) (Core.metaRegressArrow R m) :=
  fun he => Core.metaRegressArrow_injective R hij h (mor_injective he)

theorem reflectiveSlot_no_mor_is_obj (R : Core.ReflectiveSystem) (f : R.A ⟶ R.A) (c : R.C) :
    @OntologicalSlot.mor R.C (R.A ⟶ R.A) f ≠ @OntologicalSlot.obj R.C (R.A ⟶ R.A) c :=
  (@obj_ne_mor R.C (R.A ⟶ R.A) c f).symm

theorem reflectiveSlot_represent_mor_ne_obj_A (R : Core.ReflectiveSystem) :
    @OntologicalSlot.mor R.C (R.A ⟶ R.A) R.represent ≠
      @OntologicalSlot.obj R.C (R.A ⟶ R.A) R.A :=
  (@obj_ne_mor R.C (R.A ⟶ R.A) R.A R.represent).symm

end ReflectiveFoldObstruction.Core.Slots
