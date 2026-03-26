/-
  **Invariant transport** — moving predicates and slot data along equivalences and maps.

  - **`slotEquiv`:** `Obj ≃ Obj'` and `Mor ≃ Mor'` induce `OntologicalSlot Obj Mor ≃ OntologicalSlot Obj' Mor'`
    by functorial `mapSlot` (`SortSeparation`).
  - **Predicate transport:** `pullbackPred` / `transportPred` with inverse laws along `Equiv`.

  **Homeomorphs:** use `Homeomorph.toEquiv` (Mathlib) and reuse `Equiv` lemmas — no parallel API here.

  See `specs/NOTES/PROJECT_VISION.md` — Invariants/Transport.
-/

import Mathlib.Logic.Equiv.Defs

import ReflectiveFoldObstruction.Core.Slots
import ReflectiveFoldObstruction.Invariants.SortSeparation

universe u

namespace ReflectiveFoldObstruction.Invariants.Transport

open Equiv Core.Slots

variable {α β : Type u}

/-- Pull back a predicate on `β` along `f : α → β`. -/
def pullbackPred (f : α → β) (P : β → Prop) : α → Prop :=
  fun a => P (f a)

@[simp] theorem pullbackPred_apply (f : α → β) (P : β → Prop) (a : α) :
    pullbackPred f P a = P (f a) :=
  rfl

/-- Transport a predicate on `α` to `β` using `e : α ≃ β`. -/
def transportPred (e : α ≃ β) (P : α → Prop) : β → Prop :=
  fun b => P (e.symm b)

@[simp] theorem transportPred_apply (e : α ≃ β) (P : α → Prop) (b : β) :
    transportPred e P b = P (e.symm b) :=
  rfl

theorem transportPred_symm_iff (e : α ≃ β) (P : α → Prop) (a : α) :
    transportPred e P (e a) ↔ P a := by
  simp [transportPred]

theorem transportPred_pullback {e : α ≃ β} {P : β → Prop} :
    transportPred e (pullbackPred e P) = P := by
  funext b
  simp [transportPred, pullbackPred, apply_symm_apply]

theorem pullbackPred_transport {e : α ≃ β} {Q : α → Prop} :
    pullbackPred e (transportPred e Q) = Q := by
  funext a
  simp [transportPred, pullbackPred, symm_apply_apply]

section SlotEquiv

variable {Obj Mor Obj' Mor' Obj'' Mor'' : Type u}

/-- Equivalences on carriers induce an equivalence on `OntologicalSlot`. -/
def slotEquiv (eO : Obj ≃ Obj') (eM : Mor ≃ Mor') :
    OntologicalSlot Obj Mor ≃ OntologicalSlot Obj' Mor' where
  toFun := SortSeparation.mapSlot eO eM
  invFun := SortSeparation.mapSlot eO.symm eM.symm
  left_inv s := by
    cases s <;> simp [SortSeparation.mapSlot, symm_apply_apply]
  right_inv s := by
    cases s <;> simp [SortSeparation.mapSlot, apply_symm_apply]

@[simp] theorem slotEquiv_apply_obj (eO : Obj ≃ Obj') (eM : Mor ≃ Mor') (o : Obj) :
    slotEquiv eO eM (OntologicalSlot.obj o) = OntologicalSlot.obj (eO o) :=
  rfl

@[simp] theorem slotEquiv_apply_mor (eO : Obj ≃ Obj') (eM : Mor ≃ Mor') (m : Mor) :
    slotEquiv eO eM (OntologicalSlot.mor m) = OntologicalSlot.mor (eM m) :=
  rfl

/-- `mapSlot` commutes with composition. -/
theorem mapSlot_comp (f₁ : Obj → Obj') (g₁ : Mor → Mor') (f₂ : Obj' → Obj'') (g₂ : Mor' → Mor'') :
    SortSeparation.mapSlot (f₂ ∘ f₁) (g₂ ∘ g₁) =
      SortSeparation.mapSlot f₂ g₂ ∘ SortSeparation.mapSlot f₁ g₁ := by
  funext s
  cases s <;> rfl

/-- Functoriality with respect to `Equiv.trans`. -/
theorem slotEquiv_trans (eO : Obj ≃ Obj') (eO' : Obj' ≃ Obj'') (eM : Mor ≃ Mor') (eM' : Mor' ≃ Mor'') :
    slotEquiv (eO.trans eO') (eM.trans eM') = (slotEquiv eO eM).trans (slotEquiv eO' eM') := by
  refine Equiv.ext ?_
  intro s
  cases s <;> simp [slotEquiv, Equiv.trans, SortSeparation.mapSlot, Function.comp]

end SlotEquiv

end ReflectiveFoldObstruction.Invariants.Transport
