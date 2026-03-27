/-
  **Rich reflective calculus** — extends `ReflectiveSteps.reflectiveSlotStep` by allowing **one**
  mor-branch jump `f ⟶ f ≫ metaRegressArrow R n` for any **`0 < n`**.

  The sort obstruction **`obj R.A` ⇏ `mor R.represent`** survives (**`SPEC_010`**): object slots
  still never see mor-only transitions, and **`IterInjective`** separates **`n = 2`** jumps from
  the minimal **`n = 1`** slot step when exhibiting **strict extension**.

  See `specs/IN-PROCESS/SPEC_010_Q8R_RFO_RICH_REFLECTIVE_INTERNAL_CALCULI.md`.
-/

import Mathlib.CategoryTheory.Category.Basic

import ReflectiveFoldObstruction.Core.ArchitectureObstruction
import ReflectiveFoldObstruction.Core.Basic
import ReflectiveFoldObstruction.Core.Slots
import ReflectiveFoldObstruction.Obstruction.Fold
import ReflectiveFoldObstruction.Reachability.InternalOps
import ReflectiveFoldObstruction.Reachability.ReflectiveSteps

universe u

namespace ReflectiveFoldObstruction.Reachability.ReflectiveCalculus

open CategoryTheory Relation Core Slots
open ReflectiveFoldObstruction.Reachability.InternalOps
open ReflectiveFoldObstruction.Obstruction.Fold

variable (R : Core.ReflectiveSystem)

/-- Mor advancement by **`n`** composed `represent`-iterates (`n ≥ 1`). -/
def morAdvancesTower (n : ℕ) (_ : 0 < n) (f g : R.A ⟶ R.A) : Prop :=
  g = f ≫ Core.metaRegressArrow R n

/-- Strict extension of **`reflectiveSlotStep`**: reflexivity, or a **single** mor jump by any
    positive iterate tower. -/
def reflectiveCalcStep (s t : ReflectiveSlot R) : Prop :=
  s = t ∨
    (∃ n : ℕ, ∃ hn : 0 < n, ∃ f g : R.A ⟶ R.A,
      s = OntologicalSlot.mor f ∧ t = OntologicalSlot.mor g ∧ morAdvancesTower R n hn f g)

theorem reflectiveSlotStep_sub_reflectiveCalcStep ⦃s t : ReflectiveSlot R⦄
    (h : ReflectiveSteps.reflectiveSlotStep R s t) : reflectiveCalcStep R s t := by
  rcases h with rfl | ⟨f, g, hs, ht, hg⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨1, Nat.zero_lt_one, f, g, hs, ht, ?_⟩
    simp [morAdvancesTower, ReflectiveSteps.morAdvances] at hg ⊢
    rw [hg, Core.metaRegressArrow_one R]

theorem reflectiveCalc_step_preserves_sort_separation :
    ForwardClosed (reflectiveCalcStep R) (ReflectiveSteps.IsObjReflectiveSlot R) := by
  rintro s t h ⟨c, hc⟩
  subst hc
  rcases h with rfl | ⟨n, hn, f, g, hs, _, _⟩
  · exact ⟨c, rfl⟩
  · cases hs

theorem reflectiveCalc_reachability_preserves_sort_separation ⦃s t : ReflectiveSlot R⦄
    (hreach : ReflTransGen (reflectiveCalcStep R) s t) (hs : ReflectiveSteps.IsObjReflectiveSlot R s) :
    ReflectiveSteps.IsObjReflectiveSlot R t :=
  ReflTransGen.forwardClosed (reflectiveCalc_step_preserves_sort_separation R) hreach hs

theorem reflectiveCalc_fold_obstruction_slot_mismatch :
    ¬ ReflTransGen (reflectiveCalcStep R) (OntologicalSlot.obj R.A)
      (OntologicalSlot.mor R.represent) :=
  fold_obstruction_of_invariant_mismatch (reflectiveCalc_step_preserves_sort_separation R)
    ⟨R.A, rfl⟩ (ReflectiveSteps.not_IsObjReflectiveSlot_mor_represent R)

/-- Repackages the same non-reachability under the enlarged calculus (**`SPEC_010`** naming). -/
theorem obstruction_persists_under_reflectiveCalc :
    ¬ ReflTransGen (reflectiveCalcStep R) (OntologicalSlot.obj R.A)
      (OntologicalSlot.mor R.represent) :=
  reflectiveCalc_fold_obstruction_slot_mismatch R

/-- **Strict extension** (provably new jumps) assuming injective iterate indices. -/
theorem reflectiveCalc_step_strictly_extends_reflectiveSlotStep (hij : Core.IterInjective R) :
    ∃ s t : ReflectiveSlot R, reflectiveCalcStep R s t ∧ ¬ ReflectiveSteps.reflectiveSlotStep R s t := by
  let s : ReflectiveSlot R := OntologicalSlot.mor (𝟙 R.A)
  let t : ReflectiveSlot R := OntologicalSlot.mor (Core.metaRegressArrow R 2)
  refine ⟨s, t, ?_, ?_⟩
  · exact Or.inr
      ⟨2, Nat.succ_pos 1, 𝟙 R.A, Core.metaRegressArrow R 2, rfl, rfl, by
        simp [morAdvancesTower]⟩
  · intro h
    rcases h with he | ⟨f', g', hs', ht', hg'⟩
    · have hm : 𝟙 R.A = Core.metaRegressArrow R 2 :=
        (Slots.mor_injective (Obj := R.C) (Mor := R.A ⟶ R.A)) he
      rw [← Core.metaRegressArrow_zero R] at hm
      exact (Core.metaRegressArrow_injective R hij (by decide : (0 : ℕ) ≠ 2)) hm
    · have hf' : f' = 𝟙 R.A :=
        (Slots.mor_injective (Obj := R.C) (Mor := R.A ⟶ R.A)) hs'.symm
      have hg'₂ : g' = Core.metaRegressArrow R 2 :=
        (Slots.mor_injective (Obj := R.C) (Mor := R.A ⟶ R.A)) ht'.symm
      subst hf' hg'₂
      simp only [ReflectiveSteps.morAdvances, Category.id_comp] at hg'
      rw [← Core.metaRegressArrow_one R] at hg'
      exact (Core.metaRegressArrow_injective R hij (by decide : (2 : ℕ) ≠ 1)) hg'

end ReflectiveFoldObstruction.Reachability.ReflectiveCalculus
