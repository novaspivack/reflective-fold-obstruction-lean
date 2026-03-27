/-
  **Generated internal calculi** — union of primitive generator families + preservation transfer
  (`SPEC_016`).

  One-step relation: **`unionGen r`**, i.e. `∃ i, r i x y`. Reachability is **`ReflTransGen (unionGen r)`**.

  Reflective **two-generator** packaging splits the rich reflective calculus into slot steps vs **proper**
  tower jumps (`n > 1`), yielding the same sort obstruction at the generated level.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Logic.Relation

import ReflectiveFoldObstruction.Core.Basic
import ReflectiveFoldObstruction.Core.Slots
import ReflectiveFoldObstruction.Obstruction.Fold
import ReflectiveFoldObstruction.Reachability.InternalOps
import ReflectiveFoldObstruction.Reachability.ReflectiveSteps

universe u

namespace ReflectiveFoldObstruction.Reachability.GeneratedCalculi

open CategoryTheory Core Relation Slots
open ReflectiveFoldObstruction.Reachability.InternalOps
open ReflectiveFoldObstruction.Obstruction.Fold

variable {α : Type u}

/-- Disjoint union of an indexed primitive family — the **combined one-step** relation (`SPEC_016`). -/
def unionGen {ι : Type u} (r : ι → α → α → Prop) : α → α → Prop :=
  fun x y => ∃ i, r i x y

/-- Preservation transfers from each generator to the union (`SPEC_016`). -/
theorem forwardClosed_unionGen {ι : Type u} (r : ι → α → α → Prop) {I : α → Prop}
    (h : ∀ i, ForwardClosed (r i) I) : ForwardClosed (unionGen r) I := by
  rintro x y ⟨i, hi⟩ hIx
  exact h i hi hIx

alias generated_calculus_preserves_invariant := forwardClosed_unionGen

/-- Fold obstruction packaged at the **generated** primitive (`SPEC_016`). -/
theorem generated_calculus_fold_obstruction {ι : Type u} (r : ι → α → α → Prop) {I : α → Prop}
    (h : ∀ i, PreservedBy (r i) I) {S T : α} (hS : I S) (hT : ¬ I T) :
    ¬ ReflTransGen (unionGen r) S T :=
  fold_obstruction_of_invariant_mismatch (forwardClosed_unionGen r h) hS hT

/-- Union-of-generators: one preservation proof suffices for the mismatch obstruction (`SPEC_015` + `SPEC_016`). -/
theorem obstruction_persists_for_generated_calculus {ι : Type u} (r : ι → α → α → Prop) {I : α → Prop}
    (h : ∀ i, PreservedBy (r i) I) {S T : α} (hS : I S) (hT : ¬ I T) :
    ¬ ReflTransGen (unionGen r) S T :=
  generated_calculus_fold_obstruction r h hS hT

variable (R : ReflectiveSystem)

/-- Proper tower jumps: **`n > 1`** mor advancement (no reflexivity disjunct). -/
def reflectiveProperTowerStep (s t : ReflectiveSlot R) : Prop :=
  ∃ n : ℕ, ∃ hn : 1 < n, ∃ f g : R.A ⟶ R.A,
    s = OntologicalSlot.mor f ∧ t = OntologicalSlot.mor g ∧
      ReflectiveSteps.morAdvancesTower R n (Nat.lt_trans Nat.zero_lt_one hn) f g

/-- `Bool`-indexed reflective generators: slot calculus vs proper towers (`SPEC_016`). -/
def reflectiveBoolGen : Bool → ReflectiveSlot R → ReflectiveSlot R → Prop
  | true => ReflectiveSteps.reflectiveSlotStep R
  | false => reflectiveProperTowerStep R

theorem forwardClosed_reflectiveProperTower :
    ForwardClosed (reflectiveProperTowerStep R) (ReflectiveSteps.IsObjReflectiveSlot R) := by
  rintro s t ht ⟨c, hc⟩
  subst hc
  rcases ht with ⟨_, _, f, g, hs, _, _⟩
  cases hs

theorem forwardClosed_reflectiveBoolGen (b : Bool) :
    ForwardClosed (reflectiveBoolGen R b) (ReflectiveSteps.IsObjReflectiveSlot R) := by
  cases b
  · exact forwardClosed_reflectiveProperTower R
  · exact ReflectiveSteps.reflective_step_preserves_sort_separation R

theorem reflective_generator_family_preserves_sort_separation (b : Bool) :
    ForwardClosed (reflectiveBoolGen R b) (ReflectiveSteps.IsObjReflectiveSlot R) :=
  forwardClosed_reflectiveBoolGen R b

/-- **`reflectiveCalcStep`-shaped** one-step ⇒ **`unionGen (reflectiveBoolGen R)`** (inclusion on primitives).

Supplied as a disjunction to avoid importing `ReflectiveCalculus` here (prevents cycles). -/
theorem unionBoolGen_of_calcShape ⦃s t : ReflectiveSlot R⦄
    (hc : s = t ∨
        (∃ n : ℕ, ∃ hn : 0 < n, ∃ f g : R.A ⟶ R.A,
          s = OntologicalSlot.mor f ∧ t = OntologicalSlot.mor g ∧
            ReflectiveSteps.morAdvancesTower R n hn f g)) :
    unionGen (reflectiveBoolGen R) s t := by
  rcases hc with rfl | ⟨n, hn, f, g, hs, ht, hg⟩
  · exact ⟨true, Or.inl rfl⟩
  · by_cases hn1 : n = 1
    · subst hn1
      refine ⟨true, Or.inr ⟨f, g, hs, ht, ?_⟩⟩
      simp [ReflectiveSteps.morAdvances, ReflectiveSteps.morAdvancesTower, Core.metaRegressArrow_one] at hg ⊢
      exact hg
    · have h1n : 1 < n := by
        rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn) with ⟨m, hm⟩
        subst hm
        cases m with
        | zero => exact (hn1 rfl).elim
        | succ m' => exact Nat.succ_lt_succ (Nat.succ_pos m')
      exact ⟨false, ⟨n, h1n, f, g, hs, ht, hg⟩⟩

theorem reflective_unionBoolGen_fold_obstruction :
    ¬ ReflTransGen (unionGen (reflectiveBoolGen R)) (OntologicalSlot.obj R.A) (OntologicalSlot.mor R.represent) :=
  generated_calculus_fold_obstruction (reflectiveBoolGen R) (forwardClosed_reflectiveBoolGen R)
    ⟨R.A, rfl⟩ (ReflectiveSteps.not_IsObjReflectiveSlot_mor_represent R)

end ReflectiveFoldObstruction.Reachability.GeneratedCalculi
