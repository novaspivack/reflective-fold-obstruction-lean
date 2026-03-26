/-
  Categorical **reflective system**: a category, a distinguished object `A`, and a
  self-representation endomorphism `represent`.

  Per `specs/IN-PROCESS/SPEC_003_RFO_LEAN_LAYER_EPICS.md`, **structure** (this file)
  is separated from the **hypothesis** `IterInjective` (distinct iterate powers in
  `End A`). That generalizes the bundled `iter_injective` field of
  `RepresentationalRegress.RepresentationalSystem` without importing that repo.

  Slice packaging and iterates follow the same mathematics as representational regress;
  see `specs/NOTES/PROJECT_VISION.md` §3.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Endomorphism

open CategoryTheory

universe u

namespace ReflectiveFoldObstruction.Core

/-- Minimal data: category, object `A`, endomorphism `represent : A ⟶ A`. -/
structure ReflectiveSystem where
  C : Type u
  categoryData : Category C
  A : C
  represent : A ⟶ A

instance (R : ReflectiveSystem) : Category R.C :=
  R.categoryData

/-- Hypothesis layer: distinct natural-number exponents give distinct powers in `End A`. -/
def IterInjective (R : ReflectiveSystem) : Prop :=
  ∀ ⦃n m : ℕ⦄, n ≠ m → (End.of R.represent) ^ n ≠ (End.of R.represent) ^ m

/-- `represent^n` in the endomorphism monoid. -/
def representIter (R : ReflectiveSystem) (n : ℕ) : End R.A :=
  (End.of R.represent) ^ n

/-- Level `n` as a morphism `A ⟶ A` (iterate of `represent`). -/
def metaRegressArrow (R : ReflectiveSystem) (n : ℕ) : R.A ⟶ R.A :=
  (representIter R n).asHom

/-- Slice `Over A` with structure map `represent^n`. -/
def metaOver (R : ReflectiveSystem) (n : ℕ) : Over R.A :=
  Over.mk (metaRegressArrow R n)

alias metaRepresent := metaRegressArrow

@[simp] theorem representIter_zero (R : ReflectiveSystem) : representIter R 0 = 1 :=
  rfl

theorem representIter_succ (R : ReflectiveSystem) (n : ℕ) :
    representIter R (n + 1) = representIter R n * End.of R.represent := by
  simp [representIter, pow_succ]

theorem metaRegressArrow_zero (R : ReflectiveSystem) : metaRegressArrow R 0 = 𝟙 R.A := by
  simp [metaRegressArrow, representIter, End.one_def]

theorem metaRegressArrow_succ (R : ReflectiveSystem) (n : ℕ) :
    metaRegressArrow R (n + 1) = R.represent ≫ metaRegressArrow R n := by
  simp [metaRegressArrow, representIter_succ, End.mul_def]

theorem metaOver_succ (R : ReflectiveSystem) (n : ℕ) :
    metaOver R (n + 1) = Over.mk (R.represent ≫ metaRegressArrow R n) := by
  simp [metaOver, metaRegressArrow_succ]

theorem Over_mk_inj_parallel (R : ReflectiveSystem) {f g : R.A ⟶ R.A}
    (h : Over.mk f = Over.mk g) : f = g := by
  cases h
  rfl

theorem representIter_injective (R : ReflectiveSystem) (hij : IterInjective R) ⦃n m : ℕ⦄
    (h : n ≠ m) : representIter R n ≠ representIter R m :=
  hij h

theorem metaRegressArrow_injective (R : ReflectiveSystem) (hij : IterInjective R)
    ⦃n m : ℕ⦄ (h : n ≠ m) : metaRegressArrow R n ≠ metaRegressArrow R m := fun he =>
  hij h (End.ext he)

theorem metaOver_injective (R : ReflectiveSystem) (hij : IterInjective R) ⦃n m : ℕ⦄
    (h : n ≠ m) : metaOver R n ≠ metaOver R m := fun he => by
  refine metaRegressArrow_injective R hij h ?_
  simp_rw [metaOver] at he
  exact Over_mk_inj_parallel R he

theorem metaRepresent_injective (R : ReflectiveSystem) (hij : IterInjective R) :
    Function.Injective (metaRepresent R) := fun _ _ h =>
  by_contra fun hne => hij hne (End.ext h)

end ReflectiveFoldObstruction.Core
