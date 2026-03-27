/-
  **Lawvere ↔ cartesian closed `Type u`.**

  The diagonal theorem in `LawvereType.lean` is stated in ordinary function language.
  Here we package the same hypothesis using **`MonoidalClosed (Type u)`**: internal hom,
  `curry`, and evaluation via Mathlib’s closed monoidal API for types.

  Still **`Type u`** (not an abstract CCC). Matches the vocabulary in
  `Mathlib.CategoryTheory.Monoidal.Closed.Types`.

  General `C` with `[MonoidalClosed C]` + global elements is future work (see **RI** / legacy notes
  in the original `LawvereCCCType.lean`).

  **Dependency:** `ReflectiveFoldObstruction.Diagonal.LawvereType` — not `representational-incompleteness-lean`.
-/

import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Monoidal.Types.Basic

import ReflectiveFoldObstruction.Diagonal.LawvereType

universe u

namespace ReflectiveFoldObstruction.Diagonal.LawvereClosed

open CategoryTheory MonoidalCategory MonoidalClosed

variable {A B : Type u}

/--
  Binary morphism `A ⊗ A ⟶ B` from `s : A → A → B`, with tensor on `(a₁, a₂)` using
  `s a₂ a₁` so that `curry` yields `(curry f) i = s i` under Mathlib’s convention
  `(curry f) y = fun a' => f (a', y)`.
-/
def lawvereBinary (s : A → A → B) : (A ⊗ A) ⟶ B :=
  fun p : A × A => s p.2 p.1

lemma lawvereBinary_apply (s : A → A → B) (a₁ a₂ : A) :
    lawvereBinary s (a₁, a₂) = s a₂ a₁ :=
  rfl

theorem uncurry_eq_lawvereBinary (s : A → A → B) :
    uncurry (s : A ⟶ (A ⟶[Type u] B)) = lawvereBinary s := by
  funext p
  rcases p with ⟨x, i⟩
  simp [uncurry_eq, types_tensorObj_def, lawvereBinary]
  rfl

theorem curry_lawvereBinary (s : A → A → B) : curry (lawvereBinary s) = s := by
  rw [← uncurry_eq_lawvereBinary s, curry_uncurry]

/-- Pointwise universal enumerator `∀ g, ∃ a, s a = g` ↔ surjectivity of `curry (lawvereBinary s)`. -/
theorem lawvere_universal_iff_surjective_curry (s : A → A → B) :
    (∀ g : A → B, ∃ a : A, s a = g) ↔ Function.Surjective (curry (lawvereBinary s)) := by
  constructor
  · intro H k
    obtain ⟨a, ha⟩ := H k
    refine ⟨a, ?_⟩
    rw [curry_lawvereBinary, ha]
  · intro hsurj g
    obtain ⟨a, ha⟩ := hsurj g
    refine ⟨a, ?_⟩
    rw [← curry_lawvereBinary s, ha]

/--
  **Lawvere fixed point (Type u), hypothesis as surjective `curry`.**

  Same mathematics as `LawvereType.lawvere_fixed_point_Type` at identical universes
  `A B : Type u` (single `u` matches `MonoidalClosed (Type u)` here).
-/
theorem lawvere_fixed_point_MonoidalClosedType {A B : Type u} (f : B → B) (s : A → A → B)
    (hsurj : Function.Surjective (MonoidalClosed.curry (lawvereBinary s))) :
    ∃ b : B, f b = b :=
  LawvereType.lawvere_fixed_point_Type f s ((lawvere_universal_iff_surjective_curry s).1 hsurj)

end ReflectiveFoldObstruction.Diagonal.LawvereClosed
