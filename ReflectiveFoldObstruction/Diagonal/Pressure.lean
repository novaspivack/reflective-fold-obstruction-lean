/-
  **Diagonal pressure** — packaged consequences of Lawvere for `Type u` in the
  `MonoidalClosed (Type u)` vocabulary.

  Use this module when you need a **single import** for “surjective `curry (lawvereBinary s)`”
  is incompatible with a **fixed-point-free** endomap on the codomain (and the `Nat` special case).

  Proof sources: `LawvereClosed` (`lawvere_universal_iff_surjective_curry`) and
  `LawvereType` (`lawvere_fixed_point_corollary_no_universal`).
-/

import ReflectiveFoldObstruction.Diagonal.LawvereClosed

universe u

namespace ReflectiveFoldObstruction.Diagonal.Pressure

open CategoryTheory MonoidalClosed
open LawvereClosed

/--
  If `B` admits `succ` with **no** fixed points, then `curry (lawvereBinary s)` cannot be
  surjective (`A B : Type u` — the universe needed for `MonoidalClosed (Type u)`).
-/
theorem not_surjective_curry_of_fixed_point_free {A B : Type u} (succ : B → B)
    (hsucc : ∀ b : B, succ b ≠ b) (s : A → A → B)
    (hsurj : Function.Surjective (MonoidalClosed.curry (lawvereBinary s))) :
    False := by
  refine LawvereType.lawvere_fixed_point_corollary_no_universal succ hsucc s ?_
  exact (lawvere_universal_iff_surjective_curry s).2 hsurj

/--
  **`Nat`:** no `s : A → A → Nat` has `curry (lawvereBinary s)` surjective.

  Here `A : Type` (i.e. `Type 0`): `lawvereBinary` for `MonoidalClosed (Type u)` needs
  `B` in the **same** universe as `A`, and `Nat` lives in `Type 0`.
-/
theorem not_surjective_curry_into_nat {A : Type} (s : A → A → Nat)
    (hsurj : Function.Surjective (MonoidalClosed.curry (lawvereBinary s))) :
    False :=
  not_surjective_curry_of_fixed_point_free (B := Nat) Nat.succ Nat.succ_ne_self s hsurj

/--
  **Function formulation:** under `succ` fixed-point-free, there is no enumerating
  `s` with `∀ g, ∃ a, s a = g` (the hypothesis of `LawvereType.lawvere_fixed_point_Type`).
  Contrapositive of `lawvere_fixed_point_corollary_no_universal` as a `¬` lemma.
-/
theorem not_universal_binary_of_fixed_point_free {A B : Type u} (succ : B → B)
    (hsucc : ∀ b : B, succ b ≠ b) (s : A → A → B) :
    ¬(∀ g : A → B, ∃ a : A, s a = g) := fun hU =>
  LawvereType.lawvere_fixed_point_corollary_no_universal succ hsucc s hU

end ReflectiveFoldObstruction.Diagonal.Pressure
