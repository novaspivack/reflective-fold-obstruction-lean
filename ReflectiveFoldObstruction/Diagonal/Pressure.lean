/-
  **Diagonal pressure** — packaged consequences of Lawvere for `Type u` in the
  `MonoidalClosed (Type u)` vocabulary.

  Use this module when you need a **single import** for “surjective `curry (lawvereBinary s)`”
  is incompatible with a **fixed-point-free** endomap on the codomain (and the `Nat` special case).

  Proof sources: `LawvereClosed` (`lawvere_universal_iff_surjective_curry`) and
  `LawvereType` (`lawvere_fixed_point_corollary_no_universal`).
-/

import Mathlib.Data.ULift

import ReflectiveFoldObstruction.Diagonal.LawvereClosed

universe u

namespace ReflectiveFoldObstruction.Diagonal.Pressure

open CategoryTheory MonoidalClosed
open LawvereClosed

/-- `Nat.succ` pushed through `ULift.{u}` (enums live in the **same** `Type u` as an arbitrary `A`). -/
def uliftNatSucc : ULift.{u} Nat → ULift.{u} Nat :=
  fun x => ULift.up (Nat.succ x.down)

theorem uliftNat_succ_ne_self (x : ULift.{u} Nat) : uliftNatSucc x ≠ x := by
  intro h
  have heq : Nat.succ x.down = x.down := by
    simpa [uliftNatSucc] using congrArg ULift.down h
  exact absurd heq (Nat.succ_ne_self x.down)

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
  **`ULift Nat` at any universe:** for `A : Type u`, no `s : A → A → ULift.{u} Nat` makes
  `curry (lawvereBinary s)` surjective.  Strengthens `not_surjective_curry_into_nat` beyond
  `A : Type 0` by promoting the codomain (not by changing `A`’s level).
-/
theorem not_surjective_curry_into_uliftNat {A : Type u} (s : A → A → ULift.{u} Nat)
    (hsurj : Function.Surjective (MonoidalClosed.curry (lawvereBinary s))) :
    False :=
  not_surjective_curry_of_fixed_point_free uliftNatSucc uliftNat_succ_ne_self s hsurj

/--
  **Function formulation:** under `succ` fixed-point-free, there is no enumerating
  `s` with `∀ g, ∃ a, s a = g` (the hypothesis of `LawvereType.lawvere_fixed_point_Type`).
  Contrapositive of `lawvere_fixed_point_corollary_no_universal` as a `¬` lemma.
-/
theorem not_universal_binary_of_fixed_point_free {A B : Type u} (succ : B → B)
    (hsucc : ∀ b : B, succ b ≠ b) (s : A → A → B) :
    ¬(∀ g : A → B, ∃ a : A, s a = g) := fun hU =>
  LawvereType.lawvere_fixed_point_corollary_no_universal succ hsucc s hU

/--
  **Enumerator formulation at `ULift Nat`:** no binary `s` lists every `A → ULift.{u} Nat`.
-/
theorem not_universal_binary_into_uliftNat {A : Type u} (s : A → A → ULift.{u} Nat) :
    ¬(∀ g : A → ULift.{u} Nat, ∃ a : A, s a = g) := fun hU =>
  LawvereType.lawvere_fixed_point_corollary_no_universal uliftNatSucc uliftNat_succ_ne_self s hU

end ReflectiveFoldObstruction.Diagonal.Pressure
