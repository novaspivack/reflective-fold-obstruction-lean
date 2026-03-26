/-
  Lawvere's fixed-point theorem — **`Type` instantiation**.

  Same mathematical content as classical Lawvere (1969) / Mathlib-facing `Type` proofs:
  weak point-surjectivity of `s : A → A → B` (`∀ g : A → B, ∃ a, s a = g`) forces every
  `f : B → B` to have a fixed point; hence no such universal `s` when `B` has a
  fixed-point-free endomap (e.g. `Nat.succ`).

  This file is **independent** of `representational-regress-lean` (`SPEC_002`).

  For **`MonoidalClosed (Type u)`** packaging (`curry` / tensor), see `LawvereClosed.lean`.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Basic

universe u v

namespace ReflectiveFoldObstruction.Diagonal.LawvereType

/--
  **Lawvere fixed-point (Type).**

  If every `g : A → B` is `s a` for some `a : A`, then every `f : B → B` has a fixed point.

  Proof: `k a := f (s a a)`, choose `a₀` with `s a₀ = k`, then
  `s a₀ a₀ = k a₀ = f (s a₀ a₀)`.
-/
theorem lawvere_fixed_point_Type {A : Type u} {B : Type v} (f : B → B) (s : A → A → B)
    (hs : ∀ g : A → B, ∃ a : A, s a = g) :
    ∃ b : B, f b = b := by
  let k : A → B := fun a => f (s a a)
  obtain ⟨a₀, ha₀⟩ := hs k
  refine ⟨s a₀ a₀, ?_⟩
  simpa [k] using (congr_fun ha₀ a₀).symm

/--
  **Corollary:** no `s : A → A → B` can list all unary `A → B` if `B` has a fixed-point-free
  endomap `succ`.
-/
theorem lawvere_fixed_point_corollary_no_universal {A : Type u} {B : Type v} (succ : B → B)
    (hsucc : ∀ b : B, succ b ≠ b) (s : A → A → B)
    (hU : ∀ g : A → B, ∃ a : A, s a = g) : False := by
  obtain ⟨b, hb⟩ := lawvere_fixed_point_Type succ s hU
  exact hsucc b hb

/--
  **Instantiated corollary** for `B = Nat` and `Nat.succ`: no `s : A → A → Nat` enumerates
  every `A → Nat`.

  Shorthand for `lawvere_fixed_point_corollary_no_universal` at `B = Nat`.
-/
theorem lawvere_no_universal_unary_into_nat (A : Type u) (s : A → A → Nat)
    (hU : ∀ g : A → Nat, ∃ a : A, s a = g) : False :=
  lawvere_fixed_point_corollary_no_universal Nat.succ Nat.succ_ne_self s hU

end ReflectiveFoldObstruction.Diagonal.LawvereType
