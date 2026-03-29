/-
  **Tags realised on a primitive hull** — `SPEC_020` corollary API.

  Collect which semantic tags appear somewhere on `reachableFrom` from a seed set.
-/

import Mathlib.Data.Set.Defs

import ReflectiveFoldObstruction.Reachability.ClosureHull
import ReflectiveFoldObstruction.Reachability.InternalOps
import ReflectiveFoldObstruction.SemanticType.Core

universe u v

namespace ReflectiveFoldObstruction.SemanticType

open Set
open Reachability.ClosureHull
open Reachability.InternalOps

variable {System : Type u}

/-- All tags instantiated at some state in the hull of `S₀` along `T.primitiveStep`. -/
def tagsOnHull (T : Typing System) (S₀ : Set System) : Set T.Tag :=
  { τ | ∃ x, x ∈ reachableFrom T.primitiveStep S₀ ∧ T.InstantiatesType x τ }

theorem mem_tagsOnHull_iff {T : Typing System} {S₀ : Set System} {τ : T.Tag} :
    τ ∈ tagsOnHull T S₀ ↔
      ∃ x, x ∈ reachableFrom T.primitiveStep S₀ ∧ T.InstantiatesType x τ :=
  Iff.rfl

theorem tagsOnHull_mono_seed {T : Typing System} {S₀ S₁ : Set System} (h : S₀ ⊆ S₁) :
    tagsOnHull T S₀ ⊆ tagsOnHull T S₁ := by
  rintro τ ⟨x, hx, ht⟩
  exact ⟨x, reachableFrom_mono T.primitiveStep h hx, ht⟩

theorem tag_mem_hull_of_seed_instantiates {T : Typing System} {S₀ : Set System} {τ : T.Tag}
    ⦃s : System⦄ (hs : s ∈ S₀) (ht : T.InstantiatesType s τ) : τ ∈ tagsOnHull T S₀ :=
  ⟨s, subset_reachableFrom T.primitiveStep S₀ hs, ht⟩

/--
If `τ_false` classifies `¬ P`, seeds lie in `P`, and `P` is forward-closed along primitive steps,
then **`τ_false` never appears on the hull** from `S₀` --- a *seed-local* obstruction without any
global `¬ P` preservation hypothesis.
-/
theorem false_tag_not_mem_tagsOnHull_of_preserved_seed {T : Typing System} {S₀ : Set System}
    {τ_false : T.Tag} {P : System → Prop}
    (hfalse : ∀ s, T.InstantiatesType s τ_false ↔ ¬ P s)
    (hseed : ∀ x ∈ S₀, P x)
    (hP : ForwardClosed T.primitiveStep P) :
    τ_false ∉ tagsOnHull T S₀ := by
  rintro ⟨x, hx, htx⟩
  have hnPx : ¬ P x := (hfalse x).1 htx
  exact hnPx (mem_reachableFrom_induction T.primitiveStep hseed hP hx)

end ReflectiveFoldObstruction.SemanticType
