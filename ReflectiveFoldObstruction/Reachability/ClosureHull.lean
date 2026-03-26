/-
  **Reachability hulls** — points attainable from a seed set along `ReflTransGen`.

  This is the thin set-theoretic hull used before importing heavier `Topology` convergence
  notions.  Idempotence mirrors “saturation = closure” for reflexive transitive closure.

  See `specs/NOTES/PROJECT_VISION.md` — Reachability/ClosureHull.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Logic.Relation

import ReflectiveFoldObstruction.Reachability.InternalOps

universe u

namespace ReflectiveFoldObstruction.Reachability.ClosureHull

open Relation Set

variable {α : Type u} (r : α → α → Prop)

/-- Elements reachable from the seed set `S` along `r⋆` (`ReflTransGen`). -/
def reachableFrom (S : Set α) : Set α :=
  { y | ∃ x ∈ S, ReflTransGen r x y }

@[simp] theorem mem_reachableFrom {S : Set α} {y : α} :
    y ∈ reachableFrom r S ↔ ∃ x ∈ S, ReflTransGen r x y :=
  Iff.rfl

theorem subset_reachableFrom (S : Set α) : S ⊆ reachableFrom r S := by
  intro x hx
  exact ⟨x, hx, ReflTransGen.refl⟩

@[simp]
theorem reachableFrom_empty : reachableFrom r (∅ : Set α) = ∅ := by
  ext y
  constructor
  · rintro ⟨x, hx, _⟩
    exact absurd hx (notMem_empty x)
  · intro hy
    exact False.elim ((mem_empty_iff_false y).1 hy)

theorem reachableFrom_mono {S T : Set α} (h : S ⊆ T) : reachableFrom r S ⊆ reachableFrom r T := by
  rintro y ⟨x, hx, hxy⟩
  exact ⟨x, h hx, hxy⟩

theorem reachableFrom_inter_subset (S T : Set α) :
    reachableFrom r (S ∩ T) ⊆ reachableFrom r S ∩ reachableFrom r T := by
  rintro y ⟨x, ⟨hxS, hxT⟩, hxy⟩
  exact ⟨⟨x, hxS, hxy⟩, ⟨x, hxT, hxy⟩⟩

theorem reachableFrom_union (S T : Set α) :
    reachableFrom r (S ∪ T) = reachableFrom r S ∪ reachableFrom r T := by
  ext y
  simp only [mem_reachableFrom, mem_union]
  constructor
  · rintro ⟨x, hx, hxy⟩
    rcases hx with hxS | hxT
    · left; exact ⟨x, hxS, hxy⟩
    · right; exact ⟨x, hxT, hxy⟩
  · rintro (⟨x, hxS, hxy⟩ | ⟨x, hxT, hxy⟩)
    · exact ⟨x, Or.inl hxS, hxy⟩
    · exact ⟨x, Or.inr hxT, hxy⟩

/-- Saturation is idempotent: reaching twice does not enlarge the hull. -/
theorem reachableFrom_idem (S : Set α) :
    reachableFrom r (reachableFrom r S) = reachableFrom r S := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, hxz⟩, hzy⟩
    exact ⟨x, hx, hxz.trans hzy⟩
  · intro h
    rcases h with ⟨x, hx, hxy⟩
    refine ⟨x, ?_, hxy⟩
    exact subset_reachableFrom r S hx

/-- Reachability from a singleton seed is exactly `ReflTransGen` from that point. -/
theorem mem_reachableFrom_singleton {a y : α} :
    y ∈ reachableFrom r ({a} : Set α) ↔ ReflTransGen r a y := by
  simp only [mem_reachableFrom]
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [mem_singleton_iff] at hx
    subst hx
    exact hxy
  · intro hxy
    exact ⟨a, mem_singleton a, hxy⟩

/--
  Induction on the reachability hull (vision §6 / `Reachability/Invariants` pattern):
  `Q` holds on seeds in `S` and is forward-closed for `r`, hence on all of `reachableFrom r S`.
-/
theorem mem_reachableFrom_induction {S : Set α} {Q : α → Prop}
    (hseed : ∀ x ∈ S, Q x) (hstep : InternalOps.ForwardClosed r Q) ⦃y : α⦄
    (hy : y ∈ reachableFrom r S) : Q y := by
  rcases hy with ⟨x, hxS, hxy⟩
  exact InternalOps.ReflTransGen.forwardClosed hstep hxy (hseed x hxS)

end ReflectiveFoldObstruction.Reachability.ClosureHull
