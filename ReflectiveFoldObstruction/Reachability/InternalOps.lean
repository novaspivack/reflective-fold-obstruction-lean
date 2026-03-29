/-
  **Internal reachability** — one-step transitions and monotone predicates.

  The natural graph closure is `Relation.ReflTransGen`, i.e. reflexive transitive reachability
  along a relation `r : α → α → Prop` (“one internal step” from the vision).

  See `specs/NOTES/PROJECT_VISION.md` — Reachability/InternalOps.
-/

import Mathlib.Logic.Relation

universe u

namespace ReflectiveFoldObstruction.Reachability.InternalOps

open Relation

variable {α : Type u} (r : α → α → Prop)

/-- A predicate is **forward-closed** for `r` if it persists along one positive step. -/
def ForwardClosed {α : Type u} (r : α → α → Prop) (P : α → Prop) : Prop :=
  ∀ ⦃a b : α⦄, r a b → P a → P b

/-- Same notion as `ForwardClosed` — preservation along **primitive** internal steps (`SPEC_005`). -/
abbrev PreservedBy {α : Type u} (r : α → α → Prop) (I : α → Prop) : Prop :=
  ForwardClosed r I

abbrev StepPreservedBy {α : Type u} (r : α → α → Prop) (I : α → Prop) : Prop :=
  PreservedBy r I

/-- Predicate preserved along **`ReflTransGen`** — **hull** / closure preservation. -/
def HullPreservedBy {α : Type u} (r : α → α → Prop) (I : α → Prop) : Prop :=
  ∀ ⦃a b : α⦄, ReflTransGen r a b → I a → I b

variable {P : α → Prop}

/-- Forward-closed predicates survive arbitrary iterated reachability. -/
theorem ReflTransGen.forwardClosed {r : α → α → Prop} {P : α → Prop}
    (h : ForwardClosed r P) ⦃a b : α⦄ (hab : ReflTransGen r a b) : P a → P b := by
  intro ha
  induction hab generalizing ha with
  | refl => exact ha
  | tail _ hbc ih => exact h hbc (ih ha)

theorem ReflTransGen.backward_closed_of_symm {r : α → α → Prop} {P : α → Prop}
    (h : Symmetric r) (hP : ForwardClosed r P) ⦃a b : α⦄ (hab : ReflTransGen r a b) :
    P b → P a := by
  intro hb
  exact ReflTransGen.forwardClosed hP (ReflTransGen.symmetric h hab) hb

variable {r r' : α → α → Prop} {P Q : α → Prop}

theorem hullPreservedBy_iff_forwardClosed : HullPreservedBy r P ↔ ForwardClosed r P :=
  ⟨fun h ⦃_ _⦄ rab => h (ReflTransGen.single rab),
    fun h ⦃_ _⦄ hab => ReflTransGen.forwardClosed h hab⟩

theorem forwardClosed_of_weaker {r r' : α → α → Prop} (hrr : ∀ ⦃x y : α⦄, r' x y → r x y)
    (h : ForwardClosed r P) : ForwardClosed r' P := fun ⦃_ _⦄ hxy => h (hrr hxy)

/-- Every predicate is forward-closed if each `r`-step is already **equality**. -/
theorem forwardClosed_of_step_implies_eq {r : α → α → Prop} (P : α → Prop)
    (h : ∀ ⦃x y : α⦄, r x y → x = y) : ForwardClosed r P := by
  rintro x y hxy hPx
  rcases h hxy with rfl
  exact hPx

theorem reflTransGen_preserves_invariant {r : α → α → Prop} {I : α → Prop} (h : ForwardClosed r I)
    ⦃a b : α⦄ (hab : ReflTransGen r a b) : I a → I b :=
  ReflTransGen.forwardClosed h hab

theorem preserved_conj {r : α → α → Prop} (hP : ForwardClosed r P) (hQ : ForwardClosed r Q) :
    ForwardClosed r (fun x => P x ∧ Q x) := by
  rintro a b hab ⟨haP, haQ⟩
  exact ⟨hP hab haP, hQ hab haQ⟩

theorem PreservedBy.inter {r : α → α → Prop} (hP : ForwardClosed r P) (hQ : ForwardClosed r Q) :
    PreservedBy r (fun x => P x ∧ Q x) :=
  preserved_conj hP hQ

theorem ReflTransGen.eq_of_eq {a b : α} (h : ReflTransGen (@Eq α) a b) : a = b := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl x => rfl
  | single h => exact h
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Monotone reachability:** if every `r`-edge is an `r'`-edge, `r⋆ ⊆ r'⋆`.

Orientation: **`r` smaller / subrelation** → hypothesis `∀ x y, r x y → r' x y`. -/
theorem reflTransGen_mono_of_subrelation {r r' : α → α → Prop}
    (h : ∀ ⦃x y : α⦄, r x y → r' x y) ⦃a b : α⦄ (hab : ReflTransGen r a b) :
    ReflTransGen r' a b :=
  ReflTransGen.mono (fun _ _ hxy => h hxy) hab

/-- Contrapositive: not reachable in the **super**-relation ⇒ not reachable in the **sub**.

Hypothesis `∀ x y, r x y → r' x y` says **`r ⊆ r'` as graphs** (`r'` allows at least every `r`-edge). -/
theorem not_reflTransGen_of_superrelation {r r' : α → α → Prop}
    (h : ∀ ⦃x y : α⦄, r x y → r' x y) ⦃a b : α⦄ (hab' : ¬ ReflTransGen r' a b) :
    ¬ ReflTransGen r a b :=
  fun hab => hab' (reflTransGen_mono_of_subrelation h hab)

alias not_reachable_when_smaller_step_included := not_reflTransGen_of_superrelation

/-- **Homomorphic image** of reachability: a relation homomorphism lifts `r⋆` to `r'⋆`. -/
theorem reflTransGen_map {β : Type u} {r : α → α → Prop} {r' : β → β → Prop} (f : α → β)
    (h : ∀ ⦃x y : α⦄, r x y → r' (f x) (f y)) ⦃a b : α⦄
    (hab : ReflTransGen r a b) : ReflTransGen r' (f a) (f b) := by
  induction hab with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ReflTransGen.tail ih (h hbc)

/-!
## Relation extension (SPEC_015)

Orientation (graph inclusion as **hints**, not `⊆` on `Set (α × α)`):

* **`preserved_under_relation_extension`:** hypothesis `∀ x y, r x y → r' x y` means every **primitive**
  `r`-edge is an `r'`-edge (“`r` is a **subrelation** of `r'`”, `r` has **fewer** edges).
  Then forward-closure on the **larger** `'r'` **restricts** to the **smaller** `r`.

* Contrast `forwardClosed_of_weaker`: there the hypothesis flips — a **weaker** step relation carries
  **fewer** obligations.

Do **not** confuse these directions when chaining with `ReflTransGen.mono`.
-/

/-- If `r'` preserves `I` on one step, so does any **subrelation** `r` (`r ⊆ r'`). -/
theorem preserved_under_relation_extension {r r' : α → α → Prop} {I : α → Prop}
    (hsub : ∀ ⦃x y : α⦄, r x y → r' x y) (h' : ForwardClosed r' I) : ForwardClosed r I :=
  fun ⦃_ _⦄ rab ha => h' (hsub rab) ha


end ReflectiveFoldObstruction.Reachability.InternalOps
