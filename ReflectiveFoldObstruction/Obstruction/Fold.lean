/-
  **Abstract fold / architecture-change obstructions** — **summit theorems** + certificate taxonomy.

  - **Summit (`SPEC_005`):** invariant **preservation** along internal reachability ⇒ **fold
    obstruction** when source and target fall on opposite sides of an invariant.
  - **Certificates:** lightweight metadata for tracing only (`ObstructionKind`, `ObstructionCertificate`).

  Module context: Obstruction/Fold.
-/

import Mathlib.Logic.Relation

import ReflectiveFoldObstruction.Reachability.ClosureHull
import ReflectiveFoldObstruction.Reachability.InternalOps

universe u

namespace ReflectiveFoldObstruction.Obstruction.Fold

open Set Relation
open ReflectiveFoldObstruction.Reachability.ClosureHull
open ReflectiveFoldObstruction.Reachability.InternalOps

variable {α : Type u} {r : α → α → Prop} {I : α → Prop}

/-- Program-level obstruction tags (expand as the layer graph stabilizes). -/
inductive ObstructionKind : Type
  /- Diagonal / Lawvere-family certificate. -/
  | diagonal
  /- Chart compactness vs openness mismatch. -/
  | openCompact
  /- Boundary / connectivity / holonomy certificate. -/
  | boundaryTopology
  deriving DecidableEq, Repr

/-- Witness that some `ObstructionKind` is active at a type-level parameter (metadata only). -/
structure ObstructionCertificate (α : Type u) where
  kind : ObstructionKind
  /-- Payload for human-facing text / tracing (not mathematical content). -/
  description : String := ""

variable {r : α → α → Prop} {I : α → Prop}

/-- **Primitive-step** preservation — `SPEC_005` spelling of `ForwardClosed`. -/
abbrev PreservedInvariantStep : Prop := PreservedBy r I

/-- **`ReflTransGen`** lifts primitive preservation to the closure (`SPEC_005` / `SPEC_006`). -/
theorem internal_reachability_preserves_invariant (h : PreservedBy r I) ⦃a b : α⦄
    (hab : ReflTransGen r a b) : I a → I b :=
  reflTransGen_preserves_invariant h hab

/-- **Master theorem (pairwise reachability):** mismatch \(\Rightarrow\) not internally reachable. -/
theorem fold_obstruction_of_invariant_mismatch (h : PreservedBy r I) {S T : α}
    (hS : I S) (hT : ¬ I T) : ¬ ReflTransGen r S T := fun hreach =>
  hT (internal_reachability_preserves_invariant h hreach hS)

/-- Alias — same content as `fold_obstruction_of_invariant_mismatch`. -/
theorem not_reachable_of_preserved_and_mismatch (h : PreservedBy r I) {S T : α}
    (hS : I S) (hT : ¬ I T) : ¬ ReflTransGen r S T :=
  fold_obstruction_of_invariant_mismatch h hS hT

/-- **Hull form:** a forward-closed invariant holding on every seed holds on the whole hull. -/
theorem reachableFrom_hull_preserves_invariant {S₀ : Set α} (h : PreservedBy r I)
    (h₀ : ∀ s ∈ S₀, I s) ⦃x : α⦄ (hx : x ∈ reachableFrom r S₀) : I x :=
  mem_reachableFrom_induction r h₀ h hx

theorem preserved_seed_mem_reachableFrom {S₀ : Set α} (h : PreservedBy r I)
    (h₀ : ∀ s ∈ S₀, I s) ⦃x : α⦄ (hx : x ∈ reachableFrom r S₀) : I x :=
  reachableFrom_hull_preserves_invariant h h₀ hx

/-- Hull mismatch: if `T` fails `I`, it cannot lie in the hull of an `I`-seed (under preservation). -/
theorem not_mem_reachableFrom_of_preserved_invariant_mismatch {S₀ : Set α} {T : α}
    (h : PreservedBy r I) (h₀ : ∀ s ∈ S₀, I s) (hT : ¬ I T) :
    T ∉ reachableFrom r S₀ :=
  not_mem_reachableFrom_of_preserved_mismatch r h h₀ hT

/-- Packaged fold witness (`SPEC_005` optional surface). -/
structure FoldObstruction {α : Type u} (r : α → α → Prop) (I : α → Prop) (S T : α) : Prop where
  preserved : PreservedBy r I
  source_inv : I S
  target_not : ¬ I T

theorem FoldObstruction.not_reachable {α : Type u} {r : α → α → Prop} {I : α → Prop} {S T : α}
    (F : FoldObstruction r I S T) : ¬ ReflTransGen r S T :=
  fold_obstruction_of_invariant_mismatch F.preserved F.source_inv F.target_not

abbrev foldObstruction_of_preservedInvariant {α : Type u} {r : α → α → Prop} {I : α → Prop}
    {S T : α} (h : PreservedBy r I) (hS : I S) (hT : ¬ I T) : FoldObstruction r I S T :=
  ⟨h, hS, hT⟩

/-!
## Persistence under relation extension (`SPEC_015`)

If the **larger** primitive relation `r'` preserves `I`, so does the **subrelation** `r`
(`r`-edges ⊆ `r'`-edges). The fold obstruction for `r` follows without a second induction.
-/

/-- Fold mismatch obstruction for a **subrelation** once preservation is known for an **extension** (`SPEC_015`). -/
theorem fold_obstruction_persists_under_relation_extension {r r' : α → α → Prop} {I : α → Prop}
    (hsub : ∀ ⦃x y : α⦄, r x y → r' x y) (h' : PreservedBy r' I) {S T : α} (hS : I S) (hT : ¬ I T) :
    ¬ ReflTransGen r S T :=
  fold_obstruction_of_invariant_mismatch (preserved_under_relation_extension hsub h') hS hT

/-- Seed-hull exclusion for the **small** relation from preservation on the **large** one (`SPEC_015`). -/
theorem hull_exclusion_persists_under_relation_extension {r r' : α → α → Prop} {I : α → Prop}
    (hsub : ∀ ⦃x y : α⦄, r x y → r' x y) (h' : PreservedBy r' I) {S₀ : Set α} (h₀ : ∀ s ∈ S₀, I s) {T : α}
    (hT : ¬ I T) : T ∉ reachableFrom r S₀ :=
  hull_nonmembership_persists_under_relation_extension hsub
    (not_mem_reachableFrom_of_preserved_invariant_mismatch h' h₀ hT)

alias hull_nonmembership_persists_under_relation_extension :=
  hull_exclusion_persists_under_relation_extension

end ReflectiveFoldObstruction.Obstruction.Fold
