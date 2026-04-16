/-
  **RFO ↔ RI bridge** after **`SPEC_004`** import timeline **step 2**.

  `lake require «representational-incompleteness»` is **active** (see `lakefile.lean` pin).
  Flagship **`RepresentationalIncompleteness.RepresentationalSystem`** maps into RFO’s split
  **`Core.ReflectiveSystem`** + **`Core.IterInjective`** so **`PackagedReflectiveHost`**
  and obstruction certificates apply to **RI** hosts unchanged.

  

  Module context: Examples layer.
-/

import Mathlib.Logic.Relation

import RepresentationalIncompleteness.Basic
import ReflectiveFoldObstruction.Core.Basic
import ReflectiveFoldObstruction.Core.Slots
import ReflectiveFoldObstruction.Reflection.Towers
import ReflectiveFoldObstruction.Obstruction.Fold
import ReflectiveFoldObstruction.Obstruction.ReflectiveFold
import ReflectiveFoldObstruction.Reachability.ReflectiveSteps
import ReflectiveFoldObstruction.SemanticType.Instances.RIDiagonal

universe u

namespace ReflectiveFoldObstruction.Examples.RepresentationalIncompleteness

open Relation
open ReflectiveFoldObstruction
open ReflectiveFoldObstruction.Reachability.ReflectiveSteps
open ReflectiveFoldObstruction.SemanticType

/-- Working bundle for “architecture supports internal iteration with injective tower”. -/
structure PackagedReflectiveHost where
  system : Core.ReflectiveSystem.{u}
  injectiveTower : Core.IterInjective system

/-- Tower ascent is unbounded for every packaged host (internal corollary of `IterInjective`). -/
theorem iterative_unbounded (H : PackagedReflectiveHost) (n : ℕ) :
    ∃ m : ℕ, n < m ∧
      Core.metaRegressArrow H.system m ≠ Core.metaRegressArrow H.system n := by
  rcases Reflection.Towers.regress_iterates_unbounded H.system H.injectiveTower n with ⟨m, hlt, hne⟩
  exact ⟨m, hlt, hne⟩

/-- Same conclusion repackaged via `Obstruction/ReflectiveFold` (one spine, two access paths). -/
theorem iterative_unbounded_obstruction (H : PackagedReflectiveHost) (n : ℕ) :
    ∃ m : ℕ, n < m ∧
      Core.metaRegressArrow H.system m ≠ Core.metaRegressArrow H.system n :=
  Obstruction.ReflectiveFold.iterative_unbounded H.system H.injectiveTower n

/-- A canonical diagonal certificate tagging this host class (metadata). -/
def diagonalCertificate (H : PackagedReflectiveHost) :
    Obstruction.Fold.ObstructionCertificate H.system.C where
  kind := Obstruction.Fold.ObstructionKind.diagonal
  description :=
    "Packaged reflective host: see `iterative_unbounded` / `Reflection.Towers.regress_iterates_unbounded`."

/-- View an **RI** `RepresentationalSystem` as RFO `ReflectiveSystem` (data only). -/
def toReflectiveSystem (R : RepresentationalSystem) : Core.ReflectiveSystem where
  C := R.C
  categoryData := R.categoryData
  A := R.A
  represent := R.represent

theorem toReflectiveSystem_iterInjective (R : RepresentationalSystem) :
    Core.IterInjective (toReflectiveSystem R) := by
  intro n m hnm
  simpa [Core.IterInjective, toReflectiveSystem] using R.iter_injective hnm

/-- Packaged RFO host induced by a flagship **RI** system. -/
def PackagedReflectiveHost.fromRepresentational (R : RepresentationalSystem) : PackagedReflectiveHost where
  system := toReflectiveSystem R
  injectiveTower := toReflectiveSystem_iterInjective R

/-- Tower unboundedness for any **RI** `RepresentationalSystem`. -/
theorem iterative_unbounded_fromRepresentational (R : RepresentationalSystem) (n : ℕ) :
    ∃ m : ℕ, n < m ∧
      Core.metaRegressArrow (toReflectiveSystem R) m ≠ Core.metaRegressArrow (toReflectiveSystem R) n :=
  iterative_unbounded (PackagedReflectiveHost.fromRepresentational R) n

/-- Same via the obstruction packaging. -/
theorem iterative_unbounded_obstruction_fromRepresentational (R : RepresentationalSystem) (n : ℕ) :
    ∃ m : ℕ, n < m ∧
      Core.metaRegressArrow (toReflectiveSystem R) m ≠ Core.metaRegressArrow (toReflectiveSystem R) n :=
  iterative_unbounded_obstruction (PackagedReflectiveHost.fromRepresentational R) n

/-- Diagonal certificate for the **RI**-induced host. -/
def diagonalCertificate_fromRepresentational (R : RepresentationalSystem) :
    Obstruction.Fold.ObstructionCertificate (toReflectiveSystem R).C :=
  diagonalCertificate (PackagedReflectiveHost.fromRepresentational R)

/-- Human-readable note: **`lake require`** is **on**; bump `lakefile.lean` pin with upstream. -/
def riLakeRequireIntegratedNote : String :=
  "SPEC_004 step 2: `«representational-incompleteness»` pinned in lakefile; bump rev when RI moves."

/-- Back-compat name for older greps / docs. -/
abbrev riLakeRequireBlockedNote : String :=
  riLakeRequireIntegratedNote

/-- **`SPEC_008` bridge:** any **RI** host inherits the **sort** fold obstruction on induced `ReflectiveSystem`. -/
theorem representational_incompleteness_implies_reflective_fold_obstruction (R : RepresentationalSystem) :
    ¬ ReflTransGen (reflectiveSlotStep (toReflectiveSystem R))
      (Core.Slots.OntologicalSlot.obj (toReflectiveSystem R).A)
      (Core.Slots.OntologicalSlot.mor (toReflectiveSystem R).represent) := by
  simpa [toReflectiveSystem] using Obstruction.ReflectiveFold.reflective_fold_obstruction_slot_mismatch (toReflectiveSystem R)

/-- **`SPEC_020`:** RI hosts induce the semantic typing obstruction on slots (parametric vs mor-carrier). -/
theorem RI_semantic_type_mismatch_fromRepresentational (R : RepresentationalSystem) :
    SemanticTypeObstruction
      (Instances.RIDiagonal.riSemanticTyping (toReflectiveSystem R))
      Instances.RIDiagonal.RISemanticTag.parametricSelf
      Instances.RIDiagonal.RISemanticTag.morCarrier :=
  Instances.RIDiagonal.RI_semantic_type_mismatch (toReflectiveSystem R)

end ReflectiveFoldObstruction.Examples.RepresentationalIncompleteness
