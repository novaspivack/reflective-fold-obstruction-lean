/-
  **Open vs compact charts** — Mathlib hooks for chart-size obstructions.

  Concrete “no global finite chart” arguments require flagship geometry from **RI** (SPEC_002).
  Here we only record **finite sets are compact** in any topological space — a basic lemma
  used when extracting finite local covers from compact chart targets.

  Module context: Obstruction/OpenCompact.
-/

import Mathlib.Data.Fintype.Defs
import Mathlib.Topology.Compactness.Compact

universe u

namespace ReflectiveFoldObstruction.Obstruction.OpenCompact

open Set

variable {X : Type u} [TopologicalSpace X]

/-- Finite subsets are compact (subcover reduction to finitely many singleton refinements). -/
theorem isCompact_of_finite (s : Set X) (hs : s.Finite) : IsCompact s :=
  hs.isCompact

theorem isCompact_finset (s : Finset X) : IsCompact (s : Set X) :=
  Set.Finite.isCompact s.finite_toSet

end ReflectiveFoldObstruction.Obstruction.OpenCompact
