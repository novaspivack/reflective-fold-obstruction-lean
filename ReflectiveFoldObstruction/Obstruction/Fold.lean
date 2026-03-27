/-
  **Abstract fold / architecture-change obstructions** — certificate enumerations.

  The concrete “you cannot intern this without a fold” theorems live across `Diagonal/`,
  `Topology/`, and (per SPEC_002) the **RI** flagship (`representational-incompleteness-lean`).  This module only names the
  **obstruction kinds** future assembly lemmas will discharge.

  See `specs/NOTES/PROJECT_VISION.md` — Obstruction/Fold.
-/

universe u

namespace ReflectiveFoldObstruction.Obstruction.Fold

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

end ReflectiveFoldObstruction.Obstruction.Fold
