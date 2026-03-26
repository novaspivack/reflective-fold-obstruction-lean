# Reflective Fold Obstruction — formalization map

**Purpose:** Module roles; pair with `MANIFEST.md`, `THEOREM_INVENTORY.md`, outer `specs/IN-PROCESS/SPEC_003_RFO_LEAN_LAYER_EPICS.md`.  
**Narrative design:** `../specs/NOTES/PROJECT_VISION.md`

---

## Module tree (scaffold → theorems)

| Path | Role |
|------|------|
| `ReflectiveFoldObstruction/Core/Basic.lean` | Foundational objects; temporary `scaffold` / `scaffold_eq_zero` smoke test |
| `ReflectiveFoldObstruction/Core/Slots.lean` | Generalized sort-separation / slot pattern |
| `ReflectiveFoldObstruction/Reflection/Towers.lean` | Reflective towers, iterates |
| `ReflectiveFoldObstruction/Reflection/Slices.lean` | Slice packaging of stages |
| `ReflectiveFoldObstruction/Diagonal/LawvereType.lean` | Lawvere in `Type` |
| `ReflectiveFoldObstruction/Diagonal/LawvereClosed.lean` | Monoidal closed / CCC packaging |
| `ReflectiveFoldObstruction/Diagonal/Pressure.lean` | Diagonal pressure schema |
| `ReflectiveFoldObstruction/Invariants/SortSeparation.lean` | Sort-separation interfaces |
| `ReflectiveFoldObstruction/Invariants/Transport.lean` | Invariant transport |
| `ReflectiveFoldObstruction/Invariants/BoundaryType.lean` | Boundary typing |
| `ReflectiveFoldObstruction/Invariants/ConnectedBoundary.lean` | Boundary connectivity |
| `ReflectiveFoldObstruction/Invariants/OrientabilityLike.lean` | Surrogate separation / orientability-like |
| `ReflectiveFoldObstruction/Topology/Models.lean` | Shared topological models |
| `ReflectiveFoldObstruction/Topology/Hausdorff.lean` | Separation / quotients |
| `ReflectiveFoldObstruction/Topology/LocalModels1D.lean` | 1D local models |
| `ReflectiveFoldObstruction/Topology/LocalModels2D.lean` | 2D local models |
| `ReflectiveFoldObstruction/Topology/PuncturedNeighborhoods.lean` | Punctured neighborhoods, \(\pi_1\)-style obstructions |
| `ReflectiveFoldObstruction/Topology/Boundary.lean` | Boundary gluing |
| `ReflectiveFoldObstruction/Topology/MobiusCylinder.lean` | Möbius / cylinder contrast machinery |
| `ReflectiveFoldObstruction/Reachability/InternalOps.lean` | Internal one-step ops |
| `ReflectiveFoldObstruction/Reachability/ClosureHull.lean` | Closure hulls |
| `ReflectiveFoldObstruction/Reachability/Invariants.lean` | Reachability-stable predicates |
| `ReflectiveFoldObstruction/Obstruction/Fold.lean` | Abstract fold obstruction |
| `ReflectiveFoldObstruction/Obstruction/ReflectiveFold.lean` | Reflective fold specials |
| `ReflectiveFoldObstruction/Obstruction/OpenCompact.lean` | Open vs compact obstructions |
| `ReflectiveFoldObstruction/Examples/RepresentationalRegress.lean` | Future bridge to `representational-regress-lean` (SPEC_002) |
| `ReflectiveFoldObstruction/Examples/CylinderMobius.lean` | Flagship geometric example layer |
| `ReflectiveFoldObstruction/Examples/NoCollapse.lean` | Example-level non-collapse |
| `ReflectiveFoldObstruction/Main.lean` | Master assembly |

---

## Mathlib anchors (current)

| Topic | Mathlib entry points |
|-------|---------------------|
| Nat / smoke | `Mathlib.Data.Nat.Basic` |

(Expand this table as each layer imports Mathlib content.)

---

## Notes

- **Theorem inventory buckets A–F** (vision §9): maintain in `THEOREM_INVENTORY.md` as formal content appears.
- **No dependency** on `representational-regress-lean` until SPEC_004 / interface work explicitly adds `lake require`.
