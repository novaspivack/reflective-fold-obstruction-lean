# Reflective Fold Obstruction — formalization map

**Purpose:** Module roles; pair with `MANIFEST.md`, `THEOREM_INVENTORY.md`, outer `specs/IN-PROCESS/SPEC_003_RFO_LEAN_LAYER_EPICS.md`.  
**Narrative design:** `../specs/NOTES/PROJECT_VISION.md`

**Program role:** This library implements the **reachability / invariant / obstruction** layer for “**a fold is not an iterate**.” It **does not** aim to host the **Representational Incompleteness** universal diagonal flagship (RI). **Observer Exhaustion** (external) synthesizes across programs without duplicating this tree.

---

## Module tree (implemented)

| Path | Role |
|------|------|
| `ReflectiveFoldObstruction/Core/Basic.lean` | `ReflectiveSystem`, `IterInjective`, iterates + monoid `pow_succ` / `pow_add` / `pow_mul` on `End A`, `Over` packaging, injective lemmas (explicit `hij`) |
| `ReflectiveFoldObstruction/Core/Slots.lean` | Polymorphic `OntologicalSlot Obj Mor`, `ReflectiveSlot R`, non-collapse / tower slot lemmas |
| `ReflectiveFoldObstruction/Reflection/Towers.lean` | `regress_*` / unboundedness under `IterInjective` |
| `ReflectiveFoldObstruction/Reflection/Slices.lean` | `regress_over_injective` |
| `ReflectiveFoldObstruction/Diagonal/LawvereType.lean` | Lawvere fixed point + corollaries in `Type` (`universe u v`) |
| `ReflectiveFoldObstruction/Diagonal/LawvereClosed.lean` | `MonoidalClosed (Type u)`: `lawvereBinary`, curry surjectivity ↔ universality, `lawvere_fixed_point_MonoidalClosedType` |
| `ReflectiveFoldObstruction/Diagonal/Pressure.lean` | `not_surjective_curry_iff_not_universal_binary` (`Iff.not`/`symm` on `LawvereClosed`); fixed-point-free → non-surjective curry / non-universal binary; `Nat` / **`ULift.{u} Nat`** |
| `ReflectiveFoldObstruction/Invariants/SortSeparation.lean` | `mapSlot`, `mapSlot_injective`, branch disjointness; reflective `tower_slots_injective`, `represent_*` |
| `ReflectiveFoldObstruction/Invariants/Transport.lean` | Predicate pullback/transport along `Equiv`; `slotEquiv` for `OntologicalSlot`; `mapSlot_comp` / `slotEquiv_trans` |
| `ReflectiveFoldObstruction/Invariants/BoundaryType.lean` | `LocalModelKind`; `transportTyping` / `pullbackTyping`; preservation under `Equiv`; interior/boundary incompatibility |
| `ReflectiveFoldObstruction/Invariants/ConnectedBoundary.lean` | `RelBoundarySep`, `HasRelBoundarySep`, `IsRelBoundaryConnected`; `iff` under `Set.image` of `Equiv` |
| `ReflectiveFoldObstruction/Invariants/OrientabilityLike.lean` | Parity gauges `α → Bool`, transport, const vs twist witness |
| `ReflectiveFoldObstruction/Invariants/HomeomorphTransport.lean` | Re-export `BoundaryType` / `OrientabilityLike` / `ConnectedBoundary` lemmas via `Homeomorph.toEquiv` |
| `ReflectiveFoldObstruction/Topology/Models.lean` | `closedUnitInterval`, `openUnitInterval`, `closedUnitSquare` |
| `ReflectiveFoldObstruction/Topology/Hausdorff.lean` | Product inherits `T2Space` |
| `ReflectiveFoldObstruction/Topology/LocalModels1D.lean` | `halfLine` (`Ici 0`), `fullLine`; half-line ≠ univ |
| `ReflectiveFoldObstruction/Topology/LocalModels2D.lean` | Closed upper half-plane subset of `ℝ × ℝ` |
| `ReflectiveFoldObstruction/Topology/PuncturedNeighborhoods.lean` | `puncturedReals` |
| `ReflectiveFoldObstruction/Topology/Boundary.lean` | `corneredUnitSquare` (= product model) |
| `ReflectiveFoldObstruction/Topology/MobiusCylinder.lean` | `HolonomyTag`, `tagEquiv` |
| `ReflectiveFoldObstruction/Reachability/InternalOps.lean` | `ForwardClosed`, `ReflTransGen.forwardClosed` |
| `ReflectiveFoldObstruction/Reachability/ClosureHull.lean` | `reachableFrom`, `reachableFrom_empty`, `reachableFrom_univ`, `reachableFrom_inter_subset`, `reachableFrom_iUnion`, `reachableFrom_iInter_subset`, idempotence, `∪`, `mem_reachableFrom_singleton`, `mem_reachableFrom_induction` |
| `ReflectiveFoldObstruction/Reachability/Invariants.lean` | `ForwardClosed.mem_reachableFrom`, total reachability lemma |
| `ReflectiveFoldObstruction/Obstruction/Fold.lean` | `ObstructionKind`, `ObstructionCertificate` |
| `ReflectiveFoldObstruction/Obstruction/ReflectiveFold.lean` | `certificateOfIterativeUnbounded`, `iterative_unbounded` |
| `ReflectiveFoldObstruction/Obstruction/OpenCompact.lean` | `Finset` / finite-set `IsCompact` |
| `ReflectiveFoldObstruction/Examples/RepresentationalIncompleteness.lean` | `PackagedReflectiveHost`, `iterative_unbounded*`, `riLakeRequireBlockedNote`; no `lake require representational-incompleteness-lean` (SPEC_002) |
| `ReflectiveFoldObstruction/Examples/CylinderMobius.lean` | `parityOfHolonomy`, link to `OrientabilityLike` |
| `ReflectiveFoldObstruction/Examples/NoCollapse.lean` | `represent_mor_ne_obj_A` |
| `ReflectiveFoldObstruction/Main.lean` | Assembly imports + `assemblySurface` |

---

## Mathlib anchors (current)

| Topic | Mathlib entry points |
|-------|---------------------|
| Categories / slice / `End` | `Mathlib.CategoryTheory.Category.Basic`, `Mathlib.CategoryTheory.Comma.Over.Basic`, `Mathlib.CategoryTheory.Endomorphism` |
| Function / equality | `Mathlib.Logic.Function.Basic` (`congr_fun`) |
| Monoidal closed (types) | `Mathlib.CategoryTheory.Monoidal.Closed.Types`, `Mathlib.CategoryTheory.Monoidal.Closed.Basic`, `Mathlib.CategoryTheory.Monoidal.Types.Basic` |
| Nat | `Mathlib.Data.Nat.Basic` |
| Reflexive-transitive closure | `Mathlib.Logic.Relation` (`ReflTransGen`) |
| Sets / images / `Equiv` | `Mathlib.Data.Set.*`, `Mathlib.Logic.Equiv.Set` |
| Topology (compact, Hausdorff, products) | `Mathlib.Topology.Compactness.Compact`, `Mathlib.Topology.Separation.Hausdorff`, `Mathlib.Topology.Constructions` |
| Real intervals | `Mathlib.Data.Real.Basic`, `Mathlib.Order.Interval.Set.Basic` |

(Expand this table as each layer imports Mathlib content.)

---

## Notes

- **Theorem inventory buckets A–F** (vision §9): maintain in `THEOREM_INVENTORY.md` as formal content appears.
- **No `lake require`** on `representational-incompleteness-lean` until SPEC_004 step 2; re-validate `Examples/RepresentationalIncompleteness` after **RI** API changes.
