# Reflective Fold Obstruction — theorem inventory (Lean names)

**Last updated:** 2026-03-26 — `lake build ReflectiveFoldObstruction` (full tree + `IterInjective` ↔ injective `metaRepresent`, empty reachability hull, **0** `sorry`).  
**EPICs:** outer `specs/IN-PROCESS/README.md`

Buckets **A–F** (vision §9 / SPEC_003).

---

## A. Reflective generation

| Module | Names |
|--------|--------|
| `Core.Basic` | `ReflectiveSystem`, `IterInjective`, `iterInjective_iff_injective_metaRepresent`, `representIter`, `metaRegressArrow`, `metaOver`, `metaRepresent`, `Over_mk_inj_parallel`, `representIter_injective`, `metaRegressArrow_injective`, `metaOver_injective`, `metaRepresent_injective`, `representIter_zero`, `representIter_one`, `representIter_succ`, `representIter_add`, `representIter_mul`, `metaRegressArrow_zero`, `metaRegressArrow_one`, `metaRegressArrow_succ`, `metaRegressArrow_add`, `metaOver_succ`, `metaOver_add` |
| `Reflection.Towers` | `regress_no_termination`, `regress_iterates_unbounded`, `regress_is_infinite`, `meta_range_infinite` |
| `Reflection.Slices` | `regress_over_injective` |

*(All tower/slice lemmas take `(R : ReflectiveSystem)` and `(hij : IterInjective R)` explicitly.)*

---

## B. Diagonal pressure

| Module | Names |
|--------|--------|
| `Diagonal.LawvereType` | `lawvere_fixed_point_Type` (`A : Type u`, `B : Type v`), `lawvere_fixed_point_corollary_no_universal`, `lawvere_no_universal_unary_into_nat` |
| `Diagonal.LawvereClosed` | `lawvereBinary`, `lawvereBinary_apply`, `uncurry_eq_lawvereBinary`, `curry_lawvereBinary`, `lawvere_universal_iff_surjective_curry`, `lawvere_fixed_point_MonoidalClosedType` |
| `Diagonal.Pressure` | `uliftNatSucc`, `uliftNat_succ_ne_self`, `not_surjective_curry_of_fixed_point_free`, `not_surjective_curry_into_nat`, `not_surjective_curry_into_uliftNat`, `not_universal_binary_of_fixed_point_free`, `not_universal_binary_into_uliftNat` |

---

## C. Non-collapse

| Module | Names |
|--------|--------|
| `Core.Slots` | `OntologicalSlot`, `obj_ne_mor`, `obj_injective`, `mor_injective`, `reflectiveSlot_obj_ne_mor`, `reflectiveSlot_tower_preserves_mor`, `reflectiveSlot_no_mor_is_obj`, `reflectiveSlot_represent_mor_ne_obj_A` |
| `Examples.NoCollapse` | `represent_mor_ne_obj_A` (alias of `SortSeparation.represent_slot_disjoint_from_obj_A`) |
| `Examples.RepresentationalRegress` | `PackagedReflectiveHost`, `iterative_unbounded`, `iterative_unbounded_obstruction`, `diagonalCertificate`, `rrLakeRequireBlockedNote` |

---

## D. Invariant transport

| Module | Names |
|--------|--------|
| `Invariants.SortSeparation` | `mapSlot`, `mapSlot_obj`, `mapSlot_mor`, `mapSlot_injective`, `mapSlot_preserves_branch_disjoint`, `tower_slots_injective`, `represent_slot_disjoint_from_obj_A`, `represent_mor_ne_obj` |
| `Invariants.Transport` | `pullbackPred`, `pullbackPred_apply`, `transportPred`, `transportPred_apply`, `transportPred_symm_iff`, `transportPred_pullback`, `pullbackPred_transport`, `slotEquiv`, `slotEquiv_apply_obj`, `slotEquiv_apply_mor`, `mapSlot_comp`, `slotEquiv_trans` |
| `Invariants.BoundaryType` | `LocalModelKind`, `pullbackTyping`, `transportTyping`, fiber defs (`boundaryFiber`, `interiorFiber`, `mem_*`, `iff_*_nonempty`, `iff_eq_univ_*`), global predicates + transport / incompatibility + pullback lemmas |
| `Invariants.ConnectedBoundary` | `RelBoundarySep`, `HasRelBoundarySep`, `IsRelBoundaryConnected`, `RelBoundarySep.boundary_nonempty`, `RelBoundarySep.image_equiv`, `HasRelBoundarySep.iff_image_equiv`, `IsRelBoundaryConnected.iff_image_equiv`, `not_HasRelBoundarySep_of_AllInterior`, `ExistsBoundaryPoint.of_boundaryFiber_HasRelBoundarySep` |
| `Invariants.OrientabilityLike` | `ParityGauge`, `transportGauge`, `IsLocallyConstant`, `HasTwistWitness`, `IsLocallyConstant_iff_not_hasTwistWitness`, transport + const/twist `iff` lemmas |
| `Reachability.InternalOps` | `ForwardClosed`, `ReflTransGen.forwardClosed`, `ReflTransGen.backward_closed_of_symm` |
| `Reachability.ClosureHull` | `reachableFrom`, `subset_reachableFrom`, `reachableFrom_empty`, `reachableFrom_mono`, `reachableFrom_union`, `reachableFrom_idem`, `mem_reachableFrom_singleton` |
| `Reachability.Invariants` | `ForwardClosed.mem_reachableFrom`, `reachableFrom_eq_of_seed_univ` |
| `Invariants.HomeomorphTransport` | `transportTyping_homeomorph_apply`; `BoundaryType.*.iff_homeomorph`; `OrientabilityLike.*.iff_homeomorph`; `ConnectedBoundary.*.iff_image_homeomorph` |

---

## E. Concrete obstruction

| Module | Names |
|--------|--------|
| `Topology.Models` | `closedUnitInterval`, `openUnitInterval`, `closedUnitSquare`, `mem_*` simp lemmas |
| `Topology.LocalModels1D` | `halfLine`, `fullLine`, `zero_mem_halfLine`, `halfLine_subset_line`, `neg_one_not_mem_halfLine`, `halfLine_ne_univ` |
| `Topology.LocalModels2D` | `closedUpperHalfPlane`, `euclideanPlane`, `origin_mem_halfPlane`, `halfPlane_subset_plane` |
| `Topology.PuncturedNeighborhoods` | `puncturedReals`, `mem_puncturedReals`, `zero_notMem_punctured` |
| `Topology.MobiusCylinder` | `HolonomyTag`, `holonomyTag_trivial_ne_twist`, `tagEquiv` |
| `Topology.Boundary` | `corneredUnitSquare`, `corneredUnitSquare_eq` |
| `Topology.Hausdorff` | `prod_t2space` |
| `Obstruction.OpenCompact` | `isCompact_of_finite`, `isCompact_finset` |
| `Examples.CylinderMobius` | `parityOfHolonomy`, `parity_reflects_twist` |

*Flagship smooth/quotient models per SPEC_002 remain in `representational-regress-lean`.*

---

## F. General fold obstruction

| Module | Names |
|--------|--------|
| `Obstruction.Fold` | `ObstructionKind`, `ObstructionCertificate` |
| `Obstruction.ReflectiveFold` | `certificateOfIterativeUnbounded`, `iterative_unbounded` |
| `Main` | `assemblySurface` |
