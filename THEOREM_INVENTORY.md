# Reflective Fold Obstruction — theorem inventory (Lean names)

**Last updated:** 2026-03-27 — Phase A **`SPEC_015`–`018`** (relation persistence, generated calculi, architecture universality, reflective admissible families); `lake build ReflectiveFoldObstruction`, **0** `sorry`.  
**EPICs:** outer `specs/IN-PROCESS/README.md`

Buckets **A–F** (vision §9 / SPEC_003). **Portfolio:** RFO’s distinct lift is buckets **D–F** especially (`Reachability`, `Obstruction`, invariant transport) — the **internal-reachability** story — alongside **A–C** as shared reflective/diagnostic machinery, **not** as a replacement for the **Representational Incompleteness** flagship (see outer `SPEC_001` / `PROJECT_VISION` opening).

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
| `Diagonal.Pressure` | `uliftNatSucc`, `uliftNat_succ_ne_self`, `not_surjective_curry_iff_not_universal_binary`, `not_surjective_curry_into_nat_iff`, `not_surjective_curry_into_uliftNat_iff`, `not_surjective_curry_of_fixed_point_free`, `not_surjective_curry_into_nat`, `not_surjective_curry_into_uliftNat`, `not_universal_binary_of_fixed_point_free`, `not_universal_binary_into_uliftNat` |

---

## C. Non-collapse

| Module | Names |
|--------|--------|
| `Core.Slots` | `OntologicalSlot`, `obj_ne_mor`, `obj_injective`, `mor_injective`, `reflectiveSlot_obj_ne_mor`, `reflectiveSlot_tower_preserves_mor`, `reflectiveSlot_no_mor_is_obj`, `reflectiveSlot_represent_mor_ne_obj_A` |
| `Examples.NoCollapse` | `represent_mor_ne_obj_A` (alias of `SortSeparation.represent_slot_disjoint_from_obj_A`) |
| `Examples.RepresentationalIncompleteness` | `PackagedReflectiveHost`, `iterative_unbounded`, `iterative_unbounded_obstruction`, `diagonalCertificate`, `toReflectiveSystem`, `toReflectiveSystem_iterInjective`, `PackagedReflectiveHost.fromRepresentational`, `iterative_unbounded_fromRepresentational`, `iterative_unbounded_obstruction_fromRepresentational`, `diagonalCertificate_fromRepresentational`, `representational_incompleteness_implies_reflective_fold_obstruction`, `riLakeRequireIntegratedNote` / `riLakeRequireBlockedNote` |

---

## D. Invariant transport

| Module | Names |
|--------|--------|
| `Invariants.SortSeparation` | `mapSlot`, `mapSlot_obj`, `mapSlot_mor`, `mapSlot_injective`, `mapSlot_preserves_branch_disjoint`, `tower_slots_injective`, `represent_slot_disjoint_from_obj_A`, `represent_mor_ne_obj` |
| `Invariants.Transport` | `pullbackPred`, `pullbackPred_apply`, `transportPred`, `transportPred_apply`, `transportPred_symm_iff`, `transportPred_pullback`, `pullbackPred_transport`, `slotEquiv`, `slotEquiv_apply_obj`, `slotEquiv_apply_mor`, `mapSlot_comp`, `slotEquiv_trans` |
| `Invariants.BoundaryType` | `LocalModelKind`, `pullbackTyping`, `transportTyping`, fiber defs (`boundaryFiber`, `interiorFiber`, `mem_*`, `iff_*_nonempty`, `iff_eq_univ_*`), global predicates + transport / incompatibility + pullback lemmas |
| `Invariants.ConnectedBoundary` | `RelBoundarySep`, `HasRelBoundarySep`, `IsRelBoundaryConnected`, `RelBoundarySep.boundary_nonempty`, `RelBoundarySep.image_equiv`, `HasRelBoundarySep.iff_image_equiv`, `IsRelBoundaryConnected.iff_image_equiv`, `not_HasRelBoundarySep_of_AllInterior`, `ExistsBoundaryPoint.of_boundaryFiber_HasRelBoundarySep` |
| `Invariants.OrientabilityLike` | `ParityGauge`, `transportGauge`, `IsLocallyConstant`, `HasTwistWitness`, `IsLocallyConstant_iff_not_hasTwistWitness`, transport + const/twist `iff` lemmas |
| `Core.ArchitectureObstruction` | `architecture_internal_reachability_preserves_invariant`, `architecture_fold_obstruction_of_invariant_mismatch`, `architecture_seed_hull_preserves_invariant`, `architecture_not_mem_hull_of_mismatch`, `architecture_not_reachable_of_mismatch`, `architecture_class_preserved_invariant_obstruction`, `architecture_class_hull_exclusion`, `universal_fold_pattern_for_architecture_class` |
| `Reachability.ArchitectureClasses` | `Architecture`, `FoldObstructionBundle` |
| `Reachability.InternalOps` | `ForwardClosed`, `PreservedBy`, `StepPreservedBy`, `HullPreservedBy`, `hullPreservedBy_iff_forwardClosed`, `forwardClosed_of_weaker`, `forwardClosed_of_step_implies_eq`, `reflTransGen_preserves_invariant`, `preserved_conj`, `PreservedBy.inter`, `ReflTransGen.eq_of_eq`, `ReflTransGen.forwardClosed`, `ReflTransGen.backward_closed_of_symm`, `reflTransGen_mono_of_subrelation`, `not_reflTransGen_of_superrelation`, `not_reachable_when_smaller_step_included`, `preserved_under_relation_extension` |
| `Reachability.ClosureHull` | `reachableFrom`, `subset_reachableFrom`, `reachableFrom_empty`, `reachableFrom_univ`, `reachableFrom_mono`, `reachableFrom_inter_subset`, `reachableFrom_iUnion`, `reachableFrom_iInter_subset`, `reachableFrom_union`, `reachableFrom_idem`, `mem_reachableFrom_singleton`, `mem_reachableFrom_induction`, `reachableFrom_subset_setOf`, `reachableFrom_subset_of_forwardClosed`, `not_mem_reachableFrom_of_preserved_mismatch`, `reachableFrom_subset_of_subrelation`, `hull_nonmembership_persists_under_relation_extension` |
| `Reachability.GeneratedCalculi` | `unionGen`, `forwardClosed_unionGen`, `generated_calculus_preserves_invariant`, `generated_calculus_fold_obstruction`, `obstruction_persists_for_generated_calculus`, `reflectiveProperTowerStep`, `reflectiveBoolGen`, `forwardClosed_reflectiveProperTower`, `forwardClosed_reflectiveBoolGen`, `reflective_generator_family_preserves_sort_separation`, `unionBoolGen_of_calcShape`, `reflective_unionBoolGen_fold_obstruction` |
| `Reachability.Invariants` | `ForwardClosed.mem_reachableFrom`, `preserved_mem_reachableFrom`, `reachableFrom_subset_of_preserved`, `not_mem_reachableFrom_of_preserved_mismatch`, `reachableFrom_eq_of_seed_univ` |
| `Reachability.ReflectiveSteps` | `morAdvances`, `morAdvancesTower`, `reflectiveSlotStep`, `IsObjReflectiveSlot`, `reflective_step_preserves_sort_separation`, `reflective_step_preserves_objBranch`, `not_IsObjReflectiveSlot_mor_represent`, `reflective_reachable_preserves_sort_separation` |
| `Reachability.ReflectiveCalculus` | `reflectiveCalcStep`, `reflectiveSlotStep_sub_reflectiveCalcStep`, `reflectiveCalc_step_preserves_sort_separation`, `reflectiveCalc_reachability_preserves_sort_separation`, `reflectiveCalc_fold_obstruction_slot_mismatch`, `obstruction_persists_under_reflectiveCalc`, `reflectiveCalc_step_strictly_extends_reflectiveSlotStep`, `reflectiveAdmissibleUnion`, `reflective_calc_family_preserves_sort_separation`, `reflective_calc_family_fold_obstruction`, `no_internal_route_obj_to_mor_under_generated_reflective_calculus`, `reflectiveCalcStep_sub_admissibleBoolUnion`, `reflTransGen_reflectiveCalc_sub_unionBool` |
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
| `Topology.HolonomyPhase` | `HolonomyState`, `holonomyPhaseStep`, `HolonomyTrivialBounded`, `holonomy_phase_step_preserves_trivialTag`, `holonomy_phase_forwardClosed`, `holonomy_phase_dynamic_fold_obstruction` |
| `Topology.Boundary` | `corneredUnitSquare`, `corneredUnitSquare_eq` |
| `Topology.Hausdorff` | `prod_t2space` |
| `Obstruction.OpenCompact` | `isCompact_of_finite`, `isCompact_finset` |
| `Obstruction.OpenCompactWitness` | `openCompactWitnessStep`, `WitnessedFinite`, `openCompactWitness_step_preserves_WitnessedFinite`, `openCompactWitness_forwardClosed`, `openCompactWitness_fold_obstruction` |
| `Examples.CylinderMobius` | `parityOfHolonomy`, `parity_reflects_twist`, `mobius_cylinder_fold_obstruction` |
| `Examples.ObserverBridge` | `mechanistic_observer_route_blocked_by_preserved_mismatch`, `rfo_fold_pattern_of_preserved_mismatch` |

*Flagship smooth/quotient models per SPEC_002 remain in `representational-incompleteness-lean`.*

---

## F. General fold obstruction

| Module | Names |
|--------|--------|
| `Obstruction.ArchitectureUniversality` | `architecture_class_preserved_invariant_obstruction`, `architecture_class_hull_exclusion`, `universal_fold_pattern_for_architecture_class` |
| `Obstruction.Fold` | `ObstructionKind`, `ObstructionCertificate`, `PreservedInvariantStep`, `internal_reachability_preserves_invariant`, `fold_obstruction_of_invariant_mismatch`, `not_reachable_of_preserved_and_mismatch`, `reachableFrom_hull_preserves_invariant`, `preserved_seed_mem_reachableFrom`, `not_mem_reachableFrom_of_preserved_invariant_mismatch`, `fold_obstruction_persists_under_relation_extension`, `hull_exclusion_persists_under_relation_extension`, `hull_nonmembership_persists_under_relation_extension` (**`Fold`** alias), `FoldObstruction`, `FoldObstruction.not_reachable`, `foldObstruction_of_preservedInvariant` |
| `Obstruction.CanonicalInstances` | `forwardClosed_AllInterior`, `fold_obstruction_of_boundary_type_mismatch`, `forwardClosed_IsRelBoundaryConnected`, `fold_obstruction_of_connected_boundary_mismatch`, `forwardClosed_parity_false`, `fold_obstruction_of_orientability_mismatch`, `fold_obstruction_of_homeomorph_invariant_mismatch`, `isTrivialHolonomy`, `forwardClosed_isTrivialHolonomy`, `mobius_cylinder_fold_obstruction`, `fold_obstruction_of_sort_separation_mismatch` |
| `Obstruction.ReflectiveFold` | `certificateOfIterativeUnbounded`, `iterative_unbounded`, `reflective_fold_obstruction_slot_mismatch`, `reflective_architecture_fold_obstruction` |
| `Main` | `assemblySurface` |
