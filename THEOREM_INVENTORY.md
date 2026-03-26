# Reflective Fold Obstruction — theorem inventory (Lean names)

**Last updated:** 2026-03-26 — `lake build ReflectiveFoldObstruction` (incl. `Invariants/SortSeparation`, `Invariants/Transport`, `Invariants/BoundaryType`).  
**EPICs:** outer `specs/IN-PROCESS/README.md`

Buckets **A–F** (vision §9 / SPEC_003).

---

## A. Reflective generation

| Module | Names |
|--------|--------|
| `Core.Basic` | `ReflectiveSystem`, `IterInjective`, `representIter`, `metaRegressArrow`, `metaOver`, `metaRepresent`, `Over_mk_inj_parallel`, `representIter_injective`, `metaRegressArrow_injective`, `metaOver_injective`, `metaRepresent_injective`, `metaRegressArrow_zero`, `representIter_zero` |
| `Reflection.Towers` | `regress_no_termination`, `regress_iterates_unbounded`, `regress_is_infinite`, `meta_range_infinite` |
| `Reflection.Slices` | `regress_over_injective` |

*(All tower/slice lemmas take `(R : ReflectiveSystem)` and `(hij : IterInjective R)` explicitly.)*

---

## B. Diagonal pressure

| Module | Names |
|--------|--------|
| `Diagonal.LawvereType` | `lawvere_fixed_point_Type` (`A : Type u`, `B : Type v`), `lawvere_fixed_point_corollary_no_universal`, `lawvere_no_universal_unary_into_nat` |
| `Diagonal.LawvereClosed` | `lawvereBinary`, `lawvereBinary_apply`, `uncurry_eq_lawvereBinary`, `curry_lawvereBinary`, `lawvere_universal_iff_surjective_curry`, `lawvere_fixed_point_MonoidalClosedType` |
| `Diagonal.Pressure` | `not_surjective_curry_of_fixed_point_free`, `not_surjective_curry_into_nat`, `not_universal_binary_of_fixed_point_free` |

---

## C. Non-collapse

| Module | Names |
|--------|--------|
| `Core.Slots` | `OntologicalSlot`, `obj_ne_mor`, `obj_injective`, `mor_injective`, `reflectiveSlot_obj_ne_mor`, `reflectiveSlot_tower_preserves_mor`, `reflectiveSlot_no_mor_is_obj`, `reflectiveSlot_represent_mor_ne_obj_A` |

---

## D. Invariant transport

| Module | Names |
|--------|--------|
| `Invariants.SortSeparation` | `mapSlot`, `mapSlot_obj`, `mapSlot_mor`, `mapSlot_injective`, `mapSlot_preserves_branch_disjoint`, `tower_slots_injective`, `represent_slot_disjoint_from_obj_A`, `represent_mor_ne_obj` |
| `Invariants.Transport` | `pullbackPred`, `pullbackPred_apply`, `transportPred`, `transportPred_apply`, `transportPred_symm_iff`, `transportPred_pullback`, `pullbackPred_transport`, `slotEquiv`, `slotEquiv_apply_obj`, `slotEquiv_apply_mor`, `mapSlot_comp`, `slotEquiv_trans` |
| `Invariants.BoundaryType` | `LocalModelKind`, `pullbackTyping`, `pullbackTyping_apply`, `transportTyping`, `transportTyping_apply`, `transportTyping_rfl`, `transportTyping_trans`, `transportTyping_map_symm`, `transportTyping_map`, `transportTyping_eq_iff`, `ExistsBoundaryPoint`, `ExistsInteriorPoint`, `AllInterior`, `AllBoundary`, `ExistsBoundaryPoint.iff_transport`, `ExistsInteriorPoint.iff_transport`, `AllInterior.iff_transport`, `AllBoundary.iff_transport`, `not_interior_and_boundary`, `AllInterior.not_ExistsBoundaryPoint`, `ExistsBoundaryPoint.not_AllInterior`, `AllBoundary.not_ExistsInteriorPoint`, `ExistsInteriorPoint.not_AllBoundary`, `pullbackTyping_comp`, `ExistsBoundaryPoint.of_pullback`, `ExistsInteriorPoint.of_pullback`, `AllInterior.of_pullback_surjective`, `AllBoundary.of_pullback_surjective` |

---

## E. Concrete obstruction

*(No entries yet — flagship concrete work stays in `representational-regress-lean` per SPEC_002.)*

---

## F. General fold obstruction

*(No entries yet.)*
