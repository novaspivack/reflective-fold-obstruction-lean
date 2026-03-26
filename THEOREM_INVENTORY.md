# Reflective Fold Obstruction — theorem inventory (Lean names)

**Last updated:** 2026-03-26 — `lake build ReflectiveFoldObstruction`.  
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

*(No entries yet — next: `Diagonal/LawvereType.lean`.)*

---

## C. Non-collapse

| Module | Names |
|--------|--------|
| `Core.Slots` | `OntologicalSlot`, `obj_ne_mor`, `obj_injective`, `mor_injective`, `reflectiveSlot_obj_ne_mor`, `reflectiveSlot_tower_preserves_mor`, `reflectiveSlot_no_mor_is_obj`, `reflectiveSlot_represent_mor_ne_obj_A` |

---

## D. Invariant transport

*(No entries yet.)*

---

## E. Concrete obstruction

*(No entries yet — flagship concrete work stays in `representational-regress-lean` per SPEC_002.)*

---

## F. General fold obstruction

*(No entries yet.)*
