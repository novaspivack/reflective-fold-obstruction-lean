# reflective-fold-obstruction-lean — manifest

**Toolchain:** `leanprover/lean4:v4.29.0-rc6`  
**Mathlib:** `v4.29.0-rc6` (via `lakefile.lean`); use `lake exe cache get`  
**Lake package:** `«reflective-fold-obstruction-lean»`  
**Build:** `lake build ReflectiveFoldObstruction` (or `lake build`) from this directory  
**Root import:** `ReflectiveFoldObstruction.lean`  
**Formalization map:** `REFLECTIVE_FOLD_OBSTRUCTION_FORMALIZATION_MAP.md`  
**Theorem inventory:** `THEOREM_INVENTORY.md`  
**Program EPICs (outer workspace):** `../specs/IN-PROCESS/SPEC_001_RFO_REFLECTIVE_FOLD_OBSTRUCTION_LEAN_EPIC.md`  
**Two-repo policy:** `../specs/IN-PROCESS/SPEC_002_RFO_TWO_REPOSITORY_GOVERNANCE.md`

---

## Layout (layered)

| Layer | Paths | Role |
|-------|--------|------|
| Core | `ReflectiveFoldObstruction/Core/` | Foundations; slots pattern |
| Reflection | `Reflection/` | Towers, slices |
| Diagonal | `Diagonal/` | Lawvere-family, pressure |
| Invariants | `Invariants/` | Sort separation, transport, boundary, connectivity, orientability-like |
| Topology | `Topology/` | Models, separation, local 1D/2D, punctured neighborhoods, boundary, Möbius/cylinder |
| Reachability | `Reachability/` | Internal ops, closure hulls, reachability invariants |
| Obstruction | `Obstruction/` | Fold, reflective fold, open–compact |
| Examples | `Examples/` | RR bridge, cylinder/Möbius, no-collapse |
| Assembly | `Main.lean` | Master assembly (future) |

**Progress (SPEC_004 Phase 2):** `Core/`, `Reflection/`, `Diagonal/LawvereType.lean`, and `Diagonal/LawvereClosed.lean` are proof-complete (no `sorry`). `Diagonal/Pressure.lean` and below remain scaffolds until next slice.

---

## Proof status

- **0** `sorry` in shipped modules.  
- **Core:** `ReflectiveSystem`, `IterInjective`, iterate / slice packaging, injective iterate lemmas (explicit `hij` argument).  
- **Core.Slots:** polymorphic `OntologicalSlot Obj Mor` + `ReflectiveSlot R` alias and reflective-slot lemmas.  
- **Reflection:** tower and slice consequences guard `IterInjective` via an explicit argument `hij` (not bundled into `ReflectiveSystem`), per SPEC_003 separation of structure vs hypothesis.
- **Diagonal.LawvereType:** Lawvere fixed-point theorem for `A : Type u`, `B : Type v`, corollaries, `Nat` packaging.
- **Diagonal.LawvereClosed:** `lawvereBinary`, curry/`uncurry` alignment with `LawvereType`, `lawvere_universal_iff_surjective_curry`, fixed point with surjective `MonoidalClosed.curry`.

---

## Honest limits

1. **IterInjective** is a **hypothesis**, not a consequence of choosing an arbitrary `represent : A ⟶ A` (same mathematical situation as `RepresentationalRegress`).
2. **Promoted abstraction** stops at what is in this repo; paper-tied concrete geometry remains in `representational-regress-lean` until SPEC_002 promotion / SPEC_004 dependency.

---

## See also

- `ARTIFACT.md` — citation / reproduction  
- `specs/README.md` — where workspace EPICs live when using the submodule layout  
