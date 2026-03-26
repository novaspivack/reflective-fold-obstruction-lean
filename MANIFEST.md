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

Scaffold namespaces exist throughout; see SPEC_003 in outer `specs/IN-PROCESS/`.

---

## Proof status

- **0** `sorry` in scaffold modules.  
- **Core.Basic** currently exposes only `scaffold` / `scaffold_eq_zero` as a Mathlib smoke test.

---

## See also

- `ARTIFACT.md` — citation / reproduction  
- `specs/README.md` — where workspace EPICs live when using the submodule layout  
