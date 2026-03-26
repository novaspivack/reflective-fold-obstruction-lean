# reflective-fold-obstruction — manifest

**Toolchain:** `leanprover/lean4:v4.29.0-rc6`  
**Mathlib:** `v4.29.0-rc6` (via `lakefile.lean`); use `lake exe cache get`  
**Build:** `lake build ReflectiveFoldObstruction` (or `lake build`) from this directory  
**Root import:** `ReflectiveFoldObstruction.lean`  
**Formalization map:** `REFLECTIVE_FOLD_OBSTRUCTION_FORMALIZATION_MAP.md`  
**Theorem inventory:** `THEOREM_INVENTORY.md`  
**Program spec:** `../specs/IN-PROCESS/SPEC_001_RFO_REFLECTIVE_FOLD_OBSTRUCTION_LEAN_EPIC.md`  

---

## Layout

| Area | Path | Role |
|------|------|------|
| Scaffold | `ReflectiveFoldObstruction/Basic.lean` | Placeholder theorems tying the project to Mathlib; extend with core definitions |

`ReflectiveFoldObstruction.lean` imports `Basic` so it participates in the default library target.

---

## Proof status

- **0** `sorry` / **0** custom axioms in `ReflectiveFoldObstruction/` (scaffold).
- Claims are **fully checked** relative to Mathlib + Lean’s standard logical core for the statements in-repo.

---

## Honest limits (strength of claim)

1. **Scaffold:** Only trivial definitions (`scaffold`, `scaffold_eq_zero`) are present until the program spec adds real mathematical content.

---

## See also

- `ARTIFACT.md` — citation / reproduction  
- `../docs/submodule_workspace.md` — outer / inner git layout  
- `../docs/lean_mathlib_cache_workflow.md` — Mathlib cache workflow  
