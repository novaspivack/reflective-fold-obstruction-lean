# reflective-fold-obstruction-lean

Lean 4 + Mathlib library for **Reflective Fold Obstruction** (general framework layer).

**Outer workspace** (specs, EPICs, submodule wrapper): sibling repo **Reflective Fold Obstruction** — see `../specs/IN-PROCESS/README.md` when checked out as a submodule.

**Relation to `representational-regress-lean`:** keep that repo as the flagship concrete artifact; see outer `specs/IN-PROCESS/SPEC_002_RFO_TWO_REPOSITORY_GOVERNANCE.md`.

## Build

**Use the Mathlib binary cache:**

```bash
lake update
lake exe cache get       # REQUIRED: pre-built .olean blobs
lake build ReflectiveFoldObstruction
```

Workspace documentation (cache, submodule layout): outer `docs/lean_mathlib_cache_workflow.md`, `docs/optional_mathlib.md`, `docs/repository_names.md`.

## Layout

Layered module tree under `ReflectiveFoldObstruction/` (`Core`, `Reflection`, `Diagonal`, `Invariants`, `Topology`, `Reachability`, `Obstruction`, `Examples`, `Main`). Roles are specified in outer `specs/IN-PROCESS/SPEC_003_RFO_LEAN_LAYER_EPICS.md` and `specs/NOTES/PROJECT_VISION.md`.

See `MANIFEST.md`, `THEOREM_INVENTORY.md`, `REFLECTIVE_FOLD_OBSTRUCTION_FORMALIZATION_MAP.md`, `ARTIFACT.md`, `docs/argument-structure.md`.
