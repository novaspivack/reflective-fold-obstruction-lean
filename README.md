# reflective-fold-obstruction-lean

Lean 4 + Mathlib library for **Reflective Fold Obstruction** — **internal reachability, invariant obstruction, and fold-vs-iterate architecture** (general framework; **not** the RI universal-diagonal flagship).

**Outer workspace** (specs, EPICs, submodule wrapper): sibling repo **Reflective Fold Obstruction** — see `../specs/IN-PROCESS/README.md` when checked out as a submodule.

**Relation to `representational-incompleteness-lean`:** **RI** flagship Lean library (diagonal / self-model summit **and** concrete development **as maintained there**); RFO stays Mathlib-only until SPEC_004 — see outer `specs/IN-PROCESS/SPEC_002_RFO_TWO_REPOSITORY_GOVERNANCE.md`. Portfolio (**RI** vs RFO vs Observer Exhaustion): outer `SPEC_001`, `MANIFEST.md` mission.

## Build

**Use the Mathlib binary cache:**

```bash
lake update
lake exe cache get       # REQUIRED: pre-built .olean blobs
lake build ReflectiveFoldObstruction
```

Workspace documentation (cache, submodule layout): outer `docs/lean_mathlib_cache_workflow.md`, `docs/optional_mathlib.md`, `docs/repository_names.md`.

## Layout

Layered module tree under `ReflectiveFoldObstruction/` (`Core`, `Reflection`, `Diagonal`, `Invariants`, `Topology`, `Reachability`, `Obstruction`, `Examples`, `Main`). Roles are specified in outer `specs/COMPLETE/SPEC_003_RFO_LEAN_LAYER_EPICS.md` and `specs/NOTES/PROJECT_VISION.md`. Shipped modules aim for **no** `sorry`; diagonal **pressure** includes a **`ULift Nat`** track aligned with universe-polymorphic `MonoidalClosed (Type u)`.

See `MANIFEST.md`, `THEOREM_INVENTORY.md`, `REFLECTIVE_FOLD_OBSTRUCTION_FORMALIZATION_MAP.md`, `ARTIFACT.md`, `docs/argument-structure.md`.
