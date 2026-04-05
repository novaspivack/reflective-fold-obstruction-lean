# reflective-fold-obstruction-lean

Lean 4 + Mathlib library for **Reflective Fold Obstruction** — **internal reachability, invariant obstruction, and fold-vs-iterate architecture** (general framework; **not** the RI universal-diagonal flagship).

**Outer workspace** (specs, EPICs, submodule wrapper): sibling repo **Reflective Fold Obstruction** — see `../specs/IN-PROCESS/README.md` when checked out as a submodule.

**Relation to `representational-incompleteness-lean`:** **RI** flagship Lean library — **`lake require «representational-incompleteness»`** is **on** (see `lakefile.lean` pin; **SPEC_002** / **SPEC_004**). Portfolio (**RI** vs RFO vs Observer Exhaustion): outer `SPEC_001`, `MANIFEST.md` mission.

## Build

**Use the Mathlib binary cache:**

```bash
lake update
lake exe cache get       # REQUIRED: pre-built .olean blobs
lake build ReflectiveFoldObstruction
```

Workspace documentation (cache, submodule layout): outer `docs/008_LEAN_MATHLIB_CACHE_WORKFLOW.md`, `docs/009_OPTIONAL_MATHLIB.md`, `docs/007_REPOSITORY_NAMES.md`.

## Layout

Layered module tree under `ReflectiveFoldObstruction/` (`Core`, `Reflection`, `Diagonal`, `Invariants`, `Topology`, `Reachability`, `Obstruction`, `Examples`, `Main`). Roles are specified in outer `specs/COMPLETE/SPEC_003_RFO_LEAN_LAYER_EPICS.md` and `specs/NOTES/PROJECT_VISION.md`. Shipped modules aim for **no** `sorry`; diagonal **pressure** includes a **`ULift Nat`** track aligned with universe-polymorphic `MonoidalClosed (Type u)`.

See `MANIFEST.md`, `THEOREM_INVENTORY.md`, `REFLECTIVE_FOLD_OBSTRUCTION_FORMALIZATION_MAP.md`, `ARTIFACT.md`, `docs/argument-structure.md`.
<!-- NOVA_ZPO_ZENODO_SOFTWARE_BEGIN -->
**Archival software (Zenodo):** https://doi.org/10.5281/zenodo.19429256
<!-- NOVA_ZPO_ZENODO_SOFTWARE_END -->
