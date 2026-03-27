# reflective-fold-obstruction-lean — artifact documentation

**Lean:** `leanprover/lean4:v4.29.0-rc6`  
**Mathlib:** `v4.29.0-rc6` — use **`lake exe cache get`** after `lake update`  
**Build:** `lake build ReflectiveFoldObstruction` from this directory  
**Lake deps:** Mathlib + **`«representational-incompleteness»`** (`lakefile.lean`, `lake-manifest.json`)  
**Program / governance (outer):** `../specs/IN-PROCESS/SPEC_001_RFO_REFLECTIVE_FOLD_OBSTRUCTION_LEAN_EPIC.md`, `../specs/IN-PROCESS/SPEC_002_RFO_TWO_REPOSITORY_GOVERNANCE.md`; **Lean layer authority:** `../specs/COMPLETE/SPEC_003_RFO_LEAN_LAYER_EPICS.md`

---

## What this artifact is

A **Mathlib-grounded** library for **internal reachability, invariant transport, and fold obstruction** — the **Reflective Fold Obstruction** formal layer. Full `ReflectiveFoldObstruction/` tree per **`SPEC_003_RFO`** (`../specs/COMPLETE/SPEC_003_RFO_LEAN_LAYER_EPICS.md`) — definitions + lemmas, **0** `sorry`. **Lake:** Mathlib + **`«representational-incompleteness»`** (**SPEC_004** step **2**); **`Examples/RepresentationalIncompleteness`** bridges **RI** `RepresentationalSystem` into RFO. **`representational-incompleteness-lean`** remains the **flagship home** for the **concrete diagonal / geometry corpus** (SPEC_004 Phase **3**).

**What this artifact is not:** it is **not** the home of the **Representational Incompleteness** universal diagonal flagship (that lives with RI). Lawvere-family and pressure lemmas here are **general machinery** for reflective architectures and certificates, complementing RI rather than competing with it. **Observer Exhaustion** (separate program) synthesizes across repos without duplicating this proof corpus.

---

## Reproduction

```bash
cd reflective-fold-obstruction-lean
lake update
lake exe cache get
lake build
```

From outer workspace root: `scripts/verify-lean-build.sh`.

---

## Key theorem summary

See `THEOREM_INVENTORY.md` and `MANIFEST.md`. Buckets A–F in the inventory track theorem families as they land.

**Phase A (robustness / universality, `SPEC_015`–`018`, 2026-03-27):** obstruction and hull facts **persist** when the primitive relation extends (`preserved_under_relation_extension`, `fold_obstruction_persists_under_relation_extension`, hull pullback `reachableFrom_subset_of_subrelation`); **union of generator families** preserves invariants and satisfies the fold pattern (`Reachability/GeneratedCalculi.lean`); **`Architecture` / `FoldObstructionBundle`** package uniform mismatch theorems (`ArchitectureUniversality` + `Core/ArchitectureObstruction`); **admissible reflective families** (`reflectiveAdmissibleUnion`) inherit the obj/mor obstruction, with `reflectiveCalcStep` covered by the standard `Bool` union (`reflectiveCalcStep_sub_admissibleBoolUnion`, `reflTransGen_reflectiveCalc_sub_unionBool`).
