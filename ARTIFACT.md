# reflective-fold-obstruction-lean — artifact documentation

**Lean:** `leanprover/lean4:v4.29.0-rc6`  
**Mathlib:** `v4.29.0-rc6` — use **`lake exe cache get`** after `lake update`  
**Build:** `lake build ReflectiveFoldObstruction` from this directory  
**Lake deps:** Mathlib only (`lakefile.lean`, `lake-manifest.json`)  
**Program / governance (outer):** `../specs/IN-PROCESS/SPEC_001_RFO_REFLECTIVE_FOLD_OBSTRUCTION_LEAN_EPIC.md`, `SPEC_002_RFO_TWO_REPOSITORY_GOVERNANCE.md`

---

## What this artifact is

A **Mathlib-grounded** library for reflective fold obstruction theory: full `ReflectiveFoldObstruction/` tree per `SPEC_003_RFO` (definitions + lemmas, **0** `sorry`), independent of `representational-regress-lean` import (SPEC_002). The RR repo remains the **concrete flagship** for promoted geometry (SPEC_004 Phase 3).

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
