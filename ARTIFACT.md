# reflective-fold-obstruction — artifact documentation

**Lean:** `leanprover/lean4:v4.29.0-rc6`  
**Mathlib:** `v4.29.0-rc6` — use **`lake exe cache get`** after `lake update`  
**Build:** `lake build ReflectiveFoldObstruction` from this directory  
**Lake deps:** Mathlib only (`lakefile.lean`, `lake-manifest.json`)  
**Workspace handoff:** `../specs/IN-PROCESS/SPEC_001_RFO_REFLECTIVE_FOLD_OBSTRUCTION_LEAN_EPIC.md`

---

## What this artifact aims to prove

Machine-checked development for the **reflective fold obstruction** program. This repository begins as a **scaffold**; extend `THEOREM_INVENTORY.md` and this section as real claims land.

---

## Reproduction

```bash
cd reflective-fold-obstruction
lake update
lake exe cache get
lake build
```

One-shot from workspace root: `scripts/verify-lean-build.sh`.

---

## Key theorem summary

See `THEOREM_INVENTORY.md` and `MANIFEST.md`.
