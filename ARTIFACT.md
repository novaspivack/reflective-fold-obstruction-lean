# reflective-fold-obstruction-lean — artifact documentation

**Lean:** `leanprover/lean4:v4.29.0-rc6`  
**Mathlib:** `v4.29.0-rc6` — use **`lake exe cache get`** after `lake update`  
**Build:** `lake build ReflectiveFoldObstruction` from this directory  
**Lake deps:** Mathlib only (`lakefile.lean`, `lake-manifest.json`)  
**Program / governance (outer):** `../specs/IN-PROCESS/SPEC_001_RFO_REFLECTIVE_FOLD_OBSTRUCTION_LEAN_EPIC.md`, `SPEC_002_RFO_TWO_REPOSITORY_GOVERNANCE.md`

---

## What this artifact is

A **Mathlib-grounded** library for **internal reachability, invariant transport, and fold obstruction** — the **Reflective Fold Obstruction** formal layer. Full `ReflectiveFoldObstruction/` tree per `SPEC_003_RFO` (definitions + lemmas, **0** `sorry`), independent of **`lake require representational-incompleteness-lean`** (SPEC_002). **`representational-incompleteness-lean`** (**RI**) is the **sibling flagship** for the full **RI** corpus and promoted geometry (SPEC_004 Phase 3).

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
