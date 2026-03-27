# Argument structure (plain language)

**Formal EPICs:** outer `specs/IN-PROCESS/SPEC_001_RFO_REFLECTIVE_FOLD_OBSTRUCTION_LEAN_EPIC.md` and follow-ons.  
**Narrative spine:** outer `specs/NOTES/PROJECT_VISION.md` §1 (master question) and §11 (conceptual splits).

**Versus Representational Incompleteness (RI):** RI’s question is what **cannot be fully represented** under universal self-modeling; **RFO’s** question is what is **not internally reachable** without an **architecture-changing fold**. Same ecosystem; different abstraction level. **Observer Exhaustion** (external) synthesizes both.

1. **Reflection / regress / diagonal / non-collapse** — categorical and logical backbone (`Core`, `Reflection`, `Diagonal`, `Invariants`).
2. **Topology / local obstructions** — concrete spaces and neighborhood arguments (`Topology`).
3. **Internal reachability vs fold** — what closure can generate vs what needs an architecture-changing fold (`Reachability`, `Obstruction`).
4. **Examples** — portable bridge to **`representational-incompleteness-lean`** (`Examples/RepresentationalIncompleteness`) per SPEC_002 (no `lake require` until SPEC_004).

**Build:** always `lake exe cache get` after `lake update` (outer `docs/lean_mathlib_cache_workflow.md`).

---

## Preparation while **`representational-incompleteness-lean`** evolves (SPEC_004 / SPEC_002)

No `lake require` on **RI** until SPEC_004 “Import strategy” step 2. Useful parallel work:

- **Core / Reflection:** monoid laws on `End A`, `IterInjective` ↔ injective `metaRepresent` (`Core/Basic`).
- **Reachability:** hull lemmas matching vision §6 — `mem_reachableFrom_induction`, **finite** `∪`/`∩`, **indexed** `iUnion`/`iInter` subset, `univ`, empty seed.
- **Diagonal:** keep **`ULift Nat`** pressure lemmas (`Diagonal/Pressure`) as the universe-polymorphic companion to `Nat` at `Type`.
- **Integration:** when **`representational-incompleteness-lean`** `lake build` and **public types** are stable, align `Examples/RepresentationalIncompleteness` / `PackagedReflectiveHost` with **current** **RI** interfaces; run outer `scripts/verify-lean-build.sh`.
- **Tracking:** inner `MANIFEST.md` honest-limits + `THEOREM_INVENTORY.md` buckets **A–F**; EPIC status in outer `specs/IN-PROCESS/`.
