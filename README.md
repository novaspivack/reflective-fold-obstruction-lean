# reflective-fold-obstruction-lean


## Research Program

This repository is part of the **Reflexive Reality** research program by [Nova Spivack](https://www.novaspivack.com/).

**What this formalizes:** Reflective Fold Obstruction (§B5d): hull theorem — forward-closed predicates confine the entire reachable hull; fold barriers are real.

| Link | Description |
|------|-------------|
| [Research page](https://www.novaspivack.com/research/) | Full index of all papers, programs, and Lean archives |
| [Full abstracts](https://novaspivack.github.io/research/abstracts/#b5d-reflective-fold-obstruction) | Complete abstract for this library's papers |
| [Zenodo program hub](https://doi.org/10.5281/zenodo.19429270) | Citable DOI hub for the NEMS program |

All results are machine-checked in Lean 4 with a zero-sorry policy on proof targets.
See [MANIFEST.md](MANIFEST.md) for the sorry audit (if present).

---

Lean 4 + Mathlib library for **Reflective Fold Obstruction** — internal reachability, invariant obstruction, and fold-vs-iterate architecture.

**This is not the RI (Representational Incompleteness) universal-diagonal flagship.** RFO addresses a complementary question: if a predicate is preserved under primitive steps of an internal relation, can the internal reflexive-transitive closure reach any state falsifying that predicate? The answer is no — and the gap between what can be iterated and what can be folded is structurally precise.

## What it proves

- **Hull theorem:** Forward-closed predicates confine the entire reachable hull from seeds satisfying that predicate. Any target falsifying the predicate is not internally reachable — this is a fold barrier.
- **Semantic type obstruction:** Turing-completeness does not imply semantic-type completeness. A system can be Turing-complete and still be permanently type-bounded in its native primitive dynamics.
- **Simulation vs realization:** Forward simulation always projects type reachability; the converse requires a section with backward step-lifting. Without that section, a Turing-complete system can simulate a richer-type system without instantiating it.

## Build

```bash
lake update
lake exe cache get       # pre-built Mathlib .olean blobs (strongly recommended)
lake build ReflectiveFoldObstruction
```

## Layout

Layered module tree under `ReflectiveFoldObstruction/`: `Core`, `Reflection`, `Diagonal`, `Invariants`, `Topology`, `Reachability`, `Obstruction`, `Examples`, `Main`. Zero sorry on shipped proof targets.

## Documentation

See [MANIFEST.md](MANIFEST.md), [THEOREM_INVENTORY.md](THEOREM_INVENTORY.md), [REFLECTIVE_FOLD_OBSTRUCTION_FORMALIZATION_MAP.md](REFLECTIVE_FOLD_OBSTRUCTION_FORMALIZATION_MAP.md), and [ARTIFACT.md](ARTIFACT.md).

The companion paper is published on Zenodo — see [novaspivack.com/research](https://www.novaspivack.com/research).
<!-- NOVA_ZPO_ZENODO_SOFTWARE_BEGIN -->
**Archival software (Zenodo):** https://doi.org/10.5281/zenodo.19429256
<!-- NOVA_ZPO_ZENODO_SOFTWARE_END -->
