# reflective-fold-obstruction-lean — manifest

**Toolchain:** `leanprover/lean4:v4.29.0-rc6`  
**Mathlib:** `v4.29.0-rc6` (via `lakefile.lean`); use `lake exe cache get`  
**Lake package:** `«reflective-fold-obstruction-lean»`  
**Build:** `lake build ReflectiveFoldObstruction` (or `lake build`) from this directory  
**Root import:** `ReflectiveFoldObstruction.lean`  
**Formalization map:** `REFLECTIVE_FOLD_OBSTRUCTION_FORMALIZATION_MAP.md`  
**Theorem inventory:** `THEOREM_INVENTORY.md`  
**Program EPICs (outer workspace):** `../specs/IN-PROCESS/SPEC_001_RFO_REFLECTIVE_FOLD_OBSTRUCTION_LEAN_EPIC.md`  
**Two-repo policy:** `../specs/IN-PROCESS/SPEC_002_RFO_TWO_REPOSITORY_GOVERNANCE.md`

---

## Layout (layered)

| Layer | Paths | Role |
|-------|--------|------|
| Core | `ReflectiveFoldObstruction/Core/` | Foundations; slots pattern |
| Reflection | `Reflection/` | Towers, slices |
| Diagonal | `Diagonal/` | Lawvere-family, pressure |
| Invariants | `Invariants/` | Sort separation, transport, boundary, connectivity, orientability-like |
| Topology | `Topology/` | Models, separation, local 1D/2D, punctured neighborhoods, boundary, Möbius/cylinder |
| Reachability | `Reachability/` | Internal ops, closure hulls, reachability invariants |
| Obstruction | `Obstruction/` | Fold, reflective fold, open–compact |
| Examples | `Examples/` | RR bridge, cylinder/Möbius, no-collapse |
| Assembly | `Main.lean` | Cross-layer assembly index |

**Progress:** **All modules** in `ReflectiveFoldObstruction/` are substantive (definitions + lemmas, **0** `sorry`). Flagship smooth/quotient geometry remains in `representational-regress-lean` (SPEC_002); this repo supplies abstracts, ℝⁿ model sets, and generic hull/obstruction APIs.

---

## Proof status

- **0** `sorry` in shipped modules.  
- **Core:** `ReflectiveSystem`, `IterInjective`, iterate / slice packaging, monoid laws on `End A` (`representIter_{zero,succ,add,mul}`, `metaRegressArrow_{zero,succ,add}`, `metaOver_{succ,add}`), injective iterate lemmas (explicit `hij` argument).  
- **Core.Slots:** polymorphic `OntologicalSlot Obj Mor` + `ReflectiveSlot R` alias and reflective-slot lemmas.  
- **Reflection:** tower and slice consequences guard `IterInjective` via an explicit argument `hij` (not bundled into `ReflectiveSystem`), per SPEC_003 separation of structure vs hypothesis.
- **Diagonal.LawvereType:** Lawvere fixed-point theorem for `A : Type u`, `B : Type v`, corollaries, `Nat` packaging.
- **Diagonal.LawvereClosed:** `lawvereBinary`, curry/`uncurry` alignment with `LawvereType`, `lawvere_universal_iff_surjective_curry`, fixed point with surjective `MonoidalClosed.curry`.
- **Diagonal.Pressure:** packaged “no surjective `curry (lawvereBinary s)`” under fixed-point-free codomain; `not_surjective_curry_into_nat` at `A : Type` (see honest limits).
- **Invariants.SortSeparation:** functorial `mapSlot` + injectivity under injective branch maps; reflective tower / represent disjointness lemmas (invariant API for `Transport`).
- **Invariants.Transport:** `pullbackPred` / `transportPred` with inverse laws along `Equiv`; `slotEquiv` from branch equivalences + composition / transitivity lemmas.
- **Invariants.BoundaryType:** `LocalModelKind` (interior vs boundary chart tag); `transportTyping` / `pullbackTyping`; fibers; global predicates + `Equiv` preservation and incompatibility lemmas.
- **Invariants.ConnectedBoundary:** `RelBoundarySep` / `HasRelBoundarySep` / `IsRelBoundaryConnected`; equivariance under `Equiv`; link to `boundaryFiber` of a typing.
- **Invariants.OrientabilityLike:** `ParityGauge` (`α → Bool`), `transportGauge`, local constancy vs twist witnesses.
- **Reachability:** `ForwardClosed` + `ReflTransGen` preservation; `reachableFrom` hull (idempotent, union-preserving).
- **Obstruction:** `ObstructionKind` / `ObstructionCertificate`; reflective packaging `iterative_unbounded`; finite-set compactness lemmas.
- **Topology:** Euclidean anchors (`Models`, half-line / half-plane sets, punctured line); `T₂` product hook; holonomy tags + `tagEquiv`.
- **Examples:** `NoCollapse` aliases slot separation; `CylinderMobius` pairs holonomy tags with parity; `RepresentationalRegress` defines `PackagedReflectiveHost` + unboundedness lemmas without RR import.
- **Invariants.HomeomorphTransport:** chart transport lemmas specializing `Equiv` invariants through `X ≃ₜ Y`.

---

## Honest limits

1. **IterInjective** is a **hypothesis**, not a consequence of choosing an arbitrary `represent : A ⟶ A` (same mathematical situation as `RepresentationalRegress`).
2. **Promoted abstraction** stops at what is in this repo; paper-tied concrete geometry remains in `representational-regress-lean` until SPEC_002 promotion / SPEC_004 dependency. *(As of early work on that repo, its `lake build` is still being stabilized; this library stays Mathlib-only until integration is ready.)*
3. **`Pressure.not_surjective_curry_into_nat`** uses `A : Type` (`Type 0`) with codomain **`Nat`** (same universe). For the same `MonoidalClosed (Type u)` story with **`A : Type u`**, use **`Pressure.not_surjective_curry_into_uliftNat`** / **`not_universal_binary_into_uliftNat`** (codomain **`ULift.{u} Nat`**). For unary `A → Nat` enumeration without `MonoidalClosed`, see **`LawvereType`** (`lawvere_no_universal_unary_into_nat`).

---

## See also

- `ARTIFACT.md` — citation / reproduction  
- `specs/README.md` — where workspace EPICs live when using the submodule layout  
