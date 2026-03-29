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

## Mission (non-redundancy)

**RFO** proves that **iteration and internal closure do not amount to architectural transition** when an invariant preserved under internal reachability differs at the target. That is **not** the same program as **Representational Incompleteness (RI)**, which owns the flagship **universal diagonal / self-model** barrier. RFO **absorbs** diagonal and topology tools as reusable layers (`Diagonal`, `Reachability`, `Obstruction`) while keeping its **mathematical soul** the reachability / fold-obstruction schema. **Observer Exhaustion** (elsewhere) is synthesis, not a third copy of this library.

---

## Layout (layered)

| Layer | Paths | Role |
|-------|--------|------|
| Core | `ReflectiveFoldObstruction/Core/` | Foundations; slots pattern; **`ArchitectureObstruction`** export names for the fold pattern; **`SemanticTypeObstruction`** hub (`SPEC_020`) |
| SemanticType | `ReflectiveFoldObstruction/SemanticType/` | **`Typing`** bundle, `typeReachable` / `typeGap`, depth + adjudication + RI diagonal instances, non-triviality |
| Reflection | `Reflection/` | Towers, slices |
| Diagonal | `Diagonal/` | Lawvere-family, pressure |
| Invariants | `Invariants/` | Sort separation, transport, boundary, connectivity, orientability-like |
| Topology | `Topology/` | Models, separation, local 1D/2D, punctured neighborhoods, boundary, Möbius/cylinder, **holonomy phase counter** (`HolonomyPhase`) |
| Reachability | `Reachability/` | Internal ops (**`reflTransGen` monotonicity**), **reflective slot steps**, **rich reflective calculus** (`ReflectiveCalculus`), closure hulls, reachability invariants |
| Obstruction | `Obstruction/` | **Fold (abstract summit)**, canonical instances, reflective fold, open–compact hooks, **discrete open–compact witness** obstruction |
| Examples | `Examples/` | **RI** bridge (`RepresentationalIncompleteness`), cylinder/Möbius, no-collapse, **Observer Exhaustion schematic bridge** (`ObserverBridge`) |
| Assembly | `Main.lean` | Cross-layer assembly index |

**Progress:** **All modules** in `ReflectiveFoldObstruction/` are substantive (definitions + lemmas, **0** `sorry`). Promoted smooth/quotient geometry and **RI**’s full corpus live in **`representational-incompleteness-lean`** (SPEC_002); RFO supplies abstracts, ℝⁿ model sets, and generic hull/obstruction APIs.

---

## Proof status

- **0** `sorry` in shipped modules.  
- **Core:** `ReflectiveSystem`, `IterInjective` (iff injective `metaRepresent`), iterate / slice packaging, monoid laws on `End A` (`representIter_{zero,one,succ,add,mul}`, `metaRegressArrow_{zero,one,succ,add}`, `metaOver_{succ,add}`), injective iterate lemmas (explicit `hij` argument).  
- **Core.Slots:** polymorphic `OntologicalSlot Obj Mor` + `ReflectiveSlot R` alias and reflective-slot lemmas.  
- **Reflection:** tower and slice consequences guard `IterInjective` via an explicit argument `hij` (not bundled into `ReflectiveSystem`), per SPEC_003 separation of structure vs hypothesis.
- **Diagonal.LawvereType:** Lawvere fixed-point theorem for `A : Type u`, `B : Type v`, corollaries, `Nat` packaging.
- **Diagonal.LawvereClosed:** `lawvereBinary`, curry/`uncurry` alignment with `LawvereType`, `lawvere_universal_iff_surjective_curry`, fixed point with surjective `MonoidalClosed.curry`.
- **Diagonal.Pressure:** `not_surjective_curry_iff_not_universal_binary` (negated `LawvereClosed` bridge); fixed-point-free → non-surjective curry; `Nat` / `ULift Nat` packaging (see honest limits).
- **Invariants.SortSeparation:** functorial `mapSlot` + injectivity under injective branch maps; reflective tower / represent disjointness lemmas (invariant API for `Transport`).
- **Invariants.Transport:** `pullbackPred` / `transportPred` with inverse laws along `Equiv`; `slotEquiv` from branch equivalences + composition / transitivity lemmas.
- **Invariants.BoundaryType:** `LocalModelKind` (interior vs boundary chart tag); `transportTyping` / `pullbackTyping`; fibers; global predicates + `Equiv` preservation and incompatibility lemmas.
- **Invariants.ConnectedBoundary:** `RelBoundarySep` / `HasRelBoundarySep` / `IsRelBoundaryConnected`; equivariance under `Equiv`; link to `boundaryFiber` of a typing.
- **Invariants.OrientabilityLike:** `ParityGauge` (`α → Bool`), `transportGauge`, local constancy vs twist witnesses.
- **Reachability:** `PreservedBy` / `HullPreservedBy` (= `ForwardClosed` packaging); `ReflTransGen` / hull preservation; **`reflTransGen_mono_of_subrelation`** + contrapositive **`not_reflTransGen_of_superrelation`** (`SPEC_014`); **`preserved_under_relation_extension`** + **`reachableFrom_subset_of_subrelation`** / **`hull_nonmembership_persists_under_relation_extension`** (`SPEC_015`); `reachableFrom` hull (subset-from-seed, mismatch non-membership, idempotent, **∪** / **iUnion** / indexed **∩**-subset, **univ**, **empty** seed, **induction**); **`ArchitectureClasses`** (`Architecture`, `FoldObstructionBundle`); **`GeneratedCalculi`** — `unionGen`, generator ⇒ union preservation, **`reflectiveBoolGen`** / **`reflective_unionBoolGen_fold_obstruction`** (`SPEC_016`); **`ReflectiveSteps`** (`reflectiveSlotStep`, `morAdvances`, **`morAdvancesTower`**, sort forward-closed lemmas); **`ReflectiveCalculus`** (`reflectiveCalcStep`, strict extension, **`reflectiveAdmissibleUnion`** / admissible-family fold obstruction, **`reflTransGen_reflectiveCalc_sub_unionBool`**, `SPEC_018`).
- **Core.ArchitectureObstruction (`SPEC_012` / `SPEC_017`):** `architecture_*` aliases over **`Obstruction.Fold`** + bundled **`FoldObstructionBundle`** theorems (also in **`Obstruction/ArchitectureUniversality.lean`**).
- **`SemanticType` (`SPEC_020`):** **`Typing`** (SPEC prose: semantic typing), **`typeReachable`** / **`typeGap`**, **`SemanticTypeObstruction`**, **`Typing.withPrimitiveStep`** + monotone / antitone lemmas, **`not_reflTransGen_of_typeGap`**; **`SelfModelDepthDynamics`** + **`toTyping`**, **`selfModelDepth_obstruction`**; **`AdjudicationDynamics`** + **`adjudication_semantic_obstruction`**; **`riSemanticTyping`**, **`RI_semantic_type_mismatch`**, **`RI_slot_fold_obstruction`**; **`semanticType_preorder_nontrivial`** / **`depthLabelTyping`**; **`tagsOnHull`**, **`false_tag_not_mem_tagsOnHull_of_preserved_seed`**; **`conjPairTyping`** / **`typeGap_of_coord`**; **`BipartitionDyn`** ↔ **`FoldObstructionBundle`** bridge; **`TypedPrimitiveSimulation`**, **`TypedPrimitiveSimulationSection`**, **`pullbackAlongSimulation`**, **`typeReachable_pullback_iff_of_section`**, **`SemanticTypeObstruction_pullback_iff_of_section`**, **`typeGap_simulation_pullback`**; **`complementaryTagReach`** / **`typeGap_of_complementary_tags`**; **`pairwiseTypeGap`** / depth **antichain**; **`computabilityComparisonNote`**; import hub **`Core/SemanticTypeObstruction`**.
- **Reachability.InternalOps:** **`reflTransGen_map`** (relation homomorphism lifts `ReflTransGen`).
- **Obstruction.Fold (summit):** `fold_obstruction_of_invariant_mismatch`, **`fold_obstruction_persists_under_relation_extension`**, hull persistence under subrelations, `FoldObstruction` witness, **certificates** metadata only.
- **Obstruction.CanonicalInstances:** boundary typing, connectivity, parity, holonomy, **sort-separation** corollaries factoring through the summit (`SPEC_007`).
- **Obstruction.ReflectiveFold:** `reflective_fold_obstruction_slot_mismatch`, `reflective_architecture_fold_obstruction`; still exports **`iterative_unbounded`** (tower / `IterInjective` channel).
- **Topology:** Euclidean anchors (`Models`, half-line / half-plane sets, punctured line); `T₂` product hook; holonomy tags + `tagEquiv`; **`HolonomyPhase`** dynamic step + **`holonomy_phase_dynamic_fold_obstruction`** (`SPEC_011` B).
- **Obstruction.OpenCompactWitness (`SPEC_011` A):** gated successor on `ℕ`, **`openCompactWitness_fold_obstruction`**.
- **Examples:** `NoCollapse` aliases slot separation; `CylinderMobius` holonomy parity + **`mobius_cylinder_fold_obstruction`** (generic theorem instance); `ObserverBridge` — parameterized **`mechanistic_observer_route_blocked_by_preserved_mismatch`** = fold pattern (`SPEC_013`); `RepresentationalIncompleteness` — `PackagedReflectiveHost`, **RI** `RepresentationalSystem` → `toReflectiveSystem` + `fromRepresentational`, tower unboundedness + **`representational_incompleteness_implies_reflective_fold_obstruction`** (sort fold; **no extra RI axioms**) + **`RI_semantic_type_mismatch_fromRepresentational`** (`SPEC_020`) + certificates (**`lake require «representational-incompleteness»`** **on**).
- **Invariants.HomeomorphTransport:** chart transport lemmas specializing `Equiv` invariants through `X ≃ₜ Y`.

---

## Honest limits

1. **IterInjective** is a **hypothesis**, not a consequence of choosing an arbitrary `represent : A ⟶ A` (same mathematical situation as the **RI** line).
2. **Lake dependency:** **`«representational-incompleteness»`** is **`require`d** (SPEC_004 step **2**). **Promoted** summit lemmas still **prefer** living in **RI**; bump `lakefile.lean` **rev** when **RI** refactors and **re-verify** `Examples/RepresentationalIncompleteness`.
3. **`Pressure.not_surjective_curry_into_nat`** uses `A : Type` (`Type 0`) with codomain **`Nat`** (same universe). For the same `MonoidalClosed (Type u)` story with **`A : Type u`**, use **`Pressure.not_surjective_curry_into_uliftNat`** / **`not_universal_binary_into_uliftNat`** (codomain **`ULift.{u} Nat`**). For unary `A → Nat` enumeration without `MonoidalClosed`, see **`LawvereType`** (`lawvere_no_universal_unary_into_nat`).

---

## See also

- `ARTIFACT.md` — citation / reproduction  
- `specs/README.md` — where workspace EPICs live when using the submodule layout  
