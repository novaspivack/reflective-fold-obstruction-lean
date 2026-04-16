/-
  **Example hook for slot non-collapse** — re-exports the polymorphic API from `Core/Slots`.

  Concrete **RI** instantiations stay in `representational-incompleteness-lean` per SPEC_002; this module proves nothing
  new — it anchors documentation that *all* `ReflectiveSystem` hosts inherit the same lemmas.

  Module context: Examples/NoCollapse.
-/

import ReflectiveFoldObstruction.Core.Basic
import ReflectiveFoldObstruction.Core.Slots
import ReflectiveFoldObstruction.Invariants.SortSeparation

namespace ReflectiveFoldObstruction.Examples.NoCollapse

open Core Slots Invariants

variable (R : ReflectiveSystem)

/-- Slots along the representation arrow never collapse into the `A` object branch. -/
theorem represent_mor_ne_obj_A :
    @OntologicalSlot.mor R.C (R.A ⟶ R.A) R.represent ≠
      @OntologicalSlot.obj R.C (R.A ⟶ R.A) R.A :=
  SortSeparation.represent_slot_disjoint_from_obj_A R

end ReflectiveFoldObstruction.Examples.NoCollapse
