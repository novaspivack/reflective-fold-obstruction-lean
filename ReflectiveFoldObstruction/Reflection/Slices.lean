/-
  **Slice** consequences: distinct indices give distinct objects of `Over A`.
-/

import ReflectiveFoldObstruction.Core.Basic

namespace ReflectiveFoldObstruction.Reflection.Slices

theorem regress_over_injective (R : Core.ReflectiveSystem) (hij : Core.IterInjective R)
    ⦃n m : ℕ⦄ (h : n ≠ m) : Core.metaOver R n ≠ Core.metaOver R m :=
  Core.metaOver_injective R hij h

end ReflectiveFoldObstruction.Reflection.Slices
