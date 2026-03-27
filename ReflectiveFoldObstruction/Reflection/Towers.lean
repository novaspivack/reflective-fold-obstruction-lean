/-
  Reflective **towers**: consequences of `IterInjective` for iterates of `represent`.

  Mirrors the RI **regress** tower API with explicit `hij : IterInjective R` hypotheses
  (`specs/COMPLETE/SPEC_003_RFO` — structure vs hypothesis split).
-/

import Mathlib.Data.Nat.Basic
import ReflectiveFoldObstruction.Core.Basic

namespace ReflectiveFoldObstruction.Reflection.Towers

theorem regress_no_termination (R : Core.ReflectiveSystem) (hij : Core.IterInjective R)
    ⦃n m : ℕ⦄ (h : n ≠ m) :
    Core.metaRegressArrow R n ≠ Core.metaRegressArrow R m :=
  Core.metaRegressArrow_injective R hij h

theorem regress_iterates_unbounded (R : Core.ReflectiveSystem) (hij : Core.IterInjective R)
    (bound : ℕ) :
    ∃ level : ℕ, bound < level ∧ Core.metaRegressArrow R level ≠ Core.metaRegressArrow R bound :=
  ⟨Nat.succ bound, Nat.lt_succ_self bound,
   Core.metaRegressArrow_injective R hij (Nat.succ_ne_self bound)⟩

theorem regress_is_infinite (R : Core.ReflectiveSystem) (_hij : Core.IterInjective R)
    (bound : ℕ) :
    ∃ level : ℕ, bound < level ∧ ∃ _obj : R.C, True :=
  ⟨bound + 1, Nat.lt_succ_self bound, R.A, trivial⟩

theorem meta_range_infinite (R : Core.ReflectiveSystem) (_hij : Core.IterInjective R)
    (bound : ℕ) : ∃ level : ℕ, bound < level :=
  ⟨bound + 1, Nat.lt_succ_self bound⟩

end ReflectiveFoldObstruction.Reflection.Towers
