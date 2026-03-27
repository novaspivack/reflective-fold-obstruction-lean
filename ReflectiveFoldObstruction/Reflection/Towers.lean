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

/-- Same datum as `regress_iterates_unbounded`: above any `bound`, a higher stage has a **different**
    regress arrow than at `bound`. This is the right informal reading of an “infinite tower” at the
    level-map layer (not merely “some larger natural number exists”). -/
theorem regress_is_infinite (R : Core.ReflectiveSystem) (hij : Core.IterInjective R) (bound : ℕ) :
    ∃ level : ℕ, bound < level ∧ Core.metaRegressArrow R level ≠ Core.metaRegressArrow R bound :=
  regress_iterates_unbounded R hij bound

/-- There is a stage **strictly above** `bound` whose arrow is **new relative to every stage**
    `i ≤ bound` — so the image of `metaRegressArrow` cannot be covered by any initial segment
    `{0,…,bound}`. Strictly stronger than differing only from `metaRegressArrow R bound`. -/
theorem meta_range_infinite (R : Core.ReflectiveSystem) (hij : Core.IterInjective R) (bound : ℕ) :
    ∃ level : ℕ, bound < level ∧
      ∀ i ≤ bound, Core.metaRegressArrow R level ≠ Core.metaRegressArrow R i :=
  let level := bound + 1
  ⟨level, Nat.lt_succ_self bound, fun i hi =>
    Core.metaRegressArrow_injective R hij
      (Ne.symm (Nat.ne_of_lt (show i < level from Nat.lt_succ_of_le hi)))⟩

end ReflectiveFoldObstruction.Reflection.Towers
