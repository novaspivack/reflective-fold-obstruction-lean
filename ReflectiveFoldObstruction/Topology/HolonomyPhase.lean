/-
  **Holonomy + phase counter** (`SPEC_011` Part B).

  States pair a **Boolean holonomy tag** with a **`ℕ`** phase counter. Primitive steps **fix**
  the tag and advance the counter by **0** or **1**, but **+1** is legal only while
  `phase < bound` — an internal calculus discipline parallel to the open–compact witness gate.

  Invariant **`HolonomyTrivialBounded`**: trivial tag and counter within budget. Target
  `phase = bound + 1` is unreachable from the zero seed under preservation.
-/

import Mathlib.Logic.Relation

import ReflectiveFoldObstruction.Core.ArchitectureObstruction
import ReflectiveFoldObstruction.Obstruction.Fold
import ReflectiveFoldObstruction.Reachability.InternalOps

universe u

namespace ReflectiveFoldObstruction.Topology.HolonomyPhase

open Relation
open ReflectiveFoldObstruction.Obstruction.Fold
open ReflectiveFoldObstruction.Reachability.InternalOps

/-- Tag (trivial vs twist) + nonnegative phase counter. -/
structure HolonomyState : Type where
  trivial : Bool
  phase : ℕ

variable (bound : ℕ)

/-- Preserve `trivial`; stay or increment phase by **1** only when **below** `bound`. -/
def holonomyPhaseStep (bound : ℕ) (s t : HolonomyState) : Prop :=
  s.trivial = t.trivial ∧
    (t.phase = s.phase ∨ (t.phase = s.phase + 1 ∧ s.phase < bound))

/-- Trivial holonomy tag and phase not past the budget. -/
def HolonomyTrivialBounded (bound : ℕ) (s : HolonomyState) : Prop :=
  s.trivial = true ∧ s.phase ≤ bound

variable {bound : ℕ}

theorem holonomy_phase_step_preserves_trivialTag ⦃s t : HolonomyState⦄
    (h : holonomyPhaseStep bound s t) (hs : HolonomyTrivialBounded bound s) :
    HolonomyTrivialBounded bound t := by
  rcases h with ⟨htriv, hphase⟩
  rcases hs with ⟨htriv_s, hphase_s⟩
  rcases hphase with hph | ⟨hph, hlt⟩
  · refine ⟨htriv.symm.trans htriv_s, ?_⟩
    rw [hph]
    exact hphase_s
  · have htph : t.phase = Nat.succ s.phase := by simpa [Nat.succ_eq_add_one] using hph
    refine ⟨htriv.symm.trans htriv_s, ?_⟩
    rw [htph]
    exact Nat.succ_le_iff.mpr hlt

theorem holonomy_phase_forwardClosed :
    PreservedBy (holonomyPhaseStep bound) (HolonomyTrivialBounded bound) := by
  intro s t hst hs
  exact holonomy_phase_step_preserves_trivialTag hst hs

theorem holonomy_phase_dynamic_fold_obstruction :
    ¬ ReflTransGen (holonomyPhaseStep bound)
      (HolonomyState.mk true 0) (HolonomyState.mk true (bound + 1)) := by
  refine Core.ArchitectureObstruction.architecture_fold_obstruction_of_invariant_mismatch
    holonomy_phase_forwardClosed ?_ ?_
  · simp [HolonomyTrivialBounded]
  · intro ⟨_, hp⟩
    exact Nat.not_succ_le_self bound hp

end ReflectiveFoldObstruction.Topology.HolonomyPhase
