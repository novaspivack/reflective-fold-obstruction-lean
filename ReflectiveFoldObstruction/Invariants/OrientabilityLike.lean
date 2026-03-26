/-
  **Orientability-like / parity gauges** — surrogate twist data before committing to a full
  manifold-orientation API (`Orientation` bundles, `ZMod 2` principal bundles, …).

  A **parity gauge** is just `α → Bool`.  Transport along `Equiv` matches the `BoundaryType`
  typing story: compose with `symm`.  “No monodromy” is **local constancy** — every chart
  agrees — while **twist witnesses** are `∃ x y, p x ≠ p y`.

  For cylinder vs Möbius flagship geometry, see `Topology/MobiusCylinder.lean`.

  See `specs/NOTES/PROJECT_VISION.md` — Invariants/OrientabilityLike.
-/

import Mathlib.Logic.Equiv.Defs

universe u

namespace ReflectiveFoldObstruction.Invariants.OrientabilityLike

open Equiv

variable {α β γ : Type u}

/-- A `Bool`-valued **parity gauge** on `α` (abstract 2-sheet / orientation sheet labelling). -/
abbrev ParityGauge (α : Type u) :=
  α → Bool

/-- Push a gauge on `α` to `β` along `e`. -/
def transportGauge (e : α ≃ β) (p : ParityGauge α) : ParityGauge β :=
  fun b => p (e.symm b)

@[simp] theorem transportGauge_apply (e : α ≃ β) (p : ParityGauge α) (b : β) :
    transportGauge e p b = p (e.symm b) :=
  rfl

theorem transportGauge_rfl (p : ParityGauge α) : transportGauge (Equiv.refl α) p = p := by
  funext x
  simp [transportGauge]

theorem transportGauge_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) (p : ParityGauge α) :
    transportGauge (e₁.trans e₂) p = transportGauge e₂ (transportGauge e₁ p) := by
  funext x
  simp [transportGauge]

theorem transportGauge_map_symm (e : α ≃ β) (p : ParityGauge α) :
    transportGauge e.symm (transportGauge e p) = p := by
  funext x
  simp [transportGauge, symm_symm, symm_apply_apply]

theorem transportGauge_map (e : α ≃ β) (p : ParityGauge β) :
    transportGauge e (transportGauge e.symm p) = p := by
  funext x
  simp [transportGauge, symm_symm, apply_symm_apply]

/-- The gauge is constant (single sheet / “no monodromy class internally”). -/
def IsLocallyConstant (p : ParityGauge α) : Prop :=
  ∀ x y : α, p x = p y

/-- There exist two points with opposite labels — a **twist conflict** / sheet mismatch. -/
def HasTwistWitness (p : ParityGauge α) : Prop :=
  ∃ x y : α, p x ≠ p y

theorem IsLocallyConstant_iff_not_hasTwistWitness (p : ParityGauge α) :
    IsLocallyConstant p ↔ ¬HasTwistWitness p := by
  simp [IsLocallyConstant, HasTwistWitness, not_exists]

theorem IsLocallyConstant.transport_iff (e : α ≃ β) (p : ParityGauge α) :
    IsLocallyConstant p ↔ IsLocallyConstant (transportGauge e p) := by
  constructor
  · intro h x y
    simpa [transportGauge, apply_symm_apply, h] using h (e.symm x) (e.symm y)
  · intro h x y
    simpa [transportGauge, apply_symm_apply, h] using h (e x) (e y)

theorem HasTwistWitness.transport_iff (e : α ≃ β) (p : ParityGauge α) :
    HasTwistWitness p ↔ HasTwistWitness (transportGauge e p) := by
  constructor
  · rintro ⟨x, y, hn⟩
    refine ⟨e x, e y, ?_⟩
    simpa [transportGauge, apply_symm_apply] using hn
  · rintro ⟨x, y, hn⟩
    refine ⟨e.symm x, e.symm y, ?_⟩
    simpa [transportGauge] using hn

end ReflectiveFoldObstruction.Invariants.OrientabilityLike
