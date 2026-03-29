/-
  **Instance 2 — adjudication class** (`SPEC_020`).

  States carry a **kind** (e.g. total-effective vs non–total-effective) that does not change
  under internal steps — an abstraction of the NEMS Class I / II split without importing _nems_.

  See `SPEC_020` (“bridge to nems-lean” is narrative; formalization is this minimally committal layer).
-/

import Mathlib.Logic.Relation

import ReflectiveFoldObstruction.Obstruction.Fold
import ReflectiveFoldObstruction.Reachability.InternalOps
import ReflectiveFoldObstruction.SemanticType.Core

universe u

namespace ReflectiveFoldObstruction.SemanticType.Instances.AdjudicationType

open Relation
open Reachability.InternalOps
open Obstruction.Fold

/-- Discrete adjudication tags (NEMS-flavoured **labels only**). -/
inductive AdjudicationClass : Type
  /-- Class I-style: total-effective adjudication at choice points. -/
  | totalEffective
  /-- Strictly weaker adjudication behaviour (Class II flavour). -/
  | nonTotalEffective
  deriving DecidableEq

variable {α : Type u}

/-- Dynamics **respects adjudication kind** along every primitive step. -/
structure AdjudicationDynamics (α : Type u) where
  adjudicationKind : α → AdjudicationClass
  primitiveStep : α → α → Prop
  step_preserves_kind :
    ∀ ⦃s s'⦄, primitiveStep s s' → adjudicationKind s = adjudicationKind s'

variable (A : AdjudicationDynamics α)

def toTyping : Typing α where
  Tag := AdjudicationClass
  InstantiatesType s c := A.adjudicationKind s = c
  primitiveStep := A.primitiveStep
  typePreservedByStep := by
    intro s s' t hstep ht
    simp [← ht, A.step_preserves_kind hstep]

theorem adjudicationType_typePreserved (c : AdjudicationClass) :
    PreservedBy A.primitiveStep (fun x => A.adjudicationKind x = c) := by
  intro s s' hstep hc
  simp [← hc, A.step_preserves_kind hstep]

theorem adjudication_type_ne : AdjudicationClass.totalEffective ≠ AdjudicationClass.nonTotalEffective :=
  fun h => by cases h

theorem adjudicationType_obstruction {s s' : α} {c c' : AdjudicationClass} (hne : c ≠ c')
    (hs : A.adjudicationKind s = c) (hs' : A.adjudicationKind s' = c') :
    ¬ ReflTransGen A.primitiveStep s s' :=
  fold_obstruction_of_invariant_mismatch (adjudicationType_typePreserved A c) hs
    fun hbad => hne (Eq.trans hbad.symm hs')

theorem adjudication_total_to_nonTotal_typeGap :
    typeGap (toTyping A) AdjudicationClass.totalEffective
      AdjudicationClass.nonTotalEffective := by
  rintro ⟨s, s', hs, hs', hreach⟩
  exact adjudicationType_obstruction A adjudication_type_ne hs hs' hreach

theorem adjudication_semantic_obstruction :
    SemanticTypeObstruction (toTyping A) AdjudicationClass.totalEffective
      AdjudicationClass.nonTotalEffective :=
  ⟨adjudication_total_to_nonTotal_typeGap A⟩

end ReflectiveFoldObstruction.SemanticType.Instances.AdjudicationType
