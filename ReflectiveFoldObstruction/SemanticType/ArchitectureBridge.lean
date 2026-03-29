/-
  **Architecture bundles ↔ bipartite semantic typing** (`SPEC_017` × `SPEC_020`).

  When both `P` and `¬ P` are forward-closed, the state space splits into two invariant
  **zones**; the `Bool` tag typing has a permanent gap.  This is the honest generic bridge to
  `FoldObstructionBundle` (strengthened with a `¬Inv` preservation hypothesis).
-/

import Mathlib.Logic.Relation

import ReflectiveFoldObstruction.Obstruction.Fold
import ReflectiveFoldObstruction.Reachability.ArchitectureClasses
import ReflectiveFoldObstruction.Reachability.InternalOps
import ReflectiveFoldObstruction.SemanticType.Core

universe u

namespace ReflectiveFoldObstruction.SemanticType

open Relation
open Reachability.ArchitectureClasses
open Reachability.InternalOps
open Obstruction.Fold

variable {α : Type u}

/-- Both half-spaces of a predicate are primitive-stable (no `P ↔ ¬ P` crossing). -/
structure BipartitionDyn (α : Type u) where
  rel : α → α → Prop
  P : α → Prop
  hp : PreservedBy rel P
  hneg : PreservedBy rel (fun x => ¬ P x)

def BipartitionDyn.toTyping (D : BipartitionDyn α) : Typing α where
  Tag := Bool
  InstantiatesType s b := cond b (D.P s) (¬ D.P s)
  primitiveStep := D.rel
  typePreservedByStep := by
    intro s s' t h ht
    cases t with
    | false => exact D.hneg h ht
    | true => exact D.hp h ht

theorem typeGap_bipartition_tt_ff (D : BipartitionDyn α) : typeGap D.toTyping true false := by
  rintro ⟨s, s', hs, hs', hreach⟩
  have hs'' : D.P s' := ReflTransGen.forwardClosed D.hp hreach hs
  exact hs' hs''

theorem SemanticTypeObstruction_bipartition (D : BipartitionDyn α) :
    SemanticTypeObstruction D.toTyping true false :=
  ⟨typeGap_bipartition_tt_ff D⟩

/-- From a fold bundle, when **both** `Inv` and `¬Inv` are step-closed (sharp partition). -/
def BipartitionDyn.ofFoldBundle (B : FoldObstructionBundle α)
    (hp : PreservedBy B.rel B.Inv) (hneg : PreservedBy B.rel fun x => ¬ B.Inv x) :
    BipartitionDyn α :=
  ⟨B.rel, B.Inv, hp, hneg⟩

theorem fold_bundle_typeGap {B : FoldObstructionBundle α}
    (hp : PreservedBy B.rel B.Inv) (hneg : PreservedBy B.rel fun x => ¬ B.Inv x) :
    typeGap (BipartitionDyn.ofFoldBundle B hp hneg).toTyping true false :=
  typeGap_bipartition_tt_ff _

theorem not_reflTransGen_of_inv_mismatch {B : FoldObstructionBundle α}
    (hp : PreservedBy B.rel B.Inv) (hneg : PreservedBy B.rel fun x => ¬ B.Inv x)
    (hS : B.Inv B.S) (hT : ¬ B.Inv B.T) :
    ¬ ReflTransGen B.rel B.S B.T := by
  have hgap := fold_bundle_typeGap (B := B) hp hneg
  exact not_reflTransGen_of_typeGap (BipartitionDyn.ofFoldBundle B hp hneg |>.toTyping) hgap hS hT

end ReflectiveFoldObstruction.SemanticType
