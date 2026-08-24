/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Lattice

/-!
# Join-semidirect transport labels

If a monoid acts on a join-semilattice with bottom and preserves joins and
bottom, pairs `(floor, action)` act by `x ↦ floor ⊔ action • x`.
Chronological composition is the semidirect product

`(b, a) * (c, d) = (b ⊔ a • c, a * d)`.

The resulting labels form a monoid whose multiplication agrees with
composition of their actions.  Max-affine labels with nonnegative slope are a
special case.

## Main definitions

* `DirectedTransport.SupBotMulAction`: a monoid action on a join-semilattice with bottom
  that preserves binary joins and the bottom element.
* `DirectedTransport.JoinSemidirectTransport.Label`: a floor together with an acting monoid
  element, with `DirectedTransport.JoinSemidirectTransport.Label.apply` for its action and
  `DirectedTransport.JoinSemidirectTransport.Label.comp` for chronological composition.
* `DirectedTransport.JoinSemidirectTransport.Label.instMonoid`: the semidirect-product
  monoid structure on labels.

## Main results

* `DirectedTransport.JoinSemidirectTransport.Label.apply_comp`: composition of labels
  agrees with composition of their actions.
* `DirectedTransport.JoinSemidirectTransport.Label.instMulAction`: labels act on the
  underlying semilattice through `apply`.
-/

@[expose] public section

namespace DirectedTransport

noncomputable section


universe uA uL

/-- A monoid action preserving binary joins and bottom. -/
class SupBotMulAction (A : Type uA) (L : Type uL)
    [Monoid A] [SemilatticeSup L] [OrderBot L] extends MulAction A L where
  smul_sup (action : A) (first second : L) :
    action • (first ⊔ second) = action • first ⊔ action • second
  smul_bot (action : A) : action • (⊥ : L) = ⊥

namespace JoinSemidirectTransport

variable {A : Type uA} {L : Type uL}
variable [Monoid A] [SemilatticeSup L] [OrderBot L] [SupBotMulAction A L]

/-- A floor joined with the image of a monoid action. -/
@[ext] structure Label (L : Type uL) (A : Type uA) where
  floor : L
  action : A

namespace Label

/-- Action of a join-semidirect label. -/
def apply (label : Label L A) (point : L) : L :=
  label.floor ⊔ label.action • point

/-- Chronological composition: `outer.comp inner` applies `inner` first. -/
def comp (outer inner : Label L A) : Label L A where
  floor := outer.floor ⊔ outer.action • inner.floor
  action := outer.action * inner.action

/-- Identity join-semidirect label. -/
def id : Label L A := ⟨⊥, 1⟩

@[simp] theorem floor_comp (outer inner : Label L A) :
    (outer.comp inner).floor = outer.floor ⊔ outer.action • inner.floor := rfl

@[simp] theorem action_comp (outer inner : Label L A) :
    (outer.comp inner).action = outer.action * inner.action := rfl

@[simp] theorem apply_comp (outer inner : Label L A) (point : L) :
    (outer.comp inner).apply point = outer.apply (inner.apply point) := by
  simp only [apply, floor_comp, action_comp, SupBotMulAction.smul_sup, mul_smul]
  rw [sup_assoc]

theorem comp_assoc (first second third : Label L A) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  apply Label.ext
  · simp only [floor_comp, action_comp, SupBotMulAction.smul_sup, mul_smul]
    rw [sup_assoc]
  · simp [mul_assoc]

@[simp] theorem id_comp (label : Label L A) : id.comp label = label := by
  apply Label.ext
  · simp [id]
  · simp [id]

@[simp] theorem comp_id (label : Label L A) : label.comp id = label := by
  apply Label.ext
  · simp [id, SupBotMulAction.smul_bot]
  · simp [id]

instance instMonoid : Monoid (Label L A) where
  one := id
  mul := comp
  one_mul := id_comp
  mul_one := comp_id
  mul_assoc := comp_assoc

instance instSMul : SMul (Label L A) L where
  smul label point := label.apply point

instance instMulAction : MulAction (Label L A) L where
  one_smul point := by
    change id.apply point = point
    simp [id, apply]
  mul_smul outer inner point := by
    change (outer.comp inner).apply point = outer.apply (inner.apply point)
    exact apply_comp outer inner point

end Label

end JoinSemidirectTransport

end

end DirectedTransport
