/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Algebra.JoinSemidirect
public import Maths.Multitubes.MaxAffine.Basic

/-!
# Max-affine labels as a join-semidirect product

Nonnegative affine summaries act on `WithBot ℝ` by pushing finite floors
forward and preserving `⊥`.  The resulting join-semidirect labels are
multiplicatively equivalent to max-affine labels with nonnegative slope.  Under
this equivalence, the join-semidirect action agrees with max-affine evaluation
on finite points.

## Main definitions

* `Maths.MaxAffineJoinAdapter.NonnegativeAffine`,
  `Maths.MaxAffineJoinAdapter.NonnegativeLabel`,
  `Maths.MaxAffineJoinAdapter.AbstractLabel`: the three carriers being related.
* `Maths.MaxAffineJoinAdapter.instSupBotMulAction`: nonnegative affine summaries
  acting on `WithBot ℝ` preserving binary joins and `⊥`.
* `Maths.MaxAffineJoinAdapter.labelEquiv` and
  `Maths.MaxAffineJoinAdapter.labelMulEquiv`: the equivalence with max-affine
  labels of nonnegative slope, as an equivalence and as a monoid isomorphism.

## Main results

* `Maths.MaxAffineJoinAdapter.abstractApply_eq_applyBot`: the join-semidirect
  action agrees with max-affine evaluation on finite points.
-/

@[expose] public section

namespace Maths

noncomputable section

namespace MaxAffineJoinAdapter

open MaxAffineTransport

/-- Nonnegative affine summaries, used as the action monoid. -/
abbrev NonnegativeAffine := MaxAffineTransport.Label.affineNonnegSubmonoid

/-- Max-affine labels with nonnegative slope. -/
abbrev NonnegativeLabel := {label : MaxAffineTransport.Label // 0 ≤ label.slope}

/-- Abstract join-semidirect labels specialized to max-affine floors and
nonnegative affine actions. -/
abbrev AbstractLabel :=
  JoinSemidirectTransport.Label (WithBot ℝ) NonnegativeAffine

instance instSMulWithBot : SMul NonnegativeAffine (WithBot ℝ) where
  smul action floor := MaxAffineTransport.Label.pushFloor
    action.1.shift action.1.slope floor

instance instMulActionWithBot : MulAction NonnegativeAffine (WithBot ℝ) where
  one_smul floor := by
    change MaxAffineTransport.Label.pushFloor 0 1 floor = floor
    exact MaxAffineTransport.Label.pushFloor_id floor
  mul_smul outer inner floor := by
    change MaxAffineTransport.Label.pushFloor
        (outer.1.shift + outer.1.slope * inner.1.shift)
        (outer.1.slope * inner.1.slope) floor =
      MaxAffineTransport.Label.pushFloor outer.1.shift outer.1.slope
        (MaxAffineTransport.Label.pushFloor
          inner.1.shift inner.1.slope floor)
    rw [MaxAffineTransport.Label.pushFloor_pushFloor]

instance instSupBotMulAction : SupBotMulAction NonnegativeAffine (WithBot ℝ) where
  smul_sup action first second :=
    MaxAffineTransport.Label.pushFloor_sup action.2 action.1.shift first second
  smul_bot _ := MaxAffineTransport.Label.pushFloor_bot _ _

/-- Coefficient equivalence between join-semidirect labels and nonnegative
max-affine labels. -/
def labelEquiv : AbstractLabel ≃ NonnegativeLabel where
  toFun label :=
    ⟨⟨label.floor, label.action.1.shift, label.action.1.slope⟩,
      label.action.2⟩
  invFun label :=
    ⟨label.1.floor,
      ⟨⟨label.1.shift, label.1.slope⟩, label.2⟩⟩
  left_inv label := by
    rcases label with ⟨floor, ⟨⟨shift, slope⟩, hslope⟩⟩
    rfl
  right_inv label := by
    rcases label with ⟨⟨floor, shift, slope⟩, hslope⟩
    rfl

/-- The coefficient equivalence respects chronological composition. -/
def labelMulEquiv : AbstractLabel ≃* NonnegativeLabel where
  toEquiv := labelEquiv
  map_mul' outer inner := by
    apply Subtype.ext
    apply MaxAffineTransport.Label.ext
    · rfl
    · rfl
    · rfl

/-- Join-semidirect evaluation agrees with `WithBot`-valued max-affine
evaluation on finite points. -/
theorem abstractApply_eq_applyBot (label : AbstractLabel) (point : ℝ) :
    JoinSemidirectTransport.Label.apply label (point : WithBot ℝ) =
      (labelEquiv label).1.applyBot point := by
  rfl

end MaxAffineJoinAdapter

end

end Maths
