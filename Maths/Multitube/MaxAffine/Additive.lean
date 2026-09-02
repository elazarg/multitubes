/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitube.Additive.Exact
public import Maths.Multitube.MaxAffine.Basic

/-!
# Additive transport as unit-slope max-affine transport

Floorless unit-slope max-affine labels are translations. This module identifies
their lax sections, residuals, exact sections, and walk transport with additive
potentials, coboundaries, and walk sums.

## Main results

* `Maths.MaxAffineTransport.isLaxSection_translationLabel_iff`: a lax section for
  translation labels is exactly an additive potential.
* `Maths.MaxAffineTransport.defect_translationLabel`: the max-affine defect of a
  translation label is the additive defect of its weight.
* `Maths.MaxAffineTransport.isCoboundary_iff_exists_translation_defect_eq_zero`:
  edge weights are a coboundary exactly when some translation-labelled candidate has zero
  defect on every edge.
* `Maths.MaxAffineTransport.holonomyApply_translationLabel`: translation transport
  along a walk is addition of the walk weight.
-/

@[expose] public section

noncomputable section

namespace Maths.MaxAffineTransport

universe uV uE

variable {V : Type uV} {E : Type uE} {G : Maths.EdgeGraph V E}

/-- A lax section for translation labels is exactly an additive potential. -/
theorem isLaxSection_translationLabel_iff
    (G : EdgeGraph V E) (weight : E → ℝ) (potential : V → ℝ) :
    IsLaxSection G (fun edge => translationLabel (weight edge)) potential ↔
      Maths.MaxPlusPotential.IsPotential G weight potential := by
  simp only [IsLaxSection, Maths.MaxPlusPotential.IsPotential, apply_translationLabel]
  exact forall_congr' fun edge => ⟨fun h => by linarith, fun h => by linarith⟩

@[simp] theorem defect_translationLabel
    (G : EdgeGraph V E) (weight : E → ℝ) (potential : V → ℝ) (edge : E) :
    defect G (fun next => translationLabel (weight next)) potential edge =
      Maths.MaxPlusPotential.defect G weight potential edge := by
  simp only [defect, Maths.MaxPlusPotential.defect, apply_translationLabel]
  ring

/-- Edge data is a coboundary exactly when some translation-labelled candidate
has zero defect on every edge. -/
theorem isCoboundary_iff_exists_translation_defect_eq_zero
    (G : EdgeGraph V E) (weight : E → ℝ) :
    Maths.CycleCoboundary.IsCoboundary G weight ↔
      ∃ potential : V → ℝ,
        ∀ edge : E,
          defect G (fun next => translationLabel (weight next)) potential edge = 0 := by
  rw [Maths.CycleCoboundary.isCoboundary_iff_exists_defect_eq_zero]
  simp only [defect_translationLabel]

/-- Translation transport is addition of the walk weight. -/
theorem holonomyApply_translationLabel
    (weight : E → ℝ) {start finish : V} (walk : G.Walk start finish) (point : ℝ) :
    holonomyApply (fun edge => translationLabel (weight edge)) walk point =
      point + Maths.MaxPlusPotential.walkWeight weight walk := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih =>
      rw [holonomyApply_concat, ih, apply_translationLabel,
        Maths.MaxPlusPotential.walkWeight_concat]
      ring

end Maths.MaxAffineTransport

end
