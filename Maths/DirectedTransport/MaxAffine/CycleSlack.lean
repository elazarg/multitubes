/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.MaxAffine.Paths

/-!
# Exact uniform slack for one max-affine cycle

Subtracting a common edge slack from both branches of every label converts the
cyclic slack problem into an ordinary pre-fixed-point problem for one composite
label.  The exact threshold equivalence also covers an optimum that is
unbounded below.  Combining it with
`Maths.MaxAffineTransport.Label.compList_eq_pathCoefficients` and the complete
scalar classification computes every finite cycle without introducing a fake real value for
`-∞`.

## Main definitions

* `Maths.MaxAffineTransport.Label.relax`: a label with a common slack subtracted
  from both branches.
* `Maths.MaxAffineTransport.Label.IsSlackChain` and
  `Maths.MaxAffineTransport.Label.HasCyclicSlack`: the cyclic slack problem.
* `Maths.MaxAffineTransport.Label.relaxedOrbitSteps` and
  `Maths.MaxAffineTransport.Label.closeLastTarget`: the canonical chain
  realizing a slack level, and its closure at a chosen terminal value.

## Main results

* `Maths.MaxAffineTransport.Label.hasCyclicSlack_iff_compList_relaxed_prefixed`:
  cyclic slack is a pre-fixed-point problem for one composite relaxed label.
* `Maths.MaxAffineTransport.Label.hasCyclicSlack_iff_pathCoefficient_prefixed`:
  the same test read off the path coefficients.
* `Maths.MaxAffineTransport.Label.hasCyclicSlack_iff_coefficient_trichotomy`:
  the complete scalar classification, covering the optimum unbounded below.
-/

@[expose] public section

namespace Maths

noncomputable section

namespace MaxAffineTransport
namespace Label

/-- Subtract a common slack from the two output branches of a label. -/
def relax (level : ℝ) (label : Label) : Label :=
  recenter label 0 level

@[simp] theorem slope_relax (level : ℝ) (label : Label) :
    (relax level label).slope = label.slope := rfl

/-- Relaxation subtracts exactly `level` from the output. -/
theorem apply_relax (level : ℝ) (label : Label) (point : ℝ) :
    (relax level label).apply point = label.apply point - level := by
  simpa [relax] using apply_recenter label 0 level point

/-- Edgewise slack inequalities along a proposed candidate chain. -/
def IsSlackChain (level : ℝ) : ℝ → List CandidateStep → Prop
  | _, [] => True
  | source, (label, target) :: rest =>
      label.apply source - target ≤ level ∧ IsSlackChain level target rest

/-- A closed candidate chain for a chronological list of labels, with every
edge residual at most `level`. -/
def HasCyclicSlack (labels : List Label) (level : ℝ) : Prop :=
  ∃ (source : ℝ) (steps : List CandidateStep),
    chainLabels steps = labels ∧
      chainTarget source steps = source ∧ IsSlackChain level source steps

/-- Exact orbit targets for the relaxed labels, retained together with the
original labels. -/
def relaxedOrbitSteps (level : ℝ) : ℝ → List Label → List CandidateStep
  | _, [] => []
  | source, label :: rest =>
      let target := (relax level label).apply source
      (label, target) :: relaxedOrbitSteps level target rest

@[simp] theorem chainLabels_relaxedOrbitSteps (level source : ℝ)
    (labels : List Label) :
    chainLabels (relaxedOrbitSteps level source labels) = labels := by
  induction labels generalizing source with
  | nil => rfl
  | cons label rest ih =>
      simp only [relaxedOrbitSteps, chainLabels, List.map_cons]
      change label :: chainLabels
        (relaxedOrbitSteps level ((relax level label).apply source) rest) =
          label :: rest
      rw [ih]

theorem chainTarget_relaxedOrbitSteps (level source : ℝ) :
    ∀ labels : List Label,
      chainTarget source (relaxedOrbitSteps level source labels) =
        (labels.map (relax level)).foldl
          (fun point label => label.apply point) source
  | [] => rfl
  | label :: rest => by
      simp only [relaxedOrbitSteps, chainTarget, List.map_cons, List.foldl_cons]
      exact chainTarget_relaxedOrbitSteps level
        ((relax level label).apply source) rest

theorem isSlackChain_relaxedOrbitSteps (level source : ℝ)
    (labels : List Label) :
    IsSlackChain level source (relaxedOrbitSteps level source labels) := by
  induction labels generalizing source with
  | nil => trivial
  | cons label rest ih =>
      simp only [relaxedOrbitSteps, IsSlackChain]
      refine ⟨?_, ih ((relax level label).apply source)⟩
      rw [apply_relax]
      linarith

/-- Replace only the terminal target of a chain. -/
def closeLastTarget (terminal : ℝ) : List CandidateStep → List CandidateStep
  | [] => []
  | [step] => [(step.1, terminal)]
  | step :: next :: rest => step :: closeLastTarget terminal (next :: rest)

@[simp] theorem chainLabels_closeLastTarget (terminal : ℝ) :
    ∀ steps : List CandidateStep,
      chainLabels (closeLastTarget terminal steps) = chainLabels steps
  | [] => rfl
  | [step] => by simp [closeLastTarget, chainLabels]
  | step :: next :: rest => by
      simp only [closeLastTarget, chainLabels, List.map_cons]
      change step.1 :: chainLabels (closeLastTarget terminal (next :: rest)) =
        step.1 :: chainLabels (next :: rest)
      rw [chainLabels_closeLastTarget terminal (next :: rest)]

@[simp] theorem chainTarget_closeLastTarget (terminal source : ℝ) :
    ∀ steps : List CandidateStep,
      chainTarget source (closeLastTarget terminal steps) =
        if steps = [] then source else terminal
  | [] => rfl
  | [step] => by simp [closeLastTarget, chainTarget]
  | step :: next :: rest => by
      simp only [closeLastTarget, chainTarget, List.cons_ne_nil, ↓reduceIte]
      rw [chainTarget_closeLastTarget terminal step.2 (next :: rest)]
      simp

/-- Raising the terminal target to a larger value preserves all slack
inequalities and makes the chain literally close. -/
theorem isSlackChain_closeLastTarget {level source terminal : ℝ}
    {steps : List CandidateStep} (hchain : IsSlackChain level source steps)
    (hterminal : chainTarget source steps ≤ terminal) :
    IsSlackChain level source (closeLastTarget terminal steps) := by
  induction steps generalizing source with
  | nil => trivial
  | cons first rest ih =>
      rcases first with ⟨label, target⟩
      rcases hchain with ⟨hfirst, hrest⟩
      cases rest with
      | nil =>
          simp only [chainTarget] at hterminal
          simp only [closeLastTarget, IsSlackChain]
          exact ⟨by linarith, trivial⟩
      | cons next tail =>
          simp only [closeLastTarget, IsSlackChain]
          refine ⟨hfirst, ih hrest ?_⟩
          simpa only [chainTarget] using hterminal

private theorem monotone_foldl_apply {labels : List Label}
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope) :
    Monotone fun point =>
      labels.foldl (fun value label => label.apply value) point := by
  intro left right hle
  induction labels generalizing left right with
  | nil => exact hle
  | cons label rest ih =>
      apply ih
      · exact fun candidate hc => hslope candidate (List.mem_cons_of_mem _ hc)
      · exact Label.monotone_apply
          (hslope label (List.mem_cons_self ..)) hle

private theorem relaxed_foldl_le_chainTarget {level source : ℝ}
    {steps : List CandidateStep}
    (hslope : ∀ step ∈ steps, 0 ≤ step.1.slope)
    (hchain : IsSlackChain level source steps) :
    ((chainLabels steps).map (relax level)).foldl
        (fun point label => label.apply point) source ≤
      chainTarget source steps := by
  induction steps generalizing source with
  | nil => exact le_rfl
  | cons first rest ih =>
      rcases first with ⟨label, target⟩
      rcases hchain with ⟨hfirst, hrest⟩
      simp only [chainLabels, List.map_cons, List.foldl_cons, chainTarget]
      have hstep : (relax level label).apply source ≤ target := by
        rw [apply_relax]
        linarith
      have hmono := monotone_foldl_apply
        (labels := (chainLabels rest).map (relax level)) (by
          intro candidate hc
          obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hc
          rw [slope_relax]
          obtain ⟨step, hstepMem, hstepLabel⟩ := List.mem_map.mp horiginal
          subst hstepLabel
          exact hslope step (List.mem_cons_of_mem _ hstepMem))
      exact (hmono hstep).trans
        (ih (fun step hstepMem => hslope step (List.mem_cons_of_mem _ hstepMem)) hrest)

/-- **Exact cycle-slack reduction.**  A cyclic candidate with every edge
residual at most `level` exists exactly when the composite of the uniformly
relaxed labels has a pre-fixed point. -/
theorem hasCyclicSlack_iff_compList_relaxed_prefixed {labels : List Label}
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope) (level : ℝ) :
    HasCyclicSlack labels level ↔
      ∃ source : ℝ,
        (compList (labels.map (relax level))).apply source ≤ source := by
  constructor
  · rintro ⟨source, steps, hlabels, hclosed, hchain⟩
    have hstepSlope (step) (hstep : step ∈ steps) : 0 ≤ step.1.slope := by
      apply hslope step.1
      rw [← hlabels]
      exact List.mem_map_of_mem hstep
    refine ⟨source, ?_⟩
    rw [apply_compList]
    · rw [← hlabels]
      exact (relaxed_foldl_le_chainTarget hstepSlope hchain).trans_eq hclosed
    · intro relaxedLabel hrelaxed
      obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hrelaxed
      simpa using hslope original horiginal
  · rintro ⟨source, hprefixed⟩
    rw [apply_compList] at hprefixed
    · let orbit := relaxedOrbitSteps level source labels
      let steps := closeLastTarget source orbit
      refine ⟨source, steps, ?_, ?_, ?_⟩
      · simp [steps, orbit]
      · simp [steps, orbit]
      · apply isSlackChain_closeLastTarget
          (isSlackChain_relaxedOrbitSteps level source labels)
        rw [chainTarget_relaxedOrbitSteps]
        exact hprefixed
    · intro relaxedLabel hrelaxed
      obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hrelaxed
      simpa using hslope original horiginal

/-- Coefficient-level decision form of the exact cycle-slack reduction. -/
theorem hasCyclicSlack_iff_pathCoefficient_prefixed {labels : List Label}
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope) (level : ℝ) :
    HasCyclicSlack labels level ↔
      ∃ source : ℝ,
        (⟨pathFloor (labels.map (relax level)),
          pathShift (labels.map (relax level)),
          pathSlope (labels.map (relax level))⟩ : Label).apply source ≤ source := by
  rw [hasCyclicSlack_iff_compList_relaxed_prefixed hslope]
  apply exists_congr
  intro source
  rw [compList_eq_pathCoefficients]
  intro relaxedLabel hrelaxed
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hrelaxed
  simpa using hslope original horiginal

/-- Complete scalar trichotomy for an arbitrary cycle at a fixed slack
threshold.  The coefficients are explicit path coefficients of the relaxed
labels. -/
theorem hasCyclicSlack_iff_coefficient_trichotomy {labels : List Label}
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope) (level : ℝ) :
    HasCyclicSlack labels level ↔
      pathSlope (labels.map (relax level)) < 1 ∨
      (pathSlope (labels.map (relax level)) = 1 ∧
        pathShift (labels.map (relax level)) ≤ 0) ∨
      (1 < pathSlope (labels.map (relax level)) ∧
        pathFloor (labels.map (relax level)) ≤
          ((-pathShift (labels.map (relax level)) /
            (pathSlope (labels.map (relax level)) - 1) : ℝ) : WithBot ℝ)) := by
  rw [hasCyclicSlack_iff_pathCoefficient_prefixed hslope]
  simpa using
    (exists_apply_le_self_iff
      (⟨pathFloor (labels.map (relax level)),
        pathShift (labels.map (relax level)),
        pathSlope (labels.map (relax level))⟩ : Label))

end Label
end MaxAffineTransport

end

end Maths
