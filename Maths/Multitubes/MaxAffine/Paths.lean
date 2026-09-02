/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.MaxAffine.Basic

/-!
# Exact coefficients and defect normal forms for max-affine paths

Coefficient-level formulas describe arbitrary chronological lists of
max-affine labels.  The composite floor lies in `WithBot ℝ`, recording the
absent-floor case without assigning a real value to the maximum of an empty
family.  Its explicit finite family consists of one suffix-propagated branch
for every possible last-reset position.

The recentering construction turns a candidate chain into another max-affine
path acting on its initial discrepancy.  Its composite floor enumerates the
last-reset branches, while its composite affine branch is the exact weighted
affine-defect telescope.  The theorem
`Maths.MaxAffineTransport.Label.exact_defect_normal_form` combines these
branches into a nonlinear defect identity.

## Main definitions

* `Maths.MaxAffineTransport.Label.pathSlope`,
  `Maths.MaxAffineTransport.Label.pathShift`,
  `Maths.MaxAffineTransport.Label.pathFloor`: the three composite coefficients
  of a chronological list of labels, the floor valued in `WithBot ℝ`.
* `Maths.MaxAffineTransport.Label.weightedShiftTerms`,
  `Maths.MaxAffineTransport.Label.resetBranches`,
  `Maths.MaxAffineTransport.Label.resetBranchSup`: the explicit finite families
  behind those coefficients, one branch per last-reset position.
* `Maths.MaxAffineTransport.Label.recenter`,
  `Maths.MaxAffineTransport.Label.recenteredLabels`: the path acting on the
  initial discrepancy of a candidate chain.
* `Maths.MaxAffineTransport.Label.CandidateStep`,
  `Maths.MaxAffineTransport.Label.chainTarget`,
  `Maths.MaxAffineTransport.Label.chainLabels`: candidate chains.

## Main results

* `Maths.MaxAffineTransport.Label.compList_eq_pathCoefficients` and
  `Maths.MaxAffineTransport.Label.apply_compList_eq_pathCoefficients`: the
  composite label and its action are given by the path coefficients.
* `Maths.MaxAffineTransport.Label.pathFloor_eq_resetBranchSup` and
  `Maths.MaxAffineTransport.Label.pathFloor_le_iff_resetBranches`: the composite
  floor as the supremum of the last-reset branches.
* `Maths.MaxAffineTransport.Label.exact_defect_normal_form` and
  `Maths.MaxAffineTransport.Label.coe_exact_defect_eq_resetBranchSup_sup_affineSum`:
  the exact defect identity and its branch decomposition.
-/

@[expose] public section

namespace Maths

noncomputable section

namespace MaxAffineTransport
namespace Label

/-! ## Closed coefficient formulas -/

/-- Product of the slopes in a chronological list. -/
def pathSlope (labels : List Label) : ℝ :=
  (labels.map slope).prod

/-- Suffix-weighted affine shift of a chronological list. -/
def pathShift : List Label → ℝ
  | [] => 0
  | first :: rest => pathShift rest + pathSlope rest * first.shift

/-- Suffix-weighted affine terms, one for each edge position. -/
def weightedShiftTerms : List Label → List ℝ
  | [] => []
  | first :: rest =>
      pathSlope rest * first.shift :: weightedShiftTerms rest

/-- Supremum of the propagated floor branches.  The value is `⊥` exactly when
every floor is absent. -/
def pathFloor : List Label → WithBot ℝ
  | [] => ⊥
  | first :: rest =>
      pathFloor rest ⊔ pushFloor (pathShift rest) (pathSlope rest) first.floor

@[simp] theorem pathSlope_nil : pathSlope [] = 1 := rfl

@[simp] theorem pathSlope_cons (first : Label) (rest : List Label) :
    pathSlope (first :: rest) = first.slope * pathSlope rest := rfl

@[simp] theorem pathShift_nil : pathShift [] = 0 := rfl

@[simp] theorem pathShift_cons (first : Label) (rest : List Label) :
    pathShift (first :: rest) =
      pathShift rest + pathSlope rest * first.shift := rfl

@[simp] theorem pathSlope_append (first second : List Label) :
    pathSlope (first ++ second) = pathSlope first * pathSlope second := by
  simp [pathSlope, List.map_append, List.prod_append]

/-- Chronological concatenation composes path shifts semidirectly. -/
theorem pathShift_append (first second : List Label) :
    pathShift (first ++ second) =
      pathShift second + pathSlope second * pathShift first := by
  induction first with
  | nil => simp
  | cons label rest ih =>
      simp only [List.cons_append, pathShift_cons, ih, pathSlope_append]
      ring

@[simp] theorem weightedShiftTerms_nil : weightedShiftTerms [] = [] := rfl

@[simp] theorem weightedShiftTerms_cons (first : Label) (rest : List Label) :
    weightedShiftTerms (first :: rest) =
      pathSlope rest * first.shift :: weightedShiftTerms rest := rfl

/-- The affine coefficient is the sum of its explicit suffix-weighted terms. -/
theorem pathShift_eq_sum_weightedShiftTerms : ∀ labels : List Label,
    pathShift labels = (weightedShiftTerms labels).sum
  | [] => rfl
  | first :: rest => by
      simp only [pathShift_cons, weightedShiftTerms_cons, List.sum_cons,
        pathShift_eq_sum_weightedShiftTerms rest]
      ring

@[simp] theorem pathFloor_nil : pathFloor [] = ⊥ := rfl

@[simp] theorem pathFloor_cons (first : Label) (rest : List Label) :
    pathFloor (first :: rest) =
      pathFloor rest ⊔ pushFloor (pathShift rest) (pathSlope rest) first.floor := rfl

/-- A path has no propagated floor when none of its labels has a floor. -/
theorem pathFloor_eq_bot_of_floorless {labels : List Label}
    (hfloor : ∀ label ∈ labels, label.floor = ⊥) :
    pathFloor labels = ⊥ := by
  induction labels with
  | nil => rfl
  | cons first rest ih =>
      have hfirst := hfloor first (List.mem_cons_self ..)
      have hrest (label : Label) (hlabel : label ∈ rest) : label.floor = ⊥ :=
        hfloor label (List.mem_cons_of_mem _ hlabel)
      rw [pathFloor_cons, ih hrest, hfirst, pushFloor_bot, sup_bot_eq]

/-! ## Indexed last-reset formula -/

/-- Propagated floor branches, one for each edge position.  The branch at a
split `before ++ current :: after` is the current floor transported through
the suffix `after`. -/
def resetBranches : List Label → List (WithBot ℝ)
  | [] => []
  | first :: rest =>
      pushFloor (pathShift rest) (pathSlope rest) first.floor ::
        resetBranches rest

@[simp] theorem resetBranches_nil : resetBranches [] = [] := rfl

@[simp] theorem resetBranches_cons (first : Label) (rest : List Label) :
    resetBranches (first :: rest) =
      pushFloor (pathShift rest) (pathSlope rest) first.floor ::
        resetBranches rest := rfl

/-- Membership in `resetBranches` is exactly the indexed last-reset formula. -/
theorem mem_resetBranches_iff_split {labels : List Label}
    {branch : WithBot ℝ} :
    branch ∈ resetBranches labels ↔
      ∃ (before : List Label) (current : Label) (after : List Label),
        labels = before ++ current :: after ∧
          branch = pushFloor (pathShift after) (pathSlope after) current.floor := by
  induction labels with
  | nil => simp
  | cons first rest ih =>
      constructor
      · intro hbranch
        rw [resetBranches_cons, List.mem_cons] at hbranch
        rcases hbranch with hfirst | hrest
        · exact ⟨[], first, rest, rfl, hfirst⟩
        · obtain ⟨before, current, after, hlabels, hvalue⟩ := ih.mp hrest
          exact ⟨first :: before, current, after, by simp [hlabels], hvalue⟩
      · rintro ⟨before, current, after, hlabels, hvalue⟩
        rw [resetBranches_cons, List.mem_cons]
        cases before with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at hlabels
            rcases hlabels with ⟨rfl, rfl⟩
            exact Or.inl hvalue
        | cons head tail =>
            simp only [List.cons_append, List.cons.injEq] at hlabels
            rcases hlabels with ⟨_, hrest⟩
            exact Or.inr <| ih.mpr ⟨tail, current, after, hrest, hvalue⟩

/-- Finite supremum with the empty value `⊥`. -/
def resetBranchSup : List (WithBot ℝ) → WithBot ℝ
  | [] => ⊥
  | branch :: rest => branch ⊔ resetBranchSup rest

/-- **Explicit last-reset formula.**  The composite floor is the finite
supremum of the propagated branch attached to every edge position. -/
theorem pathFloor_eq_resetBranchSup : ∀ labels : List Label,
    pathFloor labels = resetBranchSup (resetBranches labels)
  | [] => rfl
  | first :: rest => by
      simp only [pathFloor_cons, resetBranches_cons, resetBranchSup]
      rw [← pathFloor_eq_resetBranchSup rest, sup_comm]

/-- Bound form of the indexed last-reset formula. -/
theorem pathFloor_le_iff_resetBranches (labels : List Label)
    (bound : WithBot ℝ) :
    pathFloor labels ≤ bound ↔
      ∀ branch ∈ resetBranches labels, branch ≤ bound := by
  induction labels with
  | nil => simp
  | cons first rest ih =>
      simp only [pathFloor_cons, resetBranches_cons, sup_le_iff,
        List.mem_cons, forall_eq_or_imp]
      tauto

private theorem slope_foldl_comp_general : ∀ (labels : List Label) (acc : Label),
    (labels.foldl (fun result next => next.comp result) acc).slope =
      pathSlope labels * acc.slope
  | [], acc => by simp [pathSlope]
  | first :: rest, acc => by
      rw [List.foldl_cons, slope_foldl_comp_general rest (first.comp acc)]
      simp only [pathSlope_cons, slope_comp]
      ring

private theorem shift_foldl_comp_general : ∀ (labels : List Label) (acc : Label),
    (labels.foldl (fun result next => next.comp result) acc).shift =
      pathShift labels + pathSlope labels * acc.shift
  | [], acc => by simp [pathShift, pathSlope]
  | first :: rest, acc => by
      rw [List.foldl_cons, shift_foldl_comp_general rest (first.comp acc)]
      simp only [pathShift_cons, pathSlope_cons, shift_comp]
      ring

/-- The slope of an arbitrary composite is the product of its slopes. -/
theorem slope_compList_eq_pathSlope (labels : List Label) :
    (compList labels).slope = pathSlope labels := by
  rw [compList, slope_foldl_comp_general labels id, slope_id, mul_one]

/-- The shift of an arbitrary composite is the suffix-weighted shift sum. -/
theorem shift_compList_eq_pathShift (labels : List Label) :
    (compList labels).shift = pathShift labels := by
  rw [compList, shift_foldl_comp_general labels id, shift_id, mul_zero, add_zero]

private theorem floor_foldl_comp_general : ∀ (labels : List Label),
    (∀ label ∈ labels, 0 ≤ label.slope) → ∀ acc : Label,
      (labels.foldl (fun result next => next.comp result) acc).floor =
        pathFloor labels ⊔
          pushFloor (pathShift labels) (pathSlope labels) acc.floor
  | [], _, acc => by simp [pathFloor, pathShift, pathSlope]
  | first :: rest, hslope, acc => by
      have hrest (label : Label) (hlabel : label ∈ rest) : 0 ≤ label.slope :=
        hslope label (List.mem_cons_of_mem _ hlabel)
      have hpathSlope : 0 ≤ pathSlope rest := by
        unfold pathSlope
        apply List.prod_nonneg
        intro value hvalue
        obtain ⟨label, hlabel, rfl⟩ := List.mem_map.mp hvalue
        exact hrest label hlabel
      rw [List.foldl_cons, floor_foldl_comp_general rest hrest (first.comp acc)]
      simp only [floor_comp]
      rw [pushFloor_sup hpathSlope, pushFloor_pushFloor]
      simp only [pathFloor_cons, pathShift_cons, pathSlope_cons]
      rw [sup_assoc]
      congr 2
      ring_nf

/-- The floor of an arbitrary nonnegative-slope composite is the supremum of
the propagated last-reset branches. -/
theorem floor_compList_eq_pathFloor {labels : List Label}
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope) :
    (compList labels).floor = pathFloor labels := by
  rw [compList, floor_foldl_comp_general labels hslope id, floor_id,
    pushFloor_bot, sup_bot_eq]

/-- A composite of floorless nonnegative-slope labels is floorless. -/
theorem floor_compList_eq_bot_of_floorless {labels : List Label}
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope)
    (hfloor : ∀ label ∈ labels, label.floor = ⊥) :
    (compList labels).floor = ⊥ := by
  rw [floor_compList_eq_pathFloor hslope,
    pathFloor_eq_bot_of_floorless hfloor]

/-- Exact coefficient normal form of a chronological max-affine path. -/
theorem compList_eq_pathCoefficients {labels : List Label}
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope) :
    compList labels = ⟨pathFloor labels, pathShift labels, pathSlope labels⟩ := by
  apply Label.ext
  · exact floor_compList_eq_pathFloor hslope
  · exact shift_compList_eq_pathShift labels
  · exact slope_compList_eq_pathSlope labels

/-- Exact action formula; `pathFloor = ⊥` is handled by `Label.apply` rather
than by an unsafe real convention. -/
theorem apply_compList_eq_pathCoefficients {labels : List Label}
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope) (point : ℝ) :
    (compList labels).apply point =
      (⟨pathFloor labels, pathShift labels, pathSlope labels⟩ : Label).apply point := by
  rw [compList_eq_pathCoefficients hslope]

/-! ## Recentered candidate chains -/

/-- Recenter one edge around proposed source and target values.  Acting on a
source discrepancy returns the resulting target discrepancy. -/
def recenter (label : Label) (source target : ℝ) : Label where
  floor := label.floor.map fun floor => floor - target
  shift := label.shift + label.slope * source - target
  slope := label.slope

@[simp] theorem slope_recenter (label : Label) (source target : ℝ) :
    (recenter label source target).slope = label.slope := rfl

/-- Edge recentering is an exact identity, including an absent floor. -/
theorem apply_recenter (label : Label) (source target discrepancy : ℝ) :
    (recenter label source target).apply discrepancy =
      label.apply (source + discrepancy) - target := by
  rcases label.floor_cases with hfloor | ⟨floor, hfloor⟩
  · rw [apply_of_floor_bot]
    · rw [label.apply_of_floor_bot hfloor]
      simp only [recenter, affinePart]
      ring
    · simp [recenter, hfloor]
  · rw [apply_of_floor_coe]
    · rw [label.apply_of_floor_coe hfloor]
      simp only [recenter, affinePart]
      have hbranch : label.shift + label.slope * source - target +
            label.slope * discrepancy =
          label.shift + label.slope * (source + discrepancy) - target := by
        ring
      rw [hbranch, ← max_sub_sub_right]
    · simp [recenter, hfloor]

/-- Candidate targets paired with their chronological edge labels. -/
abbrev CandidateStep := Label × ℝ

/-- Final proposed value of a candidate chain. -/
def chainTarget : ℝ → List CandidateStep → ℝ
  | source, [] => source
  | _, (_, target) :: rest => chainTarget target rest

/-- Original labels of a candidate chain. -/
def chainLabels (steps : List CandidateStep) : List Label :=
  steps.map Prod.fst

/-- Recentered edge labels of a candidate chain. -/
def recenteredLabels : ℝ → List CandidateStep → List Label
  | _, [] => []
  | source, (label, target) :: rest =>
      recenter label source target :: recenteredLabels target rest

private theorem foldl_recentered : ∀ (steps : List CandidateStep)
    (source discrepancy : ℝ),
    (chainLabels steps).foldl (fun point label => label.apply point)
        (source + discrepancy) - chainTarget source steps =
      (recenteredLabels source steps).foldl
        (fun point label => label.apply point) discrepancy
  | [], source, discrepancy => by simp [chainLabels, chainTarget, recenteredLabels]
  | (label, target) :: rest, source, discrepancy => by
      simp only [chainLabels, recenteredLabels, List.map_cons, List.foldl_cons,
        chainTarget]
      rw [← foldl_recentered rest target
        ((recenter label source target).apply discrepancy), apply_recenter]
      congr 2
      ring

private theorem nonnegative_recenteredLabels {steps : List CandidateStep}
    {source : ℝ} (hslope : ∀ step ∈ steps, 0 ≤ step.1.slope) :
    ∀ label ∈ recenteredLabels source steps, 0 ≤ label.slope := by
  induction steps generalizing source with
  | nil => simp [recenteredLabels]
  | cons first rest ih =>
      rcases first with ⟨firstLabel, target⟩
      intro label hlabel
      simp only [recenteredLabels, List.mem_cons] at hlabel
      rcases hlabel with rfl | hlabel
      · exact hslope (firstLabel, target) (List.mem_cons_self ..)
      · exact ih (source := target)
          (fun candidate hc => hslope candidate (List.mem_cons_of_mem _ hc))
          label hlabel

/-- **Exact defect normal form.**  The final transport discrepancy is the
action at zero of the composite recentered label.  Its affine coefficient is
the exact suffix-weighted affine-residual telescope, and its floor coefficient
is the supremum of the propagated last-reset branches, by
`compList_eq_pathCoefficients`. -/
theorem exact_defect_normal_form {steps : List CandidateStep} {source : ℝ}
    (hslope : ∀ step ∈ steps, 0 ≤ step.1.slope) :
    (chainLabels steps).foldl (fun point label => label.apply point) source -
        chainTarget source steps =
      (compList (recenteredLabels source steps)).apply 0 := by
  have hrecenter := foldl_recentered steps source 0
  simp only [add_zero] at hrecenter
  rw [hrecenter]
  symm
  exact apply_compList (nonnegative_recenteredLabels hslope) 0

/-- Fully coefficient-expanded form of `exact_defect_normal_form`. -/
theorem exact_defect_eq_pathCoefficients {steps : List CandidateStep} {source : ℝ}
    (hslope : ∀ step ∈ steps, 0 ≤ step.1.slope) :
    (chainLabels steps).foldl (fun point label => label.apply point) source -
        chainTarget source steps =
      (⟨pathFloor (recenteredLabels source steps),
          pathShift (recenteredLabels source steps),
          pathSlope (recenteredLabels source steps)⟩ : Label).apply 0 := by
  rw [exact_defect_normal_form hslope]
  apply apply_compList_eq_pathCoefficients
  exact nonnegative_recenteredLabels hslope

/-- **Expanded max formula for a candidate chain.**  In `WithBot ℝ`, the
final defect is the supremum of the affine residual telescope and every
propagated last-reset residual. -/
theorem coe_exact_defect_eq_resetBranchSup_sup_affineSum
    {steps : List CandidateStep} {source : ℝ}
    (hslope : ∀ step ∈ steps, 0 ≤ step.1.slope) :
    (((chainLabels steps).foldl (fun point label => label.apply point) source -
        chainTarget source steps : ℝ) : WithBot ℝ) =
      resetBranchSup (resetBranches (recenteredLabels source steps)) ⊔
        (((weightedShiftTerms (recenteredLabels source steps)).sum : ℝ) :
          WithBot ℝ) := by
  rw [exact_defect_eq_pathCoefficients hslope, coe_apply]
  change pathFloor (recenteredLabels source steps) ⊔
      ((pathShift (recenteredLabels source steps) +
        pathSlope (recenteredLabels source steps) * 0 : ℝ) : WithBot ℝ) = _
  rw [pathFloor_eq_resetBranchSup,
    pathShift_eq_sum_weightedShiftTerms]
  simp

end Label
end MaxAffineTransport

end

end Maths
