/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.MaxAffine.CycleSlack

/-!
# Closed relaxation formulas for max-affine cycles

Uniformly subtracting `level` from every edge does not merely preserve the
path slope.  It subtracts `level` times a canonical suffix-product mass from
the composite shift.  The resulting formulas turn the coefficient trichotomy
into closed cycle-slack criteria.

For a nonempty path with nonnegative slopes the relaxation mass is at least
one, even when some slopes vanish.  Consequently a unit-product cycle has the
exact attained threshold `pathShift / pathRelaxationMass`, with arbitrary
floors.  A subunit-product cycle is feasible at every real threshold, again
with arbitrary floors.  A superunit-product cycle has the same escape property
when all floors are absent.

## Main definitions

* `Maths.MaxAffineTransport.Label.pathRelaxationMass`: the suffix-product mass
  by which a uniform relaxation moves the composite shift.
* `Maths.MaxAffineTransport.Label.expansiveResetThreshold`,
  `Maths.MaxAffineTransport.Label.expansiveResetThresholds`,
  `Maths.MaxAffineTransport.Label.thresholdSup`: the per-reset thresholds of a
  superunit-product cycle and their supremum in `WithBot ℝ`.
* `Maths.MaxAffineTransport.Label.expansiveCyclicSlackThreshold` and
  `Maths.MaxAffineTransport.Label.cyclicSlackThreshold`: the exact cycle-slack
  threshold, `⊥` when every level is feasible.

## Main results

* `Maths.MaxAffineTransport.Label.pathShift_map_relax` and
  `Maths.MaxAffineTransport.Label.pathSlope_map_relax`: uniform relaxation
  preserves the path slope and subtracts `level` times the relaxation mass from the shift.
* `Maths.MaxAffineTransport.Label.one_le_pathRelaxationMass`: a nonempty path
  with nonnegative slopes has relaxation mass at least one.
* `Maths.MaxAffineTransport.Label.hasCyclicSlack_iff_cycleMean_le_of_pathSlope_eq_one`:
  a unit-product cycle attains the threshold `pathShift / pathRelaxationMass`.
* `Maths.MaxAffineTransport.Label.hasCyclicSlack_of_pathSlope_lt_one` and
  `Maths.MaxAffineTransport.Label.hasCyclicSlack_of_one_lt_pathSlope_of_floorless`:
  the subunit and floorless superunit escape cases.
* `Maths.MaxAffineTransport.Label.hasCyclicSlack_iff_cyclicSlackThreshold_le` and
  `Maths.MaxAffineTransport.Label.cyclicSlackThreshold_eq_bot_iff_all_levels`:
  the closed criterion and the characterisation of the all-levels case.
-/

@[expose] public section

namespace Maths

noncomputable section

namespace MaxAffineTransport
namespace Label

/-- Sum of the suffix slope products.  This is the coefficient by which a
common edge relaxation changes the composite affine shift. -/
def pathRelaxationMass : List Label → ℝ
  | [] => 0
  | _ :: rest => pathRelaxationMass rest + pathSlope rest

@[simp] theorem pathRelaxationMass_nil : pathRelaxationMass [] = 0 := rfl

@[simp] theorem pathRelaxationMass_cons (first : Label) (rest : List Label) :
    pathRelaxationMass (first :: rest) =
      pathRelaxationMass rest + pathSlope rest := rfl

/-- The common-relaxation coefficient obeys the same semidirect law as the
path shift. -/
theorem pathRelaxationMass_append (first second : List Label) :
    pathRelaxationMass (first ++ second) =
      pathRelaxationMass second +
        pathSlope second * pathRelaxationMass first := by
  induction first with
  | nil => simp
  | cons label rest ih =>
      simp only [List.cons_append, pathRelaxationMass_cons, ih,
        pathSlope_append]
      ring

/-- Uniform relaxation leaves every path slope unchanged. -/
@[simp] theorem pathSlope_map_relax (level : ℝ) : ∀ labels : List Label,
    pathSlope (labels.map (relax level)) = pathSlope labels
  | [] => rfl
  | first :: rest => by
      simp only [List.map_cons, pathSlope_cons, slope_relax,
        pathSlope_map_relax level rest]

/-- Exact affine relaxation formula for an arbitrary path. -/
theorem pathShift_map_relax (level : ℝ) : ∀ labels : List Label,
    pathShift (labels.map (relax level)) =
      pathShift labels - level * pathRelaxationMass labels
  | [] => by simp
  | first :: rest => by
      simp only [List.map_cons, pathShift_cons, pathSlope_map_relax,
        pathShift_map_relax level rest, pathRelaxationMass_cons]
      simp only [relax, recenter]
      ring

/-- Relaxing an absent floor keeps it absent. -/
theorem floor_relax_eq_bot {label : Label} (hfloor : label.floor = ⊥)
    (level : ℝ) :
    (relax level label).floor = ⊥ := by
  simp [relax, recenter, hfloor]

/-- A path is floorless after relaxation whenever every original edge is
floorless. -/
theorem pathFloor_map_relax_eq_bot {labels : List Label}
    (hfloor : ∀ label ∈ labels, label.floor = ⊥) (level : ℝ) :
    pathFloor (labels.map (relax level)) = ⊥ := by
  induction labels with
  | nil => rfl
  | cons first rest ih =>
      have hfirst := hfloor first (List.mem_cons_self ..)
      have hrest (label : Label) (hlabel : label ∈ rest) : label.floor = ⊥ :=
        hfloor label (List.mem_cons_of_mem _ hlabel)
      simp only [List.map_cons, pathFloor_cons, ih hrest,
        pathShift_map_relax, pathSlope_map_relax]
      rw [floor_relax_eq_bot hfirst, pushFloor_bot, bot_sup_eq]

private theorem pathSlope_nonneg {labels : List Label}
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope) :
    0 ≤ pathSlope labels := by
  unfold pathSlope
  apply List.prod_nonneg
  intro value hvalue
  obtain ⟨label, hlabel, rfl⟩ := List.mem_map.mp hvalue
  exact hslope label hlabel

/-- The relaxation mass of a nonempty nonnegative-slope path is at least one,
so the cycle-mean denominators are positive without requiring strictly positive
slopes. -/
theorem one_le_pathRelaxationMass {labels : List Label}
    (hne : labels ≠ [])
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope) :
    1 ≤ pathRelaxationMass labels := by
  induction labels with
  | nil => exact (hne rfl).elim
  | cons first rest ih =>
      cases rest with
      | nil => norm_num
      | cons next tail =>
          have hrest (label : Label) (hlabel : label ∈ next :: tail) : 0 ≤ label.slope :=
            hslope label (List.mem_cons_of_mem _ hlabel)
          have hmass : 1 ≤ pathRelaxationMass (next :: tail) :=
            ih (by simp) hrest
          have hproduct : 0 ≤ pathSlope (next :: tail) :=
            pathSlope_nonneg hrest
          change 1 ≤ pathRelaxationMass (next :: tail) +
            pathSlope (next :: tail)
          exact hmass.trans (le_add_of_nonneg_right hproduct)

/-- Hence every nonempty nonnegative-slope path has positive relaxation mass. -/
theorem pathRelaxationMass_pos {labels : List Label}
    (hne : labels ≠ [])
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope) :
    0 < pathRelaxationMass labels :=
  lt_of_lt_of_le zero_lt_one (one_le_pathRelaxationMass hne hslope)

/-- The exact unit-product cycle mean is invariant under moving an arbitrary
initial segment to the end. -/
theorem pathCycleMean_append_comm_of_product_one
    (first second : List Label)
    (hne : first ++ second ≠ [])
    (hslope : ∀ label ∈ first ++ second, 0 ≤ label.slope)
    (hproduct : pathSlope (first ++ second) = 1) :
    pathShift (first ++ second) / pathRelaxationMass (first ++ second) =
      pathShift (second ++ first) / pathRelaxationMass (second ++ first) := by
  have hneRotated : second ++ first ≠ [] := by
    intro hnil
    obtain ⟨hsecond, hfirst⟩ := List.append_eq_nil_iff.mp hnil
    apply hne
    simp [hfirst, hsecond]
  have hslopeRotated (label : Label) (hlabel : label ∈ second ++ first) :
      0 ≤ label.slope := by
    rw [List.mem_append] at hlabel
    apply hslope label
    rw [List.mem_append]
    exact hlabel.elim Or.inr Or.inl
  have hmass : pathRelaxationMass (first ++ second) ≠ 0 :=
    (pathRelaxationMass_pos hne hslope).ne'
  have hmassRotated : pathRelaxationMass (second ++ first) ≠ 0 :=
    (pathRelaxationMass_pos hneRotated hslopeRotated).ne'
  have hproduct' : pathSlope first * pathSlope second = 1 := by
    simpa only [pathSlope_append] using hproduct
  have hdenom : pathRelaxationMass second +
      pathSlope second * pathRelaxationMass first ≠ 0 := by
    rw [← pathRelaxationMass_append]
    exact hmass
  have hdenomRotated : pathRelaxationMass first +
      pathSlope first * pathRelaxationMass second ≠ 0 := by
    rw [← pathRelaxationMass_append]
    exact hmassRotated
  rw [pathShift_append, pathShift_append,
    pathRelaxationMass_append, pathRelaxationMass_append]
  apply (div_eq_div_iff hdenom hdenomRotated).mpr
  rw [← sub_eq_zero]
  calc
    (pathShift second + pathSlope second * pathShift first) *
          (pathRelaxationMass first +
            pathSlope first * pathRelaxationMass second) -
        (pathShift first + pathSlope first * pathShift second) *
          (pathRelaxationMass second +
            pathSlope second * pathRelaxationMass first) =
        (pathSlope first * pathSlope second - 1) *
          (pathShift first * pathRelaxationMass second -
            pathShift second * pathRelaxationMass first) := by ring
    _ = 0 := by rw [hproduct', sub_self, zero_mul]

/-- List-rotation form of unit-product cycle-mean invariance. -/
theorem pathCycleMean_rotate_of_product_one
    (labels : List Label) (steps : ℕ) (hsteps : steps ≤ labels.length)
    (hne : labels ≠ [])
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope)
    (hproduct : pathSlope labels = 1) :
    pathShift (labels.rotate steps) /
        pathRelaxationMass (labels.rotate steps) =
      pathShift labels / pathRelaxationMass labels := by
  rw [List.rotate_eq_drop_append_take hsteps]
  have hsplit := pathCycleMean_append_comm_of_product_one
    (labels.take steps) (labels.drop steps) (by
      simpa only [List.take_append_drop] using hne) (by
      simpa only [List.take_append_drop] using hslope) (by
      simpa only [List.take_append_drop] using hproduct)
  simpa only [List.take_append_drop] using hsplit.symm

/-- A subunit-product cycle admits arbitrary negative slack.  Floors do not
obstruct this escape because a contractive max-affine self-map always has a
pre-fixed point. -/
theorem hasCyclicSlack_of_pathSlope_lt_one {labels : List Label}
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope)
    (hproduct : pathSlope labels < 1) (level : ℝ) :
    HasCyclicSlack labels level := by
  rw [hasCyclicSlack_iff_coefficient_trichotomy hslope]
  exact Or.inl (by simpa using hproduct)

/-- At unit path product, arbitrary floors disappear from the exact slack
criterion.  The composite shift is the only obstruction. -/
theorem hasCyclicSlack_iff_pathShift_le_of_pathSlope_eq_one
    {labels : List Label}
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope)
    (hproduct : pathSlope labels = 1) (level : ℝ) :
    HasCyclicSlack labels level ↔
      pathShift labels ≤ level * pathRelaxationMass labels := by
  rw [hasCyclicSlack_iff_coefficient_trichotomy hslope]
  simp only [pathSlope_map_relax, pathShift_map_relax, hproduct,
    lt_self_iff_false, false_or, true_and]
  constructor
  · rintro (hshift | hlarge)
    · linarith
    · exact hlarge.1.elim
  · intro hshift
    exact Or.inl (by linarith)

/-- Closed cycle-mean formula for a nonempty unit-product cycle.  The
relaxation mass is positive under nonnegative slopes, so this is an ordinary
real quotient and the threshold is attained. -/
theorem hasCyclicSlack_iff_cycleMean_le_of_pathSlope_eq_one
    {labels : List Label}
    (hne : labels ≠ [])
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope)
    (hproduct : pathSlope labels = 1) (level : ℝ) :
    HasCyclicSlack labels level ↔
      pathShift labels / pathRelaxationMass labels ≤ level := by
  rw [hasCyclicSlack_iff_pathShift_le_of_pathSlope_eq_one hslope hproduct]
  exact (div_le_iff₀ (pathRelaxationMass_pos hne hslope)).symm

/-- The exact unit-product cycle mean is feasible, not merely an infimum. -/
theorem hasCyclicSlack_cycleMean_of_pathSlope_eq_one
    {labels : List Label}
    (hne : labels ≠ [])
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope)
    (hproduct : pathSlope labels = 1) :
    HasCyclicSlack labels
      (pathShift labels / pathRelaxationMass labels) := by
  rw [hasCyclicSlack_iff_cycleMean_le_of_pathSlope_eq_one
    hne hslope hproduct]

/-- A floorless superunit-product cycle also admits arbitrary negative slack:
its composite can escape toward negative infinity. -/
theorem hasCyclicSlack_of_one_lt_pathSlope_of_floorless
    {labels : List Label}
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope)
    (hfloor : ∀ label ∈ labels, label.floor = ⊥)
    (hproduct : 1 < pathSlope labels) (level : ℝ) :
    HasCyclicSlack labels level := by
  rw [hasCyclicSlack_iff_coefficient_trichotomy hslope]
  refine Or.inr (Or.inr ⟨?_, ?_⟩)
  · simpa using hproduct
  · rw [pathFloor_map_relax_eq_bot hfloor]
    exact bot_le

/-- Complete floorless closed form: the only finite slack threshold occurs at
unit path product. -/
theorem hasCyclicSlack_iff_of_floorless {labels : List Label}
    (hne : labels ≠ [])
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope)
    (hfloor : ∀ label ∈ labels, label.floor = ⊥)
    (level : ℝ) :
    HasCyclicSlack labels level ↔
      pathSlope labels ≠ 1 ∨
        pathShift labels / pathRelaxationMass labels ≤ level := by
  rcases lt_trichotomy (pathSlope labels) 1 with hproduct | hproduct | hproduct
  · exact ⟨fun _ => Or.inl (ne_of_lt hproduct),
      fun _ => hasCyclicSlack_of_pathSlope_lt_one hslope hproduct level⟩
  · simpa [hproduct] using
      (hasCyclicSlack_iff_cycleMean_le_of_pathSlope_eq_one
        hne hslope hproduct level)
  · exact ⟨fun _ => Or.inl (ne_of_gt hproduct),
      fun _ => hasCyclicSlack_of_one_lt_pathSlope_of_floorless hslope hfloor hproduct level⟩

/-! ## Exact finite-floor threshold in the expansive regime -/

/-- Threshold contributed by one finite reset floor.  The three total
coefficients belong to the whole cycle; `current` is the suffix beginning at
the edge carrying the floor. -/
def expansiveResetThreshold (totalSlope totalShift totalMass : ℝ)
    (current : List Label) (floor : ℝ) : ℝ :=
  ((totalSlope - 1) *
      (pathShift current.tail + pathSlope current.tail * floor) + totalShift) /
    ((totalSlope - 1) * pathRelaxationMass current + totalMass)

/-- All finite reset-floor thresholds, in chronological order.  Absent floors
contribute no constraint. -/
def expansiveResetThresholds (totalSlope totalShift totalMass : ℝ) :
    List Label → List ℝ
  | [] => []
  | first :: rest =>
      match first.floor with
      | ⊥ => expansiveResetThresholds totalSlope totalShift totalMass rest
      | (floor : ℝ) =>
          expansiveResetThreshold totalSlope totalShift totalMass
              (first :: rest) floor ::
            expansiveResetThresholds totalSlope totalShift totalMass rest

private theorem expansiveResetDenominator_pos
    {totalSlope totalMass : ℝ} (hproduct : 1 < totalSlope)
    (hmass : 0 < totalMass) {current : List Label}
    (hne : current ≠ [])
    (hslope : ∀ label ∈ current, 0 ≤ label.slope) :
    0 < (totalSlope - 1) * pathRelaxationMass current + totalMass := by
  have hcurrent := pathRelaxationMass_pos hne hslope
  positivity

private theorem reset_branch_le_iff_threshold_le
    {totalSlope totalShift totalMass level floor : ℝ}
    (hproduct : 1 < totalSlope) (hmass : 0 < totalMass)
    {first : Label} {rest : List Label}
    (hslope : ∀ label ∈ first :: rest, 0 ≤ label.slope) :
    pathShift (rest.map (relax level)) +
          pathSlope (rest.map (relax level)) * (floor - level) ≤
        (-totalShift + level * totalMass) / (totalSlope - 1) ↔
      expansiveResetThreshold totalSlope totalShift totalMass
          (first :: rest) floor ≤ level := by
  have hdenom : 0 <
      (totalSlope - 1) * pathRelaxationMass (first :: rest) + totalMass :=
    expansiveResetDenominator_pos hproduct hmass (by simp) hslope
  rw [expansiveResetThreshold, List.tail_cons, pathShift_map_relax,
    pathSlope_map_relax, div_le_iff₀ hdenom,
    le_div_iff₀ (sub_pos.mpr hproduct)]
  simp only [pathRelaxationMass_cons]
  constructor <;> intro h <;> nlinarith

private theorem pathFloor_relaxed_le_iff_expansiveResetThresholds_aux
    {totalSlope totalShift totalMass level : ℝ}
    (hproduct : 1 < totalSlope) (hmass : 0 < totalMass) :
    ∀ {labels : List Label},
      (∀ label ∈ labels, 0 ≤ label.slope) →
      (pathFloor (labels.map (relax level)) ≤
          ((-totalShift + level * totalMass) / (totalSlope - 1) : ℝ) ↔
        ∀ threshold ∈ expansiveResetThresholds
          totalSlope totalShift totalMass labels,
          threshold ≤ level)
  | [], _ => by simp [expansiveResetThresholds]
  | first :: rest, hslope => by
      have hrestSlope (label : Label) (hlabel : label ∈ rest) : 0 ≤ label.slope :=
        hslope label (List.mem_cons_of_mem _ hlabel)
      simp only [List.map_cons, pathFloor_cons, sup_le_iff]
      rw [pathFloor_relaxed_le_iff_expansiveResetThresholds_aux
        hproduct hmass hrestSlope]
      rcases first.floor_cases with hfloor | ⟨floor, hfloor⟩
      · simp [expansiveResetThresholds, hfloor, relax, recenter]
      · rw [show (relax level first).floor =
            ((floor - level : ℝ) : WithBot ℝ) by
          simp [relax, recenter, hfloor]]
        rw [pushFloor_coe, WithBot.coe_le_coe]
        simp only [expansiveResetThresholds, hfloor, List.mem_cons,
          forall_eq_or_imp]
        rw [reset_branch_le_iff_threshold_le hproduct hmass hslope]
        tauto

/-- In the expansive regime, the composite floor inequality is equivalent to
a finite family of real reset thresholds. -/
theorem pathFloor_relaxed_le_iff_expansiveResetThresholds
    {labels : List Label} (hne : labels ≠ [])
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope)
    (hproduct : 1 < pathSlope labels) (level : ℝ) :
    pathFloor (labels.map (relax level)) ≤
        ((-pathShift labels + level * pathRelaxationMass labels) /
          (pathSlope labels - 1) : ℝ) ↔
      ∀ threshold ∈ expansiveResetThresholds
        (pathSlope labels) (pathShift labels)
          (pathRelaxationMass labels) labels,
        threshold ≤ level :=
  pathFloor_relaxed_le_iff_expansiveResetThresholds_aux
    hproduct (pathRelaxationMass_pos hne hslope) hslope

/-- Complete closed threshold formula for a nonempty expansive cycle.  It is
the maximum of the finite reset thresholds when floors occur, and is
unbounded below when the list of thresholds is empty. -/
theorem hasCyclicSlack_iff_expansiveResetThresholds
    {labels : List Label} (hne : labels ≠ [])
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope)
    (hproduct : 1 < pathSlope labels) (level : ℝ) :
    HasCyclicSlack labels level ↔
      ∀ threshold ∈ expansiveResetThresholds
        (pathSlope labels) (pathShift labels)
          (pathRelaxationMass labels) labels,
        threshold ≤ level := by
  rw [hasCyclicSlack_iff_coefficient_trichotomy hslope]
  simp only [pathSlope_map_relax, pathShift_map_relax,
    not_lt_of_ge hproduct.le, false_or, ne_of_gt hproduct, false_and,
    hproduct, true_and]
  have hrewrite :
      -(pathShift labels - level * pathRelaxationMass labels) =
        -pathShift labels + level * pathRelaxationMass labels := by
    ring
  rw [hrewrite]
  exact pathFloor_relaxed_le_iff_expansiveResetThresholds
    hne hslope hproduct level

/-! ## A single exact optimum in `WithBot` -/

/-- Supremum of a finite list of real thresholds, with the empty supremum
equal to `⊥`. -/
def thresholdSup : List ℝ → WithBot ℝ
  | [] => ⊥
  | threshold :: rest => (threshold : WithBot ℝ) ⊔ thresholdSup rest

theorem thresholdSup_le_coe_iff (thresholds : List ℝ) (level : ℝ) :
    thresholdSup thresholds ≤ (level : WithBot ℝ) ↔
      ∀ threshold ∈ thresholds, threshold ≤ level := by
  induction thresholds with
  | nil => simp [thresholdSup]
  | cons threshold rest ih =>
      simp [thresholdSup, sup_le_iff, ih]

theorem thresholdSup_eq_bot_iff (thresholds : List ℝ) :
    thresholdSup thresholds = ⊥ ↔ thresholds = [] := by
  induction thresholds with
  | nil => simp [thresholdSup]
  | cons threshold rest ih => simp [thresholdSup]

theorem expansiveResetThresholds_eq_nil_iff
    (totalSlope totalShift totalMass : ℝ) : ∀ labels : List Label,
    expansiveResetThresholds totalSlope totalShift totalMass labels = [] ↔
      ∀ label ∈ labels, label.floor = ⊥
  | [] => by simp [expansiveResetThresholds]
  | first :: rest => by
      rcases first.floor_cases with hfloor | ⟨floor, hfloor⟩
      · simp [expansiveResetThresholds, hfloor,
          expansiveResetThresholds_eq_nil_iff totalSlope totalShift totalMass rest]
      · simp [expansiveResetThresholds, hfloor]

/-- Exact expansive optimum.  It is `⊥` precisely when no finite reset floor
contributes a constraint. -/
def expansiveCyclicSlackThreshold (labels : List Label) : WithBot ℝ :=
  thresholdSup <| expansiveResetThresholds
    (pathSlope labels) (pathShift labels)
      (pathRelaxationMass labels) labels

theorem expansiveCyclicSlackThreshold_eq_bot_iff (labels : List Label) :
    expansiveCyclicSlackThreshold labels = ⊥ ↔
      ∀ label ∈ labels, label.floor = ⊥ := by
  rw [expansiveCyclicSlackThreshold, thresholdSup_eq_bot_iff,
    expansiveResetThresholds_eq_nil_iff]

theorem hasCyclicSlack_iff_expansiveCyclicSlackThreshold_le
    {labels : List Label} (hne : labels ≠ [])
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope)
    (hproduct : 1 < pathSlope labels) (level : ℝ) :
    HasCyclicSlack labels level ↔
      expansiveCyclicSlackThreshold labels ≤ (level : WithBot ℝ) := by
  rw [hasCyclicSlack_iff_expansiveResetThresholds hne hslope hproduct]
  exact (thresholdSup_le_coe_iff _ _).symm

/-- **One-cycle slack threshold.**  The empty list and contractive cycles have
threshold `⊥`; unit-product cycles have their weighted cycle mean; expansive
cycles have the supremum of their finite reset thresholds.  The exact semantic
theorem below assumes that every slope in the list is nonnegative. -/
def cyclicSlackThreshold (labels : List Label) : WithBot ℝ :=
  if labels = [] then ⊥
  else if pathSlope labels = 1 then
    (pathShift labels / pathRelaxationMass labels : ℝ)
  else if 1 < pathSlope labels then
    expansiveCyclicSlackThreshold labels
  else ⊥

@[simp] theorem cyclicSlackThreshold_nil : cyclicSlackThreshold [] = ⊥ := by
  simp [cyclicSlackThreshold]

/-- The value `cyclicSlackThreshold` is an exact lower cut for feasible
uniform edge slack.  Its value is `⊥` when the optimum is unbounded below. -/
theorem hasCyclicSlack_iff_cyclicSlackThreshold_le
    {labels : List Label} (hne : labels ≠ [])
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope) (level : ℝ) :
    HasCyclicSlack labels level ↔
      cyclicSlackThreshold labels ≤ (level : WithBot ℝ) := by
  rcases lt_trichotomy (pathSlope labels) 1 with hproduct | hproduct | hproduct
  · have hneproduct : pathSlope labels ≠ 1 := ne_of_lt hproduct
    have hnexpansive : ¬1 < pathSlope labels := not_lt_of_ge hproduct.le
    rw [cyclicSlackThreshold, ite_eq_right hne, ite_eq_right hneproduct,
      ite_eq_right hnexpansive]
    simp only [bot_le, iff_true]
    exact hasCyclicSlack_of_pathSlope_lt_one hslope hproduct level
  · rw [cyclicSlackThreshold, ite_eq_right hne, ite_eq_left hproduct]
    rw [hasCyclicSlack_iff_cycleMean_le_of_pathSlope_eq_one
      hne hslope hproduct]
    simp
  · have hneproduct : pathSlope labels ≠ 1 := ne_of_gt hproduct
    rw [cyclicSlackThreshold, ite_eq_right hne, ite_eq_right hneproduct,
      ite_eq_left hproduct]
    exact hasCyclicSlack_iff_expansiveCyclicSlackThreshold_le
      hne hslope hproduct level

/-- Exact threshold theorem including the empty cycle. -/
theorem hasCyclicSlack_iff_cyclicSlackThreshold_le_all
    {labels : List Label}
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope) (level : ℝ) :
    HasCyclicSlack labels level ↔
      cyclicSlackThreshold labels ≤ (level : WithBot ℝ) := by
  by_cases hne : labels ≠ []
  · exact hasCyclicSlack_iff_cyclicSlackThreshold_le hne hslope level
  · have hnil : labels = [] := Classical.not_not.mp hne
    subst labels
    simp [HasCyclicSlack, chainLabels, chainTarget, IsSlackChain]

/-- Every finite optimum is attained by a cyclic slack witness. -/
theorem hasCyclicSlack_of_cyclicSlackThreshold_eq_coe
    {labels : List Label} (hne : labels ≠ [])
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope)
    {optimal : ℝ}
    (hoptimal : cyclicSlackThreshold labels = (optimal : WithBot ℝ)) :
    HasCyclicSlack labels optimal := by
  rw [hasCyclicSlack_iff_cyclicSlackThreshold_le hne hslope, hoptimal]

/-- A bottom optimum means feasibility at every real slack threshold. -/
theorem hasCyclicSlack_all_levels_of_cyclicSlackThreshold_eq_bot
    {labels : List Label} (hne : labels ≠ [])
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope)
    (hoptimal : cyclicSlackThreshold labels = ⊥) :
    ∀ level : ℝ, HasCyclicSlack labels level := by
  intro level
  rw [hasCyclicSlack_iff_cyclicSlackThreshold_le hne hslope, hoptimal]
  exact bot_le

/-- Exact characterization of the unbounded-below cases.  Floors are harmless
for contractive cycle product but are precisely what stops expansive escape. -/
theorem cyclicSlackThreshold_eq_bot_iff
    (labels : List Label) :
    cyclicSlackThreshold labels = ⊥ ↔
      labels = [] ∨ pathSlope labels < 1 ∨
        (1 < pathSlope labels ∧
          ∀ label ∈ labels, label.floor = ⊥) := by
  by_cases hlabels : labels = []
  · simp [hlabels]
  · rcases lt_trichotomy (pathSlope labels) 1 with
      hproduct | hproduct | hproduct
    · have hneproduct : pathSlope labels ≠ 1 := ne_of_lt hproduct
      have hnexpansive : ¬1 < pathSlope labels := not_lt_of_ge hproduct.le
      simp [cyclicSlackThreshold, hlabels, hneproduct, hnexpansive, hproduct]
    · simp [cyclicSlackThreshold, hlabels, hproduct]
    · have hneproduct : pathSlope labels ≠ 1 := ne_of_gt hproduct
      have hncontractive : ¬pathSlope labels < 1 :=
        not_lt_of_ge hproduct.le
      simp [cyclicSlackThreshold, hlabels, hneproduct, hproduct, hncontractive,
        expansiveCyclicSlackThreshold_eq_bot_iff]

/-- Bottom is not just sufficient but necessary for feasibility at every real
threshold. -/
theorem cyclicSlackThreshold_eq_bot_iff_all_levels
    {labels : List Label} (hne : labels ≠ [])
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope) :
    cyclicSlackThreshold labels = ⊥ ↔
      ∀ level : ℝ, HasCyclicSlack labels level := by
  constructor
  · exact hasCyclicSlack_all_levels_of_cyclicSlackThreshold_eq_bot
      hne hslope
  · intro hall
    rcases Option.eq_none_or_eq_some (cyclicSlackThreshold labels) with
      hbot | ⟨optimal, hoptimal⟩
    · exact hbot
    · have himpossible := hall (optimal - 1)
      have hoptimal' : cyclicSlackThreshold labels =
          (optimal : WithBot ℝ) := hoptimal
      rw [hasCyclicSlack_iff_cyclicSlackThreshold_le hne hslope,
        hoptimal'] at himpossible
      norm_num at himpossible

/-- Bottom is equivalent to all-level feasibility for every list, including
the empty cycle. -/
theorem cyclicSlackThreshold_eq_bot_iff_all_levels_all
    {labels : List Label}
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope) :
    cyclicSlackThreshold labels = ⊥ ↔
      ∀ level : ℝ, HasCyclicSlack labels level := by
  by_cases hne : labels ≠ []
  · exact cyclicSlackThreshold_eq_bot_iff_all_levels hne hslope
  · have hnil : labels = [] := Classical.not_not.mp hne
    subst labels
    simp [HasCyclicSlack, chainLabels, chainTarget, IsSlackChain]

/-- Complete criterion for arbitrarily negative cyclic slack. -/
theorem hasCyclicSlack_all_levels_iff
    {labels : List Label} (hne : labels ≠ [])
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope) :
    (∀ level : ℝ, HasCyclicSlack labels level) ↔
      pathSlope labels < 1 ∨
        (1 < pathSlope labels ∧
          ∀ label ∈ labels, label.floor = ⊥) := by
  calc
    (∀ level : ℝ, HasCyclicSlack labels level) ↔
        cyclicSlackThreshold labels = ⊥ :=
      (cyclicSlackThreshold_eq_bot_iff_all_levels hne hslope).symm
    _ ↔ labels = [] ∨ pathSlope labels < 1 ∨
        (1 < pathSlope labels ∧
          ∀ label ∈ labels, label.floor = ⊥) :=
      cyclicSlackThreshold_eq_bot_iff labels
    _ ↔ _ := by simp [hne]

/-- Complete all-list criterion for arbitrarily negative cyclic slack. -/
theorem hasCyclicSlack_all_levels_iff_all
    {labels : List Label}
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope) :
    (∀ level : ℝ, HasCyclicSlack labels level) ↔
      labels = [] ∨ pathSlope labels < 1 ∨
        (1 < pathSlope labels ∧
          ∀ label ∈ labels, label.floor = ⊥) := by
  calc
    (∀ level : ℝ, HasCyclicSlack labels level) ↔
        cyclicSlackThreshold labels = ⊥ :=
      (cyclicSlackThreshold_eq_bot_iff_all_levels_all hslope).symm
    _ ↔ _ := cyclicSlackThreshold_eq_bot_iff labels

end Label
end MaxAffineTransport

end

end Maths
