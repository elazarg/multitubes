/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.MaxAffine.Basic
public import Mathlib.Data.List.Rotate

/-!
# Complete scalar and pathwise max-affine transport theory

Max-affine transport admits the following scalar and cyclic classifications:

* complete descriptions of the pre-fixed and fixed sets of one label;
* an attained/unbounded classification of the exact scalar residual margin;
* the weighted edge obstruction for nonnegative slopes; and
* forward rotation of exact and lax cyclic certificates without inverse maps.

The residual-margin theorems are stated without an unsafe real-valued `sInf`:
the unbounded cases explicitly produce a witness below every real threshold,
and the finite cases prove a universal lower bound together with an attaining
point.  These statements determine the extended-real infimum exactly.

## Main definitions

* `Maths.MaxAffineTransport.Label.residual`: the scalar residual
  `apply f x - x` of one label at a point.

## Main results

* `Maths.MaxAffineTransport.Label.apply_le_self_iff_of_slope_lt_one`,
  `Maths.MaxAffineTransport.Label.apply_le_self_iff_of_slope_eq_one`,
  `Maths.MaxAffineTransport.Label.apply_le_self_iff_of_one_lt_slope`: the
  pre-fixed set of one label in each slope regime.
* In the namespace `Maths.MaxAffineTransport.Label`, the `apply_eq_self_iff_*`
  and `not_exists_apply_eq_self_*` results: the complete description of the fixed set.
* `Maths.MaxAffineTransport.Label.exists_residual_le_of_slope_lt_one`,
  `Maths.MaxAffineTransport.Label.exists_residual_eq_shift_of_slope_eq_one`,
  `Maths.MaxAffineTransport.Label.residual_margin_of_one_lt_slope_of_floor_coe`:
  the attained/unbounded classification of the residual margin, stated without a
  real-valued `sInf`.
* `Maths.MaxAffineTransport.exists_edge_defect_ge_of_nonnegative_slopes`: the
  weighted edge obstruction at nonnegative slopes.
* `Maths.MaxAffineTransport.isFixedPt_foldl_rotate` and
  `Maths.MaxAffineTransport.isPrefixed_foldl_rotate`: forward rotation of exact
  and lax cyclic certificates, using no inverse maps.
-/

@[expose] public section

namespace Maths

noncomputable section

namespace MaxAffineTransport

open scoped BigOperators

namespace Label

/-! ## The affine part around its fixed point

Every classification in this file reduces to the position of the candidate
point relative to the fixed point of the affine part - `f.shift / (1 - f.slope)`
below unit slope, `-f.shift / (f.slope - 1)` above it.  The lemmas of this
section state those reductions once, in both slope regimes: the sublevel sets
of the affine residual `f.affinePart x - x` are rays, and the level-zero and
exact-level cases describe the pre-fixed and fixed sets of the affine part. -/

/-- Below unit slope the sublevel sets of the affine residual are upper rays:
`f.affinePart x - x` falls to `level` exactly from
`(f.shift - level) / (1 - f.slope)` onward. -/
theorem affinePart_sub_le_iff_of_slope_lt_one (f : Label) (hslope : f.slope < 1)
    (x level : ℝ) :
    f.affinePart x - x ≤ level ↔ (f.shift - level) / (1 - f.slope) ≤ x := by
  rw [div_le_iff₀ (sub_pos.mpr hslope)]
  simp only [affinePart]
  constructor <;> intro h <;> linarith

/-- Above unit slope the sublevel sets of the affine residual are lower rays:
`f.affinePart x - x` stays at most `level` exactly up to
`(level - f.shift) / (f.slope - 1)`. -/
theorem affinePart_sub_le_iff_of_one_lt_slope (f : Label) (hslope : 1 < f.slope)
    (x level : ℝ) :
    f.affinePart x - x ≤ level ↔ x ≤ (level - f.shift) / (f.slope - 1) := by
  rw [le_div_iff₀ (sub_pos.mpr hslope)]
  simp only [affinePart]
  constructor <;> intro h <;> linarith

/-- Below unit slope the affine part lies below the identity exactly on the
closed ray above the affine fixed point. -/
theorem affinePart_le_self_iff_of_slope_lt_one (f : Label) (hslope : f.slope < 1)
    (x : ℝ) :
    f.affinePart x ≤ x ↔ f.shift / (1 - f.slope) ≤ x := by
  simpa [sub_nonpos] using f.affinePart_sub_le_iff_of_slope_lt_one hslope x 0

/-- Above unit slope the affine part lies below the identity exactly on the
closed ray below the affine fixed point. -/
theorem affinePart_le_self_iff_of_one_lt_slope (f : Label) (hslope : 1 < f.slope)
    (x : ℝ) :
    f.affinePart x ≤ x ↔ x ≤ -f.shift / (f.slope - 1) := by
  simpa [sub_nonpos, zero_sub] using
    f.affinePart_sub_le_iff_of_one_lt_slope hslope x 0

/-- Below unit slope the affine part has exactly one fixed point. -/
theorem affinePart_eq_self_iff_of_slope_lt_one (f : Label) (hslope : f.slope < 1)
    (x : ℝ) :
    f.affinePart x = x ↔ x = f.shift / (1 - f.slope) := by
  grind [affinePart]

/-- Above unit slope the affine part has exactly one fixed point. -/
theorem affinePart_eq_self_iff_of_one_lt_slope (f : Label) (hslope : 1 < f.slope)
    (x : ℝ) :
    f.affinePart x = x ↔ x = -f.shift / (f.slope - 1) := by
  grind [affinePart]

/-! ## Complete pre-fixed-set classification -/

/-- In the contractive regime, pre-fixed points form the upper ray cut out by
the floor and the affine fixed point.  The `WithBot` floor statement uniformly
covers a missing floor. -/
theorem apply_le_self_iff_of_slope_lt_one (f : Label) (hslope : f.slope < 1)
    (x : ℝ) :
    f.apply x ≤ x ↔
      f.floor ≤ (x : WithBot ℝ) ∧ f.shift / (1 - f.slope) ≤ x := by
  rw [f.apply_le_iff]
  exact and_congr_right fun _ ↦ f.affinePart_le_self_iff_of_slope_lt_one hslope x

/-- At unit slope, pre-fixed points exist precisely when the translation is
nonpositive, with the floor imposing the only bound on the point. -/
theorem apply_le_self_iff_of_slope_eq_one (f : Label) (hslope : f.slope = 1)
    (x : ℝ) :
    f.apply x ≤ x ↔ f.floor ≤ (x : WithBot ℝ) ∧ f.shift ≤ 0 := by
  simp [f.apply_le_iff, affinePart, hslope, one_mul]

/-- In the expansive regime, pre-fixed points form the interval between the
floor (if present) and the affine fixed point. -/
theorem apply_le_self_iff_of_one_lt_slope (f : Label) (hslope : 1 < f.slope)
    (x : ℝ) :
    f.apply x ≤ x ↔
      f.floor ≤ (x : WithBot ℝ) ∧ x ≤ -f.shift / (f.slope - 1) := by
  rw [f.apply_le_iff]
  exact and_congr_right fun _ ↦ f.affinePart_le_self_iff_of_one_lt_slope hslope x

/-! ## Complete fixed-set classification -/

/-- A contractive nonnegative-slope label has one fixed point.  `unbotD` uses
the affine fixed point itself when no floor is present, so one formula covers
both cases. -/
theorem apply_eq_self_iff_of_slope_lt_one
    (f : Label) (hslope : f.slope < 1) (x : ℝ) :
    f.apply x = x ↔
      x = max (f.floor.unbotD (f.shift / (1 - f.slope)))
        (f.shift / (1 - f.slope)) := by
  let q := f.shift / (1 - f.slope)
  have hq : f.affinePart q = q :=
    (f.affinePart_eq_self_iff_of_slope_lt_one hslope q).mpr rfl
  rcases f.floor_cases with hfloor | ⟨floor, hfloor⟩
  · rw [f.apply_of_floor_bot hfloor, hfloor]
    simp only [WithBot.unbotD_bot, max_self]
    exact f.affinePart_eq_self_iff_of_slope_lt_one hslope x
  · rw [f.apply_of_floor_coe hfloor, hfloor]
    simp only [WithBot.unbotD_coe]
    constructor
    · intro hx
      have hfloorx : floor ≤ x := by
        have := le_max_left floor (f.affinePart x)
        linarith
      have hqx : q ≤ x := by
        have hbranch : f.affinePart x ≤ x := by
          have := le_max_right floor (f.affinePart x)
          linarith
        exact (f.affinePart_le_self_iff_of_slope_lt_one hslope x).mp hbranch
      apply le_antisymm
      · by_cases hbranch : f.affinePart x ≤ floor
        · have : x = floor := by simpa [max_eq_left hbranch] using hx.symm
          subst x
          exact le_max_left _ _
        · have hfloorbranch : floor ≤ f.affinePart x := le_of_not_ge hbranch
          have hxaffine : f.affinePart x = x := by
            simpa [max_eq_right hfloorbranch] using hx
          rw [(f.affinePart_eq_self_iff_of_slope_lt_one hslope x).mp hxaffine]
          exact le_max_right _ _
      · exact max_le hfloorx hqx
    · rintro rfl
      by_cases hfloorq : floor ≤ q
      · rw [max_eq_right hfloorq, hq, max_eq_right hfloorq]
      · have hqfloor : q ≤ floor := le_of_not_ge hfloorq
        rw [max_eq_left hqfloor]
        have hbranch : f.affinePart floor ≤ floor := by
          have hiff := (f.apply_le_self_iff_of_slope_lt_one hslope floor).mpr
            ⟨by simp [hfloor], hqfloor⟩
          rw [f.apply_of_floor_coe hfloor, max_le_iff] at hiff
          exact hiff.2
        rw [max_eq_left hbranch]

/-- At unit slope and zero shift, the fixed set is exactly the ray above the
floor; with no floor this is all of `ℝ`. -/
theorem apply_eq_self_iff_of_slope_eq_one_of_shift_eq_zero
    (f : Label) (hslope : f.slope = 1) (hshift : f.shift = 0) (x : ℝ) :
    f.apply x = x ↔ f.floor ≤ (x : WithBot ℝ) := by
  constructor
  · intro h
    exact f.floor_le_coe_apply x |>.trans_eq (congrArg WithBot.some h)
  · intro hfloor
    apply le_antisymm
    · exact (f.apply_le_self_iff_of_slope_eq_one hslope x).mpr
        ⟨hfloor, hshift.le⟩
    · rcases f.floor_cases with hbot | ⟨floor, hfloor⟩
      · rw [f.apply_of_floor_bot hbot, affinePart, hslope, hshift]
        simp
      · rw [f.apply_of_floor_coe hfloor]
        calc
          x = f.affinePart x := by simp [affinePart, hslope, hshift]
          _ ≤ max floor (f.affinePart x) := le_max_right _ _

/-- A positive unit-slope translation has no fixed point. -/
theorem not_exists_apply_eq_self_of_slope_eq_one_of_shift_pos
    (f : Label) (hslope : f.slope = 1) (hshift : 0 < f.shift) :
    ¬∃ x : ℝ, f.apply x = x := by
  rintro ⟨x, hx⟩
  have hprefixed := (f.apply_le_self_iff_of_slope_eq_one hslope x).mp hx.le
  linarith

/-- A negative unit-slope label has a fixed point exactly when its floor is
finite, and then the floor is the unique fixed point. -/
theorem apply_eq_self_iff_of_slope_eq_one_of_shift_neg_of_floor_coe
    (f : Label) (hslope : f.slope = 1) (hshift : f.shift < 0)
    {floor x : ℝ} (hfloor : f.floor = (floor : WithBot ℝ)) :
    f.apply x = x ↔ x = floor := by
  rw [f.apply_of_floor_coe hfloor, affinePart, hslope, one_mul]
  constructor
  · intro hx
    by_cases hbranch : f.shift + x ≤ floor
    · simpa [max_eq_left hbranch] using hx.symm
    · have := (max_eq_right (le_of_not_ge hbranch)).symm.trans hx
      linarith
  · rintro rfl
    rw [max_eq_left]
    linarith

theorem not_exists_apply_eq_self_of_slope_eq_one_of_shift_neg_of_floor_bot
    (f : Label) (hslope : f.slope = 1) (hshift : f.shift < 0)
    (hfloor : f.floor = ⊥) :
    ¬∃ x : ℝ, f.apply x = x := by
  rintro ⟨x, hx⟩
  rw [f.apply_of_floor_bot hfloor, affinePart, hslope, one_mul] at hx
  linarith

/-- A floorless expansive affine map has exactly its affine fixed point. -/
theorem apply_eq_self_iff_of_one_lt_slope_of_floor_bot
    (f : Label) (hslope : 1 < f.slope) (hfloor : f.floor = ⊥) (x : ℝ) :
    f.apply x = x ↔ x = -f.shift / (f.slope - 1) := by
  rw [f.apply_of_floor_bot hfloor]
  exact f.affinePart_eq_self_iff_of_one_lt_slope hslope x

/-- With a finite floor and expansive slope, the fixed set consists of the
affine fixed point and the floor, provided the floor does not exceed the
affine fixed point.  This single formula includes the one- and two-point
boundary cases. -/
theorem apply_eq_self_iff_of_one_lt_slope_of_floor_coe
    (f : Label) (hslope : 1 < f.slope) {floor x : ℝ}
    (hfloor : f.floor = (floor : WithBot ℝ)) :
    f.apply x = x ↔
      (x = -f.shift / (f.slope - 1) ∧
        floor ≤ -f.shift / (f.slope - 1)) ∨
      (x = floor ∧ floor ≤ -f.shift / (f.slope - 1)) := by
  let q := -f.shift / (f.slope - 1)
  have hq : f.affinePart q = q :=
    (f.affinePart_eq_self_iff_of_one_lt_slope hslope q).mpr rfl
  rw [f.apply_of_floor_coe hfloor]
  constructor
  · intro hx
    have hfloorx : floor ≤ x := le_max_left _ _ |>.trans_eq hx
    by_cases hbranch : f.affinePart x ≤ floor
    · have hxfloor : x = floor := hx.symm.trans (max_eq_left hbranch)
      exact Or.inr ⟨hxfloor, by
        subst x
        have hbranchle : f.affinePart floor ≤ floor :=
          (le_max_right floor (f.affinePart floor)).trans_eq hx
        exact (f.affinePart_le_self_iff_of_one_lt_slope hslope floor).mp hbranchle⟩
    · have hfloorbranch : floor ≤ f.affinePart x := le_of_not_ge hbranch
      have hxaffine : f.affinePart x = x := (max_eq_right hfloorbranch).symm.trans hx
      have hxq : x = q :=
        (f.affinePart_eq_self_iff_of_one_lt_slope hslope x).mp hxaffine
      have hfloorq : floor ≤ q := hxq ▸ hfloorx
      exact Or.inl ⟨by simpa [q] using hxq, by simpa [q] using hfloorq⟩
  · intro hcases
    rcases hcases with ⟨hxq, hfloorq⟩ | ⟨hxfloor, hfloorq⟩
    · subst x
      change max floor (f.affinePart q) = q
      rw [hq, max_eq_right]
      simpa [q] using hfloorq
    · subst x
      have hprefixed : f.apply floor ≤ floor :=
        (f.apply_le_self_iff_of_one_lt_slope hslope floor).mpr
          ⟨by simp [hfloor], hfloorq⟩
      rw [f.apply_of_floor_coe hfloor, max_le_iff] at hprefixed
      rw [max_eq_left hprefixed.2]

/-! ## Exact residual margin without unsafe real infima -/

/-- Scalar residual of a label at a candidate point. -/
def residual (f : Label) (x : ℝ) : ℝ := f.apply x - x

/-- Contractive residuals are unbounded below as the candidate tends upward. -/
theorem exists_residual_le_of_slope_lt_one (f : Label) (hslope : f.slope < 1)
    (level : ℝ) : ∃ x : ℝ, f.residual x ≤ level := by
  rcases f.floor_cases with hfloor | ⟨floor, hfloor⟩
  · refine ⟨(f.shift - level) / (1 - f.slope), ?_⟩
    rw [residual, f.apply_of_floor_bot hfloor]
    exact (f.affinePart_sub_le_iff_of_slope_lt_one hslope _ level).mpr le_rfl
  · let x := max (floor - level) ((f.shift - level) / (1 - f.slope))
    refine ⟨x, ?_⟩
    rw [residual, f.apply_of_floor_coe hfloor, ← max_sub_sub_right]
    have hfloorx : floor - level ≤ x := le_max_left _ _
    exact max_le (by linarith)
      ((f.affinePart_sub_le_iff_of_slope_lt_one hslope x level).mpr (le_max_right _ _))

/-- At unit slope the residual has exact minimum `shift`, regardless of the
floor. -/
theorem shift_le_residual_of_slope_eq_one
    (f : Label) (hslope : f.slope = 1) (x : ℝ) :
    f.shift ≤ f.residual x := by
  rw [residual]
  have := le_max_right f.floor (f.affinePart x)
  have happly : f.affinePart x ≤ f.apply x := by
    rcases f.floor_cases with hfloor | ⟨floor, hfloor⟩
    · rw [f.apply_of_floor_bot hfloor]
    · rw [f.apply_of_floor_coe hfloor]
      exact le_max_right _ _
  simp only [affinePart, hslope, one_mul] at happly
  linarith

theorem exists_residual_eq_shift_of_slope_eq_one
    (f : Label) (hslope : f.slope = 1) :
    ∃ x : ℝ, f.residual x = f.shift := by
  rcases f.floor_cases with hfloor | ⟨floor, hfloor⟩
  · exact ⟨0, by simp [residual, f.apply_of_floor_bot hfloor, affinePart, hslope]⟩
  · let x := max floor (floor - f.shift)
    refine ⟨x, ?_⟩
    rw [residual, f.apply_of_floor_coe hfloor, affinePart, hslope, one_mul]
    have : floor ≤ f.shift + x := by
      have := le_max_right floor (floor - f.shift)
      linarith
    rw [max_eq_right this]
    ring

/-- A floorless expansive residual is unbounded below as the candidate tends
downward. -/
theorem exists_residual_le_of_one_lt_slope_of_floor_bot
    (f : Label) (hslope : 1 < f.slope) (hfloor : f.floor = ⊥)
    (level : ℝ) : ∃ x : ℝ, f.residual x ≤ level := by
  refine ⟨(level - f.shift) / (f.slope - 1), ?_⟩
  rw [residual, f.apply_of_floor_bot hfloor]
  exact (f.affinePart_sub_le_iff_of_one_lt_slope hslope _ level).mpr le_rfl

/-- Exact minimum of the residual for an expansive label with a finite floor. -/
theorem residual_margin_of_one_lt_slope_of_floor_coe
    (f : Label) (hslope : 1 < f.slope) {floor : ℝ}
    (hfloor : f.floor = (floor : WithBot ℝ)) :
    (∀ x : ℝ, ((f.slope - 1) * floor + f.shift) / f.slope ≤ f.residual x) ∧
      f.residual ((floor - f.shift) / f.slope) =
        ((f.slope - 1) * floor + f.shift) / f.slope := by
  have hapos : 0 < f.slope := lt_trans zero_lt_one hslope
  have hbranch :
      f.shift + f.slope * ((floor - f.shift) / f.slope) = floor := by
    field_simp
    ring
  constructor
  · intro x
    rw [residual, f.apply_of_floor_coe hfloor, ← max_sub_sub_right]
    by_cases hcenter : x ≤ (floor - f.shift) / f.slope
    · apply le_max_of_le_left
      rw [div_le_iff₀ hapos]
      rw [le_div_iff₀ hapos] at hcenter
      nlinarith
    · apply le_max_of_le_right
      rw [div_le_iff₀ hapos]
      have hcenter' : (floor - f.shift) / f.slope ≤ x := le_of_not_ge hcenter
      rw [div_le_iff₀ hapos] at hcenter'
      simp only [affinePart]
      nlinarith
  · rw [residual, f.apply_of_floor_coe hfloor, affinePart, hbranch, max_self]
    field_simp
    ring

end Label

/-! ## Nonnegative-slope quantitative telescope -/

section Graph

universe uV uE

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

/-- Nonnegative slopes already make every nonempty suffix-weight sum positive:
the final edge always has suffix weight one. -/
theorem suffixWeightSum_pos_of_nonempty {label : E → Label}
    (hslope : ∀ edge : E, 0 ≤ (label edge).slope) :
    ∀ edges : List E, edges ≠ [] → 0 < suffixWeightSum label edges
  | [], hne => (hne rfl).elim
  | [_], _ => by simp
  | edge :: next :: rest, _ => by
      rw [suffixWeightSum_cons]
      exact add_pos_of_nonneg_of_pos (slopeProd_nonneg hslope _)
        (suffixWeightSum_pos_of_nonempty hslope (next :: rest) (by simp))

/-- Uniform strict residual bounds control the weighted sum even when some
suffix weights vanish.  Strictness survives because the last suffix weight is
one. -/
theorem weightedDefect_lt_of_nonnegative_slopes {label : E → Label}
    (hslope : ∀ edge : E, 0 ≤ (label edge).slope)
    (φ : V → ℝ) {bound : ℝ} :
    ∀ edges : List E, edges ≠ [] →
      (∀ edge ∈ edges, max 0 (defect G label φ edge) < bound) →
      weightedDefect G label φ edges < bound * suffixWeightSum label edges
  | [], hne, _ => (hne rfl).elim
  | [edge], _, hbound => by
      have hedge := hbound edge (by simp)
      simpa using hedge
  | edge :: next :: rest, _, hbound => by
      have hedge := hbound edge (by simp)
      have hprod := slopeProd_nonneg hslope (next :: rest)
      have hfirst : slopeProd label (next :: rest) *
          max 0 (defect G label φ edge) ≤
        slopeProd label (next :: rest) * bound :=
        mul_le_mul_of_nonneg_left hedge.le hprod
      have htail := weightedDefect_lt_of_nonnegative_slopes hslope φ
        (next :: rest) (by simp)
        (fun candidate hmem ↦ hbound candidate (by simp [hmem]))
      rw [weightedDefect_cons, suffixWeightSum_cons]
      nlinarith

/-- **Sharp nonnegative-slope edge obstruction.**  Zero slopes are allowed;
only nonnegativity and nonemptiness are needed. -/
theorem exists_edge_defect_ge_of_nonnegative_slopes
    {label : E → Label} (hslope : ∀ edge : E, 0 ≤ (label edge).slope)
    (φ : V → ℝ) {base : V} (cycle : G.Walk base base) {gain : ℝ}
    (hgain : 0 < gain)
    (hcycle : φ base + gain ≤ holonomyApply label cycle (φ base)) :
    ∃ edge ∈ cycle.edges,
      gain / suffixWeightSum label cycle.edges ≤ defect G label φ edge := by
  have hne : cycle.edges ≠ [] := by
    intro hempty
    rw [holonomyApply_eq_foldl, hempty, List.foldl_nil] at hcycle
    linarith
  have hsum : 0 < suffixWeightSum label cycle.edges :=
    suffixWeightSum_pos_of_nonempty hslope _ hne
  by_contra hnone
  have hstrict (edge : E) (hedge : edge ∈ cycle.edges) :
      max 0 (defect G label φ edge) <
        gain / suffixWeightSum label cycle.edges := by
    refine max_lt (div_pos hgain hsum) ?_
    by_contra hle
    exact hnone ⟨edge, hedge, not_lt.mp hle⟩
  have hweighted := weightedDefect_lt_of_nonnegative_slopes hslope φ
    cycle.edges hne hstrict
  rw [div_mul_cancel₀ _ hsum.ne'] at hweighted
  have htelescope := holonomyApply_le_add_weightedDefect
    (G := G) hslope φ cycle
  linarith

end Graph

/-! ## Forward rotation without inverses -/

section Rotation

variable {X : Type*}

/-- A fixed point of `outer ∘ inner` rotates forward to a fixed point of
`inner ∘ outer`; no inverse map is required. -/
theorem isFixedPt_comp_rotate {outer inner : X → X} {point : X}
    (hfixed : outer (inner point) = point) :
    inner (outer (inner point)) = inner point := by
  rw [hfixed]

variable [Preorder X]

/-- A pre-fixed point rotates forward through a monotone prefix. -/
theorem isPrefixed_comp_rotate {outer inner : X → X}
    (hinner : Monotone inner) {point : X}
    (hprefixed : outer (inner point) ≤ point) :
    inner (outer (inner point)) ≤ inner point :=
  hinner hprefixed

variable {A : Type*}

omit [Preorder X] in
/-- A fixed point of a whole list propagates to a fixed point after every
prefix/suffix rotation. -/
theorem isFixedPt_foldl_split_rotate (step : X → A → X)
    (front back : List A) (point : X)
    (hfixed : (front ++ back).foldl step point = point) :
    (back ++ front).foldl step (front.foldl step point) =
      front.foldl step point := by
  simp only [List.foldl_append] at hfixed ⊢
  rw [hfixed]

private theorem monotone_foldl_step (step : X → A → X)
    {items : List A}
    (hmono : ∀ item ∈ items, Monotone fun point => step point item) :
    Monotone fun point => items.foldl step point := by
  intro first second hle
  induction items generalizing first second with
  | nil => exact hle
  | cons item rest ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact fun candidate hc => hmono candidate (List.mem_cons_of_mem _ hc)
      · exact hmono item (List.mem_cons_self ..) hle

/-- A pre-fixed point of a whole list propagates to a pre-fixed point after
every prefix/suffix rotation when the prefix maps are monotone. -/
theorem isPrefixed_foldl_split_rotate (step : X → A → X)
    (front back : List A) (point : X)
    (hmono : ∀ item ∈ front, Monotone fun value => step value item)
    (hprefixed : (front ++ back).foldl step point ≤ point) :
    (back ++ front).foldl step (front.foldl step point) ≤
      front.foldl step point := by
  simp only [List.foldl_append] at hprefixed ⊢
  exact monotone_foldl_step step hmono hprefixed

omit [Preorder X] in
/-- List-level fixed-point rotation for the split after `index` entries. -/
theorem isFixedPt_foldl_rotate (step : X → A → X)
    (items : List A) (point : X) (index : ℕ) (hindex : index ≤ items.length)
    (hfixed : items.foldl step point = point) :
    (items.rotate index).foldl step (items.take index |>.foldl step point) =
      (items.take index).foldl step point := by
  rw [List.rotate_eq_drop_append_take hindex]
  apply isFixedPt_foldl_split_rotate
  simpa only [List.take_append_drop] using hfixed

/-- List-level pre-fixed-point rotation for the split after `index` entries. -/
theorem isPrefixed_foldl_rotate (step : X → A → X)
    (items : List A) (point : X) (index : ℕ) (hindex : index ≤ items.length)
    (hmono : ∀ item ∈ items, Monotone fun value => step value item)
    (hprefixed : items.foldl step point ≤ point) :
    (items.rotate index).foldl step (items.take index |>.foldl step point) ≤
      (items.take index).foldl step point := by
  rw [List.rotate_eq_drop_append_take hindex]
  apply isPrefixed_foldl_split_rotate
  · intro item hitem
    exact hmono item (List.mem_of_mem_take hitem)
  · simpa only [List.take_append_drop] using hprefixed

/-- Every cyclic rotation of a nonnegative-slope max-affine list inherits the
propagated pre-fixed witness. -/
theorem isPrefixed_foldl_apply_rotate (labels : List Label) (point : ℝ)
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope)
    (hprefixed : labels.foldl (fun value label => label.apply value) point ≤ point)
    (index : ℕ) (hindex : index ≤ labels.length) :
    (labels.rotate index).foldl (fun value label => label.apply value)
        (labels.take index |>.foldl (fun value label => label.apply value) point) ≤
      (labels.take index |>.foldl (fun value label => label.apply value) point) := by
  apply isPrefixed_foldl_rotate
  · exact hindex
  · intro label hlabel
    exact Label.monotone_apply (hslope label hlabel)
  · exact hprefixed

end Rotation

end MaxAffineTransport

end

end Maths
