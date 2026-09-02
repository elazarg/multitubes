/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Basic
public import Maths.Recursion.CyclicMaxAffine
public import Maths.Graph.EdgeGraph
public import Maths.Recursion.InverseCoordinate
public import Maths.Recursion.TransferSummary
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.WithBot

import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Max-affine transport on a directed multigraph

A finite directed multigraph whose edges are labelled by max-affine self-maps
of the line, monotone at the nonnegative slopes used below.  A walk transports
a real number by composing its edge maps in chronological order; a closed walk
therefore acts on the line by an endomorphism.  The obstruction theory of that
action is the subject of this file.

The label of an edge is a triple `(floor, shift, slope)` acting by
`x ↦ max floor (shift + slope * x)`, with the floor allowed to be `⊥`, in which
case the action is the affine map `x ↦ shift + slope * x`.  Admitting `⊥`
supplies the identity `(⊥, 0, 1)` that the finite-floor class of
`TransferSummary.MaxAffineSummary` lacks
(`TransferSummary.MaxAffineSummary.not_exists_apply_eq_id`), so the
nonnegative-slope labels form a monoid acting on `ℝ`, and it embeds both the
affine summaries (at floor `⊥`) and the max-affine summaries (at coerced
floors).

The labelled graph is a monoid-valued generalization of the group-labelled
gain graphs of Zaslavsky, whose labels invert under edge reversal while these
generally do not, and the composite label of a walk is its holonomy.  The vertex
operator `φ v ↦ sup over incoming edges of the label actions` is the max-only
corner of a *min-max function network*; its slope-`1` sublattice consists of
*topical* maps, and the slope-`1` translation case is the theory of *timed event
graphs* of max-plus discrete-event systems.  Per vertex, a label action is a
one-step Bellman or Snell operator of a scalar optimal-stopping problem.  With
general nonnegative slopes the object is monotone but not additively
homogeneous, and appears to carry no established name.

`Maths.Multitubes.MaxAffine.Additive` identifies unit-slope
translation labels with additive potentials and coboundaries. At reflected
labels `(↑0, -g, a)` the transport along a path is the Lindley orbit
`Maths.TransferSummary.reflectedIter`
(`holonomyApply_eq_reflectedIter`), whose survival-weighted representation is
`Maths.TransferSummary.reflectedIter_eq_sup'`.

`Maths.Multitubes.Basic` is the generic semantic layer.  `toTransport`
reads a max-affine labelling as a constant-fiber transport on `ℝ`, and
`holonomyApply` is `Maths.transport` at those edge actions.
The theorem `holonomyApply_eq_walkLabel_smul` identifies it with
`Maths.walkLabel` in the nonnegative-slope label monoid.
The affine part of a composite label is represented by the transfer matrices of
`Maths.InverseCoordinate.affineTransferMatrix` through
`toTransferMatrix`.

Eigenvalue problems for the vertex operator are outside this file.  The vertex
operator itself, the identification of a lax section with one of its sub-fixed
points, and its eigenvectors in the topical regime are the subject of
`Maths.Multitubes.MaxAffine.FixedPoint`; its eigenvectors below unit slope
modulus, where the operator contracts, the subject of
`Maths.Multitubes.MaxAffine.Contraction`; and its eigenvectors at nonnegative
slopes straddling one, where neither mechanism is available and an exponential
change of coordinates makes Brouwer's theorem applicable instead, the subject of
`Maths.Multitubes.MaxAffine.Eigenproblem`.  What is settled there is existence
and not the value of the eigenvalue; the **least** eigenvalue is the optimum
of a finite linear program, by `Maths.Multitubes.MaxAffine.LeastEigenvalue`.

## Main definitions

* `Maths.MaxAffineTransport.Label`, its `apply`, `comp`, `id`, the `Monoid`
  instance on nonnegative-slope labels and the `MulAction` on `ℝ`.
* `Maths.MaxAffineTransport.Label.ofAffine`,
  `Maths.MaxAffineTransport.Label.ofAffineHom`,
  `Maths.MaxAffineTransport.Label.ofMaxAffine`,
  `Maths.MaxAffineTransport.Label.ofMaxAffineHom` -- the two embeddings of
  `Maths.TransferSummary`'s classes.
* `Maths.MaxAffineTransport.Label.toTransferMatrix` -- affine summaries as
  `2 × 2` transfer matrices.
* `Maths.MaxAffineTransport.IsLaxSection`, `defect` -- the lax section and
  its edgewise residual.
* `Maths.MaxAffineTransport.holonomyApply` -- chronological transport along a
  walk.
* `Maths.MaxAffineTransport.slopeProd`, `suffixWeight`, `suffixWeightSum`,
  `weightedDefect` -- the survival-weighted accounting along an edge list.
* `Maths.MaxAffineTransport.cyclicLabel`, `cyclicChain`, `cyclicHolonomy` -- one
  turn of a cyclic max-affine system read as a composite label action.

## Main results

* `Maths.MaxAffineTransport.Label.apply_comp`,
  `Maths.MaxAffineTransport.Label.comp_assoc` -- the composition law, at
  nonnegative outer slope.
* `Maths.MaxAffineTransport.Label.apply_add_le` -- the one-sided Lipschitz
  estimate `apply f (x + d) ≤ apply f x + slope * d` for `0 ≤ d`.
* `Maths.MaxAffineTransport.holonomyApply_le_add_weightedDefect` -- the
  **weighted-defect telescope**: transport along a walk is bounded by the value
  of the candidate at the far end plus the positive parts of the edge defects,
  each weighted by the product of the slopes traversed after it.
* `Maths.MaxAffineTransport.holonomyApply_cycle_le` -- a lax section makes
  its value at the base vertex a pre-fixed point of every cycle's composite
  action.
* `Maths.MaxAffineTransport.Label.exists_apply_le_self_iff` -- the expansivity
  trichotomy: a single label has a pre-fixed point exactly when its slope is
  below one, or is one with nonpositive shift, or exceeds one with the floor
  below the affine fixed point.
* `Maths.MaxAffineTransport.exists_edge_defect_ge` -- the quantitative
  obstruction dual to the telescope.
* `Maths.MaxAffineTransport.cyclicSolution_cyclicChain` -- a fixed point of one
  turn of the cyclic labels is a `Maths.CyclicMaxAffine.CyclicSolution`.

## Implementation notes

This file develops the label algebra, walk semantics, weak duality, and the
quantitative obstruction.  `Maths.Multitubes.MaxAffine.Sections` proves section
existence in the subunit-slope and slope-one regimes;
`Maths.Multitubes.MaxAffine.Farkas` gives the finite linear-system alternative for
general labels.

## References

* J. Gunawardena, *Min-max functions*, Discrete Event Dynamic Systems 4 (1994),
  377-407, for min-max function networks.
* S. Gaubert and J. Gunawardena, *The Perron--Frobenius theorem for homogeneous,
  monotone functions*, Trans. Amer. Math. Soc. 356 (2004), 4931-4950, for
  topical maps.
* F. Baccelli, G. Cohen, G. J. Olsder and J.-P. Quadrat, *Synchronization and
  Linearity*, Wiley (1992), for timed event graphs.
* T. Zaslavsky, *Biased graphs. I. Bias, balance, and gains*, J. Combin. Theory
  Ser. B 47 (1989), 32-52, for gain graphs.

## Tags

max-affine, tropical, max-plus, gain graph, holonomy, lax section, topical map
-/

@[expose] public section

noncomputable section

namespace Maths.MaxAffineTransport

/-! ## The label algebra -/

/-- Coefficients of a max-affine self-map of the line with a floor in
`WithBot ℝ`, monotone exactly when the slope is nonnegative.  The map is
`x ↦ max floor (shift + slope * x)`, read as the affine
map `x ↦ shift + slope * x` when the floor is `⊥`. -/
@[ext] structure Label where
  /-- The floor the map never falls below, or `⊥` for no floor at all. -/
  floor : WithBot ℝ
  /-- The additive part of the affine branch. -/
  shift : ℝ
  /-- The multiplicative part of the affine branch. -/
  slope : ℝ

namespace Label

/-- The affine branch of a label. -/
def affinePart (f : Label) (x : ℝ) : ℝ := f.shift + f.slope * x

/-- The action of a label, computed in `WithBot ℝ`. -/
def applyBot (f : Label) (x : ℝ) : WithBot ℝ :=
  f.floor ⊔ ((f.affinePart x : ℝ) : WithBot ℝ)

/-- The action of a label on the line.  The affine branch is never `⊥`, so the
action lands in `ℝ` whatever the floor. -/
def apply (f : Label) (x : ℝ) : ℝ := (f.applyBot x).unbotD 0

/-- Every floor is either absent or a real number. -/
theorem floor_cases (f : Label) : f.floor = ⊥ ∨ ∃ e : ℝ, f.floor = (e : WithBot ℝ) := by
  rcases Option.eq_none_or_eq_some f.floor with hfloor | ⟨e, hfloor⟩
  · exact Or.inl hfloor
  · exact Or.inr ⟨e, hfloor⟩

theorem apply_of_floor_bot {f : Label} (hfloor : f.floor = ⊥) (x : ℝ) :
    f.apply x = f.affinePart x := by
  simp [apply, applyBot, hfloor]

theorem apply_of_floor_coe {f : Label} {e : ℝ} (hfloor : f.floor = (e : WithBot ℝ)) (x : ℝ) :
    f.apply x = max e (f.affinePart x) := by
  simp [apply, applyBot, hfloor, ← WithBot.coe_sup]

@[simp] theorem apply_mk_bot (t a x : ℝ) : (mk ⊥ t a).apply x = t + a * x :=
  apply_of_floor_bot rfl x

@[simp] theorem apply_mk_coe (e t a x : ℝ) :
    (mk (e : WithBot ℝ) t a).apply x = max e (t + a * x) :=
  apply_of_floor_coe rfl x

/-- The real action is the `WithBot`-valued action: the latter never takes the
value `⊥`. -/
theorem coe_apply (f : Label) (x : ℝ) : ((f.apply x : ℝ) : WithBot ℝ) = f.applyBot x := by
  rcases f.floor_cases with hfloor | ⟨e, hfloor⟩
  · rw [apply_of_floor_bot hfloor, applyBot, hfloor, bot_sup_eq]
  · rw [apply_of_floor_coe hfloor, applyBot, hfloor, ← WithBot.coe_sup]

/-- The floor is never undercut. -/
theorem floor_le_coe_apply (f : Label) (x : ℝ) :
    f.floor ≤ ((f.apply x : ℝ) : WithBot ℝ) := by
  rw [coe_apply]
  exact le_sup_left

/-- A label is dominated by a point exactly when both its floor and its affine
branch are. -/
theorem apply_le_iff (f : Label) (x : ℝ) :
    f.apply x ≤ x ↔ f.floor ≤ (x : WithBot ℝ) ∧ f.affinePart x ≤ x := by
  rcases f.floor_cases with hfloor | ⟨e, hfloor⟩
  · rw [apply_of_floor_bot hfloor, hfloor]
    exact ⟨fun h => ⟨bot_le, h⟩, fun h => h.2⟩
  · rw [apply_of_floor_coe hfloor, hfloor, max_le_iff, WithBot.coe_le_coe]

/-- A label is dominated at a target value exactly when both its floor and its
affine branch are. -/
theorem apply_le_target_iff (f : Label) (x y : ℝ) :
    f.apply x ≤ y ↔ f.floor ≤ (y : WithBot ℝ) ∧ f.affinePart x ≤ y := by
  rcases f.floor_cases with hfloor | ⟨e, hfloor⟩
  · rw [apply_of_floor_bot hfloor, hfloor]
    exact ⟨fun h => ⟨bot_le, h⟩, fun h => h.2⟩
  · rw [apply_of_floor_coe hfloor, hfloor, max_le_iff, WithBot.coe_le_coe]

/-- The affine branch never exceeds the action. -/
theorem affinePart_le_apply (f : Label) (x : ℝ) : f.affinePart x ≤ f.apply x := by
  rcases f.floor_cases with hfloor | ⟨floor, hfloor⟩
  · exact le_of_eq (apply_of_floor_bot hfloor x).symm
  · rw [apply_of_floor_coe hfloor]
    exact le_max_right floor (f.affinePart x)

/-- The action is monotone at nonnegative slope. -/
theorem monotone_apply {f : Label} (hslope : 0 ≤ f.slope) : Monotone f.apply := by
  intro x y hxy
  have hbranch : f.affinePart x ≤ f.affinePart y := by
    have := mul_le_mul_of_nonneg_left hxy hslope
    simp only [affinePart]
    linarith
  rcases f.floor_cases with hfloor | ⟨e, hfloor⟩
  · rw [apply_of_floor_bot hfloor, apply_of_floor_bot hfloor]
    exact hbranch
  · rw [apply_of_floor_coe hfloor, apply_of_floor_coe hfloor]
    exact max_le_max le_rfl hbranch

/-- **The one-sided Lipschitz estimate.**  Moving the argument up by `d` moves
the value up by at most `slope * d`.  This is what makes the walk telescope of
`holonomyApply_le_add_weightedDefect` weight the edge residuals by slope
products. -/
theorem apply_add_le {f : Label} (hslope : 0 ≤ f.slope) (x : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    f.apply (x + d) ≤ f.apply x + f.slope * d := by
  have hbranch : f.affinePart (x + d) = f.affinePart x + f.slope * d := by
    simp only [affinePart]
    ring
  have hmul : 0 ≤ f.slope * d := mul_nonneg hslope hd
  rcases f.floor_cases with hfloor | ⟨e, hfloor⟩
  · rw [apply_of_floor_bot hfloor, apply_of_floor_bot hfloor, hbranch]
  · rw [apply_of_floor_coe hfloor, apply_of_floor_coe hfloor, hbranch]
    exact max_le (by have := le_max_left e (f.affinePart x); linarith)
      (by have := le_max_right e (f.affinePart x); linarith)

/-! ### Composition -/

/-- The image of a floor under an affine map, with the absent floor preserved.
`WithBot` arithmetic is avoided deliberately: at slope `0` the product of the
slope with an absent floor is not the absent floor. -/
def pushFloor (shift slope : ℝ) (b : WithBot ℝ) : WithBot ℝ :=
  b.map fun e => shift + slope * e

@[simp] theorem pushFloor_bot (shift slope : ℝ) : pushFloor shift slope ⊥ = ⊥ := rfl

@[simp] theorem pushFloor_coe (shift slope e : ℝ) :
    pushFloor shift slope (e : WithBot ℝ) = ((shift + slope * e : ℝ) : WithBot ℝ) := rfl

@[simp] theorem pushFloor_id (b : WithBot ℝ) : pushFloor 0 1 b = b := by
  cases b with
  | bot => rfl
  | coe e => simp

/-- A nonnegative slope pushes floors through suprema. -/
theorem pushFloor_sup {slope : ℝ} (hslope : 0 ≤ slope) (shift : ℝ) (b c : WithBot ℝ) :
    pushFloor shift slope (b ⊔ c) = pushFloor shift slope b ⊔ pushFloor shift slope c := by
  cases b with
  | bot => simp
  | coe u =>
      cases c with
      | bot => simp
      | coe v =>
          rw [← WithBot.coe_sup, pushFloor_coe, pushFloor_coe, pushFloor_coe, ← WithBot.coe_sup,
            WithBot.coe_inj]
          change shift + slope * max u v = max (shift + slope * u) (shift + slope * v)
          rw [mul_max_of_nonneg _ _ hslope, ← max_add_add_left]

theorem pushFloor_pushFloor (t a t' a' : ℝ) (b : WithBot ℝ) :
    pushFloor t a (pushFloor t' a' b) = pushFloor (t + a * t') (a * a') b := by
  cases b with
  | bot => simp
  | coe e =>
      rw [pushFloor_coe, pushFloor_coe, pushFloor_coe, WithBot.coe_inj]
      ring

/-- Chronological composition: `outer.comp inner` passes the state through
`inner` first.  The floor of the composite is the outer floor joined with the
inner floor pushed through the outer affine branch. -/
def comp (outer inner : Label) : Label where
  floor := outer.floor ⊔ pushFloor outer.shift outer.slope inner.floor
  shift := outer.shift + outer.slope * inner.shift
  slope := outer.slope * inner.slope

@[simp] theorem floor_comp (outer inner : Label) :
    (outer.comp inner).floor = outer.floor ⊔ pushFloor outer.shift outer.slope inner.floor := rfl

@[simp] theorem shift_comp (outer inner : Label) :
    (outer.comp inner).shift = outer.shift + outer.slope * inner.shift := rfl

@[simp] theorem slope_comp (outer inner : Label) :
    (outer.comp inner).slope = outer.slope * inner.slope := rfl

theorem applyBot_comp {outer : Label} (hslope : 0 ≤ outer.slope) (inner : Label) (x : ℝ) :
    (outer.comp inner).applyBot x = outer.applyBot (inner.apply x) := by
  have hpush : pushFloor outer.shift outer.slope ((inner.affinePart x : ℝ) : WithBot ℝ)
      = (((outer.comp inner).affinePart x : ℝ) : WithBot ℝ) := by
    rw [pushFloor_coe, WithBot.coe_inj]
    simp only [affinePart, shift_comp, slope_comp]
    ring
  calc (outer.comp inner).applyBot x
      = (outer.floor ⊔ pushFloor outer.shift outer.slope inner.floor)
          ⊔ (((outer.comp inner).affinePart x : ℝ) : WithBot ℝ) := rfl
    _ = outer.floor ⊔ (pushFloor outer.shift outer.slope inner.floor
          ⊔ pushFloor outer.shift outer.slope ((inner.affinePart x : ℝ) : WithBot ℝ)) := by
        rw [hpush, sup_assoc]
    _ = outer.floor ⊔ pushFloor outer.shift outer.slope (inner.applyBot x) := by
        rw [applyBot, pushFloor_sup hslope]
    _ = outer.applyBot (inner.apply x) := by rw [← coe_apply]; rfl

/-- **Coefficient composition represents composition of the actions**, under the
nonnegativity of the outer slope that lets it be pushed through the inner
supremum. -/
theorem apply_comp {outer : Label} (hslope : 0 ≤ outer.slope) (inner : Label) (x : ℝ) :
    (outer.comp inner).apply x = outer.apply (inner.apply x) := by
  simp only [apply, applyBot_comp hslope]

/-- Composition is associative as soon as the outermost slope is nonnegative;
the inner slopes are unconstrained. -/
theorem comp_assoc {first : Label} (hfirst : 0 ≤ first.slope) (second third : Label) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  refine Label.ext ?_ ?_ ?_
  · simp only [floor_comp, shift_comp, slope_comp]
    rw [pushFloor_sup hfirst, pushFloor_pushFloor, sup_assoc]
  · simp only [shift_comp, slope_comp]
    ring
  · simp only [slope_comp]
    ring

/-- The identity label: no floor, no shift, unit slope. -/
def id : Label := ⟨⊥, 0, 1⟩

@[simp] theorem floor_id : id.floor = ⊥ := rfl

@[simp] theorem shift_id : id.shift = 0 := rfl

@[simp] theorem slope_id : id.slope = 1 := rfl

@[simp] theorem apply_id (x : ℝ) : id.apply x = x := by
  rw [apply_of_floor_bot rfl]
  simp [affinePart]

theorem id_comp (f : Label) : id.comp f = f := by
  refine Label.ext ?_ ?_ ?_ <;> simp

theorem comp_id (f : Label) : f.comp id = f := by
  refine Label.ext ?_ ?_ ?_ <;> simp

theorem slope_comp_pos {outer inner : Label} (houter : 0 < outer.slope)
    (hinner : 0 < inner.slope) : 0 < (outer.comp inner).slope :=
  mul_pos houter hinner

theorem slope_comp_nonneg {outer inner : Label} (houter : 0 ≤ outer.slope)
    (hinner : 0 ≤ inner.slope) : 0 ≤ (outer.comp inner).slope :=
  mul_nonneg houter hinner

/-- **Nonnegative-slope labels form a monoid.**  The identity is `(⊥, 0, 1)`;
the finite-floor class of `TransferSummary.MaxAffineSummary` has none.
Slope zero is admitted: the composite then ignores its inner label, exactly as
the constant action does. -/
instance instMonoid : Monoid {f : Label // 0 ≤ f.slope} where
  mul outer inner := ⟨outer.1.comp inner.1, slope_comp_nonneg outer.2 inner.2⟩
  one := ⟨id, by simp⟩
  mul_assoc first second third := Subtype.ext (comp_assoc first.2 second.1 third.1)
  one_mul f := Subtype.ext (id_comp f.1)
  mul_one f := Subtype.ext (comp_id f.1)

@[simp] theorem val_mul (outer inner : {f : Label // 0 ≤ f.slope}) :
    (outer * inner).1 = outer.1.comp inner.1 := rfl

@[simp] theorem val_one : (1 : {f : Label // 0 ≤ f.slope}).1 = id := rfl

instance instSMul : SMul {f : Label // 0 ≤ f.slope} ℝ where
  smul f x := f.1.apply x

@[simp] theorem smul_eq_apply (f : {f : Label // 0 ≤ f.slope}) (x : ℝ) :
    f • x = f.1.apply x := rfl

/-- Nonnegative-slope labels act on the line by their max-affine maps. -/
instance instMulAction : MulAction {f : Label // 0 ≤ f.slope} ℝ where
  one_smul x := apply_id x
  mul_smul outer inner x := apply_comp outer.2 inner.1 x

/-! ### Composite labels of a list -/

/-- The composite label of a list of labels, the head acting first. This is the
coefficient form of the fold of
`Maths.MaxAffineTransport.holonomyApply_eq_foldl_map`. -/
def compList (labels : List Label) : Label :=
  labels.foldl (fun accumulated next => next.comp accumulated) Label.id

@[simp] theorem compList_nil : compList [] = Label.id := rfl

/-- Appending one chronological label composes it outside the preceding
composite.  No slope hypothesis is needed for this definitional fold law. -/
@[simp] theorem compList_append_singleton (labels : List Label) (last : Label) :
    compList (labels ++ [last]) = last.comp (compList labels) := by
  simp [compList, List.foldl_append]

theorem apply_foldl_comp : ∀ (labels : List Label),
    (∀ label ∈ labels, 0 ≤ label.slope) → ∀ accumulated : Label,
      0 ≤ accumulated.slope → ∀ point : ℝ,
        (labels.foldl (fun result next => next.comp result) accumulated).apply point =
          labels.foldl (fun value label => label.apply value) (accumulated.apply point)
  | [], _, _, _, _ => rfl
  | first :: rest, hslope, accumulated, haccumulated, point => by
      have hrest (label : Label) (hlabel : label ∈ rest) : 0 ≤ label.slope :=
        hslope label (List.mem_cons_of_mem _ hlabel)
      have hfirst : 0 ≤ first.slope := hslope first (List.mem_cons_self ..)
      rw [List.foldl_cons, List.foldl_cons,
        apply_foldl_comp rest hrest (first.comp accumulated)
          (slope_comp_nonneg hfirst haccumulated) point,
        apply_comp hfirst accumulated point]

/-- At nonnegative slopes the composite label acts by the fold of the actions. -/
theorem apply_compList {labels : List Label}
    (hslope : ∀ label ∈ labels, 0 ≤ label.slope) (point : ℝ) :
    (compList labels).apply point =
      labels.foldl (fun value label => label.apply value) point := by
  rw [compList, apply_foldl_comp labels hslope Label.id (by simp) point, apply_id]

/-- Appending chronological label lists first applies the first composite and
then the second composite. -/
theorem apply_compList_append (first second : List Label)
    (hslope : ∀ label ∈ first ++ second, 0 ≤ label.slope) (point : ℝ) :
    (compList (first ++ second)).apply point =
      (compList second).apply ((compList first).apply point) := by
  have hfirst (label : Label) (hlabel : label ∈ first) : 0 ≤ label.slope :=
    hslope label (List.mem_append_left second hlabel)
  have hsecond (label : Label) (hlabel : label ∈ second) : 0 ≤ label.slope :=
    hslope label (List.mem_append_right first hlabel)
  rw [apply_compList hslope, List.foldl_append,
    apply_compList hfirst, apply_compList hsecond]

/-- A final chronological label acts after the composite of the preceding
labels. -/
theorem apply_compList_append_singleton (labels : List Label) (last : Label)
    (hlast : 0 ≤ last.slope) (point : ℝ) :
    (compList (labels ++ [last])).apply point =
      last.apply ((compList labels).apply point) := by
  rw [compList_append_singleton, apply_comp hlast]

/-! ### The two embeddings -/

/-- An affine summary as a label with no floor. -/
def ofAffine (f : TransferSummary.AffineSummary) : Label := ⟨⊥, f.shift, f.slope⟩

@[simp] theorem floor_ofAffine (f : TransferSummary.AffineSummary) :
    (ofAffine f).floor = ⊥ := rfl

@[simp] theorem slope_ofAffine (f : TransferSummary.AffineSummary) :
    (ofAffine f).slope = f.slope := rfl

/-- The floorless embedding preserves the action. -/
@[simp] theorem apply_ofAffine (f : TransferSummary.AffineSummary) (x : ℝ) :
    (ofAffine f).apply x = f.apply x :=
  apply_of_floor_bot rfl x

/-- The floorless embedding preserves composition, at every slope. -/
theorem ofAffine_comp (outer inner : TransferSummary.AffineSummary) :
    ofAffine (outer.comp inner) = (ofAffine outer).comp (ofAffine inner) := by
  refine Label.ext ?_ rfl rfl
  simp

theorem ofAffine_one : ofAffine 1 = id := rfl

/-- The nonnegative-slope affine summaries, a submonoid of the `ax + b`
monoid. -/
def affineNonnegSubmonoid : Submonoid TransferSummary.AffineSummary where
  carrier := {f | 0 ≤ f.slope}
  mul_mem' hf hg := by
    change (0 : ℝ) ≤ _ * _
    exact mul_nonneg hf hg
  one_mem' := by
    change (0 : ℝ) ≤ 1
    exact zero_le_one

/-- **The floorless embedding as a monoid homomorphism.**  On nonnegative
slopes both sides are monoids and the embedding respects their laws. -/
def ofAffineHom : affineNonnegSubmonoid →* {f : Label // 0 ≤ f.slope} where
  toFun f := ⟨ofAffine f.1, show (0 : ℝ) ≤ f.1.slope from f.2⟩
  map_one' := rfl
  map_mul' outer inner := Subtype.ext (ofAffine_comp outer.1 inner.1)

/-- A max-affine summary as a label with a coerced floor. -/
def ofMaxAffine (f : TransferSummary.MaxAffineSummary) : Label :=
  ⟨(f.floor : WithBot ℝ), f.shift, f.slope⟩

@[simp] theorem floor_ofMaxAffine (f : TransferSummary.MaxAffineSummary) :
    (ofMaxAffine f).floor = (f.floor : WithBot ℝ) := rfl

@[simp] theorem slope_ofMaxAffine (f : TransferSummary.MaxAffineSummary) :
    (ofMaxAffine f).slope = f.slope := rfl

/-- The finite-floor embedding preserves the action. -/
@[simp] theorem apply_ofMaxAffine (f : TransferSummary.MaxAffineSummary) (x : ℝ) :
    (ofMaxAffine f).apply x = f.apply x :=
  apply_of_floor_coe rfl x

/-- The finite-floor embedding preserves the coefficient composition law.  The
two composites represent composition of the actions only at nonnegative outer
slope, where `TransferSummary.MaxAffineSummary.apply_comp` and `apply_comp`
apply. -/
theorem ofMaxAffine_comp (outer inner : TransferSummary.MaxAffineSummary) :
    ofMaxAffine (outer.comp inner) = (ofMaxAffine outer).comp (ofMaxAffine inner) := by
  refine Label.ext ?_ rfl rfl
  change ((max outer.floor (outer.shift + outer.slope * inner.floor) : ℝ) : WithBot ℝ)
    = (outer.floor : WithBot ℝ) ⊔ pushFloor outer.shift outer.slope (inner.floor : WithBot ℝ)
  rw [pushFloor_coe, ← WithBot.coe_sup, WithBot.coe_inj]

/-- The finite-floor embedding is injective: a label determines the summary it
comes from. -/
theorem ofMaxAffine_injective : Function.Injective ofMaxAffine := by
  intro f g hfg
  have hfloor : (f.floor : WithBot ℝ) = (g.floor : WithBot ℝ) := congrArg Label.floor hfg
  exact TransferSummary.MaxAffineSummary.ext (WithBot.coe_inj.mp hfloor)
    (congrArg Label.shift hfg) (congrArg Label.slope hfg)

/-- **The finite-floor embedding as a homomorphism of semigroups.**  The
nonnegative-slope max-affine summaries have no identity
(`TransferSummary.MaxAffineSummary.not_exists_apply_eq_id`), so they form only a
semigroup; the labels supply the missing identity `(⊥, 0, 1)` and this map
identifies that semigroup with the coerced-floor part of the label monoid. -/
def ofMaxAffineHom :
    {f : TransferSummary.MaxAffineSummary // 0 ≤ f.slope} →ₙ* {f : Label // 0 ≤ f.slope} where
  toFun f := ⟨ofMaxAffine f.1, show (0 : ℝ) ≤ f.1.slope from f.2⟩
  map_mul' outer inner := Subtype.ext (ofMaxAffine_comp outer.1 inner.1)

/-- The finite-floor semigroup homomorphism is injective. -/
theorem ofMaxAffineHom_injective : Function.Injective ofMaxAffineHom := fun _ _ hfg =>
  Subtype.ext (ofMaxAffine_injective (Subtype.ext_iff.mp hfg))

/-- **Affine summaries as transfer matrices.**  The upper-triangular matrices
of `InverseCoordinate.affineTransferMatrix` carry the composition law of
the summary monoid, which is
`InverseCoordinate.affineTransferMatrix_mul`. -/
def toTransferMatrix : TransferSummary.AffineSummary →* Matrix (Fin 2) (Fin 2) ℝ where
  toFun f := InverseCoordinate.affineTransferMatrix f.slope f.shift
  map_one' := by
    change InverseCoordinate.affineTransferMatrix 1 0 = 1
    rw [Matrix.one_fin_two]
    rfl
  map_mul' outer inner := by
    change InverseCoordinate.affineTransferMatrix (outer.slope * inner.slope)
        (outer.shift + outer.slope * inner.shift)
      = InverseCoordinate.affineTransferMatrix outer.slope outer.shift *
        InverseCoordinate.affineTransferMatrix inner.slope inner.shift
    rw [InverseCoordinate.affineTransferMatrix_mul, add_comm]

@[simp] theorem toTransferMatrix_apply (f : TransferSummary.AffineSummary) :
    toTransferMatrix f = InverseCoordinate.affineTransferMatrix f.slope f.shift := rfl

/-! ### The expansivity trichotomy -/
theorem le_coe_unbotD (b : WithBot ℝ) (d : ℝ) : b ≤ ((b.unbotD d : ℝ) : WithBot ℝ) := by
  cases b with
  | bot => exact bot_le
  | coe e => simp

/-- **The expansivity trichotomy.**  A label admits a pre-fixed point exactly
when its slope is below one, or equals one with nonpositive shift, or exceeds
one with the floor below the fixed point of its affine branch.  The condition
is decidable in the coefficients, and applied to the composite label of a
cycle it decides existence of a pre-fixed point for that cycle's action.  No
sign condition on the slope is needed: a negative slope falls in the first
case of the trichotomy. -/
theorem exists_apply_le_self_iff (f : Label) :
    (∃ x : ℝ, f.apply x ≤ x) ↔
      f.slope < 1 ∨ (f.slope = 1 ∧ f.shift ≤ 0) ∨
        (1 < f.slope ∧ f.floor ≤ ((-f.shift / (f.slope - 1) : ℝ) : WithBot ℝ)) := by
  constructor
  · rintro ⟨x, hx⟩
    rw [apply_le_iff] at hx
    obtain ⟨hfloor, hbranch⟩ := hx
    rw [affinePart] at hbranch
    rcases lt_trichotomy f.slope 1 with hlt | heq | hgt
    · exact Or.inl hlt
    · refine Or.inr (Or.inl ⟨heq, ?_⟩)
      rw [heq] at hbranch
      linarith
    · refine Or.inr (Or.inr ⟨hgt, ?_⟩)
      have hpos : 0 < f.slope - 1 := by linarith
      have hx' : x ≤ -f.shift / (f.slope - 1) := by
        rw [le_div_iff₀ hpos]
        nlinarith
      exact hfloor.trans (WithBot.coe_le_coe.mpr hx')
  · intro htrichotomy
    rcases htrichotomy with hlt | ⟨heq, hshift⟩ | ⟨hgt, hfloor⟩
    · have hpos : 0 < 1 - f.slope := by linarith
      refine ⟨max (f.floor.unbotD 0) (f.shift / (1 - f.slope)), ?_⟩
      rw [apply_le_iff]
      refine ⟨(le_coe_unbotD f.floor 0).trans (WithBot.coe_le_coe.mpr (le_max_left _ _)), ?_⟩
      have hge := (div_le_iff₀ hpos).mp (le_max_right (f.floor.unbotD 0)
        (f.shift / (1 - f.slope)))
      simp only [affinePart]
      nlinarith
    · refine ⟨f.floor.unbotD 0, ?_⟩
      rw [apply_le_iff]
      refine ⟨le_coe_unbotD f.floor 0, ?_⟩
      simp only [affinePart, heq]
      linarith
    · have hne : f.slope - 1 ≠ 0 := by intro hcon; linarith
      refine ⟨-f.shift / (f.slope - 1), ?_⟩
      rw [apply_le_iff]
      refine ⟨hfloor, le_of_eq ?_⟩
      simp only [affinePart]
      field_simp
      ring

end Label

/-! ## The graph layer -/
section Graph

universe uV uE

variable {V : Type uV} {E : Type uE} {G : Maths.EdgeGraph V E}

/-- A **lax section**: traversing an edge does not increase the
candidate beyond its value at the head of that edge.  Also called a
subsolution, a subinvariant family, a superharmonic section, or an
inductive invariant. -/
def IsLaxSection (G : EdgeGraph V E) (label : E → Label) (φ : V → ℝ) : Prop :=
  ∀ e : E, (label e).apply (φ (G.source e)) ≤ φ (G.target e)

/-- The amount by which a candidate fails the edge inequality.  Also called the
edge slack or the residual of the edge. -/
def defect (G : EdgeGraph V E) (label : E → Label) (φ : V → ℝ) (e : E) : ℝ :=
  (label e).apply (φ (G.source e)) - φ (G.target e)

theorem isLaxSection_iff_forall_defect_nonpos (G : EdgeGraph V E) (label : E → Label)
    (φ : V → ℝ) : IsLaxSection G label φ ↔ ∀ e : E, defect G label φ e ≤ 0 := by
  simp [IsLaxSection, defect]

/-! ### Transport along a walk -/

/-- Transport along a walk: the actions of the traversed edges composed in
chronological order.  For a closed walk this is the action of the walk's
holonomy. -/
def holonomyApply (label : E → Label) {start finish : V}
    (walk : G.Walk start finish) : ℝ → ℝ :=
  Maths.transport (fun e x => (label e).apply x) walk

@[simp] theorem holonomyApply_nil (label : E → Label) {start : V} (x : ℝ) :
    holonomyApply label (.nil : G.Walk start start) x = x := rfl

@[simp] theorem holonomyApply_concat (label : E → Label) {start finish : V}
    (walk : G.Walk start finish) (edge : E) (legal : G.source edge = finish) (x : ℝ) :
    holonomyApply label (walk.concat edge legal) x
      = (label edge).apply (holonomyApply label walk x) := rfl

theorem holonomyApply_eq_foldl (label : E → Label) {start finish : V}
    (walk : G.Walk start finish) (x : ℝ) :
    holonomyApply label walk x = walk.edges.foldl (fun y e => (label e).apply y) x := by
  induction walk with
  | nil => rfl
  | concat walkSoFar edge legal ih =>
      rw [holonomyApply_concat, EdgeGraph.Walk.edges_concat, List.foldl_append, ih]
      rfl

theorem holonomyApply_eq_foldl_map (label : E → Label) {start finish : V}
    (walk : G.Walk start finish) (x : ℝ) :
    holonomyApply label walk x = (walk.edges.map label).foldl (fun y f => f.apply y) x := by
  rw [holonomyApply_eq_foldl, List.foldl_map]

/-- The composite label of a walk acts by transport along that walk. -/
theorem apply_compList_edges
    {label : E → Label} (hslope : ∀ edge : E, 0 ≤ (label edge).slope)
    {start finish : V} (walk : G.Walk start finish) (point : ℝ) :
    (Label.compList (walk.edges.map label)).apply point =
      holonomyApply label walk point := by
  rw [holonomyApply_eq_foldl_map]
  refine Label.apply_compList (fun candidate hcandidate => ?_) point
  obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hcandidate
  exact hslope edge

/-- At nonnegative slopes the transport is the action of the gain-graph
holonomy `Maths.walkLabel` in the label monoid. -/
theorem holonomyApply_eq_walkLabel_smul
    (label : E → {f : Label // 0 ≤ f.slope}) {start finish : V}
    (walk : G.Walk start finish) (x : ℝ) :
    holonomyApply (fun e => (label e).1) walk x =
      Maths.walkLabel label walk • x :=
  Maths.transport_eq_smul (G := G) (label := label) walk x

/-! ### Survival-weighted accounting along an edge list -/

/-- The product of the slopes of a list of edges. -/
def slopeProd (label : E → Label) (l : List E) : ℝ := (l.map fun e => (label e).slope).prod

@[simp] theorem slopeProd_nil (label : E → Label) : slopeProd label ([] : List E) = 1 := rfl

@[simp] theorem slopeProd_cons (label : E → Label) (e : E) (rest : List E) :
    slopeProd label (e :: rest) = (label e).slope * slopeProd label rest := rfl

@[simp] theorem slopeProd_append (label : E → Label) (first second : List E) :
    slopeProd label (first ++ second) = slopeProd label first * slopeProd label second := by
  simp [slopeProd, List.map_append, List.prod_append]

theorem slopeProd_nonneg {label : E → Label} (hslope : ∀ e : E, 0 ≤ (label e).slope) :
    ∀ l : List E, 0 ≤ slopeProd label l
  | [] => zero_le_one
  | e :: rest => mul_nonneg (hslope e) (slopeProd_nonneg hslope rest)

theorem slopeProd_pos {label : E → Label} (hslope : ∀ e : E, 0 < (label e).slope) :
    ∀ l : List E, 0 < slopeProd label l
  | [] => zero_lt_one
  | e :: rest => mul_pos (hslope e) (slopeProd_pos hslope rest)

/-- The **suffix weight** at a position of an edge list: the product of the
slopes of the edges strictly after that position.  This is the abstract form of
the survival weighting that a later slope applies to an earlier discrepancy. -/
def suffixWeight (label : E → Label) (l : List E) (i : ℕ) : ℝ :=
  slopeProd label (l.drop (i + 1))

/-- The sum of the suffix weights of an edge list. -/
def suffixWeightSum (label : E → Label) : List E → ℝ
  | [] => 0
  | _ :: rest => slopeProd label rest + suffixWeightSum label rest

@[simp] theorem suffixWeightSum_nil (label : E → Label) :
    suffixWeightSum label ([] : List E) = 0 := rfl

@[simp] theorem suffixWeightSum_cons (label : E → Label) (e : E) (rest : List E) :
    suffixWeightSum label (e :: rest) = slopeProd label rest + suffixWeightSum label rest := rfl

/-- The suffix-weighted sum of the positive parts of the edge residuals. -/
def weightedDefect (G : EdgeGraph V E) (label : E → Label) (φ : V → ℝ) : List E → ℝ
  | [] => 0
  | e :: rest =>
      slopeProd label rest * max 0 (defect G label φ e) + weightedDefect G label φ rest

@[simp] theorem weightedDefect_nil (G : EdgeGraph V E) (label : E → Label) (φ : V → ℝ) :
    weightedDefect G label φ ([] : List E) = 0 := rfl

@[simp] theorem weightedDefect_cons (G : EdgeGraph V E) (label : E → Label)
    (φ : V → ℝ) (e : E)
    (rest : List E) :
    weightedDefect G label φ (e :: rest)
      = slopeProd label rest * max 0 (defect G label φ e) + weightedDefect G label φ rest := rfl

/-- The sum of the suffix weights is the sum over the positions of the list. -/
theorem suffixWeightSum_eq_sum (label : E → Label) : ∀ l : List E,
    suffixWeightSum label l = ∑ i : Fin l.length, suffixWeight label l i
  | [] => by simp
  | e :: rest => by
      have hsplit : ∑ i : Fin (e :: rest).length, suffixWeight label (e :: rest) i
          = suffixWeight label (e :: rest) 0
            + ∑ i : Fin rest.length, suffixWeight label (e :: rest) (i.succ : ℕ) :=
        Fin.sum_univ_succ fun i : Fin (rest.length + 1) => suffixWeight label (e :: rest) i
      have htail : ∑ i : Fin rest.length, suffixWeight label (e :: rest) (i.succ : ℕ)
          = ∑ i : Fin rest.length, suffixWeight label rest i :=
        Finset.sum_congr rfl fun i _ => by simp [suffixWeight]
      rw [suffixWeightSum_cons, suffixWeightSum_eq_sum label rest, hsplit, htail]
      simp [suffixWeight]

/-- **The weighted defect sum is the suffix-weighted sum of the positive parts
of the edge residuals. -/
theorem weightedDefect_eq_sum (G : EdgeGraph V E) (label : E → Label) (φ : V → ℝ) :
    ∀ l : List E, weightedDefect G label φ l
      = ∑ i : Fin l.length, suffixWeight label l i * max 0 (defect G label φ (l.get i))
  | [] => by simp
  | e :: rest => by
      have hsplit : ∑ i : Fin (e :: rest).length,
            suffixWeight label (e :: rest) i * max 0 (defect G label φ ((e :: rest).get i))
          = suffixWeight label (e :: rest) 0 * max 0 (defect G label φ ((e :: rest).get 0))
            + ∑ i : Fin rest.length, suffixWeight label (e :: rest) (i.succ : ℕ)
                * max 0 (defect G label φ ((e :: rest).get i.succ)) :=
        Fin.sum_univ_succ fun i : Fin (rest.length + 1) =>
          suffixWeight label (e :: rest) i * max 0 (defect G label φ ((e :: rest).get i))
      have htail : ∑ i : Fin rest.length, suffixWeight label (e :: rest) (i.succ : ℕ)
              * max 0 (defect G label φ ((e :: rest).get i.succ))
          = ∑ i : Fin rest.length,
              suffixWeight label rest i * max 0 (defect G label φ (rest.get i)) :=
        Finset.sum_congr rfl fun i _ => by simp [suffixWeight]
      rw [weightedDefect_cons, weightedDefect_eq_sum G label φ rest, hsplit, htail]
      simp [suffixWeight]

theorem suffixWeightSum_append_singleton (label : E → Label) (e : E) : ∀ l : List E,
    suffixWeightSum label (l ++ [e]) = (label e).slope * suffixWeightSum label l + 1
  | [] => by simp
  | a :: rest => by
      rw [List.cons_append, suffixWeightSum_cons, suffixWeightSum_append_singleton label e rest,
        suffixWeightSum_cons, slopeProd_append]
      simp only [slopeProd_cons, slopeProd_nil]
      ring

theorem weightedDefect_append_singleton (G : EdgeGraph V E) (label : E → Label) (φ : V → ℝ)
    (e : E) : ∀ l : List E, weightedDefect G label φ (l ++ [e])
      = (label e).slope * weightedDefect G label φ l + max 0 (defect G label φ e)
  | [] => by simp
  | a :: rest => by
      rw [List.cons_append, weightedDefect_cons,
        weightedDefect_append_singleton G label φ e rest, weightedDefect_cons, slopeProd_append]
      simp only [slopeProd_cons, slopeProd_nil]
      ring

theorem suffixWeightSum_nonneg {label : E → Label} (hslope : ∀ e : E, 0 ≤ (label e).slope) :
    ∀ l : List E, 0 ≤ suffixWeightSum label l
  | [] => le_rfl
  | _ :: rest =>
      add_nonneg (slopeProd_nonneg hslope rest) (suffixWeightSum_nonneg hslope rest)

theorem suffixWeightSum_pos {label : E → Label} (hslope : ∀ e : E, 0 < (label e).slope) :
    ∀ l : List E, l ≠ [] → 0 < suffixWeightSum label l
  | [], hne => absurd rfl hne
  | _ :: rest, _ => by
      have hprod := slopeProd_pos hslope rest
      have hrest := suffixWeightSum_nonneg (fun e => (hslope e).le) rest
      rw [suffixWeightSum_cons]
      linarith

theorem weightedDefect_nonneg {label : E → Label} (hslope : ∀ e : E, 0 ≤ (label e).slope)
    (φ : V → ℝ) : ∀ l : List E, 0 ≤ weightedDefect G label φ l
  | [] => le_rfl
  | e :: rest => by
      have hprod := slopeProd_nonneg hslope rest
      have hmax : 0 ≤ max 0 (defect G label φ e) := le_max_left _ _
      have hrest := weightedDefect_nonneg hslope φ rest
      rw [weightedDefect_cons]
      have := mul_nonneg hprod hmax
      linarith

/-- A uniform strict bound on the positive parts of the residuals caps the
weighted sum by that bound times the total suffix weight. -/
theorem weightedDefect_lt {label : E → Label} (hslope : ∀ e : E, 0 < (label e).slope)
    (φ : V → ℝ) {c : ℝ} : ∀ l : List E, l ≠ [] →
      (∀ e ∈ l, max 0 (defect G label φ e) < c) →
      weightedDefect G label φ l < c * suffixWeightSum label l
  | [], hne, _ => absurd rfl hne
  | [e], _, hbound => by
      have he := hbound e (List.mem_cons_self ..)
      simp only [weightedDefect_cons, weightedDefect_nil, suffixWeightSum_cons,
        suffixWeightSum_nil, slopeProd_nil]
      linarith
  | e :: a :: rest, _, hbound => by
      have he := hbound e (List.mem_cons_self ..)
      have hprod := slopeProd_pos hslope (a :: rest)
      have hrec := weightedDefect_lt hslope φ (a :: rest) (by simp)
        fun e' he' => hbound e' (List.mem_cons_of_mem _ he')
      rw [weightedDefect_cons, suffixWeightSum_cons]
      nlinarith [mul_lt_mul_of_pos_left he hprod]

/-! ### The weighted-defect telescope -/

/-- **The weighted-defect telescope.**  Transport of a candidate along a walk is
bounded by the candidate at the far end plus the positive parts of the edge
residuals, each weighted by the product of the slopes traversed after it.  The
inequalities of successive edges do not telescope additively; they telescope
with slope-product weights. -/
theorem holonomyApply_le_add_weightedDefect {label : E → Label}
    (hslope : ∀ e : E, 0 ≤ (label e).slope) (φ : V → ℝ) {start finish : V}
    (walk : G.Walk start finish) :
    holonomyApply label walk (φ start) ≤ φ finish + weightedDefect G label φ walk.edges := by
  induction walk with
  | nil => simp
  | @concat middle walkSoFar edge legal ih =>
      subst legal
      have hW : 0 ≤ weightedDefect G label φ walkSoFar.edges :=
        weightedDefect_nonneg hslope φ walkSoFar.edges
      have hmono := Label.monotone_apply (f := label edge) (hslope edge) ih
      have hlip := Label.apply_add_le (f := label edge) (hslope edge)
        (φ (G.source edge)) hW
      have hdefect : (label edge).apply (φ (G.source edge))
          = defect G label φ edge + φ (G.target edge) := by
        rw [defect]
        ring
      have hmax := le_max_right 0 (defect G label φ edge)
      rw [holonomyApply_concat, EdgeGraph.Walk.edges_concat, weightedDefect_append_singleton]
      linarith

/-- A lax section transports laxly: its value can only be undercut. -/
theorem holonomyApply_le_of_isLaxSection {label : E → Label}
    (hslope : ∀ e : E, 0 ≤ (label e).slope) {φ : V → ℝ}
    (hφ : IsLaxSection G label φ) {start finish : V} (walk : G.Walk start finish) :
    holonomyApply label walk (φ start) ≤ φ finish := by
  induction walk with
  | nil => simp
  | @concat middle walkSoFar edge legal ih =>
      subst legal
      have hmono := Label.monotone_apply (f := label edge) (hslope edge) ih
      exact hmono.trans (hφ edge)

/-- **Weak duality.**  A lax section makes its value at a vertex a
pre-fixed point of the composite action of every closed walk there. -/
theorem holonomyApply_cycle_le {label : E → Label} (hslope : ∀ e : E, 0 ≤ (label e).slope)
    {φ : V → ℝ} (hφ : IsLaxSection G label φ) {base : V} (cycle : G.Walk base base) :
    holonomyApply label cycle (φ base) ≤ φ base :=
  holonomyApply_le_of_isLaxSection hslope hφ cycle

/-- **The quantitative obstruction.**  A closed walk whose composite action
moves the candidate up by at least `γ > 0` forces one of its edges to fail the
section inequality by at least `γ` divided by the total suffix weight of the
walk.  At all slopes `1` the total suffix weight is the length of the walk, and
the statement becomes that of `Maths.MaxPlusPotential.exists_edge_defect_ge`. -/
theorem exists_edge_defect_ge {label : E → Label} (hslope : ∀ e : E, 0 < (label e).slope)
    (φ : V → ℝ) {base : V} (cycle : G.Walk base base) {γ : ℝ} (hγ : 0 < γ)
    (hcycle : φ base + γ ≤ holonomyApply label cycle (φ base)) :
    ∃ e ∈ cycle.edges, γ / suffixWeightSum label cycle.edges ≤ defect G label φ e := by
  have hne : cycle.edges ≠ [] := by
    intro hnil
    rw [holonomyApply_eq_foldl, hnil, List.foldl_nil] at hcycle
    linarith
  have hsum : 0 < suffixWeightSum label cycle.edges := suffixWeightSum_pos hslope _ hne
  by_contra hcon
  have hstrict (e : E) (he : e ∈ cycle.edges) :
      max 0 (defect G label φ e) < γ / suffixWeightSum label cycle.edges := by
    refine max_lt (div_pos hγ hsum) ?_
    by_contra hle
    exact hcon ⟨e, he, not_lt.mp hle⟩
  have hlt := weightedDefect_lt (G := G) hslope φ cycle.edges hne hstrict
  rw [div_mul_cancel₀ _ hsum.ne'] at hlt
  have htel := holonomyApply_le_add_weightedDefect (G := G) (fun e => (hslope e).le) φ cycle
  linarith

end Graph

/-! ## Cyclic max-affine systems -/
section Cyclic

/-- One phase of a cyclic max-affine system as a label: the equation
`C k = max (1 - p k) (q k * C (k + 1) + p k)` of
`CyclicMaxAffine.CyclicSolution` is the action of this label on
`C (k + 1)`. -/
def cyclicLabel (p q : ℕ → ℝ) (k : ℕ) : Label :=
  ⟨((1 - p k : ℝ) : WithBot ℝ), p k, q k⟩

@[simp] theorem apply_cyclicLabel (p q : ℕ → ℝ) (k : ℕ) (x : ℝ) :
    (cyclicLabel p q k).apply x = max (1 - p k) (p k + q k * x) :=
  Label.apply_of_floor_coe rfl x

/-- The backward chain of the cyclic labels: `cyclicChain p q L x d` is the
value `d` phases before the end of the unrolled cycle, started from `x`. -/
def cyclicChain (p q : ℕ → ℝ) (L : ℕ) (x : ℝ) : ℕ → ℝ
  | 0 => x
  | d + 1 => (cyclicLabel p q (L - (d + 1))).apply (cyclicChain p q L x d)

@[simp] theorem cyclicChain_zero (p q : ℕ → ℝ) (L : ℕ) (x : ℝ) :
    cyclicChain p q L x 0 = x := rfl

theorem cyclicChain_succ (p q : ℕ → ℝ) (L : ℕ) (x : ℝ) (d : ℕ) :
    cyclicChain p q L x (d + 1)
      = (cyclicLabel p q (L - (d + 1))).apply (cyclicChain p q L x d) := rfl

/-- The composite action of one full turn of the cycle. -/
def cyclicHolonomy (p q : ℕ → ℝ) (L : ℕ) (x : ℝ) : ℝ := cyclicChain p q L x L

/-- One turn of the cycle composes the phase labels in decreasing index order:
the last phase acts first. -/
theorem cyclicChain_eq_foldl (p q : ℕ → ℝ) (L : ℕ) (x : ℝ) : ∀ d : ℕ,
    cyclicChain p q L x d
      = ((List.range d).map fun j => cyclicLabel p q (L - 1 - j)).foldl
          (fun y f => f.apply y) x
  | 0 => rfl
  | d + 1 => by
      rw [cyclicChain_succ, cyclicChain_eq_foldl p q L x d, List.range_succ, List.map_append,
        List.foldl_append]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      congr 2
      omega

/-- **The periodic certificate.**  A fixed point of one turn of the cyclic
labels is the terminal value of a solution of the corresponding cyclic
max-affine system, whose survival-weighted bounds are
`CyclicMaxAffine.CyclicSolution.weightedRate_bounds`. -/
theorem cyclicSolution_cyclicChain {p q : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k)
    (hq0 : ∀ k, 0 ≤ q k)
    (hq1 : ∀ k, q k ≤ 1) {L : ℕ} {x : ℝ} (hx : cyclicHolonomy p q L x = x) :
    CyclicMaxAffine.CyclicSolution p q (fun k => cyclicChain p q L x (L - k)) L where
  rate_nonneg := hp
  survival_nonneg := hq0
  survival_le_one := hq1
  eq_max k hk := by
    have hsplit : L - k = (L - (k + 1)) + 1 := by omega
    have hindex : L - (L - (k + 1) + 1) = k := by omega
    change cyclicChain p q L x (L - k)
      = max (1 - p k) (q k * cyclicChain p q L x (L - (k + 1)) + p k)
    rw [hsplit, cyclicChain_succ, hindex, apply_cyclicLabel, add_comm (p k)]
  wrap := by
    show cyclicChain p q L x (L - L) = cyclicChain p q L x (L - 0)
    rw [Nat.sub_self, Nat.sub_zero, cyclicChain_zero]
    exact hx.symm

end Cyclic

/-! ## Specializations -/
section Specialization

universe uV uE

variable {V : Type uV} {E : Type uE} {G : Maths.EdgeGraph V E}

/-- The floorless translation label of a real edge weight. -/
def translationLabel (w : ℝ) : Label := ⟨⊥, w, 1⟩

@[simp] theorem slope_translationLabel (w : ℝ) : (translationLabel w).slope = 1 := rfl

@[simp] theorem apply_translationLabel (w x : ℝ) : (translationLabel w).apply x = w + x := by
  rw [Label.apply_of_floor_bot rfl]
  simp [Label.affinePart, translationLabel]

/-- The reflected (Lindley) label `x ↦ max 0 (a * x - g)`. -/
def reflectedLabel (a g : ℝ) : Label :=
  Label.ofMaxAffine (TransferSummary.reflectedSummary a g)

@[simp] theorem apply_reflectedLabel (a g x : ℝ) :
    (reflectedLabel a g).apply x = max 0 (a * x - g) := by
  rw [reflectedLabel, Label.apply_ofMaxAffine, TransferSummary.apply_reflectedSummary]

theorem foldl_reflectedLabel (a g : ℕ → ℝ) (x : ℝ) : ∀ n : ℕ,
    ((List.range n).map fun i => reflectedLabel (a i) (g i)).foldl (fun y f => f.apply y) x
      = TransferSummary.reflectedIter a g x n
  | 0 => rfl
  | n + 1 => by
      rw [List.range_succ, List.map_append, List.foldl_append, foldl_reflectedLabel a g x n]
      simp [TransferSummary.reflectedIter]

/-- **Reflected labels recover the Lindley recursion.**  Transport along a path
whose edges carry the reflected labels of the sequences `a` and `g`, in order,
is the reflected orbit `TransferSummary.reflectedIter`. -/
theorem holonomyApply_eq_reflectedIter {label : E → Label} (a g : ℕ → ℝ) {n : ℕ}
    {start finish : V} (walk : G.Walk start finish)
    (hmatch : walk.edges.map label = (List.range n).map fun i => reflectedLabel (a i) (g i))
    (x : ℝ) : holonomyApply label walk x = TransferSummary.reflectedIter a g x n := by
  rw [holonomyApply_eq_foldl_map, hmatch, foldl_reflectedLabel]

/-- Transport along a closed walk whose labels are the phases of a cyclic
max-affine system, in decreasing phase order, is one turn of that system. -/
theorem holonomyApply_eq_cyclicHolonomy {label : E → Label} (p q : ℕ → ℝ) {L : ℕ}
    {start finish : V} (walk : G.Walk start finish)
    (hmatch : walk.edges.map label = (List.range L).map fun j => cyclicLabel p q (L - 1 - j))
    (x : ℝ) : holonomyApply label walk x = cyclicHolonomy p q L x := by
  rw [holonomyApply_eq_foldl_map, hmatch, cyclicHolonomy, cyclicChain_eq_foldl]

/-- **The periodic certificate on a closed walk.**  A closed walk labelled by
the phases of a cyclic max-affine system, in decreasing phase order, whose
composite action fixes a point, exhibits that point as the terminal value of a
solution of the system. -/
theorem cyclicSolution_of_holonomyApply_eq {label : E → Label} {p q : ℕ → ℝ}
    (hp : ∀ k, 0 ≤ p k) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1) {L : ℕ} {base : V}
    (cycle : G.Walk base base)
    (hmatch : cycle.edges.map label = (List.range L).map fun j => cyclicLabel p q (L - 1 - j))
    {x : ℝ} (hx : holonomyApply label cycle x = x) :
    CyclicMaxAffine.CyclicSolution p q (fun k => cyclicChain p q L x (L - k)) L :=
  cyclicSolution_cyclicChain hp hq0 hq1
    (by rw [← holonomyApply_eq_cyclicHolonomy p q cycle hmatch]; exact hx)

end Specialization

/-! ## The transport interpretation
`Maths` develops transport with vertex-indexed fibers; a
max-affine transport graph is its constant-fiber case, with every fiber the line
and each edge acting by its label.  The identifications below let the

section and holonomy statements of that module specialize here. -/
section Transport

open Maths

universe uV' uE'

variable {V : Type uV'} {E : Type uE'} {G : Maths.EdgeGraph V E}

/-- The constant-fiber transport of a labelled graph: every fiber is
the line and each edge acts by its label. -/
def toTransport (G : EdgeGraph V E) (label : E → Label) :
    Transport G fun _ : V => ℝ :=
  ofEdgeAct G ℝ fun e => (label e).apply

/-- Walk transport of the constant-fiber reading is the composite label
action. -/
theorem walkMap_toTransport (label : E → Label) {start finish : V}
    (walk : G.Walk start finish) (x : ℝ) :
    (toTransport G label).walkMap walk x = holonomyApply label walk x :=
  walkMap_ofEdgeAct _ walk x

/-- A lax section of a labelled graph is a lax section of its constant-fiber
transport. -/
theorem isLaxSection_iff_toTransport_isLaxSection (G : EdgeGraph V E) (label : E → Label)
    (φ : V → ℝ) :
    IsLaxSection G label φ ↔ (toTransport G label).IsLaxSection φ :=
  Iff.rfl

end Transport

end Maths.MaxAffineTransport
