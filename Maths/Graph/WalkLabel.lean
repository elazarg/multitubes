/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Graph.EdgeGraph
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Order.Monoid.Defs

import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Monoid labels of walks

An edge labelling `label : E → M` into a monoid extends to every walk.  Two orders of
multiplication are natural.

* `Maths.walkLabel` multiplies the last edge outermost, so that a walk label acts on the
  left in the same order as the walk is traversed: `walkLabel label (p.append q) =
  walkLabel label q * walkLabel label p`.  This is the label of a gain or voltage graph and
  the composite of a chain of left actions.
* `Maths.walkProd` multiplies in chronological order, and its additive form
  `Maths.walkSum` is the sum of edge data along a walk: its tension, line integral, or
  cycle sum.

The two agree in a commutative monoid (`Maths.walkLabel_eq_walkProd`).  A labelling is
*flat*, or *balanced*, when every closed walk has trivial label.

## Main definitions

* `Maths.walkLabel` - the composite label of a walk in action order.
* `Maths.HasTrivialCycleLabels` - every closed walk has identity label.
* `Maths.walkProd` and `Maths.walkSum` - the chronological product and sum of edge data
  along a walk.

## Main results

* `Maths.walkLabel_append` - walk labels are anti-multiplicative under concatenation.
* `Maths.walkProd_append` and `Maths.walkSum_append` - chronological products and sums are
  multiplicative and additive under concatenation.
* `Maths.walkLabel_eq_walkProd` - the two orders agree in a commutative monoid.
* `Maths.countP_nsmul_le_walkSum` - a lower bound per marked traversal bounds the walk sum of
  nonnegative data.

## Tags

walk label, gain graph, voltage graph, balance, walk sum, tension, cycle sum
-/

@[expose] public section

namespace Maths

universe uV uE uM

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E} {start finish middle : V}

/-! ### Labels in action order -/

section Label

variable {M : Type uM} [Monoid M]

/-- Composite label of a walk, with the last edge outermost so that the label acts in the
order in which the walk is traversed. -/
def walkLabel (label : E → M) {start : V} :
    {finish : V} → G.Walk start finish → M
  | _, .nil => 1
  | _, .concat walkSoFar edge _ => label edge * walkLabel label walkSoFar

variable {label : E → M}

@[simp] theorem walkLabel_nil : walkLabel label (.nil : G.Walk start start) = 1 := rfl

@[simp] theorem walkLabel_concat (walk : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    walkLabel label (walk.concat edge legal) = label edge * walkLabel label walk := rfl

@[simp] theorem walkLabel_singleton (edge : E) :
    walkLabel label (EdgeGraph.Walk.singleton (G := G) edge) = label edge :=
  mul_one _

/-- Concatenating walks multiplies labels in action order. -/
@[simp] theorem walkLabel_append (first : G.Walk start middle)
    (second : G.Walk middle finish) :
    walkLabel label (first.append second) = walkLabel label second * walkLabel label first := by
  induction second with
  | nil => simp
  | concat walkSoFar edge legal ih =>
      rw [EdgeGraph.Walk.append_concat, walkLabel_concat, walkLabel_concat, ih, mul_assoc]

@[simp] theorem walkLabel_castFinish {finish' : V} (walk : G.Walk start finish)
    (hfinish : finish = finish') :
    walkLabel label (walk.castFinish hfinish) = walkLabel label walk := by
  subst hfinish
  rfl

@[simp] theorem walkLabel_castStart {start' : V} (walk : G.Walk start finish)
    (hstart : start = start') :
    walkLabel label (walk.castStart hstart) = walkLabel label walk := by
  subst hstart
  rfl

/-- Every closed walk has identity composite label.  For group-labelled gain graphs this is
balance; for a transport it is flatness. -/
def HasTrivialCycleLabels (G : EdgeGraph V E) (label : E → M) : Prop :=
  ∀ (vertex : V) (cycle : G.Walk vertex vertex), walkLabel label cycle = 1

end Label

/-! ### Chronological products and sums -/

section Product

variable {M : Type uM} [Monoid M]

/-- Product of edge data along a walk, in chronological order. -/
@[to_additive /-- Sum of edge data along a walk, in chronological order.  Also called the
walk's tension, its line integral, or its cycle sum when the walk is closed. -/]
def walkProd (w : E → M) {start finish : V} (walk : G.Walk start finish) : M :=
  (walk.edges.map w).prod

variable {w : E → M}

@[to_additive (attr := simp)]
theorem walkProd_nil : walkProd w (.nil : G.Walk start start) = 1 := rfl

@[to_additive (attr := simp)]
theorem walkProd_concat (walk : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    walkProd w (walk.concat edge legal) = walkProd w walk * w edge := by
  simp [walkProd]

@[to_additive (attr := simp)]
theorem walkProd_append (first : G.Walk start middle) (second : G.Walk middle finish) :
    walkProd w (first.append second) = walkProd w first * walkProd w second := by
  simp [walkProd]

@[to_additive (attr := simp)]
theorem walkProd_singleton (edge : E) :
    walkProd w (EdgeGraph.Walk.singleton (G := G) edge) = w edge := by
  simp [walkProd]

@[to_additive (attr := simp)]
theorem walkProd_castFinish {finish' : V} (walk : G.Walk start finish)
    (hfinish : finish = finish') :
    walkProd w (walk.castFinish hfinish) = walkProd w walk := by
  simp [walkProd]

@[to_additive (attr := simp)]
theorem walkProd_castStart {start' : V} (walk : G.Walk start finish)
    (hstart : start = start') :
    walkProd w (walk.castStart hstart) = walkProd w walk := by
  simp [walkProd]

/-- Traversing a closed walk `n` times raises its product to the `n`-th power. -/
@[to_additive (attr := simp) /-- Traversing a closed walk `n` times multiplies its sum by
`n`. -/]
theorem walkProd_iterate {base : V} (cycle : G.Walk base base) (n : ℕ) :
    walkProd w (cycle.iterate n) = walkProd w cycle ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [EdgeGraph.Walk.iterate_succ, walkProd_append, ih, pow_succ]

@[to_additive (attr := simp)]
theorem walkProd_one (walk : G.Walk start finish) : walkProd (fun _ => (1 : M)) walk = 1 := by
  simp [walkProd]

end Product

section CommMonoid

variable {M : Type uM} [CommMonoid M]

/-- In a commutative monoid the action-order label is the chronological product. -/
theorem walkLabel_eq_walkProd (label : E → M) (walk : G.Walk start finish) :
    walkLabel label walk = walkProd label walk := by
  induction walk with
  | nil => rfl
  | concat walkSoFar edge legal ih => rw [walkLabel_concat, walkProd_concat, ih, mul_comm]

/-- Chronological products of a pointwise product multiply. -/
@[to_additive /-- Walk sums of a pointwise sum add. -/]
theorem walkProd_mul (w₁ w₂ : E → M) (walk : G.Walk start finish) :
    walkProd (fun edge => w₁ edge * w₂ edge) walk = walkProd w₁ walk * walkProd w₂ walk := by
  simp [walkProd, List.prod_map_mul]

end CommMonoid

section CommGroup

variable {M : Type uM} [CommGroup M]

/-- Chronological products of a pointwise quotient divide. -/
@[to_additive /-- Walk sums of a pointwise difference subtract. -/]
theorem walkProd_div (w₁ w₂ : E → M) (walk : G.Walk start finish) :
    walkProd (fun edge => w₁ edge / w₂ edge) walk = walkProd w₁ walk / walkProd w₂ walk := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih => rw [walkProd_concat, walkProd_concat, walkProd_concat, ih,
      div_mul_div_comm]

/-- Chronological products of pointwise inverses invert. -/
@[to_additive (attr := simp) /-- Walk sums of a pointwise negation negate. -/]
theorem walkProd_inv (w : E → M) (walk : G.Walk start finish) :
    walkProd (fun edge => (w edge)⁻¹) walk = (walkProd w walk)⁻¹ := by
  simpa using walkProd_div (fun _ => 1) w walk

/-- Dividing every edge datum by a constant divides the chronological product by that
constant to the power of the length. -/
@[to_additive /-- Shifting every edge datum by a constant shifts the walk sum by that constant
times the length. -/]
theorem walkProd_div_const (w : E → M) (c : M) (walk : G.Walk start finish) :
    walkProd (fun edge => w edge / c) walk = walkProd w walk / c ^ walk.length := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih =>
      rw [walkProd_concat, walkProd_concat, ih, EdgeGraph.Walk.length_concat, pow_succ,
        div_mul_div_comm]

end CommGroup

section Ordered

variable {A : Type*} [AddCommMonoid A] [PartialOrder A] [IsOrderedAddMonoid A]

/-- If every edge with property `P` carries at least `threshold` and every edge carries a
nonnegative datum, then `threshold` times the number of traversals of `P`-edges is at most the
walk sum.  A repeated edge is counted once per traversal. -/
theorem countP_nsmul_le_walkSum (w : E → A) (hw : ∀ edge, 0 ≤ w edge) (P : E → Prop)
    [DecidablePred P] (threshold : A) (hthreshold : ∀ edge, P edge → threshold ≤ w edge)
    (walk : G.Walk start finish) :
    walk.edges.countP (fun edge => P edge) • threshold ≤ walkSum w walk := by
  induction walk with
  | nil => simp
  | concat walkSoFar edge legal ih =>
      rw [EdgeGraph.Walk.edges_concat, List.countP_append, walkSum_concat, add_nsmul]
      by_cases hedge : P edge
      · simpa [hedge, one_nsmul] using add_le_add ih (hthreshold edge hedge)
      · simpa [hedge] using add_le_add ih (hw edge)

end Ordered

end Maths
