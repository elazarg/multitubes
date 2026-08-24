/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DirectedTransport.MaxAffine.FixedPoint
public import Mathlib.Topology.MetricSpace.Contracting

import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# The vertex operator as a sup-norm contraction

`DirectedTransport.MaxAffine.FixedPoint` solves the eigenvalue equation `F x = lam + x` for the
vertex operator `F` in the topical regime, where every slope is one and every floor is absent.
This file solves it in a disjoint regime, by a metric rather than an order argument: when every
slope is bounded in absolute value by a constant below one, `F` is a contraction of `V → ℝ` in
the sup-norm, and Banach's theorem supplies a fixed point that is moreover unique.

The estimate that drives this is edgewise and needs no sign condition: a max-affine map is
Lipschitz with constant `|slope|`, because the affine branch is and because capping two
quantities at a common floor does not increase their distance
(`DirectedTransport.MaxAffineTransport.Label.abs_apply_sub_apply_le`).  Taking a supremum over
the incoming edges of a vertex does not increase the distance either, and the sup-norm on
`V → ℝ` then assembles the edgewise estimates into one Lipschitz constant.

Subtracting the constant `lam` is an isometry, so the same constant contracts `x ↦ F x - lam`
for every real `lam`.  Hence **every real number is an eigenvalue**, each with exactly one
eigenvector.  This is the sharpest possible contrast with the topical case, where the
eigenvalue is the maximum cycle mean and is uniquely determined while the eigenvector is
determined only up to an additive constant.  The mechanism is visible already for a single
vertex with one loop of slope `s`: the equation `t + s * x = lam + x` has the unique solution
`x = (t - lam) / (1 - s)` when `s ≠ 1`, and is either unsolvable or solved by every `x` when
`s = 1`.

The slopes here may be *mixed*, both in sign and in size, so long as they stay inside `(-1, 1)`;
what is excluded is a slope at or beyond unit modulus.  This is therefore not the topical
theorem and does not subsume it: the two regimes meet only at the empty edge set.  Nor does it
subsume `DirectedTransport.MaxAffineTransport.exists_const_isLaxSection_of_slope_lt_one`, which
admits arbitrarily negative slopes but concludes only the inequality `F x ≤ x`; here the
conclusion is equality and uniqueness, at the price of a two-sided slope bound and finitely
many vertices.

The last section records the one thing that is *false* outside the monotone regime.  Two
vertices joined by two edges of slope `-1`, whose shifts differ, form a strongly connected
graph on which the eigenvalue equation has no solution for any `lam`: the two tightness
equations are forced, being the only incoming edges, and they contradict each other.  So the
nonnegativity of the slopes is not a convenience in the eigenvector theory; it is load-bearing.

## Main definitions

* `DirectedTransport.MaxAffineTransport.flipGraph`,
  `DirectedTransport.MaxAffineTransport.flipLabel`: two vertices, two reflecting edges, and no
  eigenvector.

## Main results

* `DirectedTransport.MaxAffineTransport.Label.abs_apply_sub_apply_le`: a max-affine map is
  Lipschitz with constant the absolute value of its slope.
* `DirectedTransport.MaxAffineTransport.abs_vertexOperator_sub_le`: the vertex operator does not
  increase a uniform edgewise bound.
* `DirectedTransport.MaxAffineTransport.lipschitzWith_vertexOperator`: the vertex operator is
  Lipschitz in the sup-norm with the largest absolute slope as constant.
* `DirectedTransport.MaxAffineTransport.contractingWith_vertexOperator`: **below unit modulus
  the vertex operator is a contraction.**
* `DirectedTransport.MaxAffineTransport.existsUnique_isEigenvector_of_abs_slope_lt_one`: **below
  unit modulus every real number is an eigenvalue, with exactly one eigenvector.**
* `DirectedTransport.MaxAffineTransport.existsUnique_fixedPoint_of_abs_slope_lt_one`: the case
  `lam = 0`, a unique genuine section.
* `DirectedTransport.MaxAffineTransport.vertexOperator_add_const_of_slope_eq`: homogeneity of
  degree the common slope, for a floorless labelling of one slope.
* `DirectedTransport.MaxAffineTransport.isEigenvector_add_const_of_slope_eq`: **outside unit
  slope the eigenvalue is not an invariant**, translating an eigenvector moves it.
* `DirectedTransport.MaxAffineTransport.not_exists_isEigenvector_flipLabel` and
  `DirectedTransport.MaxAffineTransport.not_forall_exists_isEigenvector`: **the eigenvalue
  equation can fail on a finite strongly connected graph once a slope is negative.**

## Implementation notes

The Lipschitz constant is taken in `ℝ≥0`, as `DirectedTransport.MaxAffineTransport` has no
preferred bound available; the hypothesis is `|slope e| ≤ K` for a single `K`, which finitely
many edges always admit.

The contraction argument is indifferent to whether a vertex has an incoming edge, because the
junk value `0` of `DirectedTransport.MaxAffineTransport.vertexOperator` is constant in the
argument and therefore Lipschitz with any constant.  No nonemptiness hypothesis appears.

## TODO

The regime of nonnegative slopes straddling one is untouched.  There the vertex operator is
monotone, but a slope above one makes it expansive, so the metric argument of this file fails,
and a slope below one destroys additive homogeneity, so the Perron--Frobenius argument of
`DirectedTransport.MaxAffine.FixedPoint` fails as well.  Neither obstruction already in the
library decides the question.  A labelling can fail to have a lax section and still have an
eigenvector, so the certificate of `DirectedTransport.MaxAffine.Farkas` does not obstruct one;
and `DirectedTransport.MaxAffineTransport.not_exists_isEigenvector_flipLabel` uses a negative
slope, so it is a failure of monotonicity rather than of homogeneity.  The sharpened question
is whether a finite strongly connected graph whose slopes are all nonnegative always carries an
eigenvector of its vertex operator.

Two reductions narrow that question.  A finite floor on an edge into a vertex contributes the
same demand as an extra floorless edge into that vertex of slope `0` and shift the floor, so
floors may be assumed absent.  And when every vertex has exactly one incoming edge no supremum
is taken at all and the equations are triangular along each cycle, so a counterexample needs a
vertex of in-degree at least two, where the supremum is genuine.

## References

* S. Gaubert and J. Gunawardena, *The Perron--Frobenius theorem for homogeneous, monotone
  functions*, Trans. Amer. Math. Soc. 356 (2004), 4931-4950.
* R. D. Nussbaum, *Hilbert's projective metric and iterated nonlinear maps*, Mem. Amer. Math.
  Soc. 75 (1988), no. 391.
* F. Baccelli, G. Cohen, G. J. Olsder and J.-P. Quadrat, *Synchronization and Linearity*, Wiley
  (1992).

## Tags

contraction, Banach fixed point, vertex operator, eigenvector, max-affine, sup-norm
-/

@[expose] public section

namespace DirectedTransport

noncomputable section

namespace MaxAffineTransport

universe uV uE

/-! ## The edgewise Lipschitz estimate -/

namespace Label

/-- **A max-affine map is Lipschitz with constant the absolute value of its slope.**  No sign
condition is needed: the affine branch scales distances by the slope, and joining both branches
with a common floor cannot increase the distance between them. -/
theorem abs_apply_sub_apply_le (f : Label) (x y : ℝ) :
    |f.apply x - f.apply y| ≤ |f.slope| * |x - y| := by
  have haff : f.affinePart x - f.affinePart y = f.slope * (x - y) := by
    simp only [affinePart]; ring
  rcases f.floor_cases with hfloor | ⟨e, hfloor⟩
  · rw [apply_of_floor_bot hfloor, apply_of_floor_bot hfloor, haff, abs_mul]
  · rw [apply_of_floor_coe hfloor, apply_of_floor_coe hfloor, max_comm e, max_comm e]
    calc |max (f.affinePart x) e - max (f.affinePart y) e|
        ≤ |f.affinePart x - f.affinePart y| := abs_max_sub_max_le_abs _ _ _
      _ = |f.slope| * |x - y| := by rw [haff, abs_mul]

end Label

/-! ## The vertex operator is Lipschitz -/

section Lipschitz

variable {V : Type uV} {E : Type uE} [Fintype E] [DecidableEq V]
variable {G : EdgeGraph V E} {label : E → Label} {x y : V → ℝ}

/-- **A uniform edgewise bound passes to the vertex operator.**  A supremum of finitely many
quantities moves by at most the largest movement of the quantities, and at a vertex with no
incoming edge both values are the junk value `0`. -/
theorem abs_vertexOperator_sub_le {bound : ℝ} (hbound : 0 ≤ bound)
    (hedge : ∀ e : E,
      |(label e).apply (x (G.source e)) - (label e).apply (y (G.source e))| ≤ bound)
    (vertex : V) :
    |vertexOperator G label x vertex - vertexOperator G label y vertex| ≤ bound := by
  rcases (incoming G vertex).eq_empty_or_nonempty with hempty | hne
  · rw [vertexOperator_of_incoming_eq_empty hempty, vertexOperator_of_incoming_eq_empty hempty]
    simpa using hbound
  · rw [vertexOperator_eq_sup' hne, vertexOperator_eq_sup' hne, abs_sub_le_iff]
    constructor
    · refine sub_le_iff_le_add.2 (Finset.sup'_le _ _ fun e he => ?_)
      have hstep := (abs_sub_le_iff.1 (hedge e)).1
      have hle := Finset.le_sup' (fun e => (label e).apply (y (G.source e))) he
      linarith
    · refine sub_le_iff_le_add.2 (Finset.sup'_le _ _ fun e he => ?_)
      have hstep := (abs_sub_le_iff.1 (hedge e)).2
      have hle := Finset.le_sup' (fun e => (label e).apply (x (G.source e))) he
      linarith

variable [Fintype V]

/-- The vertex operator moves each coordinate by at most the largest absolute slope times the
sup-distance of its arguments. -/
theorem abs_vertexOperator_sub_le_dist {K : NNReal} (hslope : ∀ e : E, |(label e).slope| ≤ K)
    (x y : V → ℝ) (vertex : V) :
    |vertexOperator G label x vertex - vertexOperator G label y vertex| ≤ K * dist x y := by
  refine abs_vertexOperator_sub_le (mul_nonneg K.coe_nonneg dist_nonneg) (fun e => ?_) vertex
  refine (Label.abs_apply_sub_apply_le (label e) _ _).trans ?_
  have hcoord : |x (G.source e) - y (G.source e)| ≤ dist x y := by
    rw [← Real.dist_eq]; exact dist_le_pi_dist x y (G.source e)
  exact mul_le_mul (hslope e) hcoord (abs_nonneg _) K.coe_nonneg

/-- **The vertex operator is Lipschitz in the sup-norm**, with any common bound on the absolute
values of the slopes as constant. -/
theorem lipschitzWith_vertexOperator (G : EdgeGraph V E) (label : E → Label) {K : NNReal}
    (hslope : ∀ e : E, |(label e).slope| ≤ K) :
    LipschitzWith K (vertexOperator G label) :=
  LipschitzWith.of_dist_le_mul fun x y =>
    (dist_pi_le_iff (mul_nonneg K.coe_nonneg dist_nonneg)).2 fun vertex => by
      rw [Real.dist_eq]
      exact abs_vertexOperator_sub_le_dist hslope x y vertex

/-- The vertex operator followed by subtraction of a constant is Lipschitz with the same
constant, subtraction of a constant being an isometry of `V → ℝ`. -/
theorem lipschitzWith_vertexOperator_sub (G : EdgeGraph V E) (label : E → Label) {K : NNReal}
    (hslope : ∀ e : E, |(label e).slope| ≤ K) (lam : ℝ) :
    LipschitzWith K fun x vertex => vertexOperator G label x vertex - lam :=
  LipschitzWith.of_dist_le_mul fun x y =>
    (dist_pi_le_iff (mul_nonneg K.coe_nonneg dist_nonneg)).2 fun vertex => by
      rw [Real.dist_eq]
      have hcancel : vertexOperator G label x vertex - lam - (vertexOperator G label y vertex
          - lam) = vertexOperator G label x vertex - vertexOperator G label y vertex := by ring
      rw [hcancel]
      exact abs_vertexOperator_sub_le_dist hslope x y vertex

/-- **Below unit modulus the vertex operator is a contraction** of `V → ℝ` in the sup-norm. -/
theorem contractingWith_vertexOperator (G : EdgeGraph V E) (label : E → Label) {K : NNReal}
    (hK : K < 1) (hslope : ∀ e : E, |(label e).slope| ≤ K) :
    ContractingWith K (vertexOperator G label) :=
  ⟨hK, lipschitzWith_vertexOperator G label hslope⟩

end Lipschitz

/-! ## Existence and uniqueness of eigenvectors below unit modulus -/

section Banach

variable {V : Type uV} {E : Type uE} [Fintype E] [DecidableEq V] [Fintype V]

/-- **Below unit modulus every real number is an eigenvalue of the vertex operator, with exactly
one eigenvector.**  The slopes may be mixed in sign and in size inside `(-1, 1)`; what is asked
is one bound `K < 1` on all their absolute values, which finitely many edges always admit.

The contrast with the topical case is complete.  There the eigenvalue is forced to be the
maximum cycle mean and the eigenvector is free up to an additive constant; here the eigenvalue
is free and the eigenvector is forced. -/
theorem existsUnique_isEigenvector_of_abs_slope_lt_one (G : EdgeGraph V E) (label : E → Label)
    {K : NNReal} (hK : K < 1) (hslope : ∀ e : E, |(label e).slope| ≤ K) (lam : ℝ) :
    ∃! x : V → ℝ, IsEigenvector G label lam x := by
  have hcontract : ContractingWith K fun x vertex => vertexOperator G label x vertex - lam :=
    ⟨hK, lipschitzWith_vertexOperator_sub G label hslope lam⟩
  have hiff (x : V → ℝ) :
      IsEigenvector G label lam x ↔
        Function.IsFixedPt (fun x vertex => vertexOperator G label x vertex - lam) x := by
    constructor
    · intro hx
      funext vertex
      simp only [hx vertex]
      ring
    · intro hx vertex
      have := congrFun hx vertex
      simp only at this
      linarith
  refine ⟨_, (hiff _).2 hcontract.fixedPoint_isFixedPt, fun y hy => ?_⟩
  exact hcontract.fixedPoint_unique ((hiff y).1 hy)

/-- **A unique genuine section below unit modulus.**  At `lam = 0` the eigenvalue equation is
`F x = x`, so the unique solution is at once a lax section and tight at every vertex, by
`DirectedTransport.MaxAffineTransport.isLaxSection_iff_vertexOperator_le`. -/
theorem existsUnique_fixedPoint_of_abs_slope_lt_one (G : EdgeGraph V E) (label : E → Label)
    {K : NNReal} (hK : K < 1) (hslope : ∀ e : E, |(label e).slope| ≤ K) :
    ∃! x : V → ℝ, ∀ vertex : V, vertexOperator G label x vertex = x vertex := by
  simpa only [IsEigenvector, zero_add] using
    existsUnique_isEigenvector_of_abs_slope_lt_one G label hK hslope 0

end Banach

/-! ## The eigenvalue is an invariant only at unit slope -/

section Uniform

variable {V : Type uV} {E : Type uE} [Fintype E] [DecidableEq V]

/-- **Homogeneity of degree the common slope.**  When every label is floorless and every slope
equals `s`, raising the argument by a constant `c` raises the vertex operator by `s * c`.  No
sign condition on `s` is needed: `s * c` is added to every incoming demand at once, so it passes
through the supremum.  At `s = 1` this is
`DirectedTransport.MaxAffineTransport.vertexOperator_add_const`. -/
theorem vertexOperator_add_const_of_slope_eq (G : EdgeGraph V E) {label : E → Label} {s : ℝ}
    (hslope : ∀ e : E, (label e).slope = s) (hfloor : ∀ e : E, (label e).floor = ⊥)
    (x : V → ℝ) (c : ℝ) {vertex : V} (hne : (incoming G vertex).Nonempty) :
    vertexOperator G label (fun v => x v + c) vertex
      = vertexOperator G label x vertex + s * c := by
  have hvalue (e : E) (z : ℝ) : (label e).apply z = (label e).shift + s * z := by
    rw [Label.apply_of_floor_bot (hfloor e), Label.affinePart, hslope e]
  rw [vertexOperator_eq_sup' hne, vertexOperator_eq_sup' hne]
  refine le_antisymm (Finset.sup'_le _ _ fun e he => ?_)
    (le_sub_iff_add_le.1 (Finset.sup'_le _ _ fun e he => ?_))
  · have hle := Finset.le_sup' (fun e => (label e).apply (x (G.source e))) he
    have hexp : s * (x (G.source e) + c) = s * x (G.source e) + s * c := by ring
    rw [hvalue e] at hle ⊢
    rw [hexp]
    linarith
  · have hle := Finset.le_sup' (fun e => (label e).apply (x (G.source e) + c)) he
    have hexp : s * (x (G.source e) + c) = s * x (G.source e) + s * c := by ring
    rw [hvalue e] at hle ⊢
    rw [hexp] at hle
    linarith

/-- **Outside unit slope the eigenvalue is not an invariant.**  For a floorless labelling of
common slope `s`, translating an eigenvector by `c` produces an eigenvector again, with the
eigenvalue moved by `-(1 - s) * c`.  At `s = 1` the movement vanishes and one recovers the
topical picture, where the eigenvalue is pinned to the maximum cycle mean and the eigenvector
is free up to a constant; at any other `s` the roles are exchanged and the set of eigenvalues
is either empty or all of `ℝ`. -/
theorem isEigenvector_add_const_of_slope_eq (G : EdgeGraph V E) {label : E → Label} {s : ℝ}
    (hslope : ∀ e : E, (label e).slope = s) (hfloor : ∀ e : E, (label e).floor = ⊥)
    (hin : ∀ vertex : V, (incoming G vertex).Nonempty) {lam : ℝ} {x : V → ℝ}
    (hx : IsEigenvector G label lam x) (c : ℝ) :
    IsEigenvector G label (lam - (1 - s) * c) fun v => x v + c := by
  intro vertex
  rw [vertexOperator_add_const_of_slope_eq G hslope hfloor x c (hin vertex), hx vertex]
  ring

end Uniform

/-! ## A strongly connected graph with no eigenvector -/

section Reflection

/-- Two vertices and two edges, each edge running from one vertex to the other.  The vertex
type and the edge type are both `Bool`, the edge `e` running from `e` to `!e`. -/
def flipGraph : EdgeGraph Bool Bool where
  source := fun e => e
  target := fun e => !e

/-- The two reflecting labels of `DirectedTransport.MaxAffineTransport.flipGraph`: both have
slope `-1`, and their shifts differ.  The edge `false` acts by `x ↦ -x` and the edge `true` by
`x ↦ 1 - x`. -/
def flipLabel : Bool → Label
  | false => ⟨⊥, 0, -1⟩
  | true => ⟨⊥, 1, -1⟩

@[simp] theorem apply_flipLabel_false (x : ℝ) : (flipLabel false).apply x = -x := by
  simp [flipLabel]

@[simp] theorem apply_flipLabel_true (x : ℝ) : (flipLabel true).apply x = 1 + -x := by
  simp [flipLabel]

/-- Each vertex of `DirectedTransport.MaxAffineTransport.flipGraph` has exactly one incoming
edge, namely the edge named by the other vertex. -/
theorem incoming_flipGraph (vertex : Bool) : incoming flipGraph vertex = {!vertex} := by
  ext e
  cases e <;> cases vertex <;> simp [mem_incoming, flipGraph]

/-- With a single incoming edge the vertex operator is that edge's demand, with no supremum
left to take. -/
theorem vertexOperator_flipLabel (x : Bool → ℝ) (vertex : Bool) :
    vertexOperator flipGraph flipLabel x vertex = (flipLabel (!vertex)).apply (x (!vertex)) := by
  have hne : (incoming flipGraph vertex).Nonempty := by
    rw [incoming_flipGraph]; exact ⟨!vertex, Finset.mem_singleton_self _⟩
  have hmem (e : Bool) (he : e ∈ incoming flipGraph vertex) : e = !vertex := by
    rw [incoming_flipGraph] at he
    exact Finset.mem_singleton.1 he
  rw [vertexOperator_eq_sup' hne]
  refine le_antisymm (Finset.sup'_le _ _ fun e he => le_of_eq ?_) (Finset.le_sup'
    (fun e => (flipLabel e).apply (x (flipGraph.source e))) ?_)
  · rw [hmem e he]
    rfl
  · rw [incoming_flipGraph]
    exact Finset.mem_singleton_self _

/-- **No eigenvector, for any eigenvalue.**  Each vertex has a single incoming edge, so both
tightness equations are forced: `-x false = lam + x true` and `1 - x true = lam + x false`.
Substituting the first into the second cancels `x false` and `lam` together and leaves
`1 = 0`.  The cancellation is exactly the degeneracy of a closed walk whose slopes multiply to
one while the alternating sum of the surviving slope products vanishes, which the nonnegative
slopes of the monotone theory cannot produce. -/
theorem not_exists_isEigenvector_flipLabel :
    ¬∃ (lam : ℝ) (x : Bool → ℝ), IsEigenvector flipGraph flipLabel lam x := by
  rintro ⟨lam, x, hx⟩
  have htrue := hx true
  have hfalse := hx false
  rw [vertexOperator_flipLabel] at htrue hfalse
  simp only [Bool.not_true, apply_flipLabel_false] at htrue
  simp only [Bool.not_false, apply_flipLabel_true] at hfalse
  linarith

/-- Every vertex of `DirectedTransport.MaxAffineTransport.flipGraph` has an incoming edge. -/
theorem exists_target_flipGraph (vertex : Bool) : ∃ e : Bool, flipGraph.target e = vertex :=
  ⟨!vertex, by cases vertex <;> rfl⟩

/-- `DirectedTransport.MaxAffineTransport.flipGraph` is strongly connected: one edge joins the
two vertices in either direction, and a vertex returns to itself in two steps. -/
theorem nonempty_walk_flipGraph (start finish : Bool) :
    Nonempty (flipGraph.Walk start finish) := by
  cases start <;> cases finish
  · exact ⟨.concat (.concat .nil false rfl) true rfl⟩
  · exact ⟨.concat .nil false rfl⟩
  · exact ⟨.concat .nil true rfl⟩
  · exact ⟨.concat (.concat .nil true rfl) false rfl⟩

/-- **The eigenvalue equation is not solvable in general once a slope is negative**, even on a
finite strongly connected graph in which every vertex has an incoming edge.  These are exactly
the graph-level hypotheses of
`DirectedTransport.MaxAffineTransport.exists_isEigenvector_of_translation`, so what that theorem
draws from its slope hypothesis cannot be recovered from the graph alone. -/
theorem not_forall_exists_isEigenvector :
    ¬∀ (V E : Type) (_ : Fintype V) (_ : DecidableEq V) (_ : Fintype E) (G : EdgeGraph V E)
        (label : E → Label),
      (∀ vertex : V, ∃ e : E, G.target e = vertex) →
      (∀ start finish : V, Nonempty (G.Walk start finish)) →
      ∃ (lam : ℝ) (x : V → ℝ), IsEigenvector G label lam x := by
  intro hrule
  exact not_exists_isEigenvector_flipLabel
    (hrule Bool Bool inferInstance inferInstance inferInstance flipGraph flipLabel
      exists_target_flipGraph nonempty_walk_flipGraph)

end Reflection

end MaxAffineTransport

end

end DirectedTransport
