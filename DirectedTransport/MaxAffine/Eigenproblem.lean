/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DirectedTransport.MaxAffine.Contraction
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

import FixedPointTheorems.brouwer
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Order.Lattice

/-!
# Eigenvectors of the vertex operator at nonnegative slopes

The eigenvalue equation `F x = lam + x` for the vertex operator `F` of a max-affine labelling is
solved here for **every** nonnegative choice of slopes on a finite strongly connected graph, with
floors allowed.  Neither of the two regimes already available applies: a slope above one makes `F`
expansive in the sup-norm, so it is not a contraction, and a slope different from one destroys
additive homogeneity, so `F` is not topical.  The argument below uses neither property.

The device is an **exponential change of coordinates**.  A label acts by
`z ↦ max floor (shift + slope * z)`; conjugating by the exponential turns that into
`y ↦ max (exp floor) (exp shift * y ^ slope)` on the positive half-line, a *monomial* rather than
an affine expression.  This is `DirectedTransport.MaxAffineTransport.coneTerm`, and taking the
best incoming demand at each vertex gives the **cone operator**
`DirectedTransport.MaxAffineTransport.coneOperator`, which satisfies
`exp (F x v) = Φ (exp ∘ x) v`
(`DirectedTransport.MaxAffineTransport.exp_vertexOperator`).

What is gained is that `Φ` extends continuously to the **closed** cone `[0, ∞)^V`, because
`y ↦ y ^ a` is continuous at `0` for every `a ≥ 0` -- with the value `0` when `a > 0` and the value
`1` when `a = 0`.  This is exactly where nonnegativity of the slopes enters, and it is the whole of
its role.  Normalizing `Φ` by the sum of its coordinates gives a continuous self-map of the
standard simplex, and Brouwer's theorem supplies a fixed point `y` with `Φ y = ρ • y`, where `ρ` is
that sum, positive because some coordinate of `y` is positive and every vertex has an outgoing
edge.  No homogeneity is used: rescaling `y` moves different monomials by different factors, but
the normalized map is a self-map of the simplex all the same, and a single representative of the
ray is all the argument needs.

The fixed point has **full support**.  The set of vertices where `y` is positive is nonempty and
closed under following an edge forward, because a positive source contributes a positive monomial
to the target; in a strongly connected graph such a set is everything.  So `log ∘ y` is defined at
every vertex, and taking logarithms in `Φ y = ρ • y` returns the eigenvalue equation with
eigenvalue `log ρ`.

Negative slopes are genuinely outside the method, not merely outside this proof: `y ^ a` diverges
as `y` decreases to `0` when `a < 0`, so the cone operator has no continuous extension to the
closed simplex, and there is nothing for Brouwer's theorem to act on.  That is the regime of
`DirectedTransport.MaxAffineTransport.not_exists_isEigenvector_flipLabel`, where an eigenvector
provably fails to exist on a strongly connected graph.  The hypothesis `0 ≤ slope` is therefore
sharp.

## Main definitions

* `DirectedTransport.MaxAffineTransport.expWithBot`: the exponential of an element of `WithBot ℝ`,
  with `exp ⊥ = 0`.
* `DirectedTransport.MaxAffineTransport.coneTerm`: the exponential conjugate of a single label's
  demand, a monomial capped below by the exponential of the floor.
* `DirectedTransport.MaxAffineTransport.coneOperator`: the exponential conjugate of the vertex
  operator, defined on the closed cone.

## Main results

* `DirectedTransport.MaxAffineTransport.exp_apply_eq_coneTerm`: the edgewise conjugation identity.
* `DirectedTransport.MaxAffineTransport.exp_vertexOperator`: **the cone operator is the exponential
  conjugate of the vertex operator** on the open cone.
* `DirectedTransport.MaxAffineTransport.continuous_coneOperator`: the cone operator is continuous
  on all of `V → ℝ`, floors and slopes above one notwithstanding.
* `DirectedTransport.MaxAffineTransport.exists_source_eq`: on a strongly connected graph in which
  every vertex has an incoming edge, every vertex has an outgoing edge.
* `DirectedTransport.MaxAffineTransport.exists_mem_stdSimplex_coneOperator_eq`: **Brouwer's
  theorem applied to the normalized cone operator**, an eigenvector of `Φ` in the closed simplex.
* `DirectedTransport.MaxAffineTransport.exists_isEigenvector_of_slope_nonneg_of_incoming` and
  `DirectedTransport.MaxAffineTransport.exists_isEigenvector_of_slope_nonneg`: **a finite strongly
  connected graph whose slopes are all nonnegative carries an eigenvector of its vertex
  operator.**

## Implementation notes

`DirectedTransport.MaxAffineTransport.coneOperator` is defined through `WithBot ℝ` and carries the
junk value `0` at a vertex with no incoming edge, matching
`DirectedTransport.MaxAffineTransport.vertexOperator`; for nonnegative quantities `0` is also the
value an empty supremum ought to have, so the junk value is invisible in the estimates.

Floors need not be eliminated in advance.  A finite floor `b` contributes the constant `exp b` to
the cone term, an extra branch of the maximum that is continuous and nonnegative like the others,
so the proof runs unchanged; the reduction of a floor to an extra slope-`0` edge is available but
is not used.

The headline statement assumes only strong connectivity.  A vertex with no incoming edge forces,
by strong connectivity, that there is no other vertex and hence no edge at all, and on that graph
the vertex operator is constantly `0`, so `lam = 0` and `x = 0` solve the equation; that case is
split off and the remaining work is
`DirectedTransport.MaxAffineTransport.exists_isEigenvector_of_slope_nonneg_of_incoming`.

## TODO

The eigenvalue produced here is not unique and neither is the eigenvector, so what the Brouwer
argument leaves open is narrower than it first appears.  Both failures are settled in
`DirectedTransport.MaxAffine.Spectrum` on one vertex carrying a reset of slope `0` and a doubling
of slope `2`: its eigenvalues are exactly the reals from `5` upwards
(`DirectedTransport.MaxAffineTransport.eigenvalues_loopLabel`), each of them above `5` carried by
two distinct eigenvectors
(`DirectedTransport.MaxAffineTransport.exists_pair_ne_isEigenvector_loopLabel`).  So no formula
determines the eigenvalue at nonnegative slopes straddling one, and the question is which real
numbers are eigenvalues rather than which one is.

The **least** eigenvalue is not open, and needs none of this file: every eigenvalue is a level at
which the inequality `F x ≤ lam + x` is solvable, and by
`DirectedTransport.MaxAffine.LeastEigenvalue` a least such level is the least eigenvalue whenever
every vertex has an incoming edge, so the value is the optimum of an explicit finite linear
program.  The cyclewise description of that optimum available in the comparable regimes -- the
maximum cycle mean of the unit-slope subgraph -- does not extend to mixed slopes, by
`DirectedTransport.MaxAffineTransport.not_forall_mem_relaxationLevels_iff_unitSlopeCycles_le`.
What the Brouwer argument supplies beyond that is the eigenvalues above the least one, which the
linear program does not describe.

## References

* S. Gaubert and J. Gunawardena, *The Perron--Frobenius theorem for homogeneous, monotone
  functions*, Trans. Amer. Math. Soc. 356 (2004), 4931-4950.
* R. D. Nussbaum, *Hilbert's projective metric and iterated nonlinear maps*, Mem. Amer. Math. Soc.
  75 (1988), no. 391.
* L. E. J. Brouwer, *Über Abbildung von Mannigfaltigkeiten*, Math. Ann. 71 (1911), 97-115.

## Tags

vertex operator, eigenvector, max-affine, Brouwer fixed point, simplex, Perron-Frobenius
-/

@[expose] public section

namespace DirectedTransport

noncomputable section

namespace MaxAffineTransport

universe uV uE

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E} {label : E → Label} {y : V → ℝ}

/-! ## The exponential conjugate of a label -/

/-- The exponential of an element of `WithBot ℝ`, sending `⊥` to `0`.  It is the continuous
extension of `Real.exp` to the bottom of the line, and turns a floor into a multiplicative
lower bound. -/
def expWithBot (b : WithBot ℝ) : ℝ := b.recBotCoe 0 Real.exp

@[simp] theorem expWithBot_bot : expWithBot (⊥ : WithBot ℝ) = 0 := rfl

@[simp] theorem expWithBot_coe (r : ℝ) : expWithBot (r : WithBot ℝ) = Real.exp r := rfl

/-- The exponential of an element of `WithBot ℝ` is nonnegative. -/
theorem expWithBot_nonneg (b : WithBot ℝ) : 0 ≤ expWithBot b := by
  induction b using WithBot.recBotCoe with
  | bot => exact le_rfl
  | coe r => exact (Real.exp_pos r).le

/-- The **exponential conjugate of a label's demand along an edge**: the monomial
`exp shift * y ^ slope` in the value at the source, capped below by the exponential of the floor.
On the open cone this is `exp` of `DirectedTransport.MaxAffineTransport.Label.apply` at the
logarithm, by `DirectedTransport.MaxAffineTransport.exp_apply_eq_coneTerm`. -/
def coneTerm (G : EdgeGraph V E) (label : E → Label) (y : V → ℝ) (e : E) : ℝ :=
  max (expWithBot (label e).floor)
    (Real.exp (label e).shift * y (G.source e) ^ (label e).slope)

/-- A cone term is nonnegative, the floor branch already being so. -/
theorem coneTerm_nonneg (G : EdgeGraph V E) (label : E → Label) (y : V → ℝ) (e : E) :
    0 ≤ coneTerm G label y e :=
  le_trans (expWithBot_nonneg _) (le_max_left _ _)

/-- The monomial branch is dominated by the cone term. -/
theorem mul_rpow_le_coneTerm (G : EdgeGraph V E) (label : E → Label) (y : V → ℝ) (e : E) :
    Real.exp (label e).shift * y (G.source e) ^ (label e).slope ≤ coneTerm G label y e :=
  le_max_right _ _

/-- **The edgewise conjugation identity.**  At a positive value the exponential turns the
max-affine demand of an edge into its cone term: the shift becomes a factor, the slope becomes an
exponent, and the floor becomes a multiplicative lower bound. -/
theorem exp_apply_eq_coneTerm (G : EdgeGraph V E) (label : E → Label) {y : V → ℝ}
    (hy : ∀ v : V, 0 < y v) (e : E) :
    Real.exp ((label e).apply (Real.log (y (G.source e)))) = coneTerm G label y e := by
  have hz : 0 < y (G.source e) := hy (G.source e)
  have haffine : Real.exp ((label e).affinePart (Real.log (y (G.source e))))
      = Real.exp (label e).shift * y (G.source e) ^ (label e).slope := by
    rw [Real.rpow_def_of_pos hz, Label.affinePart, Real.exp_add, mul_comm (Real.log _)]
  rcases (label e).floor_cases with hfloor | ⟨b, hfloor⟩
  · have hpos : 0 < Real.exp (label e).shift * y (G.source e) ^ (label e).slope :=
      mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hz _)
    rw [Label.apply_of_floor_bot hfloor, haffine, coneTerm, hfloor, expWithBot_bot,
      max_eq_right hpos.le]
  · rw [Label.apply_of_floor_coe hfloor, Real.exp_monotone.map_max, haffine, coneTerm, hfloor,
      expWithBot_coe]

/-! ## The cone operator -/

section ConeOperator

variable [Fintype E] [DecidableEq V]

/-- The **cone operator**: the best cone term over the edges arriving at a vertex, with the junk
value `0` at a vertex with no incoming edge.  It is the exponential conjugate of
`DirectedTransport.MaxAffineTransport.vertexOperator`, and unlike that operator it is defined and
continuous on the closed cone `[0, ∞)^V`. -/
def coneOperator (G : EdgeGraph V E) (label : E → Label) (y : V → ℝ) (vertex : V) : ℝ :=
  ((incoming G vertex).sup fun e => ((coneTerm G label y e : ℝ) : WithBot ℝ)).unbotD 0

/-- At a vertex with an incoming edge the cone operator is the greatest incoming cone term. -/
theorem coneOperator_eq_sup' {vertex : V} (hne : (incoming G vertex).Nonempty) :
    coneOperator G label y vertex =
      (incoming G vertex).sup' hne fun e => coneTerm G label y e := by
  have hcoe : ((((incoming G vertex).sup' hne fun e => coneTerm G label y e : ℝ) : WithBot ℝ))
      = (incoming G vertex).sup fun e => ((coneTerm G label y e : ℝ) : WithBot ℝ) := by
    rw [Finset.coe_sup']
    rfl
  rw [coneOperator, ← hcoe, WithBot.unbotD_coe]

/-- Every incoming edge is dominated by the cone operator. -/
theorem coneTerm_le_coneOperator {vertex : V} {e : E} (he : G.target e = vertex) :
    coneTerm G label y e ≤ coneOperator G label y vertex := by
  have hne : (incoming G vertex).Nonempty := ⟨e, mem_incoming.2 he⟩
  rw [coneOperator_eq_sup' hne]
  exact Finset.le_sup' (fun e => coneTerm G label y e) (mem_incoming.2 he)

/-- The cone operator is nonnegative, its junk value included. -/
theorem coneOperator_nonneg (G : EdgeGraph V E) (label : E → Label) (y : V → ℝ) (vertex : V) :
    0 ≤ coneOperator G label y vertex := by
  rcases (incoming G vertex).eq_empty_or_nonempty with hempty | hne
  · rw [coneOperator, hempty, Finset.sup_empty]
    rfl
  · rw [coneOperator_eq_sup' hne]
    obtain ⟨e, he⟩ := hne
    exact le_trans (coneTerm_nonneg G label y e) (Finset.le_sup' _ he)

/-- **The cone operator is the exponential conjugate of the vertex operator.**  At a strictly
positive argument, and at a vertex with an incoming edge, the exponential carries the supremum of
the max-affine demands to the supremum of the cone terms, being monotone. -/
theorem exp_vertexOperator (G : EdgeGraph V E) (label : E → Label) {y : V → ℝ}
    (hy : ∀ v : V, 0 < y v) {vertex : V} (hne : (incoming G vertex).Nonempty) :
    Real.exp (vertexOperator G label (fun v => Real.log (y v)) vertex)
      = coneOperator G label y vertex := by
  rw [vertexOperator_eq_sup' hne, coneOperator_eq_sup',
    Finset.apply_sup'_eq_sup'_comp hne _ fun a b => Real.exp_monotone.map_max]
  exact Finset.sup'_congr hne rfl fun e _ => exp_apply_eq_coneTerm G label hy e

/-! ## Continuity on the closed cone -/

omit [Fintype E] [DecidableEq V] in
/-- Each cone term is continuous in the argument, for a nonnegative slope.  This is the only place
where nonnegativity is used, and it is used at the boundary of the cone: `y ^ a` extends
continuously to `y = 0` exactly when `a ≥ 0`. -/
theorem continuous_coneTerm (G : EdgeGraph V E) (label : E → Label) {e : E}
    (hslope : 0 ≤ (label e).slope) :
    Continuous fun y : V → ℝ => coneTerm G label y e :=
  continuous_const.max (continuous_const.mul
    ((Real.continuous_rpow_const hslope).comp (continuous_apply (G.source e))))

/-- **The cone operator is continuous on the whole of `V → ℝ`**, a finite maximum of continuous
cone terms.  No positivity of the argument is needed, and no bound on the slopes beyond
nonnegativity: a slope above one is as harmless here as a slope below one. -/
theorem continuous_coneOperator (G : EdgeGraph V E) (label : E → Label)
    (hslope : ∀ e : E, 0 ≤ (label e).slope) (vertex : V) :
    Continuous fun y : V → ℝ => coneOperator G label y vertex := by
  rcases (incoming G vertex).eq_empty_or_nonempty with hempty | hne
  · have hzero : ∀ y : V → ℝ, coneOperator G label y vertex = 0 := by
      intro y
      rw [coneOperator, hempty, Finset.sup_empty]
      rfl
    simpa only [hzero] using continuous_const
  · simpa only [coneOperator_eq_sup' hne] using
      Continuous.finset_sup'_apply (f := fun e (y : V → ℝ) => coneTerm G label y e) hne
        fun e _ => continuous_coneTerm G label (hslope e)

end ConeOperator

/-! ## Outgoing edges on a strongly connected graph -/

section Connectivity

/-- A walk either is empty or ends with an edge arriving at its endpoint. -/
theorem eq_or_exists_target_eq {start finish : V} (walk : G.Walk start finish) :
    start = finish ∨ ∃ e : E, G.target e = finish := by
  cases walk with
  | nil => exact Or.inl rfl
  | concat _ e _ => exact Or.inr ⟨e, rfl⟩

/-- **On a strongly connected graph in which every vertex has an incoming edge, every vertex has
an outgoing edge.**  If no edge left a vertex, no walk could leave it either, so the source of one
of its incoming edges would be the vertex itself. -/
theorem exists_source_eq (G : EdgeGraph V E)
    (hinEdge : ∀ vertex : V, ∃ e : E, G.target e = vertex)
    (hconn : ∀ start finish : V, Nonempty (G.Walk start finish)) (vertex : V) :
    ∃ e : E, G.source e = vertex := by
  by_contra hcon
  have hne : ∀ e : E, G.source e ≠ vertex := fun e he => hcon ⟨e, he⟩
  have hstay : ∀ {finish : V}, G.Walk vertex finish → finish = vertex := by
    intro finish walk
    induction walk with
    | nil => rfl
    | concat _ e legal ih => exact absurd (legal.trans ih) (hne e)
  obtain ⟨e, he⟩ := hinEdge vertex
  obtain ⟨walk⟩ := hconn vertex (G.source e)
  exact hne e (hstay walk)

end Connectivity

/-! ## The fixed point on the simplex -/

section Brouwer

variable [Fintype V] [Fintype E] [DecidableEq V]

omit [Fintype E] [DecidableEq V] in
/-- Some coordinate of a point of the standard simplex is positive, its coordinates being
nonnegative and summing to one. -/
theorem exists_pos_of_mem_stdSimplex {y : V → ℝ} (hy : y ∈ stdSimplex ℝ V) :
    ∃ u : V, 0 < y u := by
  by_contra hcon
  have hzero : ∀ u : V, y u = 0 := fun u => le_antisymm (not_lt.1 fun h => hcon ⟨u, h⟩) (hy.1 u)
  have hsum := hy.2
  simp only [hzero, Finset.sum_const_zero] at hsum
  exact zero_ne_one hsum

/-- The sum of the coordinates of the cone operator, the normalizing factor turning it into a
self-map of the standard simplex. -/
def coneScale (G : EdgeGraph V E) (label : E → Label) (y : V → ℝ) : ℝ :=
  ∑ vertex : V, coneOperator G label y vertex

/-- **The normalizing factor is positive on the simplex.**  Some coordinate of a point of the
simplex is positive, and the edge leaving that vertex contributes a positive monomial to the cone
operator at its target. -/
theorem coneScale_pos (G : EdgeGraph V E) (label : E → Label)
    (hout : ∀ vertex : V, ∃ e : E, G.source e = vertex) {y : V → ℝ}
    (hy : y ∈ stdSimplex ℝ V) : 0 < coneScale G label y := by
  obtain ⟨u, hu⟩ := exists_pos_of_mem_stdSimplex hy
  obtain ⟨e, he⟩ := hout u
  have hterm : 0 < coneTerm G label y e := by
    refine lt_of_lt_of_le ?_ (mul_rpow_le_coneTerm G label y e)
    rw [he]
    exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hu _)
  refine lt_of_lt_of_le (lt_of_lt_of_le hterm (coneTerm_le_coneOperator (rfl : G.target e = _)))
    (Finset.single_le_sum (f := fun vertex => coneOperator G label y vertex)
      (fun vertex _ => coneOperator_nonneg G label y vertex) (Finset.mem_univ (G.target e)))

/-- The normalized cone operator, a self-map of the standard simplex wherever the normalizing
factor is positive. -/
def coneMap (G : EdgeGraph V E) (label : E → Label) (y : V → ℝ) (vertex : V) : ℝ :=
  coneOperator G label y vertex / coneScale G label y

/-- The normalized cone operator lands in the standard simplex. -/
theorem coneMap_mem_stdSimplex (G : EdgeGraph V E) (label : E → Label)
    (hout : ∀ vertex : V, ∃ e : E, G.source e = vertex) {y : V → ℝ}
    (hy : y ∈ stdSimplex ℝ V) : coneMap G label y ∈ stdSimplex ℝ V := by
  have hscale := coneScale_pos G label hout hy
  refine ⟨fun vertex => div_nonneg (coneOperator_nonneg G label y vertex) hscale.le, ?_⟩
  simp only [coneMap]
  rw [← Finset.sum_div]
  exact div_self hscale.ne'

/-- **Brouwer's theorem applied to the normalized cone operator.**  The standard simplex is
nonempty, convex and compact, and the normalized cone operator is a continuous self-map of it, so
it has a fixed point; multiplying through by the normalizing factor gives a point of the simplex
on which the cone operator acts by a positive scalar. -/
theorem exists_mem_stdSimplex_coneOperator_eq [Nonempty V] (G : EdgeGraph V E) (label : E → Label)
    (hslope : ∀ e : E, 0 ≤ (label e).slope)
    (hout : ∀ vertex : V, ∃ e : E, G.source e = vertex) :
    ∃ (rho : ℝ) (y : V → ℝ), y ∈ stdSimplex ℝ V ∧ 0 < rho ∧
      ∀ vertex : V, coneOperator G label y vertex = rho * y vertex := by
  set s : Set (V → ℝ) := stdSimplex ℝ V with hs
  have hscale : ∀ y : s, 0 < coneScale G label (y : V → ℝ) := fun y =>
    coneScale_pos G label hout y.2
  have hcontScale : Continuous fun y : s => coneScale G label (y : V → ℝ) :=
    continuous_finsetSum _ fun vertex _ =>
      (continuous_coneOperator G label hslope vertex).comp continuous_subtype_val
  have hcont : Continuous fun y : s => (⟨coneMap G label (y : V → ℝ),
      coneMap_mem_stdSimplex G label hout y.2⟩ : s) := by
    refine Continuous.subtype_mk (continuous_pi fun vertex => ?_) _
    exact Continuous.div
      ((continuous_coneOperator G label hslope vertex).comp continuous_subtype_val) hcontScale
      fun y => (hscale y).ne'
  obtain ⟨y, hy⟩ := brouwer_fixed_point s (convex_stdSimplex ℝ V) (isCompact_stdSimplex ℝ V)
    ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary V)⟩ ⟨_, hcont⟩
  refine ⟨coneScale G label (y : V → ℝ), (y : V → ℝ), y.2, hscale y, fun vertex => ?_⟩
  have hfix : coneMap G label (y : V → ℝ) = (y : V → ℝ) := congrArg Subtype.val hy
  have hcoord := congrFun hfix vertex
  rw [coneMap, div_eq_iff (hscale y).ne'] at hcoord
  rw [hcoord, mul_comm]

end Brouwer

/-! ## Eigenvectors at nonnegative slopes -/

section Eigen

variable [Fintype V] [Fintype E] [DecidableEq V]

/-- **The fixed point of the normalized cone operator has full support.**  The vertices where it is
positive form a nonempty set closed under following an edge forward, because a positive value at
the source of an edge contributes a positive monomial at its target; strong connectivity then
spreads positivity everywhere. -/
theorem coneOperator_fixedPoint_pos (G : EdgeGraph V E) (label : E → Label)
    (hconn : ∀ start finish : V, Nonempty (G.Walk start finish)) {rho : ℝ} (hrho : 0 < rho)
    {y : V → ℝ} (hy : y ∈ stdSimplex ℝ V)
    (hfix : ∀ vertex : V, coneOperator G label y vertex = rho * y vertex) (vertex : V) :
    0 < y vertex := by
  obtain ⟨u, hu⟩ := exists_pos_of_mem_stdSimplex hy
  have hstep : ∀ {a : V} (e : E), G.source e = a → 0 < y a → 0 < y (G.target e) := by
    intro a e he ha
    have hterm : 0 < coneTerm G label y e := by
      refine lt_of_lt_of_le ?_ (mul_rpow_le_coneTerm G label y e)
      rw [he]
      exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos ha _)
    have hle := lt_of_lt_of_le hterm
      (coneTerm_le_coneOperator (y := y) (label := label) (rfl : G.target e = _))
    rw [hfix (G.target e)] at hle
    exact pos_of_mul_pos_right hle hrho.le
  have hspread : ∀ {finish : V}, G.Walk u finish → 0 < y finish := by
    intro finish walk
    induction walk with
    | nil => exact hu
    | concat _ e legal ih => exact hstep e legal ih
  exact hspread (hconn u vertex).some

/-- **A finite strongly connected graph whose slopes are all nonnegative carries an eigenvector of
its vertex operator**, floors and slopes above one included.  The proof is by Brouwer's theorem in
exponential coordinates; the eigenvalue is the logarithm of the scaling factor of the fixed point
of the normalized cone operator, and the eigenvector is its coordinatewise logarithm.

Every vertex is asked to have an incoming edge, which makes the real-valued vertex operator
faithful; `DirectedTransport.MaxAffineTransport.exists_isEigenvector_of_slope_nonneg` removes that
hypothesis. -/
theorem exists_isEigenvector_of_slope_nonneg_of_incoming [Nonempty V] (G : EdgeGraph V E)
    (label : E → Label) (hslope : ∀ e : E, 0 ≤ (label e).slope)
    (hinEdge : ∀ vertex : V, ∃ e : E, G.target e = vertex)
    (hconn : ∀ start finish : V, Nonempty (G.Walk start finish)) :
    ∃ (lam : ℝ) (x : V → ℝ), IsEigenvector G label lam x := by
  have hout := exists_source_eq G hinEdge hconn
  obtain ⟨rho, y, hy, hrho, hfix⟩ :=
    exists_mem_stdSimplex_coneOperator_eq G label hslope hout
  have hpos : ∀ vertex : V, 0 < y vertex :=
    coneOperator_fixedPoint_pos G label hconn hrho hy hfix
  refine ⟨Real.log rho, fun v => Real.log (y v), fun vertex => ?_⟩
  have hne : (incoming G vertex).Nonempty := by
    obtain ⟨e, he⟩ := hinEdge vertex
    exact ⟨e, mem_incoming.2 he⟩
  have hexp : Real.exp (vertexOperator G label (fun v => Real.log (y v)) vertex)
      = Real.exp (Real.log rho + Real.log (y vertex)) := by
    rw [exp_vertexOperator G label hpos hne, hfix vertex, Real.exp_add, Real.exp_log hrho,
      Real.exp_log (hpos vertex)]
  exact Real.exp_injective hexp

/-- **The eigenvalue equation is solvable at nonnegative slopes.**  On a finite nonempty strongly
connected graph whose labels all have nonnegative slope -- floors permitted, slopes above one
permitted, no bound on the slopes at all -- the vertex operator has an eigenvector.

This is the sharp complement of
`DirectedTransport.MaxAffineTransport.not_exists_isEigenvector_flipLabel`, where slope `-1` on a
strongly connected two-vertex graph admits no eigenvector for any eigenvalue: at a negative slope
the exponential conjugate `y ^ slope` blows up at the boundary of the cone and the compactness
argument has nothing to act on, while at every nonnegative slope it extends continuously.

Neither of the two earlier regimes covers this.  The operator need not be a contraction, since a
slope above one is allowed, and it need not be additively homogeneous, since a slope below one is
allowed; correspondingly neither the eigenvalue nor the eigenvector is unique, by
`DirectedTransport.MaxAffineTransport.eigenvalues_loopLabel` and
`DirectedTransport.MaxAffineTransport.exists_pair_ne_isEigenvector_loopLabel`. -/
theorem exists_isEigenvector_of_slope_nonneg [Nonempty V] (G : EdgeGraph V E) (label : E → Label)
    (hslope : ∀ e : E, 0 ≤ (label e).slope)
    (hconn : ∀ start finish : V, Nonempty (G.Walk start finish)) :
    ∃ (lam : ℝ) (x : V → ℝ), IsEigenvector G label lam x := by
  by_cases hinEdge : ∀ vertex : V, ∃ e : E, G.target e = vertex
  · exact exists_isEigenvector_of_slope_nonneg_of_incoming G label hslope hinEdge hconn
  · obtain ⟨base, hbase'⟩ := not_forall.1 hinEdge
    have hbase : ∀ e : E, G.target e ≠ base := not_exists.1 hbase'
    have hsub : ∀ u : V, u = base := by
      intro u
      rcases eq_or_exists_target_eq (hconn u base).some with heq | ⟨e, he⟩
      · exact heq
      · exact absurd he (hbase e)
    have hempty : ∀ vertex : V, incoming G vertex = ∅ := by
      intro vertex
      refine Finset.eq_empty_of_forall_notMem fun e he => ?_
      exact hbase e ((mem_incoming.1 he).trans (hsub vertex))
    refine ⟨0, fun _ => 0, fun vertex => ?_⟩
    rw [vertexOperator_of_incoming_eq_empty (hempty vertex), add_zero]

end Eigen

end MaxAffineTransport

end

end DirectedTransport
