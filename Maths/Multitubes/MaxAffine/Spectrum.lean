/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.MaxAffine.CycleSlack
public import Maths.Multitubes.MaxAffine.Eigenproblem
public import Maths.Multitubes.MaxAffine.Farkas
public import Maths.Multitubes.MaxAffine.Slopes

/-!
# The set of eigenvalues of a max-affine vertex operator

`Maths.MaxAffineTransport.exists_isEigenvector_of_slope_nonneg` produces an
eigenvector of the vertex operator `F` on any finite strongly connected graph with nonnegative
slopes, and says nothing about which real number the eigenvalue is.  This file studies the whole
set

`Maths.MaxAffineTransport.eigenvalues G label = {lam | ∃ x, F x = lam + x}`

not a single eigenvalue, and settles that the eigenvalue is **not** determined by the
labelling once a slope differs from one.

The comparison object is the set of **relaxation levels**
`Maths.MaxAffineTransport.relaxationLevels`, the real numbers `lam` for which the
relaxed labelling `Maths.MaxAffineTransport.Label.relax lam ∘ label` admits a lax
section, that is for which `F x ≤ lam + x` is solvable.  Two facts are immediate and hold with no
hypothesis on the slopes at all: an eigenvector is in particular a solution of the inequality, so
every eigenvalue is a relaxation level, and the inequality only becomes easier as `lam` grows, so
the relaxation levels form an up-set.  The eigenvalues are therefore squeezed into an up-set whose
infimum is a lower bound for every eigenvalue, and that up-set is computable: it is the feasible
set of a finite system of linear inequalities in the pair `(lam, x)`, one row for each branch of
each label.

In the two regimes where the sub-fixed-point theory is complete the up-set is described by cycles.
For slopes at most one, and for slopes at least one with floors absent, a lax section exists exactly
when every closed walk of the unit-slope subgraph has nonpositive shift sum, by the two cycle
criteria of `Maths.Multitubes.MaxAffine.Slopes`.  Those two are one criterion read along
the constant recession directions `1` and `-1`, by
`Maths.MaxAffineTransport.exists_isLaxSection_iff_exists_unitSlopePotential_of_const_direction`;
the pairs of statements below inherit that duplication, and are kept apart because relaxation
moves the branch index to that of the relaxed labelling.
Relaxing by `lam` subtracts `lam` from
every shift, so the criterion becomes a **cycle-mean bound**: `lam` is a relaxation level exactly
when no closed walk of the unit-slope subgraph has mean shift above `lam`.  Consequently every
eigenvalue is at least the maximum cycle mean of the unit-slope subgraph, which at unit slopes
throughout is the maximum cycle mean of the shifts and recovers the eigenvalue of the translation
regime, and below unit slope is vacuous, matching the fact that every real number is then an
eigenvalue.

Both remaining claims of the file are settled on one vertex carrying two loops, the reset
`x ↦ 10` of slope `0` and the doubling `x ↦ 2 * x` of slope `2` of
`Maths.MaxAffineTransport.loopLabel`.  Its vertex operator is `t ↦ max 10 (2 * t)`,
so the eigenvalue equation reads `max (10 - t) t = lam` and its solutions are exactly the
`lam ≥ 5`:

* the eigenvalue is not unique, and the set of eigenvalues is a proper closed half-line rather
  than a point or all of `ℝ`, at slopes that are nonnegative and straddle one; nor is the
  eigenvector unique, the two branches of the maximum giving two of them above the threshold;
* the cycle-mean formula does not extend to mixed slopes, because the unit-slope subgraph here is
  empty, so its cycle bound is vacuous while `5` is a genuine lower bound.

That the eigenvalue is not an invariant is not new at a single common slope: translating an
eigenvector of a floorless labelling of common slope `s` moves the eigenvalue by `-(1 - s) * c`
(`Maths.MaxAffineTransport.isEigenvector_add_const_of_slope_eq`), which combined with
existence at nonnegative slopes gives **every** real number as an eigenvalue when `s ≠ 1`.  The
same computation shows the translation freedom of the eigenvector is spent, not lost: at
`s ≠ 1` two eigenvectors of the *same* eigenvalue never differ by a nonzero constant, so the
equivalence under which the topical eigenvector is unique degenerates; it does not fail.

## Main definitions

* `Maths.MaxAffineTransport.eigenvalues`: the set of eigenvalues of the vertex
  operator.
* `Maths.MaxAffineTransport.relaxationLevels`: the set of levels at which the
  relaxed labelling has a lax section, equivalently the solvable levels of `F x ≤ lam + x`.

## Main results

* `Maths.MaxAffineTransport.eigenvalues_subset_relaxationLevels` and
  `Maths.MaxAffineTransport.mem_relaxationLevels_of_le`: **the eigenvalues lie in an
  up-set of relaxation levels**, with no hypothesis on the slopes.
* `Maths.MaxAffineTransport.mem_relaxationLevels_iff_unitSlopeCycles_of_slope_le_one`
  and
  `Maths.MaxAffineTransport.mem_relaxationLevels_iff_unitSlopeCycles_of_one_le_slope`:
  **the relaxation levels are the upper bounds of the unit-slope cycle means**, in the subunit and
  superunit regimes.
* `Maths.MaxAffineTransport.unitSlopeCycles_le_of_isEigenvector_of_slope_le_one` and
  `Maths.MaxAffineTransport.unitSlopeCycles_le_of_isEigenvector_of_one_le_slope`:
  **every eigenvalue dominates every unit-slope cycle mean** in those regimes.
* `Maths.MaxAffineTransport.eigenvalues_eq_univ_of_slope_eq`: **at a common
  nonnegative slope other than one every real number is an eigenvalue.**
* `Maths.MaxAffineTransport.eq_zero_of_isEigenvector_add_const_of_slope_eq`: at a
  common slope other than one, eigenvectors of one eigenvalue never differ by a nonzero constant.
* `Maths.MaxAffineTransport.eigenvalues_loopLabel`: **the two-loop labelling has
  exactly the eigenvalues `lam ≥ 5`**, so the eigenvalue is not unique at nonnegative slopes
  straddling one, and the set of eigenvalues can be a proper half-line.
* `Maths.MaxAffineTransport.exists_pair_ne_isEigenvector_loopLabel`: above the
  threshold that labelling has two distinct eigenvectors for one eigenvalue.
* `Maths.MaxAffineTransport.relaxationLevels_loopLabel`: for that labelling the
  relaxation levels are the same half-line, so its least eigenvalue is its least relaxation
  level.
* `Maths.MaxAffineTransport.not_forall_mem_relaxationLevels_iff_unitSlopeCycles_le`:
  **the unit-slope cycle bound is not the right formula at mixed slopes.**

## Implementation notes

`Maths.MaxAffineTransport.relaxationLevels` is defined through
`Maths.MaxAffineTransport.Label.relax`, not by an inequality on the vertex
operator, so that it needs no finiteness of the edge type and no hypothesis that a vertex has an
incoming edge, and so that the criteria of `Maths.Multitubes.MaxAffine.Slopes` apply to it
verbatim.  `Maths.MaxAffineTransport.mem_relaxationLevels_iff` is the elementary
edgewise reading, and `Maths.MaxAffineTransport.eigenvalues_subset_relaxationLevels`
is the only place the vertex operator meets it.

Relaxation leaves the slopes untouched, so the unit-slope subgraph of a relaxed labelling is the
unit-slope subgraph of the original one, definitionally; the cycle criteria are transported
across that identification without any coercion of walks.

## TODO

Find structural criteria and efficient algorithms for the levels above the least eigenvalue.
`Maths.Multitubes.MaxAffine.PolicySpectrum` characterizes the entire spectrum as a finite union
of closed convex policy-level sets, without restrictions on slope signs or connectivity. On a
strongly connected graph with nonnegative slopes and an incoming edge at every vertex, a least
relaxation level is the least eigenvalue, by `Maths.Multitubes.MaxAffine.LeastEigenvalue`, so
it is the optimum of an explicit finite linear program in the pair `(lam, x)`. The two-loop
labelling shows that everything above it may be an eigenvalue too. A criterion avoiding policy
enumeration, and executable computation of policy endpoints, require further results.

## References

* S. Gaubert and J. Gunawardena, *The Perron--Frobenius theorem for homogeneous, monotone
  functions*, Trans. Amer. Math. Soc. 356 (2004), 4931-4950.
* R. D. Nussbaum, *Hilbert's projective metric and iterated nonlinear maps*, Mem. Amer. Math. Soc.
  75 (1988), no. 391.
* F. Baccelli, G. Cohen, G. J. Olsder and J.-P. Quadrat, *Synchronization and Linearity*, Wiley
  (1992).

## Tags

eigenvalue, Collatz-Wielandt, vertex operator, max-affine, cycle mean, lax section
-/

@[expose] public section

namespace Maths

noncomputable section

namespace MaxAffineTransport

universe uV uE

variable {V : Type uV} {E : Type uE}

/-! ## Eigenvalues and relaxation levels -/

section Sets

variable {G : EdgeGraph V E} {label : E → Label}

/-- The set of **eigenvalues** of the vertex operator: the reals `lam` for which the equation
`F x = lam + x` has a solution. -/
def eigenvalues [Fintype E] [DecidableEq V] (G : EdgeGraph V E) (label : E → Label) : Set ℝ :=
  {lam | ∃ x : V → ℝ, IsEigenvector G label lam x}

/-- Membership in the set of eigenvalues is solvability of the eigenvalue equation. -/
theorem mem_eigenvalues_iff [Fintype E] [DecidableEq V] (G : EdgeGraph V E) (label : E → Label)
    (lam : ℝ) : lam ∈ eigenvalues G label ↔ ∃ x : V → ℝ, IsEigenvector G label lam x := Iff.rfl

/-- The set of **relaxation levels** of a labelling: the reals `lam` for which subtracting `lam`
from every label leaves a labelling with a lax section, equivalently for which the inequality
`F x ≤ lam + x` is solvable. -/
def relaxationLevels (G : EdgeGraph V E) (label : E → Label) : Set ℝ :=
  {lam | ∃ x : V → ℝ, IsLaxSection G (fun e => Label.relax lam (label e)) x}

/-- A relaxation level read edgewise: some candidate overshoots no edge by more than the level. -/
theorem mem_relaxationLevels_iff (G : EdgeGraph V E) (label : E → Label) (lam : ℝ) :
    lam ∈ relaxationLevels G label ↔
      ∃ x : V → ℝ, ∀ e : E, (label e).apply (x (G.source e)) ≤ lam + x (G.target e) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, fun e => ?_⟩
    have he := hx e
    rw [Label.apply_relax] at he
    linarith
  · rintro ⟨x, hx⟩
    refine ⟨x, fun e => ?_⟩
    have he := hx e
    rw [Label.apply_relax]
    linarith

/-- **The relaxation levels form an up-set.**  Weakening the level weakens every edge
inequality, so the same candidate still serves. -/
theorem mem_relaxationLevels_of_le {lam mu : ℝ} (hlam : lam ∈ relaxationLevels G label)
    (hle : lam ≤ mu) : mu ∈ relaxationLevels G label := by
  rw [mem_relaxationLevels_iff] at hlam ⊢
  obtain ⟨x, hx⟩ := hlam
  exact ⟨x, fun e => (hx e).trans (by linarith)⟩

/-- A lax section is exactly a relaxation at level zero. -/
theorem zero_mem_relaxationLevels_iff (G : EdgeGraph V E) (label : E → Label) :
    (0 : ℝ) ∈ relaxationLevels G label ↔ ∃ x : V → ℝ, IsLaxSection G label x := by
  rw [mem_relaxationLevels_iff]
  exact ⟨fun ⟨x, hx⟩ => ⟨x, fun e => by have := hx e; linarith⟩,
    fun ⟨x, hx⟩ => ⟨x, fun e => by have := hx e; linarith⟩⟩

variable [Fintype E] [DecidableEq V]

/-- **Every eigenvalue is a relaxation level.**  An eigenvector solves each edge inequality with
equality at the best incoming edge and with slack at the others. -/
theorem eigenvalues_subset_relaxationLevels (G : EdgeGraph V E) (label : E → Label) :
    eigenvalues G label ⊆ relaxationLevels G label := by
  rintro lam ⟨x, hx⟩
  refine (mem_relaxationLevels_iff G label lam).2 ⟨x, fun e => ?_⟩
  have hle := le_vertexOperator (G := G) (label := label) (x := x) (e := e) rfl
  rw [hx (G.target e)] at hle
  exact hle

end Sets

/-! ## The cycle description of the relaxation levels -/

section Cycles

variable [Fintype V] [DecidableEq V] [Fintype E] {G : EdgeGraph V E} {label : E → Label}

omit [Fintype V] [DecidableEq V] [Fintype E] in
/-- **Relaxation is a cycle-mean shift.**  Subtracting the level from every shift subtracts the
level times the length from the weight of every closed walk of the unit-slope subgraph, which
relaxation leaves unchanged. -/
theorem walkWeight_unitSlopeShift_relax (label : E → Label) (lam : ℝ) (base : V)
    (cycle : (unitSlopeGraph G label).Walk base base) :
    MaxPlusPotential.walkWeight (unitSlopeShift fun e => Label.relax lam (label e)) cycle
      = MaxPlusPotential.walkWeight (unitSlopeShift label) cycle - cycle.length * lam := by
  rw [← nsmul_eq_mul,
    ← MaxPlusPotential.walkWeight_sub_const (unitSlopeShift label) lam cycle]
  congr 1
  funext edge
  simp [unitSlopeShift, Label.relax, Label.recenter]

omit [Fintype V] [DecidableEq V] [Fintype E] in
/-- The cycle criterion for a relaxed labelling, read as a bound on the unit-slope cycle
means of the original one. -/
theorem forall_unitSlopeCycles_relax_nonpos_iff (label : E → Label) (lam : ℝ) :
    (∀ (base : V)
        (cycle : (unitSlopeGraph G fun e => Label.relax lam (label e)).Walk base base),
      MaxPlusPotential.walkWeight (unitSlopeShift fun e => Label.relax lam (label e)) cycle ≤ 0)
      ↔ ∀ (base : V) (cycle : (unitSlopeGraph G label).Walk base base),
        MaxPlusPotential.walkWeight (unitSlopeShift label) cycle ≤ cycle.length * lam := by
  constructor
  · intro h base cycle
    have hstep : MaxPlusPotential.walkWeight
        (unitSlopeShift fun e => Label.relax lam (label e)) cycle ≤ 0 := h base cycle
    rw [walkWeight_unitSlopeShift_relax label lam base cycle] at hstep
    linarith
  · intro h base cycle
    have hvalue : MaxPlusPotential.walkWeight
          (unitSlopeShift fun e => Label.relax lam (label e)) cycle
        = MaxPlusPotential.walkWeight (unitSlopeShift label) cycle - cycle.length * lam :=
      walkWeight_unitSlopeShift_relax label lam base cycle
    have hstep : MaxPlusPotential.walkWeight (unitSlopeShift label) cycle
        ≤ cycle.length * lam := h base cycle
    rw [hvalue]
    linarith

/-- **The relaxation levels are the upper bounds of the unit-slope cycle means, in the subunit
regime.**  With every slope at most one, floors permitted, the level `lam` is feasible exactly
when no closed walk of the unit-slope subgraph has shift sum exceeding `lam` times its length. -/
theorem mem_relaxationLevels_iff_unitSlopeCycles_of_slope_le_one
    (hslope : ∀ e : E, (label e).slope ≤ 1) (lam : ℝ) :
    lam ∈ relaxationLevels G label ↔
      ∀ (base : V) (cycle : (unitSlopeGraph G label).Walk base base),
        MaxPlusPotential.walkWeight (unitSlopeShift label) cycle ≤ cycle.length * lam := by
  rw [← forall_unitSlopeCycles_relax_nonpos_iff (G := G) label lam]
  exact exists_isLaxSection_iff_unitSlopeCycles_nonpos_of_slope_le_one
    (G := G) (label := fun e => Label.relax lam (label e)) hslope

/-- **The relaxation levels are the upper bounds of the unit-slope cycle means, in the superunit
regime.**  With every slope at least one and every floor absent, the level `lam` is feasible
exactly when no closed walk of the unit-slope subgraph has shift sum exceeding `lam` times its
length. -/
theorem mem_relaxationLevels_iff_unitSlopeCycles_of_one_le_slope
    (hslope : ∀ e : E, 1 ≤ (label e).slope) (hfloor : ∀ e : E, (label e).floor = ⊥) (lam : ℝ) :
    lam ∈ relaxationLevels G label ↔
      ∀ (base : V) (cycle : (unitSlopeGraph G label).Walk base base),
        MaxPlusPotential.walkWeight (unitSlopeShift label) cycle ≤ cycle.length * lam := by
  have hfloor' : ∀ e : E, (Label.relax lam (label e)).floor = ⊥ := by
    intro e
    simp [Label.relax, Label.recenter, hfloor e]
  rw [← forall_unitSlopeCycles_relax_nonpos_iff (G := G) label lam]
  exact exists_isLaxSection_iff_unitSlopeCycles_nonpos_of_one_le_slope
    (G := G) (label := fun e => Label.relax lam (label e)) hslope hfloor'

/-- **Every eigenvalue dominates every unit-slope cycle mean**, in the subunit regime.  This is
the maximum cycle mean of the translation regime read as a lower bound: at unit slopes throughout
it is attained, and below unit slope the unit-slope subgraph is empty and the bound says
nothing. -/
theorem unitSlopeCycles_le_of_isEigenvector_of_slope_le_one
    (hslope : ∀ e : E, (label e).slope ≤ 1) {lam : ℝ} {x : V → ℝ}
    (hx : IsEigenvector G label lam x) (base : V)
    (cycle : (unitSlopeGraph G label).Walk base base) :
    MaxPlusPotential.walkWeight (unitSlopeShift label) cycle ≤ cycle.length * lam :=
  (mem_relaxationLevels_iff_unitSlopeCycles_of_slope_le_one hslope lam).1
    (eigenvalues_subset_relaxationLevels G label ⟨x, hx⟩) base cycle

/-- **Every eigenvalue dominates every unit-slope cycle mean**, in the superunit regime. -/
theorem unitSlopeCycles_le_of_isEigenvector_of_one_le_slope
    (hslope : ∀ e : E, 1 ≤ (label e).slope) (hfloor : ∀ e : E, (label e).floor = ⊥) {lam : ℝ}
    {x : V → ℝ} (hx : IsEigenvector G label lam x) (base : V)
    (cycle : (unitSlopeGraph G label).Walk base base) :
    MaxPlusPotential.walkWeight (unitSlopeShift label) cycle ≤ cycle.length * lam :=
  (mem_relaxationLevels_iff_unitSlopeCycles_of_one_le_slope hslope hfloor lam).1
    (eigenvalues_subset_relaxationLevels G label ⟨x, hx⟩) base cycle

end Cycles

/-! ## A common slope other than one -/

section CommonSlope

variable [Fintype V] [DecidableEq V] [Fintype E] {G : EdgeGraph V E} {label : E → Label}

/-- **At a common nonnegative slope other than one every real number is an eigenvalue.**  One
eigenvector exists by `Maths.MaxAffineTransport.exists_isEigenvector_of_slope_nonneg`,
and translating it by a constant moves the eigenvalue by `-(1 - s)` times that constant, which at
`s ≠ 1` reaches every real number.  The eigenvalue is therefore not an invariant of the labelling
outside the translation regime, whatever the graph. -/
theorem eigenvalues_eq_univ_of_slope_eq [Nonempty V] (G : EdgeGraph V E) (label : E → Label)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≠ 1) (hslope : ∀ e : E, (label e).slope = s)
    (hfloor : ∀ e : E, (label e).floor = ⊥)
    (hin : ∀ vertex : V, (incoming G vertex).Nonempty)
    (hconn : ∀ start finish : V, Nonempty (G.Walk start finish)) :
    eigenvalues G label = Set.univ := by
  have hinEdge : ∀ vertex : V, ∃ e : E, G.target e = vertex := by
    intro vertex
    obtain ⟨e, he⟩ := hin vertex
    exact ⟨e, mem_incoming.1 he⟩
  obtain ⟨lam, x, hx⟩ := exists_isEigenvector_of_slope_nonneg_of_incoming G label
    (fun e => (hslope e) ▸ hs0) hinEdge hconn
  refine Set.eq_univ_of_forall fun mu => ?_
  have hne : (1 : ℝ) - s ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
  refine ⟨fun v => x v + (lam - mu) / (1 - s), ?_⟩
  have hmove := isEigenvector_add_const_of_slope_eq G hslope hfloor hin hx ((lam - mu) / (1 - s))
  have hvalue : lam - (1 - s) * ((lam - mu) / (1 - s)) = mu := by
    field_simp
    ring
  rwa [hvalue] at hmove

omit [Fintype V] in
/-- **Translation is spent on the eigenvalue, not on the eigenvector.**  At a common slope other
than one, two eigenvectors of the same eigenvalue never differ by a nonzero constant: the
additive freedom that makes the topical eigenvector unique only up to a constant is exactly what
moves the eigenvalue here. -/
theorem eq_zero_of_isEigenvector_add_const_of_slope_eq [Nonempty V] (G : EdgeGraph V E)
    {label : E → Label} {s : ℝ} (hs1 : s ≠ 1) (hslope : ∀ e : E, (label e).slope = s)
    (hfloor : ∀ e : E, (label e).floor = ⊥)
    (hin : ∀ vertex : V, (incoming G vertex).Nonempty) {lam c : ℝ} {x : V → ℝ}
    (hx : IsEigenvector G label lam x) (hxc : IsEigenvector G label lam fun v => x v + c) :
    c = 0 := by
  obtain ⟨vertex⟩ := ‹Nonempty V›
  have hhom := vertexOperator_add_const_of_slope_eq G hslope hfloor x c (hin vertex)
  have hstep := hxc vertex
  rw [hhom, hx vertex] at hstep
  have hzero : (s - 1) * c = 0 := by linarith
  rcases mul_eq_zero.1 hzero with hs | hc
  · exact absurd (by linarith : s = 1) hs1
  · exact hc

end CommonSlope

/-! ## The two-loop labelling and its eigenvalues -/

section TwoLoops

/-- The vertex operator of `Maths.MaxAffineTransport.loopLabel`: the better of the
reset and the doubling. -/
theorem vertexOperator_loopLabel (x : Unit → ℝ) :
    vertexOperator loopGraph loopLabel x () = max 10 (2 * x ()) := by
  have hne : (incoming loopGraph ()).Nonempty := ⟨false, mem_incoming.2 rfl⟩
  refine le_antisymm ?_ (max_le ?_ ?_)
  · rw [vertexOperator_eq_sup' hne]
    refine Finset.sup'_le _ _ fun e _ => ?_
    cases e with
    | false => simp
    | true => simp
  · simpa using le_vertexOperator (G := loopGraph) (label := loopLabel) (x := x) (e := false) rfl
  · simpa using le_vertexOperator (G := loopGraph) (label := loopLabel) (x := x) (e := true) rfl

/-- The eigenvalue equation for the two-loop labelling, in one real unknown. -/
theorem isEigenvector_loopLabel_iff (lam : ℝ) (x : Unit → ℝ) :
    IsEigenvector loopGraph loopLabel lam x ↔ max 10 (2 * x ()) = lam + x () := by
  constructor
  · intro hx
    have := hx ()
    rwa [vertexOperator_loopLabel] at this
  · intro hx vertex
    obtain rfl : vertex = () := rfl
    rw [vertexOperator_loopLabel]
    exact hx

/-- **The two-loop labelling has exactly the eigenvalues `lam ≥ 5`.**  Its slopes are `0` and
`2`, both nonnegative and straddling one, and its graph is strongly connected, so an eigenvector
exists; but the eigenvalue is free above the threshold `5` at which the reset and the doubling
balance, and constrained below it.  So at nonnegative slopes the eigenvalue is **not** determined
by the labelling, and the set of eigenvalues is neither a point, as in the translation regime,
nor all of `ℝ`, as below unit slope modulus. -/
theorem eigenvalues_loopLabel : eigenvalues loopGraph loopLabel = Set.Ici 5 := by
  ext lam
  rw [mem_eigenvalues_iff, Set.mem_Ici]
  constructor
  · rintro ⟨x, hx⟩
    rw [isEigenvector_loopLabel_iff] at hx
    rcases max_cases (10 : ℝ) (2 * x ()) with ⟨hvalue, hle⟩ | ⟨hvalue, hlt⟩ <;>
      rw [hvalue] at hx <;> linarith
  · intro hlam
    refine ⟨fun _ => lam, ?_⟩
    rw [isEigenvector_loopLabel_iff]
    rw [max_eq_right (by linarith : (10 : ℝ) ≤ 2 * lam)]
    ring

/-- **At every eigenvalue the two-loop labelling has exactly two eigenvectors**, one on each
branch of the maximum: the doubling is tight at `lam` and the reset at `10 - lam`.  At the
threshold `lam = 5` the two coincide, which is why the statement holds there as well and the
eigenvector set of that labelling is described with no gap. -/
theorem isEigenvector_loopLabel_iff_of_le {lam : ℝ} (hlam : 5 ≤ lam) (x : Unit → ℝ) :
    IsEigenvector loopGraph loopLabel lam x ↔ x () = lam ∨ x () = 10 - lam := by
  rw [isEigenvector_loopLabel_iff]
  constructor
  · intro hx
    rcases max_cases (10 : ℝ) (2 * x ()) with ⟨hvalue, hle⟩ | ⟨hvalue, hlt⟩ <;>
      rw [hvalue] at hx
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · rintro (hx | hx)
    · rw [hx, max_eq_right (by linarith : (10 : ℝ) ≤ 2 * lam)]
      ring
    · rw [hx, max_eq_left (by linarith : 2 * (10 - lam) ≤ (10 : ℝ))]
      ring

/-- **The eigenvector is not unique either.**  Above the threshold the two branches of the
maximum give two distinct eigenvectors of the same eigenvalue.  On one vertex this refutes
uniqueness of the eigenvector as a function and not uniqueness up to an additive constant, which
is vacuous there; what is refuted up to an additive constant is instead
`Maths.MaxAffineTransport.eq_zero_of_isEigenvector_add_const_of_slope_eq`, and only
at a common slope. -/
theorem exists_pair_ne_isEigenvector_loopLabel {lam : ℝ} (hlam : 5 < lam) :
    ∃ x y : Unit → ℝ, IsEigenvector loopGraph loopLabel lam x ∧
      IsEigenvector loopGraph loopLabel lam y ∧ x ≠ y := by
  refine ⟨fun _ => lam, fun _ => 10 - lam,
    (isEigenvector_loopLabel_iff_of_le hlam.le _).2 (Or.inl rfl),
    (isEigenvector_loopLabel_iff_of_le hlam.le _).2 (Or.inr rfl), fun hcon => ?_⟩
  have hvalue : lam = 10 - lam := congrFun hcon ()
  linarith

/-- **The relaxation levels of the two-loop labelling are its eigenvalues.**  Both are the
half-line above `5`, so for this labelling the least relaxation level is attained as an
eigenvalue. -/
theorem relaxationLevels_loopLabel : relaxationLevels loopGraph loopLabel = Set.Ici 5 := by
  ext lam
  rw [mem_relaxationLevels_iff]
  simp only [Set.mem_Ici]
  constructor
  · rintro ⟨x, hx⟩
    have hreset := hx false
    have hdouble := hx true
    simp only [loopGraph, loopLabel_false, loopLabel_true, apply_resetLabel,
      apply_doubleLabel] at hreset hdouble
    linarith
  · intro hlam
    refine ⟨fun _ => 5, fun e => ?_⟩
    cases e <;> simp only [loopLabel_false, loopLabel_true, apply_resetLabel,
      apply_doubleLabel] <;> linarith

/-- No loop of `Maths.MaxAffineTransport.loopGraph` has unit slope: the reset has
slope `0` and the doubling slope `2`. -/
instance isEmpty_unitSlopeEdge_loopLabel : IsEmpty (UnitSlopeEdge loopLabel) where
  false edge := by
    obtain ⟨e, he⟩ := edge
    cases e <;> norm_num at he

/-- The unit-slope subgraph of the two-loop labelling carries no closed walk but the empty one,
so its cycle bound holds at every level. -/
theorem unitSlopeCycles_loopLabel_le (lam : ℝ) (base : Unit)
    (cycle : (unitSlopeGraph loopGraph loopLabel).Walk base base) :
    MaxPlusPotential.walkWeight (unitSlopeShift loopLabel) cycle ≤ cycle.length * lam := by
  cases cycle with
  | nil => simp
  | concat _ edge _ => exact (isEmpty_unitSlopeEdge_loopLabel.false edge).elim

/-- **The unit-slope cycle bound is not the right formula at mixed slopes.**  For the two-loop
labelling the unit-slope subgraph is empty, so the bound of
`Maths.MaxAffineTransport.mem_relaxationLevels_iff_unitSlopeCycles_of_slope_le_one`
holds at every level, while the level `0` is infeasible -- indeed every level below `5` is.  So
neither that criterion nor its superunit twin survives the removal of its slope hypothesis, and
no maximum cycle mean of unit-slope edges can be the eigenvalue at nonnegative slopes straddling
one. -/
theorem not_forall_mem_relaxationLevels_iff_unitSlopeCycles_le :
    ¬∀ (V E : Type) (_ : Fintype V) (_ : DecidableEq V) (_ : Fintype E) (G : EdgeGraph V E)
        (label : E → Label) (lam : ℝ),
      (∀ e : E, 0 ≤ (label e).slope) →
      (lam ∈ relaxationLevels G label ↔
        ∀ (base : V) (cycle : (unitSlopeGraph G label).Walk base base),
          MaxPlusPotential.walkWeight (unitSlopeShift label) cycle ≤ cycle.length * lam) := by
  intro hrule
  have hmem : (0 : ℝ) ∈ relaxationLevels loopGraph loopLabel :=
    (hrule Unit Bool inferInstance inferInstance inferInstance loopGraph loopLabel 0
      slope_loopLabel_nonneg).2 (unitSlopeCycles_loopLabel_le 0)
  rw [relaxationLevels_loopLabel] at hmem
  exact absurd (Set.mem_Ici.1 hmem) (by norm_num)

end TwoLoops

end MaxAffineTransport

end

end Maths
