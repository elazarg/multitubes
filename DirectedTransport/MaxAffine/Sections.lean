/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DirectedTransport.Additive.Potentials
public import DirectedTransport.MaxAffine.Basic
public import Mathlib.Order.WithBot

import Mathlib.Data.Fintype.Order

/-!
# Existence of lax sections for max-affine transport graphs

`DirectedTransport.MaxAffineTransport` develops the obstruction side of max-affine
transport: at nonnegative slopes, a lax section forces the composite action of
every closed walk to have a pre-fixed point
(`DirectedTransport.MaxAffineTransport.holonomyApply_cycle_le`; without the slope
hypothesis this fails -- two labels of slope `-1` can each admit a lax value
while their composite is a positive translation).  This file supplies the
converse in two regimes.

**The subunit-slope regime.**  When every slope is strictly below one and the
edges are finitely many, a *constant* candidate already closes: a constant at
least every finite floor and every affine fixed point `shift / (1 - slope)`
satisfies the edge inequality outright, with no iteration and no structure on
the vertices.  Negative slopes are admitted, so this is wider than the
discounted, or `β`-contractive, case `0 ≤ slope < 1`; the wider class is
neither monotone nor a metric contraction in general, and the constant
witness needs neither.

**The slope-one regime.**  When every slope equals one the labels are
translations corrected by floors, and a lax section exists exactly when no
closed walk has strictly positive shift sum.  This is the mean-payoff
feasibility criterion, equivalently the Bellman--Ford criterion, lifted from
translations to floored labels.  The lift is by a constant: the translation
inequalities are unchanged by adding a constant, and the floor inequalities
only improve upward, so a potential for the shifts, raised until every floor
clears, is a lax section.  In the timed-event-graph reading of max-plus discrete-event
theory a floor is a release date, and the usual device is an anchor or
slack vertex pinned to zero and joined to every floored edge; adding a constant
achieves the same reduction without enlarging the graph.

## Main results

* `DirectedTransport.MaxAffineTransport.Label.apply_const_le` -- the edgewise subunit-slope
  estimate: below unit slope, a constant above the floor and above the affine
  fixed point is a pre-fixed point.
* `DirectedTransport.MaxAffineTransport.exists_const_isLaxSection_of_slope_lt_one` -- with
  finitely many edges and all slopes below one, a constant lax section exists.
* `DirectedTransport.MaxAffineTransport.exists_isLaxSection_iff_forall_cycle_shift_nonpos` --
  at unit slopes, a lax section exists exactly when every closed walk has
  nonpositive shift sum.
* `DirectedTransport.MaxAffineTransport.exists_isLaxSection_iff_forall_cycle_exists_prefixed`
  -- the same criterion read through the composite label of each closed walk,
  matching `DirectedTransport.MaxAffineTransport.Label.exists_apply_le_self_iff`.

## TODO

Mixed slopes are not addressed here.  `DirectedTransport.MaxAffine.Farkas`
settles them by a linear rather than a cyclewise test, and shows the cyclewise
test of this file is not sufficient once slopes straddle one.  The fixed-point
reading of a lax section, and the eigenvalue problem in the topical regime of
unit-slope floorless labels, are settled in
`DirectedTransport.MaxAffine.FixedPoint`.  Mixed slopes below unit modulus are
settled metrically in `DirectedTransport.MaxAffine.Contraction`, which also
exhibits a strongly connected labelling with a negative slope and no
eigenvector.  What remains open is the eigenvalue problem for nonnegative
slopes straddling one, where the vertex operator is monotone but neither
additively homogeneous nor contracting, so neither the Perron--Frobenius theory
of topical maps nor Banach's theorem applies.

## References

* F. Baccelli, G. Cohen, G. J. Olsder and J.-P. Quadrat, *Synchronization and
  Linearity*, Wiley (1992), for timed event graphs and release dates.
* S. Gaubert and J. Gunawardena, *The Perron--Frobenius theorem for homogeneous,
  monotone functions*, Trans. Amer. Math. Soc. 356 (2004), 4931-4950, for the
  Perron--Frobenius theory of topical maps.

## Tags

lax section, max-affine, contraction, mean payoff, Bellman-Ford, max-plus
-/

@[expose] public section

noncomputable section

namespace DirectedTransport.MaxAffineTransport

namespace Label

/-! ## Edgewise estimates -/

/-- At unit slope the action dominates the translation by the shift. -/
theorem add_shift_le_apply {f : Label} (hslope : f.slope = 1) (x : ℝ) :
    x + f.shift ≤ f.apply x := by
  refine le_trans (le_of_eq ?_) (f.affinePart_le_apply x)
  simp only [affinePart, hslope, one_mul]
  ring

/-- **The edgewise subunit-slope estimate.**  Below unit slope, any constant at
least the floor and at least the fixed point `shift / (1 - slope)` of the affine
branch is a pre-fixed point of the action.  This is the witness constructed in
the first branch of `DirectedTransport.MaxAffineTransport.Label.exists_apply_le_self_iff`,
stated for an arbitrary admissible constant so that one constant can serve every
edge of a graph. -/
theorem apply_const_le {f : Label} (hslope : f.slope < 1) {C : ℝ}
    (hfloor : f.floor ≤ (C : WithBot ℝ)) (hfix : f.shift / (1 - f.slope) ≤ C) :
    f.apply C ≤ C := by
  rw [apply_le_target_iff]
  refine ⟨hfloor, ?_⟩
  have hpos : 0 < 1 - f.slope := by linarith
  have hmul : f.shift ≤ C * (1 - f.slope) := (div_le_iff₀ hpos).mp hfix
  simp only [affinePart]
  nlinarith

/-! ## Unit-slope composite labels -/

theorem slope_foldl_comp : ∀ (l : List Label), (∀ f ∈ l, f.slope = 1) → ∀ acc : Label,
    (l.foldl (fun a f => f.comp a) acc).slope = acc.slope
  | [], _, _ => rfl
  | f :: rest, hslope, acc => by
      have hrest (g : Label) (hg : g ∈ rest) : g.slope = 1 :=
        hslope g (List.mem_cons_of_mem _ hg)
      have hf : f.slope = 1 := hslope f (List.mem_cons_self ..)
      rw [List.foldl_cons, slope_foldl_comp rest hrest (f.comp acc), slope_comp, hf, one_mul]

theorem shift_foldl_comp : ∀ (l : List Label), (∀ f ∈ l, f.slope = 1) → ∀ acc : Label,
    (l.foldl (fun a f => f.comp a) acc).shift = acc.shift + (l.map Label.shift).sum
  | [], _, acc => by simp
  | f :: rest, hslope, acc => by
      have hrest (g : Label) (hg : g ∈ rest) : g.slope = 1 :=
        hslope g (List.mem_cons_of_mem _ hg)
      have hf : f.slope = 1 := hslope f (List.mem_cons_self ..)
      rw [List.foldl_cons, shift_foldl_comp rest hrest (f.comp acc)]
      simp only [shift_comp, hf, one_mul, List.map_cons, List.sum_cons]
      ring

/-- A composite of unit-slope labels has unit slope. -/
theorem slope_compList {l : List Label} (hslope : ∀ f ∈ l, f.slope = 1) :
    (compList l).slope = 1 := by
  rw [compList, slope_foldl_comp l hslope Label.id, slope_id]

/-- A composite of unit-slope labels shifts by the sum of the shifts. -/
theorem shift_compList {l : List Label} (hslope : ∀ f ∈ l, f.slope = 1) :
    (compList l).shift = (l.map Label.shift).sum := by
  rw [compList, shift_foldl_comp l hslope Label.id, shift_id, zero_add]

/-- **A composite of unit-slope labels has a pre-fixed point exactly when its
shift sum is nonpositive.**  This is the unit-slope branch of
`DirectedTransport.MaxAffineTransport.Label.exists_apply_le_self_iff`; the floors, however
large, obstruct nothing, since a pre-fixed point may be taken above them. -/
theorem exists_apply_compList_le_self_iff {l : List Label} (hslope : ∀ f ∈ l, f.slope = 1) :
    (∃ x : ℝ, (compList l).apply x ≤ x) ↔ (l.map Label.shift).sum ≤ 0 := by
  rw [exists_apply_le_self_iff, slope_compList hslope, shift_compList hslope]
  constructor
  · rintro (hlt | ⟨_, hshift⟩ | ⟨hgt, _⟩)
    · exact absurd hlt (lt_irrefl 1)
    · exact hshift
    · exact absurd hgt (lt_irrefl 1)
  · intro hshift
    exact Or.inr (Or.inl ⟨rfl, hshift⟩)

end Label

/-! ## Existence of lax sections -/

section Graph

universe uV uE

variable {V : Type uV} {E : Type uE} {G : DirectedTransport.EdgeGraph V E}

/-! ### The subunit-slope regime -/

/-- **Subunit-slope existence, with a constant witness.**  If the edges are
finitely many and every slope is strictly below one, then some constant
candidate is a lax section: it suffices that the constant clear every floor and
every affine fixed point `shift / (1 - slope)`, and finitely many edges impose
finitely many such demands.  The vertices need not be finitely many, and no
iteration of the vertex operator is involved.  At nonnegative slopes this is
the discounted, or `β`-contractive, case; negative slopes are also
admitted. -/
theorem exists_const_isLaxSection_of_slope_lt_one [Finite E] {label : E → Label}
    (hslope : ∀ e : E, (label e).slope < 1) :
    ∃ C : ℝ, IsLaxSection G label (fun _ => C) := by
  obtain ⟨bound, hbound⟩ := Finite.exists_le fun e : E =>
    max ((label e).floor.unbotD 0) ((label e).shift / (1 - (label e).slope))
  refine ⟨bound, fun e => ?_⟩
  have hfloor : (label e).floor ≤ ((bound : ℝ) : WithBot ℝ) :=
    (Label.le_coe_unbotD _ 0).trans
      (WithBot.coe_le_coe.mpr ((le_max_left _ _).trans (hbound e)))
  have hfix : (label e).shift / (1 - (label e).slope) ≤ bound :=
    (le_max_right _ _).trans (hbound e)
  exact Label.apply_const_le (hslope e) hfloor hfix

/-- **Subunit-slope existence.**  Finitely many edges and slopes strictly below
one force a lax section to exist; the witness of
`exists_const_isLaxSection_of_slope_lt_one` is constant. -/
theorem exists_isLaxSection_of_slope_lt_one [Finite E] {label : E → Label}
    (hslope : ∀ e : E, (label e).slope < 1) : ∃ φ : V → ℝ, IsLaxSection G label φ := by
  obtain ⟨C, hC⟩ := exists_const_isLaxSection_of_slope_lt_one (G := G) hslope
  exact ⟨fun _ => C, hC⟩

/-! ### The unit-slope regime -/

/-- At unit slopes a lax section is in particular a potential for the shifts:
the floors only raise the action, so the translation inequality is implied. -/
theorem isPotential_of_isLaxSection {label : E → Label} (hslope : ∀ e : E, (label e).slope = 1)
    {φ : V → ℝ} (hφ : IsLaxSection G label φ) :
    DirectedTransport.MaxPlusPotential.IsPotential G (fun e => (label e).shift) φ := fun e =>
  (Label.add_shift_le_apply (hslope e) (φ (G.source e))).trans (hφ e)

/-- A potential for the shifts that clears every floor at the head of its edge
is a lax section, at unit slopes. -/
theorem isLaxSection_of_isPotential {label : E → Label} (hslope : ∀ e : E, (label e).slope = 1)
    {φ : V → ℝ} (hφ : DirectedTransport.MaxPlusPotential.IsPotential G (fun e => (label e).shift) φ)
    (hfloor : ∀ e : E, (label e).floor ≤ ((φ (G.target e) : ℝ) : WithBot ℝ)) :
    IsLaxSection G label φ := by
  intro e
  refine (Label.apply_le_target_iff _ _ _).2 ⟨hfloor e, ?_⟩
  have hpot := hφ e
  simp only [Label.affinePart, hslope e, one_mul]
  linarith

/-- **Strong duality at unit slopes.**  Over finitely many edges, all slopes
being one, a lax section exists exactly when no closed walk has strictly
positive shift sum.  This is the mean-payoff feasibility criterion,
equivalently the Bellman--Ford criterion, lifted from the translations of
`DirectedTransport.MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos` to
floored labels.  The translation inequalities are unchanged by adding a
constant and the floor inequalities only improve upward, and that is what
carries the lift: a potential for the shifts, raised by a constant large
enough for every floor, is a lax section.  Adjoining a
vertex pinned to zero and an edge from it to the head of each floored edge is
the same reduction performed on an enlarged graph. -/
theorem exists_isLaxSection_iff_forall_cycle_shift_nonpos [Finite E]
    {label : E → Label} (hslope : ∀ e : E, (label e).slope = 1) :
    (∃ φ : V → ℝ, IsLaxSection G label φ) ↔
      ∀ (base : V) (cycle : G.Walk base base),
        DirectedTransport.MaxPlusPotential.walkWeight (fun e => (label e).shift) cycle ≤ 0 := by
  constructor
  · rintro ⟨φ, hφ⟩ base cycle
    exact (isPotential_of_isLaxSection hslope hφ).closedWalk_nonpos cycle
  · intro hcycle
    obtain ⟨base, hbase⟩ :=
      (DirectedTransport.MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos
        (G := G) fun e => (label e).shift).2 hcycle
    obtain ⟨lift, hlift⟩ :=
      Finite.exists_le fun e : E => (label e).floor.unbotD 0 - base (G.target e)
    refine ⟨fun v => base v + lift, isLaxSection_of_isPotential hslope (fun e => ?_) fun e => ?_⟩
    · have := hbase e
      change base (G.source e) + lift + (label e).shift ≤ base (G.target e) + lift
      linarith
    · refine (Label.le_coe_unbotD _ 0).trans (WithBot.coe_le_coe.mpr ?_)
      have := hlift e
      change (label e).floor.unbotD 0 ≤ base (G.target e) + lift
      linarith

/-- The shift of the composite label of a walk is the walk's shift sum. -/
theorem shift_compList_edges {label : E → Label} (hslope : ∀ e : E, (label e).slope = 1)
    {start finish : V} (walk : G.Walk start finish) :
    (Label.compList (walk.edges.map label)).shift
      = DirectedTransport.MaxPlusPotential.walkWeight (fun e => (label e).shift) walk := by
  rw [Label.shift_compList (fun f hf => ?_)]
  · rw [DirectedTransport.MaxPlusPotential.walkWeight, List.map_map]
    rfl
  · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hf
    exact hslope e

/-- **Strong duality at unit slopes, read through composite labels.**  A lax
section exists exactly when the composite label of every closed walk admits a
pre-fixed point, the condition that
`DirectedTransport.MaxAffineTransport.Label.exists_apply_le_self_iff` decides from the
coefficients.  Together with
`DirectedTransport.MaxAffineTransport.holonomyApply_cycle_le` this closes the unit-slope case
of the duality: the necessary condition of weak duality is sufficient.  The
composite is the one that acts by transport,
`DirectedTransport.MaxAffineTransport.apply_compList_edges`. -/
theorem exists_isLaxSection_iff_forall_cycle_exists_prefixed [Finite E]
    {label : E → Label} (hslope : ∀ e : E, (label e).slope = 1) :
    (∃ φ : V → ℝ, IsLaxSection G label φ) ↔
      ∀ (base : V) (cycle : G.Walk base base),
        ∃ x : ℝ, (Label.compList (cycle.edges.map label)).apply x ≤ x := by
  rw [exists_isLaxSection_iff_forall_cycle_shift_nonpos hslope]
  refine forall_congr' fun base => forall_congr' fun cycle => ?_
  have hall (f : Label) (hf : f ∈ cycle.edges.map label) : f.slope = 1 := by
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hf
    exact hslope e
  rw [Label.exists_apply_compList_le_self_iff hall, ← Label.shift_compList hall,
    shift_compList_edges hslope]

end Graph

end DirectedTransport.MaxAffineTransport

end
