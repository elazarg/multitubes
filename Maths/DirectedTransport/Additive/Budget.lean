/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.Additive.Potentials
public import Maths.Graph.ChargedRelation

/-!
# Bounded potentials for a nonnegative weighting

`Maths.DirectedTransport.Additive.Potentials` characterizes the existence of a potential by the
absence of a closed walk of positive weight, and needs finitely many edges: the witness is a
maximum over the walks that repeat no edge, and without an edge bound there is no such maximum.
`Maths.Graph.ChargedRelation` proves a duality of a different shape for nonnegative charges -
a *bounded* potential exists exactly when the path charges are bounded above - and needs no
finiteness at all: its witness is a supremum, not a maximum.

This file is the bridge.  A digraph with a nonnegative weighting is a charged relation whose
source and target are exchanged, and with that orientation the two potential inequalities are
literally the same one: a charged potential drops by at least the charge across an edge read
backwards, which is to say it rises by at least the weight across the edge read forwards.  Finite
walks and admissible paths correspond, reversed and with equal charge, so the path charges of the
relation are exactly the walk weights of the graph.

What the transported duality says is therefore: for a nonnegative weighting on an **arbitrary**
digraph, with no hypothesis on the vertex or edge type, a potential with bounded range exists
exactly when the walk weights are bounded above; and the least oscillation of such a potential is
their supremum.  Boundedness of the potential is what replaces finiteness of the edge type.  The
two statements are not comparable: at a nonnegative weighting every nonempty closed walk already
has nonnegative weight, so the closed-walk criterion of the potential file degenerates to
demanding weight zero around every cycle, while the criterion here is a genuine boundedness
condition on the open walks.

## Main definitions

* `Maths.MaxPlusPotential.chargedRelation`: a digraph with a nonnegative weighting, read as
  a charged relation with source and target exchanged.
* `Maths.MaxPlusPotential.toChargedPath` and
  `Maths.MaxPlusPotential.ofChargedPath`: the reversal identifying finite walks with
  admissible paths.
* `Maths.MaxPlusPotential.walkWeights`: the set of weights of the finite walks.

## Main results

* `Maths.MaxPlusPotential.pathCharges_chargedRelation`: the path charges of the relation
  are the walk weights of the graph.
* `Maths.MaxPlusPotential.exists_bounded_isPotential_iff_bddAbove_walkWeights`: **the
  bridge** - for a nonnegative weighting on an arbitrary digraph, a potential of bounded range
  exists exactly when the walk weights are bounded above.
* `Maths.MaxPlusPotential.isLeast_oscillation_of_bddAbove_walkWeights`: the sharp form -
  the supremum of the walk weights is the least oscillation of such a potential, and it is
  attained.

## Tags

potential, budget, oscillation, duality, max-plus
-/

@[expose] public section

namespace Maths

namespace MaxPlusPotential

open ChargedPathBudget

universe uV uE

variable {V : Type uV} {E : Type uE}

/-! ## The charged relation of a nonnegative weighting -/

/-- A digraph with a nonnegative edge weighting, read as a charged relation with source and
target exchanged.  The exchange is what makes a charged potential of the relation the same thing
as an additive potential of the graph. -/
abbrev chargedRelation (G : EdgeGraph V E) (weight : E → ℝ)
    (hweight : ∀ edge : E, 0 ≤ weight edge) : ChargedRelation V E where
  src := G.target
  tgt := G.source
  charge := weight
  charge_nonneg := hweight

variable {G : EdgeGraph V E} {weight : E → ℝ} {hweight : ∀ edge : E, 0 ≤ weight edge}

/-- An additive potential of the graph is exactly a charged potential of the relation. -/
theorem isPotential_iff_chargedRelation_isPotential (potential : V → ℝ) :
    IsPotential G weight potential ↔
      (chargedRelation G weight hweight).IsPotential potential :=
  Iff.rfl

/-- A finite walk read backwards as an admissible path of the charged relation. -/
def toChargedPath (G : EdgeGraph V E) (weight : E → ℝ) (hweight : ∀ edge : E, 0 ≤ weight edge)
    {start : V} : {finish : V} → G.Walk start finish →
      (chargedRelation G weight hweight).Path finish start
  | _, .nil => .nil start
  | _, .concat walk edge legal =>
      (ChargedRelation.Path.edge edge rfl legal).append (toChargedPath G weight hweight walk)

@[simp] theorem chargeSum_toChargedPath {start finish : V} (walk : G.Walk start finish) :
    (toChargedPath G weight hweight walk).chargeSum = walkWeight weight walk := by
  induction walk with
  | nil => simp [toChargedPath]
  | concat walk edge legal ih => simp [toChargedPath, ih, add_comm]

/-- An admissible path of the charged relation read backwards as a finite walk. -/
def ofChargedPath (G : EdgeGraph V E) (weight : E → ℝ) (hweight : ∀ edge : E, 0 ≤ weight edge) :
    {first second : V} → (chargedRelation G weight hweight).Path first second →
      G.Walk second first
  | _, _, .nil _ => .nil
  | _, _, .cons edge rest => (ofChargedPath G weight hweight rest).concat edge rfl

@[simp] theorem walkWeight_ofChargedPath {first second : V}
    (path : (chargedRelation G weight hweight).Path first second) :
    walkWeight weight (ofChargedPath G weight hweight path) = path.chargeSum := by
  induction path with
  | nil => simp [ofChargedPath]
  | cons edge rest ih => simp [ofChargedPath, ih, add_comm]

/-! ## The two value sets agree -/

/-- The weights of the finite walks of a weighted digraph. -/
def walkWeights (G : EdgeGraph V E) (weight : E → ℝ) : Set ℝ :=
  {value | ∃ (start finish : V) (walk : G.Walk start finish), walkWeight weight walk = value}

theorem mem_walkWeights {start finish : V} (walk : G.Walk start finish) :
    walkWeight weight walk ∈ walkWeights G weight :=
  ⟨start, finish, walk, rfl⟩

/-- **The path charges of the charged relation are the walk weights of the graph.**  Reversal
carries the finite walks onto the admissible paths, preserving the accumulated value. -/
theorem pathCharges_chargedRelation :
    (chargedRelation G weight hweight).pathCharges = walkWeights G weight := by
  ext value
  constructor
  · rintro ⟨first, second, path, rfl⟩
    exact ⟨second, first, ofChargedPath G weight hweight path, walkWeight_ofChargedPath path⟩
  · rintro ⟨start, finish, walk, rfl⟩
    exact ⟨finish, start, toChargedPath G weight hweight walk, chargeSum_toChargedPath walk⟩

/-! ## The bridge -/

/-- **Bounded potentials for a nonnegative weighting.**  On an arbitrary digraph, with no
hypothesis on the vertex or the edge type, a potential whose range is bounded above and below
exists exactly when the weights of the finite walks are bounded above.  Boundedness of the
potential is what stands in for finiteness of the edge type in
`Maths.MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos`. -/
theorem exists_bounded_isPotential_iff_bddAbove_walkWeights
    (G : EdgeGraph V E) (weight : E → ℝ) (hweight : ∀ edge : E, 0 ≤ weight edge) :
    (∃ potential : V → ℝ, IsPotential G weight potential ∧
        BddAbove (Set.range potential) ∧ BddBelow (Set.range potential)) ↔
      BddAbove (walkWeights G weight) := by
  rw [← pathCharges_chargedRelation (hweight := hweight)]
  rw [show BddAbove (chargedRelation G weight hweight).pathCharges =
    (chargedRelation G weight hweight).HasFiniteBudget from rfl,
    ChargedRelation.hasFiniteBudget_iff_exists_boundedPotential]
  exact ⟨fun ⟨potential, hpotential, habove, hbelow⟩ =>
      ⟨potential, ⟨habove, hbelow, hpotential⟩⟩,
    fun ⟨potential, hpotential⟩ =>
      ⟨potential, hpotential.isPotential, hpotential.bddAbove, hpotential.bddBelow⟩⟩

/-- **The sharp form.**  When the walk weights are bounded above, their supremum is the least
oscillation of a potential of bounded range, and that least value is attained - by the
budget-to-go function of the charged relation, the greatest weight of a walk arriving at the
vertex. -/
theorem isLeast_oscillation_of_bddAbove_walkWeights
    (G : EdgeGraph V E) (weight : E → ℝ) (hweight : ∀ edge : E, 0 ≤ weight edge)
    (hbounded : BddAbove (walkWeights G weight)) :
    IsLeast {spread : ℝ | ∃ potential : V → ℝ, IsPotential G weight potential ∧
        BddAbove (Set.range potential) ∧ BddBelow (Set.range potential) ∧
        oscillation potential = spread}
      (sSup (walkWeights G weight)) := by
  have hbudget : (chargedRelation G weight hweight).HasFiniteBudget := by
    rw [show (chargedRelation G weight hweight).HasFiniteBudget =
      BddAbove (chargedRelation G weight hweight).pathCharges from rfl,
      pathCharges_chargedRelation]
    exact hbounded
  have hsup : (chargedRelation G weight hweight).budget = sSup (walkWeights G weight) := by
    rw [show (chargedRelation G weight hweight).budget =
      sSup (chargedRelation G weight hweight).pathCharges from rfl, pathCharges_chargedRelation]
  obtain ⟨hmem, hlower⟩ := (chargedRelation G weight hweight).isLeast_oscillation hbudget
  rw [hsup] at hmem hlower
  constructor
  · obtain ⟨potential, hpotential, hspread⟩ := hmem
    exact ⟨potential, hpotential.isPotential, hpotential.bddAbove, hpotential.bddBelow, hspread⟩
  · rintro spread ⟨potential, hpotential, habove, hbelow, rfl⟩
    exact hlower ⟨potential, ⟨habove, hbelow, hpotential⟩, rfl⟩

end MaxPlusPotential

end Maths
