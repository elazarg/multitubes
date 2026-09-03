/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Basic
public import Mathlib.Order.FixedPoints

/-!
# A minimal least/greatest alternation

A binary monotone system has one update for each of two complete lattices. Solving the second
equation by a greatest fixed point at each value of the first produces a monotone outer update,
whose least fixed point gives a simultaneous solution. Reversing the nesting order, while keeping
the first variable least and the second greatest, gives another simultaneous solution.

For the mutual-copy equations `x := y` and `y := x`, the least-outside/greatest-inside nesting
selects `(⊥, ⊥)`, while the opposite nesting selects `(⊤, ⊤)`. Both are exact sections of the same
two-edge identity transport. On a nontrivial lattice they differ. Hence the local equation graph,
even with every edge marked exact, does not contain the priority information of an alternating
fixed-point semantics.

## Main definitions

* `GamesModelChecking.BinaryMonotoneSystem` - two jointly monotone update maps.
* `GamesModelChecking.BinaryMonotoneSystem.leastGreatestSolution` - the `μ`-outside, `ν`-inside
  solution.
* `GamesModelChecking.BinaryMonotoneSystem.greatestLeastSolution` - the `ν`-outside, `μ`-inside
  solution.
* `GamesModelChecking.copySystem` - the mutual-copy equations.
* `GamesModelChecking.copyGraph` and `GamesModelChecking.copyTransport` - their exact local graph.

## Main results

* `GamesModelChecking.BinaryMonotoneSystem.isFixedPoint_leastGreatestSolution` - the first nesting
  solves both equations.
* `GamesModelChecking.BinaryMonotoneSystem.isFixedPoint_greatestLeastSolution` - the opposite
  nesting solves both equations.
* `GamesModelChecking.leastGreatestSolution_copySystem` and
  `GamesModelChecking.greatestLeastSolution_copySystem` - the two solutions are the bottom and top
  diagonal pairs.
* `GamesModelChecking.copyFixedPoint_iff_isSection` - simultaneous copy fixed points are exact
  sections.
* `GamesModelChecking.priority_data_not_determined_by_local_sections` - the two nesting orders
  select distinct sections of the same local system.

## Tags

fixed point, alternation, priority, parity, model checking, exact section
-/

@[expose] public section

namespace GamesModelChecking

open Maths

universe uX uY uL

variable {X : Type uX} {Y : Type uY}

/-- A two-variable monotone equation system, curried so monotonicity is explicit in each
coordinate. -/
structure BinaryMonotoneSystem (X : Type uX) (Y : Type uY)
    [Preorder X] [Preorder Y] where
  /-- The update of the first coordinate. -/
  left : X →o Y →o X
  /-- The update of the second coordinate. -/
  right : X →o Y →o Y

namespace BinaryMonotoneSystem

variable [CompleteLattice X] [CompleteLattice Y]
variable (system : BinaryMonotoneSystem X Y)

/-- The second coordinate selected as a greatest fixed point for each first coordinate. -/
def innerGreatest : X →o Y :=
  OrderHom.gfp.comp system.right

/-- The first-coordinate update after solving the second coordinate by a greatest fixed point. -/
def outerAfterGreatest : X →o X where
  toFun x := system.left x (system.innerGreatest x)
  monotone' := by
    intro first second hle
    exact ((system.left.mono hle) (system.innerGreatest first)).trans
      ((system.left second).mono (system.innerGreatest.mono hle))

/-- Solve the first coordinate least and, inside it, the second coordinate greatest. -/
def leastGreatestSolution : X × Y :=
  let first := system.outerAfterGreatest.lfp
  (first, system.innerGreatest first)

/-- The first-coordinate update with the second coordinate held fixed. -/
def leftAt : Y →o X →o X where
  toFun second :=
    { toFun := fun first ↦ system.left first second
      monotone' := fun _first _second hle ↦ (system.left.mono hle) second }
  monotone' := fun _first _second hle first ↦ (system.left first).mono hle

/-- The first coordinate selected least for each fixed second coordinate. -/
def innerLeftLeast : Y →o X :=
  OrderHom.lfp.comp system.leftAt

/-- The second-coordinate update after solving the first coordinate least. -/
def outerAfterLeftLeast : Y →o Y where
  toFun second := system.right (system.innerLeftLeast second) second
  monotone' := by
    intro first second hle
    exact ((system.right.mono (system.innerLeftLeast.mono hle)) first).trans
      ((system.right (system.innerLeftLeast second)).mono hle)

/-- Solve the second coordinate greatest and, inside it, the first coordinate least. -/
def greatestLeastSolution : X × Y :=
  let second := system.outerAfterLeftLeast.gfp
  (system.innerLeftLeast second, second)

/-- A pair satisfying both local equations of a binary monotone system. -/
def IsFixedPoint (value : X × Y) : Prop :=
  system.left value.1 value.2 = value.1 ∧ system.right value.1 value.2 = value.2

/-- The least-outside, greatest-inside nesting satisfies both local equations. -/
theorem isFixedPoint_leastGreatestSolution :
    system.IsFixedPoint system.leastGreatestSolution := by
  constructor
  · exact system.outerAfterGreatest.map_lfp
  · exact (system.right system.outerAfterGreatest.lfp).map_gfp

/-- The greatest-outside, least-inside nesting satisfies both local equations. -/
theorem isFixedPoint_greatestLeastSolution :
    system.IsFixedPoint system.greatestLeastSolution := by
  constructor
  · exact (system.leftAt system.outerAfterLeftLeast.gfp).map_lfp
  · exact system.outerAfterLeftLeast.map_gfp

end BinaryMonotoneSystem

/-! ## The mutual-copy system -/

variable {L : Type uL} [CompleteLattice L]

/-- The system of equations `x := y` and `y := x`. -/
def copySystem : BinaryMonotoneSystem L L where
  left :=
    { toFun := fun _first ↦ OrderHom.id
      monotone' := fun _first _second _hle _value ↦ le_rfl }
  right :=
    { toFun := fun first ↦ OrderHom.const L first
      monotone' := fun _first _second hle _value ↦ hle }

/-- The greatest fixed point of a constant endomap is its constant value. -/
theorem gfp_const (value : L) : (OrderHom.const L value).gfp = value := by
  apply le_antisymm
  · exact OrderHom.gfp_le _ fun _candidate hcandidate ↦ hcandidate
  · exact OrderHom.le_gfp _ le_rfl

/-- The least fixed point of a constant endomap is its constant value. -/
theorem lfp_const (value : L) : (OrderHom.const L value).lfp = value := by
  apply le_antisymm
  · exact OrderHom.lfp_le _ le_rfl
  · exact OrderHom.le_lfp _ fun _candidate hcandidate ↦ hcandidate

/-- The least fixed point of the identity is bottom. -/
theorem lfp_id : (OrderHom.id : L →o L).lfp = ⊥ := by
  apply le_antisymm
  · exact OrderHom.lfp_le _ le_rfl
  · exact bot_le

/-- The greatest fixed point of the identity is top. -/
theorem gfp_id : (OrderHom.id : L →o L).gfp = ⊤ := by
  apply le_antisymm
  · exact le_top
  · exact OrderHom.le_gfp _ le_rfl

/-- The inner greatest fixed point of the copy system returns its first coordinate. -/
theorem innerGreatest_copySystem (value : L) :
    (copySystem : BinaryMonotoneSystem L L).innerGreatest value = value :=
  gfp_const value

/-- Solving the first copy equation least with the second coordinate fixed returns that second
coordinate. -/
theorem innerLeftLeast_copySystem (value : L) :
    (copySystem : BinaryMonotoneSystem L L).innerLeftLeast value = value :=
  lfp_const value

/-- The least-outside, greatest-inside copy solution is the bottom diagonal pair. -/
theorem leastGreatestSolution_copySystem :
    (copySystem : BinaryMonotoneSystem L L).leastGreatestSolution = (⊥, ⊥) := by
  rw [BinaryMonotoneSystem.leastGreatestSolution]
  have houter :
      (copySystem : BinaryMonotoneSystem L L).outerAfterGreatest = OrderHom.id := by
    ext value
    exact innerGreatest_copySystem value
  rw [houter, lfp_id, innerGreatest_copySystem]

/-- The greatest-outside, least-inside copy solution is the top diagonal pair. -/
theorem greatestLeastSolution_copySystem :
    (copySystem : BinaryMonotoneSystem L L).greatestLeastSolution = (⊤, ⊤) := by
  rw [BinaryMonotoneSystem.greatestLeastSolution]
  have houter :
      (copySystem : BinaryMonotoneSystem L L).outerAfterLeftLeast = OrderHom.id := by
    ext value
    exact innerLeftLeast_copySystem value
  rw [houter, gfp_id, innerLeftLeast_copySystem]

/-! ## The local exact graph -/

/-- Two vertices with one edge in each direction. -/
def copyGraph : EdgeGraph Bool Bool where
  source
    | false => false
    | true => true
  target
    | false => true
    | true => false

/-- Identity transport on both edges of the copy graph. -/
def copyTransport : Transport copyGraph (fun _vertex ↦ L) where
  edgeMap _edge := id

/-- Regard a pair as a family on the two vertices of the copy graph. -/
def pairFamily (value : L × L) : Bool → L
  | false => value.1
  | true => value.2

/-- The two local copy equations are exactly the section equations of the identity transport. -/
theorem copyFixedPoint_iff_isSection (value : L × L) :
    (copySystem : BinaryMonotoneSystem L L).IsFixedPoint value ↔
      (copyTransport : Transport copyGraph (fun _vertex ↦ L)).IsSection (pairFamily value) := by
  constructor
  · rintro ⟨hleft, hright⟩ edge
    change value.2 = value.1 at hleft
    change value.1 = value.2 at hright
    cases edge with
    | false => exact hleft.symm
    | true => exact hright.symm
  · intro hsection
    have hforward := hsection false
    have hbackward := hsection true
    change value.1 = value.2 at hforward
    change value.2 = value.1 at hbackward
    constructor
    · exact hforward.symm
    · exact hbackward.symm

/-- Opposite nesting orders select distinct exact sections of the same local equation graph on
every nontrivial complete lattice. -/
theorem priority_data_not_determined_by_local_sections [Nontrivial L] :
    let leastGreatest := (copySystem : BinaryMonotoneSystem L L).leastGreatestSolution
    let greatestLeast := (copySystem : BinaryMonotoneSystem L L).greatestLeastSolution
    (copyTransport : Transport copyGraph (fun _vertex ↦ L)).IsSection
        (pairFamily leastGreatest) ∧
      (copyTransport : Transport copyGraph (fun _vertex ↦ L)).IsSection
        (pairFamily greatestLeast) ∧
      pairFamily leastGreatest ≠ pairFamily greatestLeast := by
  dsimp only
  rw [leastGreatestSolution_copySystem, greatestLeastSolution_copySystem]
  constructor
  · intro edge
    cases edge <;> rfl
  constructor
  · intro edge
    cases edge <;> rfl
  · intro heq
    have hvalue := congrFun heq false
    exact bot_ne_top hvalue

end GamesModelChecking
