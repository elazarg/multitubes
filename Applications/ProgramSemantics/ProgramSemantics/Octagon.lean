/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Additive.Potentials

import Mathlib.Tactic.Linarith
import Mathlib.Basic.Finite.Prod

/-!
# Octagon constraints by skew-symmetric doubling

The octagon abstract domain tracks unit two-variable inequalities `±x ± y ≤ c`.  Write a
*literal* as a variable with a sign, so that `(v, false)` denotes `x v` and `(v, true)` denotes
`-x v`.  Every octagon constraint reads `p - q ≤ c` for two literals `p` and `q`: this covers
`x - y ≤ c`, `x + y ≤ c` and `-x - y ≤ c`, and the unary bound `x ≤ c` is `x - (-x) ≤ 2c`.

The doubled graph has one vertex per literal.  A constraint `p - q ≤ c` contributes two edges of
weight `-c` in the convention `φ source + weight ≤ φ target` of
`Maths.MaxPlusPotential.IsPotential`: one from `p` to `q`, and one from `-q` to `-p`.  Literal
negation with edge reversal is an involution of this graph, so it is skew-symmetric.

Over a linearly ordered field, a constraint system is feasible exactly when the doubled graph
admits a potential (`ProgramSemantics.Octagon.feasible_iff_exists_isPotential`).  Feasible
values give the potential `φ (v, σ) = σ x v`; conversely a potential gives the values
`x v = (φ (v, false) - φ (v, true)) / 2`, and adding the two edge inequalities of a constraint
proves it.  By tropical Farkas duality the system is then feasible exactly when every closed walk
of the doubled graph has nonnegative total bound
(`ProgramSemantics.Octagon.feasible_iff_forall_closedWalk_nonneg`).

The proof divides by two, and nothing else separates the rational from the integer case.  Over
the integers the statement fails: `2x ≤ 1` and `-2x ≤ -1` admit an integer potential on the
doubled graph but no integer solution (`ProgramSemantics.Octagon.integer_gap`).  Integer octagon
feasibility needs a tightening of unary bounds that this file does not formalize.

The doubled graph is not the graph of elements of a sign gain: there both orientations of an
edge run in its own direction, while here the copy on negated literals runs backward.

## Main definitions

* `ProgramSemantics.Octagon.Constraint`: an octagon constraint `p - q ≤ c` on literals.
* `ProgramSemantics.Octagon.literal`: the value of a literal under an assignment.
* `ProgramSemantics.Octagon.Feasible`: an assignment satisfying every constraint exists.
* `ProgramSemantics.Octagon.doubledGraph`: the skew-symmetric doubled graph on literals.
* `ProgramSemantics.Octagon.doubledWeight`: the weight `-c` on both edges of a constraint.

## Main results

* `ProgramSemantics.Octagon.feasible_iff_exists_isPotential`: feasibility is the existence of a
  potential on the doubled graph.
* `ProgramSemantics.Octagon.feasible_iff_forall_closedWalk_nonneg`: feasibility is
  nonnegativity of the total bound around every closed walk of the doubled graph.
* `ProgramSemantics.Octagon.integer_gap`: the characterization fails over the integers.

## References

* A. Miné, *The octagon abstract domain*, Higher-Order and Symbolic Computation 19 (2006),
  31-100.
* S. K. Lahiri and M. Musuvathi, *An efficient decision procedure for UTVPI constraints*,
  FroCoS 2005.

## Tags

octagon, UTVPI, abstract interpretation, difference constraints, potential, Bellman-Ford
-/

@[expose] public section

namespace ProgramSemantics.Octagon

open Maths Maths.MaxPlusPotential

universe uV uI

variable {V : Type uV} {ι : Type uI}

/-- An octagon constraint `p - q ≤ bound` between two literals.  A literal `(v, false)` denotes
the variable `v` and `(v, true)` its negation. -/
structure Constraint (V : Type uV) (𝕜 : Type*) where
  /-- The literal entering positively. -/
  plus : V × Bool
  /-- The literal entering negatively. -/
  minus : V × Bool
  /-- The upper bound on the difference. -/
  bound : 𝕜

/-- The negated literal. -/
def negate (literal : V × Bool) : V × Bool :=
  (literal.1, !literal.2)

section Ring

variable {𝕜 : Type*} [Ring 𝕜]

/-- The value of a literal under an assignment of the variables. -/
def literal (value : V → 𝕜) : V × Bool → 𝕜
  | (vertex, false) => value vertex
  | (vertex, true) => -value vertex

/-- A literal and its negation take opposite values. -/
theorem literal_negate (value : V → 𝕜) (literal' : V × Bool) :
    literal value (negate literal') = -literal value literal' := by
  rcases literal' with ⟨vertex, _ | _⟩ <;> simp [negate, literal]

/-- An assignment satisfies a constraint. -/
def Constraint.Holds [LE 𝕜] (constraint : Constraint V 𝕜) (value : V → 𝕜) : Prop :=
  literal value constraint.plus - literal value constraint.minus ≤ constraint.bound

end Ring

/-- Some assignment satisfies every constraint of the family. -/
def Feasible {𝕜 : Type*} [Ring 𝕜] [LE 𝕜] (constraints : ι → Constraint V 𝕜) : Prop :=
  ∃ value : V → 𝕜, ∀ index, (constraints index).Holds value

/-- The doubled graph on literals: the forward edge of a constraint `p - q ≤ c` runs from `p` to
`q`, its mirror from `-q` to `-p`. -/
def doubledGraph {𝕜 : Type*} (constraints : ι → Constraint V 𝕜) : EdgeGraph (V × Bool) (ι × Bool)
    where
  source
    | (index, false) => (constraints index).plus
    | (index, true) => negate (constraints index).minus
  target
    | (index, false) => (constraints index).minus
    | (index, true) => negate (constraints index).plus

/-- Both edges of a constraint carry the negated bound. -/
def doubledWeight {𝕜 : Type*} [Neg 𝕜] (constraints : ι → Constraint V 𝕜) (edge : ι × Bool) :
    𝕜 :=
  -(constraints edge.1).bound

section Field

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The value of a literal recovered from a potential, by averaging it against its negation. -/
private theorem literal_halfDifference (φ : V × Bool → 𝕜) (literal' : V × Bool) :
    literal (fun vertex => (φ (vertex, false) - φ (vertex, true)) / 2) literal' =
      (φ literal' - φ (negate literal')) / 2 := by
  rcases literal' with ⟨vertex, _ | _⟩
  · rfl
  · simp only [literal, negate, Bool.not_true]
    ring

/-- **Doubling is exact over a field.**  An octagon system is feasible exactly when its doubled
graph admits a potential. -/
theorem feasible_iff_exists_isPotential (constraints : ι → Constraint V 𝕜) :
    Feasible constraints ↔
      ∃ φ : V × Bool → 𝕜, IsPotential (doubledGraph constraints) (doubledWeight constraints) φ := by
  constructor
  · rintro ⟨value, hholds⟩
    refine ⟨literal value, ?_⟩
    rintro ⟨index, _ | _⟩
    · have h := hholds index
      simp only [Constraint.Holds] at h
      change literal value (constraints index).plus + -(constraints index).bound ≤
        literal value (constraints index).minus
      linarith
    · have h := hholds index
      simp only [Constraint.Holds] at h
      change literal value (negate (constraints index).minus) + -(constraints index).bound ≤
        literal value (negate (constraints index).plus)
      rw [literal_negate, literal_negate]
      linarith
  · rintro ⟨φ, hφ⟩
    refine ⟨fun vertex => (φ (vertex, false) - φ (vertex, true)) / 2, fun index => ?_⟩
    have hforward : φ (constraints index).plus + -(constraints index).bound ≤
        φ (constraints index).minus := hφ (index, false)
    have hmirror : φ (negate (constraints index).minus) + -(constraints index).bound ≤
        φ (negate (constraints index).plus) := hφ (index, true)
    simp only [Constraint.Holds, literal_halfDifference]
    linarith

/-- **Cycle characterization.**  A finite octagon system is feasible exactly when the bounds
along every closed walk of its doubled graph have nonnegative sum. -/
theorem feasible_iff_forall_closedWalk_nonneg [Finite ι] (constraints : ι → Constraint V 𝕜) :
    Feasible constraints ↔
      ∀ (vertex : V × Bool) (cycle : (doubledGraph constraints).Walk vertex vertex),
        0 ≤ walkWeight (fun edge : ι × Bool => (constraints edge.1).bound) cycle := by
  rw [feasible_iff_exists_isPotential, exists_isPotential_iff_forall_closedWalk_nonpos]
  refine forall_congr' fun vertex => forall_congr' fun cycle => ?_
  rw [show doubledWeight constraints = fun edge => -(constraints edge.1).bound from rfl,
    walkWeight_neg, neg_nonpos]

end Field

/-- The system `2x ≤ 1`, `-2x ≤ -1` on one variable. -/
def halfSystem : Bool → Constraint Unit ℤ
  | false => ⟨((), false), ((), true), 1⟩
  | true => ⟨((), true), ((), false), -1⟩

/-- **The integer gap.**  The doubled graph of `2x ≤ 1`, `-2x ≤ -1` carries an integer
potential, yet the system has no integer solution.  Doubling alone does not decide integer
octagon feasibility. -/
theorem integer_gap :
    (∃ φ : Unit × Bool → ℤ, IsPotential (doubledGraph halfSystem) (doubledWeight halfSystem) φ) ∧
      ¬ Feasible halfSystem := by
  refine ⟨⟨fun literal' => if literal'.2 then 0 else 1, ?_⟩, ?_⟩
  · rintro ⟨_ | _, _ | _⟩ <;> decide
  · rintro ⟨value, hholds⟩
    have hupper := hholds false
    have hlower := hholds true
    simp only [Constraint.Holds, halfSystem, literal] at hupper hlower
    omega

end ProgramSemantics.Octagon
