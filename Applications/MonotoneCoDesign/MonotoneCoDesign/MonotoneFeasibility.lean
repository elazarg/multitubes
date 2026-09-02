/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Relational
public import Mathlib.Order.UpperLower.Basic

/-!
# Monotone co-design feasibility

A co-design feasibility relation connects functionality provided to resources required. Its basic
monotonicity law says that a feasible implementation remains feasible when less functionality is
required or more resources are allowed. This file isolates that order-theoretic fragment without
assuming completeness, continuity, implementation spaces, or Pareto-front representations.

The law is stable under serial relational composition. Consequently a composite path of monotone
components again defines monotone feasibility, and the feasible resources for each functionality
form an upper set. The order relation is the identity for this composition, rather than the
equality relation used by ordinary relational paths.

## Main definitions

* `MonotoneCoDesign.IsMonotoneFeasibility` - downward functionality and upward resource closure.
* `MonotoneCoDesign.feasibleResources` - resources feasible for a fixed functionality.
* `MonotoneCoDesign.orderFeasibility` - the order-enriched identity feasibility relation.
* `MonotoneCoDesign.RelationTransport.HasMonotoneFeasibility` - edgewise monotone feasibility.

## Main results

* `MonotoneCoDesign.IsMonotoneFeasibility.comp` - relational composition preserves monotone
  feasibility.
* `MonotoneCoDesign.IsMonotoneFeasibility.feasibleResources_isUpperSet` - feasible resources are
  upward closed.
* `MonotoneCoDesign.IsMonotoneFeasibility.antitone_feasibleResources` - stronger functionality
  requirements have fewer feasible resources.
* `MonotoneCoDesign.orderFeasibility_comp_eq` and
  `MonotoneCoDesign.comp_orderFeasibility_eq` - the order relation is the serial identity.
* `MonotoneCoDesign.RelationTransport.HasMonotoneFeasibility.walkRelation_of_pos` - every nonempty
  network path has monotone feasibility.

## References

* A. Censi, *A Mathematical Theory of Co-Design*, 2015.

## Tags

monotone co-design, feasibility relation, serial composition, upper set, Pareto order
-/

@[expose] public section

namespace MonotoneCoDesign

open scoped SetRel

universe uF uM uR

variable {Functionality : Type uF} {Middle : Type uM} {Resources : Type uR}
variable [Preorder Functionality] [Preorder Middle] [Preorder Resources]

/-- A feasibility relation is monotone when requiring less functionality and permitting more
resources both preserve feasibility. -/
def IsMonotoneFeasibility (relation : SetRel Functionality Resources) : Prop :=
  ∀ ⦃functionality functionality' resource resource'⦄,
    functionality' ≤ functionality → resource ≤ resource' →
      functionality ~[relation] resource → functionality' ~[relation] resource'

/-- The set of resources feasible for a fixed functionality requirement. -/
def feasibleResources (relation : SetRel Functionality Resources)
    (functionality : Functionality) : Set Resources :=
  {resource | functionality ~[relation] resource}

/-- The order relation, serving as the identity monotone feasibility problem. -/
def orderFeasibility : SetRel Functionality Functionality :=
  {pair | pair.1 ≤ pair.2}

/-- Serial relational composition preserves monotone co-design feasibility. -/
theorem IsMonotoneFeasibility.comp
    {first : SetRel Functionality Middle} {second : SetRel Middle Resources}
    (hfirst : IsMonotoneFeasibility first) (hsecond : IsMonotoneFeasibility second) :
    IsMonotoneFeasibility (first ○ second) := by
  intro functionality functionality' resource resource' hfunctionality hresource
  rintro ⟨middle, hfirstFeasible, hsecondFeasible⟩
  exact ⟨middle, hfirst hfunctionality le_rfl hfirstFeasible,
    hsecond le_rfl hresource hsecondFeasible⟩

/-- Feasible resources for a fixed functionality form an upper set. -/
theorem IsMonotoneFeasibility.feasibleResources_isUpperSet
    {relation : SetRel Functionality Resources} (hrelation : IsMonotoneFeasibility relation)
    (functionality : Functionality) :
    IsUpperSet (feasibleResources relation functionality) := by
  intro resource resource' hresource hfeasible
  exact hrelation le_rfl hresource hfeasible

/-- Increasing the required functionality can only shrink the feasible resource set. -/
theorem IsMonotoneFeasibility.antitone_feasibleResources
    {relation : SetRel Functionality Resources} (hrelation : IsMonotoneFeasibility relation) :
    Antitone (feasibleResources relation) := by
  intro functionality functionality' hfunctionality resource hfeasible
  exact hrelation hfunctionality le_rfl hfeasible

/-- Order comparison is a monotone feasibility relation. -/
theorem isMonotoneFeasibility_orderFeasibility :
    IsMonotoneFeasibility (orderFeasibility : SetRel Functionality Functionality) := by
  intro functionality functionality' resource resource' hfunctionality hresource hfeasible
  exact hfunctionality.trans (hfeasible.trans hresource)

/-- The order relation is a left identity for monotone feasibility composition. -/
theorem orderFeasibility_comp_eq {relation : SetRel Functionality Resources}
    (hrelation : IsMonotoneFeasibility relation) :
    orderFeasibility ○ relation = relation := by
  ext pair
  obtain ⟨functionality, resource⟩ := pair
  change (∃ middle, functionality ≤ middle ∧ middle ~[relation] resource) ↔
    functionality ~[relation] resource
  constructor
  · rintro ⟨middle, hfunctionality, hfeasible⟩
    exact hrelation hfunctionality le_rfl hfeasible
  · intro hfeasible
    exact ⟨functionality, le_rfl, hfeasible⟩

/-- The order relation is a right identity for monotone feasibility composition. -/
theorem comp_orderFeasibility_eq {relation : SetRel Functionality Resources}
    (hrelation : IsMonotoneFeasibility relation) :
    relation ○ orderFeasibility = relation := by
  ext pair
  obtain ⟨functionality, resource⟩ := pair
  change (∃ middle, functionality ~[relation] middle ∧ middle ≤ resource) ↔
    functionality ~[relation] resource
  constructor
  · rintro ⟨middle, hfeasible, hresource⟩
    exact hrelation le_rfl hresource hfeasible
  · intro hfeasible
    exact ⟨resource, hfeasible, le_rfl⟩

namespace RelationTransport

universe uV uE uI

variable {V : Type uV} {E : Type uE} {G : Maths.EdgeGraph V E}
variable {Interface : V → Type uI} [∀ vertex, Preorder (Interface vertex)]
variable {T : Maths.RelationTransport G Interface}

/-- Every component relation of a network has monotone co-design feasibility. -/
def HasMonotoneFeasibility (T : Maths.RelationTransport G Interface) : Prop :=
  ∀ edge, IsMonotoneFeasibility (T.edgeRelation edge)

/-- Reindexing an edge relation along its endpoint equality preserves monotone feasibility. -/
theorem HasMonotoneFeasibility.edgeRelation_cast (hT : HasMonotoneFeasibility T)
    (edge : E) {vertex : V} (legal : G.source edge = vertex) :
    IsMonotoneFeasibility
      ({(source, target) |
        Maths.fiberCast Interface legal.symm source ~[T.edgeRelation edge] target} :
        SetRel (Interface vertex) (Interface (G.target edge))) := by
  subst vertex
  simpa using hT edge

/-- A nonempty walk ending in one more component has monotone composite feasibility. -/
theorem HasMonotoneFeasibility.walkRelation_concat (hT : HasMonotoneFeasibility T)
    {start finish : V} (walk : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    IsMonotoneFeasibility (T.walkRelation (walk.concat edge legal)) := by
  cases walk with
  | nil =>
      simpa [Maths.RelationTransport.walkRelation] using hT.edgeRelation_cast edge legal
  | concat walk previous previousLegal =>
      rw [Maths.RelationTransport.walkRelation]
      exact (hT.walkRelation_concat walk previous previousLegal).comp
        (hT.edgeRelation_cast edge legal)

/-- Every nonempty path through a monotone co-design network has monotone feasibility. -/
theorem HasMonotoneFeasibility.walkRelation_of_pos (hT : HasMonotoneFeasibility T)
    {start finish : V} (walk : G.Walk start finish) (hpos : 0 < walk.length) :
    IsMonotoneFeasibility (T.walkRelation walk) := by
  cases walk with
  | nil => simp at hpos
  | concat walk edge legal => exact hT.walkRelation_concat walk edge legal

end RelationTransport

end MonotoneCoDesign
