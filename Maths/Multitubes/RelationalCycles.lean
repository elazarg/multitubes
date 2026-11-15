/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Relational

/-!
# Path consistency does not give a relational section

A relational section satisfies every edge relation, so it satisfies the composite relation of
every walk (`Maths.RelationTransport.IsSection.walkRelation`).  In particular every closed-walk
relation relates the section's value at its base to itself, and every edge relation is implied by
the composite relation of every walk parallel to it.  Neither condition, nor both together, is
sufficient.

The witness is the proper three-coloring problem on the complete graph with four vertices: each
directed edge between distinct vertices carries the relation `≠` on `Fin 3`.  Every nonempty walk
relates every pair of distinct colors, and every walk of length at least two relates every pair
of colors.  Hence every closed-walk relation is reflexive and the network is path-consistent in
the sense that every edge relation is contained in the composite relation of every nonempty
parallel walk.  Yet four vertices cannot be colored injectively with three colors.

This is the relational instance of the obstruction that
`Maths.MaxAffineTransport.not_forall_cycle_prefixed_imp_exists_isLaxSection` exhibits for lax
max-affine transport: closed-walk witnesses exist separately but do not synchronize into one
family.

## Main definitions

* `Maths.RelationTransport.cliqueFour` - the complete directed graph on four vertices, without
  loops.
* `Maths.RelationTransport.threeColoring` - the relation `≠` on `Fin 3` on every edge.

## Main results

* `Maths.RelationTransport.threeColoring_mem_walkRelation_of_ne` - every nonempty walk relates
  distinct colors.
* `Maths.RelationTransport.threeColoring_mem_walkRelation_of_two_le` - every walk of length at
  least two relates all colors.
* `Maths.RelationTransport.threeColoring_edgeRelation_subset_walkRelation` - path consistency:
  each edge relation is contained in the relation of every nonempty parallel walk.
* `Maths.RelationTransport.threeColoring_holonomy_refl` - every closed-walk relation is
  reflexive.
* `Maths.RelationTransport.not_exists_isSection_threeColoring` - there is no section.

## References

* U. Montanari, *Networks of constraints: fundamental properties and applications to picture
  processing*, Inform. Sci. 7 (1974), 95-132, for path consistency and the uncolorable
  tetrahedron.

## Tags

constraint network, path consistency, graph coloring, relational section, local-global
-/

@[expose] public section

namespace Maths

namespace RelationTransport

open scoped SetRel

/-- The complete directed graph on four vertices, with one edge for each ordered pair of
distinct vertices and no loops. -/
def cliqueFour : EdgeGraph (Fin 4) {pair : Fin 4 × Fin 4 // pair.1 ≠ pair.2} where
  source edge := edge.1.1
  target edge := edge.1.2

/-- Proper three-coloring as a relation-labelled transport: every edge relates distinct
colors. -/
def threeColoring : RelationTransport cliqueFour fun _ => Fin 3 where
  edgeRelation _ := {pair | pair.1 ≠ pair.2}

private theorem exists_ne_ne (first second : Fin 3) : ∃ third, first ≠ third ∧ third ≠ second := by
  revert first second
  decide

/-- A walk of length zero relates every color to itself. -/
theorem threeColoring_mem_walkRelation_of_length_eq_zero {start finish : Fin 4}
    (walk : cliqueFour.Walk start finish) (hlength : walk.length = 0) (color : Fin 3) :
    color ~[threeColoring.walkRelation walk] color := by
  induction walk with
  | nil => rfl
  | concat edge walk ih => simp at hlength

/-- Every nonempty walk relates every pair of distinct colors. -/
theorem threeColoring_mem_walkRelation_of_ne {start finish : Fin 4}
    (walk : cliqueFour.Walk start finish) (hlength : 0 < walk.length) {first second : Fin 3}
    (hne : first ≠ second) : first ~[threeColoring.walkRelation walk] second := by
  induction walk generalizing second with
  | nil => simp at hlength
  | concat edge walk ih =>
      rcases Nat.eq_zero_or_pos walk.length with hzero | hpos
      · exact ⟨first, threeColoring_mem_walkRelation_of_length_eq_zero walk hzero first, hne⟩
      · obtain ⟨third, hfirst, hsecond⟩ := exists_ne_ne first second
        exact ⟨third, ih hpos hfirst, hsecond⟩

/-- Every walk of length at least two relates every pair of colors. -/
theorem threeColoring_mem_walkRelation_of_two_le {start finish : Fin 4}
    (walk : cliqueFour.Walk start finish) (hlength : 2 ≤ walk.length) (first second : Fin 3) :
    first ~[threeColoring.walkRelation walk] second := by
  cases walk with
  | nil => simp at hlength
  | concat edge walk =>
      obtain ⟨third, hfirst, hsecond⟩ := exists_ne_ne first second
      have hpos : 0 < walk.length := by simp at hlength; omega
      exact ⟨third, threeColoring_mem_walkRelation_of_ne walk hpos hfirst, hsecond⟩

/-- **Path consistency.**  Every edge relation is contained in the composite relation of every
nonempty walk with the same endpoints. -/
theorem threeColoring_edgeRelation_subset_walkRelation (edge : {pair : Fin 4 × Fin 4 //
    pair.1 ≠ pair.2}) (walk : cliqueFour.Walk (cliqueFour.source edge) (cliqueFour.target edge))
    (hlength : 0 < walk.length) :
    threeColoring.edgeRelation edge ⊆ threeColoring.walkRelation walk :=
  fun _ hpair => threeColoring_mem_walkRelation_of_ne walk hlength hpair

/-- A walk of length one in the loopless clique joins distinct vertices. -/
theorem ne_of_length_eq_one {start finish : Fin 4} (walk : cliqueFour.Walk start finish)
    (hlength : walk.length = 1) : start ≠ finish := by
  cases walk with
  | nil => simp at hlength
  | concat edge walk =>
      have hstart : start = cliqueFour.source edge :=
        walk.eq_of_length_eq_zero (by simpa using hlength)
      rw [hstart]
      exact edge.2

/-- Every closed-walk relation is reflexive: each color at the base is consistent with every
closed walk through it. -/
theorem threeColoring_holonomy_refl {base : Fin 4} (cycle : cliqueFour.Walk base base)
    (color : Fin 3) : color ~[threeColoring.walkRelation cycle] color := by
  rcases Nat.lt_or_ge cycle.length 2 with hshort | hlong
  · rcases Nat.lt_succ_iff.mp hshort |>.lt_or_eq with hzero | hone
    · exact threeColoring_mem_walkRelation_of_length_eq_zero cycle (by omega) color
    · exact absurd rfl (ne_of_length_eq_one cycle hone)
  · exact threeColoring_mem_walkRelation_of_two_le cycle hlong color color

/-- **No section.**  A section would color the four vertices injectively with three colors. -/
theorem not_exists_isSection_threeColoring :
    ¬ ∃ family : Fin 4 → Fin 3, threeColoring.IsSection family := by
  rintro ⟨family, hfamily⟩
  have hinjective : Function.Injective family := by
    intro first second hequal
    by_contra hne
    exact hfamily ⟨(first, second), hne⟩ hequal
  simpa using Fintype.card_le_of_injective family hinjective

end RelationTransport

end Maths
