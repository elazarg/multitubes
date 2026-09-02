/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Mixed.Walk
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Graded mixed relations

A graded mixed section assigns a cost to each directed edge constraint. Grades accumulate in a
canonically ordered additive monoid along a typed walk, while the relation remains local to each
dependent fiber. Exact, lax, and oplax edges are all allowed when the relation is symmetric.

## Main definitions

* `QuantitativeRelations.IsGradedMixedSectionFor` - edge constraints with a grade.

## Main results

* `QuantitativeRelations.IsGradedMixedSectionFor.walkMap_rel_of_lax_or_exact` and
  `QuantitativeRelations.IsGradedMixedSectionFor.walkMap_rel_of_oplax_or_exact` - graded
  propagation with one compatible polarity.
* `QuantitativeRelations.IsGradedMixedSectionFor.walkMap_rel_of_symmetric` - graded
  propagation for an arbitrary mixed walk under symmetry.
* `QuantitativeRelations.walkMap_nndist_le` - a compact nonexpansive pseudometric instance.
* `QuantitativeRelations.closedWalk_nndist_le` - the corresponding closed-walk bound.

## Tags

graded relation, dependent fiber, mixed section, walk sum, pseudometric
-/

@[expose] public section

open scoped NNReal

namespace QuantitativeRelations

open Maths

universe uV uE uF uQ

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}
variable {Fiber : V → Type uF}
variable {Grade : Type uQ}

/-- A mixed section whose edge constraints carry grades. -/
def IsGradedMixedSectionFor (T : Transport G Fiber)
    (relation : ∀ vertex : V, Grade → Fiber vertex → Fiber vertex → Prop)
    (cost : E → Grade) (mode : E → EdgeMode) (family : ∀ vertex : V, Fiber vertex) : Prop :=
  ∀ edge, (mode edge).satisfies (relation (G.target edge) (cost edge))
    (T.edgeMap edge (family (G.source edge))) (family (G.target edge))

variable {T : Transport G Fiber}
variable {relation : ∀ vertex : V, Grade → Fiber vertex → Fiber vertex → Prop}
variable {cost : E → Grade} {mode : E → EdgeMode} {family : ∀ vertex : V, Fiber vertex}
variable {start finish : V}

section Graded

variable [AddCommMonoid Grade] [Preorder Grade] [CanonicallyOrderedAdd Grade]

/-- A graded mixed section propagates its relation below the terminal value along a walk
whose edges are lax or exact.

The relation is reflexive at grade zero, monotone in its grade, transitive with additive
grades, and preserved by every edge map. -/
theorem IsGradedMixedSectionFor.walkMap_rel_of_lax_or_exact
    (hfamily : IsGradedMixedSectionFor T relation cost mode family)
    (hrefl : ∀ vertex : V, relation vertex 0 (family vertex) (family vertex))
    (hweak : ∀ vertex : V, ∀ {ε δ : Grade} {x y : Fiber vertex}, ε ≤ δ →
      relation vertex ε x y → relation vertex δ x y)
    (htrans : ∀ vertex : V, ∀ {ε δ : Grade} {x y z : Fiber vertex},
      relation vertex ε x y →
      relation vertex δ y z → relation vertex (ε + δ) x z)
    (hpreserve : ∀ edge : E, ∀ {ε : Grade} {x y : Fiber (G.source edge)},
      relation (G.source edge) ε x y →
      relation (G.target edge) ε (T.edgeMap edge x) (T.edgeMap edge y))
    (walk : G.Walk start finish)
    (hmode : ∀ edge ∈ walk.edges, (mode edge).IsLaxOrExact) :
    relation finish (walkSum cost walk)
      (T.walkMap walk (family start)) (family finish) := by
  induction walk with
  | nil =>
      simpa using hrefl start
  | concat walk edge legal ih =>
      cases legal
      rw [T.walkMap_concat, walkSum_concat]
      have hprefix : ∀ edge' ∈ walk.edges, (mode edge').IsLaxOrExact := by
        intro edge' hedge'
        exact hmode edge' (by simp [EdgeGraph.Walk.edges_concat, hedge'])
      have hedge : (mode edge).IsLaxOrExact := by
        exact hmode edge (by simp [EdgeGraph.Walk.edges_concat])
      have hpoint : relation _ (walkSum cost walk)
          (T.walkMap walk (family start)) (family _) := ih hprefix
      have hmap := hpreserve edge hpoint
      rcases hedge with hedge | hedge
      · have hstep : relation _ (cost edge)
            (T.edgeMap edge (family _)) (family _) := by
          simpa [IsGradedMixedSectionFor, hedge] using hfamily edge
        have hresult := htrans _ hmap hstep
        simpa [fiberCast] using hresult
      · have hstep : T.edgeMap edge (family _) = family _ := by
          simpa [IsGradedMixedSectionFor, hedge] using hfamily edge
        have hresult := hweak _ (δ := walkSum cost walk + cost edge)
          (le_add_right le_rfl) hmap
        simpa [fiberCast, hstep] using hresult

/-- A graded mixed section propagates its relation above the terminal value along a walk
whose edges are oplax or exact.

The relation is reflexive at grade zero, monotone in its grade, transitive with additive
grades, and preserved by every edge map. -/
theorem IsGradedMixedSectionFor.walkMap_rel_of_oplax_or_exact
    (hfamily : IsGradedMixedSectionFor T relation cost mode family)
    (hrefl : ∀ vertex : V, relation vertex 0 (family vertex) (family vertex))
    (hweak : ∀ vertex : V, ∀ {ε δ : Grade} {x y : Fiber vertex}, ε ≤ δ →
      relation vertex ε x y → relation vertex δ x y)
    (htrans : ∀ vertex : V, ∀ {ε δ : Grade} {x y z : Fiber vertex},
      relation vertex ε x y →
      relation vertex δ y z → relation vertex (ε + δ) x z)
    (hpreserve : ∀ edge : E, ∀ {ε : Grade} {x y : Fiber (G.source edge)},
      relation (G.source edge) ε x y →
      relation (G.target edge) ε (T.edgeMap edge x) (T.edgeMap edge y))
    (walk : G.Walk start finish)
    (hmode : ∀ edge ∈ walk.edges, (mode edge).IsOplaxOrExact) :
    relation finish (walkSum cost walk)
      (family finish) (T.walkMap walk (family start)) := by
  induction walk with
  | nil =>
      simpa using hrefl start
  | concat walk edge legal ih =>
      cases legal
      rw [T.walkMap_concat, walkSum_concat]
      have hprefix : ∀ edge' ∈ walk.edges, (mode edge').IsOplaxOrExact := by
        intro edge' hedge'
        exact hmode edge' (by simp [EdgeGraph.Walk.edges_concat, hedge'])
      have hedge : (mode edge).IsOplaxOrExact := by
        exact hmode edge (by simp [EdgeGraph.Walk.edges_concat])
      have hpoint : relation _ (walkSum cost walk)
          (family _) (T.walkMap walk (family start)) := ih hprefix
      have hmap := hpreserve edge hpoint
      rcases hedge with hedge | hedge
      · have hstep : relation _ (cost edge)
            (family _) (T.edgeMap edge (family _)) := by
          simpa [IsGradedMixedSectionFor, hedge] using hfamily edge
        have hresult := htrans _ hstep hmap
        simpa [add_comm, fiberCast] using hresult
      · have hstep : T.edgeMap edge (family _) = family _ := by
          simpa [IsGradedMixedSectionFor, hedge] using hfamily edge
        have hresult := hweak _ (δ := walkSum cost walk + cost edge)
          (le_add_right le_rfl) hmap
        simpa [fiberCast, hstep] using hresult

/-- A graded mixed section propagates its relation along every typed walk when the relation
is symmetric.

The relation is reflexive at grade zero, monotone in its grade, transitive with additive
grades, symmetric, and preserved by every edge map. These are exactly the laws needed for
arbitrary mixtures of exact, lax, and oplax edge constraints. -/
theorem IsGradedMixedSectionFor.walkMap_rel_of_symmetric
    (hfamily : IsGradedMixedSectionFor T relation cost mode family)
    (hrefl : ∀ vertex : V, relation vertex 0 (family vertex) (family vertex))
    (hweak : ∀ vertex : V, ∀ {ε δ : Grade} {x y : Fiber vertex}, ε ≤ δ →
      relation vertex ε x y → relation vertex δ x y)
    (htrans : ∀ vertex : V, ∀ {ε δ : Grade} {x y z : Fiber vertex},
      relation vertex ε x y →
      relation vertex δ y z → relation vertex (ε + δ) x z)
    (hsymm : ∀ vertex : V, ∀ {ε : Grade} {x y : Fiber vertex},
      relation vertex ε x y →
      relation vertex ε y x)
    (hpreserve : ∀ edge : E, ∀ {ε : Grade} {x y : Fiber (G.source edge)},
      relation (G.source edge) ε x y →
      relation (G.target edge) ε (T.edgeMap edge x) (T.edgeMap edge y))
    (walk : G.Walk start finish) :
    relation finish (walkSum cost walk)
      (T.walkMap walk (family start)) (family finish) := by
  induction walk with
  | nil =>
      simpa using hrefl start
  | concat walk edge legal ih =>
      cases legal
      rw [T.walkMap_concat, walkSum_concat]
      have hpoint : relation _ (walkSum cost walk)
          (T.walkMap walk (family start)) (family _) := ih
      have hmap := hpreserve edge hpoint
      cases hmode : mode edge with
      | lax =>
          have hstep : relation _ (cost edge)
              (T.edgeMap edge (family _)) (family _) := by
            simpa [IsGradedMixedSectionFor, hmode] using hfamily edge
          have hresult := htrans _ hmap hstep
          simpa [fiberCast] using hresult
      | exact =>
          have hstep : T.edgeMap edge (family _) = family _ := by
            simpa [IsGradedMixedSectionFor, hmode] using hfamily edge
          have hresult := hweak _ (δ := walkSum cost walk + cost edge)
            (le_add_right le_rfl) hmap
          simpa [fiberCast, hstep] using hresult
      | oplax =>
          have hstep : relation _ (cost edge)
              (family _) (T.edgeMap edge (family _)) := by
            simpa [IsGradedMixedSectionFor, hmode] using hfamily edge
          have hresult := htrans _ hmap (hsymm _ hstep)
          simpa [fiberCast] using hresult

end Graded

/-- Nonexpansive edge maps give a graded mixed section for pseudometric distance. -/
theorem walkMap_nndist_le
    [∀ vertex : V, PseudoMetricSpace (Fiber vertex)]
    {edgeCost : E → ℝ≥0}
    (hfamily : IsGradedMixedSectionFor T
      (fun _vertex ε x y => nndist x y ≤ ε) edgeCost mode family)
    (hnonexpansive : ∀ edge : E, ∀ x y : Fiber (G.source edge),
      nndist (T.edgeMap edge x) (T.edgeMap edge y) ≤ nndist x y)
    (walk : G.Walk start finish) :
    nndist (T.walkMap walk (family start)) (family finish) ≤ walkSum edgeCost walk := by
  apply IsGradedMixedSectionFor.walkMap_rel_of_symmetric hfamily
  · intro vertex
    simp
  · intro vertex ε δ x y hεδ hxy
    exact hxy.trans hεδ
  · intro vertex ε δ x y z hxy hyz
    exact (nndist_triangle x y z).trans (add_le_add hxy hyz)
  · intro _vertex ε x y hxy
    simpa [nndist_comm] using hxy
  · intro edge ε x y hxy
    exact (hnonexpansive edge x y).trans hxy

/-- A closed typed walk returns within its accumulated pseudometric cost. -/
theorem closedWalk_nndist_le
    [∀ vertex : V, PseudoMetricSpace (Fiber vertex)]
    {edgeCost : E → ℝ≥0}
    (hfamily : IsGradedMixedSectionFor T
      (fun _vertex ε x y => nndist x y ≤ ε) edgeCost mode family)
    (hnonexpansive : ∀ edge : E, ∀ x y : Fiber (G.source edge),
      nndist (T.edgeMap edge x) (T.edgeMap edge y) ≤ nndist x y)
    {vertex : V} (cycle : G.Walk vertex vertex) :
    nndist (T.walkMap cycle (family vertex)) (family vertex) ≤ walkSum edgeCost cycle :=
  walkMap_nndist_le hfamily hnonexpansive cycle

end QuantitativeRelations
