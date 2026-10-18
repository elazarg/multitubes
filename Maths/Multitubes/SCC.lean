/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Exact

/-!
# Strongly connected normal forms for transport

An arbitrary type-valued transport has trivial holonomy exactly when its
restriction to every strongly connected component is equivalent to constant
transport.  The equivalences identify every edge map inside the component
with change of coordinates between its endpoint fibers.  No algebraic
structure on the fibers is required, and inter-component edges are
unconstrained.

## Main definitions

* `Maths.Transport.HasSCCTrivializationAt` and
  `Maths.Transport.HasSCCTrivializations`: fiberwise equivalences identifying
  every edge map inside a component with a change of coordinates.
* `Maths.Transport.sccTrivialization`: the trivialization built from trivial
  holonomy.

## Main results

* `Maths.Transport.hasTrivialHolonomy_iff_hasSCCTrivializations`: trivial
  holonomy is exactly componentwise triviality.
-/

@[expose] public section

noncomputable section

namespace Maths

universe uV uE uF

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}
variable {Fiber : V → Type uF} {T : Transport G Fiber}

/-! ## Componentwise transport trivializations -/

/-- A constant-transport normal form on the strongly connected component of
`base`.  Only vertices and edges in that component enter the interface. -/
def Transport.HasSCCTrivializationAt (T : Transport G Fiber)
    (base : V) : Prop :=
  ∃ trivialization :
      ∀ vertex, LinkedTo G base vertex → Fiber base ≃ Fiber vertex,
    ∀ (edge : E)
      (hsource : LinkedTo G base (G.source edge))
      (htarget : LinkedTo G base (G.target edge)),
      T.edgeMap edge =
        (trivialization (G.target edge) htarget :
            Fiber base → Fiber (G.target edge)) ∘
          (trivialization (G.source edge) hsource).symm

/-- Componentwise constant-transport normal forms on the whole graph. -/
def Transport.HasSCCTrivializations (T : Transport G Fiber) : Prop :=
  ∀ base, T.HasSCCTrivializationAt base

/-- The equivalence induced by chosen forward and return walks inside a flat
strongly connected component. -/
def Transport.sccTrivialization (hflat : T.HasTrivialHolonomy)
    (base vertex : V) (hlinked : LinkedTo G base vertex) :
    Fiber base ≃ Fiber vertex :=
  T.walkMapEquivOfTrivialHolonomy hflat hlinked.1.some hlinked.2.some

theorem Transport.sccTrivialization_edgeMap
    (hflat : T.HasTrivialHolonomy) (base : V) (edge : E)
    (hsource : LinkedTo G base (G.source edge))
    (htarget : LinkedTo G base (G.target edge)) :
    T.edgeMap edge =
      (T.sccTrivialization hflat base (G.target edge) htarget :
          Fiber base → Fiber (G.target edge)) ∘
        (T.sccTrivialization hflat base (G.source edge) hsource).symm := by
  funext point
  change T.walkMap (EdgeGraph.Walk.singleton edge) point =
    T.walkMap htarget.1.some (T.walkMap hsource.2.some point)
  rw [← T.walkMap_append]
  exact congrFun
    (T.walkMap_eq_of_trivialHolonomy_of_return hflat
      (EdgeGraph.Walk.singleton edge)
      (hsource.2.some.append htarget.1.some)
      (htarget.2.some.append hsource.1.some)) point

private theorem linkedTo_of_mem_cycle_source {base : V}
    (cycle : G.Walk base base) {edge : E} (hedge : edge ∈ cycle.edges) :
    LinkedTo G base (G.source edge) := by
  let split := cycle.vertexSplitAtSource edge hedge
  exact ⟨⟨split.before⟩, ⟨split.after⟩⟩

private theorem linkedTo_of_mem_cycle_target {base : V}
    (cycle : G.Walk base base) {edge : E} (hedge : edge ∈ cycle.edges) :
    LinkedTo G base (G.target edge) := by
  let split := cycle.vertexSplitAtTarget edge hedge
  exact ⟨⟨split.before⟩, ⟨split.after⟩⟩

private theorem Transport.walkMap_eq_of_edgeTrivializations
    {base start finish : V}
    (trivialization :
      ∀ vertex, LinkedTo G base vertex → Fiber base ≃ Fiber vertex)
    (walk : G.Walk start finish)
    (hstart : LinkedTo G base start)
    (hfinish : LinkedTo G base finish)
    (hedge : ∀ edge ∈ walk.edges,
      ∃ (hsource : LinkedTo G base (G.source edge))
        (htarget : LinkedTo G base (G.target edge)),
        T.edgeMap edge =
          (trivialization (G.target edge) htarget :
              Fiber base → Fiber (G.target edge)) ∘
            (trivialization (G.source edge) hsource).symm) :
    T.walkMap walk =
      (trivialization finish hfinish : Fiber base → Fiber finish) ∘
        (trivialization start hstart).symm := by
  induction walk with
  | nil =>
      funext point
      simp
  | @concat middle walk edge legal ih =>
      have hbefore (candidate : E) (hcandidate : candidate ∈ walk.edges) :
          ∃ (hsource : LinkedTo G base (G.source candidate))
            (htarget : LinkedTo G base (G.target candidate)),
            T.edgeMap candidate =
              (trivialization (G.target candidate) htarget :
                  Fiber base → Fiber (G.target candidate)) ∘
                (trivialization (G.source candidate) hsource).symm :=
        hedge candidate (by simp [hcandidate])
      obtain ⟨hmiddle, htarget, hlast⟩ := hedge edge (by simp)
      subst legal
      funext point
      rw [T.walkMap_concat, hlast, Function.comp_apply,
        congrFun (ih hmiddle hbefore) point]
      simp

/-- **Type-valued SCC normal form.**  Trivial holonomy is equivalent to a
constant-transport trivialization on every strongly connected component.
This is the fiber-valued counterpart of the unit-potential normal form for
monoid labels. -/
theorem Transport.hasTrivialHolonomy_iff_hasSCCTrivializations :
    T.HasTrivialHolonomy ↔ T.HasSCCTrivializations := by
  constructor
  · intro hflat base
    refine ⟨T.sccTrivialization hflat base, ?_⟩
    exact T.sccTrivialization_edgeMap hflat base
  · intro hcomponents base cycle
    obtain ⟨trivialization, htrivialization⟩ := hcomponents base
    have hbase : LinkedTo G base base := ⟨⟨.nil⟩, ⟨.nil⟩⟩
    have hedge (edge : E) (hmem : edge ∈ cycle.edges) :
        ∃ (hsource : LinkedTo G base (G.source edge))
          (htarget : LinkedTo G base (G.target edge)),
          T.edgeMap edge =
            (trivialization (G.target edge) htarget :
                Fiber base → Fiber (G.target edge)) ∘
              (trivialization (G.source edge) hsource).symm := by
      let hsource := linkedTo_of_mem_cycle_source cycle hmem
      let htarget := linkedTo_of_mem_cycle_target cycle hmem
      exact ⟨hsource, htarget, htrivialization edge hsource htarget⟩
    have hwalk := T.walkMap_eq_of_edgeTrivializations
      trivialization cycle hbase hbase hedge
    funext point
    change T.walkMap cycle point = point
    rw [hwalk]
    simp

end Maths

end
