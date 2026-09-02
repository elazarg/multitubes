/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Basic
public import Mathlib.Order.Closure
public import Mathlib.Order.FixedPoints
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Complete-lattice closure for lax transport

Exact transport uses equality of forward path maps.  Lax transport
has two canonical complete-lattice constructions:

* arbitrary-join-preserving edge maps admit an explicit closure over all
  directed walks; and
* merely monotone edge maps admit a least lax majorant as the least fixed point
  of their Bellman operator.

The synchronized-loop theorem then shows why one common pre-fixed witness at a
root is sufficient even when separate cycle witnesses are not.

## Main definitions

* `Maths.Transport.pathClosure`: the join over all directed walks of the
  transported values of a given lower bound.
* `Maths.Transport.PathClosureSupSpec`: the hypothesis under which that join is
  computed edgewise.
* `Maths.Transport.rootedLower`: the lower bound concentrated at one root.
* `Maths.Transport.bellman` and `Maths.Transport.bellmanOrderHom`:
  the Bellman operator of a monotone transport, as a function and as an order homomorphism.
* `Maths.Transport.leastLaxMajorant`: its least fixed point above a given lower
  bound.
* `Maths.Transport.leastLaxMajorantClosure`: the least-majorant construction
  bundled as a closure operator.

## Main results

* `Maths.Transport.isLaxSection_pathClosure` and
  `Maths.Transport.pathClosure_isLeast`: the path closure is the least lax
  section above the given lower bound.
* `Maths.Transport.pathClosure_isLeast_of_sSupHom`: the same conclusion for
  arbitrary-join-preserving edge maps.
* `Maths.Transport.rooted_pathClosure_isLeast`: the rooted form, where one
  pre-fixed witness at the root suffices.
* `Maths.Transport.bellman_le_iff`: lax sections are exactly the pre-fixed
  points of the Bellman operator.
* `Maths.Transport.leastLaxMajorant_isLeast`: monotone edge maps admit a least
  lax majorant.
* `Maths.Transport.leastLaxMajorant_eq_self_iff`: the closed points of the
  least-majorant operator are exactly the lax sections.

## Implementation notes

The closure and Bellman constructions require complete-lattice fibers, whereas
the real-valued walk-supremum potentials have suprema only under the
boundedness that finiteness hypotheses supply.
`Maths.MaxPlusPotential.maxIncomingWeight` and
`Maths.ChargedPathBudget.ChargedRelation.value` are the
conditionally complete counterparts of `Maths.Transport.pathClosure`
(the latter on the reversed orientation), and their least-solution theorems
are proved in their own files directly from `csSup` bounds.
-/

@[expose] public section

noncomputable section

namespace Maths
namespace Transport

universe uV uE uF

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}
variable {Fiber : V → Type uF} (T : Transport G Fiber)

section PathClosure

variable [∀ vertex : V, CompleteLattice (Fiber vertex)]

/-- The join of the lower data transported along every directed walk ending at
the selected vertex.  Empty walks are included. -/
def pathClosure (lower : ∀ vertex, Fiber vertex) (vertex : V) : Fiber vertex :=
  ⨆ (source : V) (walk : G.Walk source vertex), T.walkMap walk (lower source)

@[simp] theorem le_pathClosure (lower : ∀ vertex, Fiber vertex) (vertex : V) :
    lower vertex ≤ T.pathClosure lower vertex :=
  le_iSup_of_le vertex <|
    le_iSup_of_le (EdgeGraph.Walk.nil : G.Walk vertex vertex) le_rfl

/-- Join preservation in exactly the two universe levels consumed by path
closure, together with bottom preservation for the synchronized-root theorem. -/
structure PathClosureSupSpec : Prop where
  map_vertex_iSup (edge : E) (family : V → Fiber (G.source edge)) :
    T.edgeMap edge (⨆ vertex, family vertex) =
      ⨆ vertex, T.edgeMap edge (family vertex)
  map_walk_iSup (edge : E) (source : V)
      (family : G.Walk source (G.source edge) → Fiber (G.source edge)) :
    T.edgeMap edge (⨆ walk, family walk) =
      ⨆ walk, T.edgeMap edge (family walk)
  map_bot (edge : E) : T.edgeMap edge ⊥ = ⊥

/-- A family of standard arbitrary-supremum homomorphisms supplies the exact
join-preservation interface used by path closure. -/
theorem pathClosureSupSpec_of_sSupHom
    (edgeHom : ∀ edge : E,
      sSupHom (Fiber (G.source edge)) (Fiber (G.target edge)))
    (hedge : ∀ (edge : E) (point : Fiber (G.source edge)),
      edgeHom edge point = T.edgeMap edge point) :
    T.PathClosureSupSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro edge family
    rw [← hedge, map_iSup]
    congr 1
    funext vertex
    exact hedge edge (family vertex)
  · intro edge source family
    rw [← hedge, map_iSup]
    congr 1
    funext walk
    exact hedge edge (family walk)
  · intro edge
    rw [← hedge]
    exact map_bot (edgeHom edge)

/-- The explicit path closure is a lax section when every edge map preserves
the joins indexed by vertices and typed walks. -/
theorem isLaxSection_pathClosure
    (hSup : T.PathClosureSupSpec) (lower : ∀ vertex, Fiber vertex) :
    T.IsLaxSection (T.pathClosure lower) := by
  intro edge
  rw [pathClosure, hSup.map_vertex_iSup edge]
  refine iSup_le fun source ↦ ?_
  rw [hSup.map_walk_iSup edge source]
  refine iSup_le fun walk ↦ ?_
  exact le_iSup_of_le source <|
    le_iSup_of_le (walk.concat edge rfl) le_rfl

/-- Walk transport is monotone when every edge transport is monotone. -/
theorem monotone_walkMap
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    {start finish : V} (walk : G.Walk start finish) :
    Monotone (T.walkMap walk) := by
  intro first second hle
  induction walk with
  | nil => exact hle
  | concat walk edge legal ih =>
      rw [walkMap_concat, walkMap_concat]
      exact hmono edge (fiberCast_le_fiberCast legal.symm ih)

/-- The path closure is below every lax section that dominates the lower
data.  Only monotonicity is needed for this half. -/
theorem pathClosure_le_of_isLaxSection
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (lower family : ∀ vertex, Fiber vertex)
    (hlower : ∀ vertex, lower vertex ≤ family vertex)
    (hfamily : T.IsLaxSection family) (vertex : V) :
    T.pathClosure lower vertex ≤ family vertex := by
  refine iSup_le fun source ↦ iSup_le fun walk ↦ ?_
  exact (T.monotone_walkMap hmono walk (hlower source)).trans
    (hfamily.walkMap_le hmono walk)

/-- **Path-closure theorem.**  The explicit join over all forward walks is the
least lax section dominating the prescribed lower data. -/
theorem pathClosure_isLeast
    (hSup : T.PathClosureSupSpec)
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (lower : ∀ vertex, Fiber vertex) :
    T.IsLaxSection (T.pathClosure lower) ∧
      (∀ vertex, lower vertex ≤ T.pathClosure lower vertex) ∧
      ∀ family : ∀ vertex, Fiber vertex,
        T.IsLaxSection family →
        (∀ vertex, lower vertex ≤ family vertex) →
        ∀ vertex, T.pathClosure lower vertex ≤ family vertex :=
  ⟨T.isLaxSection_pathClosure hSup lower, T.le_pathClosure lower,
    fun family hfamily hlower vertex ↦
      T.pathClosure_le_of_isLaxSection hmono lower family hlower hfamily vertex⟩

/-- The explicit path closure theorem stated through Mathlib's bundled
arbitrary-supremum homomorphisms. -/
theorem pathClosure_isLeast_of_sSupHom
    (edgeHom : ∀ edge : E,
      sSupHom (Fiber (G.source edge)) (Fiber (G.target edge)))
    (hedge : ∀ (edge : E) (point : Fiber (G.source edge)),
      edgeHom edge point = T.edgeMap edge point)
    (lower : ∀ vertex, Fiber vertex) :
    T.IsLaxSection (T.pathClosure lower) ∧
      (∀ vertex, lower vertex ≤ T.pathClosure lower vertex) ∧
      ∀ family : ∀ vertex, Fiber vertex,
        T.IsLaxSection family →
        (∀ vertex, lower vertex ≤ family vertex) →
        ∀ vertex, T.pathClosure lower vertex ≤ family vertex := by
  have hmono (edge : E) : Monotone (T.edgeMap edge) := by
    intro first second hle
    rw [← hedge, ← hedge]
    calc
      edgeHom edge first ≤
          edgeHom edge first ⊔ edgeHom edge second := le_sup_left
      _ = edgeHom edge (first ⊔ second) := (map_sup (edgeHom edge) _ _).symm
      _ = edgeHom edge second := by rw [sup_eq_right.mpr hle]
  exact T.pathClosure_isLeast
    (T.pathClosureSupSpec_of_sSupHom edgeHom hedge) hmono lower

/-- Every walk preserves bottom when all edge maps do. -/
theorem walkMap_bot (hbot : ∀ edge : E, T.edgeMap edge ⊥ = ⊥)
    {start finish : V} (walk : G.Walk start finish) :
    T.walkMap walk ⊥ = ⊥ := by
  induction walk with
  | nil => rfl
  | concat walk edge legal ih =>
      subst legal
      rw [walkMap_concat, ih]
      exact hbot edge

/-- Lower data concentrated at one base vertex. -/
def rootedLower [DecidableEq V] (base : V) (point : Fiber base) :
    ∀ vertex, Fiber vertex :=
  fun vertex ↦ if h : vertex = base then fiberCast Fiber h.symm point else ⊥

@[simp] theorem rootedLower_base [DecidableEq V] (base : V)
    (point : Fiber base) : rootedLower (Fiber := Fiber) base point base = point := by
  simp [rootedLower]

/-- **Synchronized-loop closure.**  If one point is pre-fixed by every loop at
the root, path closure returns exactly that point at the root.  Separate
cycle-dependent witnesses would not suffice for this argument. -/
theorem pathClosure_rootedLower_eq_base
    [DecidableEq V] (hSup : T.PathClosureSupSpec)
    (base : V) (point : Fiber base)
    (hcycle : ∀ cycle : G.Walk base base, T.holonomy cycle point ≤ point) :
    T.pathClosure (rootedLower (Fiber := Fiber) base point) base = point := by
  apply le_antisymm
  · refine iSup_le fun source ↦ iSup_le fun walk ↦ ?_
    by_cases hsource : source = base
    · subst source
      rw [rootedLower, dif_pos rfl, fiberCast_rfl]
      change T.holonomy walk point ≤ point
      exact hcycle walk
    · rw [rootedLower, dif_neg hsource]
      rw [T.walkMap_bot hSup.map_bot walk]
      exact bot_le
  · simpa using T.le_pathClosure (rootedLower (Fiber := Fiber) base point) base

/-- The synchronized closure is the least lax section whose base value
dominates the selected common cycle witness. -/
theorem rooted_pathClosure_isLeast
    [DecidableEq V] (hSup : T.PathClosureSupSpec)
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (base : V) (point : Fiber base)
    (hcycle : ∀ cycle : G.Walk base base, T.holonomy cycle point ≤ point) :
    T.IsLaxSection (T.pathClosure (rootedLower (Fiber := Fiber) base point)) ∧
      T.pathClosure (rootedLower (Fiber := Fiber) base point) base = point ∧
      ∀ family : ∀ vertex, Fiber vertex,
        T.IsLaxSection family → point ≤ family base →
        ∀ vertex,
          T.pathClosure (rootedLower (Fiber := Fiber) base point) vertex ≤
            family vertex := by
  refine ⟨T.isLaxSection_pathClosure hSup _,
    T.pathClosure_rootedLower_eq_base hSup base point hcycle, ?_⟩
  intro family hfamily hbase vertex
  apply T.pathClosure_le_of_isLaxSection hmono _ family _ hfamily vertex
  intro source
  by_cases hsource : source = base
  · subst source
    simpa using hbase
  · simp [rootedLower, hsource]

end PathClosure

/-! ## Bellman least fixed point for merely monotone maps -/

section Bellman

variable [∀ vertex : V, CompleteLattice (Fiber vertex)]

/-- Edges entering one selected vertex. -/
abbrev IncomingAt (vertex : V) := {edge : E // G.target edge = vertex}

/-- The Bellman operator adjoining prescribed lower data and every incoming
one-edge transport. -/
def bellman (lower family : ∀ vertex, Fiber vertex) (vertex : V) : Fiber vertex :=
  lower vertex ⊔
    ⨆ edge : IncomingAt (G := G) vertex,
      fiberCast Fiber edge.property
        (T.edgeMap edge.1 (family (G.source edge.1)))

theorem monotone_bellman
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (lower : ∀ vertex, Fiber vertex) : Monotone (T.bellman lower) := by
  intro first second hle vertex
  refine sup_le_sup le_rfl <| iSup_mono fun edge ↦ ?_
  exact fiberCast_le_fiberCast edge.property (hmono edge.1 (hle _))

/-- The Bellman operator bundled as an order homomorphism. -/
def bellmanOrderHom
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (lower : ∀ vertex, Fiber vertex) :
    (∀ vertex, Fiber vertex) →o (∀ vertex, Fiber vertex) where
  toFun := T.bellman lower
  monotone' := T.monotone_bellman hmono lower

/-- Bellman pre-fixed points are exactly lax sections dominating the lower
data. -/
theorem bellman_le_iff
    (lower family : ∀ vertex, Fiber vertex) :
    T.bellman lower family ≤ family ↔
      (∀ vertex, lower vertex ≤ family vertex) ∧ T.IsLaxSection family := by
  constructor
  · intro h
    refine ⟨fun vertex ↦ (le_sup_left.trans (h vertex)), fun edge ↦ ?_⟩
    have hedge := le_iSup
      (fun incoming : IncomingAt (G := G) (G.target edge) ↦
        fiberCast Fiber incoming.property
          (T.edgeMap incoming.1 (family (G.source incoming.1))))
      (⟨edge, rfl⟩ : IncomingAt (G := G) (G.target edge))
    exact (hedge.trans le_sup_right).trans (h (G.target edge))
  · rintro ⟨hlower, hfamily⟩ vertex
    refine sup_le (hlower vertex) <| iSup_le fun edge ↦ ?_
    rcases edge with ⟨edge, hedge⟩
    subst vertex
    simpa using hfamily edge

/-- The least lax majorant under merely monotone edge maps. -/
def leastLaxMajorant
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (lower : ∀ vertex, Fiber vertex) : ∀ vertex, Fiber vertex :=
  OrderHom.lfp (T.bellmanOrderHom hmono lower)

theorem bellman_leastLaxMajorant
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (lower : ∀ vertex, Fiber vertex) :
    T.bellman lower (T.leastLaxMajorant hmono lower) =
      T.leastLaxMajorant hmono lower :=
  (T.bellmanOrderHom hmono lower).map_lfp

/-- Knaster--Tarski completion: the least fixed point of Bellman is the least
lax section dominating the prescribed lower data. -/
theorem leastLaxMajorant_isLeast
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (lower : ∀ vertex, Fiber vertex) :
    (∀ vertex, lower vertex ≤ T.leastLaxMajorant hmono lower vertex) ∧
      T.IsLaxSection (T.leastLaxMajorant hmono lower) ∧
      ∀ family : ∀ vertex, Fiber vertex,
        (∀ vertex, lower vertex ≤ family vertex) →
        T.IsLaxSection family →
        T.leastLaxMajorant hmono lower ≤ family := by
  have hfixed := T.bellman_leastLaxMajorant hmono lower
  have hprefixed : T.bellman lower (T.leastLaxMajorant hmono lower) ≤
      T.leastLaxMajorant hmono lower := hfixed.le
  obtain ⟨hlower, hlax⟩ := (T.bellman_le_iff lower _).mp hprefixed
  refine ⟨hlower, hlax, fun family hlower' hlax' ↦ ?_⟩
  apply (T.bellmanOrderHom hmono lower).lfp_le
  exact (T.bellman_le_iff lower family).mpr ⟨hlower', hlax'⟩

/-- Least lax majorant as a closure operator.  Its closed points are defined to
be the lax sections, so the standard closure-operator API supplies
monotonicity, extensivity, and idempotence. -/
def leastLaxMajorantClosure
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge)) :
    ClosureOperator (∀ vertex : V, Fiber vertex) :=
  ClosureOperator.ofPred (T.leastLaxMajorant hmono) T.IsLaxSection
    (fun lower ↦ (T.leastLaxMajorant_isLeast hmono lower).1)
    (fun lower ↦ (T.leastLaxMajorant_isLeast hmono lower).2.1)
    (fun {lower family} hlower hfamily ↦
      (T.leastLaxMajorant_isLeast hmono lower).2.2 family
        (fun vertex ↦ hlower vertex) hfamily)

/-- Applying the bundled closure operator computes the least lax majorant. -/
@[simp] theorem leastLaxMajorantClosure_apply
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (lower : ∀ vertex : V, Fiber vertex) :
    T.leastLaxMajorantClosure hmono lower = T.leastLaxMajorant hmono lower :=
  rfl

/-- A family is fixed by least-majorant closure exactly when it is a lax
section. -/
theorem leastLaxMajorant_eq_self_iff
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (family : ∀ vertex : V, Fiber vertex) :
    T.leastLaxMajorant hmono family = family ↔ T.IsLaxSection family := by
  exact (T.leastLaxMajorantClosure hmono).isClosed_iff.symm

end Bellman

end Transport
end Maths

end
