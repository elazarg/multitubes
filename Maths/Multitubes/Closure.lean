/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Morphism
public import Mathlib.Order.Closure
public import Mathlib.Order.FixedPoints
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Complete-lattice closure for lax transport

Exact transport uses equality of forward path maps.  Lax transport over complete-lattice
fibers has a least lax section above any prescribed lower data, and two descriptions of it.

* For merely monotone edge maps it is the least fixed point of the Bellman operator, which
  adjoins to the lower data every incoming one-edge transport.
* For edge maps preserving arbitrary suprema it is given by an explicit formula: the join over
  all directed walks of the transported lower data.  The two descriptions then agree.

The synchronized-loop theorem shows why one common pre-fixed witness at a root is sufficient
even when separate cycle witnesses are not.

## Main definitions

* `Maths.Transport.PreservesSSup`: every edge map preserves arbitrary suprema.
* `Maths.Transport.pathClosure`: the join over all directed walks of the transported values of
  a given lower bound.
* `Maths.Transport.rootedLower`: the lower bound concentrated at one root.
* `Maths.Transport.bellman` and `Maths.Transport.bellmanOrderHom`: the Bellman operator of a
  monotone transport, as a function and as an order homomorphism.
* `Maths.Transport.leastLaxMajorant`: its least fixed point above a given lower bound.
* `Maths.Transport.leastLaxMajorantClosure`: the least-majorant construction bundled as a
  closure operator.

## Main results

* `Maths.Transport.bellman_le_iff`: lax sections above the lower data are exactly the
  pre-fixed points of the Bellman operator.
* `Maths.Transport.leastLaxMajorant_isLeast`: monotone edge maps admit a least lax majorant.
* `Maths.Transport.leastLaxMajorant_eq_self_iff`: the closed points of the least-majorant
  operator are exactly the lax sections.
* `Maths.Transport.pathClosure_isLeast`: for supremum-preserving edge maps, the path closure is
  the least lax section above the lower data.
* `Maths.Transport.pathClosure_eq_leastLaxMajorant`: so it is the explicit formula for the least
  lax majorant.
* `Maths.Transport.rooted_pathClosure_isLeast`: the rooted form, where one pre-fixed witness at
  the root suffices.
* `Maths.Transport.UpperSimulation.leastLaxMajorant_le_map`: soundness of abstract closure,
  bounding concrete closure by the concretization of abstract closure.

## Implementation notes

The closure and Bellman constructions require complete-lattice fibers, whereas
the real-valued walk-supremum potentials have suprema only under the
boundedness that finiteness hypotheses supply.
`Maths.MaxPlusPotential.maxIncomingWeight` and
`Maths.MaxPlusPotential.supIncomingWeight` are the conditionally complete
counterparts of `Maths.Transport.pathClosure`, and their least-solution theorems
are proved in their own files directly from maximum and `csSup` bounds.
-/

@[expose] public section

noncomputable section

namespace Maths
namespace Transport

universe uV uE uF

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}
variable {Fiber : V → Type uF} (T : Transport G Fiber)

section CompleteLattice

variable [∀ vertex : V, CompleteLattice (Fiber vertex)]

/-! ### Bellman least fixed point for monotone maps -/

/-- Walk transport is monotone when every edge transport is monotone. -/
theorem monotone_walkMap
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    {start finish : V} (walk : G.Walk start finish) :
    Monotone (T.walkMap walk) := by
  intro first second hle
  induction walk with
  | nil => exact hle
  | concat edge walk ih => exact hmono edge ih

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
    T.bellman lower family ≤ family ↔ lower ≤ family ∧ T.IsLaxSection family := by
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

/-- **Knaster--Tarski completion.**  The least fixed point of Bellman is the least lax section
dominating the prescribed lower data. -/
theorem leastLaxMajorant_isLeast
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (lower : ∀ vertex, Fiber vertex) :
    IsLeast {family | lower ≤ family ∧ T.IsLaxSection family}
      (T.leastLaxMajorant hmono lower) := by
  refine ⟨(T.bellman_le_iff lower _).mp (T.bellman_leastLaxMajorant hmono lower).le,
    fun family hfamily ↦ ?_⟩
  exact (T.bellmanOrderHom hmono lower).lfp_le ((T.bellman_le_iff lower family).mpr hfamily)

/-- The least lax majorant dominates the lower data. -/
theorem le_leastLaxMajorant (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (lower : ∀ vertex, Fiber vertex) : lower ≤ T.leastLaxMajorant hmono lower :=
  (T.leastLaxMajorant_isLeast hmono lower).1.1

/-- The least lax majorant is a lax section. -/
theorem isLaxSection_leastLaxMajorant (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (lower : ∀ vertex, Fiber vertex) : T.IsLaxSection (T.leastLaxMajorant hmono lower) :=
  (T.leastLaxMajorant_isLeast hmono lower).1.2

/-- The least lax majorant is below every lax section dominating the lower data. -/
theorem leastLaxMajorant_le (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    {lower family : ∀ vertex, Fiber vertex} (hlower : lower ≤ family)
    (hfamily : T.IsLaxSection family) : T.leastLaxMajorant hmono lower ≤ family :=
  (T.leastLaxMajorant_isLeast hmono lower).2 ⟨hlower, hfamily⟩

/-- Least lax majorant as a closure operator.  Its closed points are defined to
be the lax sections, so the standard closure-operator API supplies
monotonicity, extensivity, and idempotence. -/
def leastLaxMajorantClosure
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge)) :
    ClosureOperator (∀ vertex : V, Fiber vertex) :=
  ClosureOperator.ofPred (T.leastLaxMajorant hmono) T.IsLaxSection
    (T.le_leastLaxMajorant hmono) (T.isLaxSection_leastLaxMajorant hmono)
    (fun _ _ hlower hfamily ↦ T.leastLaxMajorant_le hmono hlower hfamily)

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
    T.leastLaxMajorant hmono family = family ↔ T.IsLaxSection family :=
  (T.leastLaxMajorantClosure hmono).isClosed_iff.symm

variable {T} in
/-- **Closure soundness.**  Concrete closure is bounded by the concretization of abstract
closure.  Here `T` is the abstract transport, `S` is the concrete transport, and `f` is
concretization.  The edge inequality of an upper simulation is the local soundness condition;
leastness of concrete closure turns it into the global comparison. -/
theorem UpperSimulation.leastLaxMajorant_le_map {Other : V → Type*}
    [∀ vertex : V, CompleteLattice (Other vertex)] {S : Transport G Other}
    (f : UpperSimulation T S) (hfmono : ∀ vertex, Monotone (f.app vertex))
    (hTmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (hSmono : ∀ edge : E, Monotone (S.edgeMap edge))
    (lowerT : ∀ vertex, Fiber vertex) (lowerS : ∀ vertex, Other vertex)
    (hlower : lowerS ≤ f.mapFamily lowerT) :
    S.leastLaxMajorant hSmono lowerS ≤ f.mapFamily (T.leastLaxMajorant hTmono lowerT) :=
  S.leastLaxMajorant_le hSmono
    (fun vertex ↦ (hlower vertex).trans <| hfmono vertex (T.le_leastLaxMajorant hTmono _ vertex))
    (f.map_isLaxSection hfmono (T.isLaxSection_leastLaxMajorant hTmono lowerT))

/-! ### Path closure for supremum-preserving maps -/

/-- Every edge map preserves arbitrary suprema. -/
def PreservesSSup : Prop :=
  ∀ (edge : E) (points : Set (Fiber (G.source edge))),
    T.edgeMap edge (sSup points) = sSup (T.edgeMap edge '' points)

variable {T}

/-- Edge maps given by a family of supremum homomorphisms preserve suprema. -/
theorem preservesSSup_of_sSupHom
    (edgeHom : ∀ edge : E, sSupHom (Fiber (G.source edge)) (Fiber (G.target edge)))
    (hedge : ∀ edge : E, ⇑(edgeHom edge) = T.edgeMap edge) : T.PreservesSSup := by
  intro edge points
  rw [← hedge, map_sSup]

/-- A supremum-preserving edge map preserves indexed suprema over any index type. -/
theorem PreservesSSup.map_iSup (hsup : T.PreservesSSup) (edge : E) {ι : Sort*}
    (family : ι → Fiber (G.source edge)) :
    T.edgeMap edge (⨆ index, family index) = ⨆ index, T.edgeMap edge (family index) := by
  rw [iSup, hsup, ← Set.range_comp, iSup]
  rfl

/-- A supremum-preserving edge map preserves bottom. -/
theorem PreservesSSup.map_bot (hsup : T.PreservesSSup) (edge : E) :
    T.edgeMap edge ⊥ = ⊥ := by
  rw [← sSup_empty, hsup, Set.image_empty, sSup_empty]

/-- A supremum-preserving edge map is monotone. -/
theorem PreservesSSup.monotone (hsup : T.PreservesSSup) (edge : E) :
    Monotone (T.edgeMap edge) := by
  intro first second hle
  have hpair := hsup edge {first, second}
  rw [sSup_pair, sup_eq_right.mpr hle, Set.image_pair, sSup_pair] at hpair
  exact hpair ▸ le_sup_left

variable (T)

/-- The join of the lower data transported along every directed walk ending at
the selected vertex.  Empty walks are included. -/
def pathClosure (lower : ∀ vertex, Fiber vertex) (vertex : V) : Fiber vertex :=
  ⨆ (source : V) (walk : G.Walk source vertex), T.walkMap walk (lower source)

/-- The path closure dominates the lower data, through the empty walks. -/
theorem le_pathClosure (lower : ∀ vertex, Fiber vertex) : lower ≤ T.pathClosure lower :=
  fun vertex ↦ le_iSup_of_le vertex <|
    le_iSup_of_le (EdgeGraph.Walk.nil : G.Walk vertex vertex) le_rfl

variable {T}

/-- The path closure is a lax section when every edge map preserves suprema. -/
theorem isLaxSection_pathClosure (hsup : T.PreservesSSup) (lower : ∀ vertex, Fiber vertex) :
    T.IsLaxSection (T.pathClosure lower) := by
  intro edge
  rw [pathClosure, hsup.map_iSup]
  refine iSup_le fun source ↦ ?_
  rw [hsup.map_iSup]
  exact iSup_le fun walk ↦ le_iSup_of_le source <| le_iSup_of_le (walk.concat edge) le_rfl

/-- The path closure is below every lax section that dominates the lower
data.  Only monotonicity is needed for this half. -/
theorem pathClosure_le_of_isLaxSection
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    {lower family : ∀ vertex, Fiber vertex} (hlower : lower ≤ family)
    (hfamily : T.IsLaxSection family) : T.pathClosure lower ≤ family :=
  fun _ ↦ iSup_le fun source ↦ iSup_le fun walk ↦
    (T.monotone_walkMap hmono walk (hlower source)).trans (hfamily.walkMap_le hmono walk)

/-- **Path-closure theorem.**  For supremum-preserving edge maps, the explicit join over all
forward walks is the least lax section dominating the prescribed lower data. -/
theorem pathClosure_isLeast (hsup : T.PreservesSSup) (lower : ∀ vertex, Fiber vertex) :
    IsLeast {family | lower ≤ family ∧ T.IsLaxSection family} (T.pathClosure lower) :=
  ⟨⟨T.le_pathClosure lower, isLaxSection_pathClosure hsup lower⟩,
    fun _ hfamily ↦ pathClosure_le_of_isLaxSection hsup.monotone hfamily.1 hfamily.2⟩

/-- **The path closure computes the least lax majorant.**  For supremum-preserving edge maps the
least fixed point of the Bellman operator is the join of the lower data transported along all
walks. -/
theorem pathClosure_eq_leastLaxMajorant (hsup : T.PreservesSSup)
    (lower : ∀ vertex, Fiber vertex) :
    T.pathClosure lower = T.leastLaxMajorant hsup.monotone lower :=
  (pathClosure_isLeast hsup lower).unique (T.leastLaxMajorant_isLeast hsup.monotone lower)

/-- Every walk preserves bottom when all edge maps do. -/
theorem walkMap_bot (hbot : ∀ edge : E, T.edgeMap edge ⊥ = ⊥)
    {start finish : V} (walk : G.Walk start finish) :
    T.walkMap walk ⊥ = ⊥ := by
  induction walk with
  | nil => rfl
  | concat edge walk ih =>
      rw [walkMap_concat, ih]
      exact hbot edge

/-- Lower data concentrated at one base vertex. -/
def rootedLower [DecidableEq V] (base : V) (point : Fiber base) :
    ∀ vertex, Fiber vertex :=
  fun vertex ↦ if h : vertex = base then fiberCast Fiber h.symm point else ⊥

@[simp] theorem rootedLower_base [DecidableEq V] (base : V)
    (point : Fiber base) : rootedLower (Fiber := Fiber) base point base = point := by
  simp [rootedLower]

/-- Lower data concentrated at a base lies below a family exactly when the base point does. -/
theorem rootedLower_le_iff [DecidableEq V] {base : V} {point : Fiber base}
    {family : ∀ vertex, Fiber vertex} :
    rootedLower base point ≤ family ↔ point ≤ family base := by
  refine ⟨fun hle ↦ by simpa using hle base, fun hle vertex ↦ ?_⟩
  by_cases hvertex : vertex = base
  · subst vertex
    simpa using hle
  · simp [rootedLower, hvertex]

/-- **Synchronized-loop closure.**  If one point is pre-fixed by every loop at
the root, path closure returns exactly that point at the root.  Separate
cycle-dependent witnesses would not suffice for this argument. -/
theorem pathClosure_rootedLower_eq_base
    [DecidableEq V] (hsup : T.PreservesSSup)
    (base : V) (point : Fiber base)
    (hcycle : ∀ cycle : G.Walk base base, T.holonomy cycle point ≤ point) :
    T.pathClosure (rootedLower (Fiber := Fiber) base point) base = point := by
  apply le_antisymm
  · refine iSup_le fun source ↦ iSup_le fun walk ↦ ?_
    by_cases hsource : source = base
    · subst source
      rw [rootedLower, dite_eq_left rfl, fiberCast_rfl]
      exact hcycle walk
    · rw [rootedLower, dite_eq_right hsource, T.walkMap_bot hsup.map_bot walk]
      exact bot_le
  · simpa using T.le_pathClosure (rootedLower (Fiber := Fiber) base point) base

/-- The synchronized closure is the least lax section whose base value dominates the selected
common cycle witness. -/
theorem rooted_pathClosure_isLeast
    [DecidableEq V] (hsup : T.PreservesSSup) (base : V) (point : Fiber base) :
    IsLeast {family | point ≤ family base ∧ T.IsLaxSection family}
      (T.pathClosure (rootedLower (Fiber := Fiber) base point)) := by
  simpa only [rootedLower_le_iff] using pathClosure_isLeast hsup (rootedLower base point)

end CompleteLattice

end Transport
end Maths

end
