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

Over complete-lattice fibers, the lax sections of a transport with monotone edge maps are closed
under arbitrary infima: they form a Moore family.  So every prescribed lower data has a least lax
section above it, the infimum of all of them, and the corresponding closure operator.  Two
further descriptions of it follow.

* It is the least fixed point of the Bellman operator, which adjoins the lower data to the
  incoming join `Maths.Transport.incomingSup`, the join of the one-edge transports into each
  vertex.  Lax sections are exactly the pre-fixed points of the incoming join.
* For edge maps preserving arbitrary suprema it is given by an explicit formula: the join over
  all directed walks of the transported lower data.

The synchronized-loop theorem shows why one common pre-fixed witness at a root is sufficient
even when separate cycle witnesses are not.

## Main definitions

* `Maths.Transport.incomingSup` and `Maths.Transport.incomingInf`: the join and the meet of the
  values transported into each vertex.
* `Maths.Transport.leastLaxMajorant`: the least lax section above a given lower bound.
* `Maths.Transport.leastLaxMajorantClosure`: the closure operator of the Moore family of lax
  sections.
* `Maths.Transport.bellman` and `Maths.Transport.bellmanOrderHom`: the Bellman operator of a
  monotone transport, as a function and as an order homomorphism.
* `Maths.Transport.PreservesSSup`: every edge map preserves arbitrary suprema.
* `Maths.Transport.pathClosure`: the join over all directed walks of the transported values of
  a given lower bound.

## Main results

* `Maths.Transport.isLaxSection_iff_incomingSup_le` and
  `Maths.Transport.isOplaxSection_iff_le_incomingInf`: lax and oplax sections are the pre- and
  post-fixed points of the incoming operators.
* `Maths.Transport.isLaxSection_sInf`: lax sections form a Moore family.
* `Maths.Transport.leastLaxMajorant_isLeast`: monotone edge maps admit a least lax majorant.
* `Maths.Transport.leastLaxMajorant_eq_self_iff`: the closed points of the least-majorant
  operator are exactly the lax sections.
* `Maths.Transport.bellman_le_iff`: lax sections above the lower data are exactly the
  pre-fixed points of the Bellman operator.
* `Maths.Transport.leastLaxMajorant_eq_lfp`: the least lax majorant is the least fixed point of
  the Bellman operator.
* `Maths.Transport.pathClosure_isLeast`: for supremum-preserving edge maps, the path closure is
  the least lax section above the lower data.
* `Maths.Transport.pathClosure_eq_leastLaxMajorant`: so it is the explicit formula for the least
  lax majorant.
* `Maths.Transport.pathClosure_eq_iSup_iterate_incomingSup`: Kleene iteration, the path closure
  as the join of the iterates of the incoming join.
* `Maths.Transport.rooted_pathClosure_isLeast`: the rooted form, where one pre-fixed witness at
  the root suffices.
* `Maths.Transport.LaxHom.leastLaxMajorant_le_map`: soundness of abstract closure,
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

/-! ### The incoming operators -/

/-- Edges entering one selected vertex. -/
abbrev IncomingAt (vertex : V) := {edge : E // G.target edge = vertex}

/-- The join, at each vertex, of the values transported into it along its incoming edges.  A lax
section is a pre-fixed point (`Maths.Transport.isLaxSection_iff_incomingSup_le`). -/
def incomingSup (family : ∀ vertex, Fiber vertex) (vertex : V) : Fiber vertex :=
  ⨆ edge : IncomingAt (G := G) vertex,
    fiberCast Fiber edge.property (T.edgeMap edge.1 (family (G.source edge.1)))

/-- The meet, at each vertex, of the values transported into it along its incoming edges.  An
oplax section is a post-fixed point (`Maths.Transport.isOplaxSection_iff_le_incomingInf`). -/
def incomingInf (family : ∀ vertex, Fiber vertex) (vertex : V) : Fiber vertex :=
  ⨅ edge : IncomingAt (G := G) vertex,
    fiberCast Fiber edge.property (T.edgeMap edge.1 (family (G.source edge.1)))

variable {T}

/-- An incoming edge contributes to the incoming join at its target. -/
theorem edgeMap_le_incomingSup (family : ∀ vertex, Fiber vertex) (edge : E) :
    T.edgeMap edge (family (G.source edge)) ≤ T.incomingSup family (G.target edge) :=
  le_iSup_of_le (⟨edge, rfl⟩ : IncomingAt (G := G) (G.target edge)) le_rfl

/-- The incoming meet at its target is below the contribution of an incoming edge. -/
theorem incomingInf_le_edgeMap (family : ∀ vertex, Fiber vertex) (edge : E) :
    T.incomingInf family (G.target edge) ≤ T.edgeMap edge (family (G.source edge)) :=
  iInf_le_of_le (⟨edge, rfl⟩ : IncomingAt (G := G) (G.target edge)) le_rfl

/-- The incoming join is below a family exactly when every edge transports below it. -/
theorem incomingSup_le_iff {family other : ∀ vertex, Fiber vertex} :
    T.incomingSup family ≤ other ↔
      ∀ edge, T.edgeMap edge (family (G.source edge)) ≤ other (G.target edge) := by
  refine ⟨fun h edge => (edgeMap_le_incomingSup family edge).trans (h _), fun h vertex => ?_⟩
  refine iSup_le fun ⟨edge, hedge⟩ => ?_
  subst hedge
  exact h edge

/-- The incoming meet is above a family exactly when every edge transports above it. -/
theorem le_incomingInf_iff {family other : ∀ vertex, Fiber vertex} :
    other ≤ T.incomingInf family ↔
      ∀ edge, other (G.target edge) ≤ T.edgeMap edge (family (G.source edge)) := by
  refine ⟨fun h edge => (h _).trans (incomingInf_le_edgeMap family edge), fun h vertex => ?_⟩
  refine le_iInf fun ⟨edge, hedge⟩ => ?_
  subst hedge
  exact h edge

/-- Lax sections are the pre-fixed points of the incoming join. -/
theorem isLaxSection_iff_incomingSup_le {family : ∀ vertex, Fiber vertex} :
    T.IsLaxSection family ↔ T.incomingSup family ≤ family :=
  incomingSup_le_iff.symm

/-- Oplax sections are the post-fixed points of the incoming meet. -/
theorem isOplaxSection_iff_le_incomingInf {family : ∀ vertex, Fiber vertex} :
    T.IsOplaxSection family ↔ family ≤ T.incomingInf family :=
  le_incomingInf_iff.symm

/-- The incoming join is monotone when the edge maps are. -/
theorem IsMonotone.monotone_incomingSup (hmono : T.IsMonotone) : Monotone T.incomingSup :=
  fun _ _ hle _ => iSup_mono fun edge =>
    fiberCast_le_fiberCast edge.property (hmono edge.1 (hle _))

/-- The incoming meet is monotone when the edge maps are. -/
theorem IsMonotone.monotone_incomingInf (hmono : T.IsMonotone) : Monotone T.incomingInf :=
  fun _ _ hle _ => iInf_mono fun edge =>
    fiberCast_le_fiberCast edge.property (hmono edge.1 (hle _))

/-! ### The least lax majorant -/

/-- **Lax sections form a Moore family.**  Under monotone edge maps an arbitrary infimum of lax
sections is a lax section. -/
theorem isLaxSection_sInf (hmono : T.IsMonotone) {families : Set (∀ vertex, Fiber vertex)}
    (hfamilies : ∀ family ∈ families, T.IsLaxSection family) :
    T.IsLaxSection (sInf families) := fun edge => by
  simp only [sInf_apply]
  exact le_iInf fun family =>
    (hmono edge (iInf_le _ family)).trans (hfamilies family family.2 edge)

variable (T)

/-- The least lax section dominating prescribed lower data: the infimum of all of them.  No
hypothesis is needed to state it; under monotone edge maps it is itself a lax section
(`Maths.Transport.leastLaxMajorant_isLeast`). -/
def leastLaxMajorant (lower : ∀ vertex, Fiber vertex) : ∀ vertex, Fiber vertex :=
  sInf {family | lower ≤ family ∧ T.IsLaxSection family}

variable {T}

/-- The least lax majorant dominates the lower data. -/
theorem le_leastLaxMajorant (lower : ∀ vertex, Fiber vertex) :
    lower ≤ T.leastLaxMajorant lower :=
  le_sInf fun _ hfamily => hfamily.1

/-- The least lax majorant is below every lax section dominating the lower data. -/
theorem leastLaxMajorant_le {lower family : ∀ vertex, Fiber vertex} (hlower : lower ≤ family)
    (hfamily : T.IsLaxSection family) : T.leastLaxMajorant lower ≤ family :=
  sInf_le ⟨hlower, hfamily⟩

/-- The least lax majorant is a lax section. -/
theorem isLaxSection_leastLaxMajorant (hmono : T.IsMonotone)
    (lower : ∀ vertex, Fiber vertex) : T.IsLaxSection (T.leastLaxMajorant lower) :=
  isLaxSection_sInf hmono fun _ hfamily => hfamily.2

/-- Monotone edge maps admit a least lax section dominating any prescribed lower data. -/
theorem leastLaxMajorant_isLeast (hmono : T.IsMonotone) (lower : ∀ vertex, Fiber vertex) :
    IsLeast {family | lower ≤ family ∧ T.IsLaxSection family} (T.leastLaxMajorant lower) :=
  ⟨⟨le_leastLaxMajorant lower, isLaxSection_leastLaxMajorant hmono lower⟩,
    fun _ hfamily => leastLaxMajorant_le hfamily.1 hfamily.2⟩

/-- The least lax majorant as the closure operator of the Moore family of lax sections.  The
closure-operator API supplies monotonicity, extensivity, and idempotence. -/
def leastLaxMajorantClosure (hmono : T.IsMonotone) :
    ClosureOperator (∀ vertex : V, Fiber vertex) :=
  ClosureOperator.ofCompletePred T.IsLaxSection fun _ => isLaxSection_sInf hmono

/-- Applying the bundled closure operator computes the least lax majorant. -/
@[simp] theorem leastLaxMajorantClosure_apply (hmono : T.IsMonotone)
    (lower : ∀ vertex : V, Fiber vertex) :
    leastLaxMajorantClosure hmono lower = T.leastLaxMajorant lower :=
  (sInf_eq_iInf' _).symm

/-- A family is fixed by least-majorant closure exactly when it is a lax section. -/
theorem leastLaxMajorant_eq_self_iff (hmono : T.IsMonotone)
    (family : ∀ vertex : V, Fiber vertex) :
    T.leastLaxMajorant family = family ↔ T.IsLaxSection family := by
  rw [← leastLaxMajorantClosure_apply hmono]
  exact (leastLaxMajorantClosure hmono).isClosed_iff.symm

/-! ### The Bellman operator -/

variable (T)

/-- The Bellman operator, adjoining prescribed lower data to the incoming join. -/
def bellman (lower family : ∀ vertex, Fiber vertex) : ∀ vertex, Fiber vertex :=
  lower ⊔ T.incomingSup family

variable {T}

/-- The Bellman operator is monotone when the edge maps are. -/
theorem IsMonotone.monotone_bellman (hmono : T.IsMonotone) (lower : ∀ vertex, Fiber vertex) :
    Monotone (T.bellman lower) :=
  fun _ _ hle => sup_le_sup le_rfl (hmono.monotone_incomingSup hle)

/-- The Bellman operator bundled as an order homomorphism. -/
def bellmanOrderHom (hmono : T.IsMonotone) (lower : ∀ vertex, Fiber vertex) :
    (∀ vertex, Fiber vertex) →o (∀ vertex, Fiber vertex) where
  toFun := T.bellman lower
  monotone' := hmono.monotone_bellman lower

/-- Bellman pre-fixed points are exactly lax sections dominating the lower data. -/
theorem bellman_le_iff {lower family : ∀ vertex, Fiber vertex} :
    T.bellman lower family ≤ family ↔ lower ≤ family ∧ T.IsLaxSection family := by
  rw [bellman, sup_le_iff, isLaxSection_iff_incomingSup_le]

/-- **Knaster--Tarski.**  The least lax majorant is the least fixed point of the Bellman
operator. -/
theorem leastLaxMajorant_eq_lfp (hmono : T.IsMonotone) (lower : ∀ vertex, Fiber vertex) :
    T.leastLaxMajorant lower = OrderHom.lfp (bellmanOrderHom hmono lower) :=
  congrArg sInf <| Set.ext fun _ => bellman_le_iff.symm

/-- The least lax majorant is a fixed point of the Bellman operator. -/
theorem bellman_leastLaxMajorant (hmono : T.IsMonotone) (lower : ∀ vertex, Fiber vertex) :
    T.bellman lower (T.leastLaxMajorant lower) = T.leastLaxMajorant lower := by
  rw [leastLaxMajorant_eq_lfp hmono]
  exact (bellmanOrderHom hmono lower).map_lfp

/-- **Closure soundness.**  Concrete closure is bounded by the concretization of abstract
closure.  Here `T` is the abstract transport, `S` is the concrete transport, and `f` is
concretization.  The edge inequality of a lax morphism is the local soundness condition;
leastness of concrete closure turns it into the global comparison. -/
theorem LaxHom.leastLaxMajorant_le_map {Other : V → Type*}
    [∀ vertex : V, CompleteLattice (Other vertex)] {S : Transport G Other}
    (f : LaxHom T S) (hfmono : ∀ vertex, Monotone (f.app vertex)) (hTmono : T.IsMonotone)
    (lowerT : ∀ vertex, Fiber vertex) (lowerS : ∀ vertex, Other vertex)
    (hlower : lowerS ≤ f.mapFamily lowerT) :
    S.leastLaxMajorant lowerS ≤ f.mapFamily (T.leastLaxMajorant lowerT) :=
  leastLaxMajorant_le
    (fun vertex ↦ (hlower vertex).trans <| hfmono vertex (le_leastLaxMajorant lowerT vertex))
    (f.map_isLaxSection hfmono (isLaxSection_leastLaxMajorant hTmono lowerT))

/-! ### Path closure for supremum-preserving maps -/

variable (T)

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

/-- Supremum-preserving edge maps are monotone. -/
theorem PreservesSSup.isMonotone (hsup : T.PreservesSSup) : T.IsMonotone := by
  intro edge first second hle
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
theorem pathClosure_le_of_isLaxSection (hmono : T.IsMonotone)
    {lower family : ∀ vertex, Fiber vertex} (hlower : lower ≤ family)
    (hfamily : T.IsLaxSection family) : T.pathClosure lower ≤ family :=
  fun _ ↦ iSup_le fun source ↦ iSup_le fun walk ↦
    (hmono.walkMap walk (hlower source)).trans (hfamily.walkMap_le hmono walk)

/-- **Path-closure theorem.**  For supremum-preserving edge maps, the explicit join over all
forward walks is the least lax section dominating the prescribed lower data. -/
theorem pathClosure_isLeast (hsup : T.PreservesSSup) (lower : ∀ vertex, Fiber vertex) :
    IsLeast {family | lower ≤ family ∧ T.IsLaxSection family} (T.pathClosure lower) :=
  ⟨⟨T.le_pathClosure lower, isLaxSection_pathClosure hsup lower⟩,
    fun _ hfamily ↦ pathClosure_le_of_isLaxSection hsup.isMonotone hfamily.1 hfamily.2⟩

/-- **The path closure computes the least lax majorant.**  For supremum-preserving edge maps the
least fixed point of the Bellman operator is the join of the lower data transported along all
walks. -/
theorem pathClosure_eq_leastLaxMajorant (hsup : T.PreservesSSup)
    (lower : ∀ vertex, Fiber vertex) :
    T.pathClosure lower = T.leastLaxMajorant lower :=
  (pathClosure_isLeast hsup lower).unique (leastLaxMajorant_isLeast hsup.isMonotone lower)

/-- Transport of lower data along a walk of length `n` is below the `n`-th iterate of the
incoming join on that data. -/
theorem walkMap_le_iterate_incomingSup (hmono : T.IsMonotone) (lower : ∀ vertex, Fiber vertex)
    {start finish : V} (walk : G.Walk start finish) :
    T.walkMap walk (lower start) ≤ T.incomingSup^[walk.length] lower finish := by
  induction walk with
  | nil => exact le_rfl
  | concat edge walk ih =>
      rw [walkMap_concat, EdgeGraph.Walk.length_concat, Function.iterate_succ_apply']
      exact (hmono edge ih).trans (edgeMap_le_incomingSup _ edge)

/-- **Kleene iteration.**  For supremum-preserving edge maps, the path closure is the join of the
iterates of the incoming join on the lower data: its `n`-th iterate collects the walks of
length `n`. -/
theorem pathClosure_eq_iSup_iterate_incomingSup (hsup : T.PreservesSSup)
    (lower : ∀ vertex, Fiber vertex) :
    T.pathClosure lower = ⨆ n : ℕ, T.incomingSup^[n] lower := by
  refine le_antisymm (fun vertex ↦ iSup_le fun source ↦ iSup_le fun walk ↦ ?_) (iSup_le ?_)
  · rw [iSup_apply]
    exact le_iSup_of_le walk.length (walkMap_le_iterate_incomingSup hsup.isMonotone lower walk)
  · intro n
    induction n with
    | zero => exact T.le_pathClosure lower
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact (hsup.isMonotone.monotone_incomingSup ih).trans
          (isLaxSection_iff_incomingSup_le.1 (isLaxSection_pathClosure hsup lower))

/-- Every walk preserves bottom when all edge maps do. -/
theorem walkMap_bot (hbot : ∀ edge : E, T.edgeMap edge ⊥ = ⊥)
    {start finish : V} (walk : G.Walk start finish) :
    T.walkMap walk ⊥ = ⊥ := by
  induction walk with
  | nil => rfl
  | concat edge walk ih =>
      rw [walkMap_concat, ih]
      exact hbot edge

/-- **Synchronized-loop closure.**  If one point is pre-fixed by every loop at the root, path
closure of the lower data concentrated at the root, `Function.update ⊥ base point`, returns
exactly that point at the root.  Separate cycle-dependent witnesses would not suffice for this
argument. -/
theorem pathClosure_update_bot_self
    [DecidableEq V] (hsup : T.PreservesSSup)
    (base : V) (point : Fiber base)
    (hcycle : ∀ cycle : G.Walk base base, T.holonomy cycle point ≤ point) :
    T.pathClosure (Function.update ⊥ base point) base = point := by
  apply le_antisymm
  · refine iSup_le fun source ↦ iSup_le fun walk ↦ ?_
    by_cases hsource : source = base
    · subst source
      rw [Function.update_self]
      exact hcycle walk
    · rw [Function.update_of_ne hsource, Pi.bot_apply, T.walkMap_bot hsup.map_bot walk]
      exact bot_le
  · simpa using T.le_pathClosure (Function.update ⊥ base point) base

/-- The synchronized closure is the least lax section whose base value dominates the selected
common cycle witness. -/
theorem rooted_pathClosure_isLeast
    [DecidableEq V] (hsup : T.PreservesSSup) (base : V) (point : Fiber base) :
    IsLeast {family | point ≤ family base ∧ T.IsLaxSection family}
      (T.pathClosure (Function.update ⊥ base point)) := by
  simpa only [update_le_iff, Pi.bot_apply, bot_le, implies_true, and_true] using
    pathClosure_isLeast hsup (Function.update ⊥ base point)

end CompleteLattice

end Transport
end Maths

end
