/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitube.Closure
public import Maths.Multitube.Mixed.AdjointOrder
public import Mathlib.Data.Rel
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Relational dilation and erosion

For a relation from one signal space to another, `SetRel.image` is existential dilation and
`SetRel.core` is universal erosion.  Their Galois connection is the order-theoretic mechanism
that turns an oplax erosion constraint into a lax dilation constraint on the reversed graph.
The signal spaces may depend on graph vertices, so heterogeneous multiresolution signals are
allowed.

Relational images preserve arbitrary unions.  Consequently the direct path-closure theorem
applies to dilation transport and computes the least inductive signal family above lower data.

## Main definitions

* `MathematicalMorphology.erosionTransport` - transport by relation cores on reversed edges.
* `MathematicalMorphology.dilationTransport` - transport by relation images.
* `MathematicalMorphology.dilationSupHom` - arbitrary-supremum homomorphisms for dilation.
* `MathematicalMorphology.universalRelation` - the concrete nonfunctional relation.

## Main results

* `MathematicalMorphology.mixedErosionLaxification_iff` - mixed erosion constraints are
  equivalent to lax dilation constraints after edge reversal.
* `MathematicalMorphology.leastDilationEnvelope` - the least dilation-invariant envelope.
* `MathematicalMorphology.universal_core_image_not_inverse` - the concrete relation has a
  strict core-after-image expansion.
* `MathematicalMorphology.universalRelation_not_functional` - the concrete relation is not a
  function graph.

## Tags

mathematical morphology, dilation, erosion, relation, transport, path closure
-/

@[expose] public section

noncomputable section

namespace MathematicalMorphology

open Maths

universe uV uE uS

variable {V : Type uV} {E : Type uE}
variable {Signal : V → Type uS}

/-- Erosion transport on the reversed graph.  The original edge relation runs from source
signals to target signals, while its core runs backwards from target predicates to source
predicates. -/
def erosionTransport (G : EdgeGraph V E)
    (relation : (edge : E) →
      SetRel (Signal (G.source edge)) (Signal (G.target edge))) :
    Transport G.reverse (fun vertex => Set (Signal vertex)) where
  edgeMap edge := SetRel.core (relation edge)

/-- Dilation transport on the original graph. -/
def dilationTransport (G : EdgeGraph V E)
    (relation : (edge : E) →
      SetRel (Signal (G.source edge)) (Signal (G.target edge))) :
    Transport G (fun vertex => Set (Signal vertex)) where
  edgeMap edge := SetRel.image (relation edge)

variable {G : EdgeGraph V E}
variable {relation : (edge : E) →
  SetRel (Signal (G.source edge)) (Signal (G.target edge))}
variable {mode : E → EdgeMode}
variable {family : ∀ vertex, Set (Signal vertex)}

/-- Dilation is the residual of erosion on every reversed edge. -/
def dilationResidual (G : EdgeGraph V E)
    (relation : (edge : E) →
      SetRel (Signal (G.source edge)) (Signal (G.target edge)))
    (mode : E → EdgeMode) :
    ∀ _edge : Transport.LaxificationReverseEdge mode,
      Set (Signal (G.source _edge.1)) → Set (Signal (G.target _edge.1)) :=
  fun edge => SetRel.image (relation edge.1)

/-- Mixed erosion constraints become lax dilation constraints after edge reversal. -/
theorem mixedErosionLaxification_iff
    (G : EdgeGraph V E)
    (relation : (edge : E) →
      SetRel (Signal (G.source edge)) (Signal (G.target edge)))
    (mode : E → EdgeMode) (family : ∀ vertex, Set (Signal vertex)) :
    (erosionTransport G relation).IsMixedSection mode family ↔
      ((erosionTransport G relation).laxification mode
        (dilationResidual G relation mode)).IsLaxSection family := by
  apply Transport.isMixedSection_iff_laxification_of_galoisConnection
  intro edge
  exact SetRel.image_core_gc

/-- A relational dilation preserves arbitrary joins of signal predicates. -/
def dilationSupHom
    {X : Type*} {Y : Type*} (relation : SetRel X Y) :
    sSupHom (Set X) (Set Y) where
  toFun := relation.image
  map_sSup' := by
    intro sets
    change relation.image (⋃₀ sets) = ⋃₀ (relation.image '' sets)
    rw [relation.image_sUnion]
    simp only [Set.sUnion_image]

/-- The least lax dilation family containing prescribed lower signal data. -/
theorem leastDilationEnvelope
    (G : EdgeGraph V E)
    (relation : (edge : E) →
      SetRel (Signal (G.source edge)) (Signal (G.target edge)))
    (lower : ∀ vertex, Set (Signal vertex)) :
    (dilationTransport G relation).IsLaxSection
        ((dilationTransport G relation).pathClosure lower) ∧
      (∀ vertex, lower vertex ≤
        (dilationTransport G relation).pathClosure lower vertex) ∧
      ∀ family : ∀ vertex, Set (Signal vertex),
        (dilationTransport G relation).IsLaxSection family →
        (∀ vertex, lower vertex ≤ family vertex) →
        ∀ vertex,
          (dilationTransport G relation).pathClosure lower vertex ≤ family vertex := by
  apply (dilationTransport G relation).pathClosure_isLeast_of_sSupHom
    (fun edge => dilationSupHom (relation edge))
  intro edge point
  rfl

/-! ## A nonfunctional relational example -/

/-- The relation relating every Boolean signal to every Boolean signal. -/
def universalRelation : SetRel Bool Bool := Set.univ

/-- The universal relation is genuinely nonfunctional. -/
theorem universalRelation_not_functional :
    ¬ ∀ x : Bool, ∃! y : Bool, (x, y) ∈ universalRelation := by
  intro h
  obtain ⟨y, -, hunique⟩ := h false
  have htrue : true = y := hunique true (by simp [universalRelation])
  have hfalse : false = y := hunique false (by simp [universalRelation])
  cases htrue.trans hfalse.symm

/-- The universal relation fails right uniqueness, so one input has two outputs. -/
theorem universalRelation_not_rightUnique :
    ¬ Relator.RightUnique (fun x y : Bool => (x, y) ∈ universalRelation) := by
  intro h
  have heq := h (a := false) (b := false) (c := true)
    (by simp [universalRelation]) (by simp [universalRelation])
  cases heq

/-- Universal relational dilation and erosion are not inverse operations. -/
theorem universal_core_image_not_inverse :
    universalRelation.core (universalRelation.image ({true} : Set Bool)) ≠
      ({true} : Set Bool) := by
  intro heq
  have hfalse : false ∈
      universalRelation.core (universalRelation.image ({true} : Set Bool)) := by
    simp [universalRelation]
  rw [heq] at hfalse
  simp at hfalse

end MathematicalMorphology

end
