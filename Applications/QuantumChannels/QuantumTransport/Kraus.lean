/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.Mixed.Order
public import Mathlib.Analysis.Matrix.Order

/-!
# Transport by Kraus maps

A finite Kraus family from one coordinate space to another defines a positive
map between their matrix algebras. These maps preserve the Löwner order and
therefore label a directed transport whose lax and oplax constraints propagate
along walks of a compatible polarity.

The input and output coordinate types may differ.

## Main definitions

* `QuantumTransport.PositiveMatrix` - the positive semidefinite cone with its
  inherited Löwner order.
* `QuantumTransport.krausMap` - the heterogeneous Kraus map associated to a
  finite family of operators.
* `QuantumTransport.positiveKrausMap` - the induced map between positive cones.
* `QuantumTransport.ofKrausFamily` - the transport labelled by edgewise Kraus
  families.
* `QuantumTransport.ofKrausFamilyOnPositiveCone` - the corresponding transport
  on positive cones.

## Main results

* `QuantumTransport.krausMap_posSemidef` - preservation of positive
  semidefiniteness.
* `QuantumTransport.monotone_krausMap` - monotonicity for the Löwner order.
* `QuantumTransport.monotone_positiveKrausMap` - monotonicity on positive cones.
* `QuantumTransport.walkMap_le_of_lax_or_exact` - lower-bound propagation along
  compatible walks.
* `QuantumTransport.le_walkMap_of_oplax_or_exact` - upper-bound propagation
  along compatible walks.

## Implementation notes

The fiber order is Mathlib's matrix order. No lattice operations are used;
the proofs require only positivity, monotonicity, and the relation-parametric
mixed-walk calculus.

## Tags

completely positive map, Kraus map, directed transport, Löwner order, mixed section
-/

@[expose] public section

namespace QuantumTransport

open Maths Matrix
open scoped ComplexOrder MatrixOrder

universe uI uO uK uV uE uW

variable {I : Type uI} {O : Type uO} {κ : Type uK}
variable [Fintype I] [Fintype κ]

/-- Positive semidefinite matrices, ordered by the inherited Löwner order. -/
abbrev PositiveMatrix (n : Type*) [Fintype n] :=
  {X : Matrix n n ℂ // X.PosSemidef}

/-- The positive map `X ↦ ∑ a, K a * X * (K a)ᴴ` associated to a finite
heterogeneous Kraus family. -/
def krausMap (K : κ → Matrix O I ℂ) (X : Matrix I I ℂ) : Matrix O O ℂ :=
  ∑ a, K a * X * (K a)ᴴ

/-- A Kraus map preserves subtraction. -/
theorem krausMap_sub (K : κ → Matrix O I ℂ) (X Y : Matrix I I ℂ) :
    krausMap K (X - Y) = krausMap K X - krausMap K Y := by
  simp only [krausMap]
  conv_lhs =>
    enter [2, a]
    rw [Matrix.mul_sub, Matrix.sub_mul]
  exact Finset.sum_sub_distrib
    (f := fun a => K a * X * (K a)ᴴ)
    (g := fun a => K a * Y * (K a)ᴴ)

variable [Fintype O]

/-- A finite Kraus map preserves positive semidefiniteness. -/
theorem krausMap_posSemidef (K : κ → Matrix O I ℂ) {X : Matrix I I ℂ}
    (hX : X.PosSemidef) : (krausMap K X).PosSemidef := by
  rw [krausMap]
  exact (Finset.sum_nonneg fun a _ =>
    (hX.mul_mul_conjTranspose_same (K a)).nonneg).posSemidef

/-- A finite Kraus map is monotone for the Löwner order. -/
theorem monotone_krausMap (K : κ → Matrix O I ℂ) : Monotone (krausMap K) := by
  intro X Y hXY
  rw [Matrix.le_iff] at hXY ⊢
  rw [← krausMap_sub]
  exact krausMap_posSemidef K hXY

/-- The map induced by a Kraus family between positive semidefinite cones. -/
def positiveKrausMap (K : κ → Matrix O I ℂ) :
    PositiveMatrix I → PositiveMatrix O :=
  fun X => ⟨krausMap K X.1, krausMap_posSemidef K X.2⟩

/-- The induced Kraus map on positive cones is Löwner-monotone. -/
theorem monotone_positiveKrausMap (K : κ → Matrix O I ℂ) :
    Monotone (positiveKrausMap K) := by
  intro X Y hXY
  exact monotone_krausMap K hXY

section Transport

variable {V : Type uV} {E : Type uE} (G : EdgeGraph V E)
variable (W : V → Type uW) [∀ vertex, Fintype (W vertex)]
variable (κe : E → Type uK) [∀ edge, Fintype (κe edge)]

/-- The directed transport whose edge maps are the supplied Kraus maps. -/
def ofKrausFamily
    (K : (edge : E) →
      κe edge → Matrix (W (G.target edge)) (W (G.source edge)) ℂ) :
    Transport G (fun vertex => Matrix (W vertex) (W vertex) ℂ) where
  edgeMap edge := krausMap (K edge)

/-- The directed transport induced by edgewise Kraus maps on positive cones. -/
def ofKrausFamilyOnPositiveCone
    (K : (edge : E) →
      κe edge → Matrix (W (G.target edge)) (W (G.source edge)) ℂ) :
    Transport G (fun vertex => PositiveMatrix (W vertex)) where
  edgeMap edge := positiveKrausMap (K edge)

/-- Every edge map of `ofKrausFamily` is monotone for the Löwner order. -/
theorem monotone_edgeMap_ofKrausFamily
    (K : (edge : E) →
      κe edge → Matrix (W (G.target edge)) (W (G.source edge)) ℂ)
    (edge : E) : Monotone ((ofKrausFamily G W κe K).edgeMap edge) := by
  exact monotone_krausMap (K edge)

/-- Every positive-cone edge map induced by a Kraus family is monotone. -/
theorem monotone_edgeMap_ofKrausFamilyOnPositiveCone
    (K : (edge : E) →
      κe edge → Matrix (W (G.target edge)) (W (G.source edge)) ℂ)
    (edge : E) :
    Monotone ((ofKrausFamilyOnPositiveCone G W κe K).edgeMap edge) := by
  exact monotone_positiveKrausMap (K edge)

variable {G W κe}
variable {K : (edge : E) →
  κe edge → Matrix (W (G.target edge)) (W (G.source edge)) ℂ}
variable {mode : E → EdgeMode}
variable {family : ∀ vertex, Matrix (W vertex) (W vertex) ℂ}
variable {start finish : V}

/-- A mixed section transports a lower bound along every Kraus-labelled walk
whose edges are lax or exact. -/
theorem walkMap_le_of_lax_or_exact
    (hfamily : (ofKrausFamily G W κe K).IsMixedSection mode family)
    (walk : G.Walk start finish)
    (hmode : ∀ edge ∈ walk.edges, (mode edge).IsLaxOrExact) :
    (ofKrausFamily G W κe K).walkMap walk (family start) ≤ family finish := by
  exact hfamily.walkMap_le_of_lax_or_exact
    (monotone_edgeMap_ofKrausFamily G W κe K) walk hmode

/-- A mixed section transports an upper bound along every Kraus-labelled walk
whose edges are oplax or exact. -/
theorem le_walkMap_of_oplax_or_exact
    (hfamily : (ofKrausFamily G W κe K).IsMixedSection mode family)
    (walk : G.Walk start finish)
    (hmode : ∀ edge ∈ walk.edges, (mode edge).IsOplaxOrExact) :
    family finish ≤ (ofKrausFamily G W κe K).walkMap walk (family start) := by
  exact hfamily.le_walkMap_of_oplax_or_exact
    (monotone_edgeMap_ofKrausFamily G W κe K) walk hmode

end Transport

end QuantumTransport
