/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitube.Mixed.AdjointOrder
public import QuantumTransport.Kraus

/-!
# The discard channel has no order residual

The quantum discard operation sends a positive operator to its trace. In
finite coordinates it is a heterogeneous Kraus map from an arbitrary finite
system to a one-dimensional system. It is positive and monotone for the
Löwner order, but it has neither a left nor a right order adjoint on the
positive cones when the source has at least two coordinates.

The failed left adjoint is precisely the residual required to turn an oplax
transport edge into a reversed lax edge. Thus adjoint reversal is not
available for every completely positive map, even in finite dimension.

## Main definitions

* `QuantumTransport.PositiveMatrix` - the cone of positive semidefinite
  matrices with its inherited Löwner order.
* `QuantumTransport.coordinateProjection` - a coordinate projection.
* `QuantumTransport.traceDiscard` - the discard channel on positive cones.
* `QuantumTransport.discardKraus` - coordinate Kraus operators for discard.
* `QuantumTransport.discard` - the two-dimensional discard channel.
* `QuantumTransport.discardGraph` - the one-edge graph carrying discard.
* `QuantumTransport.discardTransport` - discard as transport.

## Main results

* `QuantumTransport.krausMap_discardKraus` - the Kraus formula equals the
  trace formula in arbitrary finite dimension.
* `QuantumTransport.traceDiscard_val_eq_krausMap` - the cone map is the
  restriction of the Kraus map.
* `QuantumTransport.trace_traceDiscard` - discard preserves the trace.
* `QuantumTransport.trace_discard` - the two-dimensional trace identity.
* `QuantumTransport.monotone_traceDiscard` - discard is Löwner-monotone.
* `QuantumTransport.not_exists_galoisConnection_traceDiscard` - discard has
  no left order adjoint in nontrivial dimension.
* `QuantumTransport.not_exists_galoisConnection_traceDiscard_right` - discard
  has no right order adjoint in nontrivial dimension.
* `QuantumTransport.not_exists_galoisConnection_discard` - discard has no
  left order adjoint.
* `QuantumTransport.not_exists_galoisConnection_discard_right` - discard has
  no right order adjoint.
* `QuantumTransport.not_exists_discardResidual` - the oplax discard edge has
  no residual suitable for laxification.

## Implementation notes

The obstruction is visible on the coordinate projections. Any proposed left
adjoint at the scalar identity must lie below every projection and hence
vanish. A proposed right adjoint must dominate two distinct projections,
contradicting its trace bound.

## Tags

quantum channel, discard, trace, Löwner order, Galois connection, residual
-/

@[expose] public section

namespace QuantumTransport

open Maths Matrix
open scoped ComplexOrder MatrixOrder

/-- The rank-one coordinate projection on the `i`-th coordinate. -/
def coordinateProjection {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    Matrix I I ℂ :=
  Matrix.diagonal fun j => if j = i then 1 else 0

/-- Every coordinate projection is positive semidefinite. -/
theorem coordinateProjection_posSemidef {I : Type*} [Fintype I] [DecidableEq I]
    (i : I) :
    (coordinateProjection i).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro j
  by_cases hji : j = i <;> simp [hji]

/-- A coordinate projection as a point in the positive cone. -/
def positiveCoordinateProjection {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    PositiveMatrix I :=
  ⟨coordinateProjection i, coordinateProjection_posSemidef i⟩

/-- The one-dimensional identity as a point in the positive cone. -/
def positiveOne : PositiveMatrix (Fin 1) :=
  ⟨1, Matrix.PosSemidef.one⟩

/-- The zero matrix as a point in a positive cone. -/
def positiveZero (n : Type*) [Fintype n] : PositiveMatrix n :=
  ⟨0, Matrix.PosSemidef.zero⟩

/-- The coordinate functionals as a Kraus family for the discard channel. -/
def discardKraus {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    Matrix (Fin 1) I ℂ :=
  Matrix.of fun _ j => if j = i then 1 else 0

/-- The heterogeneous Kraus map of `discardKraus` is the trace channel. -/
theorem krausMap_discardKraus {I : Type*} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) :
    krausMap (fun i => discardKraus i) X = Matrix.diagonal fun _ => X.trace := by
  ext i j
  have hi : i = 0 := Fin.eq_zero i
  have hj : j = 0 := Fin.eq_zero j
  subst i
  subst j
  rw [krausMap]
  rw [Matrix.diagonal_apply_eq]
  have hsum_apply :
      (∑ a : I, discardKraus a * X * (discardKraus a)ᴴ) 0 0 =
        ∑ a : I, (discardKraus a * X * (discardKraus a)ᴴ) 0 0 := by
    simp only [Matrix.sum_apply]
  rw [hsum_apply]
  simp_rw [Matrix.mul_apply]
  simp [discardKraus, Matrix.trace]

/-- The trace channel from finite positive matrices to the one-dimensional
positive cone. -/
def traceDiscard {I : Type*} [Fintype I] [DecidableEq I] (X : PositiveMatrix I) :
    PositiveMatrix (Fin 1) :=
  ⟨Matrix.diagonal fun _ => X.1.trace,
    Matrix.PosSemidef.diagonal fun _ => X.2.trace_nonneg⟩

/-- The two-dimensional instance of `traceDiscard` used by the transport
client below. -/
def discard (X : PositiveMatrix (Fin 2)) : PositiveMatrix (Fin 1) :=
  traceDiscard X

/-- The cone-valued discard map is the restriction of the heterogeneous
Kraus map to positive semidefinite inputs. -/
theorem traceDiscard_val_eq_krausMap {I : Type*} [Fintype I] [DecidableEq I]
    (X : PositiveMatrix I) :
    (traceDiscard X).1 = krausMap discardKraus X.1 := by
  exact (krausMap_discardKraus X.1).symm

/-- The two-dimensional cone map is the restriction of the Kraus map. -/
theorem discard_val_eq_krausMap (X : PositiveMatrix (Fin 2)) :
    (discard X).1 = krausMap discardKraus X.1 := by
  exact traceDiscard_val_eq_krausMap X

/-- Discard preserves the trace. -/
@[simp] theorem trace_traceDiscard {I : Type*} [Fintype I] [DecidableEq I]
    (X : PositiveMatrix I) :
    (traceDiscard X).1.trace = X.1.trace := by
  simp [traceDiscard, Matrix.trace]

/-- The two-dimensional discard channel preserves the trace. -/
@[simp] theorem trace_discard (X : PositiveMatrix (Fin 2)) :
    (discard X).1.trace = X.1.trace := by
  exact trace_traceDiscard X

/-- The discard channel is monotone for the Löwner order. -/
theorem monotone_traceDiscard {I : Type*} [Fintype I] [DecidableEq I] :
    Monotone (@traceDiscard I _ _) := by
  intro X Y hXY
  change X.1 ≤ Y.1 at hXY
  change (Matrix.diagonal fun _ => X.1.trace) ≤
    Matrix.diagonal fun _ => Y.1.trace
  rw [← krausMap_discardKraus, ← krausMap_discardKraus]
  exact monotone_krausMap discardKraus hXY

/-- The two-dimensional discard channel is Löwner-monotone. -/
theorem monotone_discard : Monotone discard := by
  exact monotone_traceDiscard

/-- Discard sends either coordinate projection to the scalar identity. -/
@[simp] theorem traceDiscard_positiveCoordinateProjection
    {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    traceDiscard (positiveCoordinateProjection i) = positiveOne := by
  apply Subtype.ext
  ext j k
  fin_cases j
  fin_cases k
  simp [traceDiscard, positiveCoordinateProjection, coordinateProjection,
    positiveOne, Matrix.trace]

/-- The two-dimensional discard channel sends either coordinate projection
to the scalar identity. -/
@[simp] theorem discard_positiveCoordinateProjection (i : Fin 2) :
    discard (positiveCoordinateProjection i) = positiveOne := by
  exact traceDiscard_positiveCoordinateProjection i

/-- Discard sends the zero operator to the zero scalar. -/
@[simp] theorem traceDiscard_positiveZero {I : Type*} [Fintype I] [DecidableEq I] :
    traceDiscard (positiveZero I) = positiveZero (Fin 1) := by
  apply Subtype.ext
  ext i j
  fin_cases i
  fin_cases j
  simp [traceDiscard, positiveZero, Matrix.trace]

/-- The two-dimensional discard channel sends zero to zero. -/
@[simp] theorem discard_positiveZero :
    discard (positiveZero (Fin 2)) = positiveZero (Fin 1) := by
  exact traceDiscard_positiveZero

private theorem le_all_coordinateProjections_eq_zero
    {I : Type*} [Fintype I] [DecidableEq I] [Nontrivial I]
    {X : PositiveMatrix I}
    (hproj : ∀ i : I, X ≤ positiveCoordinateProjection i) :
    X = positiveZero I := by
  apply Subtype.ext
  change X.1 = 0
  apply X.2.trace_eq_zero_iff.mp
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro i hi
  have hnonneg : 0 ≤ X.1 i i := X.2.diag_nonneg
  obtain ⟨j, hji⟩ := exists_ne i
  have hdiag := (Matrix.le_iff.mp (hproj j)).diag_nonneg (i := i)
  have hnonpos : X.1 i i ≤ 0 := by
    simpa [positiveCoordinateProjection, coordinateProjection, hji.symm] using hdiag
  exact le_antisymm hnonpos hnonneg

private theorem not_positiveOne_le_positiveZero :
    ¬ positiveOne ≤ positiveZero (Fin 1) := by
  intro h
  have hreverse : positiveZero (Fin 1) ≤ positiveOne := by
    exact Matrix.PosSemidef.one.nonneg
  have hone : (positiveOne : PositiveMatrix (Fin 1)).1 =
      (positiveZero (Fin 1)).1 :=
    congrArg Subtype.val (le_antisymm h hreverse)
  have : (1 : ℂ) = 0 := by
    simpa [positiveOne, positiveZero] using congrFun (congrFun hone 0) 0
  exact one_ne_zero this

/-- The trace discard channel has no left order adjoint in nontrivial finite
dimension. -/
theorem not_exists_galoisConnection_traceDiscard
    {I : Type*} [Fintype I] [DecidableEq I] [Nontrivial I] :
    ¬ ∃ residual : PositiveMatrix (Fin 1) → PositiveMatrix I,
      GaloisConnection residual traceDiscard := by
  apply Maths.Transport.not_exists_galoisConnection_left_of_witnesses
    traceDiscard positiveOne positiveCoordinateProjection
  · intro i
    simp
  · intro X hproj hbound
    have hzero := le_all_coordinateProjections_eq_zero hproj
    exact not_positiveOne_le_positiveZero (by simpa [hzero] using hbound)

/-- The two-dimensional discard channel has no left order adjoint. -/
theorem not_exists_galoisConnection_discard :
    ¬ ∃ residual : PositiveMatrix (Fin 1) → PositiveMatrix (Fin 2),
      GaloisConnection residual discard := by
  change ¬ ∃ residual : PositiveMatrix (Fin 1) → PositiveMatrix (Fin 2),
    GaloisConnection residual (@traceDiscard (Fin 2) _ _)
  exact not_exists_galoisConnection_traceDiscard (I := Fin 2)

/-- The trace discard channel has no right order adjoint in nontrivial
finite dimension. -/
theorem not_exists_galoisConnection_traceDiscard_right
    {I : Type*} [Fintype I] [DecidableEq I] [Nontrivial I] :
    ¬ ∃ residual : PositiveMatrix (Fin 1) → PositiveMatrix I,
      GaloisConnection traceDiscard residual := by
  apply Maths.Transport.not_exists_galoisConnection_right_of_witnesses
    traceDiscard positiveOne positiveCoordinateProjection
  · intro i
    simp
  · intro X hproj hbound
    have hdiag : ∀ i : I, (1 : ℂ) ≤ X.1 i i := by
      intro i
      have hdiag := (Matrix.le_iff.mp (hproj i)).diag_nonneg (i := i)
      simpa [positiveCoordinateProjection, coordinateProjection] using hdiag
    have hcard : (2 : ℂ) ≤ Fintype.card I := by
      exact_mod_cast (Nat.succ_le_iff.mpr Fintype.one_lt_card)
    have htraceLower : (Fintype.card I : ℂ) ≤ X.1.trace := by
      calc
        (Fintype.card I : ℂ) = ∑ _ : I, (1 : ℂ) := by simp
        _ ≤ ∑ i : I, X.1 i i := Finset.sum_le_sum fun i _ => hdiag i
        _ = X.1.trace := by rfl
    have htraceUpper : X.1.trace ≤ (1 : ℂ) := by
      have hdiag := (Matrix.le_iff.mp hbound).diag_nonneg (i := (0 : Fin 1))
      simpa [traceDiscard, positiveOne] using hdiag
    have : (2 : ℂ) ≤ 1 := hcard.trans (htraceLower.trans htraceUpper)
    norm_num at this

/-- The two-dimensional discard channel has no right order adjoint. -/
theorem not_exists_galoisConnection_discard_right :
    ¬ ∃ residual : PositiveMatrix (Fin 1) → PositiveMatrix (Fin 2),
      GaloisConnection discard residual := by
  change ¬ ∃ residual : PositiveMatrix (Fin 1) → PositiveMatrix (Fin 2),
    GaloisConnection (@traceDiscard (Fin 2) _ _) residual
  exact not_exists_galoisConnection_traceDiscard_right (I := Fin 2)

/-- The graph with one edge from the two-dimensional system to the
one-dimensional system. -/
def discardGraph : EdgeGraph Bool Unit where
  source _ := false
  target _ := true

/-- Positive matrix fibers for the source and target of `discardGraph`. -/
def discardFiber : Bool → Type
  | false => PositiveMatrix (Fin 2)
  | true => PositiveMatrix (Fin 1)

/-- The Löwner relation on each discard fiber. -/
def discardOrder : (vertex : Bool) →
    discardFiber vertex → discardFiber vertex → Prop
  | false => fun first second => first.1 ≤ second.1
  | true => fun first second => first.1 ≤ second.1

/-- The one-edge transport whose edge map is discard. -/
def discardTransport : Transport discardGraph discardFiber where
  edgeMap _ := discard

/-- The discard edge is assigned oplax polarity. -/
def discardMode : Unit → EdgeMode :=
  fun _ => .oplax

/-- The oplax discard edge admits no residual family satisfying the reversal
law used by transport laxification. -/
theorem not_exists_discardResidual :
    ¬ ∃ residual : ∀ edge : Transport.LaxificationReverseEdge discardMode,
        discardFiber (discardGraph.target edge.1) →
          discardFiber (discardGraph.source edge.1),
      discardTransport.IsResidualFor discardOrder discardMode residual := by
  rintro ⟨residual, hresidual⟩
  apply not_exists_galoisConnection_discard
  refine ⟨fun target => residual ⟨(), Or.inl rfl⟩ target, ?_⟩
  intro target source
  change (residual ⟨(), Or.inl rfl⟩ target).1 ≤ source.1 ↔
    target.1 ≤ (discard source).1
  simpa [discardGraph, discardFiber, discardOrder, discardTransport,
    discardMode] using (hresidual ⟨(), Or.inl rfl⟩ source target).symm

end QuantumTransport
