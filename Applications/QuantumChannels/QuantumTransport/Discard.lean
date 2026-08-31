/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.Mixed.Adjoint
public import QuantumTransport.Kraus

/-!
# The discard channel has no order residual

The quantum discard operation sends a positive operator to its trace. In
finite coordinates it is a heterogeneous Kraus map from a two-dimensional
system to a one-dimensional system. It is positive and monotone for the
Löwner order, but it has neither a left nor a right order adjoint on the
positive cones.

The failed left adjoint is precisely the residual required to turn an oplax
transport edge into a reversed lax edge. Thus adjoint reversal is not
available for every completely positive map, even in finite dimension.

## Main definitions

* `QuantumTransport.PositiveMatrix` - the cone of positive semidefinite
  matrices with its inherited Löwner order.
* `QuantumTransport.discardKraus` - coordinate Kraus operators for discard.
* `QuantumTransport.discard` - the discard channel on positive cones.
* `QuantumTransport.discardGraph` - the one-edge graph carrying discard.
* `QuantumTransport.discardTransport` - discard as directed transport.

## Main results

* `QuantumTransport.krausMap_discardKraus` - the Kraus formula equals the
  trace formula.
* `QuantumTransport.discard_val_eq_krausMap` - the cone map is the restriction
  of the Kraus map.
* `QuantumTransport.trace_discard` - discard preserves the trace.
* `QuantumTransport.monotone_discard` - discard is Löwner-monotone.
* `QuantumTransport.not_exists_galoisConnection_discard` - discard has no
  left order adjoint.
* `QuantumTransport.not_exists_galoisConnection_discard_right` - discard has
  no right order adjoint.
* `QuantumTransport.not_exists_discardResidual` - the oplax discard edge has
  no residual suitable for laxification.

## Implementation notes

The obstruction is already visible on the two orthogonal coordinate
projections. Any proposed left adjoint at the scalar identity must lie below
both projections and hence vanish. A proposed right adjoint must dominate
both projections, contradicting its trace bound.

## Tags

quantum channel, discard, trace, Löwner order, Galois connection, residual
-/

@[expose] public section

namespace QuantumTransport

open Maths Matrix
open scoped ComplexOrder MatrixOrder

/-- The rank-one coordinate projection on the `i`-th coordinate. -/
def coordinateProjection (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun j => if j = i then 1 else 0

/-- Every coordinate projection is positive semidefinite. -/
theorem coordinateProjection_posSemidef (i : Fin 2) :
    (coordinateProjection i).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro j
  by_cases hji : j = i <;> simp [hji]

/-- A coordinate projection as a point in the positive cone. -/
def positiveCoordinateProjection (i : Fin 2) : PositiveMatrix (Fin 2) :=
  ⟨coordinateProjection i, coordinateProjection_posSemidef i⟩

/-- The one-dimensional identity as a point in the positive cone. -/
def positiveOne : PositiveMatrix (Fin 1) :=
  ⟨1, Matrix.PosSemidef.one⟩

/-- The zero matrix as a point in a positive cone. -/
def positiveZero (n : Type*) [Fintype n] : PositiveMatrix n :=
  ⟨0, Matrix.PosSemidef.zero⟩

/-- The two coordinate functionals as Kraus operators for the discard
channel. -/
def discardKraus (i : Fin 2) : Matrix (Fin 1) (Fin 2) ℂ :=
  Matrix.of fun _ j => if j = i then 1 else 0

/-- The heterogeneous Kraus map of `discardKraus` is the trace channel. -/
theorem krausMap_discardKraus (X : Matrix (Fin 2) (Fin 2) ℂ) :
    krausMap discardKraus X = Matrix.diagonal fun _ => X.trace := by
  ext i j
  fin_cases i
  fin_cases j
  simp [krausMap, discardKraus, Matrix.mul_apply, Matrix.trace]

/-- The trace channel from two-dimensional positive matrices to the
one-dimensional positive cone. -/
def discard (X : PositiveMatrix (Fin 2)) : PositiveMatrix (Fin 1) :=
  ⟨Matrix.diagonal fun _ => X.1.trace,
    Matrix.PosSemidef.diagonal fun _ => X.2.trace_nonneg⟩

/-- The cone-valued discard map is the restriction of the heterogeneous
Kraus map to positive semidefinite inputs. -/
theorem discard_val_eq_krausMap (X : PositiveMatrix (Fin 2)) :
    (discard X).1 = krausMap discardKraus X.1 := by
  exact (krausMap_discardKraus X.1).symm

/-- Discard preserves the trace. -/
@[simp] theorem trace_discard (X : PositiveMatrix (Fin 2)) :
    (discard X).1.trace = X.1.trace := by
  simp [discard, Matrix.trace]

/-- The discard channel is monotone for the Löwner order. -/
theorem monotone_discard : Monotone discard := by
  intro X Y hXY
  change X.1 ≤ Y.1 at hXY
  change (Matrix.diagonal fun _ => X.1.trace) ≤
    Matrix.diagonal fun _ => Y.1.trace
  rw [← krausMap_discardKraus, ← krausMap_discardKraus]
  exact monotone_krausMap discardKraus hXY

/-- Discard sends either coordinate projection to the scalar identity. -/
@[simp] theorem discard_positiveCoordinateProjection (i : Fin 2) :
    discard (positiveCoordinateProjection i) = positiveOne := by
  apply Subtype.ext
  ext j k
  fin_cases j
  fin_cases k
  simp [discard, positiveCoordinateProjection, coordinateProjection,
    positiveOne, Matrix.trace]

/-- Discard sends the zero operator to the zero scalar. -/
@[simp] theorem discard_positiveZero :
    discard (positiveZero (Fin 2)) = positiveZero (Fin 1) := by
  apply Subtype.ext
  ext i j
  fin_cases i
  fin_cases j
  simp [discard, positiveZero, Matrix.trace]

private theorem le_both_coordinateProjections_eq_zero
    {X : PositiveMatrix (Fin 2)}
    (hfirst : X ≤ positiveCoordinateProjection 0)
    (hsecond : X ≤ positiveCoordinateProjection 1) :
    X = positiveZero (Fin 2) := by
  have hx0_nonneg : 0 ≤ X.1 0 0 := X.2.diag_nonneg
  have hx1_nonneg : 0 ≤ X.1 1 1 := X.2.diag_nonneg
  have hx0_nonpos : X.1 0 0 ≤ 0 := by
    have hdiag := (Matrix.le_iff.mp hsecond).diag_nonneg (i := (0 : Fin 2))
    simpa [positiveCoordinateProjection, coordinateProjection] using hdiag
  have hx1_nonpos : X.1 1 1 ≤ 0 := by
    have hdiag := (Matrix.le_iff.mp hfirst).diag_nonneg (i := (1 : Fin 2))
    simpa [positiveCoordinateProjection, coordinateProjection] using hdiag
  have hx0 : X.1 0 0 = 0 := le_antisymm hx0_nonpos hx0_nonneg
  have hx1 : X.1 1 1 = 0 := le_antisymm hx1_nonpos hx1_nonneg
  apply Subtype.ext
  change X.1 = 0
  apply X.2.trace_eq_zero_iff.mp
  simp [Matrix.trace, hx0, hx1]

/-- The discard channel has no left order adjoint. -/
theorem not_exists_galoisConnection_discard :
    ¬ ∃ residual : PositiveMatrix (Fin 1) → PositiveMatrix (Fin 2),
      GaloisConnection residual discard := by
  rintro ⟨residual, hadjoint⟩
  have hfirst : residual positiveOne ≤ positiveCoordinateProjection 0 :=
    (hadjoint positiveOne (positiveCoordinateProjection 0)).mpr (by simp)
  have hsecond : residual positiveOne ≤ positiveCoordinateProjection 1 :=
    (hadjoint positiveOne (positiveCoordinateProjection 1)).mpr (by simp)
  have hzero : residual positiveOne = positiveZero (Fin 2) :=
    le_both_coordinateProjections_eq_zero hfirst hsecond
  have himpossible : positiveOne ≤ discard (positiveZero (Fin 2)) :=
    (hadjoint positiveOne (positiveZero (Fin 2))).mp (by rw [hzero])
  rw [discard_positiveZero] at himpossible
  have hreverse : positiveZero (Fin 1) ≤ positiveOne := by
    exact Matrix.PosSemidef.one.nonneg
  have hone : (positiveOne : PositiveMatrix (Fin 1)).1 =
      (positiveZero (Fin 1)).1 :=
    congrArg Subtype.val (le_antisymm himpossible hreverse)
  have : (1 : ℂ) = 0 := by
    simpa [positiveOne, positiveZero] using congrFun (congrFun hone 0) 0
  exact one_ne_zero this

/-- The discard channel has no right order adjoint. -/
theorem not_exists_galoisConnection_discard_right :
    ¬ ∃ residual : PositiveMatrix (Fin 1) → PositiveMatrix (Fin 2),
      GaloisConnection discard residual := by
  rintro ⟨residual, hadjoint⟩
  have hfirst : positiveCoordinateProjection 0 ≤ residual positiveOne :=
    (hadjoint (positiveCoordinateProjection 0) positiveOne).mp (by simp)
  have hsecond : positiveCoordinateProjection 1 ≤ residual positiveOne :=
    (hadjoint (positiveCoordinateProjection 1) positiveOne).mp (by simp)
  have hdiag0 : (1 : ℂ) ≤ (residual positiveOne).1 0 0 := by
    have hdiag := (Matrix.le_iff.mp hfirst).diag_nonneg (i := (0 : Fin 2))
    simpa [positiveCoordinateProjection, coordinateProjection] using hdiag
  have hdiag1 : (1 : ℂ) ≤ (residual positiveOne).1 1 1 := by
    have hdiag := (Matrix.le_iff.mp hsecond).diag_nonneg (i := (1 : Fin 2))
    simpa [positiveCoordinateProjection, coordinateProjection] using hdiag
  have htraceLower : (2 : ℂ) ≤ (residual positiveOne).1.trace := by
    calc
      (2 : ℂ) = 1 + 1 := by norm_num
      _ ≤ (residual positiveOne).1 0 0 + (residual positiveOne).1 1 1 :=
        add_le_add hdiag0 hdiag1
      _ = (residual positiveOne).1.trace := by simp [Matrix.trace]
  have hdiscardUpper : discard (residual positiveOne) ≤ positiveOne :=
    (hadjoint (residual positiveOne) positiveOne).mpr le_rfl
  have htraceUpper : (residual positiveOne).1.trace ≤ (1 : ℂ) := by
    have hdiag :=
      (Matrix.le_iff.mp hdiscardUpper).diag_nonneg (i := (0 : Fin 1))
    simpa [discard, positiveOne] using hdiag
  have : (2 : ℂ) ≤ 1 := htraceLower.trans htraceUpper
  norm_num at this

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

/-- The one-edge directed transport whose edge map is discard. -/
def discardTransport : Transport discardGraph discardFiber where
  edgeMap _ := discard

/-- The discard edge is assigned oplax polarity. -/
def discardMode : Unit → EdgeMode :=
  fun _ => .oplax

/-- The oplax discard edge admits no residual family satisfying the reversal
law used by directed-transport laxification. -/
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
