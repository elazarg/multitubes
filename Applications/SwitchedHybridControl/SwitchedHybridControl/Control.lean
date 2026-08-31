/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.DirectedTransport.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Data.Fin.Basic

/-!
# Storage certificates for switched and hybrid transitions

A physical transition maps a state in its source mode to a state in its target mode.  A storage
certificate compares the target value after that transition with the source value, while
charging the edge by an additive decrease.  The associated value transport reads the physical
graph backwards and pulls the target value back, so the certificate is a lax section.  The
construction permits dependent state spaces and arbitrary, including noninjective, transitions.

## Main definitions

* `SwitchedHybridControl.storageTransport` - the value transport associated to a physical
  transport and edge decreases.
* `SwitchedHybridControl.pullbackTransport` - the uncharged pullback value transport.
* `SwitchedHybridControl.IsStorageCertificate` - the pointwise storage inequality.
* `SwitchedHybridControl.IsLyapunovFamily` - the zero-cost specialization of storage
  certification.
* `SwitchedHybridControl.ExampleMode` and `SwitchedHybridControl.ExampleEdge` - the concrete
  two-mode graph data.
* `SwitchedHybridControl.exampleEnergy` - the concrete mode-dependent energy family.

## Main results

* `SwitchedHybridControl.storageCertificate_iff_isLaxSection` - storage certification is a lax
  section on the reversed value transport.
* `SwitchedHybridControl.isLyapunovFamily_iff_isLaxSection` - the zero-cost lax-section
  characterization.
* `SwitchedHybridControl.walk_storage_nonincrease` and
  `SwitchedHybridControl.closedWalk_storage_nonincrease` - accumulated decrease along physical
  walks and closed walks.
* `SwitchedHybridControl.not_exists_fixedPoint_holonomy_of_pos_walkSum` - a positive-cost
  closed walk cannot fix a state under physical holonomy.
* `SwitchedHybridControl.exampleEnergy_certified` - certification of the concrete family.
* `SwitchedHybridControl.exampleReset_noninjective` - noninjectivity of the concrete reset.
* `SwitchedHybridControl.exampleCycle_strict_decrease` - strict decrease around a concrete
  closed physical cycle at state `1`.

## Tags

switched systems, hybrid systems, Lyapunov function, storage function, pullback, reset,
dependent state space, directed transport
-/

@[expose] public section

namespace SwitchedHybridControl

universe uV uE uS uA

variable {V : Type uV} {E : Type uE} {A : Type uA} {State : V → Type uS}

/-! ## Generic certificate transports -/

/-- Pull values back along a physical transport, on the reversed graph. -/
def pullbackTransport {G : Maths.EdgeGraph V E}
    (T : Maths.Transport G State) :
    Maths.Transport G.reverse (fun vertex => State vertex → A) where
  edgeMap edge := fun value point => value (T.edgeMap edge point)

/-- Add an edge decrease after pulling a target value back to its source state space. -/
def storageTransport [Add A] {G : Maths.EdgeGraph V E}
    (T : Maths.Transport G State) (decrease : E → A) :
    Maths.Transport G.reverse (fun vertex => State vertex → A) where
  edgeMap edge := fun value point => value (T.edgeMap edge point) + decrease edge

/-- The pointwise storage inequality on a physical transport. -/
def IsStorageCertificate [Add A] [LE A] {G : Maths.EdgeGraph V E}
    (T : Maths.Transport G State) (decrease : E → A)
    (storage : (vertex : V) → State vertex → A) : Prop :=
  ∀ edge point,
    storage (G.target edge) (T.edgeMap edge point) + decrease edge ≤
      storage (G.source edge) point

/-- Zero-cost storage certification, commonly called a Lyapunov family. -/
def IsLyapunovFamily [Zero A] [Add A] [LE A] {G : Maths.EdgeGraph V E}
    (T : Maths.Transport G State) (storage : (vertex : V) → State vertex → A) : Prop :=
  IsStorageCertificate T (fun _ => 0) storage

/-- Storage certification is exactly a lax section on the reversed value transport. -/
theorem storageCertificate_iff_isLaxSection [Add A] [LE A]
    {G : Maths.EdgeGraph V E} (T : Maths.Transport G State) (decrease : E → A)
    (storage : (vertex : V) → State vertex → A) :
    IsStorageCertificate T decrease storage ↔
      (storageTransport T decrease).IsLaxSection storage := by
  rfl

/-- Zero-cost certification is a lax section on the reversed value transport. -/
theorem isLyapunovFamily_iff_isLaxSection [Zero A] [Add A] [LE A]
    {G : Maths.EdgeGraph V E} (T : Maths.Transport G State)
    (storage : (vertex : V) → State vertex → A) :
    IsLyapunovFamily T storage ↔
      (storageTransport T (fun _ => 0)).IsLaxSection storage := by
  exact storageCertificate_iff_isLaxSection T (fun _ => 0) storage

/-- Uncharged pullback is monotone on pointwise ordered values. -/
theorem pullbackTransport_edgeMap_monotone [Preorder A]
    {G : Maths.EdgeGraph V E} (T : Maths.Transport G State) :
    ∀ edge : E, Monotone ((pullbackTransport (A := A) T).edgeMap edge) := by
  intro edge value other hvalue point
  exact hvalue (T.edgeMap edge point)

/-- Charged pullback is monotone on pointwise ordered values. -/
theorem storageTransport_edgeMap_monotone [AddCommMonoid A] [Preorder A] [IsOrderedAddMonoid A]
    {G : Maths.EdgeGraph V E} (T : Maths.Transport G State) (decrease : E → A) :
    ∀ edge : E, Monotone ((storageTransport (A := A) T decrease).edgeMap edge) := by
  intro edge value other hvalue point
  change value (T.edgeMap edge point) + decrease edge ≤
    other (T.edgeMap edge point) + decrease edge
  exact add_le_add_left (hvalue (T.edgeMap edge point)) _

/-- A storage certificate gives the accumulated physical-walk inequality. -/
theorem walk_storage_nonincrease [AddCommMonoid A] [Preorder A]
    [IsOrderedAddMonoid A] {G : Maths.EdgeGraph V E} (T : Maths.Transport G State)
    (decrease : E → A) (storage : (vertex : V) → State vertex → A)
    (hstorage : IsStorageCertificate T decrease storage)
    {start finish : V} (walk : G.Walk start finish) :
    ∀ point,
      storage finish (T.walkMap walk point) + Maths.walkSum decrease walk ≤
        storage start point := by
  induction walk with
  | nil =>
      intro point
      simp
  | concat walkSoFar edge legal ih =>
      intro point
      cases legal
      have hedge := hstorage edge
        (Maths.fiberCast State rfl (T.walkMap walkSoFar point))
      have hsum := add_le_add_left hedge (Maths.walkSum decrease walkSoFar)
      rw [Maths.Transport.walkMap_concat, Maths.walkSum_concat]
      calc
        storage (G.target edge) (T.edgeMap edge
            (Maths.fiberCast State rfl (T.walkMap walkSoFar point))) +
              (Maths.walkSum decrease walkSoFar + decrease edge) =
            (storage (G.target edge) (T.edgeMap edge
              (Maths.fiberCast State rfl (T.walkMap walkSoFar point))) +
                decrease edge) + Maths.walkSum decrease walkSoFar := by
              ac_rfl
        _ ≤ storage (G.source edge)
            (Maths.fiberCast State rfl (T.walkMap walkSoFar point)) +
              Maths.walkSum decrease walkSoFar := hsum
        _ ≤ storage start point := ih point

/-- A closed physical walk has nonincreasing storage after its accumulated decrease. -/
theorem closedWalk_storage_nonincrease [AddCommMonoid A] [Preorder A]
    [IsOrderedAddMonoid A] {G : Maths.EdgeGraph V E} (T : Maths.Transport G State)
    (decrease : E → A) (storage : (vertex : V) → State vertex → A)
    (hstorage : IsStorageCertificate T decrease storage)
    {base : V} (cycle : G.Walk base base) :
    ∀ point,
      storage base (T.holonomy cycle point) + Maths.walkSum decrease cycle ≤
        storage base point := by
  exact walk_storage_nonincrease T decrease storage hstorage cycle

/-- A positive-cost closed walk cannot fix a state under a certified transport. -/
theorem not_exists_fixedPoint_holonomy_of_pos_walkSum [AddCommMonoid A] [Preorder A]
    [IsOrderedAddMonoid A] [AddLeftStrictMono A]
    {G : Maths.EdgeGraph V E} (T : Maths.Transport G State) (decrease : E → A)
    (storage : (vertex : V) → State vertex → A)
    (hstorage : IsStorageCertificate T decrease storage)
    {base : V} (cycle : G.Walk base base)
    (hpositive : 0 < Maths.walkSum decrease cycle) :
    ¬∃ point, T.holonomy cycle point = point := by
  intro hfixed
  obtain ⟨point, hpoint⟩ := hfixed
  have hwalk := closedWalk_storage_nonincrease (A := A) T decrease storage hstorage cycle point
  rw [hpoint] at hwalk
  exact (not_lt_of_ge hwalk) (lt_add_of_pos_right _ hpositive)

/-! ## A two-mode heterogeneous example -/

/-- The two modes of the concrete example. -/
inductive ExampleMode
  | bool
  | fin3
  deriving DecidableEq

/-- The two physical transition identities. -/
inductive ExampleEdge
  | expand
  | reset
  deriving DecidableEq

/-- The state space attached to each concrete mode. -/
def exampleState : ExampleMode → Type
  | .bool => Bool
  | .fin3 => Fin 3

/-- The physical graph, oriented from pre-state mode to post-state mode. -/
def examplePhysicalGraph : Maths.EdgeGraph ExampleMode ExampleEdge where
  source
    | .expand => .bool
    | .reset => .fin3
  target
    | .expand => .fin3
    | .reset => .bool

/-- The physical expansion from `Bool` into the three-point state space. -/
def exampleExpand : Bool → Fin 3
  | false => 0
  | true => 2

/-- The physical reset, which merges the states `0` and `1`. -/
def exampleReset : Fin 3 → Bool
  | point => decide (point.val = 2)

/-- The physical transitions of the concrete graph. -/
def exampleStep : (edge : ExampleEdge) →
    exampleState (examplePhysicalGraph.source edge) →
      exampleState (examplePhysicalGraph.target edge)
  | .expand => exampleExpand
  | .reset => exampleReset

/-- The physical transport of the concrete graph. -/
def examplePhysicalTransport :
    Maths.Transport examplePhysicalGraph exampleState where
  edgeMap := exampleStep

/-- The Boolean-mode energy, with values `0` and `2`. -/
def exampleBoolEnergy : Bool → Nat
  | false => 0
  | true => 2

/-- The `Fin 3`-mode energy given by the underlying natural number. -/
def exampleFin3Energy : Fin 3 → Nat
  | point => point.val

/-- The concrete family of mode-dependent energies. -/
def exampleEnergy : (vertex : ExampleMode) → exampleState vertex → Nat
  | .bool => exampleBoolEnergy
  | .fin3 => exampleFin3Energy

/-- Every concrete edge has zero storage decrease. -/
def exampleDecrease : ExampleEdge → Nat
  | _ => 0

/-- The concrete family satisfies the physical storage inequalities. -/
theorem exampleEnergy_certified :
    IsStorageCertificate examplePhysicalTransport exampleDecrease exampleEnergy := by
  intro edge
  cases edge with
  | expand =>
      change ∀ point : Bool, _
      intro point
      cases point <;> rfl
  | reset =>
      change ∀ point : Fin 3, _
      intro point
      change exampleEnergy .bool (exampleReset point) + 0 ≤ exampleFin3Energy point
      refine Fin.cases ?_ ?_ point
      · decide
      · intro point
        refine Fin.cases ?_ ?_ point
        · decide
        · intro point
          refine Fin.cases ?_ ?_ point
          · decide
          · intro point
            exact Fin.elim0 point

/-- The concrete reset is not injective. -/
theorem exampleReset_noninjective : ¬Function.Injective exampleReset := by
  intro hinjective
  have heq : exampleReset (0 : Fin 3) = exampleReset (1 : Fin 3) := by
    rfl
  have hzeroone : (0 : Fin 3) = 1 := hinjective heq
  exact Fin.zero_ne_one hzeroone

/-- The closed physical cycle at `Fin 3`, with reset followed by expansion. -/
def exampleCycle : examplePhysicalGraph.Walk .fin3 .fin3 :=
  ((.nil : examplePhysicalGraph.Walk .fin3 .fin3).concat
      .reset rfl).concat .expand rfl

/-- The concrete closed physical cycle strictly decreases energy at state `1`. -/
theorem exampleCycle_strict_decrease :
    exampleEnergy .fin3 (examplePhysicalTransport.holonomy exampleCycle (1 : Fin 3)) <
      exampleEnergy .fin3 (1 : Fin 3) := by
  change exampleEnergy .fin3 (exampleExpand (exampleReset (1 : Fin 3))) <
    exampleEnergy .fin3 (1 : Fin 3)
  decide

end SwitchedHybridControl
