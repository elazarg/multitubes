/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DirectedTransport.EdgeGraph
public import Mathlib.Algebra.BigOperators.Pi

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-!
# Walk multiplicities as circulations

A finite walk of an `DirectedTransport.EdgeGraph` records how often it uses each edge, and
that edge multiplicity vector is a flow: at every vertex, the multiplicity leaving the vertex
matches the multiplicity entering it, up to a correction at the two endpoints of the walk. For
a closed walk the correction cancels and the multiplicity vector is an honest circulation.

Only flow conservation and the integer-charge bookkeeping that accompanies it are developed
here; no cyclic-word, lasso, or infinite-walk machinery is required.

## Main definitions

* `DirectedTransport.EdgeGraph.Walk.charge`: the total integer charge of a finite walk.
* `DirectedTransport.EdgeGraph.outgoingMultiplicity`,
  `DirectedTransport.EdgeGraph.incomingMultiplicity`: the multiplicity leaving and entering a
  vertex.
* `DirectedTransport.EdgeGraph.multiplicityCharge`: the charge carried by an edge multiplicity
  vector.

## Main results

* `DirectedTransport.EdgeGraph.Walk.edgeMultiplicity_flow_with_endpoints`: endpoint-corrected
  flow conservation for every finite typed walk.
* `DirectedTransport.EdgeGraph.Walk.edgeMultiplicity_balanced`: the edge multiplicities of a
  closed walk are balanced at every vertex.
* `DirectedTransport.EdgeGraph.Walk.multiplicityCharge_edgeMultiplicity`: the charge of a walk
  is the charge of its multiplicity vector.

## TODO

* Bounded-discrepancy walks, Eulerian realizations of connected nonnegative circulations, and
  zero-charge lassos.

## Tags

circulation, flow conservation, walk, edge multiplicity, directed multigraph
-/

@[expose] public section

namespace DirectedTransport

namespace EdgeGraph

universe uV uE uκ

variable {V : Type uV} {E : Type uE} (G : EdgeGraph V E)

namespace Walk

variable {G} {start finish middle : V}

/-- Total integer charge of a finite walk. -/
def charge {κ : Type uκ} (edgeCharge : E → κ → ℤ) {start : V} :
    {finish : V} → G.Walk start finish → κ → ℤ
  | _, .nil => 0
  | _, .concat walkSoFar edge _ => walkSoFar.charge edgeCharge + edgeCharge edge

@[simp] theorem charge_nil {κ : Type uκ} (edgeCharge : E → κ → ℤ) :
    (Walk.nil : G.Walk start start).charge edgeCharge = 0 := rfl

@[simp] theorem charge_concat {κ : Type uκ} (edgeCharge : E → κ → ℤ)
    (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    (Walk.concat walkSoFar edge legal).charge edgeCharge =
      walkSoFar.charge edgeCharge + edgeCharge edge := rfl

/-- The recursive charge agrees with summing the chronological edge list. -/
theorem charge_eq_sum_map {κ : Type uκ} (edgeCharge : E → κ → ℤ)
    (walk : G.Walk start finish) :
    walk.charge edgeCharge = (walk.edges.map edgeCharge).sum := by
  induction walk with
  | nil => rfl
  | concat walkSoFar edge legal ih => simp [charge, edges, ih]

@[simp] theorem charge_castFinish {κ : Type uκ} (edgeCharge : E → κ → ℤ)
    {start finish finish' : V} (walk : G.Walk start finish)
    (hfinish : finish = finish') :
    (walk.castFinish hfinish).charge edgeCharge = walk.charge edgeCharge := by
  subst hfinish
  rfl

@[simp] theorem charge_append {κ : Type uκ} (edgeCharge : E → κ → ℤ)
    (first : G.Walk start middle) (second : G.Walk middle finish) :
    (first.append second).charge edgeCharge =
      first.charge edgeCharge + second.charge edgeCharge := by
  induction second with
  | nil => simp
  | concat second edge legal ih => simp [ih, add_assoc]

end Walk

/-- Total multiplicity leaving a vertex. -/
def outgoingMultiplicity [Fintype E] [DecidableEq V]
    (multiplicity : E → ℕ) (vertex : V) : ℕ :=
  ∑ edge with G.source edge = vertex, multiplicity edge

/-- Total multiplicity entering a vertex. -/
def incomingMultiplicity [Fintype E] [DecidableEq V]
    (multiplicity : E → ℕ) (vertex : V) : ℕ :=
  ∑ edge with G.target edge = vertex, multiplicity edge

/-- Total charge carried by an integer edge multiplicity. -/
def multiplicityCharge (_G : EdgeGraph V E) [Fintype E] {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (multiplicity : E → ℕ) : κ → ℤ :=
  ∑ edge, multiplicity edge • edgeCharge edge

namespace Walk

variable {G} {start finish : V}

@[simp] theorem outgoingMultiplicity_edgeMultiplicity_nil
    [Fintype E] [DecidableEq E] [DecidableEq V] (vertex : V) :
    G.outgoingMultiplicity
      ((Walk.nil : G.Walk start start).edgeMultiplicity) vertex = 0 := by
  simp [outgoingMultiplicity]

@[simp] theorem incomingMultiplicity_edgeMultiplicity_nil
    [Fintype E] [DecidableEq E] [DecidableEq V] (vertex : V) :
    G.incomingMultiplicity
      ((Walk.nil : G.Walk start start).edgeMultiplicity) vertex = 0 := by
  simp [incomingMultiplicity]

/-- Extending a walk by one edge adds one unit of outgoing multiplicity at that edge's
source. -/
theorem outgoingMultiplicity_edgeMultiplicity_concat
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) (vertex : V) :
    G.outgoingMultiplicity (Walk.concat walkSoFar edge legal).edgeMultiplicity vertex =
      G.outgoingMultiplicity walkSoFar.edgeMultiplicity vertex +
        if G.source edge = vertex then 1 else 0 := by
  classical
  simp [outgoingMultiplicity, edgeMultiplicity, Finset.sum_add_distrib]

/-- Extending a walk by one edge adds one unit of incoming multiplicity at that edge's
target. -/
theorem incomingMultiplicity_edgeMultiplicity_concat
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) (vertex : V) :
    G.incomingMultiplicity (Walk.concat walkSoFar edge legal).edgeMultiplicity vertex =
      G.incomingMultiplicity walkSoFar.edgeMultiplicity vertex +
        if G.target edge = vertex then 1 else 0 := by
  classical
  simp [incomingMultiplicity, edgeMultiplicity, Finset.sum_add_distrib]

/-- The charge of a walk is the charge carried by its edge multiplicity vector. -/
theorem multiplicityCharge_edgeMultiplicity
    [Fintype E] [DecidableEq E] {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (walk : G.Walk start finish) :
    G.multiplicityCharge edgeCharge walk.edgeMultiplicity =
      walk.charge edgeCharge := by
  induction walk with
  | nil => simp [multiplicityCharge]
  | concat walkSoFar edge legal ih =>
      funext coordinate
      simp only [multiplicityCharge, edgeMultiplicity, Walk.charge_concat,
        Pi.add_apply, Finset.sum_apply, nsmul_eq_mul]
      simp_rw [Nat.cast_add, add_mul, Pi.add_apply, Pi.mul_apply]
      have ihCoordinate := congrFun ih coordinate
      simp only [multiplicityCharge, Finset.sum_apply, nsmul_eq_mul,
        Pi.mul_apply] at ihCoordinate
      rw [Finset.sum_add_distrib, ihCoordinate]
      simp

/-- Endpoint-corrected flow conservation for every finite typed walk. -/
theorem edgeMultiplicity_flow_with_endpoints
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (walk : G.Walk start finish) (vertex : V) :
    G.outgoingMultiplicity walk.edgeMultiplicity vertex +
        (if finish = vertex then 1 else 0) =
      G.incomingMultiplicity walk.edgeMultiplicity vertex +
        (if start = vertex then 1 else 0) := by
  induction walk with
  | nil => simp
  | @concat middle walkSoFar edge legal ih =>
      rw [outgoingMultiplicity_edgeMultiplicity_concat,
        incomingMultiplicity_edgeMultiplicity_concat, legal]
      omega

/-- Edge multiplicities of a closed typed walk are balanced at every vertex. -/
theorem edgeMultiplicity_balanced [Fintype E] [DecidableEq E] [DecidableEq V]
    {base : V} (walk : G.Walk base base) (vertex : V) :
    G.outgoingMultiplicity walk.edgeMultiplicity vertex =
      G.incomingMultiplicity walk.edgeMultiplicity vertex := by
  have hflow := walk.edgeMultiplicity_flow_with_endpoints vertex
  omega

end Walk

end EdgeGraph

end DirectedTransport
