/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Graph.EulerianTrail
public import Maths.Graph.InfiniteWalk

import Mathlib.Data.Fintype.Pigeonhole

/-!
# Zero-charge lassos and the finite certificate for bounded discrepancy

A lasso is a finite transient walk followed by a nonempty closed walk of exactly zero charge.
Repeating that closed period forever gives an eventually periodic infinite walk of bounded
discrepancy, so a lasso is a finite certificate for an infinite qualitative property.

Over a finite vertex set the certificate is also necessary. If an infinite walk has bounded
discrepancy, then the pairs consisting of the current vertex and the current prefix charge
range over a finite set, so two distinct times carry the same pair; the segment between them
is a nonempty closed walk of zero charge, and the prefix before them is the transient. This
is the exact repeated-configuration extraction, and it needs no finiteness of the edge type.

The extraction comes with its search bound. There are only
`Maths.EdgeGraph.InfiniteWalk.configurationCount` many configurations, so the repetition
occurs among the first that many plus one times and the lasso it yields is no longer than that
count. A bounded-discrepancy walk therefore certifies itself inside an explicitly bounded search
space. The bound depends on the walk, through the size of its prefix-charge range, and not on
the graph alone: charges are unbounded, so no single length serves every walk at once.

Passing through the Eulerian realization of a circulation, the lasso certificate is
interchangeable with a reachable connected zero-charge integer circulation: the period of a
lasso is a circulation of edge counts, and the Euler realization of a circulation at its entry
vertex is the period of a lasso. Both directions are offline and existential; neither supplies
a causal policy against an adaptive edge chooser.

## Main definitions

* `Maths.EdgeGraph.ZeroChargeLasso`: a transient walk followed by a nonempty
  zero-charge closed period.
* `Maths.EdgeGraph.ZeroChargeLasso.closedPeriod`: the period as a genuinely closed
  typed walk.
* `Maths.EdgeGraph.ZeroChargeLasso.toReachableConnectedIntegerCirculation`: the
  exact edge counts of a lasso period.

## Main results

* `Maths.EdgeGraph.ZeroChargeLasso.exists_eventuallyPeriodic_boundedDiscrepancy`:
  a lasso certificate constructs an eventually periodic walk of bounded discrepancy.
* `Maths.EdgeGraph.exists_zeroChargeLasso_length_le_of_boundedDiscrepancy`: over a
  finite vertex set, a bounded-discrepancy walk contains a lasso **no longer than its
  configuration count**, with
  `Maths.EdgeGraph.exists_zeroChargeLasso_of_boundedDiscrepancy` the bare existence
  statement.
* `Maths.EdgeGraph.exists_boundedDiscrepancy_iff_exists_eventuallyPeriodic`:
  bounded discrepancy is achievable exactly when it is achievable eventually periodically.
* `Maths.EdgeGraph.exists_boundedDiscrepancy_iff_reachableConnectedIntegerCirculation`:
  bounded discrepancy is achievable exactly when a reachable connected zero-charge integer
  circulation exists.

## Tags

lasso, bounded discrepancy, circulation, eventual periodicity, pigeonhole
-/

@[expose] public section

namespace Maths

namespace EdgeGraph

universe uV uE uκ

variable {V : Type uV} {E : Type uE} (G : EdgeGraph V E)

/-- A finite reachable lasso: first follow the transient walk, then repeat the nonempty closed
period. Exact zero period charge is the finite certificate for bounded discrepancy of the
canonical eventually periodic repetition. -/
structure ZeroChargeLasso {κ : Type uκ} (edgeCharge : E → κ → ℤ) (start : V) where
  /-- The vertex at which the period is based. -/
  base : V
  /-- The transient walk from `start` to `base`. -/
  initialWalk : G.Walk start base
  /-- The terminal vertex of the period, constrained to be `base`. -/
  periodFinish : V
  /-- The period, traversed once. -/
  period : G.Walk base periodFinish
  /-- The period returns to its base. -/
  period_closed : periodFinish = base
  /-- The period uses at least one edge. -/
  period_nonempty : 0 < period.length
  /-- The period carries no net charge. -/
  period_zero : period.charge edgeCharge = 0

namespace ReachableConnectedIntegerCirculation

variable {G} {start : V} {κ : Type uκ} {edgeCharge : E → κ → ℤ}

/-- The Euler realization of a reachable connected circulation is a zero-charge lasso whose
transient is the supplied route to the support. -/
theorem exists_zeroChargeLasso [Fintype E] [DecidableEq V]
    (circulation : G.ReachableConnectedIntegerCirculation edgeCharge start) :
    Nonempty (G.ZeroChargeLasso edgeCharge start) := by
  classical
  obtain ⟨period, hnonempty, -, hzero⟩ :=
    circulation.toConnectedIntegerCirculation.exists_closedWalk_exactMultiplicity_at
      circulation.entry circulation.entry_mem_support
  exact ⟨{
    base := circulation.entry
    initialWalk := circulation.initialWalk
    periodFinish := circulation.entry
    period := period
    period_closed := rfl
    period_nonempty := hnonempty
    period_zero := hzero }⟩

end ReachableConnectedIntegerCirculation

namespace ZeroChargeLasso

variable {G} {start : V} {κ : Type uκ} {edgeCharge : E → κ → ℤ}

/-- Regard the lasso period as a genuinely closed typed walk. -/
def closedPeriod (lasso : G.ZeroChargeLasso edgeCharge start) :
    G.Walk lasso.base lasso.base :=
  lasso.period.castFinish lasso.period_closed

@[simp] theorem closedPeriod_length (lasso : G.ZeroChargeLasso edgeCharge start) :
    lasso.closedPeriod.length = lasso.period.length := by
  simp [closedPeriod]

@[simp] theorem closedPeriod_charge (lasso : G.ZeroChargeLasso edgeCharge start) :
    lasso.closedPeriod.charge edgeCharge = 0 := by
  simpa [closedPeriod] using lasso.period_zero

/-- A lasso certificate constructs a genuine eventually periodic infinite walk from the
prescribed start, and its prefix-charge range is finite. -/
theorem exists_eventuallyPeriodic_boundedDiscrepancy
    (lasso : G.ZeroChargeLasso edgeCharge start) :
    ∃ walk : G.InfiniteWalk start,
      walk.HasBoundedDiscrepancy edgeCharge ∧ walk.IsEventuallyPeriodic := by
  have hclosedNonempty : 0 < lasso.closedPeriod.length := by
    simpa using lasso.period_nonempty
  set cycle : G.CyclicWord lasso.base := lasso.closedPeriod.toCyclicWord hclosedNonempty
    with hcycleDef
  have hwordZero : (cycle.word.map edgeCharge).sum = 0 := by
    rw [hcycleDef, Walk.toCyclicWord_word, ← lasso.closedPeriod.charge_eq_sum_map]
    exact lasso.closedPeriod_charge
  refine ⟨lasso.initialWalk.prependInfinite cycle.toInfiniteWalk,
    lasso.initialWalk.hasBoundedDiscrepancy_prependInfinite edgeCharge cycle.toInfiniteWalk
      (cycle.hasBoundedDiscrepancy_of_wordCharge_zero edgeCharge hwordZero),
    lasso.initialWalk.length, cycle.periodLength, cycle.periodLength_pos, fun n => ?_⟩
  calc
    (lasso.initialWalk.prependInfinite cycle.toInfiniteWalk).edge
          (lasso.initialWalk.length + n + cycle.periodLength) =
        cycle.toInfiniteWalk.edge (n + cycle.periodLength) := by
          rw [show lasso.initialWalk.length + n + cycle.periodLength =
            lasso.initialWalk.length + (n + cycle.periodLength) by omega]
          exact lasso.initialWalk.prependInfinite_edge_length_add cycle.toInfiniteWalk _
    _ = cycle.toInfiniteWalk.edge n := cycle.edgeAt_add_period n
    _ = (lasso.initialWalk.prependInfinite cycle.toInfiniteWalk).edge
          (lasso.initialWalk.length + n) :=
      (lasso.initialWalk.prependInfinite_edge_length_add cycle.toInfiniteWalk n).symm

/-- The exact edge counts of a lasso period form a reachable connected integer
circulation. -/
def toReachableConnectedIntegerCirculation
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (lasso : G.ZeroChargeLasso edgeCharge start) :
    G.ReachableConnectedIntegerCirculation edgeCharge start where
  toConnectedIntegerCirculation :=
    lasso.closedPeriod.toConnectedIntegerCirculation edgeCharge
      (by simpa using lasso.period_nonempty) lasso.closedPeriod_charge
  entry := lasso.base
  initialWalk := lasso.initialWalk
  entry_mem_support := by
    have hedges : lasso.closedPeriod.edges ≠ [] :=
      lasso.closedPeriod.edges_ne_nil_of_length_pos (by simpa using lasso.period_nonempty)
    exact ⟨lasso.closedPeriod.edges.head hedges,
      (lasso.closedPeriod.edgeMultiplicity_pos_iff_mem_edges _).2 (List.head_mem hedges),
      Or.inl (lasso.closedPeriod.source_head hedges)⟩

end ZeroChargeLasso

namespace ReachableConnectedIntegerCirculation

variable {G} {start : V} {κ : Type uκ} {edgeCharge : E → κ → ℤ}

/-- A reachable connected zero-charge integer circulation constructs a genuine eventually
periodic infinite walk of bounded discrepancy. -/
theorem exists_eventuallyPeriodic_boundedDiscrepancy [Fintype E] [DecidableEq V]
    (circulation : G.ReachableConnectedIntegerCirculation edgeCharge start) :
    ∃ walk : G.InfiniteWalk start,
      walk.HasBoundedDiscrepancy edgeCharge ∧ walk.IsEventuallyPeriodic := by
  obtain ⟨lasso⟩ := circulation.exists_zeroChargeLasso
  exact lasso.exists_eventuallyPeriodic_boundedDiscrepancy

end ReachableConnectedIntegerCirculation

/-- **The exact repeated-configuration extraction, with the search bound it comes with.**
Finiteness of the vertex type and of the prefix-charge range confines a walk to
`walk.configurationCount edgeCharge` many configurations, so two of the first that many plus one
times carry the same vertex and the same cumulative lattice charge; the intervening segment is
the desired nonempty zero-charge closed walk, and the lasso it forms is no longer than that
count. The certificate is therefore not merely existent but findable: it lives in an explicitly
bounded search space, one lasso per pair of times. -/
theorem exists_zeroChargeLasso_length_le_of_boundedDiscrepancy [Finite V] {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (start : V) (walk : G.InfiniteWalk start)
    (hbounded : walk.HasBoundedDiscrepancy edgeCharge) :
    ∃ lasso : G.ZeroChargeLasso edgeCharge start,
      lasso.initialWalk.length + lasso.period.length ≤
        walk.configurationCount edgeCharge := by
  classical
  have _ : Fintype V := Fintype.ofFinite V
  let _ : Fintype (Set.range (walk.prefixCharge edgeCharge)) := hbounded.fintype
  set bound := walk.configurationCount edgeCharge with hboundDef
  have makeLasso : ∀ {earlier later : ℕ}, earlier < later → later ≤ bound →
      walk.vertex earlier = walk.vertex later →
      walk.prefixCharge edgeCharge earlier = walk.prefixCharge edgeCharge later →
      ∃ lasso : G.ZeroChargeLasso edgeCharge start,
        lasso.initialWalk.length + lasso.period.length ≤ bound := by
    intro earlier later hlt hle hvertex hcharge
    have hsum : earlier + (later - earlier) = later := by omega
    refine ⟨{
      base := walk.vertex earlier
      initialWalk := walk.take earlier
      periodFinish := walk.vertex (earlier + (later - earlier))
      period := walk.segment earlier (later - earlier)
      period_closed := by rw [hsum]; exact hvertex.symm
      period_nonempty := by simpa using Nat.sub_pos_of_lt hlt
      period_zero := by
        rw [walk.segment_charge edgeCharge, hsum, ← hcharge, sub_self] }, ?_⟩
    simp only [InfiniteWalk.take_length, InfiniteWalk.segment_length]
    omega
  let state : Fin (bound + 1) → V × Set.range (walk.prefixCharge edgeCharge) := fun time =>
    (walk.vertex time, ⟨walk.prefixCharge edgeCharge time, ⟨time, rfl⟩⟩)
  have hcard : Fintype.card (V × Set.range (walk.prefixCharge edgeCharge)) = bound := by
    simp [hboundDef, InfiniteWalk.configurationCount, Nat.card_eq_fintype_card]
  obtain ⟨first, second, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt state (by simp [hcard])
  have hextract : ∀ {x y : Fin (bound + 1)}, (x : ℕ) < (y : ℕ) → state x = state y →
      ∃ lasso : G.ZeroChargeLasso edgeCharge start,
        lasso.initialWalk.length + lasso.period.length ≤ bound := by
    intro x y hlt hstate
    exact makeLasso hlt (Nat.lt_succ_iff.mp y.isLt) (congrArg Prod.fst hstate)
      (congrArg (fun pair => pair.2.1) hstate)
  rcases lt_or_gt_of_ne (fun hval => hne (Fin.ext hval)) with hlt | hgt
  · exact hextract hlt heq
  · exact hextract hgt heq.symm

/-- The lasso certificate itself, forgetting the bound. -/
theorem exists_zeroChargeLasso_of_boundedDiscrepancy [Finite V] {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (start : V) (walk : G.InfiniteWalk start)
    (hbounded : walk.HasBoundedDiscrepancy edgeCharge) :
    Nonempty (G.ZeroChargeLasso edgeCharge start) :=
  (G.exists_zeroChargeLasso_length_le_of_boundedDiscrepancy edgeCharge start walk
    hbounded).elim fun lasso _ => ⟨lasso⟩

/-- For finite vertices and integer-lattice charges, existence of any bounded-discrepancy walk
is equivalent to existence of an eventually periodic one. The witness is offline and
existential. -/
theorem exists_boundedDiscrepancy_iff_exists_eventuallyPeriodic
    [Finite V] {κ : Type uκ} (edgeCharge : E → κ → ℤ) (start : V) :
    (∃ walk : G.InfiniteWalk start, walk.HasBoundedDiscrepancy edgeCharge) ↔
      ∃ walk : G.InfiniteWalk start,
        walk.HasBoundedDiscrepancy edgeCharge ∧ walk.IsEventuallyPeriodic := by
  refine ⟨?_, fun ⟨walk, hbounded, _⟩ => ⟨walk, hbounded⟩⟩
  rintro ⟨walk, hbounded⟩
  obtain ⟨lasso⟩ :=
    G.exists_zeroChargeLasso_of_boundedDiscrepancy edgeCharge start walk hbounded
  exact lasso.exists_eventuallyPeriodic_boundedDiscrepancy

/-- The bounded-discrepancy pigeonhole certificate also yields a reachable connected integer
circulation. This is the extraction direction of the circulation equivalence below. -/
theorem exists_reachableConnectedIntegerCirculation_of_boundedDiscrepancy
    [Finite V] [Fintype E] [DecidableEq V] {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (start : V) (walk : G.InfiniteWalk start)
    (hbounded : walk.HasBoundedDiscrepancy edgeCharge) :
    Nonempty (G.ReachableConnectedIntegerCirculation edgeCharge start) := by
  classical
  obtain ⟨lasso⟩ :=
    G.exists_zeroChargeLasso_of_boundedDiscrepancy edgeCharge start walk hbounded
  exact ⟨lasso.toReachableConnectedIntegerCirculation⟩

/-- **Exact finite certificate theorem for offline bounded discrepancy.** Over a finite vertex
set and an integer charge lattice, a bounded-discrepancy walk exists exactly when a reachable
connected zero-charge integer circulation exists. The reverse construction is eventually
periodic. -/
theorem exists_boundedDiscrepancy_iff_reachableConnectedIntegerCirculation
    [Finite V] [Fintype E] [DecidableEq V] {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (start : V) :
    (∃ walk : G.InfiniteWalk start, walk.HasBoundedDiscrepancy edgeCharge) ↔
      Nonempty (G.ReachableConnectedIntegerCirculation edgeCharge start) := by
  refine ⟨fun ⟨walk, hbounded⟩ =>
    G.exists_reachableConnectedIntegerCirculation_of_boundedDiscrepancy
      edgeCharge start walk hbounded, ?_⟩
  rintro ⟨circulation⟩
  obtain ⟨walk, hbounded, -⟩ := circulation.exists_eventuallyPeriodic_boundedDiscrepancy
  exact ⟨walk, hbounded⟩

end EdgeGraph

end Maths
