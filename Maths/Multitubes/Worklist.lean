/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Closure
public import Mathlib.Order.OrderIsoNat

/-!
# Fair local relaxation for lax transport

The least lax majorant of monotone transport can be computed by local, inflationary edge
relaxations when ascending chains stabilize.  Relaxing an edge joins its transported source value
into its target and leaves every other vertex unchanged.  A fair schedule may contain idle steps;
fairness only requires that every edge is processed again after every time.

An executable finite variant folds the same relaxation over a list of edges.  If the list covers
every edge, a fixed point of one sweep is a lax section.  Under the ascending chain condition,
iteration of a covering sweep reaches the least lax majorant.  No bound on the number of steps is
asserted.

## Main definitions

* `Maths.Transport.relaxEdge` - one inflationary edge relaxation.
* `Maths.Transport.scheduledRelaxation` - iteration along an optional-edge schedule.
* `Maths.Transport.IsFairSchedule` - every edge occurs arbitrarily late in the schedule.
* `Maths.Transport.relaxSweep` and `Maths.Transport.sweepRelaxation` - finite-list relaxation.

## Main results

* `Maths.Transport.exists_scheduledRelaxation_eq_leastLaxMajorant` - a fair scheduled relaxation
  reaches the least lax majorant under the ascending chain condition.
* `Maths.Transport.isLaxSection_of_relaxSweep_eq` - a covering fixed sweep is a lax section.
* `Maths.Transport.sweepRelaxation_isLeast_of_relaxSweep_eq` - an observed fixed sweep is the
  least lax section above its seeds, without completeness or ACC.
* `Maths.Transport.exists_sweepRelaxation_eq_leastLaxMajorant` - repeated covering sweeps reach
  the least lax majorant under the ascending chain condition.

## Tags

worklist, chaotic iteration, relaxation, fair schedule, ascending chain condition
-/

@[expose] public section

namespace Maths
namespace Transport

universe uV uE uF

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}
variable {Fiber : V → Type uF} (T : Transport G Fiber)

section Relaxation

variable [DecidableEq V] [∀ vertex : V, SemilatticeSup (Fiber vertex)]

/-- Relax one edge by joining its transported source value into its target. -/
def relaxEdge (family : ∀ vertex, Fiber vertex) (edge : E) : ∀ vertex, Fiber vertex :=
  Function.update family (G.target edge)
    (family (G.target edge) ⊔ T.edgeMap edge (family (G.source edge)))

/-- At the relaxed target, the old value is joined with the transported source value. -/
@[simp] theorem relaxEdge_target (family : ∀ vertex, Fiber vertex) (edge : E) :
    T.relaxEdge family edge (G.target edge) =
      family (G.target edge) ⊔ T.edgeMap edge (family (G.source edge)) := by
  simp [relaxEdge]

/-- Relaxing an edge leaves every other vertex unchanged. -/
theorem relaxEdge_apply_of_ne (family : ∀ vertex, Fiber vertex) (edge : E) {vertex : V}
    (hne : vertex ≠ G.target edge) :
    T.relaxEdge family edge vertex = family vertex := by
  simp [relaxEdge, hne]

/-- Every edge relaxation increases the current family. -/
theorem le_relaxEdge (family : ∀ vertex, Fiber vertex) (edge : E) :
    family ≤ T.relaxEdge family edge := by
  intro vertex
  by_cases hvertex : vertex = G.target edge
  · subst vertex
    simp
  · rw [T.relaxEdge_apply_of_ne family edge hvertex]

/-- Edge relaxation is monotone when the relaxed edge map is monotone. -/
theorem monotone_relaxEdge (edge : E) (hmono : Monotone (T.edgeMap edge)) :
    Monotone fun family ↦ T.relaxEdge family edge := by
  intro first second hle vertex
  by_cases hvertex : vertex = G.target edge
  · subst vertex
    simp only [relaxEdge_target]
    exact sup_le_sup (hle _) (hmono (hle _))
  · change T.relaxEdge first edge vertex ≤ T.relaxEdge second edge vertex
    rw [T.relaxEdge_apply_of_ne first edge hvertex,
      T.relaxEdge_apply_of_ne second edge hvertex]
    exact hle vertex

/-- Relaxation stays below any lax section that already bounds the current family. -/
theorem relaxEdge_le_of_le {family majorant : ∀ vertex, Fiber vertex} (edge : E)
    (hmono : Monotone (T.edgeMap edge)) (hle : family ≤ majorant)
    (hmaj : T.IsLaxSection majorant) :
    T.relaxEdge family edge ≤ majorant := by
  intro vertex
  by_cases hvertex : vertex = G.target edge
  · subst vertex
    simp only [relaxEdge_target]
    exact sup_le (hle _) ((hmono (hle _)).trans (hmaj edge))
  · rw [T.relaxEdge_apply_of_ne family edge hvertex]
    exact hle vertex

/-- A schedule is fair when every edge is processed at arbitrarily late times. -/
def IsFairSchedule (schedule : ℕ → Option E) : Prop :=
  ∀ edge n, ∃ k, n ≤ k ∧ schedule k = some edge

/-- Iterated local relaxation along a schedule with optional idle steps. -/
def scheduledRelaxation (schedule : ℕ → Option E)
    (seed : ∀ vertex, Fiber vertex) : ℕ → (∀ vertex, Fiber vertex) :=
  fun n => Nat.rec seed (fun k current => match schedule k with
    | none => current
    | some edge => T.relaxEdge current edge) n

/-- Scheduled relaxation starts at the prescribed seed family. -/
@[simp] theorem scheduledRelaxation_zero (schedule : ℕ → Option E)
    (seed : ∀ vertex, Fiber vertex) :
    T.scheduledRelaxation schedule seed 0 = seed :=
  rfl

/-- One scheduled step is idle at `none` and relaxes the selected edge at `some`. -/
theorem scheduledRelaxation_succ (schedule : ℕ → Option E)
    (seed : ∀ vertex, Fiber vertex) (n : ℕ) :
    T.scheduledRelaxation schedule seed (n + 1) =
      match schedule n with
      | none => T.scheduledRelaxation schedule seed n
      | some edge => T.relaxEdge (T.scheduledRelaxation schedule seed n) edge :=
  rfl

/-- Scheduled relaxation is increasing in time. -/
theorem monotone_scheduledRelaxation (schedule : ℕ → Option E)
    (seed : ∀ vertex, Fiber vertex) :
    Monotone (T.scheduledRelaxation schedule seed) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [T.scheduledRelaxation_succ]
  split
  · exact le_rfl
  · exact T.le_relaxEdge _ _

/-- Every scheduled state remains below a lax majorant of the seed. -/
theorem scheduledRelaxation_le_of_le {schedule : ℕ → Option E}
    {seed majorant : ∀ vertex, Fiber vertex} (hseed : seed ≤ majorant)
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (hmaj : T.IsLaxSection majorant) (n : ℕ) :
    T.scheduledRelaxation schedule seed n ≤ majorant := by
  induction n with
  | zero => exact hseed
  | succ n ih =>
      rw [T.scheduledRelaxation_succ]
      split
      · exact ih
      · exact T.relaxEdge_le_of_le _ (hmono _) ih hmaj

/-- If a fair scheduled run is constant from one time onward, its stable value is lax. -/
theorem isLaxSection_of_scheduledRelaxation_stable {schedule : ℕ → Option E}
    (hfair : IsFairSchedule schedule) (seed : ∀ vertex, Fiber vertex) {n : ℕ}
    (hstable : ∀ m, n ≤ m → T.scheduledRelaxation schedule seed n =
      T.scheduledRelaxation schedule seed m) :
    T.IsLaxSection (T.scheduledRelaxation schedule seed n) := by
  intro edge
  obtain ⟨k, hnk, hk⟩ := hfair edge n
  have hkn : T.scheduledRelaxation schedule seed k =
      T.scheduledRelaxation schedule seed n := (hstable k hnk).symm
  have hks : T.scheduledRelaxation schedule seed (k + 1) =
      T.scheduledRelaxation schedule seed n := (hstable (k + 1) (hnk.trans (Nat.le_succ k))).symm
  rw [T.scheduledRelaxation_succ, hk] at hks
  simp only at hks
  have htarget := congrFun hks (G.target edge)
  rw [T.relaxEdge_target, hkn] at htarget
  exact le_sup_right.trans_eq htarget

end Relaxation

section LeastMajorant

variable [DecidableEq V] [∀ vertex : V, CompleteLattice (Fiber vertex)]

/-- Under ACC, a fair scheduled relaxation eventually equals the least lax majorant. -/
theorem exists_scheduledRelaxation_eq_leastLaxMajorant
    [WellFoundedGT (∀ vertex, Fiber vertex)]
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    {schedule : ℕ → Option E} (hfair : IsFairSchedule schedule)
    (seed : ∀ vertex, Fiber vertex) :
    ∃ n, ∀ m, n ≤ m →
      T.scheduledRelaxation schedule seed m = T.leastLaxMajorant hmono seed := by
  let run : ℕ →o (∀ vertex, Fiber vertex) :=
    ⟨T.scheduledRelaxation schedule seed, T.monotone_scheduledRelaxation schedule seed⟩
  obtain ⟨n, hstable⟩ := WellFoundedGT.monotone_chain_condition run
  have hlax : T.IsLaxSection (T.scheduledRelaxation schedule seed n) :=
    T.isLaxSection_of_scheduledRelaxation_stable hfair seed hstable
  have hseed : seed ≤ T.scheduledRelaxation schedule seed n :=
    T.monotone_scheduledRelaxation schedule seed (Nat.zero_le n)
  have hleast_le : T.leastLaxMajorant hmono seed ≤
      T.scheduledRelaxation schedule seed n :=
    (T.leastLaxMajorant_isLeast hmono seed).2.2 _ hseed hlax
  have hrun_le : T.scheduledRelaxation schedule seed n ≤
      T.leastLaxMajorant hmono seed :=
    T.scheduledRelaxation_le_of_le
      (T.leastLaxMajorant_isLeast hmono seed).1
      hmono
      (T.leastLaxMajorant_isLeast hmono seed).2.1 n
  have hn : T.scheduledRelaxation schedule seed n = T.leastLaxMajorant hmono seed :=
    le_antisymm hrun_le hleast_le
  exact ⟨n, fun m hnm ↦ (hstable m hnm).symm.trans hn⟩

end LeastMajorant

section Sweep

variable [DecidableEq V] [∀ vertex : V, SemilatticeSup (Fiber vertex)]

/-- Relax every edge in a finite list, in list order. -/
def relaxSweep (edges : List E) (family : ∀ vertex, Fiber vertex) :
    ∀ vertex, Fiber vertex :=
  edges.foldl (fun current edge ↦ T.relaxEdge current edge) family

/-- Sweeping the empty edge list changes nothing. -/
@[simp] theorem relaxSweep_nil (family : ∀ vertex, Fiber vertex) :
    T.relaxSweep [] family = family :=
  rfl

/-- A sweep processes the head edge before the remaining edges. -/
@[simp] theorem relaxSweep_cons (edge : E) (edges : List E)
    (family : ∀ vertex, Fiber vertex) :
    T.relaxSweep (edge :: edges) family = T.relaxSweep edges (T.relaxEdge family edge) :=
  rfl

/-- A sweep increases its input family. -/
theorem le_relaxSweep (edges : List E) (family : ∀ vertex, Fiber vertex) :
    family ≤ T.relaxSweep edges family := by
  induction edges generalizing family with
  | nil => exact le_rfl
  | cons edge edges ih =>
      rw [T.relaxSweep_cons]
      exact (T.le_relaxEdge family edge).trans (ih _)

/-- A sweep stays below every lax majorant that bounds its input. -/
theorem relaxSweep_le_of_le {family majorant : ∀ vertex, Fiber vertex}
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (edges : List E) (hle : family ≤ majorant) (hmaj : T.IsLaxSection majorant) :
    T.relaxSweep edges family ≤ majorant := by
  induction edges generalizing family with
  | nil => exact hle
  | cons edge edges ih =>
      rw [T.relaxSweep_cons]
      exact ih (T.relaxEdge_le_of_le edge (hmono edge) hle hmaj)

/-- A fixed sweep over a covering edge list is a lax section. -/
theorem isLaxSection_of_relaxSweep_eq {edges : List E}
    (hcover : ∀ edge : E, edge ∈ edges) {family : ∀ vertex, Fiber vertex}
    (hfixed : T.relaxSweep edges family = family) :
    T.IsLaxSection family := by
  intro edge
  have hedge_mem := hcover edge
  clear hcover
  have hedge_le (hmem : edge ∈ edges) :
      T.edgeMap edge (family (G.source edge)) ≤ family (G.target edge) := by
    induction edges generalizing family with
    | nil => simp at hmem
    | cons first rest ih =>
        have hfirst_le : T.relaxEdge family first ≤ family := by
          calc
            T.relaxEdge family first ≤ T.relaxSweep rest (T.relaxEdge family first) :=
              T.le_relaxSweep rest _
            _ = family := by simpa only [relaxSweep_cons] using hfixed
        have hfirst_fixed : T.relaxEdge family first = family :=
          le_antisymm hfirst_le (T.le_relaxEdge family first)
        have hrest_fixed : T.relaxSweep rest family = family := by
          calc
            T.relaxSweep rest family = T.relaxSweep rest (T.relaxEdge family first) :=
              congrArg (T.relaxSweep rest) hfirst_fixed.symm
            _ = family := by simpa only [relaxSweep_cons] using hfixed
        by_cases hedge : edge = first
        · subst edge
          have htarget := congrFun hfirst_fixed (G.target first)
          rw [T.relaxEdge_target] at htarget
          exact le_sup_right.trans_eq htarget
        · have hrest : edge ∈ rest := by simpa [hedge] using hmem
          exact ih hrest_fixed hrest hrest
  exact hedge_le hedge_mem

/-- Iteration of a fixed finite sweep from a seed family. -/
def sweepRelaxation (edges : List E) (seed : ∀ vertex, Fiber vertex) :
    ℕ → (∀ vertex, Fiber vertex) :=
  fun n => Nat.rec seed (fun _ current => T.relaxSweep edges current) n

/-- Sweep iteration starts at the prescribed seed family. -/
@[simp] theorem sweepRelaxation_zero (edges : List E) (seed : ∀ vertex, Fiber vertex) :
    T.sweepRelaxation edges seed 0 = seed :=
  rfl

/-- The next sweep iterate applies one complete sweep to the current family. -/
@[simp] theorem sweepRelaxation_succ (edges : List E) (seed : ∀ vertex, Fiber vertex)
    (n : ℕ) :
    T.sweepRelaxation edges seed (n + 1) =
      T.relaxSweep edges (T.sweepRelaxation edges seed n) :=
  rfl

/-- Repeated sweeps form an increasing sequence. -/
theorem monotone_sweepRelaxation (edges : List E) (seed : ∀ vertex, Fiber vertex) :
    Monotone (T.sweepRelaxation edges seed) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [T.sweepRelaxation_succ]
  exact T.le_relaxSweep edges _

/-- Every sweep iterate stays below a lax majorant of the seed. -/
theorem sweepRelaxation_le_of_le {seed majorant : ∀ vertex, Fiber vertex}
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (edges : List E) (hseed : seed ≤ majorant) (hmaj : T.IsLaxSection majorant) (n : ℕ) :
    T.sweepRelaxation edges seed n ≤ majorant := by
  induction n with
  | zero => exact hseed
  | succ n ih =>
      rw [T.sweepRelaxation_succ]
      exact T.relaxSweep_le_of_le hmono edges ih hmaj

/-- An observed fixed iterate of a covering monotone sweep is the least lax section above its
seed, without any ascending-chain hypothesis. -/
theorem sweepRelaxation_isLeast_of_relaxSweep_eq
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    {edges : List E} (hcover : ∀ edge : E, edge ∈ edges)
    (seed : ∀ vertex, Fiber vertex) (n : ℕ)
    (hfixed : T.relaxSweep edges (T.sweepRelaxation edges seed n) =
      T.sweepRelaxation edges seed n) :
    seed ≤ T.sweepRelaxation edges seed n ∧
      T.IsLaxSection (T.sweepRelaxation edges seed n) ∧
      ∀ majorant : ∀ vertex, Fiber vertex,
        seed ≤ majorant → T.IsLaxSection majorant →
          T.sweepRelaxation edges seed n ≤ majorant := by
  refine ⟨T.monotone_sweepRelaxation edges seed (Nat.zero_le n),
    T.isLaxSection_of_relaxSweep_eq hcover hfixed, ?_⟩
  intro majorant hseed hmaj
  exact T.sweepRelaxation_le_of_le hmono edges hseed hmaj n

end Sweep

section SweepLeastMajorant

variable [DecidableEq V] [∀ vertex : V, CompleteLattice (Fiber vertex)]

/-- A sweep iterate that is unchanged by the next covering sweep is the least lax majorant.
This is the stopping-correctness theorem for an observed finite computation; it requires no
ascending-chain hypothesis. -/
theorem sweepRelaxation_eq_leastLaxMajorant_of_relaxSweep_eq
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    {edges : List E} (hcover : ∀ edge : E, edge ∈ edges)
    (seed : ∀ vertex, Fiber vertex) (n : ℕ)
    (hfixed : T.relaxSweep edges (T.sweepRelaxation edges seed n) =
      T.sweepRelaxation edges seed n) :
    T.sweepRelaxation edges seed n = T.leastLaxMajorant hmono seed := by
  have hlax : T.IsLaxSection (T.sweepRelaxation edges seed n) :=
    T.isLaxSection_of_relaxSweep_eq hcover hfixed
  have hseed : seed ≤ T.sweepRelaxation edges seed n :=
    T.monotone_sweepRelaxation edges seed (Nat.zero_le n)
  apply le_antisymm
  · exact T.sweepRelaxation_le_of_le hmono edges
      (T.leastLaxMajorant_isLeast hmono seed).1
      (T.leastLaxMajorant_isLeast hmono seed).2.1 n
  · exact (T.leastLaxMajorant_isLeast hmono seed).2.2 _ hseed hlax

/-- Under ACC, repeated sweeps over a covering list eventually equal the least lax majorant. -/
theorem exists_sweepRelaxation_eq_leastLaxMajorant
    [WellFoundedGT (∀ vertex, Fiber vertex)]
    (hmono : ∀ edge : E, Monotone (T.edgeMap edge))
    {edges : List E} (hcover : ∀ edge : E, edge ∈ edges)
    (seed : ∀ vertex, Fiber vertex) :
    ∃ n, ∀ m, n ≤ m →
      T.sweepRelaxation edges seed m = T.leastLaxMajorant hmono seed := by
  let run : ℕ →o (∀ vertex, Fiber vertex) :=
    ⟨T.sweepRelaxation edges seed, T.monotone_sweepRelaxation edges seed⟩
  obtain ⟨n, hstable⟩ := WellFoundedGT.monotone_chain_condition run
  have hfixed : T.relaxSweep edges (T.sweepRelaxation edges seed n) =
      T.sweepRelaxation edges seed n := by
    rw [← T.sweepRelaxation_succ]
    exact (hstable (n + 1) (Nat.le_succ n)).symm
  have hlax : T.IsLaxSection (T.sweepRelaxation edges seed n) :=
    T.isLaxSection_of_relaxSweep_eq hcover hfixed
  have hseed : seed ≤ T.sweepRelaxation edges seed n :=
    T.monotone_sweepRelaxation edges seed (Nat.zero_le n)
  have hleast_le : T.leastLaxMajorant hmono seed ≤ T.sweepRelaxation edges seed n :=
    (T.leastLaxMajorant_isLeast hmono seed).2.2 _ hseed hlax
  have hrun_le : T.sweepRelaxation edges seed n ≤ T.leastLaxMajorant hmono seed :=
    T.sweepRelaxation_le_of_le hmono edges
      (T.leastLaxMajorant_isLeast hmono seed).1
      (T.leastLaxMajorant_isLeast hmono seed).2.1 n
  have hn : T.sweepRelaxation edges seed n = T.leastLaxMajorant hmono seed :=
    le_antisymm hrun_le hleast_le
  exact ⟨n, fun m hnm ↦ (hstable m hnm).symm.trans hn⟩

end SweepLeastMajorant

end Transport
end Maths

end
