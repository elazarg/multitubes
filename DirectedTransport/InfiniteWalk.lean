/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DirectedTransport.Circulation
public import Mathlib.Data.Set.Finite.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Mathlib.Data.List.OfFn

/-!
# Infinite walks, cyclic words, and bounded discrepancy

An infinite walk of an `DirectedTransport.EdgeGraph` is a sequence of edges whose consecutive
endpoints match, starting at a prescribed vertex. Its prefix charge at time `n` is the total
charge of the first `n` edges, and the walk has bounded discrepancy when the set of values
that prefix charge takes is finite. For an integer lattice of charges this is exactly
boundedness in any norm, but the finite-range form is what the arguments consume.

A cyclic word is a nonempty edge word that closes up at a base vertex, wraparound included.
Repeating it forever produces an infinite walk, and if the word carries no net charge that
walk has bounded discrepancy: the prefix charge is then genuinely periodic, so its range is
the image of one period. Bounded discrepancy also survives prepending any finite legal
transient, since that only translates and extends the prefix-charge range by finitely much.

## Main definitions

* `DirectedTransport.EdgeGraph.CyclicWord`: a nonempty closed edge word based at a vertex.
* `DirectedTransport.EdgeGraph.InfiniteWalk`: an infinite directed walk from a vertex.
* `DirectedTransport.EdgeGraph.InfiniteWalk.prefixCharge`,
  `DirectedTransport.EdgeGraph.InfiniteWalk.HasBoundedDiscrepancy`: the cumulative charge and
  the finiteness of its range.
* `DirectedTransport.EdgeGraph.InfiniteWalk.IsEventuallyPeriodic`: edge-level eventual
  periodicity with an explicit transient and positive period.
* `DirectedTransport.EdgeGraph.CyclicWord.toInfiniteWalk`,
  `DirectedTransport.EdgeGraph.Walk.prependInfinite`: repetition of a cyclic word, and
  prefixing an infinite walk by a finite one.

## Main results

* `DirectedTransport.EdgeGraph.CyclicWord.hasBoundedDiscrepancy_of_wordCharge_zero`: repeating
  a nonempty zero-charge cyclic word has bounded discrepancy.
* `DirectedTransport.EdgeGraph.Walk.hasBoundedDiscrepancy_prependInfinite`: a finite legal
  transient preserves bounded discrepancy.
* `DirectedTransport.EdgeGraph.InfiniteWalk.segment_charge`: the charge of a finite segment is
  the difference of the prefix charges at its endpoints.

## Tags

infinite walk, cyclic word, bounded discrepancy, eventual periodicity, prefix charge
-/

@[expose] public section

namespace DirectedTransport

/-- A sequence invariant under a positive shift takes only finitely many values. -/
private theorem finite_range_of_add_period {α : Type*} (sequence : ℕ → α)
    (period : ℕ) (hperiodPos : 0 < period)
    (hperiod : ∀ n, sequence (n + period) = sequence n) :
    Set.Finite (Set.range sequence) := by
  have hremainder : ∀ n, ∃ r < period, sequence n = sequence r := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
        by_cases hn : n < period
        · exact ⟨n, hn, rfl⟩
        · obtain ⟨r, hr, her⟩ := ih (n - period) (by omega)
          refine ⟨r, hr, ?_⟩
          rw [← show n - period + period = n by omega, hperiod (n - period)]
          exact her
  refine ((Finset.range period).finite_toSet.image sequence).subset ?_
  rintro value ⟨n, rfl⟩
  obtain ⟨r, hr, heq⟩ := hremainder n
  exact ⟨r, by simpa using hr, heq.symm⟩

namespace EdgeGraph

universe uV uE uκ

variable {V : Type uV} {E : Type uE} (G : EdgeGraph V E)

/-! ### Cyclic words -/

/-- A nonempty cyclic word of edge identities based at `base`. The endpoint conditions include
the wraparound edge compatibility. -/
structure CyclicWord (base : V) where
  /-- The edge identities of one period, in chronological order. -/
  word : List E
  /-- The period is nonempty. -/
  nonempty : word ≠ []
  /-- Consecutive edges of the period have matching endpoints. -/
  compatible : word.IsChain fun first second => G.target first = G.source second
  /-- The period starts at the base vertex. -/
  first_source : G.source (word.head nonempty) = base
  /-- The period returns to the base vertex. -/
  last_target : G.target (word.getLast nonempty) = base

namespace CyclicWord

variable {G} {base : V}

/-- The positive length of the cyclic word. -/
abbrev periodLength (cycle : G.CyclicWord base) : ℕ := cycle.word.length

theorem periodLength_pos (cycle : G.CyclicWord base) : 0 < cycle.periodLength := by
  simpa [periodLength, List.length_pos_iff] using cycle.nonempty

/-- The edge at time `n` in the infinite repetition of a cyclic word. -/
def edgeAt (cycle : G.CyclicWord base) (n : ℕ) : E :=
  cycle.word[n % cycle.periodLength]'(Nat.mod_lt _ cycle.periodLength_pos)

theorem source_edgeAt_zero (cycle : G.CyclicWord base) :
    G.source (cycle.edgeAt 0) = base := by
  simp only [edgeAt, Nat.zero_mod]
  simpa [List.head_eq_getElem_zero] using cycle.first_source

theorem edgeAt_add_period (cycle : G.CyclicWord base) (n : ℕ) :
    cycle.edgeAt (n + cycle.periodLength) = cycle.edgeAt n := by
  simp [edgeAt, periodLength]

/-- Successive entries of the cyclic repetition remain graph-compatible, including the
last-to-first wraparound. -/
theorem target_edgeAt_eq_source_succ (cycle : G.CyclicWord base) (n : ℕ) :
    G.target (cycle.edgeAt n) = G.source (cycle.edgeAt (n + 1)) := by
  have hpos : 0 < cycle.word.length := cycle.periodLength_pos
  have hlt : n % cycle.word.length < cycle.word.length := Nat.mod_lt _ hpos
  have hmod : (n + 1) % cycle.word.length =
      (n % cycle.word.length + 1) % cycle.word.length :=
    (Nat.mod_add_mod n cycle.word.length 1).symm
  simp only [edgeAt, periodLength, hmod]
  rcases Nat.lt_or_ge (n % cycle.word.length + 1) cycle.word.length with hnext | hge
  · simp only [Nat.mod_eq_of_lt hnext]
    exact cycle.compatible.getElem (n % cycle.word.length) hnext
  · have hwrap : n % cycle.word.length + 1 = cycle.word.length := by omega
    simp only [hwrap, Nat.mod_self]
    have hboundary := cycle.last_target.trans cycle.first_source.symm
    rw [List.getLast_eq_getElem, List.head_eq_getElem_zero] at hboundary
    simpa only [show n % cycle.word.length = cycle.word.length - 1 by omega] using hboundary

end CyclicWord

namespace Walk

variable {G} {base : V}

/-- A nonempty closed typed walk, viewed as a cyclic edge word. -/
def toCyclicWord (walk : G.Walk base base) (hne : 0 < walk.length) : G.CyclicWord base where
  word := walk.edges
  nonempty := walk.edges_ne_nil_of_length_pos hne
  compatible := walk.edges_isChain
  first_source := walk.source_head (walk.edges_ne_nil_of_length_pos hne)
  last_target := walk.target_getLast (walk.edges_ne_nil_of_length_pos hne)

@[simp] theorem toCyclicWord_word (walk : G.Walk base base) (hne : 0 < walk.length) :
    (walk.toCyclicWord hne).word = walk.edges := rfl

@[simp] theorem toCyclicWord_periodLength (walk : G.Walk base base) (hne : 0 < walk.length) :
    (walk.toCyclicWord hne).periodLength = walk.length := walk.edges_length

end Walk

/-! ### Infinite walks -/

/-- An infinite directed walk from a prescribed initial vertex. Its vertex at time `n` is
derived from the preceding edge, so the only compatibility data are the initial source and
consecutive edge endpoints. -/
structure InfiniteWalk (start : V) where
  /-- The edge traversed at each time. -/
  edge : ℕ → E
  /-- The first edge leaves the initial vertex. -/
  source_zero : G.source (edge 0) = start
  /-- Consecutive edges have matching endpoints. -/
  consecutive : ∀ n, G.target (edge n) = G.source (edge (n + 1))

namespace CyclicWord

variable {G} {base : V}

/-- Infinite repetition of a graph-compatible cyclic word. -/
def toInfiniteWalk (cycle : G.CyclicWord base) : G.InfiniteWalk base where
  edge := cycle.edgeAt
  source_zero := cycle.source_edgeAt_zero
  consecutive := cycle.target_edgeAt_eq_source_succ

@[simp] theorem toInfiniteWalk_edge (cycle : G.CyclicWord base) (n : ℕ) :
    cycle.toInfiniteWalk.edge n = cycle.edgeAt n := rfl

end CyclicWord

namespace InfiniteWalk

variable {G} {start : V}

/-- Vertex occupied before edge `n` is traversed. -/
def vertex (walk : G.InfiniteWalk start) : ℕ → V
  | 0 => start
  | n + 1 => G.target (walk.edge n)

theorem source_edge (walk : G.InfiniteWalk start) (n : ℕ) :
    G.source (walk.edge n) = walk.vertex n := by
  match n with
  | 0 => exact walk.source_zero
  | n + 1 => exact (walk.consecutive n).symm

/-- Integer cumulative charge before time `n`. -/
def prefixCharge (walk : G.InfiniteWalk start) {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) : ℕ → κ → ℤ
  | 0 => 0
  | n + 1 => prefixCharge walk edgeCharge n + edgeCharge (walk.edge n)

/-- Prefix charge as a finite sum over elapsed times. -/
theorem prefixCharge_eq_sum_range (walk : G.InfiniteWalk start) {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (horizon : ℕ) :
    walk.prefixCharge edgeCharge horizon =
      ∑ n ∈ Finset.range horizon, edgeCharge (walk.edge n) := by
  induction horizon with
  | zero => simp [prefixCharge]
  | succ horizon ih => simp [prefixCharge, Finset.sum_range_succ, ih]

/-- Finite-range form of bounded discrepancy. For a finite-dimensional integer lattice this is
equivalent to boundedness in any norm. -/
def HasBoundedDiscrepancy (walk : G.InfiniteWalk start) {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) : Prop :=
  Set.Finite (Set.range (walk.prefixCharge edgeCharge))

/-- The first `n` edges as a finite walk. -/
def take (walk : G.InfiniteWalk start) : (n : ℕ) → G.Walk start (walk.vertex n)
  | 0 => .nil
  | n + 1 => .concat (take walk n) (walk.edge n) (walk.source_edge n)

@[simp] theorem take_length (walk : G.InfiniteWalk start) (n : ℕ) :
    (walk.take n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (· + 1) ih

@[simp] theorem take_charge (walk : G.InfiniteWalk start) {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (n : ℕ) :
    (walk.take n).charge edgeCharge = walk.prefixCharge edgeCharge n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (· + edgeCharge (walk.edge n)) ih

/-- The next `length` edges beginning at time `startTime`. -/
def segment (walk : G.InfiniteWalk start) (startTime : ℕ) : (length : ℕ) →
    G.Walk (walk.vertex startTime) (walk.vertex (startTime + length))
  | 0 => .nil
  | length + 1 =>
      Walk.concat (segment walk startTime length)
        (walk.edge (startTime + length)) (walk.source_edge _)

@[simp] theorem segment_length (walk : G.InfiniteWalk start) (startTime length : ℕ) :
    (walk.segment startTime length).length = length := by
  induction length with
  | zero => rfl
  | succ length ih => exact congrArg (· + 1) ih

/-- The charge of a finite segment is the difference of the prefix charges at its
endpoints. -/
theorem segment_charge (walk : G.InfiniteWalk start) {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (startTime length : ℕ) :
    (walk.segment startTime length).charge edgeCharge =
      walk.prefixCharge edgeCharge (startTime + length) -
        walk.prefixCharge edgeCharge startTime := by
  induction length with
  | zero => simp [segment]
  | succ length ih =>
      have hstep : (walk.segment startTime (length + 1)).charge edgeCharge =
          (walk.segment startTime length).charge edgeCharge +
            edgeCharge (walk.edge (startTime + length)) := rfl
      have hnext : walk.prefixCharge edgeCharge (startTime + (length + 1)) =
          walk.prefixCharge edgeCharge (startTime + length) +
            edgeCharge (walk.edge (startTime + length)) := rfl
      rw [hstep, ih, hnext]
      abel

/-- Put one legal edge in front of an infinite walk. -/
def prependEdge (before : V) (edge : E) (hsource : G.source edge = before)
    (tail : G.InfiniteWalk (G.target edge)) : G.InfiniteWalk before where
  edge
    | 0 => edge
    | n + 1 => tail.edge n
  source_zero := hsource
  consecutive
    | 0 => tail.source_zero.symm
    | n + 1 => tail.consecutive n

@[simp] theorem prependEdge_edge_zero (before : V) (edge : E)
    (hsource : G.source edge = before) (tail : G.InfiniteWalk (G.target edge)) :
    (prependEdge before edge hsource tail).edge 0 = edge := rfl

@[simp] theorem prependEdge_edge_succ (before : V) (edge : E)
    (hsource : G.source edge = before) (tail : G.InfiniteWalk (G.target edge)) (n : ℕ) :
    (prependEdge before edge hsource tail).edge (n + 1) = tail.edge n := rfl

/-- Prefixing one edge shifts the prefix charge by that edge's charge. -/
theorem prefixCharge_prependEdge_succ {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (before : V) (edge : E)
    (hsource : G.source edge = before) (tail : G.InfiniteWalk (G.target edge)) (n : ℕ) :
    (prependEdge before edge hsource tail).prefixCharge edgeCharge (n + 1) =
      edgeCharge edge + tail.prefixCharge edgeCharge n := by
  induction n with
  | zero => simp [prefixCharge]
  | succ n ih =>
      rw [prefixCharge, ih, prependEdge_edge_succ, prefixCharge]
      abel

/-- Adding one finite initial edge preserves finite-range discrepancy. -/
theorem hasBoundedDiscrepancy_prependEdge {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (before : V) (edge : E)
    (hsource : G.source edge = before) (tail : G.InfiniteWalk (G.target edge))
    (hbounded : tail.HasBoundedDiscrepancy edgeCharge) :
    (prependEdge before edge hsource tail).HasBoundedDiscrepancy edgeCharge := by
  refine ((Set.finite_singleton 0).union
    (hbounded.image fun value => edgeCharge edge + value)).subset ?_
  rintro value ⟨n, rfl⟩
  match n with
  | 0 => exact Set.mem_union_left _ (Set.mem_singleton 0)
  | n + 1 =>
      refine Set.mem_union_right _ ⟨tail.prefixCharge edgeCharge n, ⟨n, rfl⟩, ?_⟩
      exact (prefixCharge_prependEdge_succ edgeCharge before edge hsource tail n).symm

/-- Edge-level eventual periodicity, with an explicit finite transient and positive period. -/
def IsEventuallyPeriodic (walk : G.InfiniteWalk start) : Prop :=
  ∃ transient period, 0 < period ∧
    ∀ n, walk.edge (transient + n + period) = walk.edge (transient + n)

end InfiniteWalk

namespace Walk

variable {G} {start finish : V}

/-- Put a finite typed walk in front of an infinite continuation. -/
def prependInfinite {start : V} : {finish : V} →
    G.Walk start finish → G.InfiniteWalk finish → G.InfiniteWalk start
  | _, .nil, tail => tail
  | _, .concat walkSoFar edge legal, tail =>
      prependInfinite walkSoFar (InfiniteWalk.prependEdge _ edge legal tail)

/-- After the finite prefix length, the prepended walk is exactly its continuation. -/
theorem prependInfinite_edge_length_add (walk : G.Walk start finish)
    (tail : G.InfiniteWalk finish) (n : ℕ) :
    (walk.prependInfinite tail).edge (walk.length + n) = tail.edge n := by
  induction walk generalizing n with
  | nil => simp only [prependInfinite, length_nil, Nat.zero_add]
  | concat walkSoFar edge legal ih =>
      rw [prependInfinite, length_concat,
        show walkSoFar.length + 1 + n = walkSoFar.length + (n + 1) by omega, ih]
      rfl

/-- Every finite legal transient preserves bounded discrepancy. -/
theorem hasBoundedDiscrepancy_prependInfinite {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (walk : G.Walk start finish)
    (tail : G.InfiniteWalk finish)
    (hbounded : tail.HasBoundedDiscrepancy edgeCharge) :
    (walk.prependInfinite tail).HasBoundedDiscrepancy edgeCharge := by
  induction walk with
  | nil => exact hbounded
  | concat walkSoFar edge legal ih =>
      exact ih _ (InfiniteWalk.hasBoundedDiscrepancy_prependEdge
        edgeCharge _ edge legal tail hbounded)

end Walk

/-! ### Repeating a zero-charge cyclic word -/

namespace CyclicWord

variable {G} {base : V}

/-- One full period of the canonical repetition has the charge obtained by summing the finite
cyclic word. -/
theorem prefixCharge_periodLength {κ : Type uκ} (cycle : G.CyclicWord base)
    (edgeCharge : E → κ → ℤ) :
    cycle.toInfiniteWalk.prefixCharge edgeCharge cycle.periodLength =
      (cycle.word.map edgeCharge).sum := by
  rw [InfiniteWalk.prefixCharge_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  calc
    (∑ i : Fin cycle.periodLength, edgeCharge (cycle.toInfiniteWalk.edge i)) =
        (List.ofFn fun i : Fin cycle.word.length => edgeCharge cycle.word[i]).sum := by
          rw [List.sum_ofFn]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [toInfiniteWalk, edgeAt, Nat.mod_eq_of_lt i.isLt]
    _ = (cycle.word.map edgeCharge).sum := by
      congr 1
      simp

/-- Zero charge over one cyclic word makes every prefix-charge coordinate periodic with the
same positive period. -/
theorem prefixCharge_add_period_of_wordCharge_zero {κ : Type uκ}
    (cycle : G.CyclicWord base) (edgeCharge : E → κ → ℤ)
    (hzero : (cycle.word.map edgeCharge).sum = 0) (n : ℕ) :
    cycle.toInfiniteWalk.prefixCharge edgeCharge (n + cycle.periodLength) =
      cycle.toInfiniteWalk.prefixCharge edgeCharge n := by
  induction n with
  | zero =>
      simpa [InfiniteWalk.prefixCharge] using
        (cycle.prefixCharge_periodLength edgeCharge).trans hzero
  | succ n ih =>
      rw [show n + 1 + cycle.periodLength = n + cycle.periodLength + 1 by omega,
        InfiniteWalk.prefixCharge, InfiniteWalk.prefixCharge, ih, toInfiniteWalk_edge,
        toInfiniteWalk_edge, cycle.edgeAt_add_period]

/-- Repeating a nonempty zero-charge cyclic word has bounded discrepancy. -/
theorem hasBoundedDiscrepancy_of_wordCharge_zero {κ : Type uκ}
    (cycle : G.CyclicWord base) (edgeCharge : E → κ → ℤ)
    (hzero : (cycle.word.map edgeCharge).sum = 0) :
    cycle.toInfiniteWalk.HasBoundedDiscrepancy edgeCharge :=
  finite_range_of_add_period (cycle.toInfiniteWalk.prefixCharge edgeCharge)
    cycle.periodLength cycle.periodLength_pos
    (cycle.prefixCharge_add_period_of_wordCharge_zero edgeCharge hzero)

end CyclicWord

end EdgeGraph

end DirectedTransport
