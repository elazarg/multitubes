/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import DirectedTransport.Additive.Potentials

import DirectedTransport.Additive.ShortCycles
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic.Linarith

/-!
# Karp's cycle-mean formula and the attained max-plus spectral threshold

`DirectedTransport.Additive.Potentials` characterizes the existence of a potential, that is
of a max-plus subeigenvector, by the absence of a closed walk of excessive mean weight, and
`DirectedTransport.Additive.ShortCycles` shows that the maximum cycle mean is attained on a
closed walk no longer than the number of vertices.  Two things are developed here on top of
that.

First, the composite of the two: some short cycle is an exact threshold, so the set of
admissible max-plus eigenvalues is the closed ray above its mean.  That mean is the max
cycle mean, the tropical spectral radius, or the max-plus Perron root.

Second, Karp's formula for that same quantity.  Write `n` for the number of vertices and
`D k v` for the `k`-step Bellman value at `v`, the greatest weight of a walk arriving at `v`
along exactly `k` edges.  Karp's identity is

`max cycle mean = max over v of min over 0 ≤ k < n of (D n v - D k v) / (n - k)`.

The `k`-step table is genuinely new here: the potential file records only the all-walks
maximum `DirectedTransport.MaxPlusPotential.maxIncomingWeight`, which is the value of the
same recursion run to stationarity.

## Main definitions

* `DirectedTransport.MaxPlusPotential.lengthIncomingWeights`: the weights realized by the
  walks arriving at a vertex along a prescribed number of edges.
* `DirectedTransport.MaxPlusPotential.stepValue`: the `k`-step Bellman value, the greatest
  element of that finite set.

## Main results

* `DirectedTransport.MaxPlusPotential.exists_stepValue_sub_le`: the upper half of Karp's
  formula.  At every vertex some `k < n` makes the Karp difference quotient at most the
  cycle-mean bound, obtained by deleting a closed subwalk from a maximizing walk of length
  `n`.
* `DirectedTransport.MaxPlusPotential.exists_le_stepValue_sub`: the lower half.  If the
  bound is attained by some closed walk then at some vertex every Karp difference quotient
  is at least the bound; the vertex is read off an optimal walk prolonged along the
  attaining cycle.
* `DirectedTransport.MaxPlusPotential.sup'_inf'_stepValue_div`: **Karp's formula**, over an
  arbitrary linearly ordered field, relative to a given mean-maximizing cycle.
* `DirectedTransport.MaxPlusPotential.exists_short_closedWalk_sup'_inf'_stepValue_div`: over
  the reals the maximizing cycle need not be assumed, since it is supplied by
  `DirectedTransport.AdditiveTransport.exists_short_closedWalk_maximizing_mean`.
* `DirectedTransport.MaxPlusPotential.exists_critical_cycle_subeigenvector_iff`: the
  attained max-plus spectral threshold, a short cycle deciding subeigenvector existence for
  every candidate eigenvalue.
* `DirectedTransport.EdgeGraph.Walk.exists_split_of_length_le`: the walk-splitting lemma the
  lower half needs, stated where it is used rather than in the walk calculus.

## Implementation notes

Karp's classical statement assumes the digraph strongly connected, or at least that every
vertex is reachable from a fixed source.  What the proof below actually needs is weaker and
is assumed literally: every vertex has an incoming edge, `∀ vertex, ∃ e, G.target e = vertex`.
That is exactly what makes a walk of every prescribed length arrive at every vertex, so that
each `stepValue` is a maximum over a nonempty set, and it is implied by strong connectivity
on at least two vertices.  Connectivity is used nowhere else: the value table here starts
from the zero vector rather than from a source, so no vertex needs to be reachable from any
other.

`DirectedTransport.MaxPlusPotential.stepValue` is total, taking the junk value `0` when no
walk of the given length arrives, which the incoming-edge hypothesis rules out.  This keeps
it a plain function rather than one depending on a proof.

Karp's formula is stated with `Finset.sup'` over the vertices and `Finset.inf'` over
`Finset.range n`; both index sets are nonempty exactly because the vertex type is, which is
why `[Nonempty V]` appears.  The general-field version takes the mean-maximizing cycle as a
hypothesis; only the real version invokes attainment, because
`DirectedTransport.Additive.ShortCycles` is stated over the reals.

## References

* R. M. Karp, *A characterization of the minimum cycle mean in a digraph*, Discrete
  Mathematics 23 (1978), 309-311.
* F. Baccelli, G. Cohen, G. J. Olsder and J.-P. Quadrat, *Synchronization and Linearity*,
  Wiley (1992), Chapter 3, for max-plus spectral theory.

## Tags

Karp, cycle mean, max cycle mean, max-plus, tropical, Perron root, Bellman, mean payoff
-/

@[expose] public section

namespace DirectedTransport

noncomputable section

namespace EdgeGraph.Walk

universe uV uE

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

/-- A walk splits after any prescribed number of its edges. -/
theorem exists_split_of_length_le {start finish : V} (walk : G.Walk start finish)
    {count : ℕ} (hcount : count ≤ walk.length) :
    ∃ (middle : V) (before : G.Walk start middle) (after : G.Walk middle finish),
      before.length = count ∧ walk.edges = before.edges ++ after.edges := by
  induction walk with
  | nil =>
      have hzero : count = 0 := Nat.le_zero.mp hcount
      exact ⟨start, .nil, .nil, hzero.symm ▸ rfl, by simp⟩
  | @concat middle walkSoFar edge legal ih =>
      rcases Nat.lt_or_ge count (walkSoFar.length + 1) with hlt | hge
      · obtain ⟨mid, before, after, hlen, hedges⟩ := ih (Nat.lt_succ_iff.mp hlt)
        exact ⟨mid, before, after.concat edge legal, hlen, by
          simp only [edges_concat, hedges, List.append_assoc]⟩
      · have hEq : count = walkSoFar.length + 1 := by
          simp only [length_concat] at hcount
          omega
        exact ⟨_, walkSoFar.concat edge legal, .nil, by simp [hEq], by simp⟩

end EdgeGraph.Walk

namespace MaxPlusPotential

universe uV uE

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}

/-! ### Walks of a prescribed length -/

/-- Every vertex is the endpoint of a walk with any prescribed number of edges, as soon as
every vertex has an incoming edge. -/
theorem exists_walk_length_eq (hin : ∀ vertex : V, ∃ e : E, G.target e = vertex)
    (count : ℕ) (vertex : V) :
    ∃ (start : V) (walk : G.Walk start vertex), walk.length = count := by
  induction count generalizing vertex with
  | zero => exact ⟨vertex, .nil, rfl⟩
  | succ count ih =>
      obtain ⟨e, he⟩ := hin vertex
      obtain ⟨start, walk, hlen⟩ := ih (G.source e)
      exact ⟨start, (walk.concat e rfl).castFinish he, by simp [hlen]⟩

/-- Weights of the walks arriving at a vertex with a prescribed number of edges. -/
def lengthIncomingWeights (G : EdgeGraph V E) (weight : E → 𝕜) (count : ℕ)
    (vertex : V) : Set 𝕜 :=
  {r | ∃ (start : V) (walk : G.Walk start vertex),
    walk.length = count ∧ walkWeight weight walk = r}

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- With finitely many edges only finitely many weights are realized by walks of a fixed
length, since such a walk is determined by its edge list. -/
theorem finite_lengthIncomingWeights [Finite E] (weight : E → 𝕜) (count : ℕ)
    (vertex : V) :
    (lengthIncomingWeights G weight count vertex).Finite := by
  refine Set.Finite.subset
    ((List.finite_length_le E count).image fun l => (l.map weight).sum) ?_
  rintro r ⟨start, walk, hlen, rfl⟩
  exact ⟨walk.edges, by simp [EdgeGraph.Walk.edges_length, hlen], rfl⟩

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Under the incoming-edge hypothesis every length realizes at least one weight. -/
theorem nonempty_lengthIncomingWeights
    (hin : ∀ vertex : V, ∃ e : E, G.target e = vertex) (weight : E → 𝕜)
    (count : ℕ) (vertex : V) :
    (lengthIncomingWeights G weight count vertex).Nonempty := by
  obtain ⟨start, walk, hlen⟩ := exists_walk_length_eq hin count vertex
  exact ⟨walkWeight weight walk, start, walk, hlen, rfl⟩

/-! ### The step-value table -/

/-- The `k`-step Bellman value at a vertex: the greatest weight of a walk arriving there
along exactly `count` edges.  This is the entry of the `count`-th max-plus power of the
weight matrix applied to the zero vector.  When no such walk exists the value is `0` by
convention; every result below assumes the incoming-edge hypothesis
`∀ vertex, ∃ e, G.target e = vertex`, under which that case never occurs. -/
def stepValue [Finite E] (G : EdgeGraph V E) (weight : E → 𝕜) (count : ℕ)
    (vertex : V) : 𝕜 :=
  ((finite_lengthIncomingWeights (G := G) weight count vertex).toFinset.max).unbotD 0

omit [IsStrictOrderedRing 𝕜] in
/-- The step value dominates the weight of every walk arriving along exactly that many
edges. -/
theorem le_stepValue [Finite E] {weight : E → 𝕜} {count : ℕ} {vertex : V} {r : 𝕜}
    (hr : r ∈ lengthIncomingWeights G weight count vertex) :
    r ≤ stepValue G weight count vertex := by
  have hfin := finite_lengthIncomingWeights (G := G) weight count vertex
  have hmem : r ∈ hfin.toFinset := hfin.mem_toFinset.2 hr
  obtain ⟨a, ha⟩ := Finset.max_of_nonempty ⟨r, hmem⟩
  have hle : (r : WithBot 𝕜) ≤ (a : WithBot 𝕜) := ha ▸ Finset.le_max hmem
  simpa [stepValue, ha] using (WithBot.coe_le_coe.mp hle)

omit [IsStrictOrderedRing 𝕜] in
/-- Under the incoming-edge hypothesis the step value is itself realized by a walk. -/
theorem stepValue_mem [Finite E]
    (hin : ∀ vertex : V, ∃ e : E, G.target e = vertex) (weight : E → 𝕜)
    (count : ℕ) (vertex : V) :
    stepValue G weight count vertex ∈ lengthIncomingWeights G weight count vertex := by
  have hfin := finite_lengthIncomingWeights (G := G) weight count vertex
  have hne : hfin.toFinset.Nonempty :=
    hfin.toFinset_nonempty.2 (nonempty_lengthIncomingWeights hin weight count vertex)
  obtain ⟨a, ha⟩ := Finset.max_of_nonempty hne
  have hmem := Finset.mem_of_max ha
  simpa [stepValue, ha] using hfin.mem_toFinset.1 hmem

omit [IsStrictOrderedRing 𝕜] in
/-- The walk realizing the step value. -/
theorem exists_walk_walkWeight_eq_stepValue [Finite E]
    (hin : ∀ vertex : V, ∃ e : E, G.target e = vertex) (weight : E → 𝕜)
    (count : ℕ) (vertex : V) :
    ∃ (start : V) (walk : G.Walk start vertex),
      walk.length = count ∧ walkWeight weight walk = stepValue G weight count vertex :=
  stepValue_mem hin weight count vertex

/-- Shifting every edge weight by a constant shifts the `count`-step value by `count` times
that constant. -/
theorem stepValue_sub_const [Finite E]
    (hin : ∀ vertex : V, ∃ e : E, G.target e = vertex) (weight : E → 𝕜) (lam : 𝕜)
    (count : ℕ) (vertex : V) :
    stepValue G (fun e => weight e - lam) count vertex
      = stepValue G weight count vertex - count * lam := by
  refine le_antisymm ?_ ?_
  · obtain ⟨start, walk, hlen, hwt⟩ :=
      exists_walk_walkWeight_eq_stepValue hin (fun e => weight e - lam) count vertex
    rw [← hwt, walkWeight_sub_const, hlen]
    have := le_stepValue (G := G) (weight := weight) (count := count) (vertex := vertex)
      ⟨start, walk, hlen, rfl⟩
    linarith
  · obtain ⟨start, walk, hlen, hwt⟩ :=
      exists_walk_walkWeight_eq_stepValue hin weight count vertex
    have hmem := le_stepValue (G := G) (weight := fun e => weight e - lam) (count := count)
      (vertex := vertex) ⟨start, walk, hlen, rfl⟩
    rw [walkWeight_sub_const, hlen, hwt] at hmem
    linarith

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Iterating a closed walk multiplies both its length and its weight. -/
theorem exists_closedWalk_length_mul (weight : E → 𝕜) {base : V}
    (cycle : G.Walk base base) (times : ℕ) :
    ∃ iterated : G.Walk base base,
      iterated.length = times * cycle.length ∧
        walkWeight weight iterated = times * walkWeight weight cycle := by
  induction times with
  | zero => exact ⟨.nil, by simp, by simp⟩
  | succ times ih =>
      obtain ⟨iterated, hlen, hwt⟩ := ih
      refine ⟨iterated.append cycle, by simp [hlen]; ring, ?_⟩
      rw [walkWeight_append, hwt]
      push_cast
      ring

/-! ### The two halves of Karp's formula -/

/-- **Upper half of Karp's formula.**  If every closed walk has mean weight at most `lam`,
then at every vertex some `k` below the number of vertices makes the Karp difference
quotient at most `lam`.  The witness is obtained by deleting a closed subwalk from a
maximizing walk of length `Fintype.card V`, which must revisit a vertex. -/
theorem exists_stepValue_sub_le [Fintype V] [Finite E]
    (hin : ∀ vertex : V, ∃ e : E, G.target e = vertex) (weight : E → 𝕜) (lam : 𝕜)
    (hcyc : ∀ (base : V) (cycle : G.Walk base base),
      walkWeight weight cycle ≤ cycle.length * lam)
    (vertex : V) :
    ∃ count < Fintype.card V,
      stepValue G weight (Fintype.card V) vertex - stepValue G weight count vertex
        ≤ ((Fintype.card V : 𝕜) - count) * lam := by
  obtain ⟨start, walk, hlen, hwt⟩ :=
    exists_walk_walkWeight_eq_stepValue hin weight (Fintype.card V) vertex
  have hdup : ¬ walk.visited.Nodup := by
    intro hnodup
    have hcard := hnodup.length_le_card
    rw [EdgeGraph.Walk.length_visited, hlen] at hcard
    omega
  obtain ⟨middle, before, inner, after, hinner, hedges⟩ :=
    walk.exists_closedSubwalk_of_not_nodup hdup
  have hlengths : walk.length = before.length + inner.length + after.length := by
    have hcongr := congrArg List.length hedges
    simp only [EdgeGraph.Walk.edges_length, List.length_append] at hcongr
    omega
  refine ⟨before.length + after.length, by omega, ?_⟩
  have hsplit : walkWeight weight walk
      = walkWeight weight inner + walkWeight weight (before.append after) := by
    simp only [walkWeight, hedges, List.map_append, List.sum_append,
      EdgeGraph.Walk.edges_append]
    ring
  have hle := le_stepValue (G := G) (weight := weight)
    (count := before.length + after.length) (vertex := vertex)
    ⟨start, before.append after, by simp, rfl⟩
  have hcast : ((Fintype.card V : 𝕜) - ((before.length + after.length : ℕ) : 𝕜))
      = (inner.length : 𝕜) := by
    have : Fintype.card V = (before.length + after.length) + inner.length := by omega
    rw [this]
    push_cast
    ring
  rw [hcast]
  have hinnerBound := hcyc middle inner
  linarith [hwt, hsplit]

/-- **Lower half of Karp's formula.**  If every closed walk has mean weight at most `lam`
and some closed walk attains `lam`, then at some vertex the `Fintype.card V`-step value
dominates every other step value by the corresponding multiple of `lam`. -/
theorem exists_le_stepValue_sub [Fintype V] [Finite E]
    (hin : ∀ vertex : V, ∃ e : E, G.target e = vertex) (weight : E → 𝕜) (lam : 𝕜)
    (hcyc : ∀ (base : V) (cycle : G.Walk base base),
      walkWeight weight cycle ≤ cycle.length * lam)
    {base : V} (best : G.Walk base base) (hpos : 0 < best.length)
    (hattained : walkWeight weight best = best.length * lam) :
    ∃ vertex : V, ∀ count : ℕ,
      ((Fintype.card V : 𝕜) - count) * lam
        ≤ stepValue G weight (Fintype.card V) vertex - stepValue G weight count vertex := by
  set shifted : E → 𝕜 := fun e => weight e - lam with hshifted
  have hnonpos : ∀ (v : V) (cycle : G.Walk v v), walkWeight shifted cycle ≤ 0 := by
    intro v cycle
    rw [hshifted, walkWeight_sub_const]
    linarith [hcyc v cycle]
  have hbestZero : walkWeight shifted best = 0 := by
    rw [hshifted, walkWeight_sub_const, hattained]
    ring
  -- the greatest weight of a walk arriving at the base of the attaining cycle
  have hgreatest := isGreatest_incomingWeights (G := G) (weight := shifted) hnonpos base
  obtain ⟨prefixStart, prefixWalk, -, hprefixWt⟩ :=
    maxIncomingWeight_mem (G := G) shifted base
  obtain ⟨iterated, hiterLen, hiterWt⟩ :=
    exists_closedWalk_length_mul (G := G) shifted best (Fintype.card V)
  set long := prefixWalk.append iterated with hlong
  have hlongLen : Fintype.card V ≤ long.length := by
    have : Fintype.card V * 1 ≤ Fintype.card V * best.length := by
      exact Nat.mul_le_mul_left _ hpos
    simp only [hlong, EdgeGraph.Walk.length_append, hiterLen]
    omega
  obtain ⟨vertex, front, back, hfrontLen, hedges⟩ :=
    long.exists_split_of_length_le hlongLen
  refine ⟨vertex, fun count => ?_⟩
  have hfrontBack : walkWeight shifted front + walkWeight shifted back
      = maxIncomingWeight G shifted base := by
    have hlongWt : walkWeight shifted long = maxIncomingWeight G shifted base := by
      rw [hlong, walkWeight_append, hprefixWt, hiterWt, hbestZero]
      ring
    rw [← hlongWt]
    simp only [walkWeight, hedges, List.map_append, List.sum_append]
  have hfrontLe : walkWeight shifted front
      ≤ stepValue G shifted (Fintype.card V) vertex :=
    le_stepValue ⟨prefixStart, front, hfrontLen, rfl⟩
  have hcountLe : stepValue G shifted count vertex ≤ walkWeight shifted front := by
    obtain ⟨tailStart, tailWalk, -, htailWt⟩ :=
      exists_walk_walkWeight_eq_stepValue hin shifted count vertex
    have hmem : walkWeight shifted (tailWalk.append back)
        ∈ incomingWeights G shifted base := ⟨tailStart, _, rfl⟩
    have hbound := hgreatest.2 hmem
    rw [walkWeight_append, htailWt] at hbound
    linarith
  have hshiftN : stepValue G shifted (Fintype.card V) vertex
      = stepValue G weight (Fintype.card V) vertex - (Fintype.card V : 𝕜) * lam :=
    stepValue_sub_const hin weight lam (Fintype.card V) vertex
  have hshiftK : stepValue G shifted count vertex
      = stepValue G weight count vertex - (count : 𝕜) * lam :=
    stepValue_sub_const hin weight lam count vertex
  have hexpand : ((Fintype.card V : 𝕜) - count) * lam
      = (Fintype.card V : 𝕜) * lam - (count : 𝕜) * lam := by ring
  linarith [hfrontLe, hcountLe, hshiftN, hshiftK, hexpand]

/-! ### Karp's formula -/

/-- **Karp's minimum (here maximum) mean cycle formula.**  Let every vertex of a finite
weighted digraph have an incoming edge, and let `best` be a nonempty closed walk of maximum
mean weight.  Then that maximum cycle mean is
`max_v min_{0 ≤ k < n} (D n v - D k v) / (n - k)`, where `n` is the number of vertices and
`D` is the step-value table `DirectedTransport.MaxPlusPotential.stepValue`. -/
theorem sup'_inf'_stepValue_div [Fintype V] [Nonempty V] [Finite E]
    (hin : ∀ vertex : V, ∃ e : E, G.target e = vertex) (weight : E → 𝕜)
    {base : V} (best : G.Walk base base) (hpos : 0 < best.length)
    (hbest : ∀ (vertex : V) (cycle : G.Walk vertex vertex),
      walkWeight weight cycle
        ≤ cycle.length * (walkWeight weight best / best.length)) :
    (Finset.univ : Finset V).sup' Finset.univ_nonempty (fun vertex =>
        (Finset.range (Fintype.card V)).inf'
          (Finset.nonempty_range_iff.mpr Fintype.card_ne_zero)
          (fun count => (stepValue G weight (Fintype.card V) vertex
              - stepValue G weight count vertex) / ((Fintype.card V : 𝕜) - count)))
      = walkWeight weight best / best.length := by
  set lam := walkWeight weight best / best.length with hlam
  have hlenPos : (0 : 𝕜) < best.length := by exact_mod_cast hpos
  have hattained : walkWeight weight best = best.length * lam := by
    rw [hlam]
    field_simp
  have hgap : ∀ count ∈ Finset.range (Fintype.card V),
      (0 : 𝕜) < (Fintype.card V : 𝕜) - count := by
    intro count hcount
    have : (count : 𝕜) < (Fintype.card V : 𝕜) :=
      Nat.cast_lt.mpr (Finset.mem_range.mp hcount)
    linarith
  refine le_antisymm (Finset.sup'_le _ _ fun vertex _ => ?_) ?_
  · obtain ⟨count, hcount, hle⟩ := exists_stepValue_sub_le hin weight lam hbest vertex
    have hmem : count ∈ Finset.range (Fintype.card V) := Finset.mem_range.mpr hcount
    refine (Finset.inf'_le _ hmem).trans ?_
    exact (div_le_iff₀ (hgap count hmem)).mpr (by linarith [hle])
  · obtain ⟨vertex, hvertex⟩ :=
      exists_le_stepValue_sub hin weight lam hbest best hpos hattained
    refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ vertex))
    refine Finset.le_inf' _ _ fun count hcount => ?_
    exact (le_div_iff₀ (hgap count hcount)).mpr (by linarith [hvertex count])

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- With every vertex carrying an incoming edge, a finite nonempty graph has a nonempty
closed walk. -/
theorem exists_closedWalk_length_pos [Fintype V] [Nonempty V]
    (hin : ∀ vertex : V, ∃ e : E, G.target e = vertex) :
    ∃ (base : V) (cycle : G.Walk base base), 0 < cycle.length := by
  obtain ⟨target⟩ := (inferInstance : Nonempty V)
  obtain ⟨start, walk, hlen⟩ :=
    exists_walk_length_eq (G := G) hin (Fintype.card V) target
  have hdup : ¬ walk.visited.Nodup := by
    intro hnodup
    have hcard := hnodup.length_le_card
    rw [EdgeGraph.Walk.length_visited, hlen] at hcard
    omega
  obtain ⟨vertex, -, cycle, -, hcycle, -⟩ := walk.exists_closedSubwalk_of_not_nodup hdup
  exact ⟨vertex, cycle, hcycle⟩

/-! ### Over the reals: the attained maximum -/

/-- **Karp's formula against the attained maximum cycle mean.**  Over the reals the
maximizing cycle of `DirectedTransport.AdditiveTransport.exists_short_closedWalk_maximizing_mean`
supplies the right-hand side, so Karp's expression computes the max cycle mean itself. -/
theorem exists_short_closedWalk_sup'_inf'_stepValue_div
    [Fintype V] [Nonempty V] [Finite E] (G : EdgeGraph V E) (weight : E → ℝ)
    (hin : ∀ vertex : V, ∃ e : E, G.target e = vertex) :
    ∃ (base : V) (best : G.Walk base base),
      0 < best.length ∧ best.length ≤ Fintype.card V ∧
        (∀ (vertex : V) (cycle : G.Walk vertex vertex), 0 < cycle.length →
          walkWeight weight cycle / cycle.length
            ≤ walkWeight weight best / best.length) ∧
        (Finset.univ : Finset V).sup' Finset.univ_nonempty (fun vertex =>
            (Finset.range (Fintype.card V)).inf'
              (Finset.nonempty_range_iff.mpr Fintype.card_ne_zero)
              (fun count => (stepValue G weight (Fintype.card V) vertex
                  - stepValue G weight count vertex) / ((Fintype.card V : ℝ) - count)))
          = walkWeight weight best / best.length := by
  obtain ⟨vertex, best, hpos, hcard, hmax⟩ :=
    AdditiveTransport.exists_short_closedWalk_maximizing_mean G weight
      (exists_closedWalk_length_pos hin)
  refine ⟨vertex, best, hpos, hcard, hmax, sup'_inf'_stepValue_div hin weight best hpos ?_⟩
  intro other cycle
  rcases Nat.eq_zero_or_pos cycle.length with hzero | hcyclePos
  · have hedges : cycle.edges = [] :=
      List.length_eq_zero_iff.mp (by rw [EdgeGraph.Walk.edges_length, hzero])
    simp [walkWeight, hedges, hzero]
  · have hlenPos : (0 : ℝ) < cycle.length := by exact_mod_cast hcyclePos
    have hmean := hmax other cycle hcyclePos
    have := (div_le_iff₀ hlenPos).mp hmean
    linarith

/-! ### The attained max-plus spectral threshold -/

/-- **Max-plus Perron root, assembled.**  For a real matrix over a nonempty finite index
type, some cycle of the matrix graph of length at most `Fintype.card ι` is an exact
threshold: a subeigenvector for `lam` exists precisely when that cycle's mean weight is at
most `lam`. -/
theorem exists_critical_cycle_subeigenvector_iff
    {ι : Type*} [Fintype ι] [Nonempty ι] (A : ι → ι → ℝ) :
    ∃ (i : ι) (best : (matrixGraph ι).Walk i i),
      0 < best.length ∧ best.length ≤ Fintype.card ι ∧
        ∀ lam : ℝ,
          ((∃ v : ι → ℝ, IsSubeigenvector A lam v) ↔
            walkWeight (matrixWeight A) best ≤ best.length * lam) := by
  classical
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have hexists : ∃ (vertex : ι) (cycle : (matrixGraph ι).Walk vertex vertex),
      0 < cycle.length := by
    refine ⟨i, ((EdgeGraph.Walk.nil : (matrixGraph ι).Walk i i).concat (i, i)
      (matrixGraph_source _)).castFinish (matrixGraph_target _), ?_⟩
    rw [EdgeGraph.Walk.length_castFinish, EdgeGraph.Walk.length_concat]
    exact Nat.succ_pos _
  obtain ⟨vertex, best, hpos, hcard, hmax⟩ :=
    AdditiveTransport.exists_short_closedWalk_maximizing_mean
      (matrixGraph ι) (matrixWeight A) hexists
  have hbestLenPos : (0 : ℝ) < best.length := by exact_mod_cast hpos
  refine ⟨vertex, best, hpos, hcard, fun lam => ?_⟩
  constructor
  · intro hv
    exact (exists_subeigenvector_iff_forall_closedWalk_le A lam).mp hv vertex best
  · intro hbest
    refine (exists_subeigenvector_iff_forall_closedWalk_le A lam).mpr ?_
    intro j cycle
    rcases Nat.eq_zero_or_pos cycle.length with hzero | hposCycle
    · have hedges : cycle.edges = [] :=
        List.length_eq_zero_iff.mp (by rw [EdgeGraph.Walk.edges_length, hzero])
      simp [walkWeight, hedges, hzero]
    · have hlenPos : (0 : ℝ) < cycle.length := by exact_mod_cast hposCycle
      have hmean := hmax j cycle hposCycle
      have hbestMean : walkWeight (matrixWeight A) best / best.length ≤ lam := by
        rw [div_le_iff₀ hbestLenPos]
        linarith [hbest]
      have hcycleMean := hmean.trans hbestMean
      rw [div_le_iff₀ hlenPos] at hcycleMean
      linarith [hcycleMean]

end MaxPlusPotential

end

end DirectedTransport
