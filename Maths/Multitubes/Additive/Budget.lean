/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Additive.Potentials
public import Mathlib.Basic.ENNReal.Real

import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Walk budgets are exactly bounded potentials

Let `weight` be real edge data on an arbitrary directed multigraph.  The **budget** is the
supremum of the weights of all finite walks.  A potential in the sense of
`Maths.MaxPlusPotential.IsPotential` rises by at least the weight across every edge; it is
*bounded* when its range is bounded above and below, and its **oscillation** is
`sSup (range φ) - sInf (range φ)`.

The main theorem is a duality with no hypothesis on the vertex or edge type: a bounded potential
exists exactly when the walk weights are bounded above, and then the budget is the least
oscillation of a bounded potential.  The least value is attained by the supremum of the weights
of the walks arriving at each vertex, which is also the least nonnegative potential.

`Maths.MaxPlusPotential.exists_isPotential_iff_forall_closedWalk_nonpos` characterizes the
existence of a possibly unbounded potential by the absence of a positive closed walk, and needs
finitely many edges; boundedness of the potential is what replaces that finiteness here.  The
two criteria differ: a bounded potential forbids every positive closed walk, but it also
forbids arbitrarily heavy open walks.

## Main definitions

* `Maths.MaxPlusPotential.oscillation`: the spread of the range of a real function.
* `Maths.MaxPlusPotential.walkWeights`: the weights of all finite walks.
* `Maths.MaxPlusPotential.HasFiniteBudget` and `Maths.MaxPlusPotential.budget`: the walk
  weights are bounded above, and their supremum.
* `Maths.MaxPlusPotential.budgetEN`: the same budget as a totally defined `ℝ≥0∞`.
* `Maths.MaxPlusPotential.supIncomingWeight`: the supremum of the weights of the walks
  arriving at a vertex.
* `Maths.MaxPlusPotential.IsBoundedPotential`: a potential with bounded range.

## Main results

* `Maths.MaxPlusPotential.hasFiniteBudget_iff_exists_boundedPotential`: the budget is finite
  exactly when a bounded potential exists.
* `Maths.MaxPlusPotential.budget_eq_oscillation_supIncomingWeight` and
  `Maths.MaxPlusPotential.isLeast_oscillation`: strong duality, the budget is the minimum
  oscillation of a bounded potential, attained by `supIncomingWeight`.  The two inequalities
  `Maths.MaxPlusPotential.budget_le_oscillation` and
  `Maths.MaxPlusPotential.oscillation_supIncomingWeight_le_budget` hold separately.
* `Maths.MaxPlusPotential.budgetEN_eq_iInf_oscillation`: the same duality with no finiteness
  hypothesis, in `ℝ≥0∞`, both sides being `⊤` in the unbounded case.
* `Maths.MaxPlusPotential.isLeast_supIncomingWeight` and
  `Maths.MaxPlusPotential.supIncomingWeight_le_iff`: Bellman characterisation,
  `supIncomingWeight` is the least nonnegative potential.
* `Maths.MaxPlusPotential.not_hasFiniteBudget_of_positive_cycle` and
  `Maths.MaxPlusPotential.not_exists_boundedPotential_of_positive_cycle`: a closed walk of
  positive weight forces an infinite budget, hence excludes bounded potentials.

## Implementation notes

No sign condition on the weights is needed.  The empty walk makes `0` a walk weight, so the
budget and `supIncomingWeight` are nonnegative whenever they are finite.

The oscillation is taken over *all* vertices, not only over those touched by an edge, and the
duality is nevertheless exact: `supIncomingWeight` is globally nonnegative and globally bounded
by the budget, so its oscillation over all vertices is already at most the budget.

No maximising walk is assumed to exist: `supIncomingWeight` is a supremum, and its edge
inequality is obtained by extending an arbitrary walk by one edge.

## Tags

potential, budget, oscillation, duality, max-plus, Bellman equation
-/

@[expose] public section

namespace Maths

namespace MaxPlusPotential

open scoped ENNReal

universe uV uE

variable {V : Type uV} {E : Type uE}

/-- Oscillation of a real-valued function: the spread of its range.  For an unbounded function
the value is junk, and every statement about it carries an explicit boundedness hypothesis. -/
noncomputable def oscillation (f : V → ℝ) : ℝ :=
  sSup (Set.range f) - sInf (Set.range f)

/-- The oscillation of a function with bounded range is nonnegative. -/
theorem oscillation_nonneg {f : V → ℝ}
    (hA : BddAbove (Set.range f)) (hB : BddBelow (Set.range f)) : 0 ≤ oscillation f := by
  rcases isEmpty_or_nonempty V with hV | hV
  · simp [oscillation, Set.range_eq_empty f, Real.sSup_empty, Real.sInf_empty]
  · have := csInf_le_csSup (Set.range_nonempty f) hB hA
    simpa [oscillation, sub_nonneg] using this

variable (G : EdgeGraph V E) (weight : E → ℝ)

/-- The weights of the finite walks of a weighted directed multigraph. -/
def walkWeights : Set ℝ :=
  {value | ∃ (start finish : V) (walk : G.Walk start finish), walkSum weight walk = value}

/-- The walk weights are bounded above. -/
def HasFiniteBudget : Prop := BddAbove (walkWeights G weight)

/-- The budget: the supremum of the walk weights.  When the walk weights are unbounded this is
junk; every statement about it carries a `HasFiniteBudget` hypothesis, or is stated for
`budgetEN`. -/
noncomputable def budget : ℝ := sSup (walkWeights G weight)

/-- The supremum of the weights of the finite walks arriving at a vertex. -/
noncomputable def supIncomingWeight (vertex : V) : ℝ := sSup (incomingWeights G weight vertex)

/-- A potential whose range is bounded above and below. -/
structure IsBoundedPotential (φ : V → ℝ) : Prop where
  /-- The range of the potential is bounded above. -/
  bddAbove : BddAbove (Set.range φ)
  /-- The range of the potential is bounded below. -/
  bddBelow : BddBelow (Set.range φ)
  /-- The edge increment inequality. -/
  isPotential : IsPotential G weight φ

variable {G weight}

theorem mem_walkWeights {start finish : V} (walk : G.Walk start finish) :
    walkSum weight walk ∈ walkWeights G weight :=
  ⟨start, finish, walk, rfl⟩

theorem incomingWeights_subset_walkWeights (vertex : V) :
    incomingWeights G weight vertex ⊆ walkWeights G weight := by
  rintro value ⟨start, walk, rfl⟩
  exact mem_walkWeights walk

theorem walkSum_mem_incomingWeights {start finish : V} (walk : G.Walk start finish) :
    walkSum weight walk ∈ incomingWeights G weight finish :=
  ⟨start, walk, rfl⟩

/-- The budget is nonnegative: when it is finite the empty walk is among the walk weights, and
otherwise it is the junk value `0`. -/
theorem budget_nonneg : 0 ≤ budget G weight := by
  by_cases h : HasFiniteBudget G weight
  · rcases isEmpty_or_nonempty V with hV | hV
    · simp [budget, walkWeights, Real.sSup_empty]
    · obtain ⟨vertex⟩ := hV
      exact le_csSup h (incomingWeights_subset_walkWeights vertex
        (zero_mem_incomingWeights (G := G) weight vertex))
  · simp [budget, Real.sSup_of_not_bddAbove h]

/-- Under a finite budget, every walk weight is at most the budget. -/
theorem walkSum_le_budget (h : HasFiniteBudget G weight) {start finish : V}
    (walk : G.Walk start finish) : walkSum weight walk ≤ budget G weight :=
  le_csSup h (mem_walkWeights walk)

/-- A nonnegative bound on every walk weight bounds the budget. -/
theorem budget_le {c : ℝ} (hc : 0 ≤ c)
    (hwalk : ∀ {start finish : V} (walk : G.Walk start finish), walkSum weight walk ≤ c) :
    budget G weight ≤ c :=
  Real.sSup_le (by rintro x ⟨start, finish, walk, rfl⟩; exact hwalk walk) hc

theorem bddAbove_incomingWeights_of_hasFiniteBudget (h : HasFiniteBudget G weight)
    (vertex : V) : BddAbove (incomingWeights G weight vertex) :=
  h.mono (incomingWeights_subset_walkWeights vertex)

/-- Under a finite budget, `supIncomingWeight` is nonnegative. -/
theorem supIncomingWeight_nonneg (h : HasFiniteBudget G weight) (vertex : V) :
    0 ≤ supIncomingWeight G weight vertex :=
  le_csSup (bddAbove_incomingWeights_of_hasFiniteBudget h vertex)
    (zero_mem_incomingWeights weight vertex)

/-- Under a finite budget, a walk arriving at a vertex weighs at most `supIncomingWeight`
there. -/
theorem walkSum_le_supIncomingWeight (h : HasFiniteBudget G weight) {start finish : V}
    (walk : G.Walk start finish) : walkSum weight walk ≤ supIncomingWeight G weight finish :=
  le_csSup (bddAbove_incomingWeights_of_hasFiniteBudget h finish)
    (walkSum_mem_incomingWeights walk)

/-- A nonnegative bound on every walk arriving at a vertex bounds `supIncomingWeight` there. -/
theorem supIncomingWeight_le {c : ℝ} {finish : V} (hc : 0 ≤ c)
    (hwalk : ∀ {start : V} (walk : G.Walk start finish), walkSum weight walk ≤ c) :
    supIncomingWeight G weight finish ≤ c :=
  Real.sSup_le (by rintro x ⟨start, walk, rfl⟩; exact hwalk walk) hc

/-- Under a finite budget, `supIncomingWeight` never exceeds the budget. -/
theorem supIncomingWeight_le_budget (h : HasFiniteBudget G weight) (vertex : V) :
    supIncomingWeight G weight vertex ≤ budget G weight :=
  supIncomingWeight_le budget_nonneg fun walk => walkSum_le_budget h walk

/-! ### Bounded potentials -/

/-- Every walk weight is bounded by the oscillation of a bounded potential. -/
theorem IsBoundedPotential.walkSum_le_oscillation {φ : V → ℝ}
    (hφ : IsBoundedPotential G weight φ) {start finish : V} (walk : G.Walk start finish) :
    walkSum weight walk ≤ oscillation φ := by
  have h1 : φ finish ≤ sSup (Set.range φ) := le_csSup hφ.bddAbove ⟨finish, rfl⟩
  have h2 : sInf (Set.range φ) ≤ φ start := csInf_le hφ.bddBelow ⟨start, rfl⟩
  have h3 := hφ.isPotential.walkSum_add_le walk
  simp only [oscillation]
  linarith

/-- A bounded potential bounds the walk weights. -/
theorem IsBoundedPotential.hasFiniteBudget {φ : V → ℝ}
    (hφ : IsBoundedPotential G weight φ) : HasFiniteBudget G weight :=
  ⟨oscillation φ, by
    rintro x ⟨start, finish, walk, rfl⟩
    exact hφ.walkSum_le_oscillation walk⟩

/-- Weak duality: the budget is at most the oscillation of any bounded potential. -/
theorem budget_le_oscillation {φ : V → ℝ} (hφ : IsBoundedPotential G weight φ) :
    budget G weight ≤ oscillation φ :=
  budget_le (oscillation_nonneg hφ.bddAbove hφ.bddBelow) fun walk =>
    hφ.walkSum_le_oscillation walk

/-! ### The supremum of arriving weights is an optimal potential -/

/-- Under a finite budget, `supIncomingWeight` obeys the edge increment inequality.  No
maximising walk is assumed: an arbitrary walk arriving at the source is extended by the
edge. -/
theorem isPotential_supIncomingWeight (h : HasFiniteBudget G weight) :
    IsPotential G weight (supIncomingWeight G weight) := by
  intro edge
  have hedge : weight edge ≤ supIncomingWeight G weight (G.target edge) := by
    simpa using walkSum_le_supIncomingWeight h (EdgeGraph.Walk.singleton (G := G) edge)
  have key : supIncomingWeight G weight (G.source edge) ≤
      supIncomingWeight G weight (G.target edge) - weight edge := by
    refine supIncomingWeight_le (by linarith) fun walk => ?_
    have := walkSum_le_supIncomingWeight h (walk.concat edge rfl)
    rw [walkSum_concat] at this
    linarith
  linarith

/-- Under a finite budget, `supIncomingWeight` is a bounded potential. -/
theorem isBoundedPotential_supIncomingWeight (h : HasFiniteBudget G weight) :
    IsBoundedPotential G weight (supIncomingWeight G weight) where
  bddAbove := ⟨budget G weight, by
    rintro x ⟨vertex, rfl⟩
    exact supIncomingWeight_le_budget h vertex⟩
  bddBelow := ⟨0, by
    rintro x ⟨vertex, rfl⟩
    exact supIncomingWeight_nonneg h vertex⟩
  isPotential := isPotential_supIncomingWeight h

theorem sSup_range_supIncomingWeight_le_budget (h : HasFiniteBudget G weight) :
    sSup (Set.range (supIncomingWeight G weight)) ≤ budget G weight :=
  Real.sSup_le (by
    rintro x ⟨vertex, rfl⟩
    exact supIncomingWeight_le_budget h vertex) budget_nonneg

theorem sInf_range_supIncomingWeight_nonneg (h : HasFiniteBudget G weight) :
    0 ≤ sInf (Set.range (supIncomingWeight G weight)) :=
  Real.le_sInf (by
    rintro x ⟨vertex, rfl⟩
    exact supIncomingWeight_nonneg h vertex) le_rfl

/-- The oscillation of `supIncomingWeight` is at most the budget. -/
theorem oscillation_supIncomingWeight_le_budget (h : HasFiniteBudget G weight) :
    oscillation (supIncomingWeight G weight) ≤ budget G weight := by
  have hA := sSup_range_supIncomingWeight_le_budget h
  have hB := sInf_range_supIncomingWeight_nonneg h
  simp only [oscillation]
  linarith

/-- **Budget theorem.**  The walk weights are bounded above exactly when a bounded potential
exists.  The forward witness is `supIncomingWeight`. -/
theorem hasFiniteBudget_iff_exists_boundedPotential :
    HasFiniteBudget G weight ↔ ∃ φ : V → ℝ, IsBoundedPotential G weight φ :=
  ⟨fun h => ⟨_, isBoundedPotential_supIncomingWeight h⟩, fun ⟨_, hφ⟩ => hφ.hasFiniteBudget⟩

/-- **Strong duality.**  The budget equals the oscillation of `supIncomingWeight`. -/
theorem budget_eq_oscillation_supIncomingWeight (h : HasFiniteBudget G weight) :
    budget G weight = oscillation (supIncomingWeight G weight) :=
  le_antisymm (budget_le_oscillation (isBoundedPotential_supIncomingWeight h))
    (oscillation_supIncomingWeight_le_budget h)

/-- **Strong duality, packaged.**  The budget is the least oscillation of a bounded potential,
and the least value is attained. -/
theorem isLeast_oscillation (h : HasFiniteBudget G weight) :
    IsLeast {c : ℝ | ∃ φ : V → ℝ, IsBoundedPotential G weight φ ∧ oscillation φ = c}
      (budget G weight) :=
  ⟨⟨_, isBoundedPotential_supIncomingWeight h,
      (budget_eq_oscillation_supIncomingWeight h).symm⟩,
    by rintro c ⟨φ, hφ, rfl⟩; exact budget_le_oscillation hφ⟩

/-- `supIncomingWeight` attains the budget as its supremum. -/
theorem sSup_range_supIncomingWeight (h : HasFiniteBudget G weight) :
    sSup (Set.range (supIncomingWeight G weight)) = budget G weight := by
  have hA := sSup_range_supIncomingWeight_le_budget h
  have hB := sInf_range_supIncomingWeight_nonneg h
  have hosc := budget_eq_oscillation_supIncomingWeight h
  simp only [oscillation] at hosc
  linarith

/-- `supIncomingWeight` has infimum zero. -/
theorem sInf_range_supIncomingWeight (h : HasFiniteBudget G weight) :
    sInf (Set.range (supIncomingWeight G weight)) = 0 := by
  have hA := sSup_range_supIncomingWeight_le_budget h
  have hB := sInf_range_supIncomingWeight_nonneg h
  have hosc := budget_eq_oscillation_supIncomingWeight h
  simp only [oscillation] at hosc
  linarith

/-! ### Bellman characterisation -/

/-- Every nonnegative potential dominates `supIncomingWeight`.  No finiteness hypothesis is
needed: the potential itself bounds the weights of the walks arriving at each vertex. -/
theorem supIncomingWeight_le_of_isPotential {φ : V → ℝ} (hnonneg : 0 ≤ φ)
    (hφ : IsPotential G weight φ) (vertex : V) : supIncomingWeight G weight vertex ≤ φ vertex :=
  supIncomingWeight_le (hnonneg vertex) fun {start} walk => by
    have := hφ.walkSum_add_le walk
    have : (0 : ℝ) ≤ φ start := hnonneg start
    linarith

/-- **Bellman characterisation.**  Under a finite budget, `supIncomingWeight` is the least
nonnegative potential, in the pointwise order. -/
theorem isLeast_supIncomingWeight (h : HasFiniteBudget G weight) :
    IsLeast {φ : V → ℝ | 0 ≤ φ ∧ IsPotential G weight φ} (supIncomingWeight G weight) :=
  ⟨⟨supIncomingWeight_nonneg h, isPotential_supIncomingWeight h⟩,
    fun _ hφ vertex => supIncomingWeight_le_of_isPotential hφ.1 hφ.2 vertex⟩

/-- The local Bellman equation, in elimination form: `supIncomingWeight` at a vertex is the
least number that is nonnegative and dominates `supIncomingWeight (source e) + weight e` for
every edge `e` entering the vertex. -/
theorem supIncomingWeight_le_iff (h : HasFiniteBudget G weight) (vertex : V) (c : ℝ) :
    supIncomingWeight G weight vertex ≤ c ↔
      0 ≤ c ∧ ∀ edge : E, G.target edge = vertex →
        supIncomingWeight G weight (G.source edge) + weight edge ≤ c := by
  constructor
  · intro hle
    refine ⟨(supIncomingWeight_nonneg h vertex).trans hle, ?_⟩
    rintro edge rfl
    exact (isPotential_supIncomingWeight h edge).trans hle
  · rintro ⟨hc, hedge⟩
    refine supIncomingWeight_le hc fun walk => ?_
    revert hedge
    cases walk with
    | nil => intro _; simpa using hc
    | concat walk edge legal =>
        intro hedge
        subst legal
        have h1 := hedge edge rfl
        have h2 := walkSum_le_supIncomingWeight h walk
        rw [walkSum_concat]
        linarith

/-! ### Positive closed walks destroy every bounded potential -/

/-- A closed walk of positive weight forces an infinite budget. -/
theorem not_hasFiniteBudget_of_positive_cycle {base : V} (cycle : G.Walk base base)
    (hcycle : 0 < walkSum weight cycle) : ¬ HasFiniteBudget G weight := by
  intro h
  obtain ⟨n, hn⟩ := exists_nat_gt (budget G weight / walkSum weight cycle)
  have hle : (n : ℝ) * walkSum weight cycle ≤ budget G weight := by
    simpa using walkSum_le_budget h (cycle.iterate n)
  rw [div_lt_iff₀ hcycle] at hn
  linarith

/-- A closed walk of positive weight excludes bounded potentials. -/
theorem not_exists_boundedPotential_of_positive_cycle {base : V} (cycle : G.Walk base base)
    (hcycle : 0 < walkSum weight cycle) : ¬ ∃ φ : V → ℝ, IsBoundedPotential G weight φ :=
  fun ⟨_, hφ⟩ => not_hasFiniteBudget_of_positive_cycle cycle hcycle hφ.hasFiniteBudget

/-! ### The budget as an extended nonnegative real -/

variable (G weight) in
/-- The budget as an extended nonnegative real.  This is totally defined and equals `⊤`
exactly when the walk weights are unbounded. -/
noncomputable def budgetEN : ℝ≥0∞ :=
  ⨆ (start : V) (finish : V) (walk : G.Walk start finish), ENNReal.ofReal (walkSum weight walk)

theorem ofReal_walkSum_le_budgetEN {start finish : V} (walk : G.Walk start finish) :
    ENNReal.ofReal (walkSum weight walk) ≤ budgetEN G weight :=
  le_iSup_of_le start (le_iSup_of_le finish
    (le_iSup (fun other : G.Walk start finish => ENNReal.ofReal (walkSum weight other)) walk))

/-- The extended budget is finite exactly when the walk weights are bounded above. -/
theorem budgetEN_lt_top_iff : budgetEN G weight < ⊤ ↔ HasFiniteBudget G weight := by
  constructor
  · intro h
    refine ⟨(budgetEN G weight).toReal, ?_⟩
    rintro x ⟨start, finish, walk, rfl⟩
    exact (ENNReal.ofReal_le_iff_le_toReal h.ne).1 (ofReal_walkSum_le_budgetEN walk)
  · rintro ⟨M, hM⟩
    refine lt_of_le_of_lt (iSup_le fun start => iSup_le fun finish => iSup_le fun walk => ?_)
      (ENNReal.ofReal_lt_top (r := M))
    exact ENNReal.ofReal_le_ofReal (hM (mem_walkWeights walk))

/-- The extended budget is `⊤` exactly when the walk weights are unbounded. -/
theorem budgetEN_eq_top_iff : budgetEN G weight = ⊤ ↔ ¬ HasFiniteBudget G weight := by
  rw [← budgetEN_lt_top_iff, not_lt_top_iff]

/-- Under a finite budget, the extended budget is the coercion of the budget. -/
theorem budgetEN_eq_ofReal_budget (h : HasFiniteBudget G weight) :
    budgetEN G weight = ENNReal.ofReal (budget G weight) := by
  have hne : budgetEN G weight ≠ ⊤ := (budgetEN_lt_top_iff.2 h).ne
  refine le_antisymm ?_ ?_
  · exact iSup_le fun start => iSup_le fun finish => iSup_le fun walk =>
      ENNReal.ofReal_le_ofReal (walkSum_le_budget h walk)
  · have hbudget : budget G weight ≤ (budgetEN G weight).toReal :=
      budget_le ENNReal.toReal_nonneg fun walk =>
        (ENNReal.ofReal_le_iff_le_toReal hne).1 (ofReal_walkSum_le_budgetEN walk)
    calc ENNReal.ofReal (budget G weight) ≤ ENNReal.ofReal (budgetEN G weight).toReal :=
          ENNReal.ofReal_le_ofReal hbudget
      _ = budgetEN G weight := ENNReal.ofReal_toReal hne

/-- **Strong duality without a finiteness hypothesis.**  In `ℝ≥0∞` the budget is always the
infimum of the oscillations of bounded potentials.  When no bounded potential exists the index
type is empty and both sides are `⊤`. -/
theorem budgetEN_eq_iInf_oscillation :
    budgetEN G weight =
      ⨅ φ : {φ : V → ℝ // IsBoundedPotential G weight φ}, ENNReal.ofReal (oscillation φ.1) := by
  by_cases h : HasFiniteBudget G weight
  · refine le_antisymm (le_iInf fun φ => ?_) ?_
    · rw [budgetEN_eq_ofReal_budget h]
      exact ENNReal.ofReal_le_ofReal (budget_le_oscillation φ.2)
    · refine le_trans (iInf_le _ ⟨_, isBoundedPotential_supIncomingWeight h⟩) ?_
      rw [budgetEN_eq_ofReal_budget h, ← budget_eq_oscillation_supIncomingWeight h]
  · have hempty : IsEmpty {φ : V → ℝ // IsBoundedPotential G weight φ} :=
      ⟨fun φ => h φ.2.hasFiniteBudget⟩
    rw [budgetEN_eq_top_iff.2 h, iInf_of_isEmpty, sInf_empty]

end MaxPlusPotential

end Maths
