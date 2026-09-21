/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Relational
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Basic.Rel
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# Transaction paths and solvency increments

A deterministic market edge carries the set of feasible net portfolio changes. Edge relations
compose existentially along typed walks, and the attainable increment set of a serial path is the
Minkowski sum of its edge sets. Existential image realizes the same relation as ordinary transport
on powersets.

This formulation uses only an additive group for path accounting. A solvency cone induces a
preorder without requiring joins or meets, while convexity is an independent property preserved
by serial Minkowski addition. A pair of parallel transactions shows that union over alternative
paths may leave the convex sets even when every individual transaction set is convex.

## Main definitions

* `ConicFinance.SolvencyLE` - comparison induced by an additive solvency cone.
* `ConicFinance.IsPointed` - the condition making the cone comparison antisymmetric.
* `ConicFinance.TransactionMarket` - feasible net increments attached to graph edges.
* `ConicFinance.TransactionMarket.edgeRelation` - one-edge portfolio feasibility.
* `ConicFinance.TransactionMarket.walkIncrement` - pathwise Minkowski sum.
* `ConicFinance.TransactionMarket.relationTransport` - the relation-labelled market graph.
* `ConicFinance.alternativeReachable` - one-step reachability through two parallel transactions.

## Main results

* `ConicFinance.solvencyLE_refl`, `ConicFinance.solvencyLE_trans`, and
  `ConicFinance.solvencyLE_antisymm` - the precise cone laws behind the induced order.
* `ConicFinance.TransactionMarket.walkRelation_iff_sub_mem_walkIncrement` - native path
  feasibility is net-change membership in the pathwise Minkowski sum.
* `ConicFinance.TransactionMarket.walkIncrement_append` - serial composition is Minkowski
  addition.
* `Maths.RelationTransport.walkMap_eq_image_walkRelation` - powerset walk transport is exactly
  native path feasibility.
* `ConicFinance.TransactionMarket.convex_walkIncrement` - serial paths preserve convexity.
* `ConicFinance.alternativeReachable_eq` and
  `ConicFinance.not_convex_alternativeReachable` - alternative paths aggregate by a nonconvex
  union.
* `ConicFinance.zero_mem_convexHull_alternativeReachable` - convexification adds a portfolio
  that no transaction path reaches.

## Tags

transaction costs, solvency cone, Minkowski sum, relation, convexity, powerset
-/

@[expose] public section

noncomputable section

open scoped Pointwise

namespace ConicFinance

open Maths
open scoped SetRel

universe uV uE uP uR

variable {Portfolio : Type uP}

/-! ## Cone-induced comparison -/

/-- The comparison induced by an additive solvency cone: `x` can be improved to `y` when the
increment `y - x` belongs to the cone. -/
def SolvencyLE [AddCommGroup Portfolio] (cone : AddSubmonoid Portfolio)
    (x y : Portfolio) : Prop :=
  y - x ∈ cone

/-- Every portfolio is comparable to itself under a cone-induced comparison. -/
theorem solvencyLE_refl [AddCommGroup Portfolio] (cone : AddSubmonoid Portfolio)
    (x : Portfolio) : SolvencyLE cone x x := by
  simp [SolvencyLE]

/-- Additive closure of the cone gives transitivity of its induced comparison. -/
theorem solvencyLE_trans [AddCommGroup Portfolio] (cone : AddSubmonoid Portfolio)
    {x y z : Portfolio} (hxy : SolvencyLE cone x y) (hyz : SolvencyLE cone y z) :
    SolvencyLE cone x z := by
  have hsum := cone.add_mem hxy hyz
  simpa only [SolvencyLE, show y - x + (z - y) = z - x by abel] using hsum

/-- A cone is pointed when it contains no nonzero element together with its negative. -/
def IsPointed [AddCommGroup Portfolio] (cone : AddSubmonoid Portfolio) : Prop :=
  ∀ x : Portfolio, x ∈ cone → -x ∈ cone → x = 0

/-- Pointedness gives antisymmetry of the cone-induced comparison. -/
theorem solvencyLE_antisymm [AddCommGroup Portfolio] (cone : AddSubmonoid Portfolio)
    (hpointed : IsPointed cone) {x y : Portfolio}
    (hxy : SolvencyLE cone x y) (hyx : SolvencyLE cone y x) : x = y := by
  change y - x ∈ cone at hxy
  change x - y ∈ cone at hyx
  have hneg : -(y - x) ∈ cone := by
    simpa only [neg_sub] using hyx
  have hzero : y - x = 0 := hpointed (y - x) hxy hneg
  exact (sub_eq_zero.mp hzero).symm

/-! ## Transaction paths -/

variable {V : Type uV} {E : Type uE}

/-- A deterministic market graph whose edge labels are feasible net portfolio changes. -/
structure TransactionMarket (G : EdgeGraph V E) (Portfolio : Type uP) where
  /-- The set of feasible net changes on each transaction edge. -/
  increment : E → Set Portfolio

namespace TransactionMarket

variable {G : EdgeGraph V E} (market : TransactionMarket G Portfolio)

/-- The feasibility relation carried by a transaction edge. -/
def edgeRelation [AddCommGroup Portfolio] (edge : E) : SetRel Portfolio Portfolio :=
  {(source, target) | target - source ∈ market.increment edge}

/-- The market regarded as relation-labelled transport on the constant portfolio fiber. -/
def relationTransport [AddCommGroup Portfolio] :
    RelationTransport G (fun _vertex ↦ Portfolio) where
  edgeRelation := market.edgeRelation

/-- The set of feasible net changes along a path, obtained by Minkowski addition. -/
def walkIncrement [Zero Portfolio] [Add Portfolio] {start : V} :
    {finish : V} → G.Walk start finish → Set Portfolio
  | _, .nil => {0}
  | _, .concat walk edge _ => walkIncrement walk + market.increment edge

/-- Native transaction feasibility is membership of the net change in the pathwise Minkowski
sum. -/
theorem walkRelation_iff_sub_mem_walkIncrement [AddCommGroup Portfolio]
    {start finish : V} (walk : G.Walk start finish) (source target : Portfolio) :
    source ~[market.relationTransport.walkRelation walk] target ↔
      target - source ∈ market.walkIncrement walk := by
  induction walk generalizing source target with
  | nil =>
      simpa [RelationTransport.walkRelation, walkIncrement, sub_eq_zero] using
        (eq_comm : source = target ↔ target = source)
  | @concat middle walk edge legal ih =>
      subst middle
      constructor
      · rintro ⟨middle, hprefix, hedge⟩
        have hsum := Set.add_mem_add ((ih source middle).mp hprefix) hedge
        simpa only [fiberCast_const, walkIncrement,
          show middle - source + (target - middle) = target - source by abel] using hsum
      · intro hchange
        rw [walkIncrement, Set.mem_add] at hchange
        rcases hchange with ⟨firstChange, hfirst, lastChange, hlast, hsum⟩
        refine ⟨source + firstChange, (ih source (source + firstChange)).mpr ?_, ?_⟩
        · have heq : source + firstChange - source = firstChange := by abel
          simpa only [heq] using hfirst
        · change target - (source + firstChange) ∈ market.increment edge
          have heq : target - (source + firstChange) = lastChange := by
            calc
              target - (source + firstChange) = (target - source) - firstChange := by abel
              _ = (firstChange + lastChange) - firstChange := by rw [hsum]
              _ = lastChange := by abel
          simpa only [heq] using hlast

/-- Serial path concatenation adds the two pathwise attainable increment sets. -/
theorem walkIncrement_append [AddCommMonoid Portfolio]
    {start middle finish : V} (first : G.Walk start middle)
    (second : G.Walk middle finish) :
    market.walkIncrement (first.append second) =
      market.walkIncrement first + market.walkIncrement second := by
  induction second with
  | nil => simp [walkIncrement]
  | concat walk edge _ ih =>
      rw [EdgeGraph.Walk.append_concat]
      simp only [walkIncrement, ih, add_assoc]

/-- Powerset walk membership has an explicit source and net-increment witness. -/
theorem mem_walkMap_iff [AddCommGroup Portfolio]
    {start finish : V} (walk : G.Walk start finish)
    (set : Set Portfolio) (target : Portfolio) :
    target ∈ market.relationTransport.powersetTransport.walkMap walk set ↔
      ∃ source ∈ set, target - source ∈ market.walkIncrement walk := by
  rw [RelationTransport.walkMap_eq_image_walkRelation, SetRel.mem_image]
  constructor
  · rintro ⟨source, hsource, hrelation⟩
    exact ⟨source, hsource,
      (market.walkRelation_iff_sub_mem_walkIncrement walk source target).mp hrelation⟩
  · rintro ⟨source, hsource, hchange⟩
    exact ⟨source, hsource,
      (market.walkRelation_iff_sub_mem_walkIncrement walk source target).mpr hchange⟩

/-- Minkowski addition preserves convexity along every serial transaction path. -/
theorem convex_walkIncrement {Scalar : Type uR}
    [Semiring Scalar] [LinearOrder Scalar] [AddCommMonoid Portfolio]
    [Module Scalar Portfolio]
    (hconvex : ∀ edge : E, Convex Scalar (market.increment edge))
    {start finish : V} (walk : G.Walk start finish) :
    Convex Scalar (market.walkIncrement walk) := by
  induction walk with
  | nil =>
      change Convex Scalar ({0} : Set Portfolio)
      exact convex_singleton 0
  | concat walk edge _ ih =>
      simpa only [walkIncrement] using ih.add (hconvex edge)

end TransactionMarket

/-! ## Alternative paths versus convexification -/

/-- Two parallel one-step transaction opportunities. -/
def alternativeGraph : EdgeGraph Bool Bool where
  source _edge := false
  target _edge := true

/-- The two feasible changes are `-1` and `1`. -/
def alternativeMarket : TransactionMarket alternativeGraph ℝ where
  increment
    | false => {-1}
    | true => {1}

/-- Portfolios reachable from zero through either of the two parallel transactions. -/
def alternativeReachable : Set ℝ :=
  alternativeMarket.relationTransport.powersetTransport.edgeMap false {0} ∪
    alternativeMarket.relationTransport.powersetTransport.edgeMap true {0}

/-- Exact one-step reachability through the parallel edges is the two-point set `{-1, 1}`. -/
theorem alternativeReachable_eq : alternativeReachable = {-1, 1} := by
  ext target
  simp [alternativeReachable, TransactionMarket.relationTransport,
    RelationTransport.powersetTransport, TransactionMarket.edgeRelation, alternativeMarket]

/-- Aggregating two individually convex transaction paths by union need not preserve convexity. -/
theorem not_convex_alternativeReachable : ¬ Convex ℝ alternativeReachable := by
  rw [alternativeReachable_eq]
  intro hconvex
  have hneg : (-1 : ℝ) ∈ ({-1, 1} : Set ℝ) := by simp
  have hpos : (1 : ℝ) ∈ ({-1, 1} : Set ℝ) := by simp
  have hmid := hconvex hneg hpos
    (show (0 : ℝ) ≤ 2⁻¹ by norm_num) (show (0 : ℝ) ≤ 2⁻¹ by norm_num)
    (show (2⁻¹ : ℝ) + 2⁻¹ = 1 by norm_num)
  norm_num at hmid

/-- Convexification adds zero, although no transaction edge reaches zero from zero. -/
theorem zero_mem_convexHull_alternativeReachable :
    (0 : ℝ) ∈ convexHull ℝ alternativeReachable := by
  have hneg : (-1 : ℝ) ∈ convexHull ℝ alternativeReachable :=
    subset_convexHull ℝ alternativeReachable (by simp [alternativeReachable_eq])
  have hpos : (1 : ℝ) ∈ convexHull ℝ alternativeReachable :=
    subset_convexHull ℝ alternativeReachable (by simp [alternativeReachable_eq])
  have hmid := (convex_convexHull ℝ alternativeReachable) hneg hpos
    (show (0 : ℝ) ≤ 2⁻¹ by norm_num) (show (0 : ℝ) ≤ 2⁻¹ by norm_num)
    (show (2⁻¹ : ℝ) + 2⁻¹ = 1 by norm_num)
  norm_num at hmid ⊢
  exact hmid

/-- Zero is not exactly reachable through either parallel transaction edge. -/
theorem zero_not_mem_alternativeReachable : (0 : ℝ) ∉ alternativeReachable := by
  simp [alternativeReachable_eq]

end ConicFinance
