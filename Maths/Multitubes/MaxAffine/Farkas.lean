/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.MaxAffine.Basic
public import Mathlib.Data.Fintype.Sum

import Maths.Multitubes.FiniteInequality.Basic

/-!
# Lax sections at mixed slopes: the cyclewise test fails, the linear test does not

`Maths.Multitubes.MaxAffine.Sections` settles existence of a lax section in
two regimes -- all slopes below one, and all slopes equal to one -- and in the
unit-slope regime the criterion is cyclewise: a lax section exists exactly when
the composite label of every closed walk has a pre-fixed point
(`Maths.MaxAffineTransport.exists_isLaxSection_iff_forall_cycle_exists_prefixed`).
This file settles what happens when the slopes are mixed.

**The cyclewise test is not complete.**  One vertex carrying two loops, a
constant reset `x ↦ 10` of slope `0` and a doubling `x ↦ 2 * x` of slope `2`,
admits no lax section: the two edge inequalities read `10 ≤ φ` and
`2 * φ ≤ φ`.  Yet every closed walk passes the per-cycle test of
`Maths.MaxAffineTransport.Label.exists_apply_le_self_iff`.  A walk using the
reset has slope product `0`, so it is contractive; a walk of pure doublings has
slope product above one and no floor, so its affine branch has a fixed point
below which everything is dominated; and the empty walk is the identity.  The
pre-fixed points of the separate closed walks exist at incompatible values, and
nothing makes them synchronize.

**The complete test is linear, not cyclewise.**  Each edge contributes two
linear inequalities in the candidate, `floor e ≤ φ (target e)` when the floor is
finite and `shift e + slope e * φ (source e) ≤ φ (target e)` always -- the
splitting of `Maths.MaxAffineTransport.Label.apply_le_target_iff`.  Whatever the
signs of the slopes, this is a finite system of linear inequalities, so
existence of a lax section is governed by the theorem of the alternative of
`Maths.exists_potential_iff_no_nonnegative_incompatibility`.

## Main definitions

* `Maths.MaxAffineTransport.loopGraph`,
  `Maths.MaxAffineTransport.resetLabel`,
  `Maths.MaxAffineTransport.doubleLabel`,
  `Maths.MaxAffineTransport.loopLabel` -- the one-vertex two-loop
  counterexample.
* `Maths.MaxAffineTransport.rowDelta`,
  `Maths.MaxAffineTransport.rowBase` -- the two linear inequality rows
  contributed by each edge.
* `Maths.MaxAffineTransport.IsFarkasCertificate` -- a nonnegative balanced
  combination of those rows with positive total bound.

## Main results

* `Maths.MaxAffineTransport.isLaxSection_iff_forall_row` -- lax sections are
  exactly the solutions of the row system.
* `Maths.MaxAffineTransport.not_exists_isLaxSection_loopLabel` -- the two-loop
  labelling has no lax section.
* `Maths.MaxAffineTransport.exists_apply_compList_le_self_loopLabel` -- every
  closed walk of that graph has a composite label with a pre-fixed point.
* `Maths.MaxAffineTransport.not_forall_cycle_prefixed_imp_exists_isLaxSection` --
  the two together: the cyclewise test is not sufficient, even for finitely many
  vertices and edges and nonnegative slopes.
* `Maths.MaxAffineTransport.exists_isLaxSection_iff_no_nonnegative_certificate` --
  the general duality: a lax section exists exactly when no nonnegative
  combination of the edge rows is balanced at every vertex with positive total
  bound.

## Implementation notes

The certificate of the last theorem is a generalized-flow, or gain-flow,
certificate: the weights of the affine rows are edge flows, the balance
condition at a vertex equates the incoming flow with the outgoing flow scaled by
the edge slopes, and the weights of the floor rows are the slack absorbed by the
floors.  A positive-weight cycle is the special case whose support is one closed
walk, with the slopes multiplying along it.

The duality is existential on both sides: nothing here computes a certificate or
bounds its size.

## References

* A. Schrijver, *Theory of Linear and Integer Programming*, Wiley (1986), for
  Farkas' lemma and linear programming duality.
* R. K. Ahuja, T. L. Magnanti and J. B. Orlin, *Network Flows: Theory,
  Algorithms, and Applications*, Prentice Hall (1993), for generalized network
  flows.

## Tags

Farkas lemma, theorem of the alternative, generalized flow, gain flow,
max-affine, lax section
-/

@[expose] public section

noncomputable section

namespace Maths.MaxAffineTransport

namespace Label

/-! ## Coefficients of a composite of floorless labels -/

/-- Composition keeps the absent floor absent: the outer floor is joined with
the inner floor pushed forward, and `Maths.MaxAffineTransport.Label.pushFloor`
preserves `⊥`. -/
theorem floor_foldl_comp : ∀ (l : List Label), (∀ f ∈ l, f.floor = ⊥) → ∀ acc : Label,
    acc.floor = ⊥ → (l.foldl (fun a f => f.comp a) acc).floor = ⊥
  | [], _, _, hacc => hacc
  | f :: rest, hfloor, acc, hacc => by
      have hrest (g : Label) (hg : g ∈ rest) : g.floor = ⊥ :=
        hfloor g (List.mem_cons_of_mem _ hg)
      have hf : f.floor = ⊥ := hfloor f (List.mem_cons_self ..)
      refine floor_foldl_comp rest hrest (f.comp acc) ?_
      simp [hf, hacc]

/-- A composite of floorless labels is floorless. -/
theorem floor_compList {l : List Label} (hfloor : ∀ f ∈ l, f.floor = ⊥) :
    (compList l).floor = ⊥ :=
  floor_foldl_comp l hfloor Label.id floor_id

theorem slope_foldl_comp_eq_prod : ∀ (l : List Label) (acc : Label),
    (l.foldl (fun a f => f.comp a) acc).slope = (l.map Label.slope).prod * acc.slope
  | [], acc => by simp
  | f :: rest, acc => by
      rw [List.foldl_cons, slope_foldl_comp_eq_prod rest (f.comp acc)]
      simp only [List.map_cons, List.prod_cons, slope_comp]
      ring

/-- The slope of a composite is the product of the slopes. -/
theorem slope_compList_eq_prod (l : List Label) :
    (compList l).slope = (l.map Label.slope).prod := by
  rw [compList, slope_foldl_comp_eq_prod l Label.id, slope_id, mul_one]

/-- **A floorless label has a pre-fixed point unless it is a positive
translation.**  The absent floor satisfies the expansive branch of
`Maths.MaxAffineTransport.Label.exists_apply_le_self_iff` outright, so only the
unit slope carries a condition. -/
theorem exists_apply_le_self_of_floor_bot {f : Label} (hfloor : f.floor = ⊥)
    (hunit : f.slope = 1 → f.shift ≤ 0) : ∃ x : ℝ, f.apply x ≤ x := by
  rw [exists_apply_le_self_iff]
  rcases lt_trichotomy f.slope 1 with hlt | heq | hgt
  · exact Or.inl hlt
  · exact Or.inr (Or.inl ⟨heq, hunit heq⟩)
  · exact Or.inr (Or.inr ⟨hgt, by rw [hfloor]; exact bot_le⟩)

end Label

/-! ## The two-loop counterexample to the cyclewise test -/

section Counterexample

/-- One vertex with two loops. -/
def loopGraph : EdgeGraph Unit Bool where
  source := fun _ => ()
  target := fun _ => ()

/-- The constant reset `x ↦ 10`: slope `0`, no floor. -/
def resetLabel : Label := ⟨⊥, 10, 0⟩

/-- The doubling `x ↦ 2 * x`: slope `2`, no floor. -/
def doubleLabel : Label := ⟨⊥, 0, 2⟩

/-- The two loops of `Maths.MaxAffineTransport.loopGraph`: `false` resets and
`true` doubles. -/
def loopLabel : Bool → Label
  | false => resetLabel
  | true => doubleLabel

@[simp] theorem loopLabel_false : loopLabel false = resetLabel := rfl

@[simp] theorem loopLabel_true : loopLabel true = doubleLabel := rfl

@[simp] theorem floor_resetLabel : resetLabel.floor = ⊥ := rfl

@[simp] theorem floor_doubleLabel : doubleLabel.floor = ⊥ := rfl

@[simp] theorem slope_resetLabel : resetLabel.slope = 0 := rfl

@[simp] theorem slope_doubleLabel : doubleLabel.slope = 2 := rfl

@[simp] theorem apply_resetLabel (x : ℝ) : resetLabel.apply x = 10 := by
  simp [resetLabel]

@[simp] theorem apply_doubleLabel (x : ℝ) : doubleLabel.apply x = 2 * x := by
  simp [doubleLabel]

theorem floor_loopLabel (e : Bool) : (loopLabel e).floor = ⊥ := by
  cases e <;> rfl

theorem slope_loopLabel_nonneg (e : Bool) : 0 ≤ (loopLabel e).slope := by
  cases e <;> simp

/-- **No lax section.**  The reset demands `10 ≤ φ` and the doubling demands
`2 * φ ≤ φ`. -/
theorem not_exists_isLaxSection_loopLabel :
    ¬∃ φ : Unit → ℝ, IsLaxSection loopGraph loopLabel φ := by
  rintro ⟨φ, hφ⟩
  have hreset : (10 : ℝ) ≤ φ () := by
    have := hφ false
    simpa using this
  have hdouble : 2 * φ () ≤ φ () := by
    have := hφ true
    simpa using this
  linarith

/-- The slope product of a closed walk is either zero, or above one, or the
walk is empty: the doubling contributes `2` and the reset contributes `0`. -/
theorem slopeProd_loopLabel_cases (l : List Bool) :
    (l.map fun e => (loopLabel e).slope).prod = 0 ∨
      1 < (l.map fun e => (loopLabel e).slope).prod ∨ l = [] := by
  induction l with
  | nil => exact Or.inr (Or.inr rfl)
  | cons e rest ih =>
      cases e with
      | false => exact Or.inl (by simp)
      | true =>
          rcases ih with hzero | hgt | hnil
          · exact Or.inl (by simp [hzero])
          · refine Or.inr (Or.inl ?_)
            simp only [List.map_cons, List.prod_cons, loopLabel_true, slope_doubleLabel]
            linarith
          · subst hnil
            exact Or.inr (Or.inl (by norm_num))

/-- **Every closed walk passes the cyclewise test.**  All floors are absent, so
`Maths.MaxAffineTransport.Label.exists_apply_le_self_of_floor_bot` reduces the
question to the unit-slope case, which by
`Maths.MaxAffineTransport.slopeProd_loopLabel_cases` occurs only for the empty
walk, whose composite is the identity. -/
theorem exists_apply_compList_le_self_loopLabel (base : Unit)
    (cycle : loopGraph.Walk base base) :
    ∃ x : ℝ, (Label.compList (cycle.edges.map loopLabel)).apply x ≤ x := by
  refine Label.exists_apply_le_self_of_floor_bot (Label.floor_compList ?_) ?_
  · intro f hf
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hf
    exact floor_loopLabel e
  · intro hslope
    rw [Label.slope_compList_eq_prod] at hslope
    simp only [List.map_map, Function.comp_def] at hslope
    rcases slopeProd_loopLabel_cases cycle.edges with hzero | hgt | hnil
    · rw [hzero] at hslope
      exact absurd hslope.symm (by norm_num)
    · rw [hslope] at hgt
      exact absurd hgt (lt_irrefl 1)
    · rw [hnil]
      simp

/-- **The cyclewise test is not a complete proof rule for lax sections.**  The
labelling of `Maths.MaxAffineTransport.loopLabel` has nonnegative slopes on a
graph with finitely many vertices and edges, every closed walk has a composite
label with a pre-fixed point, and there is no lax section.  Under all slopes
equal to one the implication does hold, by
`Maths.MaxAffineTransport.exists_isLaxSection_iff_forall_cycle_exists_prefixed`;
`Maths.MaxAffineTransport.exists_isLaxSection_iff_no_nonnegative_certificate` is
the criterion that survives mixed slopes. -/
theorem not_forall_cycle_prefixed_imp_exists_isLaxSection :
    ¬∀ (V E : Type) (_ : Fintype V) (_ : Fintype E) (G : EdgeGraph V E) (label : E → Label),
        (∀ e : E, 0 ≤ (label e).slope) →
        (∀ (base : V) (cycle : G.Walk base base),
          ∃ x : ℝ, (Label.compList (cycle.edges.map label)).apply x ≤ x) →
        ∃ φ : V → ℝ, IsLaxSection G label φ := by
  intro hrule
  exact not_exists_isLaxSection_loopLabel
    (hrule Unit Bool inferInstance inferInstance loopGraph loopLabel slope_loopLabel_nonneg
      exists_apply_compList_le_self_loopLabel)

end Counterexample

/-! ## The linear duality at arbitrary slopes -/

section Farkas

variable {V E : Type*} [Fintype V] [DecidableEq V] {G : EdgeGraph V E} {label : E → Label}

/-- The row vectors of the lax-section system, indexed by `E ⊕ E`: the left copy
carries the affine inequality of an edge, the right copy its floor inequality.
An absent floor gives the zero row, which the zero bound of
`Maths.MaxAffineTransport.rowBase` makes vacuous. -/
def rowDelta (G : EdgeGraph V E) (label : E → Label) : E ⊕ E → V → ℝ
  | Sum.inl e => fun v =>
      (if v = G.target e then 1 else 0) -
        (label e).slope * (if v = G.source e then 1 else 0)
  | Sum.inr e => fun v =>
      (label e).floor.recBotCoe 0 (fun _ => if v = G.target e then 1 else 0)

/-- The lower bounds of the lax-section system: the shift on an affine row, the
floor on a floor row, and `0` on the vacuous row of a floorless edge. -/
def rowBase (label : E → Label) : E ⊕ E → ℝ
  | Sum.inl e => (label e).shift
  | Sum.inr e => (label e).floor.unbotD 0

theorem dotProduct_rowDelta_inl (e : E) (φ : V → ℝ) :
    dotProduct (rowDelta G label (Sum.inl e)) φ
      = φ (G.target e) - (label e).slope * φ (G.source e) := by
  have hterm (v : V) : rowDelta G label (Sum.inl e) v * φ v
      = (if v = G.target e then φ v else 0)
        - (label e).slope * (if v = G.source e then φ v else 0) := by
    simp only [rowDelta, sub_mul, ite_mul, one_mul, zero_mul, mul_assoc]
  rw [dotProduct]
  simp only [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

theorem dotProduct_rowDelta_inr_of_floor_bot {e : E} (hfloor : (label e).floor = ⊥)
    (φ : V → ℝ) : dotProduct (rowDelta G label (Sum.inr e)) φ = 0 := by
  have hrow : rowDelta G label (Sum.inr e) = fun _ : V => (0 : ℝ) := by
    funext v
    simp [rowDelta, hfloor]
  simp [hrow]

theorem dotProduct_rowDelta_inr_of_floor_coe {e : E} {c : ℝ}
    (hfloor : (label e).floor = (c : WithBot ℝ)) (φ : V → ℝ) :
    dotProduct (rowDelta G label (Sum.inr e)) φ = φ (G.target e) := by
  have hrow : rowDelta G label (Sum.inr e)
      = fun v : V => if v = G.target e then (1 : ℝ) else 0 := by
    funext v
    simp [rowDelta, hfloor]
  rw [dotProduct, hrow]
  simp

/-- **The lax-section system is the row system of the rows above.**  The two
halves of an edge inequality are exactly the splitting of
`Maths.MaxAffineTransport.Label.apply_le_target_iff`. -/
theorem isLaxSection_iff_forall_row (G : EdgeGraph V E) (label : E → Label) (φ : V → ℝ) :
    IsLaxSection G label φ ↔
      ∀ action, rowBase label action ≤ dotProduct (rowDelta G label action) φ := by
  constructor
  · intro hφ action
    cases action with
    | inl e =>
        obtain ⟨_, haffine⟩ := (Label.apply_le_target_iff _ _ _).1 (hφ e)
        rw [dotProduct_rowDelta_inl]
        simp only [Label.affinePart] at haffine
        change (label e).shift ≤ _
        linarith
    | inr e =>
        obtain ⟨hfloorle, _⟩ := (Label.apply_le_target_iff _ _ _).1 (hφ e)
        rcases (label e).floor_cases with hfloor | ⟨c, hfloor⟩
        · rw [dotProduct_rowDelta_inr_of_floor_bot hfloor]
          change (label e).floor.unbotD 0 ≤ (0 : ℝ)
          rw [hfloor]
          simp
        · rw [dotProduct_rowDelta_inr_of_floor_coe hfloor]
          change (label e).floor.unbotD 0 ≤ _
          rw [hfloor] at hfloorle ⊢
          simpa using hfloorle
  · intro hrow e
    refine (Label.apply_le_target_iff _ _ _).2 ⟨?_, ?_⟩
    · rcases (label e).floor_cases with hfloor | ⟨c, hfloor⟩
      · rw [hfloor]
        exact bot_le
      · have := hrow (Sum.inr e)
        rw [dotProduct_rowDelta_inr_of_floor_coe hfloor] at this
        rw [hfloor]
        refine WithBot.coe_le_coe.2 ?_
        have hbase : rowBase label (Sum.inr e) = c := by
          change (label e).floor.unbotD 0 = c
          rw [hfloor]
          simp
        rwa [hbase] at this
    · have := hrow (Sum.inl e)
      rw [dotProduct_rowDelta_inl] at this
      have hbase : rowBase label (Sum.inl e) = (label e).shift := rfl
      rw [hbase] at this
      simp only [Label.affinePart]
      linarith

/-- **Strong duality for lax sections, at arbitrary slopes.**  A lax section
exists exactly when the rows of the lax-section system admit no nonnegative
combination that is balanced at every vertex and has strictly positive total
bound.  This is
`Maths.exists_potential_iff_no_nonnegative_incompatibility` at the encoding of
`Maths.MaxAffineTransport.rowDelta` and
`Maths.MaxAffineTransport.rowBase`, so no sign condition on the slopes and no
structure on the graph is used.

At arbitrary slopes the certificate is a nonnegative linear dependency among
the rows.  At nonnegative slopes it additionally reads as a generalized-flow,
or gain-flow, certificate: the weights of the affine rows are edge flows whose
balance at a vertex scales the outgoing flow by the edge slopes, and the
weights of the floor rows absorb the floors; a negative slope puts positive
coefficients at both endpoints of its row, which no flow reading carries.  An
affine-only certificate supported on one closed walk must satisfy
`λ (i - 1) = slope i * λ i` around the cycle, forcing the slope product to be
one; the classical positive-shift cycle at unit slopes is that case, and an
expanding cycle obstructed by a floor needs a floor-row weight as well.
Cyclewise certificates alone are not complete, by
`Maths.MaxAffineTransport.not_forall_cycle_prefixed_imp_exists_isLaxSection`.
Literature: linear programming duality and Farkas' lemma; generalized network
flows. -/
theorem exists_isLaxSection_iff_no_nonnegative_certificate [Fintype E]
    (G : EdgeGraph V E) (label : E → Label) :
    (∃ φ : V → ℝ, IsLaxSection G label φ) ↔
      ¬∃ coefficient : E ⊕ E → ℝ,
        (∀ action, 0 ≤ coefficient action) ∧
        (∀ v : V, ∑ action, coefficient action * rowDelta G label action v = 0) ∧
        0 < ∑ action, coefficient action * rowBase label action := by
  rw [exists_congr fun φ => isLaxSection_iff_forall_row G label φ]
  exact Maths.exists_potential_iff_no_nonnegative_incompatibility
    (rowDelta G label) (rowBase label)

/-- A **Farkas certificate** against the lax-section system of a labelled
graph: nonnegative weights on the rows, balanced at every vertex, with
strictly positive total bound.  At nonnegative slopes this reads as a
generalized-flow (gain-flow) certificate; at arbitrary slopes it is a
nonnegative linear dependency witnessing infeasibility. -/
def IsFarkasCertificate [Fintype E] (G : EdgeGraph V E) (label : E → Label)
    (coefficient : E ⊕ E → ℝ) : Prop :=
  (∀ action, 0 ≤ coefficient action) ∧
    (∀ v : V, ∑ action, coefficient action * rowDelta G label action v = 0) ∧
    0 < ∑ action, coefficient action * rowBase label action

/-- Strong duality through the certificate predicate. -/
theorem exists_isLaxSection_iff_no_farkasCertificate [Fintype E]
    (G : EdgeGraph V E) (label : E → Label) :
    (∃ φ : V → ℝ, IsLaxSection G label φ) ↔
      ¬∃ coefficient, IsFarkasCertificate G label coefficient := by
  simp only [IsFarkasCertificate]
  exact exists_isLaxSection_iff_no_nonnegative_certificate G label

/-- The certificate as a produced obstruction: when no lax section exists, a
certificate does. -/
theorem not_exists_isLaxSection_iff_exists_farkasCertificate [Fintype E]
    (G : EdgeGraph V E) (label : E → Label) :
    (¬∃ φ : V → ℝ, IsLaxSection G label φ) ↔
      ∃ coefficient, IsFarkasCertificate G label coefficient := by
  rw [exists_isLaxSection_iff_no_farkasCertificate, not_not]

/-- The alternative: a lax section or a certificate, never neither. -/
theorem exists_isLaxSection_or_exists_farkasCertificate [Fintype E]
    (G : EdgeGraph V E) (label : E → Label) :
    (∃ φ : V → ℝ, IsLaxSection G label φ) ∨
      ∃ coefficient, IsFarkasCertificate G label coefficient := by
  by_cases hcert : ∃ coefficient, IsFarkasCertificate G label coefficient
  · exact Or.inr hcert
  · exact Or.inl ((exists_isLaxSection_iff_no_farkasCertificate G label).mpr hcert)

end Farkas

/-! ## The certificate of the two-loop counterexample -/

section LoopCertificate

/-- The explicit certificate of the two-loop counterexample: unit weight on
each affine row, none on the floor rows.  The reset's affine row is `1` at the
unique vertex with bound `10`, the doubling's is `1 - 2 = -1` with bound `0`,
so the combination is balanced with total bound `10`. -/
theorem isFarkasCertificate_loopLabel :
    IsFarkasCertificate loopGraph loopLabel (Sum.elim (fun _ => 1) fun _ => 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (e | e) <;> simp
  · intro v
    rw [Fintype.sum_sum_type]
    simp [rowDelta, loopGraph, resetLabel, doubleLabel]
  · rw [Fintype.sum_sum_type]
    simp [rowBase, resetLabel, doubleLabel]

end LoopCertificate

end Maths.MaxAffineTransport

end
