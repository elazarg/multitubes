/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import ProgramSemantics.PredicateTransport
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Union

/-!
# Executable finite-state reachability

A finite control-flow graph with a common finite state space admits a terminating saturation
algorithm. It exhausts the configuration space in a cardinality-bounded number of rounds and
agrees with execution along typed walks and with the least predicate closure.

## Main definitions

* `ProgramSemantics.successors` - immediate successors of a configuration.
* `ProgramSemantics.reachabilityStep` - one round of finite successor saturation.
* `ProgramSemantics.reachableConfigurations` - the terminating saturation result.
* `ProgramSemantics.reachableStates` - the result projected to each control location.

## Main results

* `ProgramSemantics.mem_reachableConfigurations_iff` - agreement with typed-walk execution.
* `ProgramSemantics.reachableWithin_stable` - saturation stabilizes by the configuration count.
* `ProgramSemantics.mem_reachableStates_iff_pathClosure` - agreement with least path closure.
* `ProgramSemantics.reset_reachableStates` - a concrete kernel-checked safety computation.

## Tags

program semantics, finite state, reachability, execution, path closure
-/

@[expose] public section

namespace ProgramSemantics

open Maths

universe uV uE uS

variable {V : Type uV} {E : Type uE} {State : Type uS}
variable (G : EdgeGraph V E) (step : E → State → State)

variable [Fintype V] [DecidableEq V] [Fintype E]
variable [Fintype State] [DecidableEq State]

/-- All immediate successors of one control-location/state configuration. -/
def successors (configuration : V × State) : Finset (V × State) :=
  Finset.univ.biUnion fun edge =>
    if G.source edge = configuration.1 then {(G.target edge, step edge configuration.2)} else ∅

/-- One saturation round: retain all known configurations and add their successors. -/
def reachabilityStep (known : Finset (V × State)) : Finset (V × State) :=
  known ∪ known.biUnion (successors G step)

/-- Configurations found after a prescribed number of saturation rounds. -/
def reachableWithin (initial : Finset (V × State)) (rounds : ℕ) : Finset (V × State) :=
  (reachabilityStep G step)^[rounds] initial

/-- The terminating reachability analysis, run for the size of the configuration space. -/
def reachableConfigurations (initial : Finset (V × State)) : Finset (V × State) :=
  reachableWithin G step initial (Fintype.card (V × State))

/-- The states found by finite reachability analysis at one control location. -/
def reachableStates (initial : V → Finset State) (vertex : V) : Finset State :=
  Finset.univ.filter fun state =>
    (vertex, state) ∈ reachableConfigurations G step
      (Finset.univ.biUnion fun source => (initial source).image (source, ·))

omit [Fintype V] [Fintype State] in
private theorem mem_successors_iff (source target : V × State) :
    target ∈ successors G step source ↔
      ∃ edge : E, G.source edge = source.1 ∧
        target = (G.target edge, step edge source.2) := by
  simp only [successors, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨edge, hedge⟩
    split at hedge
    · exact ⟨edge, ‹G.source edge = source.1›, Finset.mem_singleton.mp hedge⟩
    · simp at hedge
  · rintro ⟨edge, hsource, rfl⟩
    exact ⟨edge, by simp [hsource]⟩

omit [Fintype V] [Fintype State] in
/-- Membership after a fixed number of rounds is execution by a walk of at most that length. -/
theorem mem_reachableWithin_iff (initial : Finset (V × State))
    (rounds : ℕ) (target : V × State) :
    target ∈ reachableWithin G step initial rounds ↔
      ∃ (source : V × State) (walk : G.Walk source.1 target.1),
        source ∈ initial ∧ walk.length ≤ rounds ∧ target.2 = transport step walk source.2 := by
  induction rounds generalizing target with
  | zero =>
      rcases target with ⟨targetVertex, targetState⟩
      rw [reachableWithin, Function.iterate_zero_apply]
      constructor
      · intro h
        exact ⟨(targetVertex, targetState), EdgeGraph.Walk.nil, h, by simp, rfl⟩
      · rintro ⟨source, walk, hsource, hlength, hstate⟩
        rcases source with ⟨sourceVertex, sourceState⟩
        cases walk with
        | nil =>
            change targetState = sourceState at hstate
            subst targetState
            exact hsource
        | concat walk edge legal => simp at hlength
  | succ rounds ih =>
      rcases target with ⟨targetVertex, targetState⟩
      rw [reachableWithin, Function.iterate_succ_apply']
      simp only [reachabilityStep, Finset.mem_union, Finset.mem_biUnion]
      constructor
      · rintro (hknown | ⟨middle, hmiddle, hnext⟩)
        · obtain ⟨source, walk, hsource, hlength, hstate⟩ :=
            (ih (targetVertex, targetState)).mp hknown
          exact ⟨source, walk, hsource, hlength.trans (Nat.le_succ rounds), hstate⟩
        · obtain ⟨source, walk, hsource, hlength, hstate⟩ := (ih middle).mp hmiddle
          obtain ⟨edge, legal, htarget⟩ :=
            (mem_successors_iff G step middle (targetVertex, targetState)).mp hnext
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj htarget
          refine ⟨source, walk.concat edge legal, hsource, by simpa, ?_⟩
          simp [transport_concat, hstate]
      · rintro ⟨source, walk, hsource, hlength, hstate⟩
        by_cases hshort : walk.length ≤ rounds
        · exact Or.inl
            ((ih (targetVertex, targetState)).mpr ⟨source, walk, hsource, hshort, hstate⟩)
        · cases walk with
          | nil => simp at hshort
          | @concat middle walk edge legal =>
              apply Or.inr
              let before : V × State := (middle, transport step walk source.2)
              have hbefore : walk.length ≤ rounds := by simpa using hlength
              refine ⟨before, (ih before).mpr ⟨source, walk, hsource, hbefore, rfl⟩, ?_⟩
              apply (mem_successors_iff G step before (G.target edge, targetState)).mpr
              refine ⟨edge, legal, Prod.ext rfl ?_⟩
              change targetState = step edge (transport step walk source.2)
              simpa [transport_concat] using hstate

omit [Fintype V] [Fintype State] in
private theorem reachableWithin_mono (initial : Finset (V × State)) :
    Monotone (reachableWithin G step initial) := by
  intro first second hle target htarget
  obtain ⟨source, walk, hsource, hlength, hstate⟩ :=
    (mem_reachableWithin_iff G step initial first target).mp htarget
  exact (mem_reachableWithin_iff G step initial second target).mpr
    ⟨source, walk, hsource, hlength.trans hle, hstate⟩

/-- Saturation has stabilized after as many rounds as there are configurations. -/
theorem reachableWithin_stable (initial : Finset (V × State)) :
    reachabilityStep G step (reachableConfigurations G step initial) =
      reachableConfigurations G step initial := by
  let total := Fintype.card (V × State)
  by_contra hne
  have hstrict : ∀ n ≤ total,
      reachableWithin G step initial n ⊂ reachableWithin G step initial (n + 1) := by
    intro n hn
    refine Finset.ssubset_iff_subset_ne.mpr ⟨
      reachableWithin_mono G step initial (Nat.le_succ n), ?_⟩
    intro heq
    have hpersist : ∀ k, reachableWithin G step initial (n + k) =
        reachableWithin G step initial n := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
          calc
            reachableWithin G step initial (n + (k + 1)) =
                reachabilityStep G step (reachableWithin G step initial (n + k)) := by
              rw [show n + (k + 1) = (n + k) + 1 by omega]
              simp [reachableWithin, Function.iterate_succ_apply']
            _ = reachabilityStep G step (reachableWithin G step initial n) :=
              congrArg (reachabilityStep G step) ih
            _ = reachableWithin G step initial n := by
              simpa [reachableWithin, Function.iterate_succ_apply'] using heq.symm
    have htotal := hpersist (total - n)
    rw [Nat.add_sub_of_le hn] at htotal
    apply hne
    change reachabilityStep G step
      (reachableWithin G step initial total) = reachableWithin G step initial total
    rw [htotal]
    simpa [reachableWithin, Function.iterate_succ_apply'] using heq.symm
  have hcard : ∀ n ≤ total + 1, n ≤ (reachableWithin G step initial n).card := by
    intro n hn
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
        exact (Nat.succ_le_succ (ih (Nat.le_trans (Nat.le_succ n) hn))).trans
          (Finset.card_lt_card (hstrict n (Nat.le_of_succ_le_succ hn)))
  have huniv := Finset.card_le_card
    (show reachableWithin G step initial (total + 1) ⊆ Finset.univ from Finset.subset_univ _)
  exact Nat.not_succ_le_self total <| by
    simpa [total] using (hcard (total + 1) le_rfl).trans huniv

/-- The finite analysis contains exactly the configurations obtained by executing a typed walk
from an initial configuration. -/
theorem mem_reachableConfigurations_iff (initial : Finset (V × State))
    (target : V × State) :
    target ∈ reachableConfigurations G step initial ↔
      ∃ (source : V × State) (walk : G.Walk source.1 target.1),
        source ∈ initial ∧ target.2 = transport step walk source.2 := by
  constructor
  · rw [reachableConfigurations, mem_reachableWithin_iff]
    rintro ⟨source, walk, hsource, -, hstate⟩
    exact ⟨source, walk, hsource, hstate⟩
  · rintro ⟨source, walk, hsource, hstate⟩
    have hfixed := reachableWithin_stable G step initial
    have hclosed : ∀ n,
        reachableWithin G step initial (Fintype.card (V × State) + n) =
          reachableConfigurations G step initial := by
      intro n
      induction n with
      | zero => simp [reachableConfigurations]
      | succ n ih =>
          rw [show Fintype.card (V × State) + (n + 1) =
            (Fintype.card (V × State) + n) + 1 by omega]
          rw [reachableWithin, Function.iterate_succ_apply']
          change reachabilityStep G step
            (reachableWithin G step initial (Fintype.card (V × State) + n)) = _
          rw [ih, hfixed]
    have hmem := (mem_reachableWithin_iff G step initial
      (Fintype.card (V × State) + walk.length) target).mpr
        ⟨source, walk, hsource, Nat.le_add_left _ _, hstate⟩
    rwa [hclosed walk.length] at hmem

omit [Fintype V] [DecidableEq V] [Fintype E] [Fintype State] [DecidableEq State] in
private theorem mem_walkMap_forwardPredicateTransport_iff {start finish : V}
    (walk : G.Walk start finish) (initial : Set State) (target : State) :
    target ∈ (forwardPredicateTransport (State := fun _ : V => State) G step).walkMap
      walk initial ↔
      ∃ source ∈ initial, target = transport step walk source := by
  induction walk generalizing target with
  | nil => simp
  | concat walk edge legal ih =>
      simp only [Transport.walkMap_concat, forwardPredicateTransport, fiberCast_const,
        Set.mem_image]
      constructor
      · rintro ⟨middle, hmiddle, rfl⟩
        obtain ⟨source, hsource, rfl⟩ := (ih middle).mp hmiddle
        exact ⟨source, hsource, by simp [transport_concat]⟩
      · rintro ⟨source, hsource, rfl⟩
        exact ⟨transport step walk source,
          (ih (transport step walk source)).mpr ⟨source, hsource, rfl⟩,
          by simp [transport_concat]⟩

/-- Projected finite reachability agrees with membership in the existing least path closure. -/
theorem mem_reachableStates_iff_pathClosure (initial : V → Finset State)
    (vertex : V) (state : State) :
    state ∈ reachableStates G step initial vertex ↔
      state ∈ (forwardPredicateTransport G step).pathClosure
        (fun source => (initial source : Set State)) vertex := by
  rw [reachableStates, Finset.mem_filter, mem_reachableConfigurations_iff]
  simp only [Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_image]
  change (∃ source walk, (∃ (control : V) (initialState : State),
      initialState ∈ initial control ∧ (control, initialState) = source) ∧
      state = transport step walk source.2) ↔ _
  have hleft : (∃ (source : V × State) (walk : G.Walk source.1 vertex),
      (∃ (control : V) (initialState : State),
      initialState ∈ initial control ∧ (control, initialState) = source) ∧
      state = transport step walk source.2) ↔
      ∃ (source : V) (walk : G.Walk source vertex) (initialState : State),
        initialState ∈ initial source ∧ state = transport step walk initialState := by
    constructor
    · rintro ⟨source, walk, ⟨control, initialState, hinitial, rfl⟩, hstate⟩
      exact ⟨control, walk, initialState, hinitial, hstate⟩
    · rintro ⟨source, walk, initialState, hinitial, hstate⟩
      exact ⟨(source, initialState), walk, ⟨source, initialState, hinitial, rfl⟩, hstate⟩
  rw [hleft]
  simp [Transport.pathClosure, mem_walkMap_forwardPredicateTransport_iff]

/-! ## Main results -/

/-- The one-location control-flow graph whose unique instruction toggles a Boolean state. -/
def toggleGraph : EdgeGraph Unit Unit where
  source _ := ()
  target _ := ()

/-- The state transformer of the Boolean toggle program. -/
def toggleStep (_ : Unit) : Bool → Bool := Bool.not

/-- Starting at `false`, saturation of the toggle program computes both Boolean states. -/
theorem toggle_reachableStates :
    reachableStates toggleGraph toggleStep (fun _ => {false}) () = {false, true} := by
  decide

/-- The one-instruction program that resets every Boolean state to `false`. -/
def resetStep (_ : Unit) : Bool → Bool := collapse

/-- The noninjective reset reaches only `false` from `false`, certifying that `true` is
unreachable. -/
theorem reset_reachableStates :
    reachableStates toggleGraph resetStep (fun _ => {false}) () = {false} := by
  decide

end ProgramSemantics

end
