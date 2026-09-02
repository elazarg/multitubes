/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitube.Closure
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Provenance-aware endorsement transport

An evidence record may retain its issuer, subject, capability, confidence, and supporting
principals. An endorsement edge acts on sets of such records. Requiring the action to preserve
arbitrary unions says that alternatives may be transported independently and that no evidence is
created from an empty input.

A sound assignment contains every record transferred across each endorsement. This is precisely
a lax section. The transport path closure therefore constructs the least sound
assignment containing prescribed seed evidence and identifies each generated record with an
endorsement-chain witness.

## Main definitions

* `WebOfTrust.evidenceTransport` - transport by union-preserving evidence transfers.
* `WebOfTrust.IsSoundAssignment` - an evidence family closed under every edge transfer.
* `WebOfTrust.soundClosure` - evidence generated from seeds along all typed walks.

## Main results

* `WebOfTrust.isSoundAssignment_iff` - soundness is the local edgewise inclusion.
* `WebOfTrust.evidenceTransport_edgeMap_monotone` - evidence transfer is monotone.
* `WebOfTrust.chainEvidence_le_of_isSound` - every endorsement chain preserves soundness.
* `WebOfTrust.seedEvidence_le_along` - seed evidence is sound along every chain.
* `WebOfTrust.mem_soundClosure_iff` - generated evidence has a source and path witness.
* `WebOfTrust.soundClosure_isLeast` - generated evidence is the least sound extension.

## Tags

web of trust, endorsement, provenance, evidence, path closure, lax section
-/

@[expose] public section

noncomputable section

namespace WebOfTrust

open Maths

universe uV uE uP

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}
variable {Evidence : V → Type uP}

/-- Transport induced by union-preserving endorsement transfers on evidence sets. -/
def evidenceTransport (G : EdgeGraph V E)
    (transfer : (edge : E) →
      sSupHom (Set (Evidence (G.source edge))) (Set (Evidence (G.target edge)))) :
    Transport G (fun vertex ↦ Set (Evidence vertex)) where
  edgeMap edge := transfer edge

/-- A global evidence assignment containing every record justified by one endorsement step. -/
def IsSoundAssignment (G : EdgeGraph V E)
    (transfer : (edge : E) →
      sSupHom (Set (Evidence (G.source edge))) (Set (Evidence (G.target edge))))
    (assignment : ∀ vertex, Set (Evidence vertex)) : Prop :=
  (evidenceTransport G transfer).IsLaxSection assignment

/-- Soundness is exactly the local inclusion attached to each endorsement edge. -/
theorem isSoundAssignment_iff (G : EdgeGraph V E)
    (transfer : (edge : E) →
      sSupHom (Set (Evidence (G.source edge))) (Set (Evidence (G.target edge))))
    (assignment : ∀ vertex, Set (Evidence vertex)) :
    IsSoundAssignment G transfer assignment ↔
      ∀ edge, transfer edge (assignment (G.source edge)) ⊆
        assignment (G.target edge) :=
  Iff.rfl

/-- Every union-preserving endorsement transfer is monotone. -/
theorem evidenceTransport_edgeMap_monotone (G : EdgeGraph V E)
    (transfer : (edge : E) →
      sSupHom (Set (Evidence (G.source edge))) (Set (Evidence (G.target edge)))) :
    ∀ edge, Monotone ((evidenceTransport G transfer).edgeMap edge) := by
  intro edge lower upper hlower
  change transfer edge lower ⊆ transfer edge upper
  calc
    transfer edge lower ⊆ transfer edge lower ⊔ transfer edge upper := le_sup_left
    _ = transfer edge (lower ⊔ upper) := (map_sup (transfer edge) lower upper).symm
    _ = transfer edge upper := by rw [sup_eq_right.mpr hlower]

/-- A sound assignment contains the evidence transported along every endorsement chain. -/
theorem chainEvidence_le_of_isSound (G : EdgeGraph V E)
    (transfer : (edge : E) →
      sSupHom (Set (Evidence (G.source edge))) (Set (Evidence (G.target edge))))
    (assignment : ∀ vertex, Set (Evidence vertex))
    (hsound : IsSoundAssignment G transfer assignment)
    {start finish : V} (walk : G.Walk start finish) :
    (evidenceTransport G transfer).walkMap walk (assignment start) ⊆
      assignment finish :=
  hsound.walkMap_le (evidenceTransport_edgeMap_monotone G transfer) walk

/-- Evidence included at a sound source remains included after transport along a chain. -/
theorem seedEvidence_le_along (G : EdgeGraph V E)
    (transfer : (edge : E) →
      sSupHom (Set (Evidence (G.source edge))) (Set (Evidence (G.target edge))))
    (assignment : ∀ vertex, Set (Evidence vertex))
    (hsound : IsSoundAssignment G transfer assignment)
    {start finish : V} (walk : G.Walk start finish)
    (seed : Set (Evidence start)) (hseed : seed ⊆ assignment start) :
    (evidenceTransport G transfer).walkMap walk seed ⊆ assignment finish := by
  let T := evidenceTransport G transfer
  have hmono := evidenceTransport_edgeMap_monotone G transfer
  exact (T.monotone_walkMap hmono walk hseed).trans
    (chainEvidence_le_of_isSound G transfer assignment hsound walk)

/-- The family of all evidence generated from seeds along typed endorsement chains. -/
def soundClosure (G : EdgeGraph V E)
    (transfer : (edge : E) →
      sSupHom (Set (Evidence (G.source edge))) (Set (Evidence (G.target edge))))
    (seed : ∀ vertex, Set (Evidence vertex)) : ∀ vertex, Set (Evidence vertex) :=
  (evidenceTransport G transfer).pathClosure seed

/-- An evidence record belongs to the sound closure exactly when some seed record transports to
it along a typed endorsement chain. -/
theorem mem_soundClosure_iff (G : EdgeGraph V E)
    (transfer : (edge : E) →
      sSupHom (Set (Evidence (G.source edge))) (Set (Evidence (G.target edge))))
    (seed : ∀ vertex, Set (Evidence vertex)) {vertex : V} {record : Evidence vertex} :
    record ∈ soundClosure G transfer seed vertex ↔
      ∃ source, ∃ walk : G.Walk source vertex,
        record ∈ (evidenceTransport G transfer).walkMap walk (seed source) := by
  simp [soundClosure, Transport.pathClosure]

/-- The sound closure is the least sound evidence assignment containing the seeds. -/
theorem soundClosure_isLeast (G : EdgeGraph V E)
    (transfer : (edge : E) →
      sSupHom (Set (Evidence (G.source edge))) (Set (Evidence (G.target edge))))
    (seed : ∀ vertex, Set (Evidence vertex)) :
    IsSoundAssignment G transfer (soundClosure G transfer seed) ∧
      (∀ vertex, seed vertex ⊆ soundClosure G transfer seed vertex) ∧
      ∀ assignment : ∀ vertex, Set (Evidence vertex),
        IsSoundAssignment G transfer assignment →
        (∀ vertex, seed vertex ⊆ assignment vertex) →
        ∀ vertex, soundClosure G transfer seed vertex ⊆ assignment vertex := by
  exact (evidenceTransport G transfer).pathClosure_isLeast_of_sSupHom transfer
    (fun _edge _evidence ↦ rfl) seed

end WebOfTrust

end
