/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Basic

/-!
# Morphisms and simulations of transports

A morphism between two transports on the same edge graph is a fiberwise map
commuting with every edge map.  Edgewise commutation extends to every walk,
so morphisms carry exact sections to exact sections.  Monotone morphisms also
carry lax and oplax sections to sections of the same kind.

A simulation weakens commutation to a fiberwise relation between mapping after
transport and transport after mapping.  If the relation is reflexive, transitive,
and preserved by the target edge maps, the edgewise comparison extends along every
walk; commutation along walks is the case of equality.  The two order-theoretic
cases have different uses.  A lower simulation satisfies
`h (T.edgeMap edge point) ≤ S.edgeMap edge (h point)` and carries oplax sections
forward.  An upper simulation satisfies the reverse inequality and carries lax
sections forward.

## Main definitions

* `Maths.Transport.Simulation` - a fiberwise map comparing edge maps through a relation.
* `Maths.Transport.Hom` - a fiberwise map commuting with edge transport: the simulation for
  equality.
* `Maths.Transport.LowerSimulation` and `Maths.Transport.UpperSimulation` - the
  simulations for `≤` and `≥`.

## Main results

* `Maths.Transport.Simulation.walkMap_rel` - edgewise comparison extends along walks.
* `Maths.Transport.Hom.walkMap_naturality` - commutation extends along walks.
* `Maths.Transport.Hom.ext`, `Maths.Transport.Hom.id_comp`,
  `Maths.Transport.Hom.comp_id`, and `Maths.Transport.Hom.comp_assoc` - extensionality and
  composition laws.
* `Maths.Transport.Hom.map_isSection` - morphisms carry exact sections forward.
* `Maths.Transport.Hom.map_isLaxSection` and
  `Maths.Transport.Hom.map_isOplaxSection` - monotone morphisms preserve ordered sections.
* `Maths.Transport.LowerSimulation.walkMap_le` and
  `Maths.Transport.UpperSimulation.walkMap_le` - simulations extend along walks.
* `Maths.Transport.LowerSimulation.map_isOplaxSection` and
  `Maths.Transport.UpperSimulation.map_isLaxSection` - directed section preservation.
-/

@[expose] public section

namespace Maths

universe uV uE uF uH uK uL

variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E}
variable {Fiber : V → Type uF} {Other : V → Type uH} {Third : V → Type uK}
variable {Fourth : V → Type uL}

namespace Transport

variable {T : Transport G Fiber} {S : Transport G Other} {R : Transport G Third}
variable {Q : Transport G Fourth}

/-! ### Simulations -/

/-- A fiberwise map comparing the edge maps of two transports through a fiberwise relation on
the second: along every edge, mapping after transport in `T` is `relation`-related to transport
in `S` after mapping.  A morphism, `Maths.Transport.Hom`, gives the case of equality; lower
and upper simulations are the cases `≤` and `≥`. -/
structure Simulation (T : Transport G Fiber) (S : Transport G Other)
    (relation : ∀ vertex, Other vertex → Other vertex → Prop) where
  /-- The map on the fiber over each vertex. -/
  app : (vertex : V) → Fiber vertex → Other vertex
  /-- The edgewise comparison of the two transports. -/
  edge_rel : ∀ (edge : E) (point : Fiber (G.source edge)),
    relation (G.target edge) (app (G.target edge) (T.edgeMap edge point))
      (S.edgeMap edge (app (G.source edge) point))

namespace Simulation

variable {relation : ∀ vertex, Other vertex → Other vertex → Prop}

/-- Apply a simulation to a vertex-indexed family. -/
def mapFamily (f : Simulation T S relation) (family : ∀ vertex, Fiber vertex) :
    ∀ vertex, Other vertex :=
  fun vertex => f.app vertex (family vertex)

/-- A simulation extends from edges to walks when its relation is reflexive and transitive and
preserved by the edge maps of `S`. -/
theorem walkMap_rel (f : Simulation T S relation)
    (hrefl : ∀ vertex x, relation vertex x x)
    (htrans : ∀ vertex {x y z}, relation vertex x y → relation vertex y z → relation vertex x z)
    (hpreserve : ∀ edge {x y}, relation (G.source edge) x y →
      relation (G.target edge) (S.edgeMap edge x) (S.edgeMap edge y))
    {start finish : V} (walk : G.Walk start finish) (point : Fiber start) :
    relation finish (f.app finish (T.walkMap walk point)) (S.walkMap walk (f.app start point)) := by
  induction walk with
  | nil => exact hrefl _ _
  | concat edge walk ih =>
      exact htrans _ (f.edge_rel edge _) (hpreserve edge ih)

end Simulation

/-- A fiberwise map intertwining the edge maps of two transports: a simulation for equality.
Its edge comparison is `Maths.Transport.Hom.naturality`. -/
abbrev Hom (T : Transport G Fiber) (S : Transport G Other) :=
  Simulation T S fun _ => Eq

namespace Hom

/-- The fiber maps of a morphism commute with transport along each edge. -/
theorem naturality (f : Hom T S) (edge : E) (point : Fiber (G.source edge)) :
    f.app (G.target edge) (T.edgeMap edge point) = S.edgeMap edge (f.app (G.source edge) point) :=
  f.edge_rel edge point

/-- The identity morphism of a transport. -/
def id (T : Transport G Fiber) : Hom T T where
  app _ := fun point => point
  edge_rel _ _ := rfl

/-- The composite of two transport morphisms. -/
def comp (g : Hom S R) (f : Hom T S) : Hom T R where
  app vertex := g.app vertex ∘ f.app vertex
  edge_rel edge point := by
    rw [Function.comp_apply, f.naturality, Function.comp_apply, g.naturality]

/-- Two transport morphisms are equal when all their fiber maps agree. -/
@[ext] theorem ext {f g : Hom T S} (happ : ∀ vertex point,
    f.app vertex point = g.app vertex point) : f = g := by
  obtain ⟨fapp, _⟩ := f
  obtain ⟨gapp, _⟩ := g
  congr
  funext vertex point
  exact happ vertex point

/-- Left composition by the identity morphism changes nothing. -/
@[simp] theorem id_comp (f : Hom T S) : (id S).comp f = f := by
  ext vertex point
  rfl

/-- Right composition by the identity morphism changes nothing. -/
@[simp] theorem comp_id (f : Hom T S) : f.comp (id T) = f := by
  ext vertex point
  rfl

/-- Composition of transport morphisms is associative. -/
@[simp] theorem comp_assoc (h : Hom R Q) (g : Hom S R) (f : Hom T S) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext vertex point
  rfl

/-- The identity morphism acts as the identity on every fiber. -/
@[simp] theorem id_app (vertex : V) (point : Fiber vertex) :
    (id T).app vertex point = point := rfl

/-- Composition of transport morphisms is pointwise composition. -/
@[simp] theorem comp_app (g : Hom S R) (f : Hom T S) (vertex : V)
    (point : Fiber vertex) :
    (g.comp f).app vertex point = g.app vertex (f.app vertex point) := rfl

/-- A transport morphism intertwines transport along every walk. -/
theorem walkMap_naturality (f : Hom T S) {start finish : V}
    (walk : G.Walk start finish) (point : Fiber start) :
    f.app finish (T.walkMap walk point) =
      S.walkMap walk (f.app start point) :=
  Simulation.walkMap_rel f (fun _ _ => rfl) (fun _ => Eq.trans) (fun _ => congrArg _) walk point

/-- A transport morphism intertwines the holonomy of every closed walk. -/
theorem holonomy_naturality (f : Hom T S) {base : V} (cycle : G.Walk base base)
    (point : Fiber base) :
    f.app base (T.holonomy cycle point) = S.holonomy cycle (f.app base point) :=
  f.walkMap_naturality cycle point

/-- A transport morphism carries exact sections to exact sections. -/
theorem map_isSection (f : Hom T S) {family : ∀ vertex, Fiber vertex}
    (hfamily : T.IsSection family) : S.IsSection (f.mapFamily family) := by
  intro edge
  change S.edgeMap edge (f.app _ _) = f.app _ _
  rw [← f.naturality, hfamily edge]

section Ordered

variable [∀ vertex : V, Preorder (Fiber vertex)]
variable [∀ vertex : V, Preorder (Other vertex)]

/-- A monotone transport morphism carries lax sections to lax sections. -/
theorem map_isLaxSection (f : Hom T S)
    (hmono : ∀ vertex, Monotone (f.app vertex))
    {family : ∀ vertex, Fiber vertex} (hfamily : T.IsLaxSection family) :
    S.IsLaxSection (f.mapFamily family) := by
  intro edge
  change S.edgeMap edge (f.app _ _) ≤ f.app _ _
  rw [← f.naturality]
  exact hmono _ (hfamily edge)

/-- A monotone transport morphism carries oplax sections to oplax sections. -/
theorem map_isOplaxSection (f : Hom T S)
    (hmono : ∀ vertex, Monotone (f.app vertex))
    {family : ∀ vertex, Fiber vertex} (hfamily : T.IsOplaxSection family) :
    S.IsOplaxSection (f.mapFamily family) := by
  intro edge
  change f.app _ _ ≤ S.edgeMap edge (f.app _ _)
  rw [← f.naturality]
  exact hmono _ (hfamily edge)

end Ordered

end Hom

section Ordered

variable [∀ vertex : V, Preorder (Other vertex)]

/-- A fiberwise comparison satisfying
`h (T.edgeMap edge point) ≤ S.edgeMap edge (h point)` on every edge. -/
abbrev LowerSimulation (T : Transport G Fiber) (S : Transport G Other) :=
  Simulation T S fun _ => (· ≤ ·)

/-- A fiberwise comparison satisfying
`S.edgeMap edge (h point) ≤ h (T.edgeMap edge point)` on every edge. -/
abbrev UpperSimulation (T : Transport G Fiber) (S : Transport G Other) :=
  Simulation T S fun _ => (· ≥ ·)

/-- A lower simulation extends from edges to walks when the edge maps of `S` are monotone. -/
theorem LowerSimulation.walkMap_le (f : LowerSimulation T S)
    (hmono : ∀ edge : E, Monotone (S.edgeMap edge))
    {start finish : V} (walk : G.Walk start finish) (point : Fiber start) :
    f.app finish (T.walkMap walk point) ≤ S.walkMap walk (f.app start point) :=
  Simulation.walkMap_rel f (fun _ => le_refl) (fun _ => le_trans)
    (fun edge _ _ hxy => hmono edge hxy) walk point

/-- An upper simulation extends from edges to walks when the edge maps of `S` are monotone. -/
theorem UpperSimulation.walkMap_le (f : UpperSimulation T S)
    (hmono : ∀ edge : E, Monotone (S.edgeMap edge))
    {start finish : V} (walk : G.Walk start finish) (point : Fiber start) :
    S.walkMap walk (f.app start point) ≤ f.app finish (T.walkMap walk point) :=
  Simulation.walkMap_rel f (fun _ => le_refl) (fun _ _ _ _ hxy hyz => le_trans hyz hxy)
    (fun edge _ _ hxy => hmono edge hxy) walk point

variable [∀ vertex : V, Preorder (Fiber vertex)]

/-- A monotone lower simulation carries oplax sections to oplax sections. -/
theorem LowerSimulation.map_isOplaxSection (f : LowerSimulation T S)
    (hmono : ∀ vertex, Monotone (f.app vertex))
    {family : ∀ vertex, Fiber vertex} (hfamily : T.IsOplaxSection family) :
    S.IsOplaxSection (f.mapFamily family) :=
  fun edge => le_trans (hmono _ (hfamily edge)) (f.edge_rel edge _)

/-- A monotone upper simulation carries lax sections to lax sections. -/
theorem UpperSimulation.map_isLaxSection (f : UpperSimulation T S)
    (hmono : ∀ vertex, Monotone (f.app vertex))
    {family : ∀ vertex, Fiber vertex} (hfamily : T.IsLaxSection family) :
    S.IsLaxSection (f.mapFamily family) :=
  fun edge => le_trans (f.edge_rel edge _) (hmono _ (hfamily edge))

end Ordered

end Transport

end Maths
