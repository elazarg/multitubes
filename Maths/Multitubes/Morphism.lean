/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Closure

/-!
# Morphisms and simulations of transports

A morphism between two transports on the same edge graph is a fiberwise map
commuting with every edge map.  Edgewise commutation extends to every walk,
so morphisms carry exact sections to exact sections.  Monotone morphisms also
carry lax and oplax sections to sections of the same kind.

The two directed weakenings of commutation have different uses.  A lower
simulation satisfies `h (T.edgeMap edge point) ≤ S.edgeMap edge (h point)` and
carries oplax sections forward.  An upper simulation satisfies the reverse
inequality and carries lax sections forward.  If the target edge maps are
monotone, either edgewise inequality extends along every walk.

## Main definitions

* `Maths.Transport.Hom` - a fiberwise map commuting with edge transport.
* `Maths.Transport.LowerSimulation` - a fiberwise lower comparison of edge maps.
* `Maths.Transport.UpperSimulation` - a fiberwise upper comparison of edge maps.

## Main results

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
* `Maths.Transport.UpperSimulation.leastLaxMajorant_le_map` - global closure soundness.
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

/-- A fiberwise map intertwining the edge maps of two transports. -/
structure Hom (T : Transport G Fiber) (S : Transport G Other) where
  /-- The map on the fiber over each vertex. -/
  app : (vertex : V) → Fiber vertex → Other vertex
  /-- The fiber maps commute with transport along each edge. -/
  naturality : ∀ (edge : E) (point : Fiber (G.source edge)),
    app (G.target edge) (T.edgeMap edge point) =
      S.edgeMap edge (app (G.source edge) point)

namespace Hom

/-- The identity morphism of a transport. -/
def id (T : Transport G Fiber) : Hom T T where
  app _ := fun point => point
  naturality _ _ := rfl

/-- The composite of two transport morphisms. -/
def comp (g : Hom S R) (f : Hom T S) : Hom T R where
  app vertex := g.app vertex ∘ f.app vertex
  naturality edge point := by
    rw [Function.comp_apply, f.naturality, Function.comp_apply, g.naturality]

/-- Two transport morphisms are equal when all their fiber maps agree. -/
@[ext] theorem ext {f g : Hom T S} (happ : ∀ vertex point,
    f.app vertex point = g.app vertex point) : f = g := by
  cases f with
  | mk fapp fnaturality =>
      cases g with
      | mk gapp gnaturality =>
          simp only [mk.injEq]
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

/-- A fiberwise map commutes with casts of its vertex index. -/
theorem app_fiberCast (f : Hom T S) {first second : V} (hvertex : first = second)
    (point : Fiber first) :
    f.app second (fiberCast Fiber hvertex point) =
      fiberCast Other hvertex (f.app first point) := by
  subst hvertex
  rfl

/-- A transport morphism intertwines transport along every walk. -/
theorem walkMap_naturality (f : Hom T S) {start finish : V}
    (walk : G.Walk start finish) (point : Fiber start) :
    f.app finish (T.walkMap walk point) =
      S.walkMap walk (f.app start point) := by
  induction walk with
  | nil => rfl
  | concat walk edge legal ih =>
      rw [Transport.walkMap_concat, Transport.walkMap_concat, f.naturality]
      rw [f.app_fiberCast, ih]

/-- A transport morphism intertwines the holonomy of every closed walk. -/
theorem holonomy_naturality (f : Hom T S) {base : V} (cycle : G.Walk base base)
    (point : Fiber base) :
    f.app base (T.holonomy cycle point) = S.holonomy cycle (f.app base point) :=
  f.walkMap_naturality cycle point

/-- Apply a transport morphism to a vertex-indexed family. -/
def mapFamily (f : Hom T S) (family : ∀ vertex, Fiber vertex) :
    ∀ vertex, Other vertex :=
  fun vertex => f.app vertex (family vertex)

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

section Lower

variable [∀ vertex : V, Preorder (Other vertex)]

/-- A fiberwise comparison satisfying
`h (T.edgeMap edge point) ≤ S.edgeMap edge (h point)` on every edge. -/
structure LowerSimulation (T : Transport G Fiber) (S : Transport G Other) where
  /-- The map on the fiber over each vertex. -/
  app : (vertex : V) → Fiber vertex → Other vertex
  /-- Transport in the source, followed by comparison, is below transport in the target. -/
  edge_le : ∀ (edge : E) (point : Fiber (G.source edge)),
    app (G.target edge) (T.edgeMap edge point) ≤
      S.edgeMap edge (app (G.source edge) point)

namespace LowerSimulation

/-- Apply a lower simulation to a vertex-indexed family. -/
def mapFamily (f : LowerSimulation T S) (family : ∀ vertex, Fiber vertex) :
    ∀ vertex, Other vertex :=
  fun vertex => f.app vertex (family vertex)

/-- A lower simulation commutes with casts of its vertex index. -/
theorem app_fiberCast (f : LowerSimulation T S) {first second : V}
    (hvertex : first = second) (point : Fiber first) :
    f.app second (fiberCast Fiber hvertex point) =
      fiberCast Other hvertex (f.app first point) := by
  subst hvertex
  rfl

section Ordered

/-- A lower simulation extends from edges to walks when target edge maps are monotone. -/
theorem walkMap_le (f : LowerSimulation T S)
    (hmono : ∀ edge : E, Monotone (S.edgeMap edge))
    {start finish : V} (walk : G.Walk start finish) (point : Fiber start) :
    f.app finish (T.walkMap walk point) ≤ S.walkMap walk (f.app start point) := by
  induction walk with
  | nil => exact le_rfl
  | concat walk edge legal ih =>
      rw [Transport.walkMap_concat, Transport.walkMap_concat]
      refine le_trans (f.edge_le edge _) (hmono edge ?_)
      rw [f.app_fiberCast]
      exact fiberCast_le_fiberCast legal.symm ih

variable [∀ vertex : V, Preorder (Fiber vertex)]

/-- A monotone lower simulation carries oplax sections to oplax sections. -/
theorem map_isOplaxSection (f : LowerSimulation T S)
    (hmono : ∀ vertex, Monotone (f.app vertex))
    {family : ∀ vertex, Fiber vertex} (hfamily : T.IsOplaxSection family) :
    S.IsOplaxSection (f.mapFamily family) := by
  intro edge
  exact le_trans (hmono _ (hfamily edge)) (f.edge_le edge _)

end Ordered

end LowerSimulation

end Lower

section Upper

variable [∀ vertex : V, Preorder (Other vertex)]

/-- A fiberwise comparison satisfying
`S.edgeMap edge (h point) ≤ h (T.edgeMap edge point)` on every edge. -/
structure UpperSimulation (T : Transport G Fiber) (S : Transport G Other) where
  /-- The map on the fiber over each vertex. -/
  app : (vertex : V) → Fiber vertex → Other vertex
  /-- Transport in the target is below source transport followed by comparison. -/
  edge_le : ∀ (edge : E) (point : Fiber (G.source edge)),
    S.edgeMap edge (app (G.source edge) point) ≤
      app (G.target edge) (T.edgeMap edge point)

namespace UpperSimulation

/-- Apply an upper simulation to a vertex-indexed family. -/
def mapFamily (f : UpperSimulation T S) (family : ∀ vertex, Fiber vertex) :
    ∀ vertex, Other vertex :=
  fun vertex => f.app vertex (family vertex)

/-- An upper simulation commutes with casts of its vertex index. -/
theorem app_fiberCast (f : UpperSimulation T S) {first second : V}
    (hvertex : first = second) (point : Fiber first) :
    f.app second (fiberCast Fiber hvertex point) =
      fiberCast Other hvertex (f.app first point) := by
  subst hvertex
  rfl

section Ordered

/-- An upper simulation extends from edges to walks when target edge maps are monotone. -/
theorem walkMap_le (f : UpperSimulation T S)
    (hmono : ∀ edge : E, Monotone (S.edgeMap edge))
    {start finish : V} (walk : G.Walk start finish) (point : Fiber start) :
    S.walkMap walk (f.app start point) ≤ f.app finish (T.walkMap walk point) := by
  induction walk with
  | nil => exact le_rfl
  | concat walk edge legal ih =>
      rw [Transport.walkMap_concat, Transport.walkMap_concat]
      refine le_trans (hmono edge ?_) (f.edge_le edge _)
      rw [f.app_fiberCast]
      exact fiberCast_le_fiberCast legal.symm ih

variable [∀ vertex : V, Preorder (Fiber vertex)]

/-- A monotone upper simulation carries lax sections to lax sections. -/
theorem map_isLaxSection (f : UpperSimulation T S)
    (hmono : ∀ vertex, Monotone (f.app vertex))
    {family : ∀ vertex, Fiber vertex} (hfamily : T.IsLaxSection family) :
    S.IsLaxSection (f.mapFamily family) := by
  intro edge
  exact le_trans (f.edge_le edge _) (hmono _ (hfamily edge))

end Ordered

end UpperSimulation


end Upper

section HomSimulations

variable [∀ vertex : V, Preorder (Other vertex)]

namespace Hom

/-- An exact transport morphism is a lower simulation. -/
def toLowerSimulation (f : Hom T S) : LowerSimulation T S where
  app := f.app
  edge_le edge point := (f.naturality edge point).le

/-- An exact transport morphism is an upper simulation. -/
def toUpperSimulation (f : Hom T S) : UpperSimulation T S where
  app := f.app
  edge_le edge point := (f.naturality edge point).ge

/-- The lower simulation underlying a morphism has the same fiber maps. -/
@[simp] theorem toLowerSimulation_app (f : Hom T S) (vertex : V) (point : Fiber vertex) :
    f.toLowerSimulation.app vertex point = f.app vertex point := rfl

/-- The upper simulation underlying a morphism has the same fiber maps. -/
@[simp] theorem toUpperSimulation_app (f : Hom T S) (vertex : V) (point : Fiber vertex) :
    f.toUpperSimulation.app vertex point = f.app vertex point := rfl

end Hom

end HomSimulations

section UpperClosure

variable [∀ vertex : V, CompleteLattice (Fiber vertex)]
variable [∀ vertex : V, CompleteLattice (Other vertex)]

namespace UpperSimulation

/-- Concrete closure is bounded by the concretization of abstract closure.

Here `T` is the abstract transport, `S` is the concrete transport, and `f` is
concretization.  The edge inequality of an upper simulation is the local
soundness condition; leastness of concrete closure turns it into the global
comparison. -/
theorem leastLaxMajorant_le_map (f : UpperSimulation T S)
    (hfmono : ∀ vertex, Monotone (f.app vertex))
    (hTmono : ∀ edge : E, Monotone (T.edgeMap edge))
    (hSmono : ∀ edge : E, Monotone (S.edgeMap edge))
    (lowerT : ∀ vertex, Fiber vertex) (lowerS : ∀ vertex, Other vertex)
    (hlower : ∀ vertex, lowerS vertex ≤ f.app vertex (lowerT vertex)) :
    S.leastLaxMajorant hSmono lowerS ≤
      f.mapFamily (T.leastLaxMajorant hTmono lowerT) := by
  apply (S.leastLaxMajorant_isLeast hSmono lowerS).2.2
  · intro vertex
    exact (hlower vertex).trans <| hfmono vertex
      ((T.leastLaxMajorant_isLeast hTmono lowerT).1 vertex)
  · exact f.map_isLaxSection hfmono
      (T.leastLaxMajorant_isLeast hTmono lowerT).2.1

end UpperSimulation

end UpperClosure

end Transport

end Maths
