/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Maths.Multitubes.Basic

/-!
# Morphisms and lax morphisms of transports

A relational morphism, `Maths.Transport.HomFor`, compares the edge maps of two transports through a
relation; a section is a relational morphism out of the terminal transport.  This file composes
relational morphisms and specializes them to three relations.

* A **morphism** commutes with every edge map: the case of equality.
* A **lax morphism** satisfies `S.edgeMap edge (h point) ≤ h (T.edgeMap edge point)`, the
  inequality a lax section satisfies; in abstract interpretation it is the soundness condition of
  a concretization.
* An **oplax morphism** satisfies the reverse inequality.

Edgewise comparison extends along every walk, and composing with a section gives a section, so
morphisms carry exact sections forward and monotone lax and oplax morphisms carry lax and oplax
sections forward.

## Main definitions

* `Maths.Transport.HomFor.comp` - the composite of two relational morphisms.
* `Maths.Transport.Hom` - a fiberwise map commuting with edge transport.
* `Maths.Transport.LaxHom` and `Maths.Transport.OplaxHom` - the relational morphisms for `≤` and
  `≥`.
* `Maths.Transport.Hom.toLaxHom` and `Maths.Transport.Hom.toOplaxHom` - a morphism is both.

## Main results

* `Maths.Transport.Hom.walkMap_naturality` - commutation extends along walks.
* `Maths.Transport.Hom.ext`, `Maths.Transport.Hom.id_comp`,
  `Maths.Transport.Hom.comp_id`, and `Maths.Transport.Hom.comp_assoc` - extensionality and
  composition laws.
* `Maths.Transport.HomFor.map_isSectionFor` - a relational morphism carries sections forward.
* `Maths.Transport.Hom.map_isSection` - morphisms carry exact sections forward.
* `Maths.Transport.Hom.map_isLaxSection` and
  `Maths.Transport.Hom.map_isOplaxSection` - monotone morphisms preserve ordered sections.
* `Maths.Transport.LaxHom.walkMap_le` and `Maths.Transport.OplaxHom.le_walkMap` - lax and oplax
  morphisms extend along walks.
* `Maths.Transport.LaxHom.map_isLaxSection` and `Maths.Transport.OplaxHom.map_isOplaxSection` -
  directed section preservation.
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

/-! ### Composition of relational morphisms -/

namespace HomFor

variable {relation : ∀ edge : E, Other (G.target edge) → Other (G.target edge) → Prop}
variable {relation' : ∀ edge : E, Third (G.target edge) → Third (G.target edge) → Prop}

/-- The composite of two relational morphisms, when the second carries the comparison relation of
the first into its own, and its own relation is transitive. -/
def comp (g : HomFor S R relation') (f : HomFor T S relation)
    (hmap : ∀ edge {x y}, relation edge x y →
      relation' edge (g.app (G.target edge) x) (g.app (G.target edge) y))
    (htrans : ∀ edge {x y z}, relation' edge x y → relation' edge y z → relation' edge x z) :
    HomFor T R relation' where
  app vertex := g.app vertex ∘ f.app vertex
  edge_rel edge point := htrans edge (g.edge_rel edge _) (hmap edge (f.edge_rel edge point))

/-- **Relational morphisms carry sections forward.**  Composing a section, a relational morphism out
of the terminal transport, with a relational morphism gives a section. -/
theorem map_isSectionFor (g : HomFor T S relation)
    {sectionRelation : ∀ edge : E, Fiber (G.target edge) → Fiber (G.target edge) → Prop}
    (hmap : ∀ edge {x y}, sectionRelation edge x y →
      relation edge (g.app (G.target edge) x) (g.app (G.target edge) y))
    (htrans : ∀ edge {x y z}, relation edge x y → relation edge y z → relation edge x z)
    {family : ∀ vertex, Fiber vertex} (hfamily : T.IsSectionFor sectionRelation family) :
    S.IsSectionFor relation (g.mapFamily family) :=
  (g.comp hfamily.toHomFor hmap htrans).isSectionFor

end HomFor

/-! ### Morphisms -/

/-- A fiberwise map intertwining the edge maps of two transports: a relational morphism for
equality.  Its edge comparison is `Maths.Transport.Hom.naturality`. -/
abbrev Hom (T : Transport G Fiber) (S : Transport G Other) :=
  HomFor T S fun _ => Eq

namespace Hom

/-- The fiber maps of a morphism commute with transport along each edge. -/
theorem naturality (f : Hom T S) (edge : E) (point : Fiber (G.source edge)) :
    f.app (G.target edge) (T.edgeMap edge point) = S.edgeMap edge (f.app (G.source edge) point) :=
  (f.edge_rel edge point).symm

/-- The identity morphism of a transport. -/
def id (T : Transport G Fiber) : Hom T T where
  app _ := fun point => point
  edge_rel _ _ := rfl

/-- The composite of two transport morphisms. -/
def comp (g : Hom S R) (f : Hom T S) : Hom T R :=
  HomFor.comp g f (fun _ _ _ => congrArg _) fun _ => Eq.trans

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
  (HomFor.walkMap_rel f (R := fun _ => Eq) (fun _ _ => rfl) (fun _ => Eq.trans)
    (fun _ => congrArg _) (fun _ _ _ => _root_.id) walk point).symm

/-- A transport morphism intertwines the holonomy of every closed walk. -/
theorem holonomy_naturality (f : Hom T S) {base : V} (cycle : G.Walk base base)
    (point : Fiber base) :
    f.app base (T.holonomy cycle point) = S.holonomy cycle (f.app base point) :=
  f.walkMap_naturality cycle point

/-- A transport morphism carries exact sections to exact sections. -/
theorem map_isSection (f : Hom T S) {family : ∀ vertex, Fiber vertex}
    (hfamily : T.IsSection family) : S.IsSection (f.mapFamily family) :=
  HomFor.map_isSectionFor f (fun _ _ _ => congrArg _) (fun _ => Eq.trans) hfamily

end Hom

/-! ### Lax and oplax morphisms -/

section Ordered

variable [∀ vertex : V, Preorder (Other vertex)]

/-- A fiberwise map satisfying `S.edgeMap edge (h point) ≤ h (T.edgeMap edge point)` on every edge:
the relational morphism for `≤`.  A lax section is a lax morphism out of the terminal transport. -/
abbrev LaxHom (T : Transport G Fiber) (S : Transport G Other) :=
  HomFor T S fun _ => (· ≤ ·)

/-- A fiberwise map satisfying `h (T.edgeMap edge point) ≤ S.edgeMap edge (h point)` on every
edge: the relational morphism for `≥`.  An oplax section is an oplax morphism out of the terminal
transport. -/
abbrev OplaxHom (T : Transport G Fiber) (S : Transport G Other) :=
  HomFor T S fun _ => (· ≥ ·)

/-- A morphism is a lax morphism. -/
def Hom.toLaxHom (f : Hom T S) : LaxHom T S :=
  f.mono fun _ _ _ h => h.le

/-- A morphism is an oplax morphism. -/
def Hom.toOplaxHom (f : Hom T S) : OplaxHom T S :=
  f.mono fun _ _ _ h => h.ge

/-- A lax morphism extends from edges to walks when the edge maps of `S` are monotone. -/
theorem LaxHom.walkMap_le (f : LaxHom T S) (hmono : S.IsMonotone)
    {start finish : V} (walk : G.Walk start finish) (point : Fiber start) :
    S.walkMap walk (f.app start point) ≤ f.app finish (T.walkMap walk point) :=
  HomFor.walkMap_rel f (fun _ _ => le_rfl) (fun _ => le_trans)
    (fun edge _ _ hxy => hmono edge hxy) (fun _ _ _ => _root_.id) walk point

/-- An oplax morphism extends from edges to walks when the edge maps of `S` are monotone. -/
theorem OplaxHom.le_walkMap (f : OplaxHom T S) (hmono : S.IsMonotone)
    {start finish : V} (walk : G.Walk start finish) (point : Fiber start) :
    f.app finish (T.walkMap walk point) ≤ S.walkMap walk (f.app start point) :=
  HomFor.walkMap_rel f (R := fun _ => (· ≥ ·)) (fun _ _ => le_rfl)
    (fun _ _ _ _ hxy hyz => le_trans hyz hxy) (fun edge _ _ hxy => hmono edge hxy)
    (fun _ _ _ => _root_.id) walk point

variable [∀ vertex : V, Preorder (Fiber vertex)]

/-- A monotone lax morphism carries lax sections to lax sections. -/
theorem LaxHom.map_isLaxSection (f : LaxHom T S) (hmono : ∀ vertex, Monotone (f.app vertex))
    {family : ∀ vertex, Fiber vertex} (hfamily : T.IsLaxSection family) :
    S.IsLaxSection (f.mapFamily family) :=
  HomFor.map_isSectionFor f (fun _ _ _ hxy => hmono _ hxy) (fun _ => le_trans) hfamily

/-- A monotone oplax morphism carries oplax sections to oplax sections. -/
theorem OplaxHom.map_isOplaxSection (f : OplaxHom T S) (hmono : ∀ vertex, Monotone (f.app vertex))
    {family : ∀ vertex, Fiber vertex} (hfamily : T.IsOplaxSection family) :
    S.IsOplaxSection (f.mapFamily family) :=
  HomFor.map_isSectionFor f (sectionRelation := fun _ => (· ≥ ·))
    (fun _ _ _ hxy => hmono _ hxy) (fun _ _ _ _ hxy hyz => le_trans hyz hxy) hfamily

/-- A monotone transport morphism carries lax sections to lax sections. -/
theorem Hom.map_isLaxSection (f : Hom T S) (hmono : ∀ vertex, Monotone (f.app vertex))
    {family : ∀ vertex, Fiber vertex} (hfamily : T.IsLaxSection family) :
    S.IsLaxSection (f.mapFamily family) :=
  f.toLaxHom.map_isLaxSection hmono hfamily

/-- A monotone transport morphism carries oplax sections to oplax sections. -/
theorem Hom.map_isOplaxSection (f : Hom T S) (hmono : ∀ vertex, Monotone (f.app vertex))
    {family : ∀ vertex, Fiber vertex} (hfamily : T.IsOplaxSection family) :
    S.IsOplaxSection (f.mapFamily family) :=
  f.toOplaxHom.map_isOplaxSection hmono hfamily

end Ordered

end Transport

end Maths
