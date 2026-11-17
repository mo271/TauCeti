/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Quotient
public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
public import TauCeti.Topology.Category.BasedTopologicalSpace
public import TauCeti.Topology.Homotopy.Extension.HomotopyEquivRel
public import TauCeti.Topology.Homotopy.HomotopyGroup.Homotopy
public import TauCeti.Topology.Homotopy.Homotopic.Rel

/-!
# The pointed homotopy category

The pointed homotopy category `TauCeti.PointedHomotopyCat` has the based topological spaces as
objects, and as morphisms the pointed homotopy classes of base-point-preserving continuous maps:
two based maps are identified when they are homotopic relative to the base point of the source.
It is the quotient of the category `TauCeti.BasedTopologicalSpace` by the congruence
`TauCeti.BasedTopologicalSpace.homotopicRel`, built with Mathlib's `CategoryTheory.Quotient`, so a
functor into based spaces that is defined strictly descends to the pointed homotopy category by
composing with `TauCeti.PointedHomotopyCat.quotient`.

Pointed-homotopic maps induce the same homomorphism of fundamental groups, so the fundamental
group at the base point is a functor `TauCeti.PointedHomotopyCat.fundamentalGroupFunctor` on the
pointed homotopy category. It factors the fundamental-group functor
`TauCeti.BasedTopologicalSpace.fundamentalGroupFunctor` of based spaces through the quotient.

When the base points of two spaces have the homotopy extension property, a pointed map whose
underlying continuous map is a homotopy equivalence has a based homotopy inverse with both
homotopies relative to the base points
(`TauCeti.HasHomotopyExtensionProperty.exists_basedInverse_homotopicRel`), so it descends to an
isomorphism in `TauCeti.PointedHomotopyCat` (`TauCeti.PointedHomotopyCat.isoOfHomotopyEquiv`,
`TauCeti.PointedHomotopyCat.isIso_quotient_map_of_homotopyEquiv`). Conversely, every isomorphism
in `TauCeti.PointedHomotopyCat` yields a homotopy equivalence of underlying spaces whose forward
and inverse maps preserve the base points (`TauCeti.PointedHomotopyCat.homotopyEquivOfIso`).

## Main definitions

* `TauCeti.BasedTopologicalSpace.homotopicRel`: pointed homotopy, as a congruence on based maps.
* `TauCeti.PointedHomotopyCat`: the pointed homotopy category.
* `TauCeti.PointedHomotopyCat.quotient`: the quotient functor from based spaces.
* `TauCeti.BasedTopologicalSpace.fundamentalGroupFunctor`: the fundamental group at the base
  point, as a functor on based spaces.
* `TauCeti.PointedHomotopyCat.fundamentalGroupFunctor`: the induced functor on the pointed
  homotopy category.
* `TauCeti.PointedHomotopyCat.isoOfHomotopyEquiv`: an isomorphism in the pointed homotopy category
  from a base-point-preserving homotopy equivalence between well-pointed spaces.
* `TauCeti.PointedHomotopyCat.homotopyEquivOfIso`: a homotopy equivalence of underlying spaces
  extracted from an isomorphism in the pointed homotopy category.

## Main results

* `TauCeti.PointedHomotopyCat.quotient_map_eq_iff`: two based maps have the same class exactly
  when they are homotopic relative to the base point.
* `TauCeti.PointedHomotopyCat.quotient_comp_fundamentalGroupFunctor`: the fundamental group of
  based spaces factors through the pointed homotopy category.
* `TauCeti.PointedHomotopyCat.isIso_quotient_map_of_homotopyEquiv`: a based map between
  well-pointed spaces that is an underlying homotopy equivalence induces an isomorphism in the
  pointed homotopy category.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0 and Section 1.1.
-/

public section

noncomputable section

universe u

open CategoryTheory

namespace TauCeti

namespace BasedTopologicalSpace

/-- **Pointed homotopy** of based maps: two morphisms `f g : X ⟶ Y` of based spaces are related
when their underlying continuous maps are homotopic relative to the base point of `X`. -/
def homotopicRel : HomRel BasedTopologicalSpace.{u} := fun X _ f g ↦
  f.toContinuousMap.HomotopicRel g.toContinuousMap {X.basepoint}

theorem homotopicRel_iff {X Y : BasedTopologicalSpace.{u}} {f g : X ⟶ Y} :
    homotopicRel f g ↔ f.toContinuousMap.HomotopicRel g.toContinuousMap {X.basepoint} :=
  Iff.rfl

instance : Congruence homotopicRel.{u} where
  equivalence := ⟨fun f ↦ .refl f.toContinuousMap, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩
  comp_left f g g' h := by
    simp only [homotopicRel_iff, comp_eq_hom_comp, Hom.toContinuousMap_comp]
    -- Precomposing with `f` gives a homotopy relative to `f ⁻¹' {basepoint}`, which contains the
    -- base point of the source.
    exact (h.precomp f.toContinuousMap).mono (by simp)
  comp_right g h := by
    simp only [homotopicRel_iff, comp_eq_hom_comp, Hom.toContinuousMap_comp]
    exact h.comp_continuousMap g.toContinuousMap

/-- **The fundamental group at the base point**, as a functor from based spaces to groups. A based
map induces `FundamentalGroup.mapOfEq` along its base-point equation. -/
@[expose] def fundamentalGroupFunctor : BasedTopologicalSpace.{u} ⥤ GrpCat.{u} where
  obj X := GrpCat.of (FundamentalGroup X.carrier X.basepoint)
  map f := GrpCat.ofHom (FundamentalGroup.mapOfEq f.toContinuousMap f.map_basepoint)
  map_id X := by
    refine GrpCat.hom_ext (MonoidHom.ext fun a ↦ ?_)
    rw [GrpCat.hom_ofHom, GrpCat.hom_id, MonoidHom.id_apply]
    exact (FundamentalGroup.mapOfEq_congr (Hom.toContinuousMap_id X) _ rfl a).trans
      (FundamentalGroup.mapOfEq_id rfl a)
  map_comp f g := by
    refine GrpCat.hom_ext (MonoidHom.ext fun a ↦ ?_)
    simp only [GrpCat.hom_comp, MonoidHom.comp_apply, GrpCat.hom_ofHom]
    exact (FundamentalGroup.mapOfEq_congr (Hom.toContinuousMap_comp g f) _ _ a).trans
      (FundamentalGroup.mapOfEq_comp _ _ _ _ a).symm

@[simp]
theorem fundamentalGroupFunctor_obj (X : BasedTopologicalSpace.{u}) :
    fundamentalGroupFunctor.obj X = GrpCat.of (FundamentalGroup X.carrier X.basepoint) :=
  (rfl)

@[simp]
theorem fundamentalGroupFunctor_map_hom {X Y : BasedTopologicalSpace.{u}} (f : X ⟶ Y) :
    (fundamentalGroupFunctor.map f).hom =
      FundamentalGroup.mapOfEq f.toContinuousMap f.map_basepoint :=
  (rfl)

/-- Pointed-homotopic based maps induce the same homomorphism of fundamental groups. -/
theorem fundamentalGroupFunctor_map_eq_of_homotopicRel {X Y : BasedTopologicalSpace.{u}}
    {f g : X ⟶ Y} (h : homotopicRel f g) :
    fundamentalGroupFunctor.map f = fundamentalGroupFunctor.map g :=
  GrpCat.hom_ext (FundamentalGroup.mapOfEq_eq_of_homotopicRel _ _ rfl h)

end BasedTopologicalSpace

/-- **The pointed homotopy category.** Its objects are the based topological spaces, and its
morphisms are the classes of based maps up to homotopy relative to the base point. -/
@[expose] def PointedHomotopyCat : Type (u + 1) :=
  CategoryTheory.Quotient BasedTopologicalSpace.homotopicRel.{u}

namespace PointedHomotopyCat

instance : Category PointedHomotopyCat.{u} :=
  inferInstanceAs (Category (CategoryTheory.Quotient BasedTopologicalSpace.homotopicRel.{u}))

/-- The functor sending a based space to itself and a based map to its pointed homotopy class. -/
@[expose] def quotient : BasedTopologicalSpace.{u} ⥤ PointedHomotopyCat.{u} :=
  CategoryTheory.Quotient.functor _

instance : quotient.{u}.Full :=
  inferInstanceAs (CategoryTheory.Quotient.functor _).Full

instance : quotient.{u}.EssSurj :=
  inferInstanceAs (CategoryTheory.Quotient.functor _).EssSurj

/-- **Two based maps have the same pointed homotopy class exactly when they are homotopic
relative to the base point.** -/
theorem quotient_map_eq_iff {X Y : BasedTopologicalSpace.{u}} (f g : X ⟶ Y) :
    quotient.map f = quotient.map g ↔
      f.toContinuousMap.HomotopicRel g.toContinuousMap {X.basepoint} :=
  CategoryTheory.Quotient.functor_map_eq_iff _ f g

/-- **The fundamental group on the pointed homotopy category**, induced by the fundamental group of
based spaces: pointed-homotopic maps induce the same homomorphism. -/
@[expose] def fundamentalGroupFunctor : PointedHomotopyCat.{u} ⥤ GrpCat.{u} :=
  CategoryTheory.Quotient.lift _ BasedTopologicalSpace.fundamentalGroupFunctor
    fun _ _ _ _ h ↦ BasedTopologicalSpace.fundamentalGroupFunctor_map_eq_of_homotopicRel h

/-- The fundamental group of based spaces factors through the pointed homotopy category. -/
theorem quotient_comp_fundamentalGroupFunctor :
    quotient.{u} ⋙ fundamentalGroupFunctor = BasedTopologicalSpace.fundamentalGroupFunctor :=
  CategoryTheory.Quotient.lift_spec _ _ _

@[simp]
theorem fundamentalGroupFunctor_obj_quotient_obj (X : BasedTopologicalSpace.{u}) :
    fundamentalGroupFunctor.obj (quotient.obj X) =
      GrpCat.of (FundamentalGroup X.carrier X.basepoint) :=
  (rfl)

@[simp]
theorem fundamentalGroupFunctor_map_quotient_map {X Y : BasedTopologicalSpace.{u}} (f : X ⟶ Y) :
    fundamentalGroupFunctor.map (quotient.map f) =
      BasedTopologicalSpace.fundamentalGroupFunctor.map f :=
  (rfl)

/-- **A pointed homotopy equivalence between well-pointed spaces is an isomorphism in the pointed
homotopy category.** When the base points of `X` and `Y` have the homotopy extension property, a
homotopy equivalence `e : X.carrier ≃ₕ Y.carrier` preserving base points has a based homotopy
inverse with both homotopies relative to the base points
(`TauCeti.HasHomotopyExtensionProperty.exists_basedInverse_homotopicRel`), so it descends to an
isomorphism in `TauCeti.PointedHomotopyCat`. -/
def isoOfHomotopyEquiv {X Y : BasedTopologicalSpace.{u}}
    (hX : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (hY : HasHomotopyExtensionProperty ({Y.basepoint} : Set Y.carrier))
    (e : ContinuousMap.HomotopyEquiv X.carrier Y.carrier)
    (he : e.toFun X.basepoint = Y.basepoint) :
    quotient.obj X ≅ quotient.obj Y :=
  have hinv := hX.exists_basedInverse_homotopicRel hY e he
  { hom := quotient.map ⟨e.toFun, he⟩
    inv := quotient.map ⟨hinv.choose, hinv.choose_spec.1⟩
    hom_inv_id := by
      rw [← Functor.map_comp, ← quotient.map_id, quotient_map_eq_iff]
      simpa only [BasedTopologicalSpace.comp_eq_hom_comp,
        BasedTopologicalSpace.Hom.toContinuousMap_comp, BasedTopologicalSpace.id_eq_hom_id,
        BasedTopologicalSpace.Hom.toContinuousMap_id] using hinv.choose_spec.2.1
    inv_hom_id := by
      rw [← Functor.map_comp, ← quotient.map_id, quotient_map_eq_iff]
      simpa only [BasedTopologicalSpace.comp_eq_hom_comp,
        BasedTopologicalSpace.Hom.toContinuousMap_comp, BasedTopologicalSpace.id_eq_hom_id,
        BasedTopologicalSpace.Hom.toContinuousMap_id] using hinv.choose_spec.2.2 }

/-- The forward morphism of `isoOfHomotopyEquiv` is the pointed homotopy class of `e.toFun`. -/
@[simp]
theorem isoOfHomotopyEquiv_hom {X Y : BasedTopologicalSpace.{u}}
    (hX : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (hY : HasHomotopyExtensionProperty ({Y.basepoint} : Set Y.carrier))
    (e : ContinuousMap.HomotopyEquiv X.carrier Y.carrier)
    (he : e.toFun X.basepoint = Y.basepoint) :
    (isoOfHomotopyEquiv hX hY e he).hom = quotient.map ⟨e.toFun, he⟩ :=
  (rfl)

/-- **A based map between well-pointed spaces whose underlying continuous map is a homotopy
equivalence induces an isomorphism in the pointed homotopy category.** -/
theorem isIso_quotient_map_of_homotopyEquiv {X Y : BasedTopologicalSpace.{u}}
    (hX : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (hY : HasHomotopyExtensionProperty ({Y.basepoint} : Set Y.carrier))
    {f : X ⟶ Y} (e : ContinuousMap.HomotopyEquiv X.carrier Y.carrier)
    (he : e.toFun = f.toContinuousMap) :
    IsIso (quotient.map f) := by
  have hbp : e.toFun X.basepoint = Y.basepoint := by rw [he]; exact f.map_basepoint
  have hf : f = ⟨e.toFun, hbp⟩ := BasedTopologicalSpace.Hom.ext he.symm
  rw [hf]
  exact (isoOfHomotopyEquiv hX hY e hbp).isIso_hom

/-- **An isomorphism in the pointed homotopy category yields a homotopy equivalence of underlying
spaces**, whose forward and inverse maps preserve the base points and represent the isomorphism and
its inverse. -/
def homotopyEquivOfIso {X Y : BasedTopologicalSpace.{u}}
    (e : quotient.obj X ≅ quotient.obj Y) :
    ContinuousMap.HomotopyEquiv X.carrier Y.carrier where
  toFun := (quotient.preimage e.hom).toContinuousMap
  invFun := (quotient.preimage e.inv).toContinuousMap
  left_inv := by
    have h : quotient.map (quotient.preimage e.hom ≫ quotient.preimage e.inv) =
        quotient.map (𝟙 X) := by
      rw [Functor.map_comp, quotient.map_preimage, quotient.map_preimage, e.hom_inv_id,
        quotient.map_id]
    have hrel := (quotient_map_eq_iff _ _).1 h
    simp only [BasedTopologicalSpace.comp_eq_hom_comp,
      BasedTopologicalSpace.Hom.toContinuousMap_comp, BasedTopologicalSpace.id_eq_hom_id,
      BasedTopologicalSpace.Hom.toContinuousMap_id] at hrel
    exact ⟨hrel.some.toHomotopy⟩
  right_inv := by
    have h : quotient.map (quotient.preimage e.inv ≫ quotient.preimage e.hom) =
        quotient.map (𝟙 Y) := by
      rw [Functor.map_comp, quotient.map_preimage, quotient.map_preimage, e.inv_hom_id,
        quotient.map_id]
    have hrel := (quotient_map_eq_iff _ _).1 h
    simp only [BasedTopologicalSpace.comp_eq_hom_comp,
      BasedTopologicalSpace.Hom.toContinuousMap_comp, BasedTopologicalSpace.id_eq_hom_id,
      BasedTopologicalSpace.Hom.toContinuousMap_id] at hrel
    exact ⟨hrel.some.toHomotopy⟩

/-- The forward map of `homotopyEquivOfIso e` preserves the base point. -/
@[simp]
theorem homotopyEquivOfIso_toFun_basepoint {X Y : BasedTopologicalSpace.{u}}
    (e : quotient.obj X ≅ quotient.obj Y) :
    (homotopyEquivOfIso e).toFun X.basepoint = Y.basepoint :=
  (quotient.preimage e.hom).map_basepoint

/-- The inverse map of `homotopyEquivOfIso e` preserves the base point. -/
@[simp]
theorem homotopyEquivOfIso_invFun_basepoint {X Y : BasedTopologicalSpace.{u}}
    (e : quotient.obj X ≅ quotient.obj Y) :
    (homotopyEquivOfIso e).invFun Y.basepoint = X.basepoint :=
  (quotient.preimage e.inv).map_basepoint

/-- The forward map of `homotopyEquivOfIso e` represents `e.hom`. -/
@[simp]
theorem quotient_map_homotopyEquivOfIso_toFun {X Y : BasedTopologicalSpace.{u}}
    (e : quotient.obj X ≅ quotient.obj Y) :
    quotient.map ⟨(homotopyEquivOfIso e).toFun, homotopyEquivOfIso_toFun_basepoint e⟩ = e.hom :=
  quotient.map_preimage e.hom

/-- The inverse map of `homotopyEquivOfIso e` represents `e.inv`. -/
@[simp]
theorem quotient_map_homotopyEquivOfIso_invFun {X Y : BasedTopologicalSpace.{u}}
    (e : quotient.obj X ≅ quotient.obj Y) :
    quotient.map ⟨(homotopyEquivOfIso e).invFun, homotopyEquivOfIso_invFun_basepoint e⟩ = e.inv :=
  quotient.map_preimage e.inv

end PointedHomotopyCat

end TauCeti
