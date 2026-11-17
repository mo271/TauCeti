/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.EssentialImage
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Comparison
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Functoriality
public import TauCeti.AlgebraicTopology.Homotopy.PointedHomotopyCat
public import TauCeti.Topology.Homotopy.Extension.CWComplex
import TauCeti.AlgebraicTopology.EilenbergMacLane.WeakHomotopyEquivalence

/-!
# The classifying space as a functor to the pointed homotopy category

Milnor's classifying space is strictly functorial in the group
(`MonoidHom.classifyingSpaceMap`), so it is a functor
`TauCeti.classifyingSpaceFunctor : GrpCat ⥤ BasedTopologicalSpace` to based spaces. Composing with
the quotient by pointed homotopy gives the classifying-space functor
`TauCeti.classifyingSpaceHomotopyFunctor : GrpCat ⥤ PointedHomotopyCat` to the pointed homotopy
category, which the strict functor refines by construction.

Under the identifications `TauCeti.classifyingSpaceFundamentalGroupMulEquiv` of the fundamental
groups of the classifying spaces with the groups, the fundamental group undoes the classifying
space: `TauCeti.classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso` is a natural
isomorphism from `B ⋙ π₁` to the identity functor of `GrpCat`. In particular the
classifying-space functor is faithful.

Both `TauCeti.cellularClassifyingSpace R` and `TauCeti.classifyingSpace G` are Hausdorff CW
complexes based at a `0`-cell, so their base points have the homotopy extension property
(`TauCeti.hasHomotopyExtensionProperty_cellularClassifyingSpaceBasepoint`,
`TauCeti.hasHomotopyExtensionProperty_classifyingSpaceBasepoint`). Upgrading the unpointed
homotopy equivalences of `TauCeti.AlgebraicTopology.ClassifyingSpace.Comparison` via
`TauCeti.PointedHomotopyCat.isoOfHomotopyEquiv` identifies the cellular model with Milnor's
model (`TauCeti.cellularIsoClassifyingSpace`) and with every well-pointed aspherical space of CW
type (`TauCeti.cellularClassifyingSpaceBasedIso`) in `TauCeti.PointedHomotopyCat`.

Transporting `TauCeti.fundamentalGroupFunctor_map_bijective_cellularClassifyingSpace` along these
isomorphisms yields:

* **Universal property:** pointed homotopy classes of maps out of any well-pointed aspherical
  space of CW type (in particular any Hausdorff CW `K(G, 1)` based at a `0`-cell, or
  `classifyingSpace G`) into a space without higher homotopy groups correspond bijectively to
  homomorphisms on `π₁`.
* **Full faithfulness:** `TauCeti.classifyingSpaceHomotopyFunctor` is fully faithful
  (`TauCeti.classifyingSpaceHomotopyFunctorFullyFaithful`,
  `TauCeti.instFullClassifyingSpaceHomotopyFunctor`), with explicit preimage via `π₁`.
* **Pointed uniqueness:** between any two well-pointed aspherical spaces of CW type, every
  isomorphism on `π₁` is induced by a unique isomorphism in `PointedHomotopyCat`
  (`TauCeti.existsUnique_iso_of_isAspherical`, `TauCeti.existsUnique_iso_classifyingSpace`).
* **Equivalence of categories:** `TauCeti.classifyingSpaceEquivalence` is an explicit equivalence
  `GrpCat ≌ classifyingSpaceHomotopyFunctor.EssImageSubcategory` with quasi-inverse
  `PointedHomotopyCat.fundamentalGroupFunctor`. The essential image contains every well-pointed
  aspherical space of CW type and consists of aspherical spaces of CW type; it is strictly larger
  than the well-pointed ones (for instance `[0, 1]^ℝ` based at `0` is pointed-contractible, hence
  isomorphic in `PointedHomotopyCat` to `classifyingSpace PUnit`, yet `{0}` is not a `G_δ` set
  and lacks the homotopy extension property).

## Main definitions

* `TauCeti.classifyingSpaceFunctor`, `TauCeti.classifyingSpaceHomotopyFunctor`: Milnor's
  classifying space as a functor to `BasedTopologicalSpace` and `PointedHomotopyCat`.
* `TauCeti.classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso`: the natural
  isomorphism `π₁ ∘ B ≅ 𝟭`.
* `TauCeti.cellularClassifyingSpaceBased`, `TauCeti.cellularHomotopyEquivClassifyingSpaceBasedHom`:
  the cellular classifying space and its comparison map with Milnor's model as based data.
* `TauCeti.cellularClassifyingSpaceBasedIso`, `TauCeti.cellularIsoClassifyingSpace`: isomorphisms
  in `PointedHomotopyCat` from the cellular model to any well-pointed aspherical space of CW type
  and to Milnor's classifying space.
* `TauCeti.classifyingSpaceHomotopyFunctorFullyFaithful`: explicit full faithfulness of
  `classifyingSpaceHomotopyFunctor`.
* `TauCeti.classifyingSpaceHomEquiv`: natural bijection `(BG ⟶ Y) ≃ (G ⟶ π₁ Y)` when `Y` has no
  higher homotopy groups.
* `TauCeti.classifyingSpaceEquivalence`: equivalence between `GrpCat` and
  `classifyingSpaceHomotopyFunctor.EssImageSubcategory`.

## Main results

* `TauCeti.fundamentalGroupFunctor_map_bijective_cellularClassifyingSpace`,
  `TauCeti.fundamentalGroupFunctor_map_bijective_of_isAspherical`,
  `TauCeti.fundamentalGroupFunctor_map_bijective_classifyingSpace`: classification of pointed
  homotopy classes of maps out of a `K(G, 1)` into a space without higher homotopy groups.
* `TauCeti.IsAspherical.exists_mapOfEq`, `TauCeti.IsAspherical.homotopicRel_of_mapOfEq_eq`,
  `TauCeti.homotopicRel_classifyingSpaceMap`: concrete topological existence and pointed-homotopy
  uniqueness statements.
* `TauCeti.existsUnique_iso_of_isAspherical`, `TauCeti.existsUnique_iso_classifyingSpace`:
  pointed uniqueness of well-pointed `K(G, 1)` spaces of CW type in `PointedHomotopyCat`.
* `TauCeti.mem_essImage_classifyingSpaceHomotopyFunctor_of_isAspherical`,
  `TauCeti.cwType_of_mem_essImage_classifyingSpaceHomotopyFunctor`,
  `TauCeti.isAspherical_of_mem_essImage_classifyingSpaceHomotopyFunctor`: characterization of
  objects in the essential image of `classifyingSpaceHomotopyFunctor`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0, Proposition 0.19,
  and Section 1.B, Theorem 1B.8 and Proposition 1B.9.
* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
-/

public section

noncomputable section

open CategoryTheory

open scoped Topology

universe u v

namespace TauCeti

/-- **Milnor's classifying space as a functor to based spaces.** A group goes to
`classifyingSpace G` with its base point, and a homomorphism to the strictly functorial map
`MonoidHom.classifyingSpaceMap`. -/
@[expose] def classifyingSpaceFunctor : GrpCat.{u} ⥤ BasedTopologicalSpace.{u} where
  obj G := ⟨classifyingSpace G, classifyingSpaceBasepoint G⟩
  map φ := ⟨φ.hom.classifyingSpaceMap, φ.hom.classifyingSpaceMap_basepoint⟩
  map_id G := BasedTopologicalSpace.Hom.ext (by
    simp only [GrpCat.hom_id, MonoidHom.classifyingSpaceMap_id,
      BasedTopologicalSpace.id_eq_hom_id, BasedTopologicalSpace.Hom.toContinuousMap_id])
  map_comp φ ψ := BasedTopologicalSpace.Hom.ext (by
    simp only [GrpCat.hom_comp, MonoidHom.classifyingSpaceMap_comp,
      BasedTopologicalSpace.comp_eq_hom_comp, BasedTopologicalSpace.Hom.toContinuousMap_comp])

@[simp]
theorem classifyingSpaceFunctor_obj_carrier (G : GrpCat.{u}) :
    (classifyingSpaceFunctor.obj G).carrier = classifyingSpace G :=
  (rfl)

@[simp]
theorem classifyingSpaceFunctor_obj_basepoint (G : GrpCat.{u}) :
    (classifyingSpaceFunctor.obj G).basepoint = classifyingSpaceBasepoint G :=
  (rfl)

@[simp]
theorem classifyingSpaceFunctor_map_toContinuousMap {G H : GrpCat.{u}} (φ : G ⟶ H) :
    (classifyingSpaceFunctor.map φ).toContinuousMap = φ.hom.classifyingSpaceMap :=
  (rfl)

/-- **The classifying space as a functor to the pointed homotopy category.** It sends a
homomorphism to the pointed homotopy class of the strictly functorial map of Milnor's classifying
spaces, so `TauCeti.classifyingSpaceFunctor` refines it. -/
@[expose] def classifyingSpaceHomotopyFunctor : GrpCat.{u} ⥤ PointedHomotopyCat.{u} :=
  classifyingSpaceFunctor ⋙ PointedHomotopyCat.quotient

@[simp]
theorem classifyingSpaceHomotopyFunctor_map {G H : GrpCat.{u}} (φ : G ⟶ H) :
    classifyingSpaceHomotopyFunctor.map φ =
      PointedHomotopyCat.quotient.map (classifyingSpaceFunctor.map φ) :=
  (rfl)

/-- **The fundamental group of the classifying space is the group, naturally.** The isomorphisms
`classifyingSpaceFundamentalGroupMulEquiv G` assemble into a natural isomorphism from the
fundamental group of the classifying space, as functors on `GrpCat`, to the identity functor. -/
def classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso :
    classifyingSpaceHomotopyFunctor ⋙ PointedHomotopyCat.fundamentalGroupFunctor ≅
      𝟭 GrpCat.{u} :=
  NatIso.ofComponents (fun G ↦ (classifyingSpaceFundamentalGroupMulEquiv G).toGrpIso)
    fun φ ↦ by
      ext a
      -- The composite sends `φ` to `mapOfEq` along `φ.hom.classifyingSpaceMap`: this is the
      -- definitional chain `classifyingSpaceHomotopyFunctor_map`,
      -- `PointedHomotopyCat.fundamentalGroupFunctor_map_quotient_map`,
      -- `BasedTopologicalSpace.fundamentalGroupFunctor_map_hom` and
      -- `classifyingSpaceFunctor_map_toContinuousMap`, which `rw` cannot apply because the source
      -- and target objects of the composite only agree with theirs up to unfolding.
      change classifyingSpaceFundamentalGroupMulEquiv _ (FundamentalGroup.mapOfEq
          φ.hom.classifyingSpaceMap φ.hom.classifyingSpaceMap_basepoint a) =
        φ.hom (classifyingSpaceFundamentalGroupMulEquiv _ a)
      exact φ.hom.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq a

@[simp]
theorem classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso_hom_app_hom
    (G : GrpCat.{u}) :
    (classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app G).hom =
      (classifyingSpaceFundamentalGroupMulEquiv G).toMonoidHom :=
  (rfl)

@[simp]
theorem classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso_inv_app_hom
    (G : GrpCat.{u}) :
    (classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app G).hom =
      (classifyingSpaceFundamentalGroupMulEquiv G).symm.toMonoidHom :=
  (rfl)

/-- The classifying-space functor to the pointed homotopy category is faithful: the fundamental
group recovers the homomorphism inducing a map. -/
instance : classifyingSpaceHomotopyFunctor.{u}.Faithful :=
  .of_comp_iso classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso

section Cellular

variable {S : Type u} (R : Set (FreeGroup S))

/-- The cellular classifying space `cellularClassifyingSpace R` as a based space, based at the
vertex `cellularClassifyingSpaceBasepoint R`. -/
@[expose] def cellularClassifyingSpaceBased : BasedTopologicalSpace.{u} :=
  ⟨cellularClassifyingSpace R, cellularClassifyingSpaceBasepoint R⟩

@[simp]
theorem cellularClassifyingSpaceBased_carrier :
    (cellularClassifyingSpaceBased R).carrier = cellularClassifyingSpace R :=
  (rfl)

@[simp]
theorem cellularClassifyingSpaceBased_basepoint :
    (cellularClassifyingSpaceBased R).basepoint = cellularClassifyingSpaceBasepoint R :=
  (rfl)

/-- The comparison `cellularHomotopyEquivClassifyingSpace R e` of the cellular model with Milnor's
classifying space, as a based map. -/
@[expose] def cellularHomotopyEquivClassifyingSpaceBasedHom {G : GrpCat.{u}}
    (e : PresentedGroup R ≃* G) :
    cellularClassifyingSpaceBased R ⟶ classifyingSpaceFunctor.obj G :=
  ⟨(cellularHomotopyEquivClassifyingSpace R e).toFun,
    cellularHomotopyEquivClassifyingSpace_toFun_basepoint R e⟩

@[simp]
theorem cellularHomotopyEquivClassifyingSpaceBasedHom_toContinuousMap {G : GrpCat.{u}}
    (e : PresentedGroup R ≃* G) :
    (cellularHomotopyEquivClassifyingSpaceBasedHom R e).toContinuousMap =
      (cellularHomotopyEquivClassifyingSpace R e).toFun :=
  (rfl)

/-- Based maps out of the cellular classifying space into a space without higher homotopy groups
that induce the same homomorphism of fundamental groups have the same pointed homotopy class. -/
private theorem quotient_map_eq_cellularClassifyingSpace {Y : BasedTopologicalSpace.{u}}
    (hY : ∀ (y : Y.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.carrier y))
    {f g : cellularClassifyingSpaceBased R ⟶ Y}
    (h : BasedTopologicalSpace.fundamentalGroupFunctor.map f =
      BasedTopologicalSpace.fundamentalGroupFunctor.map g) :
    PointedHomotopyCat.quotient.map f = PointedHomotopyCat.quotient.map g :=
  (PointedHomotopyCat.quotient_map_eq_iff f g).2
    (homotopicRel_of_mapOfEq_eq_cellularClassifyingSpace R hY f.map_basepoint g.map_basepoint
      (by
        have h' := congrArg GrpCat.Hom.hom h
        rw [BasedTopologicalSpace.fundamentalGroupFunctor_map_hom,
          BasedTopologicalSpace.fundamentalGroupFunctor_map_hom] at h'
        exact h'))

/-- **Pointed maps out of a cellular classifying space are classified by `π₁`.** If the homotopy
groups of `Y` vanish from degree `2` on, at every point, then a pointed homotopy class of maps from
the cellular classifying space `cellularClassifyingSpace R` to `Y` is determined by the homomorphism
it induces on fundamental groups, and every homomorphism is induced by such a class. -/
theorem fundamentalGroupFunctor_map_bijective_cellularClassifyingSpace
    {Y : BasedTopologicalSpace.{u}}
    (hY : ∀ (y : Y.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.carrier y)) :
    Function.Bijective (PointedHomotopyCat.fundamentalGroupFunctor.map
      (X := PointedHomotopyCat.quotient.obj (cellularClassifyingSpaceBased R))
      (Y := PointedHomotopyCat.quotient.obj Y)) := by
  refine ⟨fun a b hab ↦ ?_, fun ψ ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := PointedHomotopyCat.quotient.map_surjective a
    obtain ⟨g, rfl⟩ := PointedHomotopyCat.quotient.map_surjective b
    simp only [PointedHomotopyCat.fundamentalGroupFunctor_map_quotient_map] at hab
    exact quotient_map_eq_cellularClassifyingSpace R hY hab
  · obtain ⟨f, hf, hfψ⟩ := exists_mapOfEq_cellularClassifyingSpace R
      (fun k hk ↦ by
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
        exact hY _ n) ψ.hom
    exact ⟨PointedHomotopyCat.quotient.map ⟨f, hf⟩, GrpCat.hom_ext <|
      (congrArg GrpCat.Hom.hom
        (PointedHomotopyCat.fundamentalGroupFunctor_map_quotient_map _)).trans
        ((BasedTopologicalSpace.fundamentalGroupFunctor_map_hom _).trans hfψ)⟩

/-- **The map induced by a homomorphism is determined up to pointed homotopy.** Let
`e : PresentedGroup R ≃* G` be a presentation and `φ : G ⟶ H`. Every pointed map from the cellular
classifying space of `R` to `classifyingSpace H` that induces `φ` under the identifications of both
fundamental groups is pointed homotopic to the comparison map of
`cellularHomotopyEquivClassifyingSpace R e` followed by `classifyingSpaceMap φ`. In the pointed
homotopy category the right-hand side is the comparison map followed by
`classifyingSpaceHomotopyFunctor.map φ`. -/
theorem quotient_map_eq_quotient_map_comp_cellularClassifyingSpace {G H : GrpCat.{u}}
    (e : PresentedGroup R ≃* G) (φ : G ⟶ H)
    (f : cellularClassifyingSpaceBased R ⟶ classifyingSpaceFunctor.obj H)
    (hf : ∀ a, classifyingSpaceFundamentalGroupMulEquiv H
        ((BasedTopologicalSpace.fundamentalGroupFunctor.map f).hom a) =
      φ.hom (e (cellularClassifyingSpaceFundamentalGroupMulEquiv R a))) :
    PointedHomotopyCat.quotient.map f =
      PointedHomotopyCat.quotient.map
        (cellularHomotopyEquivClassifyingSpaceBasedHom R e ≫ classifyingSpaceFunctor.map φ) := by
  refine quotient_map_eq_cellularClassifyingSpace R
    (fun y n ↦ subsingleton_homotopyGroup_classifyingSpace H n y) ?_
  rw [Functor.map_comp]
  refine GrpCat.hom_ext <| MonoidHom.ext fun a ↦
    (classifyingSpaceFundamentalGroupMulEquiv H).injective ?_
  simp only [GrpCat.hom_comp, BasedTopologicalSpace.fundamentalGroupFunctor_map_hom,
    cellularHomotopyEquivClassifyingSpaceBasedHom_toContinuousMap] at hf ⊢
  -- Both sides are `φ ∘ e` under the identifications: the comparison induces `e`, and the strict
  -- map induces `φ`.
  exact (hf a).trans <| (congrArg φ.hom
    (classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_cellularHomotopyEquivClassifyingSpace R e
      a).symm).trans (φ.hom.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq _).symm

/-- **The base point of the cellular classifying space has the homotopy extension property**, as
it is the unique `0`-cell of a Hausdorff CW complex. -/
theorem hasHomotopyExtensionProperty_cellularClassifyingSpaceBasepoint :
    HasHomotopyExtensionProperty
      ({cellularClassifyingSpaceBasepoint R} : Set (cellularClassifyingSpace R)) :=
  hasHomotopyExtensionProperty_singleton_of_mem_skeletonLT_one <| by
    rw [skeletonLT_one_cellularClassifyingSpace]
    rfl

end Cellular

section PointedEquivalence

/-- **The base point of Milnor's classifying space has the homotopy extension property**, as it
lies in the `0`-skeleton of the Hausdorff CW complex `classifyingSpace G`. -/
theorem hasHomotopyExtensionProperty_classifyingSpaceBasepoint (G : Type u) [Group G] :
    HasHomotopyExtensionProperty ({classifyingSpaceBasepoint G} : Set (classifyingSpace G)) :=
  hasHomotopyExtensionProperty_singleton_of_mem_skeletonLT_one
    (mem_skeletonLT_one_classifyingSpaceBasepoint G)

section BasedIso

variable {S : Type u} (R : Set (FreeGroup S)) {X : BasedTopologicalSpace.{u}} [CWType X.carrier]
  (hX : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
  (hX' : IsAspherical X.carrier X.basepoint)
  (φ : FundamentalGroup (cellularClassifyingSpace R) (cellularClassifyingSpaceBasepoint R) ≃*
    FundamentalGroup X.carrier X.basepoint)

/-- **The cellular model is pointed homotopy equivalent to every well-pointed aspherical space of
CW type with the same fundamental group.** The forward map is the pointed homotopy equivalence
`cellularClassifyingSpaceHomotopyEquiv R hX' φ`, upgraded to an isomorphism in
`TauCeti.PointedHomotopyCat` using the homotopy extension property of both base points. -/
def cellularClassifyingSpaceBasedIso :
    PointedHomotopyCat.quotient.obj (cellularClassifyingSpaceBased R) ≅
      PointedHomotopyCat.quotient.obj X :=
  PointedHomotopyCat.isoOfHomotopyEquiv
    (hasHomotopyExtensionProperty_cellularClassifyingSpaceBasepoint R) hX
    (cellularClassifyingSpaceHomotopyEquiv R hX' φ)
    (cellularClassifyingSpaceHomotopyEquiv_toFun_basepoint R hX' φ)

@[simp]
theorem cellularClassifyingSpaceBasedIso_hom :
    (cellularClassifyingSpaceBasedIso R hX hX' φ).hom =
      PointedHomotopyCat.quotient.map
        ⟨(cellularClassifyingSpaceHomotopyEquiv R hX' φ).toFun,
          cellularClassifyingSpaceHomotopyEquiv_toFun_basepoint R hX' φ⟩ :=
  PointedHomotopyCat.isoOfHomotopyEquiv_hom ..

/-- The forward morphism of `cellularClassifyingSpaceBasedIso` induces `φ` on fundamental
groups. -/
theorem fundamentalGroupFunctor_map_cellularClassifyingSpaceBasedIso_hom_hom :
    (PointedHomotopyCat.fundamentalGroupFunctor.map
        (cellularClassifyingSpaceBasedIso R hX hX' φ).hom).hom =
      φ.toMonoidHom := by
  rw [cellularClassifyingSpaceBasedIso_hom]
  exact MonoidHom.ext fun a ↦ mapOfEq_cellularClassifyingSpaceHomotopyEquiv_toFun_apply R hX' φ a

/-- The inverse morphism of `cellularClassifyingSpaceBasedIso` induces `φ⁻¹` on fundamental
groups, strictly and without any change of base point. -/
@[simp]
theorem fundamentalGroupFunctor_map_cellularClassifyingSpaceBasedIso_inv_hom :
    (PointedHomotopyCat.fundamentalGroupFunctor.map
        (cellularClassifyingSpaceBasedIso R hX hX' φ).inv).hom =
      φ.symm.toMonoidHom := by
  let φIso : PointedHomotopyCat.fundamentalGroupFunctor.obj
        (PointedHomotopyCat.quotient.obj (cellularClassifyingSpaceBased R)) ≅
      PointedHomotopyCat.fundamentalGroupFunctor.obj (PointedHomotopyCat.quotient.obj X) :=
    MulEquiv.toGrpIso φ
  exact congrArg (fun i ↦ i.inv.hom)
    (Iso.ext
      (α := PointedHomotopyCat.fundamentalGroupFunctor.mapIso
        (cellularClassifyingSpaceBasedIso R hX hX' φ))
      (β := φIso)
      (GrpCat.hom_ext
        (fundamentalGroupFunctor_map_cellularClassifyingSpaceBasedIso_hom_hom R hX hX' φ)))

end BasedIso

section CellularModelIso

variable {S : Type u} (R : Set (FreeGroup S)) {G : GrpCat.{u}} (e : PresentedGroup R ≃* G)

/-- **The cellular and simplicial classifying spaces are isomorphic in the pointed homotopy
category.** The forward morphism is the pointed homotopy class of
`cellularHomotopyEquivClassifyingSpaceBasedHom R e`. -/
def cellularIsoClassifyingSpace :
    PointedHomotopyCat.quotient.obj (cellularClassifyingSpaceBased R) ≅
      classifyingSpaceHomotopyFunctor.obj G :=
  PointedHomotopyCat.isoOfHomotopyEquiv
    (hasHomotopyExtensionProperty_cellularClassifyingSpaceBasepoint R)
    (hasHomotopyExtensionProperty_classifyingSpaceBasepoint G)
    (cellularHomotopyEquivClassifyingSpace R e)
    (cellularHomotopyEquivClassifyingSpace_toFun_basepoint R e)

@[simp]
theorem cellularIsoClassifyingSpace_hom :
    (cellularIsoClassifyingSpace R e).hom =
      PointedHomotopyCat.quotient.map (cellularHomotopyEquivClassifyingSpaceBasedHom R e) :=
  PointedHomotopyCat.isoOfHomotopyEquiv_hom ..

/-- The comparison map from the cellular model to Milnor's classifying space induces an isomorphism
in the pointed homotopy category. -/
theorem isIso_quotient_map_cellularHomotopyEquivClassifyingSpaceBasedHom :
    IsIso (PointedHomotopyCat.quotient.map
      (cellularHomotopyEquivClassifyingSpaceBasedHom R e)) := by
  rw [← cellularIsoClassifyingSpace_hom]
  exact (cellularIsoClassifyingSpace R e).isIso_hom

/-- Under the identifications of both fundamental groups, the forward morphism of
`cellularIsoClassifyingSpace R e` induces `e`. -/
theorem classifyingSpaceFundamentalGroupMulEquiv_cellularIsoClassifyingSpace_hom
    (a : FundamentalGroup (cellularClassifyingSpace R) (cellularClassifyingSpaceBasepoint R)) :
    classifyingSpaceFundamentalGroupMulEquiv G
        ((PointedHomotopyCat.fundamentalGroupFunctor.map
          (cellularIsoClassifyingSpace R e).hom).hom a) =
      e (cellularClassifyingSpaceFundamentalGroupMulEquiv R a) := by
  rw [cellularIsoClassifyingSpace_hom]
  exact classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_cellularHomotopyEquivClassifyingSpace
    R e a

/-- Under the identifications of both fundamental groups, the inverse morphism of
`cellularIsoClassifyingSpace R e` induces `e⁻¹`. -/
@[simp]
theorem cellularClassifyingSpaceFundamentalGroupMulEquiv_cellularIsoClassifyingSpace_inv
    (a : FundamentalGroup (classifyingSpace G) (classifyingSpaceBasepoint G)) :
    cellularClassifyingSpaceFundamentalGroupMulEquiv R
        ((PointedHomotopyCat.fundamentalGroupFunctor.map
          (cellularIsoClassifyingSpace R e).inv).hom a) =
      e.symm (classifyingSpaceFundamentalGroupMulEquiv G a) := by
  let φ : FundamentalGroup (cellularClassifyingSpace R) (cellularClassifyingSpaceBasepoint R) ≃*
      FundamentalGroup (classifyingSpace G) (classifyingSpaceBasepoint G) :=
    (cellularClassifyingSpaceFundamentalGroupMulEquiv R).trans
      (e.trans (classifyingSpaceFundamentalGroupMulEquiv G).symm)
  let φIso : PointedHomotopyCat.fundamentalGroupFunctor.obj
        (PointedHomotopyCat.quotient.obj (cellularClassifyingSpaceBased R)) ≅
      PointedHomotopyCat.fundamentalGroupFunctor.obj (classifyingSpaceHomotopyFunctor.obj G) :=
    MulEquiv.toGrpIso φ
  have hhom : (PointedHomotopyCat.fundamentalGroupFunctor.mapIso
      (cellularIsoClassifyingSpace R e)).hom = φIso.hom :=
    GrpCat.hom_ext <| MonoidHom.ext fun b ↦
      (classifyingSpaceFundamentalGroupMulEquiv G).injective <|
        (classifyingSpaceFundamentalGroupMulEquiv_cellularIsoClassifyingSpace_hom
          R e b).trans (MulEquiv.apply_symm_apply _ _).symm
  exact (congrArg (cellularClassifyingSpaceFundamentalGroupMulEquiv R)
      (congrArg (fun i ↦ i.inv.hom a) (Iso.ext hhom))).trans
    (MulEquiv.apply_symm_apply (cellularClassifyingSpaceFundamentalGroupMulEquiv R)
      (e.symm (classifyingSpaceFundamentalGroupMulEquiv G a)))

end CellularModelIso

/-- **A based homotopy inverse for the comparison of the two models.** The homotopy equivalence
`cellularHomotopyEquivClassifyingSpace R e` has a based homotopy inverse `g` with both homotopies
relative to the base points, inducing `e⁻¹` strictly on fundamental groups without any change of
base point. -/
theorem exists_basedInverse_cellularHomotopyEquivClassifyingSpace {S : Type u}
    (R : Set (FreeGroup S)) {G : Type u} [Group G] (e : PresentedGroup R ≃* G) :
    ∃ (g : C(classifyingSpace G, cellularClassifyingSpace R))
      (hg : g (classifyingSpaceBasepoint G) = cellularClassifyingSpaceBasepoint R),
      (g.comp (cellularHomotopyEquivClassifyingSpace R e).toFun).HomotopicRel
        (ContinuousMap.id _) {cellularClassifyingSpaceBasepoint R} ∧
      ((cellularHomotopyEquivClassifyingSpace R e).toFun.comp g).HomotopicRel
        (ContinuousMap.id _) {classifyingSpaceBasepoint G} ∧
      ∀ a, cellularClassifyingSpaceFundamentalGroupMulEquiv R (FundamentalGroup.mapOfEq g hg a) =
        e.symm (classifyingSpaceFundamentalGroupMulEquiv G a) := by
  obtain ⟨g, hg, hgh, hhg⟩ :=
    (hasHomotopyExtensionProperty_cellularClassifyingSpaceBasepoint
      R).exists_basedInverse_homotopicRel
      (hasHomotopyExtensionProperty_classifyingSpaceBasepoint G)
      (cellularHomotopyEquivClassifyingSpace R e)
      (cellularHomotopyEquivClassifyingSpace_toFun_basepoint R e)
  refine ⟨g, hg, hgh, hhg, fun a ↦ e.injective ?_⟩
  have hcomp := DFunLike.congr_fun (FundamentalGroup.mapOfEq_eq_of_homotopicRel
    (f := (cellularHomotopyEquivClassifyingSpace R e).toFun.comp g) (g := ContinuousMap.id _)
    (by rw [ContinuousMap.comp_apply, hg, cellularHomotopyEquivClassifyingSpace_toFun_basepoint])
    (ContinuousMap.id_apply _) rfl hhg) a
  rw [← FundamentalGroup.mapOfEq_comp _ _ hg
      (cellularHomotopyEquivClassifyingSpace_toFun_basepoint R e),
    FundamentalGroup.mapOfEq_id (ContinuousMap.id_apply _)] at hcomp
  have h := congrArg (classifyingSpaceFundamentalGroupMulEquiv G) hcomp
  rw [classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_cellularHomotopyEquivClassifyingSpace] at h
  simpa using h

end PointedEquivalence

section UniversalProperty

/-- Bijectivity of `fundamentalGroupFunctor.map` on morphisms out of an object of
`PointedHomotopyCat` is invariant under isomorphism of the source. -/
private theorem bijective_fundamentalGroupFunctor_map_of_iso {X X' Y : PointedHomotopyCat.{u}}
    (e : X ≅ X')
    (h : Function.Bijective
      (PointedHomotopyCat.fundamentalGroupFunctor.map (X := X) (Y := Y))) :
    Function.Bijective
      (PointedHomotopyCat.fundamentalGroupFunctor.map (X := X') (Y := Y)) := by
  have heq : (PointedHomotopyCat.fundamentalGroupFunctor.map (X := X') (Y := Y)) =
      (Iso.homCongr (PointedHomotopyCat.fundamentalGroupFunctor.mapIso e) (Iso.refl _)) ∘
        (PointedHomotopyCat.fundamentalGroupFunctor.map (X := X) (Y := Y)) ∘
        (Iso.homCongr e.symm (Iso.refl _)) := by
    funext f
    simp [Function.comp_apply]
  rw [heq]
  exact (Iso.homCongr (PointedHomotopyCat.fundamentalGroupFunctor.mapIso e)
      (Iso.refl _)).bijective.comp
    (h.comp (Iso.homCongr e.symm (Iso.refl _)).bijective)

/-- **Pointed maps out of a well-pointed aspherical space of CW type are classified by `π₁`.** If
`X` is an aspherical space of CW type whose base point has the homotopy extension property, and
the homotopy groups of `Y` vanish from degree `2` on at every point, then pointed homotopy classes
of maps from `X` to `Y` correspond bijectively to homomorphisms `π₁(X) → π₁(Y)`. -/
theorem fundamentalGroupFunctor_map_bijective_of_isAspherical {X Y : BasedTopologicalSpace.{u}}
    [CWType X.carrier] (hX : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (hX' : IsAspherical X.carrier X.basepoint)
    (hY : ∀ (y : Y.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.carrier y)) :
    Function.Bijective (PointedHomotopyCat.fundamentalGroupFunctor.map
      (X := PointedHomotopyCat.quotient.obj X) (Y := PointedHomotopyCat.quotient.obj Y)) := by
  obtain ⟨R, -, -, hR⟩ :=
    exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace
      (FundamentalGroup X.carrier X.basepoint)
  obtain ⟨φ⟩ := hR.nonempty_fundamentalGroupMulEquiv
  exact bijective_fundamentalGroupFunctor_map_of_iso
    (cellularClassifyingSpaceBasedIso R hX hX' φ)
    (fundamentalGroupFunctor_map_bijective_cellularClassifyingSpace R hY)

/-- **Pointed maps out of a Hausdorff CW `K(G, 1)` based at a `0`-cell are classified by `π₁`.**
Specializes `TauCeti.fundamentalGroupFunctor_map_bijective_of_isAspherical` by discharging CW type
and the homotopy extension property of the base point from the CW structure. -/
theorem fundamentalGroupFunctor_map_bijective_of_cwComplex {X : Type u} [TopologicalSpace X]
    [T2Space X] [Topology.CWComplex (Set.univ : Set X)] {x : X}
    (hx : x ∈ (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) 1 : Set X))
    (hX : IsAspherical X x) {Y : BasedTopologicalSpace.{u}}
    (hY : ∀ (y : Y.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.carrier y)) :
    Function.Bijective (PointedHomotopyCat.fundamentalGroupFunctor.map
      (X := PointedHomotopyCat.quotient.obj ⟨X, x⟩) (Y := PointedHomotopyCat.quotient.obj Y)) :=
  fundamentalGroupFunctor_map_bijective_of_isAspherical
    (hasHomotopyExtensionProperty_singleton_of_mem_skeletonLT_one hx) hX hY

/-- **Pointed maps out of Milnor's classifying space are classified by `π₁`.** If the homotopy
groups of `Y` vanish from degree `2` on at every point, then pointed homotopy classes of maps from
`classifyingSpace G` to `Y` correspond bijectively to homomorphisms of fundamental groups. -/
theorem fundamentalGroupFunctor_map_bijective_classifyingSpace (G : GrpCat.{u})
    {Y : BasedTopologicalSpace.{u}}
    (hY : ∀ (y : Y.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.carrier y)) :
    Function.Bijective (PointedHomotopyCat.fundamentalGroupFunctor.map
      (X := classifyingSpaceHomotopyFunctor.obj G) (Y := PointedHomotopyCat.quotient.obj Y)) := by
  let : CWType (classifyingSpaceFunctor.obj G).carrier :=
    inferInstanceAs (CWType (classifyingSpace G))
  exact fundamentalGroupFunctor_map_bijective_of_isAspherical
    (hasHomotopyExtensionProperty_classifyingSpaceBasepoint G)
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical hY

/-- **Homomorphisms out of `π₁` of a well-pointed aspherical space of CW type are realized by
pointed maps.** Only the vanishing of the higher homotopy groups of `Z` at `z` is required. -/
theorem IsAspherical.exists_mapOfEq {X Z : Type u} [TopologicalSpace X] [CWType X] {x : X}
    (hX : IsAspherical X x) (hx : HasHomotopyExtensionProperty ({x} : Set X))
    [TopologicalSpace Z] {z : Z} (hZ : ∀ k, 2 ≤ k → Subsingleton (π_ k Z z))
    (fπ : FundamentalGroup X x →* FundamentalGroup Z z) :
    ∃ (f : C(X, Z)) (hf : f x = z), FundamentalGroup.mapOfEq f hf = fπ := by
  obtain ⟨R, -, -, hR⟩ :=
    exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace (FundamentalGroup X x)
  obtain ⟨φ⟩ := hR.nonempty_fundamentalGroupMulEquiv
  set h := cellularClassifyingSpaceHomotopyEquiv R hX φ
  have hh : h.toFun (cellularClassifyingSpaceBasepoint R) = x :=
    cellularClassifyingSpaceHomotopyEquiv_toFun_basepoint R hX φ
  obtain ⟨g, hg, -, hhg⟩ :=
    (hasHomotopyExtensionProperty_cellularClassifyingSpaceBasepoint
      R).exists_basedInverse_homotopicRel hx h hh
  obtain ⟨k, hk, hkπ⟩ := exists_mapOfEq_cellularClassifyingSpace R hZ (fπ.comp φ.toMonoidHom)
  refine ⟨k.comp g, by rw [ContinuousMap.comp_apply, hg, hk], MonoidHom.ext fun a ↦ ?_⟩
  rw [← FundamentalGroup.mapOfEq_comp k g hg hk, hkπ, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom]
  have hcomp := DFunLike.congr_fun
    (FundamentalGroup.mapOfEq_eq_of_homotopicRel (f := h.toFun.comp g) (g := ContinuousMap.id X)
      (by rw [ContinuousMap.comp_apply, hg, hh]) (ContinuousMap.id_apply x) rfl hhg) a
  rw [← FundamentalGroup.mapOfEq_comp h.toFun g hg hh,
    FundamentalGroup.mapOfEq_id (ContinuousMap.id_apply x),
    mapOfEq_cellularClassifyingSpaceHomotopyEquiv_toFun_apply R hX φ] at hcomp
  rw [hcomp]

/-- **Pointed maps out of a well-pointed aspherical space of CW type are determined up to pointed
homotopy by their effect on `π₁`.** The target space `Z` may live in any universe. -/
theorem IsAspherical.homotopicRel_of_mapOfEq_eq {X : Type u} {Z : Type v} [TopologicalSpace X]
    [CWType X] {x : X} (hX : IsAspherical X x) (hx : HasHomotopyExtensionProperty ({x} : Set X))
    [TopologicalSpace Z] (hZ : ∀ (z : Z) (n : ℕ), Subsingleton (π_ (n + 2) Z z))
    {f g : C(X, Z)} {z : Z} (hf : f x = z) (hg : g x = z)
    (hfg : FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg) :
    f.HomotopicRel g {x} := by
  obtain ⟨R, -, -, hR⟩ :=
    exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace (FundamentalGroup X x)
  obtain ⟨φ⟩ := hR.nonempty_fundamentalGroupMulEquiv
  set h := cellularClassifyingSpaceHomotopyEquiv R hX φ
  have hh : h.toFun (cellularClassifyingSpaceBasepoint R) = x :=
    cellularClassifyingSpaceHomotopyEquiv_toFun_basepoint R hX φ
  obtain ⟨h', hh', -, hhh'⟩ :=
    (hasHomotopyExtensionProperty_cellularClassifyingSpaceBasepoint
      R).exists_basedInverse_homotopicRel hx h hh
  have hfh_eq : (f.comp h.toFun).HomotopicRel (g.comp h.toFun)
      {cellularClassifyingSpaceBasepoint R} :=
    homotopicRel_of_mapOfEq_eq_cellularClassifyingSpace R hZ
      (by rw [ContinuousMap.comp_apply, hh, hf]) (by rw [ContinuousMap.comp_apply, hh, hg]) <|
      MonoidHom.ext fun a ↦ by
        rw [← FundamentalGroup.mapOfEq_comp f h.toFun hh hf,
          ← FundamentalGroup.mapOfEq_comp g h.toFun hh hg, hfg]
  have h1 : f.HomotopicRel (f.comp (h.toFun.comp h')) {x} := by
    simpa only [ContinuousMap.comp_id] using (hhh'.symm.comp_continuousMap f)
  have h2 : (f.comp (h.toFun.comp h')).HomotopicRel (g.comp (h.toFun.comp h')) {x} := by
    have hpre := (hfh_eq.precomp h').mono (fun y hy ↦ by
      rw [Set.mem_preimage, Set.mem_singleton_iff.1 hy, hh']
      rfl)
    simpa only [ContinuousMap.comp_assoc] using hpre
  have h3 : (g.comp (h.toFun.comp h')).HomotopicRel g {x} := by
    simpa only [ContinuousMap.comp_id] using (hhh'.comp_continuousMap g)
  exact h1.trans (h2.trans h3)

/-- **Homomorphisms out of `G` are realized by pointed maps out of `classifyingSpace G`.** If the
homotopy groups of `(Z, z)` vanish from degree `2` on, every homomorphism `φ : G →* π₁(Z, z)` is
induced by a pointed map `classifyingSpace G → Z` under
`classifyingSpaceFundamentalGroupMulEquiv G`. -/
theorem exists_mapOfEq_classifyingSpace (G : Type u) [Group G] {Z : Type u} [TopologicalSpace Z]
    {z : Z} (hZ : ∀ k, 2 ≤ k → Subsingleton (π_ k Z z)) (φ : G →* FundamentalGroup Z z) :
    ∃ (f : C(classifyingSpace G, Z)) (hf : f (classifyingSpaceBasepoint G) = z),
      ∀ a, FundamentalGroup.mapOfEq f hf a =
        φ (classifyingSpaceFundamentalGroupMulEquiv G a) := by
  obtain ⟨f, hf, hfπ⟩ :=
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical.exists_mapOfEq
      (hasHomotopyExtensionProperty_classifyingSpaceBasepoint G) hZ
      (φ.comp (classifyingSpaceFundamentalGroupMulEquiv G).toMonoidHom)
  exact ⟨f, hf, fun a ↦ DFunLike.congr_fun hfπ a⟩

/-- **Pointed maps out of Milnor's classifying space are determined up to pointed homotopy by
their effect on `π₁`.** The target space `Z` may live in any universe. -/
theorem homotopicRel_of_mapOfEq_eq_classifyingSpace (G : Type u) [Group G] {Z : Type v}
    [TopologicalSpace Z] (hZ : ∀ (z : Z) (n : ℕ), Subsingleton (π_ (n + 2) Z z))
    {f g : C(classifyingSpace G, Z)} {z : Z}
    (hf : f (classifyingSpaceBasepoint G) = z) (hg : g (classifyingSpaceBasepoint G) = z)
    (hfg : FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg) :
    f.HomotopicRel g {classifyingSpaceBasepoint G} :=
  (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical.homotopicRel_of_mapOfEq_eq
    (hasHomotopyExtensionProperty_classifyingSpaceBasepoint G) hZ hf hg hfg

/-- **Every pointed map between Milnor classifying spaces is pointed-homotopic to the strictly
functorial map induced by its effect on `π₁`.** The groups `G` and `H` may live in independent
universes. -/
theorem homotopicRel_classifyingSpaceMap {G : Type u} {H : Type v} [Group G] [Group H]
    (φ : G →* H) {f : C(classifyingSpace G, classifyingSpace H)}
    (hf : f (classifyingSpaceBasepoint G) = classifyingSpaceBasepoint H)
    (hfφ : ∀ a, classifyingSpaceFundamentalGroupMulEquiv H (FundamentalGroup.mapOfEq f hf a) =
      φ (classifyingSpaceFundamentalGroupMulEquiv G a)) :
    f.HomotopicRel φ.classifyingSpaceMap {classifyingSpaceBasepoint G} :=
  homotopicRel_of_mapOfEq_eq_classifyingSpace G
    (fun y n ↦ subsingleton_homotopyGroup_classifyingSpace H n y)
    hf φ.classifyingSpaceMap_basepoint <|
    MonoidHom.ext fun a ↦ (classifyingSpaceFundamentalGroupMulEquiv H).injective <| by
      rw [hfφ, φ.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq]

end UniversalProperty

section FullyFaithful

/-- **The classifying-space functor to the pointed homotopy category is fully faithful.** Its
explicit inverse on morphisms applies `PointedHomotopyCat.fundamentalGroupFunctor` and conjugates
by `classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso`. -/
def classifyingSpaceHomotopyFunctorFullyFaithful :
    classifyingSpaceHomotopyFunctor.{u}.FullyFaithful where
  preimage {G H} f :=
    classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app G ≫
      PointedHomotopyCat.fundamentalGroupFunctor.map f ≫
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app H
  map_preimage {G H} f := by
    apply (fundamentalGroupFunctor_map_bijective_classifyingSpace G
      (Y := classifyingSpaceFunctor.obj H)
      (fun y n ↦ subsingleton_homotopyGroup_classifyingSpace H n y)).1
    have hnat := classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.naturality
      (classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app G ≫
        PointedHomotopyCat.fundamentalGroupFunctor.map f ≫
        classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app H)
    refine (cancel_mono
      (classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app H)).1 ?_
    simp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj,
      Iso.hom_inv_id_app_assoc] at hnat
    exact hnat
  preimage_map {G H} φ := by
    have hnat := classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.naturality φ
    simp only [Functor.comp_map, Functor.id_map] at hnat
    rw [hnat, ← Category.assoc, Iso.inv_hom_id_app]
    exact Category.id_comp φ

/-- The classifying-space functor to the pointed homotopy category is full. -/
instance instFullClassifyingSpaceHomotopyFunctor : classifyingSpaceHomotopyFunctor.{u}.Full :=
  classifyingSpaceHomotopyFunctorFullyFaithful.full

@[simp]
theorem classifyingSpaceHomotopyFunctorFullyFaithful_preimage {G H : GrpCat.{u}}
    (f : classifyingSpaceHomotopyFunctor.obj G ⟶ classifyingSpaceHomotopyFunctor.obj H) :
    classifyingSpaceHomotopyFunctorFullyFaithful.preimage f =
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app G ≫
        PointedHomotopyCat.fundamentalGroupFunctor.map f ≫
        classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app H :=
  (rfl)

/-- The preimage of a morphism `BG ⟶ BH` under `classifyingSpaceHomotopyFunctor` is its induced
homomorphism on `π₁`, conjugated by `classifyingSpaceFundamentalGroupMulEquiv`. -/
theorem classifyingSpaceHomotopyFunctor_preimage_eq {G H : GrpCat.{u}}
    (f : classifyingSpaceHomotopyFunctor.obj G ⟶ classifyingSpaceHomotopyFunctor.obj H) :
    classifyingSpaceHomotopyFunctor.preimage f =
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app G ≫
        PointedHomotopyCat.fundamentalGroupFunctor.map f ≫
        classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app H := by
  apply classifyingSpaceHomotopyFunctor.map_injective
  rw [Functor.map_preimage]
  exact (classifyingSpaceHomotopyFunctorFullyFaithful.map_preimage f).symm

/-- **Natural bijection between pointed homotopy classes `BG ⟶ Y` and homomorphisms
`G ⟶ π₁(Y)`**, whenever the homotopy groups of `Y` vanish from degree `2` on at every point. -/
def classifyingSpaceHomEquiv (G : GrpCat.{u}) {Y : BasedTopologicalSpace.{u}}
    (hY : ∀ (y : Y.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.carrier y)) :
    (classifyingSpaceHomotopyFunctor.obj G ⟶ PointedHomotopyCat.quotient.obj Y) ≃
      (G ⟶ PointedHomotopyCat.fundamentalGroupFunctor.obj (PointedHomotopyCat.quotient.obj Y)) :=
  Equiv.ofBijective
    (fun f ↦ classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app G ≫
      PointedHomotopyCat.fundamentalGroupFunctor.map f)
    ((Iso.homCongr (classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.app G)
      (Iso.refl _)).bijective.comp (fundamentalGroupFunctor_map_bijective_classifyingSpace G hY))

@[simp]
theorem classifyingSpaceHomEquiv_apply (G : GrpCat.{u}) {Y : BasedTopologicalSpace.{u}}
    (hY : ∀ (y : Y.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.carrier y))
    (f : classifyingSpaceHomotopyFunctor.obj G ⟶ PointedHomotopyCat.quotient.obj Y) :
    classifyingSpaceHomEquiv G hY f =
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app G ≫
        PointedHomotopyCat.fundamentalGroupFunctor.map f :=
  (rfl)

/-- Naturality of `classifyingSpaceHomEquiv` in the group variable. -/
theorem classifyingSpaceHomEquiv_comp_left {G H : GrpCat.{u}} {Y : BasedTopologicalSpace.{u}}
    (hY : ∀ (y : Y.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.carrier y))
    (φ : G ⟶ H) (f : classifyingSpaceHomotopyFunctor.obj H ⟶ PointedHomotopyCat.quotient.obj Y) :
    classifyingSpaceHomEquiv G hY (classifyingSpaceHomotopyFunctor.map φ ≫ f) =
      φ ≫ classifyingSpaceHomEquiv H hY f := by
  simp only [classifyingSpaceHomEquiv_apply, Functor.map_comp, ← Category.assoc]
  congr 1
  simpa only [Functor.id_map, Functor.comp_map] using
    (classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.naturality φ).symm

/-- Naturality of `classifyingSpaceHomEquiv` in the target space. -/
theorem classifyingSpaceHomEquiv_comp_right (G : GrpCat.{u}) {Y Z : BasedTopologicalSpace.{u}}
    (hY : ∀ (y : Y.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.carrier y))
    (hZ : ∀ (z : Z.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Z.carrier z))
    (f : classifyingSpaceHomotopyFunctor.obj G ⟶ PointedHomotopyCat.quotient.obj Y)
    (g : PointedHomotopyCat.quotient.obj Y ⟶ PointedHomotopyCat.quotient.obj Z) :
    classifyingSpaceHomEquiv G hZ (f ≫ g) =
      classifyingSpaceHomEquiv G hY f ≫ PointedHomotopyCat.fundamentalGroupFunctor.map g := by
  simp only [classifyingSpaceHomEquiv_apply, Functor.map_comp, Category.assoc]

end FullyFaithful

section PointedUniquenessAndEquivalence

/-- **Pointed uniqueness of well-pointed aspherical spaces of CW type.** Between any two
aspherical spaces of CW type whose base points have the homotopy extension property, every
isomorphism `φ : π₁(X) ≃* π₁(Y)` is induced by a **unique** isomorphism in
`TauCeti.PointedHomotopyCat`. -/
theorem existsUnique_iso_of_isAspherical {X Y : BasedTopologicalSpace.{u}}
    [CWType X.carrier] [CWType Y.carrier]
    (hX : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (hY : HasHomotopyExtensionProperty ({Y.basepoint} : Set Y.carrier))
    (hX' : IsAspherical X.carrier X.basepoint) (hY' : IsAspherical Y.carrier Y.basepoint)
    (φ : FundamentalGroup X.carrier X.basepoint ≃* FundamentalGroup Y.carrier Y.basepoint) :
    ∃! e : PointedHomotopyCat.quotient.obj X ≅ PointedHomotopyCat.quotient.obj Y,
      (PointedHomotopyCat.fundamentalGroupFunctor.map e.hom).hom = φ.toMonoidHom := by
  have hXπ : ∀ (x : X.carrier) (n : ℕ), Subsingleton (π_ (n + 2) X.carrier x) :=
    fun x n ↦ (hX'.of_basepoint x).subsingleton_homotopyGroup n
  have hYπ : ∀ (y : Y.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.carrier y) :=
    fun y n ↦ (hY'.of_basepoint y).subsingleton_homotopyGroup n
  have hXY := fundamentalGroupFunctor_map_bijective_of_isAspherical hX hX' hYπ
  have hYX := fundamentalGroupFunctor_map_bijective_of_isAspherical hY hY' hXπ
  have hXX := fundamentalGroupFunctor_map_bijective_of_isAspherical hX hX' hXπ
  have hYY := fundamentalGroupFunctor_map_bijective_of_isAspherical hY hY' hYπ
  let φIso : PointedHomotopyCat.fundamentalGroupFunctor.obj (PointedHomotopyCat.quotient.obj X) ≅
      PointedHomotopyCat.fundamentalGroupFunctor.obj (PointedHomotopyCat.quotient.obj Y) :=
    MulEquiv.toGrpIso φ
  obtain ⟨f, hf⟩ := hXY.2 φIso.hom
  obtain ⟨g, hg⟩ := hYX.2 φIso.inv
  have hfg : f ≫ g = 𝟙 _ := hXX.1 <| by
    rw [Functor.map_comp, hf, hg, CategoryTheory.Functor.map_id]
    exact φIso.hom_inv_id
  have hgf : g ≫ f = 𝟙 _ := hYY.1 <| by
    rw [Functor.map_comp, hg, hf, CategoryTheory.Functor.map_id]
    exact φIso.inv_hom_id
  refine ⟨⟨f, g, hfg, hgf⟩, congrArg GrpCat.Hom.hom hf, fun e he ↦ Iso.ext <| hXY.1 ?_⟩
  rw [hf]
  exact GrpCat.hom_ext he

/-- **Every well-pointed `K(G, 1)` of CW type is uniquely isomorphic to `classifyingSpace G` in
the pointed homotopy category**, compatibly with a prescribed identification of its fundamental
group with `G`. -/
theorem existsUnique_iso_classifyingSpace {X : BasedTopologicalSpace.{u}} [CWType X.carrier]
    (hX : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (hX' : IsAspherical X.carrier X.basepoint) {G : GrpCat.{u}}
    (eX : FundamentalGroup X.carrier X.basepoint ≃* G) :
    ∃! e : PointedHomotopyCat.quotient.obj X ≅ classifyingSpaceHomotopyFunctor.obj G,
      ∀ a, classifyingSpaceFundamentalGroupMulEquiv G
        ((PointedHomotopyCat.fundamentalGroupFunctor.map e.hom).hom a) = eX a := by
  dsimp only [classifyingSpaceHomotopyFunctor, Functor.comp_obj]
  let : CWType (classifyingSpaceFunctor.obj G).carrier :=
    inferInstanceAs (CWType (classifyingSpace G))
  obtain ⟨e, he, huniq⟩ := existsUnique_iso_of_isAspherical
    (X := X) (Y := classifyingSpaceFunctor.obj G) hX
    (hasHomotopyExtensionProperty_classifyingSpaceBasepoint G) hX'
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical
    (eX.trans (classifyingSpaceFundamentalGroupMulEquiv G).symm)
  refine ⟨e, fun a ↦ ?_, fun e' he' ↦ huniq e' <| MonoidHom.ext fun a ↦
    (classifyingSpaceFundamentalGroupMulEquiv G).injective ?_⟩
  · rw [he]
    exact MulEquiv.apply_symm_apply (classifyingSpaceFundamentalGroupMulEquiv G) (eX a)
  · exact (he' a).trans
      (MulEquiv.apply_symm_apply (classifyingSpaceFundamentalGroupMulEquiv G) (eX a)).symm

/-- **Every well-pointed aspherical space of CW type lies in the essential image of
`classifyingSpaceHomotopyFunctor`.** -/
theorem mem_essImage_classifyingSpaceHomotopyFunctor_of_isAspherical
    {X : BasedTopologicalSpace.{u}} [CWType X.carrier]
    (hX : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (hX' : IsAspherical X.carrier X.basepoint) :
    classifyingSpaceHomotopyFunctor.essImage (PointedHomotopyCat.quotient.obj X) := by
  obtain ⟨e, -, -⟩ := existsUnique_iso_classifyingSpace hX hX'
    (G := GrpCat.of (FundamentalGroup X.carrier X.basepoint)) (MulEquiv.refl _)
  exact ⟨GrpCat.of (FundamentalGroup X.carrier X.basepoint), ⟨e.symm⟩⟩

/-- **Every Hausdorff CW `K(G, 1)` based at a `0`-cell lies in the essential image of
`classifyingSpaceHomotopyFunctor`.** -/
theorem mem_essImage_classifyingSpaceHomotopyFunctor_of_cwComplex {X : Type u}
    [TopologicalSpace X] [T2Space X] [Topology.CWComplex (Set.univ : Set X)] {x : X}
    (hx : x ∈ (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) 1 : Set X))
    (hX : IsAspherical X x) :
    classifyingSpaceHomotopyFunctor.essImage (PointedHomotopyCat.quotient.obj ⟨X, x⟩) :=
  mem_essImage_classifyingSpaceHomotopyFunctor_of_isAspherical
    (hasHomotopyExtensionProperty_singleton_of_mem_skeletonLT_one hx) hX

/-- Every space in the essential image of `classifyingSpaceHomotopyFunctor` has CW type. -/
theorem cwType_of_mem_essImage_classifyingSpaceHomotopyFunctor {X : BasedTopologicalSpace.{u}}
    (hX : classifyingSpaceHomotopyFunctor.essImage (PointedHomotopyCat.quotient.obj X)) :
    CWType X.carrier := by
  let : CWType (classifyingSpaceFunctor.obj hX.witness).carrier :=
    inferInstanceAs (CWType (classifyingSpace hX.witness))
  exact (PointedHomotopyCat.homotopyEquivOfIso hX.getIso.symm).cwType

/-- Every space in the essential image of `classifyingSpaceHomotopyFunctor` is aspherical at its
base point. -/
theorem isAspherical_of_mem_essImage_classifyingSpaceHomotopyFunctor
    {X : BasedTopologicalSpace.{u}}
    (hX : classifyingSpaceHomotopyFunctor.essImage (PointedHomotopyCat.quotient.obj X)) :
    IsAspherical X.carrier X.basepoint := by
  set he := PointedHomotopyCat.homotopyEquivOfIso hX.getIso
  have hbp := PointedHomotopyCat.homotopyEquivOfIso_toFun_basepoint hX.getIso
  rw [classifyingSpaceFunctor_obj_basepoint] at hbp
  have hasph := (he.isWeakHomotopyEquivalence.isAspherical_iff
    (classifyingSpaceBasepoint hX.witness)).1
    (isEilenbergMacLaneSpaceOne_classifyingSpace hX.witness).isAspherical
  rwa [hbp] at hasph

/-- **Pointed maps out of any object in the essential image of `classifyingSpaceHomotopyFunctor`
into a space without higher homotopy groups are classified by `π₁`.** -/
theorem fundamentalGroupFunctor_map_bijective_of_mem_essImage {X : PointedHomotopyCat.{u}}
    (hX : classifyingSpaceHomotopyFunctor.essImage X) {Y : BasedTopologicalSpace.{u}}
    (hY : ∀ (y : Y.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.carrier y)) :
    Function.Bijective (PointedHomotopyCat.fundamentalGroupFunctor.map
      (X := X) (Y := PointedHomotopyCat.quotient.obj Y)) :=
  bijective_fundamentalGroupFunctor_map_of_iso hX.getIso
    (fundamentalGroupFunctor_map_bijective_classifyingSpace hX.witness hY)

/-- Morphisms from `BG` into any object of the essential image of `classifyingSpaceHomotopyFunctor`
are determined by their effect on `π₁`. -/
private theorem injective_fundamentalGroupFunctor_map_of_mem_essImage {G : GrpCat.{u}}
    {Y : PointedHomotopyCat.{u}} (hY : classifyingSpaceHomotopyFunctor.essImage Y) :
    Function.Injective (PointedHomotopyCat.fundamentalGroupFunctor.map
      (X := classifyingSpaceHomotopyFunctor.obj G) (Y := Y)) := by
  intro f g hfg
  have hcomp : PointedHomotopyCat.fundamentalGroupFunctor.map (f ≫ hY.getIso.inv) =
      PointedHomotopyCat.fundamentalGroupFunctor.map (g ≫ hY.getIso.inv) := by
    rw [Functor.map_comp, Functor.map_comp, hfg]
  rw [← cancel_mono hY.getIso.inv]
  exact (fundamentalGroupFunctor_map_bijective_classifyingSpace G
    (Y := classifyingSpaceFunctor.obj hY.witness)
    (fun y n ↦ subsingleton_homotopyGroup_classifyingSpace hY.witness n y)).1 hcomp

/-- The fundamental-group action of the canonical isomorphism `B(π₁ X) ≅ X` for `X` in the
essential image of `classifyingSpaceHomotopyFunctor`. -/
private theorem fundamentalGroupFunctor_map_counitApp
    (X : classifyingSpaceHomotopyFunctor.{u}.EssImageSubcategory) :
    PointedHomotopyCat.fundamentalGroupFunctor.map
        ((classifyingSpaceHomotopyFunctor.mapIso
            (PointedHomotopyCat.fundamentalGroupFunctor.mapIso X.property.getIso.symm ≪≫
              classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.app
                X.property.witness) ≪≫
          X.property.getIso).hom) =
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app
        (PointedHomotopyCat.fundamentalGroupFunctor.obj X.obj) := by
  set e : classifyingSpaceHomotopyFunctor.obj X.property.witness ≅ X.obj := X.property.getIso
  set α : PointedHomotopyCat.fundamentalGroupFunctor.obj X.obj ≅ X.property.witness :=
    PointedHomotopyCat.fundamentalGroupFunctor.mapIso e.symm ≪≫
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.app X.property.witness
  have h : PointedHomotopyCat.fundamentalGroupFunctor.map
      (classifyingSpaceHomotopyFunctor.map α.hom) =
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app
          (PointedHomotopyCat.fundamentalGroupFunctor.obj X.obj) ≫
        α.hom ≫
        classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app
          X.property.witness :=
    (Iso.eq_comp_inv
      (classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.app
        X.property.witness)).2 <| by
      simpa only [Functor.comp_map, Functor.id_map, Iso.app_hom, Category.assoc] using
        classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.naturality α.hom
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp]
  rw [h]
  simp only [α, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc,
    Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.symm_hom, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Functor.id_obj, Category.comp_id]

/-- **Equivalence between groups and classifying spaces in the pointed homotopy category.** The
classifying-space functor and the fundamental-group functor form an equivalence between `GrpCat`
and the essential image subcategory `classifyingSpaceHomotopyFunctor.EssImageSubcategory` in
`PointedHomotopyCat`, which contains every well-pointed aspherical space of CW type
(`TauCeti.mem_essImage_classifyingSpaceHomotopyFunctor_of_isAspherical`). -/
@[expose] def classifyingSpaceEquivalence :
    GrpCat.{u} ≌ classifyingSpaceHomotopyFunctor.{u}.EssImageSubcategory where
  functor := classifyingSpaceHomotopyFunctor.toEssImage
  inverse := classifyingSpaceHomotopyFunctor.essImage.ι ⋙
    PointedHomotopyCat.fundamentalGroupFunctor
  unitIso :=
    NatIso.ofComponents
      (fun G ↦ (classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.app G).symm)
      (fun φ ↦ classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.naturality φ)
  counitIso :=
    NatIso.ofComponents
      (fun X ↦ classifyingSpaceHomotopyFunctor.essImage.isoMk
        (classifyingSpaceHomotopyFunctor.mapIso
            (PointedHomotopyCat.fundamentalGroupFunctor.mapIso X.property.getIso.symm ≪≫
              classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.app
                X.property.witness) ≪≫
          X.property.getIso))
      (fun {X Y} f ↦ by
        apply classifyingSpaceHomotopyFunctor.essImage.ι.map_injective
        apply injective_fundamentalGroupFunctor_map_of_mem_essImage Y.property
        simp only [Functor.comp_map, Functor.id_map, ObjectProperty.ι_map, ObjectProperty.isoMk_hom,
          ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
          Functor.toEssImage_map_hom, Functor.map_comp]
        rw [fundamentalGroupFunctor_map_counitApp X, fundamentalGroupFunctor_map_counitApp Y]
        simpa only [Functor.comp_map, Functor.id_map] using
          classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.naturality
            (PointedHomotopyCat.fundamentalGroupFunctor.map f.hom))
  functor_unitIso_comp G := by
    apply classifyingSpaceHomotopyFunctor.essImage.ι.map_injective
    apply injective_fundamentalGroupFunctor_map_of_mem_essImage
      (classifyingSpaceHomotopyFunctor.toEssImage.obj G).property
    simp only [ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.FullSubcategory.id_hom, NatIso.ofComponents_hom_app, Iso.symm_hom,
      Iso.app_inv, ObjectProperty.isoMk_hom, Functor.toEssImage_map_hom, ObjectProperty.homMk_hom,
      Functor.map_comp]
    rw [fundamentalGroupFunctor_map_counitApp]
    have hnat := classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.naturality
      (classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app G)
    simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj,
      Functor.toEssImage_obj_obj, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id] using hnat

@[simp]
theorem classifyingSpaceEquivalence_functor :
    classifyingSpaceEquivalence.{u}.functor = classifyingSpaceHomotopyFunctor.toEssImage :=
  (rfl)

@[simp]
theorem classifyingSpaceEquivalence_inverse :
    classifyingSpaceEquivalence.{u}.inverse =
      classifyingSpaceHomotopyFunctor.essImage.ι ⋙ PointedHomotopyCat.fundamentalGroupFunctor :=
  (rfl)

@[simp]
theorem classifyingSpaceEquivalence_unitIso_hom_app (G : GrpCat.{u}) :
    classifyingSpaceEquivalence.unitIso.hom.app G =
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.inv.app G :=
  (rfl)

@[simp]
theorem classifyingSpaceEquivalence_unitIso_inv_app (G : GrpCat.{u}) :
    classifyingSpaceEquivalence.unitIso.inv.app G =
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app G :=
  (rfl)

/-- The counit of `classifyingSpaceEquivalence` induces
`classifyingSpaceFundamentalGroupMulEquiv` on fundamental groups. -/
@[simp]
theorem fundamentalGroupFunctor_map_classifyingSpaceEquivalence_counitIso_hom_app
    (X : classifyingSpaceHomotopyFunctor.{u}.EssImageSubcategory) :
    PointedHomotopyCat.fundamentalGroupFunctor.map
        (classifyingSpaceEquivalence.counitIso.hom.app X).hom =
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app
        (PointedHomotopyCat.fundamentalGroupFunctor.obj X.obj) :=
  fundamentalGroupFunctor_map_counitApp X

end PointedUniquenessAndEquivalence

end TauCeti
