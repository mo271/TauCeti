/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pushforward.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Skyscraper
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Stalks of a pulled-back sheaf of modules

Let `f : Y ⟶ X` be a continuous map of topological spaces, `𝒪X` and `𝒪Y` sheaves of
commutative rings on `X` and `Y`, and `φ : 𝒪X ⟶ f_* 𝒪Y` a morphism of the underlying sheaves of
rings. For every point `y : Y`, the morphism `φ` induces a ring homomorphism on stalks
`SheafOfModules.ringStalkMap φ y : 𝒪X_{f y} ⟶ 𝒪Y_y`.

This file constructs the canonical natural isomorphism
`SheafOfModules.pullbackStalkIso φ y`, identifying the stalk `(φ^* G)_y` of the pulled-back sheaf
of modules with the base change `𝒪Y_y ⊗_{𝒪X_{f y}} G_{f y}` along `ringStalkMap φ y`, naturally
in `G : SheafOfModules (ringCatSheaf 𝒪X)`.

The isomorphism is obtained from uniqueness of left adjoints
(`CategoryTheory.Adjunction.leftAdjointUniq`): the pushforward of the skyscraper sheaf at `y` is
canonically the skyscraper sheaf at `f y` of the restricted module
(`SheafOfModules.pushforwardSkyscraperIso`), so both
`stalkFunctorCommRing 𝒪X (f y) ⋙ ModuleCat.extendScalars (ringStalkMap φ y).hom` and
`pullback φ ⋙ stalkFunctorCommRing 𝒪Y y` are left adjoint to the same composite right adjoint.
On generators, `pullbackStalkIso φ y` sends `a ⊗ₜ germ_U(m)` to `a • germ_{f⁻¹ U}(η_G(m))`,
where `η_G : G ⟶ φ_* φ^* G` is the unit of the pullback--pushforward adjunction
(`SheafOfModules.pullbackStalkIso_hom_app_tmul_germ`). At the structure sheaf `G = 𝒪X`, composing
with the unit comparison `pullbackObjUnitToUnit φ` recovers multiplication by `φ` on germs
(`SheafOfModules.pullbackStalkIso_hom_app_unit_comp_pullbackObjUnitToUnit`).

## Main declarations

* `SheafOfModules.ringStalkMap`: the induced homomorphism `𝒪X_{f y} ⟶ 𝒪Y_y` on ring stalks,
  characterized on germs by `SheafOfModules.ringStalkMap_germ`;
* `SheafOfModules.pushforwardSkyscraperIso`: pushforward of a skyscraper module sheaf at `y` is
  the skyscraper module sheaf at `f y` of the scalar-restricted module;
* `SheafOfModules.pullbackStalkIso`: natural isomorphism
  `stalkFunctorCommRing 𝒪X (f y) ⋙ ModuleCat.extendScalars (ringStalkMap φ y).hom ≅`
  `pullback φ ⋙ stalkFunctorCommRing 𝒪Y y`;
* `SheafOfModules.pullbackStalkIso_hom_app_tmul_germ`: formula on pure tensors `a ⊗ₜ germ(m)`;
* `SheafOfModules.pullbackStalkIso_hom_app_unit_comp_pullbackObjUnitToUnit`: compatibility with
  the structure-sheaf comparison `SheafOfModules.pullbackObjUnitToUnit`.

## References

* The Stacks Project, *Modules on Ringed Spaces*, Lemma 0098 (stalks of pullbacks of modules).
-/

public section

open CategoryTheory TopologicalSpace Opposite TopCat.Presheaf TauCeti.SheafOfModules
open scoped ChangeOfRings

universe u

noncomputable section

namespace SheafOfModules

variable {X Y : TopCat.{u}} {f : Y ⟶ X}
  {𝒪X : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {𝒪Y : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}}
  (φ : ringCatSheaf 𝒪X ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Y))
  (y : Y)

/-- The ring homomorphism `𝒪X_{f y} ⟶ 𝒪Y_y` on stalks induced by a morphism of ringed spaces
`φ : 𝒪X ⟶ f_* 𝒪Y`. -/
def ringStalkMap :
    TopCat.Presheaf.stalk 𝒪X.obj (f y) ⟶ TopCat.Presheaf.stalk 𝒪Y.obj y :=
  (TopCat.Presheaf.stalkFunctor CommRingCat.{u} (f y)).map
      (commRingCatHom (S := 𝒪X) (R := 𝒪Y) (F := Opens.map f) φ) ≫
    TopCat.Presheaf.stalkPushforward CommRingCat.{u} f 𝒪Y.obj y

/-- On germs, `ringStalkMap` applies `φ` on sections and takes the germ at `y`. -/
@[simp]
theorem ringStalkMap_germ (U : Opens X) (hy : f y ∈ U) (r : 𝒪X.obj.obj (op U)) :
    ringStalkMap φ y (TopCat.Presheaf.germ 𝒪X.obj U (f y) hy r) =
      TopCat.Presheaf.germ 𝒪Y.obj ((Opens.map f).obj U) y hy (φ.hom.app (op U) r) := by
  dsimp only [ringStalkMap]
  erw [ConcreteCategory.comp_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkPushforward_germ_apply]
  rfl

/-- Forward direction of the sectionwise isomorphism identifying sections of the pushforward of a
skyscraper sheaf at `y` with sections of the skyscraper sheaf at `f y`. -/
private def pushforwardSkyscraperSectionHom
    (T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) (U : Opens X) :
    ((pushforward.{u} φ).obj ((skyscraperFunctorCommRing 𝒪Y y).obj T)).val.obj (op U) ⟶
      ((skyscraperFunctorCommRing 𝒪X (f y)).obj
        ((ModuleCat.restrictScalars (ringStalkMap φ y).hom).obj T)).val.obj (op U) :=
  let TR : ModuleCat.{u} ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) :=
    (ModuleCat.restrictScalars (ringStalkMap φ y).hom).obj T
  let eX := skyscraperSectionCommRingEquiv 𝒪X (f y) TR U
  let eY := skyscraperSectionCommRingEquiv 𝒪Y y T ((Opens.map f).obj U)
  let toY :
      ((pushforward.{u} φ).obj ((skyscraperFunctorCommRing 𝒪Y y).obj T)).val.obj (op U) →
        ((skyscraperFunctorCommRing 𝒪Y y).obj T).val.obj (op ((Opens.map f).obj U)) := id
  ModuleCat.ofHom
    (X := ((pushforward.{u} φ).obj ((skyscraperFunctorCommRing 𝒪Y y).obj T)).val.obj (op U))
    (Y := ((skyscraperFunctorCommRing 𝒪X (f y)).obj TR).val.obj (op U))
    { toFun := fun s ↦ eX.symm (fun hy ↦ eY (toY s) hy)
      map_add' := fun s₁ s₂ ↦ by
        apply eX.injective
        funext hy
        erw [skyscraperSectionCommRingEquiv_add, eX.apply_symm_apply, eX.apply_symm_apply,
          eX.apply_symm_apply]
        exact skyscraperSectionCommRingEquiv_add 𝒪Y y T ((Opens.map f).obj U)
          (toY s₁) (toY s₂) hy
      map_smul' := fun r s ↦ by
        apply eX.injective
        funext hy
        rw [RingHom.id_apply]
        let r' : 𝒪Y.obj.obj (op ((Opens.map f).obj U)) := φ.hom.app (op U) r
        change eX (eX.symm (fun hy ↦ eY (r' • toY s) hy)) hy =
          eX (r • eX.symm (fun hy ↦ eY (toY s) hy)) hy
        erw [eX.apply_symm_apply, skyscraperSectionCommRingEquiv_smul 𝒪X (f y) TR U,
          eX.apply_symm_apply,
          skyscraperSectionCommRingEquiv_smul 𝒪Y y T ((Opens.map f).obj U)]
        change TopCat.Presheaf.germ 𝒪Y.obj ((Opens.map f).obj U) y hy r' •
            (eY (toY s) hy : T) =
          ringStalkMap φ y (TopCat.Presheaf.germ 𝒪X.obj U (f y) hy r) •
            (eY (toY s) hy : T)
        erw [ringStalkMap_germ] }

/-- Inverse direction of the sectionwise isomorphism identifying sections of the pushforward of a
skyscraper sheaf at `y` with sections of the skyscraper sheaf at `f y`. -/
private def pushforwardSkyscraperSectionInv
    (T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) (U : Opens X) :
    ((skyscraperFunctorCommRing 𝒪X (f y)).obj
        ((ModuleCat.restrictScalars (ringStalkMap φ y).hom).obj T)).val.obj (op U) ⟶
      ((pushforward.{u} φ).obj ((skyscraperFunctorCommRing 𝒪Y y).obj T)).val.obj (op U) :=
  let TR : ModuleCat.{u} ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) :=
    (ModuleCat.restrictScalars (ringStalkMap φ y).hom).obj T
  let eX := skyscraperSectionCommRingEquiv 𝒪X (f y) TR U
  let eY := skyscraperSectionCommRingEquiv 𝒪Y y T ((Opens.map f).obj U)
  let fromY :
      ((skyscraperFunctorCommRing 𝒪Y y).obj T).val.obj (op ((Opens.map f).obj U)) →
        ((pushforward.{u} φ).obj ((skyscraperFunctorCommRing 𝒪Y y).obj T)).val.obj (op U) := id
  ModuleCat.ofHom
    (X := ((skyscraperFunctorCommRing 𝒪X (f y)).obj TR).val.obj (op U))
    (Y := ((pushforward.{u} φ).obj ((skyscraperFunctorCommRing 𝒪Y y).obj T)).val.obj (op U))
    { toFun := fun s ↦ fromY (eY.symm (fun hy ↦ eX s hy))
      map_add' := fun s₁ s₂ ↦ by
        apply eY.injective
        funext hy
        change eY (eY.symm (fun hy ↦ eX (s₁ + s₂) hy)) hy =
          eY (eY.symm (fun hy ↦ eX s₁ hy) + eY.symm (fun hy ↦ eX s₂ hy)) hy
        erw [eY.apply_symm_apply,
          skyscraperSectionCommRingEquiv_add 𝒪Y y T ((Opens.map f).obj U),
          eY.apply_symm_apply, eY.apply_symm_apply]
        exact skyscraperSectionCommRingEquiv_add 𝒪X (f y) TR U s₁ s₂ hy
      map_smul' := fun r s ↦ by
        apply eY.injective
        funext hy
        rw [RingHom.id_apply]
        let r' : 𝒪Y.obj.obj (op ((Opens.map f).obj U)) := φ.hom.app (op U) r
        change eY (eY.symm (fun hy ↦ eX (r • s) hy)) hy =
          eY (r' • eY.symm (fun hy ↦ eX s hy)) hy
        erw [eY.apply_symm_apply, skyscraperSectionCommRingEquiv_smul 𝒪X (f y) TR U,
          skyscraperSectionCommRingEquiv_smul 𝒪Y y T ((Opens.map f).obj U),
          eY.apply_symm_apply]
        change ringStalkMap φ y (TopCat.Presheaf.germ 𝒪X.obj U (f y) hy r) •
            (eX s hy : T) =
          TopCat.Presheaf.germ 𝒪Y.obj ((Opens.map f).obj U) y hy r' •
            (eX s hy : T)
        erw [ringStalkMap_germ] }

/-- The sectionwise module isomorphism identifying sections over `U` of the pushforward of a
skyscraper sheaf at `y` with sections over `U` of the skyscraper sheaf at `f y` of the
scalar-restricted module. -/
private def pushforwardSkyscraperSectionIso
    (T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) (U : Opens X) :
    ((pushforward.{u} φ).obj ((skyscraperFunctorCommRing 𝒪Y y).obj T)).val.obj (op U) ≅
      ((skyscraperFunctorCommRing 𝒪X (f y)).obj
        ((ModuleCat.restrictScalars (ringStalkMap φ y).hom).obj T)).val.obj (op U) where
  hom := pushforwardSkyscraperSectionHom φ y T U
  inv := pushforwardSkyscraperSectionInv φ y T U
  hom_inv_id := by
    let TR : ModuleCat.{u} ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) :=
      (ModuleCat.restrictScalars (ringStalkMap φ y).hom).obj T
    let eX := skyscraperSectionCommRingEquiv 𝒪X (f y) TR U
    let eY := skyscraperSectionCommRingEquiv 𝒪Y y T ((Opens.map f).obj U)
    ext s
    apply eY.injective
    funext hy
    let s' : ((skyscraperFunctorCommRing 𝒪Y y).obj T).val.obj (op ((Opens.map f).obj U)) := s
    change eY (eY.symm (fun hy ↦ eX (eX.symm (fun hy ↦ eY s' hy)) hy)) hy = eY s' hy
    erw [eY.apply_symm_apply, eX.apply_symm_apply]
  inv_hom_id := by
    let TR : ModuleCat.{u} ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) :=
      (ModuleCat.restrictScalars (ringStalkMap φ y).hom).obj T
    let eX := skyscraperSectionCommRingEquiv 𝒪X (f y) TR U
    let eY := skyscraperSectionCommRingEquiv 𝒪Y y T ((Opens.map f).obj U)
    ext s
    apply eX.injective
    funext hy
    change eX (eX.symm (fun hy ↦ eY (eY.symm (fun hy ↦ eX s hy)) hy)) hy = eX s hy
    erw [eX.apply_symm_apply, eY.apply_symm_apply]

/-- Objectwise isomorphism identifying the pushforward of a skyscraper module sheaf at `y` with the
skyscraper sheaf at `f y` of the scalar-restricted module. -/
private def pushforwardSkyscraperObjIso
    (T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) :
    (pushforward.{u} φ).obj ((skyscraperFunctorCommRing 𝒪Y y).obj T) ≅
      (skyscraperFunctorCommRing 𝒪X (f y)).obj
        ((ModuleCat.restrictScalars (ringStalkMap φ y).hom).obj T) :=
  (fullyFaithfulForget (ringCatSheaf 𝒪X)).preimageIso
    (PresheafOfModules.isoMk
      (fun U ↦ pushforwardSkyscraperSectionIso φ y T U.unop)
      (fun {U V} i ↦ by
        induction U with | op U =>
        induction V with | op V =>
        let TR : ModuleCat.{u} ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) :=
          (ModuleCat.restrictScalars (ringStalkMap φ y).hom).obj T
        let eXV := skyscraperSectionCommRingEquiv 𝒪X (f y) TR V
        let eXU := skyscraperSectionCommRingEquiv 𝒪X (f y) TR U
        let eYV := skyscraperSectionCommRingEquiv 𝒪Y y T ((Opens.map f).obj V)
        let eYU := skyscraperSectionCommRingEquiv 𝒪Y y T ((Opens.map f).obj U)
        ext s
        let s' :
            ((skyscraperFunctorCommRing 𝒪Y y).obj T).val.obj (op ((Opens.map f).obj U)) := s
        apply eXV.injective
        funext hy
        change eXV (eXV.symm (fun hy ↦ eYV
            (((skyscraperFunctorCommRing 𝒪Y y).obj T).val.map
              ((Opens.map f).map i.unop).op s') hy)) hy =
          eXV (((skyscraperFunctorCommRing 𝒪X (f y)).obj TR).val.map i.unop.op
            (eXU.symm (fun hy ↦ eYU s' hy))) hy
        erw [eXV.apply_symm_apply, skyscraperSectionCommRingEquiv_map 𝒪Y y T,
          skyscraperSectionCommRingEquiv_map 𝒪X (f y), eXU.apply_symm_apply]
        rfl))

/-- Naturality of `pushforwardSkyscraperObjIso` in the module `T`. -/
private lemma pushforwardSkyscraperObjIso_naturality
    {T₁ T₂ : ModuleCat.{u} ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)} (g : T₁ ⟶ T₂) :
    (pushforward.{u} φ).map ((skyscraperFunctorCommRing 𝒪Y y).map g) ≫
        (pushforwardSkyscraperObjIso φ y T₂).hom =
      (pushforwardSkyscraperObjIso φ y T₁).hom ≫
        (skyscraperFunctorCommRing 𝒪X (f y)).map
          ((ModuleCat.restrictScalars (ringStalkMap φ y).hom).map g) := by
  ext U s
  induction U with | op U =>
  let TR₁ : ModuleCat.{u} ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) :=
    (ModuleCat.restrictScalars (ringStalkMap φ y).hom).obj T₁
  let TR₂ : ModuleCat.{u} ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) :=
    (ModuleCat.restrictScalars (ringStalkMap φ y).hom).obj T₂
  let eX₁ := skyscraperSectionCommRingEquiv 𝒪X (f y) TR₁ U
  let eX₂ := skyscraperSectionCommRingEquiv 𝒪X (f y) TR₂ U
  let eY₁ := skyscraperSectionCommRingEquiv 𝒪Y y T₁ ((Opens.map f).obj U)
  let eY₂ := skyscraperSectionCommRingEquiv 𝒪Y y T₂ ((Opens.map f).obj U)
  let s' : ((skyscraperFunctorCommRing 𝒪Y y).obj T₁).val.obj (op ((Opens.map f).obj U)) := s
  apply eX₂.injective
  funext hy
  change eX₂ (eX₂.symm (fun hy ↦ eY₂
      (((skyscraperFunctorCommRing 𝒪Y y).map g).val.app (op ((Opens.map f).obj U)) s') hy)) hy =
    eX₂ (((skyscraperFunctorCommRing 𝒪X (f y)).map
      ((ModuleCat.restrictScalars (ringStalkMap φ y).hom).map g)).val.app (op U)
      (eX₁.symm (fun hy ↦ eY₁ s' hy))) hy
  erw [eX₂.apply_symm_apply,
    skyscraperSectionCommRingEquiv_skyscraperFunctorCommRing_map 𝒪Y y g,
    skyscraperSectionCommRingEquiv_skyscraperFunctorCommRing_map 𝒪X (f y),
    eX₁.apply_symm_apply]
  rfl

/-- Pushing forward a skyscraper module sheaf at `y` along `φ : 𝒪X ⟶ f_* 𝒪Y` yields the
skyscraper module sheaf at `f y` of the module obtained by restricting scalars along
`ringStalkMap φ y`. -/
def pushforwardSkyscraperIso :
    skyscraperFunctorCommRing 𝒪Y y ⋙ pushforward.{u} φ ≅
      ModuleCat.restrictScalars (ringStalkMap φ y).hom ⋙
        skyscraperFunctorCommRing 𝒪X (f y) :=
  NatIso.ofComponents (pushforwardSkyscraperObjIso φ y)
    (fun g ↦ pushforwardSkyscraperObjIso_naturality φ y g)

/-- On sections over `U`, `pushforwardSkyscraperIso.hom` identifies sections of the pushforward
skyscraper sheaf at `y` with sections of the skyscraper sheaf at `f y`. -/
theorem skyscraperSectionCommRingEquiv_pushforwardSkyscraperIso_hom_app
    (T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) (U : Opens X)
    (s : ((pushforward.{u} φ).obj ((skyscraperFunctorCommRing 𝒪Y y).obj T)).val.obj (op U))
    (hy : f y ∈ U) :
    skyscraperSectionCommRingEquiv 𝒪X (f y)
        ((ModuleCat.restrictScalars (ringStalkMap φ y).hom).obj T) U
        (((pushforwardSkyscraperIso φ y).hom.app T).val.app (op U) s) hy =
      skyscraperSectionCommRingEquiv 𝒪Y y T ((Opens.map f).obj U) s hy := by
  let TR : ModuleCat.{u} ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) :=
    (ModuleCat.restrictScalars (ringStalkMap φ y).hom).obj T
  change skyscraperSectionCommRingEquiv 𝒪X (f y) TR U
      ((skyscraperSectionCommRingEquiv 𝒪X (f y) TR U).symm
        (skyscraperSectionCommRingEquiv 𝒪Y y T ((Opens.map f).obj U) s)) hy = _
  exact congrFun (Equiv.apply_symm_apply _ _) hy

/-- On sections over `U`, `pushforwardSkyscraperIso.inv` identifies sections of the skyscraper
sheaf at `f y` with sections of the pushforward skyscraper sheaf at `y`. -/
theorem skyscraperSectionCommRingEquiv_pushforwardSkyscraperIso_inv_app
    (T : ModuleCat.{u} ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) (U : Opens X)
    (s : ((skyscraperFunctorCommRing 𝒪X (f y)).obj
      ((ModuleCat.restrictScalars (ringStalkMap φ y).hom).obj T)).val.obj (op U))
    (hy : f y ∈ U) :
    skyscraperSectionCommRingEquiv 𝒪Y y T ((Opens.map f).obj U)
        (((pushforwardSkyscraperIso φ y).inv.app T).val.app (op U) s) hy =
      skyscraperSectionCommRingEquiv 𝒪X (f y)
        ((ModuleCat.restrictScalars (ringStalkMap φ y).hom).obj T) U s hy := by
  let TR : ModuleCat.{u} ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) :=
    (ModuleCat.restrictScalars (ringStalkMap φ y).hom).obj T
  change skyscraperSectionCommRingEquiv 𝒪Y y T ((Opens.map f).obj U)
      ((skyscraperSectionCommRingEquiv 𝒪Y y T ((Opens.map f).obj U)).symm
        (skyscraperSectionCommRingEquiv 𝒪X (f y) TR U s)) hy = _
  exact congrFun (Equiv.apply_symm_apply _ _) hy

variable [(pushforward.{u} φ).IsRightAdjoint]

/-- The stalk of a pulled-back sheaf of modules `(φ^* G)_y` is naturally isomorphic to the base
change `𝒪Y_y ⊗_{𝒪X_{f y}} G_{f y}` along `ringStalkMap φ y`. -/
def pullbackStalkIso :
    stalkFunctorCommRing 𝒪X (f y) ⋙ ModuleCat.extendScalars (ringStalkMap φ y).hom ≅
      pullback.{u} φ ⋙ stalkFunctorCommRing 𝒪Y y :=
  Adjunction.leftAdjointUniq
    ((stalkSkyscraperAdjunctionCommRing 𝒪X (f y)).comp
      (ModuleCat.extendRestrictScalarsAdj (ringStalkMap φ y).hom))
    (((pullbackPushforwardAdjunction φ).comp
      (stalkSkyscraperAdjunctionCommRing 𝒪Y y)).ofNatIsoRight (pushforwardSkyscraperIso φ y))

/-- On generators `1 ⊗ₜ germ_U(m)`, `pullbackStalkIso` takes the germ at `y` of the image of `m`
under the unit `G ⟶ φ_* φ^* G` of the pullback--pushforward adjunction. -/
theorem pullbackStalkIso_hom_app_one_tmul_germ
    (G : SheafOfModules.{u} (ringCatSheaf 𝒪X)) (U : Opens X) (hy : f y ∈ U)
    (m : G.val.obj (op U)) :
    (pullbackStalkIso φ y).hom.app G
        ((1 : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) ⊗ₜ[
          ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)), (ringStalkMap φ y).hom]
          TopCat.Presheaf.germ G.val.presheaf U (f y) hy m) =
      TopCat.Presheaf.germ ((pullback.{u} φ).obj G).val.presheaf ((Opens.map f).obj U) y hy
        (((pullbackPushforwardAdjunction φ).unit.app G).val.app (op U) m) := by
  let adj₁ := (stalkSkyscraperAdjunctionCommRing 𝒪X (f y)).comp
    (ModuleCat.extendRestrictScalarsAdj (ringStalkMap φ y).hom)
  let adj₂ := ((pullbackPushforwardAdjunction φ).comp
    (stalkSkyscraperAdjunctionCommRing 𝒪Y y)).ofNatIsoRight (pushforwardSkyscraperIso φ y)
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app adj₁ adj₂ G
  have hsec := congrArg
    (fun k ↦ skyscraperSectionCommRingEquiv 𝒪X (f y) _ U (k.val.app (op U) m) hy) h
  have hlhs : skyscraperSectionCommRingEquiv 𝒪X (f y) _ U
      ((adj₁.homEquiv G _ ((pullbackStalkIso φ y).hom.app G)).val.app (op U) m) hy =
      (pullbackStalkIso φ y).hom.app G
        ((1 : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) ⊗ₜ[
          ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)), (ringStalkMap φ y).hom]
          TopCat.Presheaf.germ G.val.presheaf U (f y) hy m) := by
    rw [Adjunction.comp_homEquiv, Equiv.trans_apply,
      stalkSkyscraperAdjunctionCommRing_homEquiv_apply]
    exact ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
      ((pullbackStalkIso φ y).hom.app G) (TopCat.Presheaf.germ G.val.presheaf U (f y) hy m)
  have hrhs : skyscraperSectionCommRingEquiv 𝒪X (f y) _ U
      ((adj₂.unit.app G).val.app (op U) m) hy =
      TopCat.Presheaf.germ ((pullback.{u} φ).obj G).val.presheaf ((Opens.map f).obj U) y hy
        (((pullbackPushforwardAdjunction φ).unit.app G).val.app (op U) m) := by
    change skyscraperSectionCommRingEquiv 𝒪X (f y) _ U
        ((((pushforwardSkyscraperIso φ y).hom.app _).val.app (op U))
          ((((stalkSkyscraperAdjunctionCommRing 𝒪Y y).unit.app ((pullback.{u} φ).obj G)).val.app
            (op ((Opens.map f).obj U)))
            (((pullbackPushforwardAdjunction φ).unit.app G).val.app (op U) m))) hy = _
    erw [skyscraperSectionCommRingEquiv_pushforwardSkyscraperIso_hom_app,
      stalkSkyscraperAdjunctionCommRing_unit_app_val_app]
  exact hlhs.symm.trans (hsec.trans hrhs)

/-- On pure tensors `a ⊗ₜ germ_U(m)`, `pullbackStalkIso` multiplies the germ at `y` of the image
of `m` under the adjunction unit `G ⟶ φ_* φ^* G` by `a`. -/
theorem pullbackStalkIso_hom_app_tmul_germ
    (G : SheafOfModules.{u} (ringCatSheaf 𝒪X)) (U : Opens X) (hy : f y ∈ U)
    (a : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) (m : G.val.obj (op U)) :
    (pullbackStalkIso φ y).hom.app G
        (a ⊗ₜ[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)), (ringStalkMap φ y).hom]
          TopCat.Presheaf.germ G.val.presheaf U (f y) hy m) =
      a • TopCat.Presheaf.germ ((pullback.{u} φ).obj G).val.presheaf ((Opens.map f).obj U) y hy
        (((pullbackPushforwardAdjunction φ).unit.app G).val.app (op U) m) := by
  erw [← pullbackStalkIso_hom_app_one_tmul_germ φ y G U hy m, ← map_smul]
  congr 1
  erw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  rfl

/-- At the structure sheaf `𝒪X`, composing `pullbackStalkIso` with the stalk map of
`pullbackObjUnitToUnit φ : φ^* 𝒪X ⟶ 𝒪Y` sends `a ⊗ₜ germ_U(r)` to
`a • germ_{f⁻¹ U}(φ_U(r))`. -/
theorem pullbackStalkIso_hom_app_unit_comp_pullbackObjUnitToUnit
    (U : Opens X) (hy : f y ∈ U) (a : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y))
    (r : 𝒪X.obj.obj (op U)) :
    (stalkFunctorCommRing 𝒪Y y).map (pullbackObjUnitToUnit φ)
        ((pullbackStalkIso φ y).hom.app (unit (ringCatSheaf 𝒪X))
          (a ⊗ₜ[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)), (ringStalkMap φ y).hom]
            TopCat.Presheaf.germ (unit (ringCatSheaf 𝒪X)).val.presheaf U (f y) hy r)) =
      a • TopCat.Presheaf.germ (unit (ringCatSheaf 𝒪Y)).val.presheaf ((Opens.map f).obj U) y hy
        (φ.hom.app (op U) r) := by
  erw [pullbackStalkIso_hom_app_tmul_germ, map_smul, stalkFunctorCommRing_map_germ]
  congr 1
  have h := (pullbackPushforwardAdjunction φ).homEquiv_unit (unit (ringCatSheaf 𝒪X))
    (unit (ringCatSheaf 𝒪Y)) (pullbackObjUnitToUnit φ)
  rw [pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit] at h
  have happ := congrArg (fun k ↦ k.val.app (op U) r) h.symm
  exact congrArg (TopCat.Presheaf.germ (unit (ringCatSheaf 𝒪Y)).val.presheaf
    ((Opens.map f).obj U) y hy) happ

end SheafOfModules

end
