/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pullback.Stalk
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Presentation
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pushforward
import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pullback.Identity
import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Stalk

/-!
# Pullback of sheaves of modules is strong symmetric monoidal

Let `f : Y ⟶ X` be a continuous map of topological spaces, `𝒪X` and `𝒪Y` sheaves of
commutative rings on `X` and `Y`, and `φ : 𝒪X ⟶ f_* 𝒪Y` a morphism of the underlying sheaves of
rings. This file proves that the canonical oplax tensor comparison
`Functor.OplaxMonoidal.δ (SheafOfModules.pullback φ) E F : φ^* (E ⊗ F) ⟶ φ^* E ⊗ φ^* F`
is an isomorphism for all sheaves of `𝒪X`-modules `E` and `F`, with no quasi-coherence,
finiteness, or flatness hypotheses.

Consequently, `SheafOfModules.pullback φ` is a strong symmetric monoidal functor
(`SheafOfModules.pullbackMonoidal` and `SheafOfModules.pullbackBraided`), whose lax unit and tensor
maps are the inverses of the canonical structure-sheaf and tensor comparisons.

The proof checks invertibility on stalks (`SheafOfModules.isIso_of_stalkFunctorCommRing_map_isIso`).
At every point `y : Y`, the stalk of a sheaf tensor product identifies with the tensor product of
the stalks (`SheafOfModules.stalkTensorIso`), and the stalk of a pullback identifies with extension
of scalars along the induced ring stalk map `ringStalkMap φ y` (`SheafOfModules.pullbackStalkIso`).
Under these isomorphisms, the stalk map of `δ (pullback φ) E F` corresponds to the canonical
tensor comparison `δ (ModuleCat.extendScalars (ringStalkMap φ y).hom)`
(`SheafOfModules.pullbackStalkIso_hom_app_tensor_comp_map_δ`), which is an isomorphism in
`ModuleCat`.

We also record the compatibility of the pullback tensor comparison with free sheaves on arbitrary
ringed sites with a continuous final functor (`SheafOfModules.pullback_δ_free`), as well as the
monoidal coherence of the identity and composition isomorphisms of pullbacks.

## Main declarations

* `SheafOfModules.isIso_pullback_η_of_isIso`: the canonical unit comparison `φ^* S ⟶ R` of module
  pullback on any ringed site is an isomorphism whenever `SheafOfModules.pullbackObjUnitToUnit φ`
  is;
* `SheafOfModules.pullback_δ_free`: compatibility of the pullback tensor comparison with
  `SheafOfModules.pullbackObjFreeIso` and `TauCeti.SheafOfModules.freeTensorFreeIso`;
* `SheafOfModules.stalkTensorIso`: canonical isomorphism
  `(stalkFunctorCommRing R x).obj (M ⊗ N) ≅`
  `(stalkFunctorCommRing R x).obj M ⊗ (stalkFunctorCommRing R x).obj N`,
  computed on germs by `SheafOfModules.stalkTensorIso_hom_germ_forget_μ_tmul` and
  `SheafOfModules.stalkTensorIso_inv_tmul_germ`;
* `SheafOfModules.pullbackStalkIso_hom_app_tensor_comp_map_δ`: compatibility of
  `SheafOfModules.pullbackStalkIso` and `SheafOfModules.stalkTensorIso` with
  `Functor.OplaxMonoidal.δ (pullback φ)`;
* `SheafOfModules.isIso_pullback_η` and `SheafOfModules.isIso_pullback_δ`: the canonical unit and
  tensor comparisons of `SheafOfModules.pullback φ` on ringed spaces are isomorphisms for all
  sheaves of modules;
* `SheafOfModules.pullbackMonoidal` and `SheafOfModules.pullbackBraided`: the strong symmetric
  monoidal structure on `SheafOfModules.pullback φ`, with `SheafOfModules.pullback_ε`;
* `SheafOfModules.pullbackIdMonoidal`, `SheafOfModules.isMonoidal_pullbackId_hom`,
  `SheafOfModules.pullbackCompMonoidal`, `SheafOfModules.isMonoidal_pullbackComp_hom_of_isIso`, and
  `SheafOfModules.isMonoidal_pullbackComp_hom`: strong monoidal structures on identity and
  composite pullbacks and monoidal coherence of the identity and composition isomorphisms.

## References

* The Stacks Project, *Modules on Ringed Spaces*, Lemma 0098 (stalks of pullbacks) and
  *Sheaves of Modules*, Lemma 03EL (pullback of a tensor product).
-/

public section

open CategoryTheory Category MonoidalCategory TopologicalSpace Opposite Limits
open TauCeti.SheafOfModules
open scoped ChangeOfRings TensorProduct

universe u

noncomputable section

namespace SheafOfModules

section Free

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {F : C ⥤ D} [F.IsContinuous J K]
  {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  (φ : ringCatSheaf S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj (ringCatSheaf R))
  [(pushforward.{u} φ).IsRightAdjoint]

/-- The unit comparison `φ^* S ⟶ R` of module pullback on any ringed site is an isomorphism
whenever `SheafOfModules.pullbackObjUnitToUnit φ` is (in particular whenever `F` is final). -/
theorem isIso_pullback_η_of_isIso [IsIso (pullbackObjUnitToUnit φ)] :
    IsIso (Functor.OplaxMonoidal.η (pullback.{u} φ)) := by
  rw [pullback_η φ]
  infer_instance

variable [F.Final]

/-- On free sheaves of modules, the pullback tensor comparison is compatible with
`pullbackObjFreeIso` and `freeTensorFreeIso`. -/
@[reassoc]
theorem pullback_δ_free (I I' : Type u) :
    Functor.OplaxMonoidal.δ (pullback.{u} φ) (free I) (free I') ≫
        ((pullbackObjFreeIso φ I).hom ⊗ₘ (pullbackObjFreeIso φ I').hom) ≫
        (freeTensorFreeIso (R := R) I I').hom =
      (pullback.{u} φ).map (freeTensorFreeIso (R := S) I I').hom ≫
        (pullbackObjFreeIso φ (I × I')).hom := by
  rw [← cancel_epi ((pullback.{u} φ).map (freeTensorFreeIso (R := S) I I').inv)]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, id_comp]
  apply Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit (pullback.{u} φ) _ _
      (isColimitFreeCofan (R := ringCatSheaf S) (I × I')))
  rintro ⟨i, i'⟩
  dsimp only [Cofan.inj, Cofan.mk_pt, Cofan.mk_ι_app, freeCofan_inj]
  rw [← Functor.map_comp_assoc, ιFree_freeTensorFreeIso_inv, Functor.map_comp_assoc,
    ← Functor.OplaxMonoidal.δ_natural_assoc, tensorHom_comp_tensorHom_assoc,
    pullback_map_ιFree_comp_pullbackObjFreeIso_hom,
    pullback_map_ιFree_comp_pullbackObjFreeIso_hom,
    pullback_map_ιFree_comp_pullbackObjFreeIso_hom]
  rw [← pullback_η φ]
  have hunitor :
      (pullback.{u} φ).map (λ_ (𝟙_ _)).inv ≫
          Functor.OplaxMonoidal.δ (pullback.{u} φ) (𝟙_ _) (𝟙_ _) ≫
          (Functor.OplaxMonoidal.η (pullback.{u} φ) ⊗ₘ
            Functor.OplaxMonoidal.η (pullback.{u} φ)) =
        Functor.OplaxMonoidal.η (pullback.{u} φ) ≫ (λ_ (𝟙_ _)).inv := by
    rw [tensorHom_def, ← Functor.OplaxMonoidal.left_unitality_assoc (pullback.{u} φ) (𝟙_ _)]
    exact (leftUnitor_inv_naturality (Functor.OplaxMonoidal.η (pullback.{u} φ))).symm
  have hfree :
      (λ_ (unit (ringCatSheaf R))).inv ≫ (ιFree i ⊗ₘ ιFree i') ≫
          (freeTensorFreeIso (R := R) I I').hom = ιFree (i, i') := by
    rw [← Category.assoc, ← ιFree_freeTensorFreeIso_inv (R := R) i i',
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← tensorHom_comp_tensorHom_assoc]
  have h1 := congrArg
    (· ≫ (ιFree i ⊗ₘ ιFree i') ≫ (freeTensorFreeIso (R := R) I I').hom) hunitor
  simp only [Category.assoc] at h1
  exact h1.trans (congrArg (Functor.OplaxMonoidal.η (pullback.{u} φ) ≫ ·) hfree)

end Free

section StalkTensor

variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-- The stalk of the tensor product `M ⊗ N` of two sheaves of `R`-modules is canonically
isomorphic to the tensor product of their stalks over the ring stalk `R_x`. -/
def stalkTensorIso (M N : SheafOfModules.{u} (ringCatSheaf R)) (x : X) :
    (stalkFunctorCommRing R x).obj (M ⊗ N) ≅
      (stalkFunctorCommRing R x).obj M ⊗ (stalkFunctorCommRing R x).obj N :=
  (stalkFunctorCommRing R x).mapIso
      (M.tensorUnderlyingIso N ≪≫ (tensorProductIso R M N).symm) ≪≫
    (TauCeti.SheafOfModules.tensorStalkEquiv R M N x).toModuleIso

/-- The lax tensor map of `SheafOfModules.forget`, composed with the identification of `M ⊗ N`
with `tensorProduct R M N`, factors through the sheafification unit and
`(tensorProductIso R M N).inv`. -/
private lemma forget_μ_comp_tensorUnderlyingIso_hom
    (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (Functor.LaxMonoidal.μ (forget (ringCatSheaf R)) M N : M.val ⊗ N.val ⟶ (M ⊗ N).val) ≫
        (M.tensorUnderlyingIso N ≪≫ (tensorProductIso R M N).symm).hom.val =
      ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (ringCatSheaf R).obj)).unit.app (M.val ⊗ N.val) :
          M.val ⊗ N.val ⟶
            ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj
              (M.val ⊗ N.val)).val) ≫
        (tensorProductIso R M N).inv.val := by
  let μF : M.val ⊗ N.val ⟶ (M ⊗ N).val := Functor.LaxMonoidal.μ (forget (ringCatSheaf R)) M N
  let η : M.val ⊗ N.val ⟶
      ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj (M.val ⊗ N.val)).val :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringCatSheaf R).obj)).unit.app (M.val ⊗ N.val)
  have hμ : μF = η ≫ (M.tensorUnderlyingIso N).inv.val := by
    let := (PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringCatSheaf R).obj)).rightAdjointLaxMonoidal
    have hinv : (M.tensorUnderlyingIso N).inv =
        Functor.OplaxMonoidal.δ
            (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)) M.val N.val ≫
          ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).counit.app M ⊗ₘ
            (PresheafOfModules.sheafificationAdjunction
              (𝟙 (ringCatSheaf R).obj)).counit.app N) :=
      (SheafOfModules.tensorUnderlyingIso_inv (R := R) M N).trans
        (by rw [sheafificationIso_hom, sheafificationIso_hom])
    rw [hinv]
    change @Functor.LaxMonoidal.μ _ _ _ _ _ _ (forget (ringCatSheaf R))
      (forgetLaxMonoidal R) M N = _
    rw [← sheafificationAdjunction_μ_eq_forget_μ R M N, Adjunction.rightAdjointLaxMonoidal_μ,
      Adjunction.homEquiv_unit]
    rfl
  change μF ≫ (M.tensorUnderlyingIso N ≪≫ (tensorProductIso R M N).symm).hom.val =
    η ≫ (tensorProductIso R M N).inv.val
  rw [hμ, Category.assoc]
  have hinv : (M.tensorUnderlyingIso N).inv.val ≫
      (M.tensorUnderlyingIso N ≪≫ (tensorProductIso R M N).symm).hom.val =
      (tensorProductIso R M N).inv.val := by
    change ((M.tensorUnderlyingIso N).inv ≫
      (M.tensorUnderlyingIso N).hom ≫ (tensorProductIso R M N).inv).val = _
    rw [Iso.inv_hom_id_assoc]
  rw [hinv]

/-- On germs of sheafified pure tensors `m ⊗ₜ n`, `stalkTensorIso.hom` yields the tensor product
of the germs of `m` and `n`. -/
theorem stalkTensorIso_hom_germ_forget_μ_tmul
    (M N : SheafOfModules.{u} (ringCatSheaf R)) (x : X) (U : Opens X) (hx : x ∈ U)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (stalkTensorIso R M N x).hom
        (TopCat.Presheaf.germ (M ⊗ N).val.presheaf U x hx
          ((Functor.LaxMonoidal.μ (forget (ringCatSheaf R)) M N).app (op U)
            (m ⊗ₜ[R.obj.obj (op U)] n))) =
      TopCat.Presheaf.germ M.val.presheaf U x hx m ⊗ₜ[↑(TopCat.Presheaf.stalk R.obj x)]
        TopCat.Presheaf.germ N.val.presheaf U x hx n := by
  change TauCeti.SheafOfModules.tensorStalkEquiv R M N x
      ((stalkFunctorCommRing R x).map
        (M.tensorUnderlyingIso N ≪≫ (tensorProductIso R M N).symm).hom
        (TopCat.Presheaf.germ (M ⊗ N).val.presheaf U x hx
          ((Functor.LaxMonoidal.μ (forget (ringCatSheaf R)) M N).app (op U)
            (m ⊗ₜ[R.obj.obj (op U)] n)))) = _
  have hgerm := stalkFunctorCommRing_map_germ R x
    (M.tensorUnderlyingIso N ≪≫ (tensorProductIso R M N).symm).hom U hx
    ((Functor.LaxMonoidal.μ (forget (ringCatSheaf R)) M N).app (op U)
      (m ⊗ₜ[R.obj.obj (op U)] n))
  have hsec :
      (M.tensorUnderlyingIso N ≪≫ (tensorProductIso R M N).symm).hom.val.app (op U)
          ((Functor.LaxMonoidal.μ (forget (ringCatSheaf R)) M N).app (op U)
            (m ⊗ₜ[R.obj.obj (op U)] n)) =
        (tensorProductIso R M N).inv.val.app (op U)
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 (ringCatSheaf R).obj)).unit.app (M.val ⊗ N.val)).app (op U)
            (m ⊗ₜ[R.obj.obj (op U)] n)) :=
    congrArg (fun k ↦ (k.app (op U)).hom (m ⊗ₜ[R.obj.obj (op U)] n))
      (forget_μ_comp_tensorUnderlyingIso_hom R M N)
  have h1 := congrArg (TauCeti.SheafOfModules.tensorStalkEquiv R M N x)
    (hgerm.trans (congrArg
      (TopCat.Presheaf.germ (tensorProduct R M N).val.presheaf U x hx) hsec))
  refine h1.trans ?_
  rw [TauCeti.SheafOfModules.tensorStalkEquiv_apply]
  exact TauCeti.SheafOfModules.tensorStalkComparison_germ_unit_tmul R M N x U hx m n

/-- On a pure tensor of germs `germ_U(m) ⊗ₜ germ_U(n)` on a common open neighborhood `U` of `x`,
`stalkTensorIso.inv` returns the germ of the sheafified pure tensor. -/
theorem stalkTensorIso_inv_tmul_germ
    (M N : SheafOfModules.{u} (ringCatSheaf R)) (x : X) (U : Opens X) (hx : x ∈ U)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (stalkTensorIso R M N x).inv
        (TopCat.Presheaf.germ M.val.presheaf U x hx m ⊗ₜ[↑(TopCat.Presheaf.stalk R.obj x)]
          TopCat.Presheaf.germ N.val.presheaf U x hx n) =
      TopCat.Presheaf.germ (M ⊗ N).val.presheaf U x hx
        ((Functor.LaxMonoidal.μ (forget (ringCatSheaf R)) M N).app (op U)
          (m ⊗ₜ[R.obj.obj (op U)] n)) := by
  have h := congrArg (stalkTensorIso R M N x).inv
    (stalkTensorIso_hom_germ_forget_μ_tmul R M N x U hx m n)
  exact h.symm.trans (ConcreteCategory.congr_hom (stalkTensorIso R M N x).hom_inv_id _)

end StalkTensor

section RingedSpace

variable {X Y : TopCat.{u}} {f : Y ⟶ X}
  {𝒪X : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {𝒪Y : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}}
  (φ : ringCatSheaf 𝒪X ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Y))
  [(pushforward.{u} φ).IsRightAdjoint]

/-- On underlying sections over `U`, applying the adjunction unit and the pullback tensor
comparison `δ (pullback φ) E F` to a pure tensor `m ⊗ₜ n` agrees with applying the adjunction
unit to each factor and then taking the pure tensor in `φ^* E ⊗ φ^* F`. -/
private lemma pullback_δ_val_app_unit_forget_μ_tmul
    (E F : SheafOfModules.{u} (ringCatSheaf 𝒪X)) (U : Opens X)
    (m : E.val.obj (op U)) (n : F.val.obj (op U)) :
    (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F).val.app (op ((Opens.map f).obj U))
        (((pullbackPushforwardAdjunction φ).unit.app (E ⊗ F)).val.app (op U)
          ((Functor.LaxMonoidal.μ (forget (ringCatSheaf 𝒪X)) E F).app (op U)
            (m ⊗ₜ[𝒪X.obj.obj (op U)] n))) =
      (Functor.LaxMonoidal.μ (forget (ringCatSheaf 𝒪Y))
          ((pullback.{u} φ).obj E) ((pullback.{u} φ).obj F)).app (op ((Opens.map f).obj U))
        ((((pullbackPushforwardAdjunction φ).unit.app E).val.app (op U) m) ⊗ₜ[
          𝒪Y.obj.obj (op ((Opens.map f).obj U))]
          (((pullbackPushforwardAdjunction φ).unit.app F).val.app (op U) n)) := by
  have hadj :
      (pullbackPushforwardAdjunction φ).unit.app (E ⊗ F) ≫
          (pushforward.{u} φ).map (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F) =
        ((pullbackPushforwardAdjunction φ).unit.app E ⊗ₘ
            (pullbackPushforwardAdjunction φ).unit.app F) ≫
          Functor.LaxMonoidal.μ (pushforward.{u} φ)
            ((pullback.{u} φ).obj E) ((pullback.{u} φ).obj F) :=
    ((pullbackPushforwardAdjunction φ).homEquiv_unit (E ⊗ F)
      (((pullback.{u} φ).obj E) ⊗ ((pullback.{u} φ).obj F))
      (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F)).symm.trans
      (by erw [pullback_δ φ E F, Equiv.apply_symm_apply])
  have h1 := congrArg (fun k ↦ (k.val.app (op U)).hom
    ((Functor.LaxMonoidal.μ (forget (ringCatSheaf 𝒪X)) E F).app (op U)
      (m ⊗ₜ[𝒪X.obj.obj (op U)] n))) hadj
  have hnat := congrArg (fun k ↦ (k.app (op U)).hom (m ⊗ₜ[𝒪X.obj.obj (op U)] n))
    (Functor.LaxMonoidal.μ_natural (forget (ringCatSheaf 𝒪X))
      ((pullbackPushforwardAdjunction φ).unit.app E)
      ((pullbackPushforwardAdjunction φ).unit.app F))
  have hμ := pushforward_μ_app_tmul φ ((pullback.{u} φ).obj E) ((pullback.{u} φ).obj F) (op U)
    (((pullbackPushforwardAdjunction φ).unit.app E).val.app (op U) m)
    (((pullbackPushforwardAdjunction φ).unit.app F).val.app (op U) n)
  exact h1.trans ((congrArg
    ((Functor.LaxMonoidal.μ (pushforward.{u} φ)
      ((pullback.{u} φ).obj E) ((pullback.{u} φ).obj F)).val.app (op U)) hnat.symm).trans hμ)

/-- Left-hand evaluation on a pure tensor of germs in
`pullbackStalkIso_hom_app_tensor_comp_map_δ`. -/
private lemma pullbackStalkIso_hom_app_tensor_comp_map_δ_lhs_germ
    (y : Y) (E F : SheafOfModules.{u} (ringCatSheaf 𝒪X))
    (V : Opens X) (hyV : f y ∈ V) (m : E.val.obj (op V)) (n : F.val.obj (op V)) :
    (stalkTensorIso 𝒪Y ((pullback.{u} φ).obj E) ((pullback.{u} φ).obj F) y).hom
        ((stalkFunctorCommRing 𝒪Y y).map (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F)
          ((pullbackStalkIso φ y).hom.app (E ⊗ F)
            ((ModuleCat.extendScalars (ringStalkMap φ y).hom).map
              (stalkTensorIso 𝒪X E F (f y)).inv
              ((1 : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) ⊗ₜ[
                ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)), (ringStalkMap φ y).hom]
                (TopCat.Presheaf.germ E.val.presheaf V (f y) hyV m ⊗ₜ[
                  ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
                  TopCat.Presheaf.germ F.val.presheaf V (f y) hyV n))))) =
      TopCat.Presheaf.germ ((pullback.{u} φ).obj E).val.presheaf ((Opens.map f).obj V) y hyV
          (((pullbackPushforwardAdjunction φ).unit.app E).val.app (op V) m) ⊗ₜ[
            ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)]
        TopCat.Presheaf.germ ((pullback.{u} φ).obj F).val.presheaf ((Opens.map f).obj V) y hyV
          (((pullbackPushforwardAdjunction φ).unit.app F).val.app (op V) n) := by
  let ρ := (ringStalkMap φ y).hom
  let gE : (stalkFunctorCommRing 𝒪X (f y)).obj E :=
    TopCat.Presheaf.germ E.val.presheaf V (f y) hyV m
  let gF : (stalkFunctorCommRing 𝒪X (f y)).obj F :=
    TopCat.Presheaf.germ F.val.presheaf V (f y) hyV n
  let secEF : (E ⊗ F).val.obj (op V) :=
    (Functor.LaxMonoidal.μ (forget (ringCatSheaf 𝒪X)) E F).app (op V)
      (m ⊗ₜ[𝒪X.obj.obj (op V)] n)
  let uE : ((pullback.{u} φ).obj E).val.obj (op ((Opens.map f).obj V)) :=
    ((pullbackPushforwardAdjunction φ).unit.app E).val.app (op V) m
  let uF : ((pullback.{u} φ).obj F).val.obj (op ((Opens.map f).obj V)) :=
    ((pullbackPushforwardAdjunction φ).unit.app F).val.app (op V) n
  have hl1 :=
    (ModuleCat.ExtendScalars.map_tmul ρ (stalkTensorIso 𝒪X E F (f y)).inv 1
      (gE ⊗ₜ[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))] gF)).trans
      (congrArg ((1 : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) ⊗ₜ[
        ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)), ρ] ·)
        (stalkTensorIso_inv_tmul_germ 𝒪X E F (f y) V hyV m n))
  have hl2 := pullbackStalkIso_hom_app_one_tmul_germ φ y (E ⊗ F) V hyV secEF
  have hl3 :=
    (stalkFunctorCommRing_map_germ 𝒪Y y (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F)
      ((Opens.map f).obj V) hyV
      (((pullbackPushforwardAdjunction φ).unit.app (E ⊗ F)).val.app (op V) secEF)).trans
      (congrArg
        (TopCat.Presheaf.germ (((pullback.{u} φ).obj E) ⊗ ((pullback.{u} φ).obj F)).val.presheaf
          ((Opens.map f).obj V) y hyV)
        (pullback_δ_val_app_unit_forget_μ_tmul φ E F V m n))
  have hl4 := stalkTensorIso_hom_germ_forget_μ_tmul 𝒪Y
    ((pullback.{u} φ).obj E) ((pullback.{u} φ).obj F) y ((Opens.map f).obj V) hyV uE uF
  exact (congrArg (fun z ↦ (stalkTensorIso 𝒪Y _ _ y).hom
      ((stalkFunctorCommRing 𝒪Y y).map (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F)
        ((pullbackStalkIso φ y).hom.app (E ⊗ F) z))) hl1).trans
    ((congrArg (fun z ↦ (stalkTensorIso 𝒪Y _ _ y).hom
      ((stalkFunctorCommRing 𝒪Y y).map (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F) z))
        hl2).trans
      ((congrArg (stalkTensorIso 𝒪Y _ _ y).hom hl3).trans hl4))

/-- Right-hand evaluation on a pure tensor of germs in
`pullbackStalkIso_hom_app_tensor_comp_map_δ`. -/
private lemma pullbackStalkIso_hom_app_tensor_comp_map_δ_rhs_germ
    (y : Y) (E F : SheafOfModules.{u} (ringCatSheaf 𝒪X))
    (V : Opens X) (hyV : f y ∈ V) (m : E.val.obj (op V)) (n : F.val.obj (op V)) :
    ((pullbackStalkIso φ y).hom.app E ⊗ₘ (pullbackStalkIso φ y).hom.app F)
        (Functor.OplaxMonoidal.δ (ModuleCat.extendScalars (ringStalkMap φ y).hom)
          ((stalkFunctorCommRing 𝒪X (f y)).obj E) ((stalkFunctorCommRing 𝒪X (f y)).obj F)
          ((1 : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) ⊗ₜ[
            ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)), (ringStalkMap φ y).hom]
            (TopCat.Presheaf.germ E.val.presheaf V (f y) hyV m ⊗ₜ[
              ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
              TopCat.Presheaf.germ F.val.presheaf V (f y) hyV n))) =
      TopCat.Presheaf.germ ((pullback.{u} φ).obj E).val.presheaf ((Opens.map f).obj V) y hyV
          (((pullbackPushforwardAdjunction φ).unit.app E).val.app (op V) m) ⊗ₜ[
            ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)]
        TopCat.Presheaf.germ ((pullback.{u} φ).obj F).val.presheaf ((Opens.map f).obj V) y hyV
          (((pullbackPushforwardAdjunction φ).unit.app F).val.app (op V) n) := by
  let ρ := (ringStalkMap φ y).hom
  let gE : (stalkFunctorCommRing 𝒪X (f y)).obj E :=
    TopCat.Presheaf.germ E.val.presheaf V (f y) hyV m
  let gF : (stalkFunctorCommRing 𝒪X (f y)).obj F :=
    TopCat.Presheaf.germ F.val.presheaf V (f y) hyV n
  let xE : (ModuleCat.extendScalars ρ).obj ((stalkFunctorCommRing 𝒪X (f y)).obj E) :=
    (1 : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) ⊗ₜ[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)), ρ] gE
  let xF : (ModuleCat.extendScalars ρ).obj ((stalkFunctorCommRing 𝒪X (f y)).obj F) :=
    (1 : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) ⊗ₜ[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)), ρ] gF
  have hr1 := ModuleCat.extendScalars_δ_tmul ρ
    ((stalkFunctorCommRing 𝒪X (f y)).obj E) ((stalkFunctorCommRing 𝒪X (f y)).obj F) gE gF
  have hr2 :=
    (ModuleCat.MonoidalCategory.tensorHom_tmul
      ((pullbackStalkIso φ y).hom.app E) ((pullbackStalkIso φ y).hom.app F) xE xF).trans
      (congrArg₂ (· ⊗ₜ[↑(TopCat.Presheaf.stalk 𝒪Y.obj y)] ·)
        (pullbackStalkIso_hom_app_one_tmul_germ φ y E V hyV m)
        (pullbackStalkIso_hom_app_one_tmul_germ φ y F V hyV n))
  exact (congrArg ((pullbackStalkIso φ y).hom.app E ⊗ₘ
    (pullbackStalkIso φ y).hom.app F) hr1).trans hr2

/-- Elementwise check of `pullbackStalkIso_hom_app_tensor_comp_map_δ` on a pure tensor of germs
defined over a common open neighborhood `V` of `f y`. -/
private lemma pullbackStalkIso_hom_app_tensor_comp_map_δ_germ
    (y : Y) (E F : SheafOfModules.{u} (ringCatSheaf 𝒪X))
    (V : Opens X) (hyV : f y ∈ V) (m : E.val.obj (op V)) (n : F.val.obj (op V)) :
    ((ModuleCat.extendRestrictScalarsAdj (ringStalkMap φ y).hom).homEquiv _ _
      ((ModuleCat.extendScalars (ringStalkMap φ y).hom).map
          (stalkTensorIso 𝒪X E F (f y)).inv ≫
        (pullbackStalkIso φ y).hom.app (E ⊗ F) ≫
        (stalkFunctorCommRing 𝒪Y y).map (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F) ≫
        (stalkTensorIso 𝒪Y ((pullback.{u} φ).obj E) ((pullback.{u} φ).obj F) y).hom))
      (TopCat.Presheaf.germ E.val.presheaf V (f y) hyV m ⊗ₜ[
        ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
        TopCat.Presheaf.germ F.val.presheaf V (f y) hyV n) =
    ((ModuleCat.extendRestrictScalarsAdj (ringStalkMap φ y).hom).homEquiv _ _
      (Functor.OplaxMonoidal.δ (ModuleCat.extendScalars (ringStalkMap φ y).hom)
          ((stalkFunctorCommRing 𝒪X (f y)).obj E) ((stalkFunctorCommRing 𝒪X (f y)).obj F) ≫
        ((pullbackStalkIso φ y).hom.app E ⊗ₘ (pullbackStalkIso φ y).hom.app F)))
      (TopCat.Presheaf.germ E.val.presheaf V (f y) hyV m ⊗ₜ[
        ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
        TopCat.Presheaf.germ F.val.presheaf V (f y) hyV n) := by
  let ρ := (ringStalkMap φ y).hom
  let gEF :=
    TopCat.Presheaf.germ E.val.presheaf V (f y) hyV m ⊗ₜ[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
      TopCat.Presheaf.germ F.val.presheaf V (f y) hyV n
  let lhs := (ModuleCat.extendScalars ρ).map (stalkTensorIso 𝒪X E F (f y)).inv ≫
    (pullbackStalkIso φ y).hom.app (E ⊗ F) ≫
    (stalkFunctorCommRing 𝒪Y y).map (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F) ≫
    (stalkTensorIso 𝒪Y ((pullback.{u} φ).obj E) ((pullback.{u} φ).obj F) y).hom
  let rhs := Functor.OplaxMonoidal.δ (ModuleCat.extendScalars ρ)
      ((stalkFunctorCommRing 𝒪X (f y)).obj E) ((stalkFunctorCommRing 𝒪X (f y)).obj F) ≫
    ((pullbackStalkIso φ y).hom.app E ⊗ₘ (pullbackStalkIso φ y).hom.app F)
  exact (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply lhs gEF).trans
    (((pullbackStalkIso_hom_app_tensor_comp_map_δ_lhs_germ φ y E F V hyV m n).trans
      (pullbackStalkIso_hom_app_tensor_comp_map_δ_rhs_germ φ y E F V hyV m n).symm).trans
      (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply rhs gEF).symm)

/-- Under `pullbackStalkIso` and `stalkTensorIso`, the stalk map of the pullback tensor comparison
`δ (pullback φ) E F` at `y : Y` corresponds to the canonical tensor comparison of scalar extension
along `ringStalkMap φ y`. -/
theorem pullbackStalkIso_hom_app_tensor_comp_map_δ
    (y : Y) (E F : SheafOfModules.{u} (ringCatSheaf 𝒪X)) :
    (ModuleCat.extendScalars (ringStalkMap φ y).hom).map (stalkTensorIso 𝒪X E F (f y)).inv ≫
        (pullbackStalkIso φ y).hom.app (E ⊗ F) ≫
        (stalkFunctorCommRing 𝒪Y y).map (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F) ≫
        (stalkTensorIso 𝒪Y ((pullback.{u} φ).obj E) ((pullback.{u} φ).obj F) y).hom =
      Functor.OplaxMonoidal.δ (ModuleCat.extendScalars (ringStalkMap φ y).hom)
          ((stalkFunctorCommRing 𝒪X (f y)).obj E) ((stalkFunctorCommRing 𝒪X (f y)).obj F) ≫
        ((pullbackStalkIso φ y).hom.app E ⊗ₘ (pullbackStalkIso φ y).hom.app F) := by
  apply ((ModuleCat.extendRestrictScalarsAdj (ringStalkMap φ y).hom).homEquiv _ _).injective
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro e f'
  obtain ⟨U, hyU, m, hm⟩ := TopCat.Presheaf.exists_germ_eq E.val.presheaf e
  obtain ⟨V, hVU, hyV, n, hn⟩ := TopCat.Presheaf.exists_le_germ_eq F.val.presheaf f' hyU
  have hm' : TopCat.Presheaf.germ E.val.presheaf V (f y) hyV
      (E.val.presheaf.map (homOfLE hVU).op m) = e :=
    (TopCat.Presheaf.germ_res_apply E.val.presheaf (homOfLE hVU) (f y) hyV m).trans hm
  have hEF :
      e ⊗ₜ[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))] f' =
        TopCat.Presheaf.germ E.val.presheaf V (f y) hyV (E.val.presheaf.map (homOfLE hVU).op m)
          ⊗ₜ[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
          TopCat.Presheaf.germ F.val.presheaf V (f y) hyV n :=
    congrArg₂ (· ⊗ₜ[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))] ·) hm'.symm hn.symm
  exact (congrArg _ hEF).trans
    ((pullbackStalkIso_hom_app_tensor_comp_map_δ_germ φ y E F V hyV _ n).trans
      (congrArg _ hEF.symm))

/-- The canonical unit comparison `φ^* 𝒪X ⟶ 𝒪Y` of module pullback along a morphism of ringed
spaces is an isomorphism. -/
instance isIso_pullback_η : IsIso (Functor.OplaxMonoidal.η (pullback.{u} φ)) :=
  isIso_pullback_η_of_isIso φ

/-- The canonical tensor comparison `φ^* (E ⊗ F) ⟶ φ^* E ⊗ φ^* F` of module pullback along a
morphism of ringed spaces is an isomorphism for all sheaves of modules `E` and `F`, with no
quasi-coherence, finiteness, or flatness hypotheses. -/
instance isIso_pullback_δ (E F : SheafOfModules.{u} (ringCatSheaf 𝒪X)) :
    IsIso (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F) := by
  apply isIso_of_stalkFunctorCommRing_map_isIso 𝒪Y
  intro y
  have h := pullbackStalkIso_hom_app_tensor_comp_map_δ φ y E F
  have hcomp : IsIso
      ((ModuleCat.extendScalars (ringStalkMap φ y).hom).map
          (stalkTensorIso 𝒪X E F (f y)).inv ≫
        (pullbackStalkIso φ y).hom.app (E ⊗ F) ≫
        (stalkFunctorCommRing 𝒪Y y).map (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F) ≫
        (stalkTensorIso 𝒪Y ((pullback.{u} φ).obj E) ((pullback.{u} φ).obj F) y).hom) := by
    rw [h]
    infer_instance
  have h1 : IsIso
      ((pullbackStalkIso φ y).hom.app (E ⊗ F) ≫
        (stalkFunctorCommRing 𝒪Y y).map (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F) ≫
        (stalkTensorIso 𝒪Y ((pullback.{u} φ).obj E) ((pullback.{u} φ).obj F) y).hom) :=
    IsIso.of_isIso_comp_left
      ((ModuleCat.extendScalars (ringStalkMap φ y).hom).map (stalkTensorIso 𝒪X E F (f y)).inv) _
  have h2 : IsIso
      ((stalkFunctorCommRing 𝒪Y y).map (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F) ≫
        (stalkTensorIso 𝒪Y ((pullback.{u} φ).obj E) ((pullback.{u} φ).obj F) y).hom) :=
    IsIso.of_isIso_comp_left ((pullbackStalkIso φ y).hom.app (E ⊗ F)) _
  exact IsIso.of_isIso_comp_right _
    (stalkTensorIso 𝒪Y ((pullback.{u} φ).obj E) ((pullback.{u} φ).obj F) y).hom

/-- Pullback of sheaves of modules along a morphism of ringed spaces is a strong monoidal functor,
whose oplax structure is the canonical `SheafOfModules.pullbackOplaxMonoidal`. -/
instance pullbackMonoidal : (pullback.{u} φ).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal (pullback.{u} φ)

/-- Pullback of sheaves of modules along a morphism of ringed spaces is a strong symmetric monoidal
functor. -/
instance pullbackBraided : (pullback.{u} φ).Braided where
  toMonoidal := pullbackMonoidal φ
  braided E F := by
    rw [← cancel_epi (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F),
      ← cancel_mono (Functor.OplaxMonoidal.δ (pullback.{u} φ) F E)]
    simp only [Category.assoc, Functor.Monoidal.δ_μ_assoc, Functor.Monoidal.μ_δ,
      Category.comp_id]
    exact pullback_map_braiding_hom_comp_δ φ E F

/-- The lax unit map of module pullback is the inverse of `pullbackObjUnitToUnit φ`. -/
@[simp]
theorem pullback_ε :
    Functor.LaxMonoidal.ε (pullback.{u} φ) = inv (pullbackObjUnitToUnit φ) :=
  IsIso.eq_inv_of_inv_hom_id ((congrArg (_ ≫ ·) (pullback_η φ).symm).trans
    (Functor.Monoidal.ε_η (pullback.{u} φ)))

end RingedSpace

section Coherence

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

/-- The identity pullback functor on any ringed site is strong monoidal, with oplax structure
given by `SheafOfModules.pullbackOplaxMonoidal`. -/
instance pullbackIdMonoidal :
    (pullback.{u} (J := J) (K := J) (S := ringCatSheaf R) (R := ringCatSheaf R)
      (F := 𝟭 C) (𝟙 (ringCatSheaf R))).Monoidal :=
  letI := pullbackOplaxMonoidal (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
  haveI : IsIso (Functor.OplaxMonoidal.η (pullback.{u} (J := J) (K := J)
      (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R)))) := by
    rw [TauCeti.SheafOfModules.pullback_id_η R]
    infer_instance
  haveI (E F : SheafOfModules.{u} (ringCatSheaf R)) :
      IsIso (Functor.OplaxMonoidal.δ (pullback.{u} (J := J) (K := J)
        (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C)
        (𝟙 (ringCatSheaf R))) E F) := by
    have : IsIso (Functor.OplaxMonoidal.δ (pullback.{u} (J := J) (K := J)
        (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))) E F ≫
      ((pullbackId (ringCatSheaf R)).hom.app E ⊗ₘ
        (pullbackId (ringCatSheaf R)).hom.app F)) := by
      rw [TauCeti.SheafOfModules.pullback_id_δ R E F]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((pullbackId (ringCatSheaf R)).hom.app E ⊗ₘ (pullbackId (ringCatSheaf R)).hom.app F)
  Functor.Monoidal.ofOplaxMonoidal _

/-- The identity isomorphism of module pullback on any ringed site is monoidal. -/
instance isMonoidal_pullbackId_hom :
    NatTrans.IsMonoidal (pullbackId (ringCatSheaf R)).hom where
  unit := by
    erw [← TauCeti.SheafOfModules.pullback_id_η R]
    exact Functor.Monoidal.ε_η _
  tensor E F := by
    rw [← cancel_epi (Functor.OplaxMonoidal.δ
      (pullback.{u} (J := J) (K := J) (S := ringCatSheaf R) (R := ringCatSheaf R)
        (F := 𝟭 C) (𝟙 (ringCatSheaf R))) E F)]
    erw [Functor.Monoidal.δ_μ_assoc, Functor.LaxMonoidal.id_μ, Category.comp_id]
    exact (TauCeti.SheafOfModules.pullback_id_δ R E F).symm

variable {D E : Type u} [SmallCategory D] [SmallCategory E]
  {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [L.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify L AddCommGrpCat.{u}] [L.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {F : C ⥤ D} {G : D ⥤ E} [F.IsContinuous J K] [G.IsContinuous K L] [(F ⋙ G).IsContinuous J L]
  {S : Sheaf J CommRingCat.{u}} {R' : Sheaf K CommRingCat.{u}} {T : Sheaf L CommRingCat.{u}}
  (φ : ringCatSheaf S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj (ringCatSheaf R'))
  (ψ : ringCatSheaf R' ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj (ringCatSheaf T))
  [(pushforward.{u} φ).IsRightAdjoint] [(pushforward.{u} ψ).IsRightAdjoint]

/-- When two composable pullbacks have invertible unit and tensor comparisons, so does the
pullback along their composite, which is therefore strong monoidal. -/
instance pullbackCompMonoidal
    [IsIso (Functor.OplaxMonoidal.η (pullback.{u} φ))]
    [IsIso (Functor.OplaxMonoidal.η (pullback.{u} ψ))]
    [∀ M N, IsIso (Functor.OplaxMonoidal.δ (pullback.{u} φ) M N)]
    [∀ M N, IsIso (Functor.OplaxMonoidal.δ (pullback.{u} ψ) M N)] :
    (pullback.{u} (F := F ⋙ G) (R := ringCatSheaf T)
      (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)).Monoidal := by
  haveI : IsIso (Functor.OplaxMonoidal.η (pullback.{u} (F := F ⋙ G) (R := ringCatSheaf T)
      (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ))) := by
    rw [pullback_comp_η φ ψ]
    infer_instance
  haveI (M N : SheafOfModules.{u} (ringCatSheaf S)) :
      IsIso (Functor.OplaxMonoidal.δ (pullback.{u} (F := F ⋙ G) (R := ringCatSheaf T)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)) M N) := by
    rw [pullback_comp_δ φ ψ M N]
    infer_instance
  exact Functor.Monoidal.ofOplaxMonoidal _

/-- On any ringed site, the composition isomorphism of pullbacks is monoidal whenever both factors
have invertible unit and tensor comparisons. -/
theorem isMonoidal_pullbackComp_hom_of_isIso
    [IsIso (Functor.OplaxMonoidal.η (pullback.{u} φ))]
    [IsIso (Functor.OplaxMonoidal.η (pullback.{u} ψ))]
    [∀ M N, IsIso (Functor.OplaxMonoidal.δ (pullback.{u} φ) M N)]
    [∀ M N, IsIso (Functor.OplaxMonoidal.δ (pullback.{u} ψ) M N)] :
    letI := Functor.Monoidal.ofOplaxMonoidal (pullback.{u} φ)
    letI := Functor.Monoidal.ofOplaxMonoidal (pullback.{u} ψ)
    NatTrans.IsMonoidal (pullbackComp φ ψ).hom := by
  let := Functor.Monoidal.ofOplaxMonoidal (pullback.{u} φ)
  let := Functor.Monoidal.ofOplaxMonoidal (pullback.{u} ψ)
  refine { unit := ?_, tensor := fun M N ↦ ?_ }
  · rw [← cancel_mono (Functor.OplaxMonoidal.η
      (pullback.{u} (F := F ⋙ G) (R := ringCatSheaf T)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)))]
    rw [Category.assoc]
    have hη := congrArg ((pullbackComp φ ψ).hom.app (𝟙_ _) ≫ ·) (pullback_comp_η φ ψ)
    simp only [Iso.hom_inv_id_app_assoc] at hη
    erw [hη, ← Functor.OplaxMonoidal.comp_η, Functor.Monoidal.ε_η]
    exact (Functor.Monoidal.ε_η _).symm
  · rw [← cancel_epi (Functor.OplaxMonoidal.δ (pullback.{u} φ ⋙ pullback.{u} ψ) M N),
      ← cancel_mono (Functor.OplaxMonoidal.δ (pullback.{u} (F := F ⋙ G) (R := ringCatSheaf T)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)) M N)]
    simp only [Category.assoc, Functor.Monoidal.δ_μ_assoc, Functor.Monoidal.μ_δ,
      Category.comp_id]
    have hδ := congrArg ((pullbackComp φ ψ).hom.app (M ⊗ N) ≫ ·)
      (pullback_comp_δ φ ψ M N)
    simp only [Iso.hom_inv_id_app_assoc] at hδ
    rw [Functor.OplaxMonoidal.comp_δ, Category.assoc]
    exact hδ

/-- The composition isomorphism of pullbacks along composable morphisms of ringed spaces is
monoidal. -/
instance isMonoidal_pullbackComp_hom
    {X Y Z : TopCat.{u}} {f : Y ⟶ X} {g : Z ⟶ Y}
    {𝒪X : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    {𝒪Y : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}}
    {𝒪Z : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u}}
    (φ : ringCatSheaf 𝒪X ⟶
      ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Y))
    (ψ : ringCatSheaf 𝒪Y ⟶
      ((Opens.map g).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Z))
    [(pushforward.{u} φ).IsRightAdjoint] [(pushforward.{u} ψ).IsRightAdjoint] :
    NatTrans.IsMonoidal (pullbackComp φ ψ).hom :=
  isMonoidal_pullbackComp_hom_of_isIso φ ψ

end Coherence

end SheafOfModules

end
