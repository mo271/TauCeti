/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pullback.Monoidal
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Identity
public import TauCeti.AlgebraicGeometry.Modules.Stalk

/-!
# Strong symmetric monoidal pullback of all modules on schemes

For any morphism of schemes `f : X ⟶ Y`, pullback of modules `Scheme.Modules.pullback f` is a
strong symmetric monoidal functor on the full category `Y.Modules` of all `𝒪_Y`-modules, with no
quasi-coherence, finiteness, or flatness hypotheses.

The stalk of a pulled-back module `f^* M` at `x : X` is canonically identified with the extension
of scalars of the stalk `M_{f(x)}` along `f.stalkMap x` (`Scheme.Modules.pullbackStalkIso`),
specializing the ringed-space isomorphism `SheafOfModules.pullbackStalkIso` via the identification
`Scheme.Hom.ringStalkMap_eq_stalkMap`. The invertibility of the canonical oplax tensor comparison
`Functor.OplaxMonoidal.δ (pullback f) M N` for arbitrary modules `M` and `N`
(`Scheme.Modules.isIso_pullback_δ`) then specializes `SheafOfModules.isIso_pullback_δ`, yielding
the strong symmetric monoidal structure `Scheme.Modules.pullbackMonoidal` and
`Scheme.Modules.pullbackBraided`.

We also record the compatibility of the pullback tensor comparison with free sheaves
(`Scheme.Modules.pullback_δ_free`), and the monoidal coherence of the identity, composition, and
congruence isomorphisms of module pullback (`Scheme.Modules.isMonoidal_pullbackId_hom`,
`Scheme.Modules.isMonoidal_pullbackComp_hom`, and `Scheme.Modules.isMonoidal_pullbackCongr_hom`).

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.ringStalkMap_eq_stalkMap`: identifies the ring-sheaf stalk map of
  `f.toRingCatSheafHom` with `f.stalkMap x`;
* `AlgebraicGeometry.Scheme.Modules.pullbackStalkIso`: canonical natural isomorphism
  `(stalkFunctorCommRing Y.sheaf (f x)) ⋙ extendScalars (f.stalkMap x).hom ≅`
  `pullback f ⋙ stalkFunctorCommRing X.sheaf x`, evaluated on pure tensors of germs by
  `AlgebraicGeometry.Scheme.Modules.pullbackStalkIso_hom_app_tmul_germ`;
* `AlgebraicGeometry.Scheme.Modules.isIso_pullback_δ`: the canonical tensor comparison
  `f^* (M ⊗ N) ⟶ f^* M ⊗ f^* N` is an isomorphism for all `𝒪_Y`-modules `M` and `N`;
* `AlgebraicGeometry.Scheme.Modules.pullbackMonoidal` and
  `AlgebraicGeometry.Scheme.Modules.pullbackBraided`: the strong symmetric monoidal structure on
  `Scheme.Modules.pullback f`, with `Scheme.Modules.pullback_ε`;
* `AlgebraicGeometry.Scheme.Modules.isMonoidal_pullbackId_hom`,
  `AlgebraicGeometry.Scheme.Modules.isMonoidal_pullbackComp_hom`, and
  `AlgebraicGeometry.Scheme.Modules.isMonoidal_pullbackCongr_hom`: monoidal coherence of the
  identity, composition, and congruence isomorphisms of module pullback;
* `AlgebraicGeometry.Scheme.Modules.pullback_δ_free`: compatibility of the pullback tensor
  comparison with free modules.

## References

* The Stacks Project, *Modules on Ringed Spaces*, Lemma 0098 (stalks of pullbacks) and
  *Sheaves of Modules*, Lemma 03EL (pullback of a tensor product).
-/

public section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open scoped ChangeOfRings TensorProduct

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

/-- For a morphism of schemes `f : X ⟶ Y` and `x : X`, the ring stalk map induced by
`f.toRingCatSheafHom` coincides with `f.stalkMap x`. -/
@[simp]
theorem Hom.ringStalkMap_eq_stalkMap (f : X ⟶ Y) (x : X) :
    SheafOfModules.ringStalkMap f.toRingCatSheafHom x = f.stalkMap x := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hx
  ext r
  exact (SheafOfModules.ringStalkMap_germ f.toRingCatSheafHom x U hx r).trans
    (Scheme.Hom.germ_stalkMap_apply f U x hx r).symm

namespace Modules

private lemma extendScalars_eqToIso_inv_app_tmul {R S : CommRingCat.{u}}
    {ρ₁ ρ₂ : R ⟶ S} (h : ρ₁ = ρ₂) (M : ModuleCat.{u} R) (a : S) (m : M) :
    (eqToIso (congrArg (fun ρ : R ⟶ S ↦ ModuleCat.extendScalars ρ.hom) h)).inv.app M
        (a ⊗ₜ[R, ρ₂.hom] m) =
      a ⊗ₜ[R, ρ₁.hom] m := by
  subst h
  rfl

/-- The stalk of the pullback `f^* M` of an `𝒪_Y`-module `M` at `x : X` is naturally isomorphic
to the extension of scalars of the stalk `M_{f(x)}` along `f.stalkMap x`. -/
def pullbackStalkIso (f : X ⟶ Y) (x : X) :
    SheafOfModules.stalkFunctorCommRing Y.sheaf (f x) ⋙
        ModuleCat.extendScalars (f.stalkMap x).hom ≅
      pullback f ⋙ SheafOfModules.stalkFunctorCommRing X.sheaf x :=
  Functor.isoWhiskerLeft (SheafOfModules.stalkFunctorCommRing Y.sheaf (f x))
      (eqToIso (congrArg (fun ρ : Y.presheaf.stalk (f x) ⟶ X.presheaf.stalk x ↦
        ModuleCat.extendScalars ρ.hom) (f.ringStalkMap_eq_stalkMap x))).symm ≪≫
    SheafOfModules.pullbackStalkIso f.toRingCatSheafHom x

/-- On a pure tensor `a ⊗ₜ germ_U(m)`, `pullbackStalkIso` maps to `a` times the germ of the
adjunction unit applied to `m`. -/
@[simp]
theorem pullbackStalkIso_hom_app_tmul_germ (f : X ⟶ Y) (x : X) (M : Y.Modules)
    (U : Y.Opens) (hx : f x ∈ U) (a : X.presheaf.stalk x) (m : Γ(M, U)) :
    (pullbackStalkIso f x).hom.app M
        (a ⊗ₜ[Y.presheaf.stalk (f x), (f.stalkMap x).hom] M.presheaf.germ U (f x) hx m) =
      a • ((pullback f).obj M).presheaf.germ (f ⁻¹ᵁ U) x hx
        (((pullbackPushforwardAdjunction f).unit.app M).val.app (op U) m) :=
  (congrArg ((SheafOfModules.pullbackStalkIso f.toRingCatSheafHom x).hom.app M)
    (extendScalars_eqToIso_inv_app_tmul (f.ringStalkMap_eq_stalkMap x)
      ((SheafOfModules.stalkFunctorCommRing Y.sheaf (f x)).obj M) a
      (M.presheaf.germ U (f x) hx m))).trans
    (SheafOfModules.pullbackStalkIso_hom_app_tmul_germ f.toRingCatSheafHom x M U hx a m)

/-- The canonical tensor comparison `f^* (M ⊗ N) ⟶ f^* M ⊗ f^* N` of module pullback along any
morphism of schemes is an isomorphism for all `𝒪_Y`-modules `M` and `N`, with no quasi-coherence,
finiteness, or flatness hypotheses. -/
instance isIso_pullback_δ (f : X ⟶ Y) (M N : Y.Modules) :
    IsIso (Functor.OplaxMonoidal.δ (pullback f) M N) :=
  SheafOfModules.isIso_pullback_δ f.toRingCatSheafHom M N

/-- Pullback of modules along a morphism of schemes is a strong monoidal functor, whose oplax
structure is the canonical `Scheme.Modules.pullbackOplaxMonoidal`. -/
instance pullbackMonoidal (f : X ⟶ Y) : (pullback f).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal (pullback f)

/-- Pullback of modules along a morphism of schemes is a strong symmetric monoidal functor. -/
instance pullbackBraided (f : X ⟶ Y) : (pullback f).Braided where
  toMonoidal := pullbackMonoidal f
  braided M N := by
    rw [← cancel_epi (Functor.OplaxMonoidal.δ (pullback f) M N),
      ← cancel_mono (Functor.OplaxMonoidal.δ (pullback f) N M)]
    simp only [Category.assoc, Functor.Monoidal.δ_μ_assoc, Functor.Monoidal.μ_δ,
      Category.comp_id]
    exact pullback_map_braiding_hom_comp_δ f M N

/-- The lax unit map of module pullback on schemes is the inverse of `pullbackObjUnitIso f`. -/
@[simp]
theorem pullback_ε (f : X ⟶ Y) :
    Functor.LaxMonoidal.ε (pullback f) = (pullbackObjUnitIso f).inv :=
  (Iso.comp_hom_eq_id _).mp ((congrArg (_ ≫ ·) (pullback_η f).symm).trans
    (Functor.Monoidal.ε_η (pullback f)))

/-- The identity isomorphism of module pullback on a scheme is monoidal. -/
instance isMonoidal_pullbackId_hom (X : Scheme.{u}) :
    NatTrans.IsMonoidal (pullbackId X).hom where
  unit := by
    rw [pullback_ε, Functor.LaxMonoidal.id_ε, ← pullbackObjUnitIso_id, Iso.inv_hom_id]
  tensor M N := by
    rw [← cancel_epi (Functor.OplaxMonoidal.δ (pullback (𝟙 X)) M N)]
    simp only [Functor.Monoidal.δ_μ_assoc, Functor.LaxMonoidal.id_μ, Category.comp_id,
      pullback_id_δ]

/-- The composition isomorphism of module pullback along composable morphisms of schemes is
monoidal. -/
instance isMonoidal_pullbackComp_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.IsMonoidal (pullbackComp f g).hom where
  unit := by
    rw [Functor.LaxMonoidal.comp_ε, pullback_ε, pullback_ε, pullback_ε, Category.assoc]
    exact pullbackObjUnitIso_inv_comp f g
  tensor M N := by
    rw [Functor.LaxMonoidal.comp_μ, ← Functor.Monoidal.inv_δ, ← Functor.Monoidal.inv_δ,
      ← Functor.Monoidal.inv_δ, Category.assoc]
    exact inv_δ_comp_pullbackComp_hom_app f g M N

/-- The identification of module pullbacks along equal morphisms of schemes is monoidal. -/
instance isMonoidal_pullbackCongr_hom {f f' : X ⟶ Y} (hf : f = f') :
    NatTrans.IsMonoidal (pullbackCongr hf).hom := by
  subst hf
  have h : (pullbackCongr (rfl : f = f)).hom = 𝟙 (pullback f) := by
    simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom]
  rw [h]
  infer_instance

/-- On free `𝒪_Y`-modules, the pullback tensor comparison is compatible with
`SheafOfModules.pullbackObjFreeIso` and `TauCeti.SheafOfModules.freeTensorFreeIso`. -/
@[reassoc]
theorem pullback_δ_free (f : X ⟶ Y) (I I' : Type u) :
    Functor.OplaxMonoidal.δ (pullback f)
        (SheafOfModules.free (R := Y.ringCatSheaf) I)
        (SheafOfModules.free (R := Y.ringCatSheaf) I') ≫
      ((SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I).hom ⊗ₘ
        (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I').hom) ≫
      (TauCeti.SheafOfModules.freeTensorFreeIso (R := X.sheaf) I I').hom =
    (pullback f).map (TauCeti.SheafOfModules.freeTensorFreeIso (R := Y.sheaf) I I').hom ≫
      (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (I × I')).hom :=
  SheafOfModules.pullback_δ_free f.toRingCatSheafHom I I'

end Modules

end AlgebraicGeometry.Scheme

end
