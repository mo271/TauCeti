/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.Basic
public import TauCeti.AlgebraicGeometry.GroupScheme.BaseChange

/-!
# Base change of abelian schemes

This file develops base change of abelian schemes along an arbitrary morphism of schemes
`f : T ⟶ S`.

Pullback in the `Over` category preserves properness, smoothness, and geometric connectedness, and
carries the group-object structure via Mathlib's `Functor.grpObjObj` instance for lax monoidal
functors. Thus `A.baseChange f` is an abelian scheme over `T`. Pulling back homomorphisms gives
the functor `baseChangeFunctor f : AbelianScheme S ⥤ AbelianScheme T`, which satisfies the
identity and composition pseudofunctor laws (`baseChangeIdNatIso`, `baseChangeCompNatIso`) and
preserves the identity abelian scheme (`baseChangeIdentityIso`) and integer multiplication
(`baseChange_mulBy`).

Finally, `baseChangePointMulEquiv` transports `TauCeti.GroupScheme.baseChangePointMulEquiv` to
`A.baseChange f`, giving a multiplicative equivalence between `V`-points of `A.baseChange f` and
`((Over.map f).obj V)`-points of `A`, together with naturality in `V`, compatibility with
postcomposition by homomorphisms, and identity/composition coherence.

## Main declarations

* `TauCeti.AlgebraicGeometry.AbelianScheme.baseChange`: base change of an abelian scheme along
  `f : T ⟶ S`.
* `TauCeti.AlgebraicGeometry.AbelianScheme.Hom.baseChange`: base change of a homomorphism.
* `TauCeti.AlgebraicGeometry.AbelianScheme.baseChangeFunctor`: the base-change functor
  `AbelianScheme S ⥤ AbelianScheme T`.
* `TauCeti.AlgebraicGeometry.AbelianScheme.baseChangeIdIso`, `baseChangeIdNatIso`: coherence
  with the identity base morphism.
* `TauCeti.AlgebraicGeometry.AbelianScheme.baseChangeCompIso`, `baseChangeCompNatIso`: coherence
  with composition of base morphisms.
* `TauCeti.AlgebraicGeometry.AbelianScheme.baseChangeIdentityIso`: base change preserves the
  identity abelian scheme.
* `TauCeti.AlgebraicGeometry.AbelianScheme.baseChange_mulBy`: base change commutes with integer
  multiplication.
* `TauCeti.AlgebraicGeometry.AbelianScheme.baseChangePointMulEquiv`: multiplicative equivalence
  for `V`-points of a base-changed abelian scheme, with naturality and coherence laws.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianScheme

variable {S T U : Scheme.{u}}

noncomputable section

/-! ### Base change of abelian schemes -/

/-- The base change of an abelian scheme `A` over `S` along a morphism of schemes `f : T ⟶ S`,
obtained by pulling back `A.toOver` along `f`. -/
def baseChange (A : AbelianScheme S) (f : T ⟶ S) : AbelianScheme T where
  toOver := (Over.pullback f).obj A.toOver
  grpObj := Functor.grpObjObj
  isProper := inferInstanceAs (IsProper (pullback.snd A.toOver.hom f))
  smooth := inferInstanceAs (Smooth (pullback.snd A.toOver.hom f))
  geometricallyConnected := inferInstanceAs (GeometricallyConnected (pullback.snd A.toOver.hom f))

/-- The underlying `Over T` object of a base change is the pullback along `f`. -/
@[simp]
lemma baseChange_toOver (A : AbelianScheme S) (f : T ⟶ S) :
    (A.baseChange f).toOver = (Over.pullback f).obj A.toOver :=
  (rfl)

/-- The underlying scheme of a base change is the fibre product over `S`. -/
@[simp]
lemma baseChange_toScheme (A : AbelianScheme S) (f : T ⟶ S) :
    (A.baseChange f).toScheme = pullback A.toOver.hom f := by
  rw [toScheme, baseChange_toOver]
  rfl

/-- Bundling the underlying `Over` object of a base change with `Grp.mk` agrees with applying
`(Over.pullback f).mapGrp`. -/
lemma grpMk_baseChange_toOver (A : AbelianScheme S) (f : T ⟶ S) :
    Grp.mk (A.baseChange f).toOver = (Over.pullback f).mapGrp.obj (Grp.mk A.toOver) := by
  unfold baseChange
  rfl

/-- The unit of a base-changed abelian scheme is the pullback of the unit with the monoidal
comparison for `Over.pullback`. -/
@[simp]
lemma baseChange_one (A : AbelianScheme S) (f : T ⟶ S) :
    η[(A.baseChange f).toOver] ≫ eqToHom (baseChange_toOver A f) =
      Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map η[A.toOver] := by
  unfold baseChange
  simp

/-- The multiplication of a base-changed abelian scheme is the pullback of the multiplication with
the monoidal comparison for `Over.pullback`. -/
@[simp]
lemma baseChange_mul (A : AbelianScheme S) (f : T ⟶ S) :
    μ[(A.baseChange f).toOver] ≫ eqToHom (baseChange_toOver A f) =
      (eqToHom (baseChange_toOver A f) ⊗ₘ eqToHom (baseChange_toOver A f)) ≫
        Functor.LaxMonoidal.μ (Over.pullback f) A.toOver A.toOver ≫
        (Over.pullback f).map μ[A.toOver] := by
  unfold baseChange
  -- After `unfold baseChange`, the `eqToHom` casts are between syntactically equal objects, so
  -- `change` replaces them with identities before `simp`.
  change _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ _
  simp [Functor.obj.μ_def]

/-- The inversion of a base-changed abelian scheme is the pullback of the inversion. -/
@[simp]
lemma baseChange_inv (A : AbelianScheme S) (f : T ⟶ S) :
    ι[(A.baseChange f).toOver] ≫ eqToHom (baseChange_toOver A f) =
      eqToHom (baseChange_toOver A f) ≫ (Over.pullback f).map ι[A.toOver] := by
  unfold baseChange
  -- After `unfold baseChange`, the `eqToHom` cast on the right is between identical objects.
  change _ = 𝟙 _ ≫ _
  simp [Functor.obj.ι_def]

/-- The transport isomorphism along `baseChange_toOver` is a group-object homomorphism. -/
instance isMonHom_eqToHom_baseChange_toOver (A : AbelianScheme S) (f : T ⟶ S) :
    IsMonHom (eqToHom (baseChange_toOver A f)) where
  one_hom := by
    rw [baseChange_one]
    exact (Functor.obj.η_def (F := Over.pullback f) A.toOver).symm
  mul_hom := by
    rw [baseChange_mul]
    simp only [Functor.obj.μ_def]

/-- The inverse transport isomorphism along `baseChange_toOver` is a group-object homomorphism. -/
instance isMonHom_eqToHom_baseChange_toOver_symm (A : AbelianScheme S) (f : T ⟶ S) :
    IsMonHom (eqToHom (baseChange_toOver A f).symm) :=
  have : IsMonHom (eqToIso (baseChange_toOver A f)).hom :=
    isMonHom_eqToHom_baseChange_toOver A f
  inferInstanceAs (IsMonHom (eqToIso (baseChange_toOver A f)).inv)

/-! ### Functoriality of base change -/

/-- Base change of a homomorphism of abelian schemes along a base morphism `f : T ⟶ S`. -/
def Hom.baseChange {A B : AbelianScheme S} (g : A ⟶ B) (f : T ⟶ S) :
    A.baseChange f ⟶ B.baseChange f :=
  let h : (A.baseChange f).toOver ⟶ (B.baseChange f).toOver :=
    eqToHom (baseChange_toOver A f) ≫
      (Over.pullback f).map (Hom.toOverHom g) ≫
      eqToHom (baseChange_toOver B f).symm
  have : IsMonHom h := by dsimp [h]; infer_instance
  Hom.mk' h (IsMonHom.one_hom h) (IsMonHom.mul_hom h)

/-- The underlying morphism over `T` of a base-changed homomorphism is the pullback of its
underlying morphism over `S`. -/
@[simp]
lemma Hom.toOverHom_baseChange {A B : AbelianScheme S} (g : A ⟶ B) (f : T ⟶ S) :
    Hom.toOverHom (Hom.baseChange g f) =
      eqToHom (baseChange_toOver A f) ≫
        (Over.pullback f).map (Hom.toOverHom g) ≫
        eqToHom (baseChange_toOver B f).symm := by
  unfold Hom.baseChange
  exact Hom.toOverHom_mk' _ _ _

/-- The underlying scheme morphism of a base-changed homomorphism is the left component of the
pulled-back morphism in `Over T`. -/
@[simp]
lemma Hom.toSchemeHom_baseChange {A B : AbelianScheme S} (g : A ⟶ B) (f : T ⟶ S) :
    Hom.toSchemeHom (Hom.baseChange g f) =
      (eqToHom (baseChange_toOver A f) ≫
        (Over.pullback f).map (Hom.toOverHom g) ≫
        eqToHom (baseChange_toOver B f).symm).left :=
  congrArg Over.Hom.left (Hom.toOverHom_baseChange g f)

/-- Base change preserves identity homomorphisms. -/
@[simp]
lemma Hom.baseChange_id (A : AbelianScheme S) (f : T ⟶ S) :
    Hom.baseChange (𝟙 A) f = 𝟙 (A.baseChange f) := by
  apply Hom.toOverHom_injective
  simp

/-- Base change preserves composition of homomorphisms. -/
@[simp, reassoc]
lemma Hom.baseChange_comp {A B C : AbelianScheme S} (g : A ⟶ B) (h : B ⟶ C) (f : T ⟶ S) :
    Hom.baseChange (g ≫ h) f = Hom.baseChange g f ≫ Hom.baseChange h f := by
  apply Hom.toOverHom_injective
  simp [Category.assoc]

/-- Base change along `f : T ⟶ S` as a functor `AbelianScheme S ⥤ AbelianScheme T`. -/
def baseChangeFunctor (f : T ⟶ S) : AbelianScheme S ⥤ AbelianScheme T where
  obj A := A.baseChange f
  map g := Hom.baseChange g f
  map_id A := Hom.baseChange_id A f
  map_comp g h := Hom.baseChange_comp g h f

@[simp]
lemma baseChangeFunctor_obj (f : T ⟶ S) (A : AbelianScheme S) :
    (baseChangeFunctor f).obj A = A.baseChange f :=
  (rfl)

@[simp]
lemma baseChangeFunctor_map {A B : AbelianScheme S} (f : T ⟶ S) (g : A ⟶ B) :
    (baseChangeFunctor f).map g =
      eqToHom (baseChangeFunctor_obj f A) ≫ Hom.baseChange g f ≫
        eqToHom (baseChangeFunctor_obj f B).symm := by
  unfold baseChangeFunctor
  exact (rfl)

/-! ### Pseudofunctor coherence -/

private lemma isMonHom_pullbackId_hom (A : AbelianScheme S) :
    IsMonHom (Over.pullbackId.hom.app A.toOver) := by
  have h := ((GroupScheme.pullbackMapGrpIdIso S).hom.app (Grp.mk A.toOver)).hom.isMonHom_hom
  rw [GroupScheme.pullbackMapGrpIdIso_hom_app_hom] at h
  exact h

/-- Base change along the identity morphism is isomorphic to the original abelian scheme. -/
def baseChangeIdIso (A : AbelianScheme S) : A.baseChange (𝟙 S) ≅ A := by
  let eMid : (Over.pullback (𝟙 S)).obj A.toOver ≅ A.toOver := Over.pullbackId.app A.toOver
  have : IsMonHom eMid.hom := isMonHom_pullbackId_hom A
  have : IsMonHom (eqToIso (baseChange_toOver A (𝟙 S)) ≪≫ eMid).hom := by
    dsimp only [Iso.trans_hom, eqToIso.hom]
    infer_instance
  exact mkIso' (eqToIso (baseChange_toOver A (𝟙 S)) ≪≫ eMid)

@[simp]
lemma toOverHom_baseChangeIdIso_hom (A : AbelianScheme S) :
    Hom.toOverHom (baseChangeIdIso A).hom =
      eqToHom (baseChange_toOver A (𝟙 S)) ≫ Over.pullbackId.hom.app A.toOver := by
  unfold baseChangeIdIso
  simp

@[simp]
lemma toOverHom_baseChangeIdIso_inv (A : AbelianScheme S) :
    Hom.toOverHom (baseChangeIdIso A).inv =
      Over.pullbackId.inv.app A.toOver ≫ eqToHom (baseChange_toOver A (𝟙 S)).symm := by
  unfold baseChangeIdIso
  simp

/-- Base change along `𝟙 S` is naturally isomorphic to the identity functor. -/
def baseChangeIdNatIso :
    baseChangeFunctor (𝟙 S) ≅ 𝟭 (AbelianScheme S) :=
  NatIso.ofComponents baseChangeIdIso fun {A B} g ↦ by
    apply Hom.toOverHom_injective
    dsimp only [baseChangeFunctor, Functor.id_obj, Functor.id_map]
    rw [Hom.toOverHom_comp, Hom.toOverHom_comp, Hom.toOverHom_baseChange,
      toOverHom_baseChangeIdIso_hom, toOverHom_baseChangeIdIso_hom]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact congrArg (eqToHom (baseChange_toOver A (𝟙 S)) ≫ ·)
      (Over.pullbackId.hom.naturality (Hom.toOverHom g))

/-- The underlying `Over U` object of an iterated base change is the iterated pullback. -/
lemma baseChange_toOver_comp (A : AbelianScheme S) (f₁ : U ⟶ T) (f₂ : T ⟶ S) :
    ((A.baseChange f₂).baseChange f₁).toOver =
      (Over.pullback f₁).obj ((Over.pullback f₂).obj A.toOver) :=
  (baseChange_toOver (A.baseChange f₂) f₁).trans
    (congrArg ((Over.pullback f₁).obj) (baseChange_toOver A f₂))

private lemma isMonHom_pullbackComp_hom (A : AbelianScheme S) (f₁ : U ⟶ T) (f₂ : T ⟶ S) :
    IsMonHom (M := (Over.pullback (f₁ ≫ f₂)).obj A.toOver)
      (N := (Over.pullback f₁).obj ((Over.pullback f₂).obj A.toOver))
      ((Over.pullbackComp f₁ f₂).hom.app A.toOver) := by
  have h :=
    ((GroupScheme.pullbackMapGrpCompIso f₁ f₂).hom.app (Grp.mk A.toOver)).hom.isMonHom_hom
  rw [GroupScheme.pullbackMapGrpCompIso_hom_app_hom] at h
  exact h

private lemma isMonHom_eqToHom_baseChange_toOver_comp_symm
    (A : AbelianScheme S) (f₁ : U ⟶ T) (f₂ : T ⟶ S) :
    IsMonHom (eqToHom (baseChange_toOver_comp A f₁ f₂).symm) := by
  have heq : eqToHom (baseChange_toOver_comp A f₁ f₂).symm =
      (Over.pullback f₁).map (eqToHom (baseChange_toOver A f₂).symm) ≫
        eqToHom (baseChange_toOver (A.baseChange f₂) f₁).symm := by
    rw [eqToHom_map]
    simp only [eqToHom_trans]
  rw [heq]
  infer_instance

/-- Base change along a composite `f₁ ≫ f₂` is isomorphic to iterated base change along `f₂`
followed by `f₁`. -/
def baseChangeCompIso (A : AbelianScheme S) (f₁ : U ⟶ T) (f₂ : T ⟶ S) :
    A.baseChange (f₁ ≫ f₂) ≅ (A.baseChange f₂).baseChange f₁ := by
  let eMid : (Over.pullback (f₁ ≫ f₂)).obj A.toOver ≅
      (Over.pullback f₁).obj ((Over.pullback f₂).obj A.toOver) :=
    (Over.pullbackComp f₁ f₂).app A.toOver
  have : IsMonHom eMid.hom := isMonHom_pullbackComp_hom A f₁ f₂
  have : IsMonHom (eqToHom (baseChange_toOver_comp A f₁ f₂).symm) :=
    isMonHom_eqToHom_baseChange_toOver_comp_symm A f₁ f₂
  have : IsMonHom (eqToIso (baseChange_toOver A (f₁ ≫ f₂)) ≪≫ eMid ≪≫
      (eqToIso (baseChange_toOver_comp A f₁ f₂)).symm).hom := by
    dsimp only [Iso.trans_hom, eqToIso.hom, Iso.symm_hom, eqToIso.inv]
    infer_instance
  exact mkIso' (eqToIso (baseChange_toOver A (f₁ ≫ f₂)) ≪≫ eMid ≪≫
    (eqToIso (baseChange_toOver_comp A f₁ f₂)).symm)

@[simp]
lemma toOverHom_baseChangeCompIso_hom (A : AbelianScheme S) (f₁ : U ⟶ T) (f₂ : T ⟶ S) :
    Hom.toOverHom (baseChangeCompIso A f₁ f₂).hom =
      eqToHom (baseChange_toOver A (f₁ ≫ f₂)) ≫
        (Over.pullbackComp f₁ f₂).hom.app A.toOver ≫
        eqToHom (baseChange_toOver_comp A f₁ f₂).symm := by
  unfold baseChangeCompIso
  simp

@[simp]
lemma toOverHom_baseChangeCompIso_inv (A : AbelianScheme S) (f₁ : U ⟶ T) (f₂ : T ⟶ S) :
    Hom.toOverHom (baseChangeCompIso A f₁ f₂).inv =
      eqToHom (baseChange_toOver_comp A f₁ f₂) ≫
        (Over.pullbackComp f₁ f₂).inv.app A.toOver ≫
        eqToHom (baseChange_toOver A (f₁ ≫ f₂)).symm := by
  unfold baseChangeCompIso
  simp [Category.assoc]

/-- Base change along `f₁ ≫ f₂` is naturally isomorphic to the composite of base-change
functors. -/
def baseChangeCompNatIso (f₁ : U ⟶ T) (f₂ : T ⟶ S) :
    baseChangeFunctor (f₁ ≫ f₂) ≅ baseChangeFunctor f₂ ⋙ baseChangeFunctor f₁ :=
  NatIso.ofComponents (fun A ↦ baseChangeCompIso A f₁ f₂) fun {A B} g ↦ by
    apply Hom.toOverHom_injective
    dsimp only [baseChangeFunctor, Functor.comp_map]
    rw [Hom.toOverHom_comp, Hom.toOverHom_comp, Hom.toOverHom_baseChange,
      toOverHom_baseChangeCompIso_hom, toOverHom_baseChangeCompIso_hom,
      Hom.toOverHom_baseChange, Hom.toOverHom_baseChange]
    simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    have hnat : (Over.pullback (f₁ ≫ f₂)).map (Hom.toOverHom g) ≫
          (Over.pullbackComp f₁ f₂).hom.app B.toOver =
        (Over.pullbackComp f₁ f₂).hom.app A.toOver ≫
          (Over.pullback f₁).map ((Over.pullback f₂).map (Hom.toOverHom g)) :=
      (Over.pullbackComp f₁ f₂).hom.naturality (Hom.toOverHom g)
    rw [← Category.assoc ((Over.pullback (f₁ ≫ f₂)).map _), hnat, Category.assoc]
    simp only [eqToHom_trans]

/-! ### Preservation of identity and integer multiplication -/

/-- Base change of the identity abelian scheme is canonically isomorphic to the identity abelian
scheme over the new base, since both are terminal objects of `AbelianScheme T`. -/
def baseChangeIdentityIso (f : T ⟶ S) : (identity S).baseChange f ≅ identity T where
  hom := toIdentity ((identity S).baseChange f)
  inv := fromIdentity ((identity S).baseChange f)
  hom_inv_id := by
    apply Hom.ext
    have hiso : IsIso (identity S).toOver.hom := by
      have h := (toSchemeHom_toIdentity (identity S)).symm
      have hid : toIdentity (identity S) = 𝟙 (identity S) := Subsingleton.elim _ _
      rw [hid, Hom.toSchemeHom_id, Category.id_comp] at h
      rw [h]
      infer_instance
    have : IsIso ((identity S).baseChange f).toOver.hom :=
      inferInstanceAs (IsIso (pullback.snd (identity S).toOver.hom f))
    rw [← cancel_mono ((identity S).baseChange f).toOver.hom, Hom.toSchemeHom_comp_hom,
      Hom.toSchemeHom_id, Category.id_comp]
  inv_hom_id := Subsingleton.elim _ _

/-- Base change commutes with integer multiplication on an abelian scheme. -/
lemma baseChange_mulBy (A : AbelianScheme S) (f : T ⟶ S) (n : ℤ) :
    (A.baseChange f).mulBy n =
      eqToHom (baseChange_toOver A f) ≫
        (Over.pullback f).map (A.mulBy n) ≫
        eqToHom (baseChange_toOver A f).symm := by
  let φ : (A.toOver ⟶ A.toOver) →*
      ((Over.pullback f).obj A.toOver ⟶ (Over.pullback f).obj A.toOver) :=
    { toFun := (Over.pullback f).map
      map_one' := Functor.map_one (Over.pullback f)
      map_mul' := fun x y ↦ Functor.map_mul (Over.pullback f) x y }
  have hz : (Over.pullback f).map (A.mulBy n) = (𝟙 ((Over.pullback f).obj A.toOver)) ^ n := by
    rw [mulBy_def, ← CategoryTheory.Functor.map_id (Over.pullback f) A.toOver]
    exact map_zpow φ (𝟙 A.toOver) n
  rw [mulBy_def, hz]
  have he : ((𝟙 (A.baseChange f).toOver) ^ n) ≫ eqToHom (baseChange_toOver A f) =
      eqToHom (baseChange_toOver A f) ≫ ((𝟙 ((Over.pullback f).obj A.toOver)) ^ n) := by
    rw [GrpObj.zpow_comp, Category.id_comp, GrpObj.comp_zpow, Category.comp_id]
  rw [← cancel_mono (eqToHom (baseChange_toOver A f)), Category.assoc, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]
  exact he

/-! ### Point-group equivalence under base change -/

/-- Points of a base-changed abelian scheme `A.baseChange f` are points of `A` on the restricted
test scheme, with the same group law. -/
def baseChangePointMulEquiv (A : AbelianScheme S) (f : T ⟶ S) (V : Over T) :
    (V ⟶ (A.baseChange f).toOver) ≃* ((Over.map f).obj V ⟶ A.toOver) :=
  let : IsMonHom (eqToIso (baseChange_toOver A f)).hom :=
    isMonHom_eqToHom_baseChange_toOver A f
  (CategoryTheory.Hom.mulEquivCongrRight (eqToIso (baseChange_toOver A f)) V).trans
    (GroupScheme.baseChangePointMulEquiv f (Grp.mk A.toOver) V)

/-- On elements, `baseChangePointMulEquiv` is the pullback-adjunction equivalence composed with
transport along `baseChange_toOver`. -/
lemma baseChangePointMulEquiv_apply (A : AbelianScheme S) (f : T ⟶ S) (V : Over T)
    (p : V ⟶ (A.baseChange f).toOver) :
    baseChangePointMulEquiv A f V p =
      ((Over.mapPullbackAdj f).homEquiv V A.toOver).symm
        (p ≫ eqToHom (baseChange_toOver A f)) := by
  unfold baseChangePointMulEquiv
  exact GroupScheme.baseChangePointMulEquiv_apply f (Grp.mk A.toOver) V _

/-- Construct a point of `A.baseChange f` from a point of `A` via the pullback adjunction. -/
@[simp]
lemma baseChangePointMulEquiv_symm_apply (A : AbelianScheme S) (f : T ⟶ S) (V : Over T)
    (p : (Over.map f).obj V ⟶ A.toOver) :
    (baseChangePointMulEquiv A f V).symm p =
      (Over.mapPullbackAdj f).homEquiv V A.toOver p ≫ eqToHom (baseChange_toOver A f).symm := by
  apply (baseChangePointMulEquiv A f V).injective
  rw [MulEquiv.apply_symm_apply, baseChangePointMulEquiv_apply]
  simp

/-- On underlying schemes, `baseChangePointMulEquiv` postcomposes with `pullback.fst`. -/
@[simp]
lemma baseChangePointMulEquiv_apply_left (A : AbelianScheme S) (f : T ⟶ S) (V : Over T)
    (p : V ⟶ (A.baseChange f).toOver) :
    (baseChangePointMulEquiv A f V p).left =
      (p ≫ eqToHom (baseChange_toOver A f)).left ≫ pullback.fst A.toOver.hom f := by
  rw [baseChangePointMulEquiv_apply]
  rfl

/-- `baseChangePointMulEquiv` is natural with respect to precomposition by morphisms of test
schemes. -/
lemma baseChangePointMulEquiv_naturality_left (A : AbelianScheme S) (f : T ⟶ S)
    {V W : Over T} (h : W ⟶ V) (p : V ⟶ (A.baseChange f).toOver) :
    baseChangePointMulEquiv A f W (h ≫ p) =
      (Over.map f).map h ≫ baseChangePointMulEquiv A f V p := by
  rw [baseChangePointMulEquiv_apply, baseChangePointMulEquiv_apply, Category.assoc]
  exact (Over.mapPullbackAdj f).homEquiv_naturality_left_symm h
    (p ≫ eqToHom (baseChange_toOver A f))

/-- `baseChangePointMulEquiv` commutes with postcomposition by homomorphisms of abelian schemes. -/
lemma baseChangePointMulEquiv_postcomp {A B : AbelianScheme S} (g : A ⟶ B) (f : T ⟶ S)
    (V : Over T) (p : V ⟶ (A.baseChange f).toOver) :
    baseChangePointMulEquiv B f V (p ≫ Hom.toOverHom (Hom.baseChange g f)) =
      baseChangePointMulEquiv A f V p ≫ Hom.toOverHom g := by
  rw [baseChangePointMulEquiv_apply B f V, baseChangePointMulEquiv_apply A f V,
    Hom.toOverHom_baseChange]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  simpa only [Category.assoc] using
    (Over.mapPullbackAdj f).homEquiv_naturality_right_symm
      (p ≫ eqToHom (baseChange_toOver A f)) (Hom.toOverHom g)

/-- Under base change along `𝟙 S`, `baseChangePointMulEquiv` agrees with `baseChangeIdIso`. -/
lemma baseChangePointMulEquiv_id (A : AbelianScheme S) (V : Over S)
    (p : V ⟶ (A.baseChange (𝟙 S)).toOver) :
    (Over.mapId S).inv.app V ≫ baseChangePointMulEquiv A (𝟙 S) V p =
      p ≫ Hom.toOverHom (baseChangeIdIso A).hom := by
  rw [baseChangePointMulEquiv_apply, toOverHom_baseChangeIdIso_hom, ← Category.assoc]
  have h := GroupScheme.baseChangePointMulEquiv_id (Grp.mk A.toOver) V
    (p ≫ eqToHom (baseChange_toOver A (𝟙 S)))
  rw [GroupScheme.baseChangePointMulEquiv_apply, GroupScheme.pullbackMapGrpIdIso_hom_app_hom] at h
  exact h

/-- Iterating `baseChangePointMulEquiv` along `f₁` and `f₂` agrees with
`baseChangePointMulEquiv` along `f₁ ≫ f₂`, transported along `baseChangeCompIso`. -/
lemma baseChangePointMulEquiv_comp (A : AbelianScheme S) (f₁ : U ⟶ T) (f₂ : T ⟶ S)
    (V : Over U) (p : V ⟶ (A.baseChange (f₁ ≫ f₂)).toOver) :
    baseChangePointMulEquiv A f₂ ((Over.map f₁).obj V)
        (baseChangePointMulEquiv (A.baseChange f₂) f₁ V
          (p ≫ Hom.toOverHom (baseChangeCompIso A f₁ f₂).hom)) =
      (Over.mapComp f₁ f₂).inv.app V ≫ baseChangePointMulEquiv A (f₁ ≫ f₂) V p := by
  rw [baseChangePointMulEquiv_apply, baseChangePointMulEquiv_apply, baseChangePointMulEquiv_apply,
    toOverHom_baseChangeCompIso_hom]
  have h := GroupScheme.baseChangePointMulEquiv_comp f₁ f₂ (Grp.mk A.toOver) V
    (p ≫ eqToHom (baseChange_toOver A (f₁ ≫ f₂)))
  rw [GroupScheme.baseChangePointMulEquiv_apply, GroupScheme.baseChangePointMulEquiv_apply,
    GroupScheme.baseChangePointMulEquiv_apply, GroupScheme.pullbackMapGrpCompIso_hom_app_hom] at h
  have hstep : eqToHom (baseChange_toOver_comp A f₁ f₂).symm ≫
      eqToHom (baseChange_toOver (A.baseChange f₂) f₁) =
      (Over.pullback f₁).map (eqToHom (baseChange_toOver A f₂).symm) := by
    rw [eqToHom_map]
    simp only [eqToHom_trans]
  have hnat := (Over.mapPullbackAdj f₁).homEquiv_naturality_right_symm
    (p ≫ eqToHom (baseChange_toOver A (f₁ ≫ f₂)) ≫
      (Over.pullbackComp f₁ f₂).hom.app A.toOver)
    (eqToHom (baseChange_toOver A f₂).symm)
  simp only [Category.assoc] at h hstep hnat ⊢
  rw [hstep, hnat, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  exact h

end

end AbelianScheme

end AlgebraicGeometry

end TauCeti
