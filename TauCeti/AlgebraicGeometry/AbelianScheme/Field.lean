/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.Dimension
public import TauCeti.AlgebraicGeometry.AbelianVariety.End.Basic
public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.BaseChange
public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.Rigidity
public import TauCeti.AlgebraicGeometry.AbelianVariety.Product

/-!
# Equivalence between abelian schemes over a field and abelian varieties

Over the spectrum of a field `K`, an abelian scheme is the same mathematical object as an abelian
variety (`TauCeti.AlgebraicGeometry.AbelianVariety K`):
* Every abelian scheme over `Spec K` is smooth with geometrically connected fibres, hence
  geometrically integral (`AbelianScheme.geometricallyIntegral`), and therefore defines an
  `AbelianVariety K` (`toAbelianVariety`).
* Conversely, every `AbelianVariety K` is smooth and geometrically connected over `Spec K`
  (`AbelianVariety.smooth`, `AbelianVariety.geometricallyConnected`), and therefore defines an
  `AbelianScheme (Spec (.of K))` (`ofAbelianVariety`).

These two constructions are mutual inverses (`toAbelianVariety_ofAbelianVariety`,
`ofAbelianVariety_toAbelianVariety`) and extend to an equivalence of categories
`fieldEquivalence : AbelianScheme (Spec (.of K)) ≌ AbelianVariety K`. We verify that the adapters
preserve:
* commutativity of the group law (`isCommMonObj_of_field`) and rigidity of homomorphisms
  (`Hom.equivPointed`);
* the group-law operations (`η`, `μ`, `ι`), zero sections, and integer multiplication (`mulBy`);
* the trivial/identity object (`toAbelianVarietyIdentityIso`, `ofAbelianVarietyTrivialIso`);
* binary products (`toAbelianVarietyProdIso`, `ofAbelianVarietyProdIso`, compatible with
  projections);
* base change along any field extension `K → L` (`toAbelianVarietyBaseChangeIso`,
  `ofAbelianVarietyBaseChangeIso`, natural in homomorphisms);
* dimension (`relativeDimension_eq_dim_toAbelianVariety`, `relativeDimension_ofAbelianVariety`).

## Main declarations

* `TauCeti.AlgebraicGeometry.AbelianScheme.toAbelianVariety`, `ofAbelianVariety`: inverse adapters
  between `AbelianScheme (Spec (.of K))` and `AbelianVariety K`.
* `TauCeti.AlgebraicGeometry.AbelianScheme.fieldEquivalence`: categorical equivalence
  `AbelianScheme (Spec (.of K)) ≌ AbelianVariety K`.
* `TauCeti.AlgebraicGeometry.AbelianScheme.isCommMonObj_of_field`: commutativity over a field.
* `TauCeti.AlgebraicGeometry.AbelianScheme.Hom.equivPointed`: rigidity of homomorphisms over a
  field.
* `TauCeti.AlgebraicGeometry.AbelianScheme.toAbelianVariety_mulBy`, `ofAbelianVariety_mulBy`:
  compatibility with integer multiplication.
* `TauCeti.AlgebraicGeometry.AbelianScheme.toAbelianVarietyIdentityIso`,
  `ofAbelianVarietyTrivialIso`: preservation of the zero object.
* `TauCeti.AlgebraicGeometry.AbelianScheme.toAbelianVarietyProdIso`,
  `ofAbelianVarietyProdIso`: preservation of binary products.
* `TauCeti.AlgebraicGeometry.AbelianScheme.toAbelianVarietyBaseChangeIso`,
  `ofAbelianVarietyBaseChangeIso`: preservation of base change along field extensions.
* `TauCeti.AlgebraicGeometry.AbelianScheme.relativeDimension_eq_dim_toAbelianVariety`:
  compatibility of relative dimension with `AbelianVariety.dim`.

## References

* G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties*, Chapter I, §§1.1–1.2.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj TauCeti.AlgebraicGeometry.AbelianVariety.Hom

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianScheme

variable {K : Type u} [Field K]

noncomputable section

/-! ### Inverse adapters on objects -/

/-- View an abelian scheme over `Spec K` as an `AbelianVariety K`, recovering geometric
integrality from smoothness and geometric connectedness. -/
def toAbelianVariety (A : AbelianScheme (Spec (.of K))) : AbelianVariety K where
  toOver := A.toOver
  grpObj := A.grpObj
  isProper := A.isProper
  geometricallyIntegral := A.geometricallyIntegral

/-- View an `AbelianVariety K` as an abelian scheme over `Spec K`, using smoothness and geometric
connectedness of abelian varieties. -/
def ofAbelianVariety (A : AbelianVariety K) : AbelianScheme (Spec (.of K)) where
  toOver := A.toOver
  grpObj := A.grpObj
  isProper := A.isProper
  smooth := A.smooth
  geometricallyConnected := A.geometricallyConnected

@[simp]
lemma toAbelianVariety_ofAbelianVariety (A : AbelianVariety K) :
    (ofAbelianVariety A).toAbelianVariety = A :=
  (rfl)

@[simp]
lemma ofAbelianVariety_toAbelianVariety (A : AbelianScheme (Spec (.of K))) :
    ofAbelianVariety A.toAbelianVariety = A :=
  (rfl)

@[simp]
lemma toAbelianVariety_toOver (A : AbelianScheme (Spec (.of K))) :
    A.toAbelianVariety.toOver = A.toOver :=
  (rfl)

@[simp]
lemma ofAbelianVariety_toOver (A : AbelianVariety K) :
    (ofAbelianVariety A).toOver = A.toOver :=
  (rfl)

@[simp]
lemma toAbelianVariety_toScheme (A : AbelianScheme (Spec (.of K))) :
    A.toAbelianVariety.toScheme = A.toScheme := by
  rw [AbelianVariety.toScheme, toAbelianVariety_toOver]

@[simp]
lemma ofAbelianVariety_toScheme (A : AbelianVariety K) :
    (ofAbelianVariety A).toScheme = A.toScheme := by
  rw [toScheme, ofAbelianVariety_toOver]

/-- An abelian scheme over a field has a commutative group law. -/
instance isCommMonObj_of_field (A : AbelianScheme (Spec (.of K))) : IsCommMonObj A.toOver :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A.toOver

lemma toAbelianVariety_one (A : AbelianScheme (Spec (.of K))) :
    η[A.toAbelianVariety.toOver] ≫ eqToHom (toAbelianVariety_toOver A) = η[A.toOver] := by
  unfold toAbelianVariety
  -- After `unfold toAbelianVariety`, the `eqToHom` cast is between identical objects.
  change _ ≫ 𝟙 _ = _
  simp

lemma toAbelianVariety_mul (A : AbelianScheme (Spec (.of K))) :
    μ[A.toAbelianVariety.toOver] ≫ eqToHom (toAbelianVariety_toOver A) =
      (eqToHom (toAbelianVariety_toOver A) ⊗ₘ eqToHom (toAbelianVariety_toOver A)) ≫
        μ[A.toOver] := by
  unfold toAbelianVariety
  -- After `unfold toAbelianVariety`, the `eqToHom` casts are between identical objects.
  change _ ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ _
  simp

lemma toAbelianVariety_inv (A : AbelianScheme (Spec (.of K))) :
    ι[A.toAbelianVariety.toOver] ≫ eqToHom (toAbelianVariety_toOver A) =
      eqToHom (toAbelianVariety_toOver A) ≫ ι[A.toOver] := by
  unfold toAbelianVariety
  -- After `unfold toAbelianVariety`, the `eqToHom` casts are between identical objects.
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
  simp

@[simp]
lemma toAbelianVariety_zeroSection (A : AbelianScheme (Spec (.of K))) :
    A.toAbelianVariety.zeroSection ≫ eqToHom (toAbelianVariety_toScheme A) = A.zeroSection := by
  have h := congrArg Over.Hom.left (toAbelianVariety_one A)
  rw [Over.comp_left, Over.eqToHom_left] at h
  exact h

instance isMonHom_eqToHom_toAbelianVariety_toOver (A : AbelianScheme (Spec (.of K))) :
    IsMonHom (eqToHom (toAbelianVariety_toOver A)) where
  one_hom := toAbelianVariety_one A
  mul_hom := toAbelianVariety_mul A

instance isMonHom_eqToHom_toAbelianVariety_toOver_symm (A : AbelianScheme (Spec (.of K))) :
    IsMonHom (eqToHom (toAbelianVariety_toOver A).symm) :=
  have : IsMonHom (eqToIso (toAbelianVariety_toOver A)).hom :=
    isMonHom_eqToHom_toAbelianVariety_toOver A
  inferInstanceAs (IsMonHom (eqToIso (toAbelianVariety_toOver A)).inv)

lemma ofAbelianVariety_one (A : AbelianVariety K) :
    η[(ofAbelianVariety A).toOver] ≫ eqToHom (ofAbelianVariety_toOver A) = η[A.toOver] := by
  unfold ofAbelianVariety
  -- After `unfold ofAbelianVariety`, the `eqToHom` cast is between identical objects.
  change _ ≫ 𝟙 _ = _
  simp

lemma ofAbelianVariety_mul (A : AbelianVariety K) :
    μ[(ofAbelianVariety A).toOver] ≫ eqToHom (ofAbelianVariety_toOver A) =
      (eqToHom (ofAbelianVariety_toOver A) ⊗ₘ eqToHom (ofAbelianVariety_toOver A)) ≫
        μ[A.toOver] := by
  unfold ofAbelianVariety
  -- After `unfold ofAbelianVariety`, the `eqToHom` casts are between identical objects.
  change _ ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ _
  simp

lemma ofAbelianVariety_inv (A : AbelianVariety K) :
    ι[(ofAbelianVariety A).toOver] ≫ eqToHom (ofAbelianVariety_toOver A) =
      eqToHom (ofAbelianVariety_toOver A) ≫ ι[A.toOver] := by
  unfold ofAbelianVariety
  -- After `unfold ofAbelianVariety`, the `eqToHom` casts are between identical objects.
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
  simp

@[simp]
lemma ofAbelianVariety_zeroSection (A : AbelianVariety K) :
    (ofAbelianVariety A).zeroSection ≫ eqToHom (ofAbelianVariety_toScheme A) = A.zeroSection := by
  have h := congrArg Over.Hom.left (ofAbelianVariety_one A)
  rw [Over.comp_left, Over.eqToHom_left] at h
  exact h

instance isMonHom_eqToHom_ofAbelianVariety_toOver (A : AbelianVariety K) :
    IsMonHom (eqToHom (ofAbelianVariety_toOver A)) where
  one_hom := ofAbelianVariety_one A
  mul_hom := ofAbelianVariety_mul A

instance isMonHom_eqToHom_ofAbelianVariety_toOver_symm (A : AbelianVariety K) :
    IsMonHom (eqToHom (ofAbelianVariety_toOver A).symm) :=
  have : IsMonHom (eqToIso (ofAbelianVariety_toOver A)).hom :=
    isMonHom_eqToHom_ofAbelianVariety_toOver A
  inferInstanceAs (IsMonHom (eqToIso (ofAbelianVariety_toOver A)).inv)

/-! ### Functoriality and equivalence of categories -/

/-- Transport a homomorphism of abelian schemes over `Spec K` to a homomorphism of abelian
varieties over `K`. -/
def Hom.toAbelianVariety {A B : AbelianScheme (Spec (.of K))} (f : A ⟶ B) :
    A.toAbelianVariety ⟶ B.toAbelianVariety :=
  let h : A.toAbelianVariety.toOver ⟶ B.toAbelianVariety.toOver :=
    eqToHom (toAbelianVariety_toOver A) ≫ Hom.toOverHom f ≫
      eqToHom (toAbelianVariety_toOver B).symm
  have : IsMonHom h := by dsimp [h]; infer_instance
  AbelianVariety.Hom.mk' h (IsMonHom.one_hom h) (IsMonHom.mul_hom h)

@[simp]
lemma Hom.toOverHom_toAbelianVariety {A B : AbelianScheme (Spec (.of K))} (f : A ⟶ B) :
    AbelianVariety.Hom.toOverHom (Hom.toAbelianVariety f) =
      eqToHom (toAbelianVariety_toOver A) ≫ Hom.toOverHom f ≫
        eqToHom (toAbelianVariety_toOver B).symm := by
  unfold Hom.toAbelianVariety
  exact AbelianVariety.Hom.toOverHom_mk' _ _ _

@[simp]
lemma Hom.toAbelianVariety_id (A : AbelianScheme (Spec (.of K))) :
    Hom.toAbelianVariety (𝟙 A) = 𝟙 A.toAbelianVariety := by
  apply AbelianVariety.Hom.toOverHom_injective
  rw [Hom.toOverHom_toAbelianVariety, AbelianVariety.Hom.toOverHom_id]
  simp

@[simp, reassoc]
lemma Hom.toAbelianVariety_comp {A B C : AbelianScheme (Spec (.of K))} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.toAbelianVariety (f ≫ g) = Hom.toAbelianVariety f ≫ Hom.toAbelianVariety g := by
  apply AbelianVariety.Hom.toOverHom_injective
  rw [Hom.toOverHom_toAbelianVariety, AbelianVariety.Hom.toOverHom_comp,
    Hom.toOverHom_toAbelianVariety, Hom.toOverHom_toAbelianVariety]
  simp only [Hom.toOverHom_comp, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]

/-- Transport a homomorphism of abelian varieties over `K` to a homomorphism of abelian schemes
over `Spec K`. -/
def Hom.ofAbelianVariety {A B : AbelianVariety K} (f : A ⟶ B) :
    AbelianScheme.ofAbelianVariety A ⟶ AbelianScheme.ofAbelianVariety B :=
  let h : (AbelianScheme.ofAbelianVariety A).toOver ⟶ (AbelianScheme.ofAbelianVariety B).toOver :=
    eqToHom (ofAbelianVariety_toOver A) ≫ AbelianVariety.Hom.toOverHom f ≫
      eqToHom (ofAbelianVariety_toOver B).symm
  have : IsMonHom h := by dsimp [h]; infer_instance
  Hom.mk' h (IsMonHom.one_hom h) (IsMonHom.mul_hom h)

@[simp]
lemma Hom.toOverHom_ofAbelianVariety {A B : AbelianVariety K} (f : A ⟶ B) :
    Hom.toOverHom (Hom.ofAbelianVariety f) =
      eqToHom (ofAbelianVariety_toOver A) ≫ AbelianVariety.Hom.toOverHom f ≫
        eqToHom (ofAbelianVariety_toOver B).symm := by
  unfold Hom.ofAbelianVariety
  exact Hom.toOverHom_mk' _ _ _

@[simp]
lemma Hom.ofAbelianVariety_id (A : AbelianVariety K) :
    Hom.ofAbelianVariety (𝟙 A) = 𝟙 (AbelianScheme.ofAbelianVariety A) := by
  apply Hom.toOverHom_injective
  rw [Hom.toOverHom_ofAbelianVariety, AbelianVariety.Hom.toOverHom_id, Hom.toOverHom_id]
  simp

@[simp, reassoc]
lemma Hom.ofAbelianVariety_comp {A B C : AbelianVariety K} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.ofAbelianVariety (f ≫ g) = Hom.ofAbelianVariety f ≫ Hom.ofAbelianVariety g := by
  apply Hom.toOverHom_injective
  rw [Hom.toOverHom_ofAbelianVariety, Hom.toOverHom_comp, Hom.toOverHom_ofAbelianVariety,
    Hom.toOverHom_ofAbelianVariety, AbelianVariety.Hom.toOverHom_comp]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The functor sending abelian schemes over `Spec K` to abelian varieties over `K`. -/
def toAbelianVarietyFunctor : AbelianScheme (Spec (.of K)) ⥤ AbelianVariety K where
  obj := toAbelianVariety
  map f := Hom.toAbelianVariety f
  map_id := Hom.toAbelianVariety_id
  map_comp f g := Hom.toAbelianVariety_comp f g

@[simp]
lemma toAbelianVarietyFunctor_obj (A : AbelianScheme (Spec (.of K))) :
    (toAbelianVarietyFunctor (K := K)).obj A = A.toAbelianVariety :=
  (rfl)

@[simp]
lemma toAbelianVarietyFunctor_map {A B : AbelianScheme (Spec (.of K))} (f : A ⟶ B) :
    (toAbelianVarietyFunctor (K := K)).map f =
      eqToHom (toAbelianVarietyFunctor_obj A) ≫ Hom.toAbelianVariety f ≫
        eqToHom (toAbelianVarietyFunctor_obj B).symm := by
  unfold toAbelianVarietyFunctor
  exact (rfl)

/-- The functor sending abelian varieties over `K` to abelian schemes over `Spec K`. -/
def ofAbelianVarietyFunctor : AbelianVariety K ⥤ AbelianScheme (Spec (.of K)) where
  obj := ofAbelianVariety
  map f := Hom.ofAbelianVariety f
  map_id := Hom.ofAbelianVariety_id
  map_comp f g := Hom.ofAbelianVariety_comp f g

@[simp]
lemma ofAbelianVarietyFunctor_obj (A : AbelianVariety K) :
    (ofAbelianVarietyFunctor (K := K)).obj A = ofAbelianVariety A :=
  (rfl)

@[simp]
lemma ofAbelianVarietyFunctor_map {A B : AbelianVariety K} (f : A ⟶ B) :
    (ofAbelianVarietyFunctor (K := K)).map f =
      eqToHom (ofAbelianVarietyFunctor_obj A) ≫ Hom.ofAbelianVariety f ≫
        eqToHom (ofAbelianVarietyFunctor_obj B).symm := by
  unfold ofAbelianVarietyFunctor
  exact (rfl)

private lemma toOverHom_eqToHom {A B : AbelianScheme (Spec (.of K))} (h : A = B) :
    Hom.toOverHom (eqToHom h) = eqToHom (congrArg toOver h) := by
  subst h
  exact Hom.toOverHom_id A

private lemma av_toOverHom_eqToHom {A B : AbelianVariety K} (h : A = B) :
    AbelianVariety.Hom.toOverHom (eqToHom h) = eqToHom (congrArg AbelianVariety.toOver h) := by
  subst h
  exact AbelianVariety.Hom.toOverHom_id A

private lemma unit_obj_eq (A : AbelianScheme (Spec (.of K))) :
    (𝟭 _).obj A = (toAbelianVarietyFunctor ⋙ ofAbelianVarietyFunctor).obj A := by
  simp only [Functor.id_obj, Functor.comp_obj, toAbelianVarietyFunctor_obj,
    ofAbelianVarietyFunctor_obj]
  exact (ofAbelianVariety_toAbelianVariety A).symm

private lemma counit_obj_eq (A : AbelianVariety K) :
    (ofAbelianVarietyFunctor ⋙ toAbelianVarietyFunctor).obj A = (𝟭 _).obj A := by
  simp only [Functor.id_obj, Functor.comp_obj, toAbelianVarietyFunctor_obj,
    ofAbelianVarietyFunctor_obj]
  exact toAbelianVariety_ofAbelianVariety A

/-- The category of abelian schemes over `Spec K` is equivalent to `AbelianVariety K`. -/
def fieldEquivalence : AbelianScheme (Spec (.of K)) ≌ AbelianVariety K where
  functor := toAbelianVarietyFunctor
  inverse := ofAbelianVarietyFunctor
  unitIso := NatIso.ofComponents (fun A ↦ eqToIso (unit_obj_eq A)) fun {A B} f ↦ by
    apply Hom.toOverHom_injective
    dsimp only [Functor.id_map, Functor.comp_map, eqToIso.hom]
    rw [toAbelianVarietyFunctor_map, ofAbelianVarietyFunctor_map]
    simp only [Hom.toOverHom_comp, toOverHom_eqToHom, Hom.toOverHom_ofAbelianVariety,
      Hom.toOverHom_toAbelianVariety, AbelianVariety.Hom.toOverHom_comp, av_toOverHom_eqToHom,
      Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  counitIso := NatIso.ofComponents (fun A ↦ eqToIso (counit_obj_eq A)) fun {A B} f ↦ by
    apply AbelianVariety.Hom.toOverHom_injective
    dsimp only [Functor.id_map, Functor.comp_map, eqToIso.hom]
    rw [ofAbelianVarietyFunctor_map, toAbelianVarietyFunctor_map]
    simp only [AbelianVariety.Hom.toOverHom_comp, av_toOverHom_eqToHom,
      Hom.toOverHom_toAbelianVariety, Hom.toOverHom_comp, toOverHom_eqToHom,
      Hom.toOverHom_ofAbelianVariety, Category.assoc, eqToHom_trans, eqToHom_trans_assoc,
      eqToHom_refl, Category.comp_id]
  functor_unitIso_comp X := by
    apply AbelianVariety.Hom.toOverHom_injective
    rw [AbelianVariety.Hom.toOverHom_comp, AbelianVariety.Hom.toOverHom_id,
      toAbelianVarietyFunctor_map]
    simp only [NatIso.ofComponents_hom_app]
    dsimp only [eqToIso.hom]
    simp only [AbelianVariety.Hom.toOverHom_comp, Hom.toOverHom_toAbelianVariety,
      toOverHom_eqToHom, av_toOverHom_eqToHom, eqToHom_trans, eqToHom_refl]

/-! ### Rigidity over a field and compatibility with integer multiplication -/

/-- Over a field `K`, homomorphisms of abelian schemes are precisely the morphisms over `Spec K`
preserving the unit section. -/
def Hom.equivPointed (A B : AbelianScheme (Spec (.of K))) :
    (A ⟶ B) ≃ {f : A.toOver ⟶ B.toOver // η[A.toOver] ≫ f = η[B.toOver]} where
  toFun f := ⟨Hom.toOverHom f, Hom.one_hom f⟩
  invFun f := Hom.mk' f.1 f.2 (isMonHom_of_one_hom f.1 f.2).mul_hom
  left_inv _ := Hom.toOverHom_injective (Hom.toOverHom_mk' _ _ _)
  right_inv _ := Subtype.ext (Hom.toOverHom_mk' _ _ _)

@[simp]
lemma Hom.coe_equivPointed_apply {A B : AbelianScheme (Spec (.of K))} (f : A ⟶ B) :
    (Hom.equivPointed A B f : A.toOver ⟶ B.toOver) = Hom.toOverHom f := by
  unfold Hom.equivPointed
  rfl

@[simp]
lemma Hom.toOverHom_equivPointed_symm_apply {A B : AbelianScheme (Spec (.of K))}
    (f : {f : A.toOver ⟶ B.toOver // η[A.toOver] ≫ f = η[B.toOver]}) :
    Hom.toOverHom ((Hom.equivPointed A B).symm f) = f.1 :=
  Hom.toOverHom_mk' _ _ _

/-- Integer multiplication on `A.toAbelianVariety` agrees with `A.mulBy` on the underlying scheme
over `Spec K`. -/
lemma toAbelianVariety_mulBy (A : AbelianScheme (Spec (.of K))) (n : ℤ) :
    AbelianVariety.Hom.toOverHom (A.toAbelianVariety.mulBy n) =
      eqToHom (toAbelianVariety_toOver A) ≫ A.mulBy n ≫
        eqToHom (toAbelianVariety_toOver A).symm := by
  let φ : (A.toAbelianVariety ⟶ A.toAbelianVariety) →*
      (A.toAbelianVariety.toOver ⟶ A.toAbelianVariety.toOver) :=
    { toFun := AbelianVariety.Hom.toOverHom
      map_one' := AbelianVariety.Hom.toOverHom_one
      map_mul' := AbelianVariety.Hom.toOverHom_mul }
  have hz : AbelianVariety.Hom.toOverHom (A.toAbelianVariety.mulBy n) =
      (𝟙 A.toAbelianVariety.toOver) ^ n := by
    rw [AbelianVariety.mulBy_eq_zpow]
    simpa only [φ, MonoidHom.coe_mk, OneHom.coe_mk, AbelianVariety.Hom.toOverHom_id] using
      map_zpow φ (𝟙 A.toAbelianVariety) n
  rw [hz, mulBy_def]
  have he : ((𝟙 A.toAbelianVariety.toOver) ^ n) ≫ eqToHom (toAbelianVariety_toOver A) =
      eqToHom (toAbelianVariety_toOver A) ≫ ((𝟙 A.toOver) ^ n) := by
    rw [GrpObj.zpow_comp, Category.id_comp, GrpObj.comp_zpow, Category.comp_id]
  rw [← cancel_mono (eqToHom (toAbelianVariety_toOver A)), Category.assoc, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]
  exact he

/-- Integer multiplication on `ofAbelianVariety A` agrees with `A.mulBy` on the underlying scheme
over `Spec K`. -/
lemma ofAbelianVariety_mulBy (A : AbelianVariety K) (n : ℤ) :
    (ofAbelianVariety A).mulBy n =
      eqToHom (ofAbelianVariety_toOver A) ≫ AbelianVariety.Hom.toOverHom (A.mulBy n) ≫
        eqToHom (ofAbelianVariety_toOver A).symm := by
  let φ : (A ⟶ A) →* (A.toOver ⟶ A.toOver) :=
    { toFun := AbelianVariety.Hom.toOverHom
      map_one' := AbelianVariety.Hom.toOverHom_one
      map_mul' := AbelianVariety.Hom.toOverHom_mul }
  have hz : AbelianVariety.Hom.toOverHom (A.mulBy n) = (𝟙 A.toOver) ^ n := by
    rw [AbelianVariety.mulBy_eq_zpow]
    simpa only [φ, MonoidHom.coe_mk, OneHom.coe_mk, AbelianVariety.Hom.toOverHom_id] using
      map_zpow φ (𝟙 A) n
  rw [hz, mulBy_def]
  have he : ((𝟙 (ofAbelianVariety A).toOver) ^ n) ≫ eqToHom (ofAbelianVariety_toOver A) =
      eqToHom (ofAbelianVariety_toOver A) ≫ ((𝟙 A.toOver) ^ n) := by
    rw [GrpObj.zpow_comp, Category.id_comp, GrpObj.comp_zpow, Category.comp_id]
  rw [← cancel_mono (eqToHom (ofAbelianVariety_toOver A)), Category.assoc, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]
  exact he

/-! ### Preservation of identity, products, base change, and dimension -/

/-- `toAbelianVariety` sends the identity abelian scheme over `Spec K` to the trivial abelian
variety over `K`. -/
def toAbelianVarietyIdentityIso :
    (identity (Spec (.of K))).toAbelianVariety ≅ AbelianVariety.trivial K where
  hom := AbelianVariety.toTrivial _
  inv := AbelianVariety.fromTrivial _
  hom_inv_id := by
    apply AbelianVariety.Hom.toOverHom_injective
    have hterm : IsTerminal (identity (Spec (.of K))).toAbelianVariety.toOver :=
      IsTerminal.ofIso (isTerminalIdentityToOver (Spec (.of K)))
        (eqToIso (toAbelianVariety_toOver _).symm)
    exact hterm.hom_ext _ _
  inv_hom_id := Subsingleton.elim _ _

/-- `ofAbelianVariety` sends the trivial abelian variety over `K` to the identity abelian scheme
over `Spec K`. -/
def ofAbelianVarietyTrivialIso :
    ofAbelianVariety (AbelianVariety.trivial K) ≅ identity (Spec (.of K)) where
  hom := toIdentity _
  inv := fromIdentity _
  hom_inv_id := by
    apply Hom.toOverHom_injective
    have hterm : IsTerminal (ofAbelianVariety (AbelianVariety.trivial K)).toOver :=
      IsTerminal.ofIso isTerminalTensorUnit
        (eqToIso ((ofAbelianVariety_toOver _).trans (AbelianVariety.trivial_toOver K)).symm)
    exact hterm.hom_ext _ _
  inv_hom_id := Subsingleton.elim _ _

private def mkAbelianVarietyIso {A B : AbelianVariety K} (e : A.toOver ≅ B.toOver)
    [IsMonHom e.hom] : A ≅ B where
  hom := AbelianVariety.Hom.mk' e.hom (IsMonHom.one_hom e.hom) (IsMonHom.mul_hom e.hom)
  inv := AbelianVariety.Hom.mk' e.inv (IsMonHom.one_hom e.inv) (IsMonHom.mul_hom e.inv)
  hom_inv_id := AbelianVariety.Hom.toOverHom_injective <| by
    rw [AbelianVariety.Hom.toOverHom_comp, AbelianVariety.Hom.toOverHom_id,
      AbelianVariety.Hom.toOverHom_mk' _ _ _, AbelianVariety.Hom.toOverHom_mk' _ _ _, e.hom_inv_id]
  inv_hom_id := AbelianVariety.Hom.toOverHom_injective <| by
    rw [AbelianVariety.Hom.toOverHom_comp, AbelianVariety.Hom.toOverHom_id,
      AbelianVariety.Hom.toOverHom_mk' _ _ _, AbelianVariety.Hom.toOverHom_mk' _ _ _, e.inv_hom_id]

private lemma isMonHom_eqToHom_avProd (A B : AbelianVariety K) :
    IsMonHom (eqToHom (AbelianVariety.prod_toOver A B)) where
  one_hom := AbelianVariety.prod_one A B
  mul_hom := AbelianVariety.prod_mul A B

private lemma isMonHom_eqToHom_avProd_symm (A B : AbelianVariety K) :
    IsMonHom (eqToHom (AbelianVariety.prod_toOver A B).symm) :=
  have : IsMonHom (eqToIso (AbelianVariety.prod_toOver A B)).hom := isMonHom_eqToHom_avProd A B
  inferInstanceAs (IsMonHom (eqToIso (AbelianVariety.prod_toOver A B)).inv)

private def toAbelianVarietyProdOverIso (A B : AbelianScheme (Spec (.of K))) :
    (A.prod B).toAbelianVariety.toOver ≅ (A.toAbelianVariety.prod B.toAbelianVariety).toOver :=
  eqToIso (toAbelianVariety_toOver (A.prod B)) ≪≫
    eqToIso (prod_toOver A B) ≪≫
    ((eqToIso (toAbelianVariety_toOver A)).symm ⊗ᵢ
      (eqToIso (toAbelianVariety_toOver B)).symm) ≪≫
    (eqToIso (AbelianVariety.prod_toOver A.toAbelianVariety B.toAbelianVariety)).symm

/-- `toAbelianVariety` preserves binary products, canonically compatible with projections. -/
def toAbelianVarietyProdIso (A B : AbelianScheme (Spec (.of K))) :
    (A.prod B).toAbelianVariety ≅ A.toAbelianVariety.prod B.toAbelianVariety := by
  have : IsMonHom (eqToHom (AbelianVariety.prod_toOver A.toAbelianVariety
      B.toAbelianVariety).symm) :=
    isMonHom_eqToHom_avProd_symm A.toAbelianVariety B.toAbelianVariety
  have : IsMonHom (toAbelianVarietyProdOverIso A B).hom := by
    dsimp only [toAbelianVarietyProdOverIso, Iso.trans_hom, eqToIso.hom, eqToIso.inv,
      Iso.symm_hom, tensorIso_hom]
    infer_instance
  exact mkAbelianVarietyIso (toAbelianVarietyProdOverIso A B)

private lemma toOverHom_toAbelianVarietyProdIso_hom (A B : AbelianScheme (Spec (.of K))) :
    AbelianVariety.Hom.toOverHom (toAbelianVarietyProdIso A B).hom =
      (toAbelianVarietyProdOverIso A B).hom := by
  unfold toAbelianVarietyProdIso mkAbelianVarietyIso
  simp

@[simp, reassoc]
lemma toAbelianVarietyProdIso_hom_fst (A B : AbelianScheme (Spec (.of K))) :
    (toAbelianVarietyProdIso A B).hom ≫
        AbelianVariety.prod.fst A.toAbelianVariety B.toAbelianVariety =
      Hom.toAbelianVariety (prod.fst A B) := by
  apply AbelianVariety.Hom.toOverHom_injective
  rw [AbelianVariety.Hom.toOverHom_comp, toOverHom_toAbelianVarietyProdIso_hom,
    AbelianVariety.prod.toOverHom_fst, Hom.toOverHom_toAbelianVariety, prod.toOverHom_fst]
  dsimp only [toAbelianVarietyProdOverIso, Iso.trans_hom, eqToIso.hom, eqToIso.inv,
    Iso.symm_hom, tensorIso_hom]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    tensorHom_fst]

@[simp, reassoc]
lemma toAbelianVarietyProdIso_hom_snd (A B : AbelianScheme (Spec (.of K))) :
    (toAbelianVarietyProdIso A B).hom ≫
        AbelianVariety.prod.snd A.toAbelianVariety B.toAbelianVariety =
      Hom.toAbelianVariety (prod.snd A B) := by
  apply AbelianVariety.Hom.toOverHom_injective
  rw [AbelianVariety.Hom.toOverHom_comp, toOverHom_toAbelianVarietyProdIso_hom,
    AbelianVariety.prod.toOverHom_snd, Hom.toOverHom_toAbelianVariety, prod.toOverHom_snd]
  dsimp only [toAbelianVarietyProdOverIso, Iso.trans_hom, eqToIso.hom, eqToIso.inv,
    Iso.symm_hom, tensorIso_hom]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    tensorHom_snd]

private def ofAbelianVarietyProdOverIso (A B : AbelianVariety K) :
    (ofAbelianVariety (A.prod B)).toOver ≅
      ((ofAbelianVariety A).prod (ofAbelianVariety B)).toOver :=
  eqToIso (ofAbelianVariety_toOver (A.prod B)) ≪≫
    eqToIso (AbelianVariety.prod_toOver A B) ≪≫
    ((eqToIso (ofAbelianVariety_toOver A)).symm ⊗ᵢ
      (eqToIso (ofAbelianVariety_toOver B)).symm) ≪≫
    (eqToIso (prod_toOver (ofAbelianVariety A) (ofAbelianVariety B))).symm

/-- `ofAbelianVariety` preserves binary products, canonically compatible with projections. -/
def ofAbelianVarietyProdIso (A B : AbelianVariety K) :
    ofAbelianVariety (A.prod B) ≅ (ofAbelianVariety A).prod (ofAbelianVariety B) := by
  have : IsMonHom (eqToHom (AbelianVariety.prod_toOver A B)) := isMonHom_eqToHom_avProd A B
  have : IsMonHom (ofAbelianVarietyProdOverIso A B).hom := by
    dsimp only [ofAbelianVarietyProdOverIso, Iso.trans_hom, eqToIso.hom, eqToIso.inv,
      Iso.symm_hom, tensorIso_hom]
    infer_instance
  exact mkIso' (ofAbelianVarietyProdOverIso A B)

private lemma toOverHom_ofAbelianVarietyProdIso_hom (A B : AbelianVariety K) :
    Hom.toOverHom (ofAbelianVarietyProdIso A B).hom = (ofAbelianVarietyProdOverIso A B).hom := by
  unfold ofAbelianVarietyProdIso
  simp

@[simp, reassoc]
lemma ofAbelianVarietyProdIso_hom_fst (A B : AbelianVariety K) :
    (ofAbelianVarietyProdIso A B).hom ≫ prod.fst (ofAbelianVariety A) (ofAbelianVariety B) =
      Hom.ofAbelianVariety (AbelianVariety.prod.fst A B) := by
  apply Hom.toOverHom_injective
  rw [Hom.toOverHom_comp, toOverHom_ofAbelianVarietyProdIso_hom, prod.toOverHom_fst,
    Hom.toOverHom_ofAbelianVariety, AbelianVariety.prod.toOverHom_fst]
  dsimp only [ofAbelianVarietyProdOverIso, Iso.trans_hom, eqToIso.hom, eqToIso.inv,
    Iso.symm_hom, tensorIso_hom]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    tensorHom_fst]

@[simp, reassoc]
lemma ofAbelianVarietyProdIso_hom_snd (A B : AbelianVariety K) :
    (ofAbelianVarietyProdIso A B).hom ≫ prod.snd (ofAbelianVariety A) (ofAbelianVariety B) =
      Hom.ofAbelianVariety (AbelianVariety.prod.snd A B) := by
  apply Hom.toOverHom_injective
  rw [Hom.toOverHom_comp, toOverHom_ofAbelianVarietyProdIso_hom, prod.toOverHom_snd,
    Hom.toOverHom_ofAbelianVariety, AbelianVariety.prod.toOverHom_snd]
  dsimp only [ofAbelianVarietyProdOverIso, Iso.trans_hom, eqToIso.hom, eqToIso.inv,
    Iso.symm_hom, tensorIso_hom]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    tensorHom_snd]

private def toAbelianVarietyBaseChangeOverIso (A : AbelianScheme (Spec (.of K)))
    (L : Type u) [Field L] [Algebra K L] :
    (A.baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).toAbelianVariety.toOver ≅
      (A.toAbelianVariety.baseChange L).toOver :=
  eqToIso (toAbelianVariety_toOver _) ≪≫
    eqToIso (baseChange_toOver A (Spec.map (CommRingCat.ofHom (algebraMap K L)))) ≪≫
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapIso
      (eqToIso (toAbelianVariety_toOver A)).symm ≪≫
    (eqToIso (AbelianVariety.baseChange_toOver A.toAbelianVariety L)).symm

/-- `toAbelianVariety` commutes with base change along a field extension `K → L`. -/
def toAbelianVarietyBaseChangeIso (A : AbelianScheme (Spec (.of K)))
    (L : Type u) [Field L] [Algebra K L] :
    (A.baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).toAbelianVariety ≅
      A.toAbelianVariety.baseChange L := by
  have : IsMonHom (toAbelianVarietyBaseChangeOverIso A L).hom := by
    dsimp only [toAbelianVarietyBaseChangeOverIso, Iso.trans_hom, eqToIso.hom, eqToIso.inv,
      Iso.symm_hom, Functor.mapIso_hom]
    infer_instance
  exact mkAbelianVarietyIso (toAbelianVarietyBaseChangeOverIso A L)

private lemma toOverHom_toAbelianVarietyBaseChangeIso_hom (A : AbelianScheme (Spec (.of K)))
    (L : Type u) [Field L] [Algebra K L] :
    AbelianVariety.Hom.toOverHom (toAbelianVarietyBaseChangeIso A L).hom =
      (toAbelianVarietyBaseChangeOverIso A L).hom := by
  unfold toAbelianVarietyBaseChangeIso mkAbelianVarietyIso
  simp

/-- `toAbelianVarietyBaseChangeIso` is natural in homomorphisms of abelian schemes. -/
lemma toAbelianVarietyBaseChangeIso_hom_naturality {A B : AbelianScheme (Spec (.of K))}
    (g : A ⟶ B) (L : Type u) [Field L] [Algebra K L] :
    Hom.toAbelianVariety
        (Hom.baseChange g (Spec.map (CommRingCat.ofHom (algebraMap K L)))) ≫
        (toAbelianVarietyBaseChangeIso B L).hom =
      (toAbelianVarietyBaseChangeIso A L).hom ≫
        AbelianVariety.Hom.baseChange (Hom.toAbelianVariety g) L := by
  apply AbelianVariety.Hom.toOverHom_injective
  rw [AbelianVariety.Hom.toOverHom_comp, AbelianVariety.Hom.toOverHom_comp,
    Hom.toOverHom_toAbelianVariety, Hom.toOverHom_baseChange,
    toOverHom_toAbelianVarietyBaseChangeIso_hom, toOverHom_toAbelianVarietyBaseChangeIso_hom,
    AbelianVariety.Hom.toOverHom_baseChange, Hom.toOverHom_toAbelianVariety]
  dsimp only [toAbelianVarietyBaseChangeOverIso, Iso.trans_hom, eqToIso.hom, eqToIso.inv,
    Iso.symm_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc]

private def ofAbelianVarietyBaseChangeOverIso (A : AbelianVariety K)
    (L : Type u) [Field L] [Algebra K L] :
    (ofAbelianVariety (A.baseChange L)).toOver ≅
      ((ofAbelianVariety A).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))).toOver :=
  eqToIso (ofAbelianVariety_toOver _) ≪≫
    eqToIso (AbelianVariety.baseChange_toOver A L) ≪≫
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapIso
      (eqToIso (ofAbelianVariety_toOver A)).symm ≪≫
    (eqToIso (baseChange_toOver (ofAbelianVariety A)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))))).symm

/-- `ofAbelianVariety` commutes with base change along a field extension `K → L`. -/
def ofAbelianVarietyBaseChangeIso (A : AbelianVariety K)
    (L : Type u) [Field L] [Algebra K L] :
    ofAbelianVariety (A.baseChange L) ≅
      (ofAbelianVariety A).baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  have : IsMonHom (ofAbelianVarietyBaseChangeOverIso A L).hom := by
    dsimp only [ofAbelianVarietyBaseChangeOverIso, Iso.trans_hom, eqToIso.hom, eqToIso.inv,
      Iso.symm_hom, Functor.mapIso_hom]
    infer_instance
  exact mkIso' (ofAbelianVarietyBaseChangeOverIso A L)

private lemma toOverHom_ofAbelianVarietyBaseChangeIso_hom (A : AbelianVariety K)
    (L : Type u) [Field L] [Algebra K L] :
    Hom.toOverHom (ofAbelianVarietyBaseChangeIso A L).hom =
      (ofAbelianVarietyBaseChangeOverIso A L).hom := by
  unfold ofAbelianVarietyBaseChangeIso
  simp

/-- `ofAbelianVarietyBaseChangeIso` is natural in homomorphisms of abelian varieties. -/
lemma ofAbelianVarietyBaseChangeIso_hom_naturality {A B : AbelianVariety K}
    (g : A ⟶ B) (L : Type u) [Field L] [Algebra K L] :
    Hom.ofAbelianVariety (AbelianVariety.Hom.baseChange g L) ≫
        (ofAbelianVarietyBaseChangeIso B L).hom =
      (ofAbelianVarietyBaseChangeIso A L).hom ≫
        Hom.baseChange (Hom.ofAbelianVariety g)
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  apply Hom.toOverHom_injective
  rw [Hom.toOverHom_comp, Hom.toOverHom_comp, Hom.toOverHom_ofAbelianVariety,
    AbelianVariety.Hom.toOverHom_baseChange, toOverHom_ofAbelianVarietyBaseChangeIso_hom,
    toOverHom_ofAbelianVarietyBaseChangeIso_hom, Hom.toOverHom_baseChange,
    Hom.toOverHom_ofAbelianVariety]
  dsimp only [ofAbelianVarietyBaseChangeOverIso, Iso.trans_hom, eqToIso.hom, eqToIso.inv,
    Iso.symm_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc]

/-- The relative dimension of an abelian scheme over `Spec K` equals the dimension of the
corresponding `AbelianVariety K`. -/
lemma relativeDimension_eq_dim_toAbelianVariety (A : AbelianScheme (Spec (.of K)))
    (s : Spec (.of K)) :
    (A.relativeDimension s : WithBot ℕ∞) = A.toAbelianVariety.dim := by
  have hconst : ∀ s' : Spec (.of K), A.relativeDimension s' = A.relativeDimension s :=
    fun s' ↦ congrArg A.relativeDimension (Subsingleton.elim s' s)
  have hsm : SmoothOfRelativeDimension (A.relativeDimension s) A.toOver.hom :=
    (smoothOfRelativeDimension_iff_forall_relativeDimension_eq A _).mpr hconst
  have : Nonempty A.toScheme := ⟨A.zeroSection s⟩
  rw [AbelianVariety.dim_def, toAbelianVariety_toScheme]
  exact (topologicalKrullDim_eq_of_smoothOfRelativeDimension A.toOver.hom).symm

/-- The relative dimension of `ofAbelianVariety A` equals `A.dim`. -/
lemma relativeDimension_ofAbelianVariety (A : AbelianVariety K) (s : Spec (.of K)) :
    ((ofAbelianVariety A).relativeDimension s : WithBot ℕ∞) = A.dim := by
  simpa only [toAbelianVariety_ofAbelianVariety] using
    relativeDimension_eq_dim_toAbelianVariety (ofAbelianVariety A) s

end

end AbelianScheme

end AlgebraicGeometry

end TauCeti
