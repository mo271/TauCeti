/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.BaseChange

/-!
# Products of abelian schemes

This file constructs the binary product `A.prod B` of two abelian schemes over an arbitrary base
scheme `S`. Its underlying scheme is the fibre product over `S`, equipped with the componentwise
group law. Properness and smoothness pass to fibre products by stability under base change and
composition; geometric connectedness passes to fibre products via `GeometricallyConnected.comp`
since smooth morphisms are universally open.

The projections `prod.fst`, `prod.snd` and pairing `prod.lift` exhibit `A.prod B` as the
categorical binary product in `AbelianScheme S`, giving `HasBinaryProducts (AbelianScheme S)` and
`HasFiniteProducts (AbelianScheme S)`. We also supply the unital isomorphisms with `identity S`
(`prodIdentityRightIso`, `prodIdentityLeftIso`) and show that base change along any `f : T ⟶ S`
preserves binary products (`baseChangeProdIso`), with `@[simp]` projection compatibilities.

## Main declarations

* `TauCeti.AlgebraicGeometry.AbelianScheme.prod`: the fibre-product abelian scheme `A ×_S B`.
* `TauCeti.AlgebraicGeometry.AbelianScheme.prod.fst`, `prod.snd`, `prod.lift`: projections and
  universal pairing for binary products of abelian schemes.
* `TauCeti.AlgebraicGeometry.AbelianScheme.hasBinaryProducts`, `hasFiniteProducts`: categorical
  product instances on `AbelianScheme S`.
* `TauCeti.AlgebraicGeometry.AbelianScheme.prodIdentityRightIso`, `prodIdentityLeftIso`: unital
  isomorphisms `A.prod (identity S) ≅ A` and `(identity S).prod A ≅ A`.
* `TauCeti.AlgebraicGeometry.AbelianScheme.baseChangeProdIso`: canonical isomorphism
  `(A.prod B).baseChange f ≅ (A.baseChange f).prod (B.baseChange f)` compatible with projections.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianScheme

variable {S T : Scheme.{u}}

noncomputable section

private lemma isProper_tensor (A B : AbelianScheme S) :
    IsProper (A.toOver ⊗ B.toOver).hom := by
  rw [Over.tensorObj_hom]
  exact MorphismProperty.comp_mem @IsProper _ _
    (inferInstanceAs (IsProper (pullback.fst A.toOver.hom B.toOver.hom)))
    (inferInstanceAs (IsProper A.toOver.hom))

private lemma smooth_tensor (A B : AbelianScheme S) :
    Smooth (A.toOver ⊗ B.toOver).hom := by
  rw [Over.tensorObj_hom]
  exact MorphismProperty.comp_mem @Smooth _ _
    (inferInstanceAs (Smooth (pullback.fst A.toOver.hom B.toOver.hom)))
    (inferInstanceAs (Smooth A.toOver.hom))

private lemma geometricallyConnected_tensor (A B : AbelianScheme S) :
    GeometricallyConnected (A.toOver ⊗ B.toOver).hom := by
  rw [Over.tensorObj_hom]
  exact GeometricallyConnected.comp (pullback.fst A.toOver.hom B.toOver.hom) A.toOver.hom

/-- The product of two abelian schemes over `S`. Its underlying scheme is their fibre product over
`S`, equipped with the componentwise group law. -/
def prod (A B : AbelianScheme S) : AbelianScheme S where
  toOver := A.toOver ⊗ B.toOver
  grpObj := inferInstance
  isProper := isProper_tensor A B
  smooth := smooth_tensor A B
  geometricallyConnected := geometricallyConnected_tensor A B

/-- The `Over S` object underlying a product is the tensor product (fibre product over `S`). -/
@[simp]
lemma prod_toOver (A B : AbelianScheme S) : (prod A B).toOver = A.toOver ⊗ B.toOver :=
  (rfl)

/-- The scheme underlying a product is the fibre product over `S`. -/
@[simp]
lemma prod_toScheme (A B : AbelianScheme S) :
    (prod A B).toScheme = pullback A.toOver.hom B.toOver.hom := by
  rw [toScheme, prod_toOver, Over.tensorObj_left]

/-- The unit section of a product is the componentwise unit section. -/
lemma prod_one (A B : AbelianScheme S) :
    η[(prod A B).toOver] ≫ eqToHom (prod_toOver A B) = η[A.toOver ⊗ B.toOver] := by
  unfold prod
  -- After `unfold prod`, the `eqToHom` cast is between identical objects.
  change _ ≫ 𝟙 _ = _
  simp

/-- The multiplication on a product is componentwise multiplication. -/
lemma prod_mul (A B : AbelianScheme S) :
    μ[(prod A B).toOver] ≫ eqToHom (prod_toOver A B) =
      (eqToHom (prod_toOver A B) ⊗ₘ eqToHom (prod_toOver A B)) ≫
        μ[A.toOver ⊗ B.toOver] := by
  unfold prod
  -- After `unfold prod`, the `eqToHom` casts are between syntactically equal objects.
  change _ ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ _
  simp

/-- Inversion on a product is componentwise inversion. -/
lemma prod_inv (A B : AbelianScheme S) :
    ι[(prod A B).toOver] ≫ eqToHom (prod_toOver A B) =
      eqToHom (prod_toOver A B) ≫ ι[A.toOver ⊗ B.toOver] := by
  unfold prod
  -- After `unfold prod`, the `eqToHom` cast on the right is between identical objects.
  change _ = 𝟙 _ ≫ _
  simp

/-- The transport isomorphism along `prod_toOver` is a group-object homomorphism. -/
instance isMonHom_eqToHom_prod_toOver (A B : AbelianScheme S) :
    IsMonHom (eqToHom (prod_toOver A B)) where
  one_hom := prod_one A B
  mul_hom := prod_mul A B

/-- The inverse transport isomorphism along `prod_toOver` is a group-object homomorphism. -/
instance isMonHom_eqToHom_prod_toOver_symm (A B : AbelianScheme S) :
    IsMonHom (eqToHom (prod_toOver A B).symm) :=
  have : IsMonHom (eqToIso (prod_toOver A B)).hom := isMonHom_eqToHom_prod_toOver A B
  inferInstanceAs (IsMonHom (eqToIso (prod_toOver A B)).inv)

namespace prod

/-- The first projection from a product of abelian schemes. -/
def fst (A B : AbelianScheme S) : prod A B ⟶ A := by
  refine Hom.mk'
    (eqToHom (prod_toOver A B) ≫ CartesianMonoidalCategory.fst A.toOver B.toOver) ?_ ?_
  · rw [← Category.assoc, prod_one]
    simp only [IsMonHom.one_hom]
  · rw [← Category.assoc, prod_mul]
    simp only [Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc]

/-- The second projection from a product of abelian schemes. -/
def snd (A B : AbelianScheme S) : prod A B ⟶ B := by
  refine Hom.mk'
    (eqToHom (prod_toOver A B) ≫ CartesianMonoidalCategory.snd A.toOver B.toOver) ?_ ?_
  · rw [← Category.assoc, prod_one]
    simp only [IsMonHom.one_hom]
  · rw [← Category.assoc, prod_mul]
    simp only [Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc]

/-- Pair two homomorphisms with a common source to obtain a homomorphism into a product. -/
def lift {A B C : AbelianScheme S} (f : C ⟶ A) (g : C ⟶ B) : C ⟶ prod A B := by
  refine Hom.mk'
    (CartesianMonoidalCategory.lift (Hom.toOverHom f) (Hom.toOverHom g) ≫
      eqToHom (prod_toOver A B).symm) ?_ ?_
  · simp only [IsMonHom.one_hom_assoc, ← cancel_mono (eqToHom (prod_toOver A B)),
      Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, prod_one]
  · simp only [IsMonHom.mul_hom_assoc, ← cancel_mono (eqToHom (prod_toOver A B)),
      Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, prod_mul,
      tensorHom_comp_tensorHom_assoc]

@[simp]
lemma toOverHom_fst (A B : AbelianScheme S) :
    Hom.toOverHom (fst A B) =
      eqToHom (prod_toOver A B) ≫ CartesianMonoidalCategory.fst A.toOver B.toOver := by
  unfold fst
  exact Hom.toOverHom_mk' _ _ _

@[simp]
lemma toOverHom_snd (A B : AbelianScheme S) :
    Hom.toOverHom (snd A B) =
      eqToHom (prod_toOver A B) ≫ CartesianMonoidalCategory.snd A.toOver B.toOver := by
  unfold snd
  exact Hom.toOverHom_mk' _ _ _

@[simp]
lemma toOverHom_lift {A B C : AbelianScheme S} (f : C ⟶ A) (g : C ⟶ B) :
    Hom.toOverHom (lift f g) =
      CartesianMonoidalCategory.lift (Hom.toOverHom f) (Hom.toOverHom g) ≫
        eqToHom (prod_toOver A B).symm := by
  unfold lift
  exact Hom.toOverHom_mk' _ _ _

/-- The first projection of a pairing is its first component. -/
@[simp, reassoc]
lemma lift_fst {A B C : AbelianScheme S} (f : C ⟶ A) (g : C ⟶ B) :
    lift f g ≫ fst A B = f := by
  apply Hom.toOverHom_injective
  rw [Hom.toOverHom_comp, toOverHom_lift, toOverHom_fst]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simp

/-- The second projection of a pairing is its second component. -/
@[simp, reassoc]
lemma lift_snd {A B C : AbelianScheme S} (f : C ⟶ A) (g : C ⟶ B) :
    lift f g ≫ snd A B = g := by
  apply Hom.toOverHom_injective
  rw [Hom.toOverHom_comp, toOverHom_lift, toOverHom_snd]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simp

/-- Homomorphisms into a product are determined by their two projections. -/
@[ext]
lemma hom_ext {A B C : AbelianScheme S} {f g : C ⟶ prod A B}
    (hfst : f ≫ fst A B = g ≫ fst A B) (hsnd : f ≫ snd A B = g ≫ snd A B) : f = g := by
  apply Hom.toOverHom_injective
  rw [← cancel_mono (eqToHom (prod_toOver A B))]
  apply CartesianMonoidalCategory.hom_ext
  · have h := congrArg Hom.toOverHom hfst
    simpa only [Hom.toOverHom_comp, toOverHom_fst, ← Category.assoc] using h
  · have h := congrArg Hom.toOverHom hsnd
    simpa only [Hom.toOverHom_comp, toOverHom_snd, ← Category.assoc] using h

/-- Precomposing a pairing composes each of its components. -/
@[reassoc, simp]
lemma comp_lift {A B C D : AbelianScheme S} (h : D ⟶ C) (f : C ⟶ A) (g : C ⟶ B) :
    h ≫ lift f g = lift (h ≫ f) (h ≫ g) := by
  apply hom_ext <;> simp

/-- Pairing the two projections of a homomorphism into a product recovers that homomorphism. -/
@[simp]
lemma lift_comp_fst_snd {A B C : AbelianScheme S} (f : C ⟶ prod A B) :
    lift (f ≫ fst A B) (f ≫ snd A B) = f := by
  apply hom_ext <;> simp

private def binaryFan (A B : AbelianScheme S) : BinaryFan A B :=
  BinaryFan.mk (fst A B) (snd A B)

private def binaryFanIsLimit (A B : AbelianScheme S) : IsLimit (binaryFan A B) :=
  BinaryFan.IsLimit.mk _
    (fun f g ↦ lift f g)
    (fun f g ↦ lift_fst f g)
    (fun f g ↦ lift_snd f g)
    (fun f g _ hfst hsnd ↦
      hom_ext
        (hfst.trans (lift_fst f g).symm)
        (hsnd.trans (lift_snd f g).symm))

end prod

/-! ### Categorical product instances -/

/-- `AbelianScheme S` has a terminal object, namely `identity S`. -/
instance hasTerminal : HasTerminal (AbelianScheme S) :=
  hasTerminal_of_unique (identity S)

/-- The concrete product supplies the categorical binary product of abelian schemes. -/
instance hasBinaryProduct (A B : AbelianScheme S) : HasBinaryProduct A B :=
  HasLimit.mk ⟨prod.binaryFan A B, prod.binaryFanIsLimit A B⟩

/-- Abelian schemes over an arbitrary base have categorical binary products. -/
instance hasBinaryProducts : HasBinaryProducts (AbelianScheme S) :=
  hasBinaryProducts_of_hasLimit_pair (AbelianScheme S)

/-- Abelian schemes over an arbitrary base have all finite products. -/
instance hasFiniteProducts : HasFiniteProducts (AbelianScheme S) :=
  CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal

/-! ### Unital isomorphisms with the identity abelian scheme -/

/-- The product of `A` with the identity abelian scheme on the right is isomorphic to `A`. -/
def prodIdentityRightIso (A : AbelianScheme S) : A.prod (identity S) ≅ A where
  hom := prod.fst A (identity S)
  inv := prod.lift (𝟙 A) (toIdentity A)
  hom_inv_id := by
    apply prod.hom_ext
    · simp
    · exact Subsingleton.elim _ _
  inv_hom_id := by simp

@[simp]
lemma prodIdentityRightIso_hom (A : AbelianScheme S) :
    (prodIdentityRightIso A).hom = prod.fst A (identity S) :=
  (rfl)

@[simp]
lemma prodIdentityRightIso_inv (A : AbelianScheme S) :
    (prodIdentityRightIso A).inv = prod.lift (𝟙 A) (toIdentity A) :=
  (rfl)

/-- The product of `A` with the identity abelian scheme on the left is isomorphic to `A`. -/
def prodIdentityLeftIso (A : AbelianScheme S) : (identity S).prod A ≅ A where
  hom := prod.snd (identity S) A
  inv := prod.lift (toIdentity A) (𝟙 A)
  hom_inv_id := by
    apply prod.hom_ext
    · exact Subsingleton.elim _ _
    · simp
  inv_hom_id := by simp

@[simp]
lemma prodIdentityLeftIso_hom (A : AbelianScheme S) :
    (prodIdentityLeftIso A).hom = prod.snd (identity S) A :=
  (rfl)

@[simp]
lemma prodIdentityLeftIso_inv (A : AbelianScheme S) :
    (prodIdentityLeftIso A).inv = prod.lift (toIdentity A) (𝟙 A) :=
  (rfl)

/-! ### Compatibility of products with base change -/

private def prodBaseChangeOverIso (A B : AbelianScheme S) (f : T ⟶ S) :
    ((A.baseChange f).prod (B.baseChange f)).toOver ≅ ((A.prod B).baseChange f).toOver :=
  eqToIso (prod_toOver (A.baseChange f) (B.baseChange f)) ≪≫
    (eqToIso (baseChange_toOver A f) ⊗ᵢ eqToIso (baseChange_toOver B f)) ≪≫
    Functor.Monoidal.μIso (Over.pullback f) A.toOver B.toOver ≪≫
    (Over.pullback f).mapIso (eqToIso (prod_toOver A B)).symm ≪≫
    (eqToIso (baseChange_toOver (A.prod B) f)).symm

private lemma isMonHom_prodBaseChangeOverIso_hom (A B : AbelianScheme S) (f : T ⟶ S) :
    IsMonHom (prodBaseChangeOverIso A B f).hom := by
  dsimp only [prodBaseChangeOverIso, Iso.trans_hom, eqToIso.hom, eqToIso.inv, Iso.symm_hom,
    tensorIso_hom, Functor.mapIso_hom, Functor.Monoidal.μIso_hom]
  infer_instance

/-- Base change preserves binary products of abelian schemes: `(A ×_S B)_T ≅ A_T ×_T B_T`. -/
def baseChangeProdIso (A B : AbelianScheme S) (f : T ⟶ S) :
    (A.prod B).baseChange f ≅ (A.baseChange f).prod (B.baseChange f) := by
  have : IsMonHom (prodBaseChangeOverIso A B f).hom := isMonHom_prodBaseChangeOverIso_hom A B f
  exact (mkIso' (prodBaseChangeOverIso A B f)).symm

/-- The first projection of `baseChangeProdIso` is the base change of `prod.fst`. -/
@[simp, reassoc]
lemma baseChangeProdIso_hom_fst (A B : AbelianScheme S) (f : T ⟶ S) :
    (baseChangeProdIso A B f).hom ≫ prod.fst (A.baseChange f) (B.baseChange f) =
      Hom.baseChange (prod.fst A B) f := by
  rw [← cancel_epi (baseChangeProdIso A B f).inv, Iso.inv_hom_id_assoc]
  apply Hom.toOverHom_injective
  have hinv : Hom.toOverHom (baseChangeProdIso A B f).inv =
      (prodBaseChangeOverIso A B f).hom := by
    unfold baseChangeProdIso
    simp
  rw [Hom.toOverHom_comp, hinv, prod.toOverHom_fst, Hom.toOverHom_baseChange, prod.toOverHom_fst]
  dsimp only [prodBaseChangeOverIso, Iso.trans_hom, eqToIso.hom, eqToIso.inv, Iso.symm_hom,
    tensorIso_hom, Functor.mapIso_hom, Functor.Monoidal.μIso_hom]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  have hμ : Functor.LaxMonoidal.μ (Over.pullback f) A.toOver B.toOver ≫
        (Over.pullback f).map (CartesianMonoidalCategory.fst A.toOver B.toOver) =
      CartesianMonoidalCategory.fst ((Over.pullback f).obj A.toOver)
        ((Over.pullback f).obj B.toOver) := by
    rw [← Functor.OplaxMonoidal.δ_fst (Over.pullback f) A.toOver B.toOver]
    simp
  rw [← Category.assoc (Functor.LaxMonoidal.μ (Over.pullback f) A.toOver B.toOver), hμ]
  simp only [tensorHom_fst_assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The second projection of `baseChangeProdIso` is the base change of `prod.snd`. -/
@[simp, reassoc]
lemma baseChangeProdIso_hom_snd (A B : AbelianScheme S) (f : T ⟶ S) :
    (baseChangeProdIso A B f).hom ≫ prod.snd (A.baseChange f) (B.baseChange f) =
      Hom.baseChange (prod.snd A B) f := by
  rw [← cancel_epi (baseChangeProdIso A B f).inv, Iso.inv_hom_id_assoc]
  apply Hom.toOverHom_injective
  have hinv : Hom.toOverHom (baseChangeProdIso A B f).inv =
      (prodBaseChangeOverIso A B f).hom := by
    unfold baseChangeProdIso
    simp
  rw [Hom.toOverHom_comp, hinv, prod.toOverHom_snd, Hom.toOverHom_baseChange, prod.toOverHom_snd]
  dsimp only [prodBaseChangeOverIso, Iso.trans_hom, eqToIso.hom, eqToIso.inv, Iso.symm_hom,
    tensorIso_hom, Functor.mapIso_hom, Functor.Monoidal.μIso_hom]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  have hμ : Functor.LaxMonoidal.μ (Over.pullback f) A.toOver B.toOver ≫
        (Over.pullback f).map (CartesianMonoidalCategory.snd A.toOver B.toOver) =
      CartesianMonoidalCategory.snd ((Over.pullback f).obj A.toOver)
        ((Over.pullback f).obj B.toOver) := by
    rw [← Functor.OplaxMonoidal.δ_snd (Over.pullback f) A.toOver B.toOver]
    simp
  rw [← Category.assoc (Functor.LaxMonoidal.μ (Over.pullback f) A.toOver B.toOver), hμ]
  simp only [tensorHom_snd_assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The forward map of `baseChangeProdIso` is the pairing of the base-changed projections. -/
lemma baseChangeProdIso_hom (A B : AbelianScheme S) (f : T ⟶ S) :
    (baseChangeProdIso A B f).hom =
      prod.lift (Hom.baseChange (prod.fst A B) f) (Hom.baseChange (prod.snd A B) f) := by
  apply prod.hom_ext <;> simp

end

end AbelianScheme

end AlgebraicGeometry

end TauCeti
