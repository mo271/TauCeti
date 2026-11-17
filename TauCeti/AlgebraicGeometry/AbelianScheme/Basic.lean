/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import TauCeti.AlgebraicGeometry.Geometrically.Integral
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral
public import TauCeti.CategoryTheory.Monoidal.Cartesian.Mon

/-!
# Abelian schemes

This file defines an **abelian scheme** over an arbitrary base scheme `S`: a group object
`toOver : Over S` whose structure morphism `toOver.hom : toOver.left ⟶ S` is proper and smooth
with geometrically connected fibres. No commutativity axiom, dimension hypothesis, or choice of
ample line bundle is part of the data.

Because `toOver.hom` is smooth with geometrically connected fibres, it is automatically
geometrically integral (`TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`). The category
`AbelianScheme S` has group-scheme homomorphisms (morphisms in `Over S` satisfying `IsMonHom`) as
its morphisms, induced from Mathlib's `Grp (Over S)`.

For an abelian scheme `A`, the integer multiplication morphism `A.mulBy n : A.toOver ⟶ A.toOver`
is `(𝟙 A.toOver) ^ n` in Mathlib's group structure on morphisms into a group object
(`CategoryTheory.Hom.group`). Naturality with respect to homomorphisms and the composition law
`A.mulBy m ≫ A.mulBy n = A.mulBy (m * n)` hold for arbitrary group objects, without assuming
commutativity.

Finally, `AbelianScheme.identity S` constructs the identity group scheme `S ⟶ S` as the zero
object of `AbelianScheme S`, with `mulBy (identity S) n = 𝟙 _` (hence an isomorphism for every
integer `n`, including `n = 0` and multiples of any prime `p`).

## Main declarations

* `TauCeti.AlgebraicGeometry.AbelianScheme`: an abelian scheme over `S : Scheme`.
* `TauCeti.AlgebraicGeometry.AbelianScheme.toScheme`, `zeroSection`, `mulBy`: the underlying
  scheme, zero section, and integer multiplication morphism.
* `TauCeti.AlgebraicGeometry.AbelianScheme.Hom`: constructors (`mk'`, `mkOfPoints`), forgetful
  functors (`toOverFunctor`, `toSchemeFunctor`), underlying maps (`toOverHom`, `toSchemeHom`),
  preservation laws (`one_hom`, `mul_hom`, `inv_hom`), and isomorphism wrappers (`isoToOver`,
  `isoToScheme`).
* `TauCeti.AlgebraicGeometry.AbelianScheme.identity`: the identity abelian scheme `S ⟶ S`, shown
  to be terminal, initial, and a zero object of `AbelianScheme S`.

## References

* G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties*, Chapter I, §§1.1–1.2.
* J. S. Milne, *Abelian Varieties* (2022 revision), §20.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
open scoped CategoryTheory.MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- An **abelian scheme** over a scheme `S`: a group object in `Over S` whose structure morphism
is proper and smooth with geometrically connected fibres. No commutativity, dimension, or ample
line bundle is part of the data. -/
structure AbelianScheme (S : Scheme.{u}) where
  /-- The underlying group scheme over `S`. -/
  toOver : Over S
  /-- The group-object structure on `toOver`. -/
  grpObj : GrpObj toOver
  /-- The structure morphism to `S` is proper. -/
  isProper : IsProper toOver.hom
  /-- The structure morphism to `S` is smooth. -/
  smooth : Smooth toOver.hom
  /-- The structure morphism to `S` has geometrically connected fibres. -/
  geometricallyConnected : GeometricallyConnected toOver.hom

namespace AbelianScheme

attribute [instance] AbelianScheme.grpObj AbelianScheme.isProper AbelianScheme.smooth
  AbelianScheme.geometricallyConnected

variable {S : Scheme.{u}}

/-- An abelian scheme is geometrically integral over its base, since its structure morphism is
smooth with geometrically connected fibres. -/
instance geometricallyIntegral (A : AbelianScheme S) : GeometricallyIntegral A.toOver.hom :=
  Smooth.geometricallyIntegral A.toOver.hom

/-- The underlying scheme of an abelian scheme. -/
noncomputable abbrev toScheme (A : AbelianScheme S) : Scheme.{u} :=
  A.toOver.left

/-- The zero section `S ⟶ A` of an abelian scheme, that is, the unit of its group law. -/
noncomputable abbrev zeroSection (A : AbelianScheme S) : S ⟶ A.toScheme :=
  η[A.toOver].left

/-- The zero section is a section of the structure morphism of `A`. -/
@[reassoc]
lemma zeroSection_comp_toOver_hom (A : AbelianScheme S) :
    A.zeroSection ≫ A.toOver.hom = 𝟙 S := by
  simpa only [Over.tensorUnit_hom] using η[A.toOver].w

/-! ### Integer multiplication -/

/-- Multiplication by `n : ℤ` on an abelian scheme, defined as `(𝟙 A.toOver) ^ n` in the group
`A.toOver ⟶ A.toOver`. -/
noncomputable def mulBy (A : AbelianScheme S) (n : ℤ) : A.toOver ⟶ A.toOver :=
  (𝟙 A.toOver) ^ n

lemma mulBy_def (A : AbelianScheme S) (n : ℤ) : A.mulBy n = (𝟙 A.toOver) ^ n :=
  (rfl)

@[simp]
lemma mulBy_zero (A : AbelianScheme S) : A.mulBy 0 = 1 :=
  zpow_zero (𝟙 A.toOver)

@[simp]
lemma mulBy_one (A : AbelianScheme S) : A.mulBy 1 = 𝟙 A.toOver :=
  zpow_one (𝟙 A.toOver)

@[simp]
lemma mulBy_neg_one (A : AbelianScheme S) : A.mulBy (-1) = ι[A.toOver] := by
  rw [mulBy, zpow_neg_one, ← GrpObj.inv_eq_inv]

lemma mulBy_neg (A : AbelianScheme S) (n : ℤ) : A.mulBy (-n) = (A.mulBy n)⁻¹ :=
  zpow_neg (𝟙 A.toOver) n

lemma mulBy_add (A : AbelianScheme S) (m n : ℤ) : A.mulBy (m + n) = A.mulBy m * A.mulBy n :=
  zpow_add (𝟙 A.toOver) m n

@[reassoc]
lemma mulBy_comp_mulBy (A : AbelianScheme S) (m n : ℤ) :
    A.mulBy m ≫ A.mulBy n = A.mulBy (m * n) := by
  simp only [mulBy]
  rw [GrpObj.comp_zpow, Category.comp_id, ← zpow_mul]

/-! ### Category of abelian schemes -/

noncomputable section

/-- Abelian schemes over a fixed base `S` form a category whose morphisms are group-scheme
homomorphisms over `S`. -/
instance : Category (AbelianScheme S) :=
  inferInstanceAs (Category (InducedCategory _ (fun A : AbelianScheme S ↦ Grp.mk A.toOver)))

/-- Homomorphisms of abelian schemes over `S`, i.e., morphisms `A ⟶ B` in `AbelianScheme S`. -/
abbrev Hom (A B : AbelianScheme S) : Type u := A ⟶ B

/-- Construct a homomorphism of abelian schemes from a morphism over `S` and proofs that it
preserves the unit and multiplication. -/
def Hom.mk' {A B : AbelianScheme S} (f : A.toOver ⟶ B.toOver)
    (one_f : η[A.toOver] ≫ f = η[B.toOver] := by cat_disch)
    (mul_f : μ[A.toOver] ≫ f = (f ⊗ₘ f) ≫ μ[B.toOver] := by cat_disch) : A ⟶ B :=
  InducedCategory.homMk (Grp.homMk'' f one_f mul_f)

/-- Construct a homomorphism of abelian schemes from a morphism over `S` that preserves the unit
and multiplication on `T`-points for every `T : Over S`. -/
def Hom.mkOfPoints {A B : AbelianScheme S} (f : A.toOver ⟶ B.toOver)
    (hone : ∀ T : Over S, (1 : T ⟶ A.toOver) ≫ f = 1)
    (hmul : ∀ (T : Over S) (x y : T ⟶ A.toOver), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) :
    A ⟶ B :=
  have : IsMonHom f := (TauCeti.CategoryTheory.isMonHom_iff_forall_comp f).mpr ⟨hone, hmul⟩
  Hom.mk' f (IsMonHom.one_hom f) (IsMonHom.mul_hom f)

/-- The underlying morphism in `Over S` of a homomorphism of abelian schemes. -/
def Hom.toOverHom {A B : AbelianScheme S} (f : A ⟶ B) : A.toOver ⟶ B.toOver :=
  (InducedCategory.homEquiv (C := AbelianScheme S) f).hom.hom

/-- The underlying `Over S` morphism of `InducedCategory.homMk f` is the underlying morphism of
`f : Grp.mk A.toOver ⟶ Grp.mk B.toOver`. -/
@[simp]
lemma Hom.toOverHom_homMk {A B : AbelianScheme S}
    (f : Grp.mk A.toOver ⟶ Grp.mk B.toOver) :
    Hom.toOverHom (InducedCategory.homMk (C := AbelianScheme S) f) = f.hom.hom := by
  unfold Hom.toOverHom
  rfl

/-- `Hom.toOverHom` preserves identities. -/
@[simp]
lemma Hom.toOverHom_id (A : AbelianScheme S) : Hom.toOverHom (𝟙 A) = 𝟙 A.toOver := by
  unfold Hom.toOverHom
  rfl

/-- `Hom.toOverHom` preserves composition. -/
@[simp, reassoc]
lemma Hom.toOverHom_comp {A B C : AbelianScheme S} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.toOverHom (f ≫ g) = Hom.toOverHom f ≫ Hom.toOverHom g := by
  unfold Hom.toOverHom
  rfl

/-- The underlying morphism of an abelian-scheme homomorphism preserves the group-object
structure. -/
instance {A B : AbelianScheme S} (f : A ⟶ B) : IsMonHom (Hom.toOverHom f) := by
  unfold Hom.toOverHom
  infer_instance

/-- The underlying morphism over `S` of a homomorphism built by `Hom.mk'` is the supplied
morphism. -/
@[simp]
lemma Hom.toOverHom_mk' {A B : AbelianScheme S} (f : A.toOver ⟶ B.toOver)
    (one_f : η[A.toOver] ≫ f = η[B.toOver] := by cat_disch)
    (mul_f : μ[A.toOver] ≫ f = (f ⊗ₘ f) ≫ μ[B.toOver] := by cat_disch) :
    Hom.toOverHom (Hom.mk' f one_f mul_f) = f :=
  Grp.homMk''_hom_hom (A := Grp.mk A.toOver) (B := Grp.mk B.toOver) f one_f mul_f

/-- The underlying morphism over `S` of a homomorphism built by `Hom.mkOfPoints` is the supplied
morphism. -/
@[simp]
lemma Hom.toOverHom_mkOfPoints {A B : AbelianScheme S} (f : A.toOver ⟶ B.toOver)
    (hone : ∀ T : Over S, (1 : T ⟶ A.toOver) ≫ f = 1)
    (hmul : ∀ (T : Over S) (x y : T ⟶ A.toOver), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) :
    Hom.toOverHom (Hom.mkOfPoints f hone hmul) = f :=
  Hom.toOverHom_mk' f _ _

/-- A homomorphism of abelian schemes preserves the unit section. -/
@[reassoc]
lemma Hom.one_hom {A B : AbelianScheme S} (f : A ⟶ B) :
    η[A.toOver] ≫ Hom.toOverHom f = η[B.toOver] :=
  IsMonHom.one_hom (Hom.toOverHom f)

/-- A homomorphism of abelian schemes preserves multiplication. -/
@[reassoc]
lemma Hom.mul_hom {A B : AbelianScheme S} (f : A ⟶ B) :
    μ[A.toOver] ≫ Hom.toOverHom f =
      (Hom.toOverHom f ⊗ₘ Hom.toOverHom f) ≫ μ[B.toOver] :=
  IsMonHom.mul_hom (Hom.toOverHom f)

/-- A homomorphism of abelian schemes preserves inverses. -/
@[reassoc]
lemma Hom.inv_hom {A B : AbelianScheme S} (f : A ⟶ B) :
    ι[A.toOver] ≫ Hom.toOverHom f = Hom.toOverHom f ≫ ι[B.toOver] :=
  GrpObj.inv_hom (Hom.toOverHom f)

/-- Homomorphisms of abelian schemes commute with integer multiplication. -/
@[reassoc]
lemma Hom.mulBy_comp {A B : AbelianScheme S} (f : A ⟶ B) (n : ℤ) :
    A.mulBy n ≫ Hom.toOverHom f = Hom.toOverHom f ≫ B.mulBy n := by
  rw [mulBy, GrpObj.zpow_comp, Category.id_comp, mulBy, GrpObj.comp_zpow, Category.comp_id]

/-- The forgetful functor from abelian schemes over `S` to `Over S`. -/
def Hom.toOverFunctor : AbelianScheme S ⥤ Over S where
  obj A := A.toOver
  map f := Hom.toOverHom f
  map_id := Hom.toOverHom_id
  map_comp f g := Hom.toOverHom_comp f g

@[simp]
lemma Hom.toOverFunctor_obj (A : AbelianScheme S) :
    (Hom.toOverFunctor (S := S)).obj A = A.toOver :=
  (rfl)

@[simp]
lemma Hom.toOverFunctor_map {A B : AbelianScheme S} (f : A ⟶ B) :
    (Hom.toOverFunctor (S := S)).map f =
      eqToHom (Hom.toOverFunctor_obj A) ≫ Hom.toOverHom f ≫
        eqToHom (Hom.toOverFunctor_obj B).symm := by
  unfold Hom.toOverFunctor
  exact (rfl)

/-- The forgetful functor from abelian schemes over `S` to their underlying schemes. -/
def Hom.toSchemeFunctor : AbelianScheme S ⥤ Scheme.{u} :=
  Hom.toOverFunctor ⋙ Over.forget S

@[simp]
lemma Hom.toSchemeFunctor_obj (A : AbelianScheme S) :
    (Hom.toSchemeFunctor (S := S)).obj A = A.toScheme :=
  (rfl)

/-- The underlying morphism between the schemes of two abelian schemes. -/
abbrev Hom.toSchemeHom {A B : AbelianScheme S} (f : A ⟶ B) : A.toScheme ⟶ B.toScheme :=
  (Hom.toOverHom f).left

@[simp]
lemma Hom.toSchemeFunctor_map {A B : AbelianScheme S} (f : A ⟶ B) :
    (Hom.toSchemeFunctor (S := S)).map f =
      eqToHom (Hom.toSchemeFunctor_obj A) ≫ Hom.toSchemeHom f ≫
        eqToHom (Hom.toSchemeFunctor_obj B).symm := by
  unfold Hom.toSchemeFunctor Hom.toOverFunctor
  exact (rfl)

@[simp]
lemma Hom.toSchemeHom_mk' {A B : AbelianScheme S} (f : A.toOver ⟶ B.toOver)
    (one_f : η[A.toOver] ≫ f = η[B.toOver] := by cat_disch)
    (mul_f : μ[A.toOver] ≫ f = (f ⊗ₘ f) ≫ μ[B.toOver] := by cat_disch) :
    Hom.toSchemeHom (Hom.mk' f one_f mul_f) = f.left :=
  congrArg Over.Hom.left (Hom.toOverHom_mk' f one_f mul_f)

@[simp]
lemma Hom.toSchemeHom_id (A : AbelianScheme S) :
    Hom.toSchemeHom (𝟙 A) = 𝟙 A.toScheme :=
  congrArg Over.Hom.left (Hom.toOverHom_id A)

@[simp, reassoc]
lemma Hom.toSchemeHom_comp {A B C : AbelianScheme S} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.toSchemeHom (f ≫ g) = Hom.toSchemeHom f ≫ Hom.toSchemeHom g :=
  congrArg Over.Hom.left (Hom.toOverHom_comp f g)

/-- The underlying scheme morphism of an abelian-scheme homomorphism commutes with the structure
morphisms to `S`. -/
@[reassoc]
lemma Hom.toSchemeHom_comp_hom {A B : AbelianScheme S} (f : A ⟶ B) :
    Hom.toSchemeHom f ≫ B.toOver.hom = A.toOver.hom :=
  (Hom.toOverHom f).w

/-- Two homomorphisms of abelian schemes are equal when their underlying scheme morphisms are
equal. -/
@[ext]
lemma Hom.ext {A B : AbelianScheme S} {f g : A ⟶ B}
    (h : Hom.toSchemeHom f = Hom.toSchemeHom g) : f = g := by
  unfold Hom.toSchemeHom Hom.toOverHom at h
  apply InducedCategory.hom_ext
  apply Grp.hom_ext
  exact Over.OverMorphism.ext h

/-- Two homomorphisms of abelian schemes with the same underlying morphism over `S` are equal. -/
lemma Hom.toOverHom_injective {A B : AbelianScheme S} {f g : A ⟶ B}
    (h : Hom.toOverHom f = Hom.toOverHom g) : f = g :=
  Hom.ext (congrArg Over.Hom.left h)

instance : (Hom.toOverFunctor (S := S)).Faithful where
  map_injective h := by
    rw [Hom.toOverFunctor_map, Hom.toOverFunctor_map] at h
    simp only [cancel_epi, cancel_mono] at h
    exact Hom.toOverHom_injective h

/-! ### Isomorphisms -/

/-- Construct an isomorphism of abelian schemes from an isomorphism of their underlying objects in
`Over S` whose forward map is a group-object homomorphism. -/
def mkIso' {A B : AbelianScheme S} (e : A.toOver ≅ B.toOver) [IsMonHom e.hom] : A ≅ B where
  hom := Hom.mk' e.hom
  inv := Hom.mk' e.inv
  hom_inv_id := Hom.toOverHom_injective (by simp)
  inv_hom_id := Hom.toOverHom_injective (by simp)

@[simp]
lemma toOverHom_mkIso'_hom {A B : AbelianScheme S} (e : A.toOver ≅ B.toOver) [IsMonHom e.hom] :
    Hom.toOverHom (mkIso' e).hom = e.hom := by
  unfold mkIso'
  simp

@[simp]
lemma toOverHom_mkIso'_inv {A B : AbelianScheme S} (e : A.toOver ≅ B.toOver) [IsMonHom e.hom] :
    Hom.toOverHom (mkIso' e).inv = e.inv := by
  unfold mkIso'
  simp

/-- The isomorphism of schemes over `S` underlying an isomorphism of abelian schemes. -/
def isoToOver {A B : AbelianScheme S} (e : A ≅ B) : A.toOver ≅ B.toOver where
  hom := Hom.toOverHom e.hom
  inv := Hom.toOverHom e.inv
  hom_inv_id := by rw [← Hom.toOverHom_comp, e.hom_inv_id, Hom.toOverHom_id]
  inv_hom_id := by rw [← Hom.toOverHom_comp, e.inv_hom_id, Hom.toOverHom_id]

/-- The isomorphism of schemes underlying an isomorphism of abelian schemes. -/
def isoToScheme {A B : AbelianScheme S} (e : A ≅ B) : A.toScheme ≅ B.toScheme :=
  (Over.forget S).mapIso (isoToOver e)

@[simp]
lemma isoToOver_hom {A B : AbelianScheme S} (e : A ≅ B) :
    (isoToOver e).hom = Hom.toOverHom e.hom := by
  unfold isoToOver
  rfl

@[simp]
lemma isoToOver_inv {A B : AbelianScheme S} (e : A ≅ B) :
    (isoToOver e).inv = Hom.toOverHom e.inv := by
  unfold isoToOver
  rfl

@[simp]
lemma isoToScheme_hom {A B : AbelianScheme S} (e : A ≅ B) :
    (isoToScheme e).hom = Hom.toSchemeHom e.hom := by
  simp [isoToScheme]

@[simp]
lemma isoToScheme_inv {A B : AbelianScheme S} (e : A ≅ B) :
    (isoToScheme e).inv = Hom.toSchemeHom e.inv := by
  simp [isoToScheme]

@[simp]
lemma isoToOver_refl (A : AbelianScheme S) :
    isoToOver (Iso.refl A) = Iso.refl A.toOver := by
  apply Iso.ext
  simp

@[simp]
lemma isoToOver_symm {A B : AbelianScheme S} (e : A ≅ B) :
    isoToOver e.symm = (isoToOver e).symm := by
  apply Iso.ext
  simp

@[simp]
lemma isoToOver_trans {A B C : AbelianScheme S} (e : A ≅ B) (f : B ≅ C) :
    isoToOver (e.trans f) = (isoToOver e).trans (isoToOver f) := by
  apply Iso.ext
  simp

@[simp]
lemma isoToScheme_refl (A : AbelianScheme S) :
    isoToScheme (Iso.refl A) = Iso.refl A.toScheme := by
  apply Iso.ext
  simp

@[simp]
lemma isoToScheme_symm {A B : AbelianScheme S} (e : A ≅ B) :
    isoToScheme e.symm = (isoToScheme e).symm := by
  apply Iso.ext
  simp

@[simp]
lemma isoToScheme_trans {A B C : AbelianScheme S} (e : A ≅ B) (f : B ≅ C) :
    isoToScheme (e.trans f) = (isoToScheme e).trans (isoToScheme f) := by
  apply Iso.ext
  simp

/-! ### The identity (dimension-zero) abelian scheme -/

variable (S)

private lemma isProper_tensorUnit : IsProper (𝟙_ (Over S)).hom := by
  rw [Over.tensorUnit_hom]
  exact inferInstanceAs (IsProper (𝟙 S))

private lemma smooth_tensorUnit : Smooth (𝟙_ (Over S)).hom := by
  rw [Over.tensorUnit_hom]
  exact inferInstanceAs (Smooth (𝟙 S))

private lemma geometricallyConnected_tensorUnit :
    GeometricallyConnected (𝟙_ (Over S)).hom := by
  rw [Over.tensorUnit_hom]
  exact ⟨fun _ _ y Z fst snd h ↦
    have : IsIntegral Z :=
      (geometricallyIntegral_of_isIso (𝟙 S)).geometrically_isIntegral y fst snd h
    inferInstance⟩

/-- The **identity abelian scheme** over `S`: the base scheme `S` viewed as the trivial group
scheme over itself via the monoidal unit `𝟙_ (Over S)`. -/
def identity : AbelianScheme S where
  toOver := 𝟙_ (Over S)
  grpObj := inferInstance
  isProper := isProper_tensorUnit S
  smooth := smooth_tensorUnit S
  geometricallyConnected := geometricallyConnected_tensorUnit S

@[simp]
lemma identity_toOver : (identity S).toOver = 𝟙_ (Over S) :=
  (rfl)

@[simp]
lemma identity_toScheme : (identity S).toScheme = S := by
  simp only [toScheme, identity_toOver, Over.tensorUnit_left]

/-- The group object underlying `identity S` is definitionally `Grp.trivial (Over S)`. -/
lemma grpMk_identity_toOver :
    Grp.mk (identity S).toOver = Grp.trivial (Over S) :=
  (rfl)

/-- The `Over S` object underlying `identity S` is terminal. -/
def isTerminalIdentityToOver : IsTerminal (identity S).toOver :=
  IsTerminal.ofIso isTerminalTensorUnit (eqToIso (identity_toOver S).symm)

@[simp]
lemma identity_one :
    η[(identity S).toOver] ≫ eqToHom (identity_toOver S) = η[𝟙_ (Over S)] := by
  unfold identity
  simp

@[simp]
lemma identity_mul :
    μ[(identity S).toOver] ≫ eqToHom (identity_toOver S) =
      (eqToHom (identity_toOver S) ⊗ₘ eqToHom (identity_toOver S)) ≫ μ[𝟙_ (Over S)] := by
  exact isTerminalTensorUnit.hom_ext _ _

@[simp]
lemma identity_inv :
    ι[(identity S).toOver] ≫ eqToHom (identity_toOver S) =
      eqToHom (identity_toOver S) ≫ ι[𝟙_ (Over S)] := by
  exact isTerminalTensorUnit.hom_ext _ _

/-- Every integer multiplication map on `identity S` is the identity morphism, hence an
isomorphism even for `n = 0` or multiples of any prime `p`. -/
@[simp]
lemma mulBy_identity (n : ℤ) : (identity S).mulBy n = 𝟙 (identity S).toOver :=
  (isTerminalIdentityToOver S).hom_ext _ _

/-- Multiplication by any integer on `identity S` is an isomorphism. -/
instance isIso_mulBy_identity (n : ℤ) : IsIso ((identity S).mulBy n) := by
  rw [mulBy_identity]
  infer_instance

variable {S}

/-- There is a unique homomorphism from any abelian scheme over `S` to `identity S`. -/
instance uniqueHomToIdentity (A : AbelianScheme S) : Unique (A ⟶ identity S) :=
  let iso : Grp.mk (identity S).toOver ≅ Grp.trivial (Over S) :=
    Grp.mkIso (eqToIso (identity_toOver S)) (identity_one S) (identity_mul S)
  let e : (A ⟶ identity S) ≃ (Grp.mk A.toOver ⟶ Grp.mk (identity S).toOver) :=
    InducedCategory.homEquiv
  (e.trans ((Iso.refl _).homCongr iso)).unique

/-- There is a unique homomorphism from `identity S` to any abelian scheme over `S`. -/
instance uniqueHomFromIdentity (A : AbelianScheme S) : Unique (identity S ⟶ A) :=
  let iso : Grp.mk (identity S).toOver ≅ Grp.trivial (Over S) :=
    Grp.mkIso (eqToIso (identity_toOver S)) (identity_one S) (identity_mul S)
  let e : (identity S ⟶ A) ≃ (Grp.mk (identity S).toOver ⟶ Grp.mk A.toOver) :=
    InducedCategory.homEquiv
  (e.trans (iso.homCongr (Iso.refl _))).unique

/-- The unique homomorphism from `A` to `identity S`. -/
def toIdentity (A : AbelianScheme S) : A ⟶ identity S :=
  default

/-- The unique homomorphism from `identity S` to `A`. -/
def fromIdentity (A : AbelianScheme S) : identity S ⟶ A :=
  default

@[simp]
lemma toOverHom_toIdentity (A : AbelianScheme S) :
    Hom.toOverHom (toIdentity A) ≫ eqToHom (identity_toOver S) = toUnit A.toOver :=
  isTerminalTensorUnit.hom_ext _ _

@[simp]
lemma toSchemeHom_toIdentity (A : AbelianScheme S) :
    Hom.toSchemeHom (toIdentity A) ≫ eqToHom (identity_toScheme S) = A.toOver.hom := by
  have h := congrArg Over.Hom.left (toOverHom_toIdentity A)
  rw [Over.comp_left, Over.eqToHom_left] at h
  exact h

@[simp]
lemma toOverHom_fromIdentity (A : AbelianScheme S) :
    eqToHom (identity_toOver S).symm ≫ Hom.toOverHom (fromIdentity A) = η[A.toOver] := by
  have h := Hom.one_hom (fromIdentity A)
  have h1 : η[(identity S).toOver] = eqToHom (identity_toOver S).symm :=
    (isTerminalIdentityToOver S).hom_ext _ _
  rwa [h1] at h

@[simp]
lemma toSchemeHom_fromIdentity (A : AbelianScheme S) :
    eqToHom (identity_toScheme S).symm ≫ Hom.toSchemeHom (fromIdentity A) = A.zeroSection := by
  have h := congrArg Over.Hom.left (toOverHom_fromIdentity A)
  rw [Over.comp_left, Over.eqToHom_left] at h
  exact h

/-- `identity S` is terminal in `AbelianScheme S`. -/
def isTerminalIdentity (S : Scheme.{u}) : IsTerminal (identity S) :=
  IsTerminal.ofUnique _

/-- `identity S` is initial in `AbelianScheme S`. -/
def isInitialIdentity (S : Scheme.{u}) : IsInitial (identity S) :=
  IsInitial.ofUnique _

/-- `identity S` is a zero object of `AbelianScheme S`. -/
lemma isZeroIdentity (S : Scheme.{u}) : IsZero (identity S) where
  unique_to A := nonempty_unique (identity S ⟶ A)
  unique_from A := nonempty_unique (A ⟶ identity S)

instance (S : Scheme.{u}) : HasZeroObject (AbelianScheme S) :=
  ⟨identity S, isZeroIdentity S⟩

end

end AbelianScheme

end AlgebraicGeometry

end TauCeti
