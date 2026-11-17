/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import TauCeti.CategoryTheory.GradedObject.Twisted.Basic
public import TauCeti.CategoryTheory.GradedObject.Scalar

/-!
# Changing the cocycle of a twisted graded category

A normalized two-cochain relating two associator cocycles gives a strong monoidal, additive, and
linear equivalence between their twisted graded categories. The underlying functor is the identity
on graded objects and morphisms; its tensorator multiplies the summand of bidegree `(i, j)` by the
two-cochain, and in particular acts on `(single i).obj A ⊗ (single j).obj B` as scalar
multiplication by `g.u i j`. Thus changing the cocycle by a coboundary changes the monoidal
structure only up to linear monoidal equivalence.

`TauCeti.GradedObject.TwistingCocycle.Gauge` records the scalar coherence equation, with its
orientation fixed by the tensorator. `Gauge.equivalence` and its monoidal, additive, and linear
instances implement the change of cocycle without changing the objects or their supports.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §2.6
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.GradedObject CategoryTheory.GradedObject.Monoidal

namespace TauCeti.GradedObject.TwistingCocycle

section Cochains

variable {I R : Type*} [AddMonoid I] [CommMonoid R]

/-- A normalized two-cochain whose scalar tensorator carries the associator `c` to `d`.
The coherence equation is the multiplicative coboundary relation, oriented for a functor
from the `c`-twisted category to the `d`-twisted category. -/
@[ext]
structure Gauge (c d : TwistingCocycle I R) where
  /-- The scalar of the tensorator on a homogeneous tensor product. -/
  u : I → I → Rˣ
  /-- Normalization at the left unit. -/
  u_zero_left : ∀ i, u 0 i = 1
  /-- Normalization at the right unit. -/
  u_zero_right : ∀ i, u i 0 = 1
  /-- The associativity coherence equation. -/
  coherence : ∀ i j k, u i j * u (i + j) k * c.ω i j k =
    d.ω i j k * u j k * u i (j + k)

namespace Gauge

attribute [simp] u_zero_left u_zero_right

variable {c d : TwistingCocycle I R}

/-- The identity change of cocycle. -/
def refl (c : TwistingCocycle I R) : Gauge c c where
  u _ _ := 1
  u_zero_left _ := rfl
  u_zero_right _ := rfl
  coherence _ _ _ := by simp

/-- Inverting the two-cochain reverses the change of cocycle. -/
def symm (g : Gauge c d) : Gauge d c where
  u i j := (g.u i j)⁻¹
  u_zero_left _ := by simp
  u_zero_right _ := by simp
  coherence i j k := by
    have h := g.coherence i j k
    apply (mul_left_cancel_iff (a := g.u i j * g.u (i + j) k)).mp
    apply (mul_right_cancel_iff (a := g.u j k * g.u i (j + k))).mp
    simpa [mul_assoc, mul_comm, mul_left_comm] using h.symm

/-- The identity gauge has constant scalar one. -/
@[simp]
lemma refl_u (c : TwistingCocycle I R) (i j : I) : (refl c).u i j = 1 := (rfl)

/-- The reversed gauge uses inverse scalars. -/
@[simp]
lemma symm_u (g : Gauge c d) (i j : I) : g.symm.u i j = (g.u i j)⁻¹ := (rfl)

/-- Normalize a two-cochain satisfying the scalar coherence relation by dividing by its
value at `(0, 0)`. Normalization of the associator cocycles forces both unit edges of the
original two-cochain to have this same constant value. -/
def ofCochain (c d : TwistingCocycle I R) (u : I → I → Rˣ)
    (h : ∀ i j k, u i j * u (i + j) k * c.ω i j k =
      d.ω i j k * u j k * u i (j + k)) : Gauge c d where
  u i j := u i j / u 0 0
  u_zero_left i := by
    have hi : u 0 0 = u 0 i := by simpa using h 0 0 i
    simp [hi]
  u_zero_right i := by
    have hi : u i 0 = u 0 0 := by simpa using h i 0 0
    simp [hi]
  coherence i j k := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      congrArg (fun t ↦ t * (u 0 0)⁻¹ * (u 0 0)⁻¹) (h i j k)

/-- The normalized two-cochain divides the original scalars by their value at `(0, 0)`. -/
@[simp]
lemma ofCochain_u (c d : TwistingCocycle I R) (u : I → I → Rˣ)
    (h : ∀ i j k, u i j * u (i + j) k * c.ω i j k =
      d.ω i j k * u j k * u i (j + k)) (i j : I) :
    (ofCochain c d u h).u i j = u i j / u 0 0 := (rfl)

end Gauge

end Cochains

namespace Gauge

variable {I R : Type*} [AddMonoid I] [CommSemiring R]
  {c d : TwistingCocycle I R} (g : Gauge c d) (C : Type*) [Category* C]

/-- The identity on graded objects and morphisms, regarded as a functor between twists. -/
-- Expose the identity carrier so the tensorators on graded objects have the required types.
@[expose]
def functor (_g : Gauge c d) : TwistedGradedObject c C ⥤ TwistedGradedObject d C where
  obj X := X
  map f := f

variable {C} in
/-- A change of cocycle leaves graded objects unchanged. -/
@[simp]
lemma _root_.CategoryTheory.GradedObject.gaugeFunctor_obj (X : GradedObject I C)
    (g : Gauge c d) : (g.functor C).obj X = X := (rfl)

/-- A change of cocycle leaves graded morphisms unchanged. -/
@[simp]
lemma functor_map {X Y : GradedObject I C} (f : X ⟶ Y) :
    (g.functor C).map f = f := (rfl)

/-- The equivalence underlying a change of cocycle. -/
def equivalence : TwistedGradedObject c C ≌ TwistedGradedObject d C where
  functor := g.functor C
  inverse := g.symm.functor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := by
    -- The unit and counit are identity transformations on the underlying graded category.
    exact Category.id_comp _

/-- The forward functor of the equivalence is the identity with the gauge tensorator. -/
@[simp]
lemma equivalence_functor : (g.equivalence C).functor = g.functor C := (rfl)

/-- The inverse functor is the identity with inverse gauge scalars. -/
@[simp]
lemma equivalence_inverse : (g.equivalence C).inverse = g.symm.functor C := (rfl)

/-- The forward functor of the gauge equivalence leaves objects unchanged. -/
lemma equivalence_functor_obj (X : GradedObject I C) :
    (g.equivalence C).functor.obj X = X := (rfl)

/-- The inverse functor of the gauge equivalence leaves objects unchanged. -/
lemma equivalence_inverse_obj (X : GradedObject I C) :
    (g.equivalence C).inverse.obj X = X := (rfl)

/-- The forward functor of the gauge equivalence is the identity on graded morphisms, up to
`eqToHom`. -/
lemma equivalence_functor_map {X Y : GradedObject I C} (f : X ⟶ Y) :
    (g.equivalence C).functor.map f =
      eqToHom (g.equivalence_functor_obj C X) ≫ f ≫
        eqToHom (g.equivalence_functor_obj C Y).symm := by
  -- Inside this module `equivalence` unfolds to `g.functor C`, whose map is the identity.
  change f = eqToHom (rfl : X = X) ≫ f ≫ eqToHom (rfl : Y = Y)
  simp

/-- The inverse functor of the gauge equivalence is the identity on graded morphisms, up to
`eqToHom`. -/
lemma equivalence_inverse_map {X Y : GradedObject I C} (f : X ⟶ Y) :
    (g.equivalence C).inverse.map f =
      eqToHom (g.equivalence_inverse_obj C X) ≫ f ≫
        eqToHom (g.equivalence_inverse_obj C Y).symm := by
  -- Inside this module `equivalence` unfolds to `g.symm.functor C`, whose map is the identity.
  change f = eqToHom (rfl : X = X) ≫ f ≫ eqToHom (rfl : Y = Y)
  simp

-- Equality transports let the component formulas avoid unfolding the sealed equivalence.
/-- The unit of the gauge equivalence is the identity on each graded object. -/
@[simp]
lemma equivalence_unitIso_hom_app (X : TwistedGradedObject c C) :
    (g.equivalence C).unitIso.hom.app X = eqToHom (by simp [functor]) := (rfl)

/-- The inverse unit of the gauge equivalence is the identity on each graded object. -/
@[simp]
lemma equivalence_unitIso_inv_app (X : TwistedGradedObject c C) :
    (g.equivalence C).unitIso.inv.app X = eqToHom (by simp [functor]) := (rfl)

/-- The counit of the gauge equivalence is the identity on each graded object. -/
@[simp]
lemma equivalence_counitIso_hom_app (X : TwistedGradedObject d C) :
    (g.equivalence C).counitIso.hom.app X = eqToHom (by simp [functor]) := (rfl)

/-- The inverse counit of the gauge equivalence is the identity on each graded object. -/
@[simp]
lemma equivalence_counitIso_inv_app (X : TwistedGradedObject d C) :
    (g.equivalence C).counitIso.inv.app X = eqToHom (by simp [functor]) := (rfl)

/-- A change of cocycle is additive on morphisms. -/
instance functor_additive [Preadditive C] : (g.functor C).Additive where
  map_add := rfl

/-- A change of cocycle is `S`-linear on morphisms. -/
instance functor_linear (S : Type*) [Semiring S] [Preadditive C] [Linear S C] :
    (g.functor C).Linear S where
  map_smul _ _ := rfl

/-- The forward functor of the gauge equivalence is additive. -/
instance equivalence_functor_additive [Preadditive C] : (g.equivalence C).functor.Additive :=
  inferInstanceAs (g.functor C).Additive

/-- The forward functor of the gauge equivalence is `S`-linear. -/
instance equivalence_functor_linear (S : Type*) [Semiring S] [Preadditive C] [Linear S C] :
    (g.equivalence C).functor.Linear S where
  map_smul _ _ := rfl

/-- The inverse functor of the gauge equivalence is additive. -/
instance equivalence_inverse_additive [Preadditive C] : (g.equivalence C).inverse.Additive where
  map_add := rfl

/-- The inverse functor of the gauge equivalence is `S`-linear. -/
instance equivalence_inverse_linear (S : Type*) [Semiring S] [Preadditive C] [Linear S C] :
    (g.equivalence C).inverse.Linear S where
  map_smul _ _ := rfl

variable [MonoidalCategory C] [Preadditive C] [Linear R C] [MonoidalPreadditive C]
  [MonoidalLinear R C]
  [∀ (X Y : GradedObject I C), HasTensor X Y]
  [∀ (X Y Z : GradedObject I C), HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject I C), HasGoodTensorTensor₂₃ X Y Z]
  [DecidableEq I] [HasInitial C]
  [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
  [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X)]
  [∀ (W X Y Z : GradedObject I C), HasTensor₄ObjExt W X Y Z]

/-- The scalar tensorator makes the change-of-cocycle functor strong monoidal. -/
instance functorMonoidal : (g.functor C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
  εIso := Iso.refl _
  μIso (X Y : GradedObject I C) := scaleTensorIso X Y g.u
  μIso_hom_natural_left {X Y : GradedObject I C} f (Z : GradedObject I C) := by
    -- Unwrap the monoidal type synonyms before comparing their degreewise maps.
    change Monoidal.tensorHom f (𝟙 Z) ≫ (scaleTensorIso Y Z g.u).hom =
      (scaleTensorIso X Z g.u).hom ≫ Monoidal.tensorHom f (𝟙 Z)
    rw [scaleTensorIso_hom, scaleTensorIso_hom]
    exact tensorHom_scaleTensorObj f (𝟙 Z) (fun i j ↦ (g.u i j : R))
  μIso_hom_natural_right {X Y : GradedObject I C} (Z : GradedObject I C) f := by
    -- Unwrap the monoidal type synonyms before comparing their degreewise maps.
    change Monoidal.tensorHom (𝟙 Z) f ≫ (scaleTensorIso Z Y g.u).hom =
      (scaleTensorIso Z X g.u).hom ≫ Monoidal.tensorHom (𝟙 Z) f
    rw [scaleTensorIso_hom, scaleTensorIso_hom]
    exact tensorHom_scaleTensorObj (𝟙 Z) f (fun i j ↦ (g.u i j : R))
  associativity (X Y Z : GradedObject I C) := by
    -- Unwrap the identity functor and the two monoidal type synonyms, so coproduct
    -- extensionality applies in the underlying graded category.
    change Monoidal.tensorHom (scaleTensorIso X Y g.u).hom (𝟙 Z) ≫
        (scaleTensorIso (Monoidal.tensorObj X Y) Z g.u).hom ≫
        (twistedAssociator c.ω X Y Z).hom =
      (twistedAssociator d.ω X Y Z).hom ≫
        Monoidal.tensorHom (𝟙 X) (scaleTensorIso Y Z g.u).hom ≫
        (scaleTensorIso X (Monoidal.tensorObj Y Z) g.u).hom
    simp only [scaleTensorIso_hom]
    ext n i j k h
    simp only [categoryOfGradedObjects_comp, Category.assoc,
      ιTensorObj₃'_tensorHom_scaleTensorObj_assoc, Linear.smul_comp,
      ιTensorObj₃'_scaleTensorObj_assoc, ιTensorObj₃'_twistedAssociator_hom,
      ιTensorObj₃'_twistedAssociator_hom_assoc, Linear.comp_smul,
      ιTensorObj₃_tensorHom_scaleTensorObj_assoc, ιTensorObj₃_scaleTensorObj, smul_smul]
    have hc := congrArg (fun x : Rˣ ↦ (x : R)) (g.coherence i j k)
    simp only [Units.val_mul] at hc
    simp only [← mul_assoc, hc]
  left_unitality (X : GradedObject I C) := by
    -- Both twists have Mathlib's unit and unitors; unwrap their identity functor.
    change (Monoidal.leftUnitor X).hom = Monoidal.tensorHom (𝟙 Monoidal.tensorUnit) (𝟙 X) ≫
      (scaleTensorIso Monoidal.tensorUnit X g.u).hom ≫ (Monoidal.leftUnitor X).hom
    rw [scaleTensorIso_hom, scaleTensorObj_tensorUnit_left _ _ (by simp)]
    simp
  right_unitality (X : GradedObject I C) := by
    -- Both twists have Mathlib's unit and unitors; unwrap their identity functor.
    change (Monoidal.rightUnitor X).hom = Monoidal.tensorHom (𝟙 X) (𝟙 Monoidal.tensorUnit) ≫
      (scaleTensorIso X Monoidal.tensorUnit g.u).hom ≫ (Monoidal.rightUnitor X).hom
    rw [scaleTensorIso_hom, scaleTensorObj_tensorUnit_right _ _ (by simp)]
    simp }

/-- The unit comparison of the change-of-cocycle functor is the identity. -/
@[simp]
lemma functor_ε : Functor.LaxMonoidal.ε (g.functor C) = 𝟙 Monoidal.tensorUnit := (rfl)

variable {C} in
/-- The tensorator is multiplication by the two-cochain on each homogeneous summand. -/
lemma _root_.CategoryTheory.GradedObject.gaugeFunctor_μ (X Y : GradedObject I C)
    (g : Gauge c d) :
    Functor.LaxMonoidal.μ (g.functor C) X Y =
      scaleTensorObj X Y (fun i j ↦ (g.u i j : R)) :=
  scaleTensorIso_hom X Y g.u

/-- The inverse unit comparison of the change-of-cocycle functor is the identity. -/
@[simp]
lemma functor_η : Functor.OplaxMonoidal.η (g.functor C) = 𝟙 Monoidal.tensorUnit := (rfl)

variable {C} in
/-- The inverse tensorator acts by the inverse two-cochain. -/
lemma _root_.CategoryTheory.GradedObject.gaugeFunctor_δ (X Y : GradedObject I C)
    (g : Gauge c d) :
    Functor.OplaxMonoidal.δ (g.functor C) X Y =
      scaleTensorObj X Y (fun i j ↦ (((g.u i j)⁻¹ : Rˣ) : R)) :=
  scaleTensorIso_inv X Y g.u

variable {C} in
/-- The tensorator multiplies a tensor summand by its gauge scalar. -/
@[reassoc, simp]
lemma _root_.CategoryTheory.GradedObject.ι_gaugeFunctor_μ (X Y : GradedObject I C)
    (g : Gauge c d) (i j n : I) (h : i + j = n) :
    ιTensorObj X Y i j n h ≫ Functor.LaxMonoidal.μ (g.functor C) X Y n =
      (g.u i j : R) • ιTensorObj X Y i j n h := by
  rw [gaugeFunctor_μ]
  exact ι_scaleTensorObj X Y _ i j n h

variable {C} in
/-- The inverse tensorator multiplies a tensor summand by its inverse gauge scalar. -/
@[reassoc, simp]
lemma _root_.CategoryTheory.GradedObject.ι_gaugeFunctor_δ (X Y : GradedObject I C)
    (g : Gauge c d) (i j n : I) (h : i + j = n) :
    ιTensorObj X Y i j n h ≫ Functor.OplaxMonoidal.δ (g.functor C) X Y n =
      (((g.u i j)⁻¹ : Rˣ) : R) • ιTensorObj X Y i j n h := by
  rw [gaugeFunctor_δ]
  exact ι_scaleTensorObj X Y _ i j n h

variable {C} in
/-- On two single-degree graded objects, the gauge tensorator is scalar multiplication by
`g.u i j`. -/
lemma functor_μ_single (i j : I) (A B : C) :
    Functor.LaxMonoidal.μ (g.functor C) ((single i).obj A) ((single j).obj B) =
      (g.u i j : R) • 𝟙 (Monoidal.tensorObj ((single i).obj A) ((single j).obj B)) := by
  rw [gaugeFunctor_μ]
  -- Unwrap the type synonym `TwistedGradedObject d C` so graded coproduct extensionality applies.
  change (scaleTensorObj ((single i).obj A) ((single j).obj B) (fun a b ↦ (g.u a b : R)) :
      Monoidal.tensorObj ((single i).obj A) ((single j).obj B) ⟶ _) =
    (g.u i j : R) • 𝟙 _
  ext n a b h
  rw [ι_scaleTensorObj, GradedObject.smul_apply, Linear.comp_smul, categoryOfGradedObjects_id,
    Category.comp_id]
  by_cases ha : a = i
  · subst ha
    by_cases hb : b = j
    · subst hb
      rfl
    · exact ((isInitialSingleObjApply j B b hb).isInitialObj
        ((curriedTensor C).obj _)).hom_ext _ _
  · exact ((isInitialSingleObjApply i A a ha).isInitialObj
      ((curriedTensor C).flip.obj _)).hom_ext _ _

/-- The forward functor of the gauge equivalence has the scalar tensorator. -/
instance equivalenceFunctorMonoidal : (g.equivalence C).functor.Monoidal :=
  inferInstanceAs (g.functor C).Monoidal

/-- The inverse functor of the gauge equivalence has the inverse scalar tensorator. -/
instance equivalenceInverseMonoidal : (g.equivalence C).inverse.Monoidal :=
  inferInstanceAs (g.symm.functor C).Monoidal

/-- The unit comparison of `(g.equivalence C).functor` is `eqToHom`. -/
lemma equivalence_functor_ε :
    Functor.LaxMonoidal.ε (g.equivalence C).functor =
      eqToHom (g.equivalence_functor_obj C (𝟙_ (TwistedGradedObject c C))).symm := by
  -- Inside `Twisted/Equivalence.lean`, `equivalence` unfolds to `g.functor C`.
  change Functor.LaxMonoidal.ε (g.functor C) = 𝟙 Monoidal.tensorUnit
  exact g.functor_ε C

/-- The tensorator of `(g.equivalence C).functor` acts by `scaleTensorObj` up to `eqToHom`. -/
lemma equivalence_functor_μ (X Y : GradedObject I C) :
    Functor.LaxMonoidal.μ (g.equivalence C).functor X Y =
      eqToHom (by rw [g.equivalence_functor_obj, g.equivalence_functor_obj]; rfl) ≫
        scaleTensorObj X Y (fun i j ↦ (g.u i j : R)) ≫
        eqToHom (g.equivalence_functor_obj C (Monoidal.tensorObj X Y)).symm := by
  -- Inside `Twisted/Equivalence.lean`, `equivalence` unfolds to `g.functor C`.
  change Functor.LaxMonoidal.μ (g.functor C) X Y =
    𝟙 _ ≫ scaleTensorObj X Y (fun i j ↦ (g.u i j : R)) ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  exact gaugeFunctor_μ X Y g

variable {C} in
/-- On two single-degree objects, the tensorator of `(g.equivalence C).functor` is scalar
multiplication by `g.u i j`. -/
lemma equivalence_functor_μ_single (i j : I) (A B : C) :
    Functor.LaxMonoidal.μ (g.equivalence C).functor ((single i).obj A) ((single j).obj B) =
      (g.u i j : R) •
        eqToHom (Eq.trans
          (congrArg₂ (MonoidalCategoryStruct.tensorObj (C := TwistedGradedObject d C))
            (g.equivalence_functor_obj C ((single i).obj A))
            (g.equivalence_functor_obj C ((single j).obj B)))
          (Eq.trans
            (TwistedGradedObject.tensorObj_eq ((single i).obj A) ((single j).obj B))
            (g.equivalence_functor_obj C
              (Monoidal.tensorObj ((single i).obj A) ((single j).obj B))).symm)) := by
  -- Inside `Twisted/Equivalence.lean`, `equivalence` unfolds to `g.functor C`.
  change Functor.LaxMonoidal.μ (g.functor C) ((single i).obj A) ((single j).obj B) =
    (g.u i j : R) • 𝟙 _
  exact g.functor_μ_single i j A B

/-- The inverse gauge tensorator is compatible with the identity unit and counit. -/
instance equivalence_isMonoidal : (g.equivalence C).IsMonoidal where
  leftAdjoint_ε := by
    -- Unwrap the identity unit of the equivalence's adjunction.
    change Functor.LaxMonoidal.ε (g.symm.functor C) =
      𝟙 (Monoidal.tensorUnit : GradedObject I C) ≫ Functor.OplaxMonoidal.η (g.functor C)
    rw [functor_ε, functor_η]
    exact (Category.id_comp _).symm
  leftAdjoint_μ (X Y : GradedObject I C) := by
    -- The counit and underlying inverse functor are identities on graded morphisms.
    change Functor.LaxMonoidal.μ (g.symm.functor C) X Y =
      𝟙 (Monoidal.tensorObj X Y) ≫ (Functor.OplaxMonoidal.δ (g.functor C) X Y ≫
        Monoidal.tensorHom (𝟙 X) (𝟙 Y))
    simp only [gaugeFunctor_μ, gaugeFunctor_δ, Monoidal.id_tensorHom_id, Category.id_comp, symm_u]
    exact (Category.comp_id _).symm

end Gauge

variable {R : Type*} [CommMonoid R]

/-- Two normalized group cocycles admit a gauge tensorator exactly when their quotient is a
three-coboundary for the trivial action on the coefficient units. In conjunction with
`Gauge.equivalence`, this gives the monoidal equivalence associated to cohomologous cocycles. -/
theorem nonempty_gauge_iff_isMulCoboundary₃ {G : Type*} [Monoid G] [SMul G Rˣ]
    (c d : TwistingCocycle (Additive G) R) (htriv : ∀ (a : G) (x : Rˣ), a • x = x) :
    Nonempty (Gauge c d) ↔ groupCohomology.IsMulCoboundary₃
      (fun (a, b, e) ↦ c.ω (Additive.ofMul a) (Additive.ofMul b) (Additive.ofMul e) /
        d.ω (Additive.ofMul a) (Additive.ofMul b) (Additive.ofMul e)) := by
  rw [groupCohomology.isMulCoboundary₃_iff]
  constructor
  · rintro ⟨g⟩
    refine ⟨fun (a, b) ↦ g.u (Additive.ofMul a) (Additive.ofMul b), fun a b e ↦ ?_⟩
    simp only [htriv]
    rw [div_mul_eq_mul_div, div_div, div_eq_div_iff_mul_eq_mul]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (g.coherence (Additive.ofMul a) (Additive.ofMul b) (Additive.ofMul e)).symm
  · rintro ⟨u, hu⟩
    refine ⟨Gauge.ofCochain c d (fun i j ↦ u (i.toMul, j.toMul)) fun i j k ↦ ?_⟩
    have h := hu i.toMul j.toMul k.toMul
    rw [htriv, div_mul_eq_mul_div, div_div, div_eq_div_iff_mul_eq_mul] at h
    simpa [mul_assoc, mul_comm, mul_left_comm] using h.symm

end TauCeti.GradedObject.TwistingCocycle
