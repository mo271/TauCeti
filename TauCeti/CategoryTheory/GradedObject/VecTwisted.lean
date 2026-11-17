/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Preadditive.HomOrthogonal
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Finiteness.Prod
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit
public import TauCeti.CategoryTheory.GradedObject.Module
public import TauCeti.CategoryTheory.GradedObject.Twisted.Basic
public import TauCeti.CategoryTheory.GradedObject.Twisted.Equivalence
public import TauCeti.CategoryTheory.Linear.Endomorphism
public import TauCeti.CategoryTheory.Linear.FullSubcategory
public import TauCeti.CategoryTheory.Monoidal.Subcategory
public import TauCeti.CategoryTheory.ObjectProperty
public import TauCeti.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Finitely supported cocycle-twisted graded projective modules

`VecTwisted R G c` is the full subcategory of cocycle-twisted `G`-graded `R`-modules whose
components are finitely generated and projective over the commutative ring `R`, and whose
categorical support is finite. No finiteness assumption on the grading monoid `G` is required,
and `G` need only be a `Monoid` for the constructions in this file. Over a field, every module is
free (hence projective), recovering the pointed monoidal category usually denoted `Vec^ω_G`.

The defining property `VecTwisted.objects R G c` is closed under isomorphisms, finite products,
and convolution tensor products (including the tensor unit). As a result `VecTwisted R G c`
inherits `Preadditive`, `Linear R`, `HasFiniteBiproducts`, `MonoidalCategory`,
`MonoidalPreadditive`, and `MonoidalLinear R` structures directly from
`TwistedGradedObject c (ModuleCat.{u} R)`.

## Main definitions and results

* `TauCeti.VecTwisted`: the full subcategory of `TwistedGradedObject c (ModuleCat.{u} R)` on
  finitely supported graded modules with finitely generated projective components.
* `TauCeti.VecTwisted.single`, `TauCeti.VecTwisted.singleMap`, `TauCeti.VecTwisted.singleEvalIso`,
  `TauCeti.VecTwisted.delta`, and `TauCeti.VecTwisted.deltaEvalIso`: objects concentrated in a
  single degree `g`, functoriality on morphisms, evaluation isomorphisms, and the rank-one object
  `delta g = single g (ModuleCat.of R R)`.
* `TauCeti.VecTwisted.singleHomEquiv` and `TauCeti.VecTwisted.deltaHomEquiv`: `R`-linear
  identifications of morphisms out of `single g M` and `delta g`.
* `TauCeti.VecTwisted.bijective_algebraMap_end_delta` and `TauCeti.VecTwisted.endDeltaAlgEquiv`:
  `algebraMap R (End (delta g))` is an `R`-algebra isomorphism `End (delta g) ≃ₐ[R] R` for every
  `g : G` (over every commutative ring `R`, including the zero ring).
* `TauCeti.VecTwisted.homOrthogonal_delta`: the family `delta : G → VecTwisted R G c` is
  hom-orthogonal (`Hom (delta g) (delta h)` is subsingleton for `g ≠ h`).
* `TauCeti.VecTwisted.deltaOneIso`, `TauCeti.VecTwisted.deltaTensorIso`,
  `TauCeti.VecTwisted.deltaTensorIso_one_left`, `TauCeti.VecTwisted.deltaTensorIso_one_right`,
  and `TauCeti.VecTwisted.associator_hom_delta`: monoidal calculus on the rank-one generators
  `delta g`, showing in particular that the associator on `(delta g ⊗ delta h) ⊗ delta l` acts
  by the scalar `c.ω (Additive.ofMul g) (Additive.ofMul h) (Additive.ofMul l)`.
* `TauCeti.VecTwisted.isoBiproductSingle`, `TauCeti.VecTwisted.singleIsoBiproductDelta`, and
  `TauCeti.VecTwisted.exists_iso_biproduct_delta_of_free`: decomposition of every object into a
  finite biproduct of single-degree summands, and into a finite biproduct of `delta` objects
  whenever every homogeneous component is free.
* `TauCeti.VecTwisted.gaugeEquivalence`: cohomologous cocycles yield `R`-linear strong monoidal
  equivalences `VecTwisted R G c ≌ VecTwisted R G d`, with tensorator `g.u x y` on
  single-degree objects.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §2.3 and §2.6
  (Example 2.3.8, Proposition 2.6.1).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe u

namespace TauCeti

variable (R G : Type u) [CommRing R] [Monoid G]

/-- The objects of `VecTwisted`: finitely supported graded `R`-modules with finitely generated
projective components. The grading is written additively using `Additive G`, so that convolution
uses multiplication in `G`. -/
def VecTwisted.objects (c : GradedObject.TwistingCocycle (Additive G) R) :
    ObjectProperty (TwistedGradedObject c (ModuleCat.{u} R)) :=
  fun X ↦ CategoryTheory.GradedObject.HasFiniteSupport X ∧
    (∀ g, Module.Finite R (X g)) ∧ ∀ g, Module.Projective R (X g)

/-- The category of finitely supported `G`-graded `R`-modules with finitely generated projective
components, with associator twisted by the normalized three-cocycle `c`. -/
abbrev VecTwisted (c : GradedObject.TwistingCocycle (Additive G) R) :=
  (VecTwisted.objects R G c).FullSubcategory

namespace VecTwisted

variable {R G} (c : GradedObject.TwistingCocycle (Additive G) R)

/-- Membership in the defining full subcategory is exactly finite support together with finiteness
and projectivity of every homogeneous component. -/
theorem objects_iff (X : TwistedGradedObject c (ModuleCat.{u} R)) :
    objects R G c X ↔
      CategoryTheory.GradedObject.HasFiniteSupport X ∧
        (∀ g, Module.Finite R (X g)) ∧ ∀ g, Module.Projective R (X g) :=
  Iff.rfl

/-- The defining object property of `VecTwisted` is closed under isomorphisms. -/
instance objects_isClosedUnderIsomorphisms :
    (objects R G c).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    have : ∀ g, Module.Finite R (X g) := hX.2.1
    have : ∀ g, Module.Projective R (X g) := hX.2.2
    refine ⟨(CategoryTheory.GradedObject.hasFiniteSupport_iff_of_iso e).mp hX.1,
      fun g ↦ ?_, fun g ↦ ?_⟩
    · let eg : X g ≅ Y g :=
        { hom := e.hom g
          inv := e.inv g
          hom_inv_id := congrFun e.hom_inv_id g
          inv_hom_id := congrFun e.inv_hom_id g }
      exact Module.Finite.equiv eg.toLinearEquiv
    · let eg : X g ≅ Y g :=
        { hom := e.hom g
          inv := e.inv g
          hom_inv_id := congrFun e.hom_inv_id g
          inv_hom_id := congrFun e.inv_hom_id g }
      exact Module.Projective.of_equiv eg.toLinearEquiv

/-- The defining object property of `VecTwisted` contains the zero graded module. -/
instance objects_containsZero : (objects R G c).ContainsZero := by
  let Z : TwistedGradedObject c (ModuleCat.{u} R) := fun _ ↦ ModuleCat.of R PUnit.{u + 1}
  have hzComp (g : Additive G) : IsZero (Z g) :=
    ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  have hZ : IsZero Z :=
    (IsZero.iff_id_eq_zero Z).mpr (funext fun g ↦ (hzComp g).eq_of_src _ _)
  refine ⟨Z, hZ, ?_, fun _ ↦ inferInstance, fun _ ↦ Module.Projective.of_free⟩
  have hsup : CategoryTheory.GradedObject.support Z = ∅ := by
    ext g
    exact ⟨fun h ↦ ((CategoryTheory.GradedObject.mem_support Z g).mp h) (hzComp g),
      False.elim⟩
  rw [CategoryTheory.GradedObject.hasFiniteSupport_iff_finite, hsup]
  exact Set.finite_empty

/-- The defining object property of `VecTwisted` is closed under binary products. -/
instance objects_isClosedUnderBinaryProducts :
    (objects R G c).IsClosedUnderBinaryProducts := by
  have : HasBinaryBiproducts (TwistedGradedObject c (ModuleCat.{u} R)) :=
    Limits.hasBinaryBiproducts_of_finite_biproducts (TwistedGradedObject c (ModuleCat.{u} R))
  refine ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod (objects R G c) ?_
  intro X Y hX hY
  have : ∀ g, Module.Finite R (X g) := hX.2.1
  have : ∀ g, Module.Projective R (X g) := hX.2.2
  have : ∀ g, Module.Finite R (Y g) := hY.2.1
  have : ∀ g, Module.Projective R (Y g) := hY.2.2
  let XY : TwistedGradedObject c (ModuleCat.{u} R) := X ⊞ Y
  let fst : XY ⟶ X := biprod.fst (X := X) (Y := Y)
  let snd : XY ⟶ Y := biprod.snd (X := X) (Y := Y)
  let inl : X ⟶ XY := biprod.inl (X := X) (Y := Y)
  let inr : Y ⟶ XY := biprod.inr (X := X) (Y := Y)
  let isoProd (g : Additive G) : XY g ≅ ModuleCat.of R (X g × Y g) :=
    { hom := ModuleCat.ofHom ((fst g).hom.prod (snd g).hom)
      inv := ModuleCat.ofHom ((inl g).hom.coprod (inr g).hom)
      hom_inv_id := by
        apply ModuleCat.hom_ext
        ext x
        have htot : (fst g ≫ inl g) + (snd g ≫ inr g) = 𝟙 (XY g) :=
          congrFun (biprod.total (X := X) (Y := Y)) g
        exact congrArg (fun φ : XY g ⟶ XY g ↦ φ.hom x) htot
      inv_hom_id := by
        apply ModuleCat.hom_ext
        refine LinearMap.ext fun ⟨x, y⟩ ↦ Prod.ext ?_ ?_
        · have h1 : inl g ≫ fst g = 𝟙 (X g) := congrFun (biprod.inl_fst (X := X) (Y := Y)) g
          have h2 : inr g ≫ fst g = 0 := congrFun (biprod.inr_fst (X := X) (Y := Y)) g
          have hx : (fst g).hom ((inl g).hom x) = x :=
            congrArg (fun φ : X g ⟶ X g ↦ φ.hom x) h1
          have hy : (fst g).hom ((inr g).hom y) = 0 :=
            congrArg (fun φ : Y g ⟶ X g ↦ φ.hom y) h2
          exact (map_add (fst g).hom _ _).trans ((congrArg₂ (· + ·) hx hy).trans (add_zero x))
        · have h1 : inl g ≫ snd g = 0 := congrFun (biprod.inl_snd (X := X) (Y := Y)) g
          have h2 : inr g ≫ snd g = 𝟙 (Y g) := congrFun (biprod.inr_snd (X := X) (Y := Y)) g
          have hx : (snd g).hom ((inl g).hom x) = 0 :=
            congrArg (fun φ : X g ⟶ Y g ↦ φ.hom x) h1
          have hy : (snd g).hom ((inr g).hom y) = y :=
            congrArg (fun φ : Y g ⟶ Y g ↦ φ.hom y) h2
          exact (map_add (snd g).hom _ _).trans ((congrArg₂ (· + ·) hx hy).trans (zero_add y)) }
  refine ⟨?_, fun g ↦ ?_, fun g ↦ ?_⟩
  · have hXfin : X.support.Finite :=
      (CategoryTheory.GradedObject.hasFiniteSupport_iff_finite X).mp hX.1
    have hYfin : Y.support.Finite :=
      (CategoryTheory.GradedObject.hasFiniteSupport_iff_finite Y).mp hY.1
    refine (CategoryTheory.GradedObject.hasFiniteSupport_iff_finite
      (XY : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R))).mpr
      ((hXfin.union hYfin).subset fun g hg ↦ ?_)
    by_contra hnot
    rw [Set.mem_union, not_or] at hnot
    have hzX : IsZero (X g) :=
      not_not.mp ((CategoryTheory.GradedObject.mem_support X g).not.mp hnot.1)
    have hzY : IsZero (Y g) :=
      not_not.mp ((CategoryTheory.GradedObject.mem_support Y g).not.mp hnot.2)
    have := ModuleCat.isZero_iff_subsingleton.mp hzX
    have := ModuleCat.isZero_iff_subsingleton.mp hzY
    have hzProd : IsZero (ModuleCat.of R (X g × Y g)) :=
      ModuleCat.isZero_iff_subsingleton.mpr inferInstance
    exact (CategoryTheory.GradedObject.mem_support
      (XY : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R)) g).mp hg
      ((isoProd g).isZero_iff.mpr hzProd)
  · have : Module.Finite R (ModuleCat.of R (X g × Y g)) :=
      inferInstanceAs (Module.Finite R (X g × Y g))
    exact Module.Finite.equiv (isoProd g).symm.toLinearEquiv
  · have : Module.Projective R (ModuleCat.of R (X g × Y g)) :=
      inferInstanceAs (Module.Projective R (X g × Y g))
    exact Module.Projective.of_equiv (isoProd g).symm.toLinearEquiv

/-- The defining object property of `VecTwisted` is closed under finite products, so
`VecTwisted R G c` inherits finite biproducts from `TwistedGradedObject c (ModuleCat.{u} R)`. -/
instance objects_isClosedUnderFiniteProducts :
    (objects R G c).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

section Monoidal

variable [DecidableEq G]

/-- Convolution and the unit preserve the finiteness and projectivity conditions defining
`VecTwisted`. -/
instance objects_isMonoidal : (objects R G c).IsMonoidal := by
  refine { prop_unit := ?_, prop_tensor := ?_ }
  · refine ⟨CategoryTheory.GradedObject.hasFiniteSupport_single 0 _,
      fun g ↦ ?_, fun g ↦ ?_⟩
    · exact CategoryTheory.GradedObject.finite_single_obj 0 (𝟙_ (ModuleCat R)) g
    · have : Module.Projective R (𝟙_ (ModuleCat.{u} R)) := Module.Projective.of_free
      exact CategoryTheory.GradedObject.projective_single_obj 0 (𝟙_ (ModuleCat R)) g
  · intro X Y hX hY
    have := hX.2.1
    have := hX.2.2
    have := hY.2.1
    have := hY.2.2
    exact ⟨hX.1.tensorObj hY.1,
      fun g ↦ hX.1.finite_tensorObj hY.1 g,
      fun g ↦ CategoryTheory.GradedObject.projective_tensorObj X Y g⟩

end Monoidal

/-- The fully faithful inclusion into all cocycle-twisted graded `R`-modules. -/
abbrev forget : VecTwisted R G c ⥤ TwistedGradedObject c (ModuleCat.{u} R) :=
  (objects R G c).ι

variable {c}

/-- The underlying graded module of an object of `VecTwisted` has finite support. -/
theorem hasFiniteSupport (X : VecTwisted R G c) :
    CategoryTheory.GradedObject.HasFiniteSupport X.obj :=
  X.property.1

/-- Every homogeneous component is a finitely generated `R`-module. -/
instance finite_component (X : VecTwisted R G c) (g : Additive G) :
    Module.Finite R (X.obj g) :=
  X.property.2.1 g

/-- Every homogeneous component is a projective `R`-module. -/
instance projective_component (X : VecTwisted R G c) (g : Additive G) :
    Module.Projective R (X.obj g) :=
  X.property.2.2 g

/-- Form an object of `VecTwisted` from a finitely supported graded `R`-module with finitely
generated projective components. -/
def of (X : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R))
    (hX : X.HasFiniteSupport) [∀ g, Module.Finite R (X g)] [∀ g, Module.Projective R (X g)] :
    VecTwisted R G c :=
  ⟨X, hX, inferInstance, inferInstance⟩

@[simp]
theorem of_obj (X : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R))
    (hX : X.HasFiniteSupport) [∀ g, Module.Finite R (X g)] [∀ g, Module.Projective R (X g)] :
    (of (c := c) X hX).obj = X :=
  (rfl)

section SingleDelta

variable [DecidableEq G]

/-- The underlying graded object of the tensor unit in `VecTwisted R G c` is
`GradedObject.Monoidal.tensorUnit`. -/
theorem tensorUnit_obj :
    (𝟙_ (VecTwisted R G c)).obj =
      (CategoryTheory.GradedObject.Monoidal.tensorUnit :
        CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R)) :=
  rfl

/-- The underlying graded object of a tensor product in `VecTwisted R G c` is the convolution
tensor product of graded objects. -/
theorem tensorObj_obj (X Y : VecTwisted R G c) :
    (X ⊗ Y).obj = CategoryTheory.GradedObject.Monoidal.tensorObj X.obj Y.obj :=
  rfl

/-- A finitely generated projective `R`-module concentrated in degree `g`. -/
def single (g : G) (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Projective R M] :
    VecTwisted R G c := by
  letI (i : Additive G) := CategoryTheory.GradedObject.finite_single_obj (Additive.ofMul g) M i
  letI (i : Additive G) := CategoryTheory.GradedObject.projective_single_obj (Additive.ofMul g) M i
  exact of ((CategoryTheory.GradedObject.single (Additive.ofMul g)).obj M)
    (CategoryTheory.GradedObject.hasFiniteSupport_single _ _)

@[simp]
theorem single_obj (g : G) (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Projective R M] :
    (single (c := c) g M).obj =
      (CategoryTheory.GradedObject.single (Additive.ofMul g)).obj M :=
  (rfl)

/-- The canonical isomorphism between the degree-`g` component of `single g M` and `M`. -/
def singleEvalIso (g : G) (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Projective R M] :
    (single (c := c) g M).obj (Additive.ofMul g) ≅ M :=
  (eqToIso (congrFun (single_obj (c := c) g M) (Additive.ofMul g))).trans
    (CategoryTheory.GradedObject.singleObjApplyIso (Additive.ofMul g) M)

/-- Functorial action of `single g` on morphisms between finitely generated projective modules. -/
def singleMap (g : G) {M N : ModuleCat.{u} R} [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] (f : M ⟶ N) :
    single (c := c) g M ⟶ single (c := c) g N :=
  ObjectProperty.homMk
    ((CategoryTheory.GradedObject.single (Additive.ofMul g)).map f)

@[simp]
theorem singleMap_id (g : G) (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Projective R M] :
    singleMap (c := c) g (𝟙 M) = 𝟙 (single (c := c) g M) := by
  apply ObjectProperty.hom_ext
  exact (CategoryTheory.GradedObject.single (Additive.ofMul g)).map_id M

@[simp]
theorem singleMap_comp (g : G) {M N P : ModuleCat.{u} R}
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    [Module.Finite R P] [Module.Projective R P]
    (f : M ⟶ N) (h : N ⟶ P) :
    singleMap (c := c) g (f ≫ h) = singleMap g f ≫ singleMap g h := by
  apply ObjectProperty.hom_ext
  exact (CategoryTheory.GradedObject.single (Additive.ofMul g)).map_comp f h

@[simp]
theorem singleMap_zero (g : G) (M N : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] :
    singleMap (c := c) g (0 : M ⟶ N) = 0 := by
  apply ObjectProperty.hom_ext
  exact (CategoryTheory.GradedObject.single (C := ModuleCat.{u} R) (Additive.ofMul g)).map_zero M N

@[simp]
theorem singleMap_add (g : G) {M N : ModuleCat.{u} R}
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f₁ f₂ : M ⟶ N) :
    singleMap (c := c) g (f₁ + f₂) = singleMap g f₁ + singleMap g f₂ := by
  apply ObjectProperty.hom_ext
  exact (CategoryTheory.GradedObject.single (Additive.ofMul g)).map_add

@[simp]
theorem singleMap_smul (g : G) {M N : ModuleCat.{u} R}
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (r : R) (f : M ⟶ N) :
    singleMap (c := c) g (r • f) = r • singleMap g f := by
  apply ObjectProperty.hom_ext
  exact (CategoryTheory.GradedObject.single (Additive.ofMul g)).map_smul r f

theorem singleMap_sum {ι : Type*} (s : Finset ι) (g : G) {M N : ModuleCat.{u} R}
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : ι → (M ⟶ N)) :
    singleMap (c := c) g (∑ i ∈ s, f i) = ∑ i ∈ s, singleMap g (f i) := by
  apply ObjectProperty.hom_ext
  -- `ObjectProperty.ι` is additive so `.hom` commutes with finite sums.
  change (CategoryTheory.GradedObject.single (Additive.ofMul g)).map (∑ i ∈ s, f i) =
    (objects R G c).ι.map (∑ i ∈ s, singleMap (c := c) g (f i))
  rw [Functor.map_sum, Functor.map_sum]
  rfl

/-- A nonzero finitely generated projective module concentrated in degree `g` has singleton
support. -/
theorem support_single (g : G) (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Projective R M]
    (hM : ¬ IsZero M) : (single (c := c) g M).obj.support = {Additive.ofMul g} := by
  rw [single_obj]
  exact CategoryTheory.GradedObject.support_single _ M hM

/-- The free rank-one graded `R`-module concentrated in degree `g`. -/
def delta (g : G) : VecTwisted R G c :=
  single g (ModuleCat.of R R)

/-- The underlying graded module of `δ_g` is the single-degree copy of `R`. -/
@[simp]
theorem delta_obj (g : G) : (delta (c := c) g).obj =
    (CategoryTheory.GradedObject.single (Additive.ofMul g)).obj (ModuleCat.of R R) :=
  (rfl)

/-- The canonical isomorphism between the degree-`g` component of `delta g` and `R`. -/
def deltaEvalIso (g : G) : (delta (c := c) g).obj (Additive.ofMul g) ≅ ModuleCat.of R R :=
  (eqToIso (congrFun (delta_obj (c := c) g) (Additive.ofMul g))).trans
    (CategoryTheory.GradedObject.singleObjApplyIso (Additive.ofMul g) (ModuleCat.of R R))

/-- Over a nontrivial ring `R`, the support of `δ_g` is exactly `{g}`; in particular these objects
are nonzero even when the grading monoid is infinite. -/
theorem support_delta [Nontrivial R] (g : G) :
    (delta (c := c) g).obj.support = {Additive.ofMul g} := by
  apply support_single
  intro hz
  have := ModuleCat.isZero_iff_subsingleton.mp hz
  exact zero_ne_one (Subsingleton.elim (0 : R) 1)

/-- Morphisms out of `single g M` correspond `R`-linearly to morphisms out of `M` into the
degree-`g` component of `X`. -/
def singleHomEquiv (g : G) (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Projective R M]
    (X : VecTwisted R G c) :
    (single (c := c) g M ⟶ X) ≃ₗ[R] (M ⟶ X.obj (Additive.ofMul g)) where
  toFun f := (CategoryTheory.GradedObject.singleAdjEval (Additive.ofMul g)).homEquiv M X.obj f.hom
  invFun φ := ObjectProperty.homMk
    (((CategoryTheory.GradedObject.singleAdjEval (Additive.ofMul g)).homEquiv M X.obj).symm φ)
  left_inv f := ObjectProperty.hom_ext _ (((CategoryTheory.GradedObject.singleAdjEval
    (Additive.ofMul g)).homEquiv M X.obj).left_inv f.hom)
  right_inv φ := ((CategoryTheory.GradedObject.singleAdjEval
    (Additive.ofMul g)).homEquiv M X.obj).right_inv φ
  map_add' f₁ f₂ := by
    let X' : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) := X.obj
    let g₁ : (CategoryTheory.GradedObject.single (Additive.ofMul g)).obj M ⟶ X' := f₁.hom
    let g₂ : (CategoryTheory.GradedObject.single (Additive.ofMul g)).obj M ⟶ X' := f₂.hom
    -- Morphism addition in `VecTwisted` is computed in `GradedObject`.
    change (CategoryTheory.GradedObject.singleAdjEval
        (Additive.ofMul g)).homEquiv M X' (g₁ + g₂) =
      (CategoryTheory.GradedObject.singleAdjEval (Additive.ofMul g)).homEquiv M X' g₁ +
        (CategoryTheory.GradedObject.singleAdjEval (Additive.ofMul g)).homEquiv M X' g₂
    rw [CategoryTheory.GradedObject.singleAdjEval_homEquiv_apply,
      CategoryTheory.GradedObject.singleAdjEval_homEquiv_apply,
      CategoryTheory.GradedObject.singleAdjEval_homEquiv_apply,
      CategoryTheory.GradedObject.add_apply, Preadditive.comp_add]
  map_smul' r f := by
    let X' : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) := X.obj
    let g₁ : (CategoryTheory.GradedObject.single (Additive.ofMul g)).obj M ⟶ X' := f.hom
    -- Scalar multiplication in `VecTwisted` is computed in `GradedObject`.
    change (CategoryTheory.GradedObject.singleAdjEval
        (Additive.ofMul g)).homEquiv M X' (r • g₁) =
      r • (CategoryTheory.GradedObject.singleAdjEval (Additive.ofMul g)).homEquiv M X' g₁
    rw [CategoryTheory.GradedObject.singleAdjEval_homEquiv_apply,
      CategoryTheory.GradedObject.singleAdjEval_homEquiv_apply,
      CategoryTheory.GradedObject.smul_apply, Linear.comp_smul]

/-- `singleHomEquiv` evaluates a morphism at degree `g` and precomposes with
`(singleEvalIso g M).inv`. -/
@[simp]
theorem singleHomEquiv_apply (g : G) (M : ModuleCat.{u} R) [Module.Finite R M]
    [Module.Projective R M] (X : VecTwisted R G c) (f : single (c := c) g M ⟶ X) :
    singleHomEquiv g M X f = (singleEvalIso (c := c) g M).inv ≫ f.hom (Additive.ofMul g) := by
  change (CategoryTheory.GradedObject.singleAdjEval (Additive.ofMul g)).homEquiv M X.obj f.hom =
    (CategoryTheory.GradedObject.singleObjApplyIso (Additive.ofMul g) M).inv ≫
      f.hom (Additive.ofMul g)
  exact CategoryTheory.GradedObject.singleAdjEval_homEquiv_apply _ f.hom

/-- The inverse of `singleHomEquiv` evaluated in degree `g` is `(singleEvalIso g M).hom ≫ φ`. -/
@[simp]
theorem singleHomEquiv_symm_apply_self (g : G) (M : ModuleCat.{u} R) [Module.Finite R M]
    [Module.Projective R M] (X : VecTwisted R G c) (φ : M ⟶ X.obj (Additive.ofMul g)) :
    ((singleHomEquiv (c := c) g M X).symm φ).hom (Additive.ofMul g) =
      (singleEvalIso (c := c) g M).hom ≫ φ := by
  change ((CategoryTheory.GradedObject.singleAdjEval (Additive.ofMul g)).homEquiv M X.obj).symm
      φ (Additive.ofMul g) =
    (CategoryTheory.GradedObject.singleObjApplyIso (Additive.ofMul g) M).hom ≫ φ
  exact CategoryTheory.GradedObject.singleAdjEval_homEquiv_symm_apply_self _ φ

/-- Morphisms `delta g ⟶ X` correspond `R`-linearly to elements of the degree-`g` component of
`X`, by evaluating the corresponding map `R → X.obj (Additive.ofMul g)` at `1`. -/
def deltaHomEquiv (g : G) (X : VecTwisted R G c) :
    (delta (c := c) g ⟶ X) ≃ₗ[R] X.obj (Additive.ofMul g) :=
  (singleHomEquiv g (ModuleCat.of R R) X).trans
    ({ toFun := fun φ ↦ φ (1 : R)
       invFun := fun x ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x)
       left_inv := fun φ ↦ by
         ext : 1
         apply LinearMap.ext_ring
         simp
       right_inv := fun x ↦ by simp
       map_add' := fun _ _ ↦ rfl
       map_smul' := fun _ _ ↦ rfl })

/-- `deltaHomEquiv` evaluates `(deltaEvalIso g).inv ≫ f.hom (Additive.ofMul g)` at `1 : R`. -/
@[simp]
theorem deltaHomEquiv_apply (g : G) (X : VecTwisted R G c) (f : delta (c := c) g ⟶ X) :
    deltaHomEquiv g X f =
      ((deltaEvalIso (c := c) g).inv ≫ f.hom (Additive.ofMul g)) (1 : R) :=
  congrArg (fun φ : ModuleCat.of R R ⟶ X.obj (Additive.ofMul g) ↦ φ (1 : R))
    (singleHomEquiv_apply (c := c) g (ModuleCat.of R R) X f)

/-- The structure map `R → End (delta g)` sending `r` to `r • 𝟙 (delta g)` is bijective over
every commutative ring `R` (including the zero ring). -/
theorem bijective_algebraMap_end_delta (g : G) :
    Function.Bijective (algebraMap R (End (delta (c := c) g))) := by
  let e : (delta (c := c) g).obj (Additive.ofMul g) ≅ ModuleCat.of R R := deltaEvalIso g
  let ev : End (delta (c := c) g) → R :=
    fun f ↦ (e.inv ≫ f.asHom.hom (Additive.ofMul g) ≫ e.hom) 1
  refine Function.bijective_iff_has_inverse.mpr ⟨ev, fun r ↦ ?_, fun f ↦ ?_⟩
  · have hcomp : (algebraMap R (End (delta (c := c) g)) r).asHom.hom (Additive.ofMul g) =
        r • 𝟙 ((delta (c := c) g).obj (Additive.ofMul g)) := by
      rw [End.algebraMap_asHom, ObjectProperty.smul_hom]
      rfl
    have h : e.inv ≫ (algebraMap R (End (delta (c := c) g)) r).asHom.hom (Additive.ofMul g) ≫
        e.hom = r • 𝟙 (ModuleCat.of R R) := by
      rw [hcomp, Linear.smul_comp, Linear.comp_smul, Category.id_comp, Iso.inv_hom_id]
    -- Apply `ev` as evaluation at `1 : R` after simplifying the morphism composition.
    change (e.inv ≫ _ ≫ e.hom) (1 : R) = r
    rw [h]
    simp
  · refine End.ext (ObjectProperty.hom_ext _ (funext fun i ↦ ?_))
    have hcomp : (algebraMap R (End (delta (c := c) g)) (ev f)).asHom.hom i =
        ev f • 𝟙 ((delta (c := c) g).obj i) := by
      rw [End.algebraMap_asHom, ObjectProperty.smul_hom]
      rfl
    rw [hcomp]
    by_cases h : i = Additive.ofMul g
    · subst i
      rw [← cancel_epi e.inv, ← cancel_mono e.hom]
      simp only [Category.assoc, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
        Iso.inv_hom_id]
      ext : 1
      apply LinearMap.ext_ring
      -- Both sides evaluate at `1 : R` to `ev f`.
      change (ev f • 𝟙 (ModuleCat.of R R)) (1 : R) = ev f
      simp
    · exact (CategoryTheory.GradedObject.isInitialSingleObjApply
        (Additive.ofMul g) (ModuleCat.of R R) i h).hom_ext _ _

/-- The endomorphism `R`-algebra of `delta g` is canonically isomorphic to `R`, inverse to the
structure map `r ↦ r • 𝟙 (delta g)`. -/
def endDeltaAlgEquiv (g : G) : End (delta (c := c) g) ≃ₐ[R] R :=
  (AlgEquiv.ofBijective (Algebra.ofId R (End (delta (c := c) g))) <| by
    have h : ⇑(Algebra.ofId R (End (delta (c := c) g))) = algebraMap R _ :=
      funext (Algebra.ofId_apply _)
    rw [h]
    exact bijective_algebraMap_end_delta g).symm

/-- The inverse of `endDeltaAlgEquiv` is the structure map `algebraMap R (End (delta g))`. -/
@[simp]
theorem endDeltaAlgEquiv_symm_apply (g : G) (r : R) :
    (endDeltaAlgEquiv (c := c) g).symm r = algebraMap R (End (delta (c := c) g)) r := by
  rw [endDeltaAlgEquiv, AlgEquiv.symm_symm, AlgEquiv.ofBijective_apply, Algebra.ofId_apply]

/-- Every endomorphism of `delta g` is its scalar times the identity. -/
@[simp]
theorem endDeltaAlgEquiv_smul_id (g : G) (f : End (delta (c := c) g)) :
    endDeltaAlgEquiv (c := c) g f • 𝟙 (delta (c := c) g) = f.asHom := by
  rw [← End.algebraMap_asHom, ← endDeltaAlgEquiv_symm_apply, AlgEquiv.symm_apply_apply]

/-- The scalar extracted by `endDeltaAlgEquiv` is obtained by transporting `f` along
`deltaEvalIso` and evaluating at `1 : R`. -/
theorem endDeltaAlgEquiv_apply (g : G) (f : End (delta (c := c) g)) :
    endDeltaAlgEquiv (c := c) g f =
      ((deltaEvalIso (c := c) g).inv ≫ f.asHom.hom (Additive.ofMul g) ≫
        (deltaEvalIso (c := c) g).hom) (1 : R) := by
  have hf : f.asHom.hom (Additive.ofMul g) =
      endDeltaAlgEquiv (c := c) g f • 𝟙 ((delta (c := c) g).obj (Additive.ofMul g)) := by
    have h := congrFun (congrArg InducedCategory.Hom.hom (endDeltaAlgEquiv_smul_id g f).symm)
      (Additive.ofMul g)
    rw [ObjectProperty.smul_hom] at h
    exact h
  have h : (deltaEvalIso (c := c) g).inv ≫ f.asHom.hom (Additive.ofMul g) ≫
      (deltaEvalIso (c := c) g).hom =
      endDeltaAlgEquiv (c := c) g f • 𝟙 (ModuleCat.of R R) := by
    rw [hf, Linear.smul_comp, Linear.comp_smul, Category.id_comp, Iso.inv_hom_id]
  rw [h]
  simp

/-- The family `delta : G → VecTwisted R G c` is hom-orthogonal: there is at most one morphism
between `delta g` and `delta h` for `g ≠ h`. -/
theorem homOrthogonal_delta : HomOrthogonal (delta (c := c)) := by
  intro g h hne
  have hne' : Additive.ofMul g ≠ Additive.ofMul h := fun heq ↦
    hne (Additive.ofMul.injective heq)
  have hz : IsZero ((delta (c := c) h).obj (Additive.ofMul g)) :=
    (CategoryTheory.GradedObject.isInitialSingleObjApply
      (Additive.ofMul h) (ModuleCat.of R R) (Additive.ofMul g) hne').isZero
  have := ModuleCat.isZero_iff_subsingleton.mp hz
  exact (deltaHomEquiv g (delta (c := c) h)).toEquiv.subsingleton

/-! ### Monoidal calculus on `delta` -/

/-- The tensor unit of `VecTwisted R G c` is canonically isomorphic to `delta 1`. -/
def deltaOneIso : 𝟙_ (VecTwisted R G c) ≅ delta (c := c) 1 :=
  (objects R G c).isoMk (Iso.refl _)

@[simp]
theorem deltaOneIso_hom_hom :
    (deltaOneIso (c := c)).hom.hom =
      eqToHom ((tensorUnit_obj (c := c)).trans (delta_obj (c := c) 1).symm) :=
  (rfl)

@[simp]
theorem deltaOneIso_inv_hom :
    (deltaOneIso (c := c)).inv.hom =
      eqToHom ((delta_obj (c := c) 1).trans (tensorUnit_obj (c := c)).symm) :=
  (rfl)

/-- The tensor product `delta g ⊗ delta h` is canonically isomorphic to `delta (g * h)`. -/
def deltaTensorIso (g h : G) :
    delta (c := c) g ⊗ delta (c := c) h ≅ delta (c := c) (g * h) :=
  (objects R G c).isoMk
    ((CategoryTheory.GradedObject.Monoidal.singleTensorIso
        (Additive.ofMul g) (Additive.ofMul h) (ModuleCat.of R R) (ModuleCat.of R R)).trans
      ((CategoryTheory.GradedObject.single (Additive.ofMul (g * h))).mapIso
        (λ_ (𝟙_ (ModuleCat.{u} R)))))

/-- The underlying graded morphism of `deltaTensorIso g h` is `singleTensorIso` composed with the
left unitor on `𝟙_ (ModuleCat R)`. -/
theorem deltaTensorIso_hom_hom (g h : G) :
    (deltaTensorIso (c := c) g h).hom.hom =
      eqToHom (by rw [tensorObj_obj, delta_obj, delta_obj]) ≫
        (CategoryTheory.GradedObject.Monoidal.singleTensorIso
            (Additive.ofMul g) (Additive.ofMul h) (ModuleCat.of R R) (ModuleCat.of R R)).hom ≫
        (CategoryTheory.GradedObject.single (Additive.ofMul (g * h))).map
          (λ_ (𝟙_ (ModuleCat.{u} R))).hom ≫
        eqToHom (delta_obj (c := c) (g * h)).symm := by
  -- Both `eqToHom` factors are identities because `delta_obj` and `tensorObj_obj` hold by `rfl`.
  change (CategoryTheory.GradedObject.Monoidal.singleTensorIso
        (Additive.ofMul g) (Additive.ofMul h) (ModuleCat.of R R) (ModuleCat.of R R)).hom ≫
      (CategoryTheory.GradedObject.single (Additive.ofMul (g * h))).map
        (λ_ (𝟙_ (ModuleCat.{u} R))).hom =
    eqToHom (rfl : _ = _) ≫ _ ≫ _ ≫ eqToHom (rfl : _ = _)
  simp

/-- Left unit normalization of `deltaTensorIso`: composing `deltaOneIso ▷ delta h` with
`deltaTensorIso 1 h` recovers the left unitor `λ_ (delta h)`. -/
theorem deltaTensorIso_one_left (h : G) :
    (deltaOneIso (c := c)).hom ▷ delta h ≫ (deltaTensorIso 1 h).hom ≫
        eqToHom (congrArg (delta (c := c)) (one_mul h)) =
      (λ_ (delta (c := c) h)).hom := by
  apply ObjectProperty.hom_ext
  let U : ModuleCat.{u} R := 𝟙_ (ModuleCat.{u} R)
  have heq_fn : ∀ {x y : G} (e : x = y),
      (eqToHom (congrArg (delta (c := c)) e)).hom =
        (eqToHom (congrArg (fun k ↦ (CategoryTheory.GradedObject.single k).obj U)
            (congrArg Additive.ofMul e)) :
          (CategoryTheory.GradedObject.single (Additive.ofMul x)).obj U ⟶
            (CategoryTheory.GradedObject.single (Additive.ofMul y)).obj U) :=
    fun {x y} e ↦ by subst e; rfl
  have hgoal :
      CategoryTheory.GradedObject.Monoidal.whiskerRight
          (𝟙 ((CategoryTheory.GradedObject.single (0 : Additive G)).obj U))
          ((CategoryTheory.GradedObject.single (Additive.ofMul h)).obj U) ≫
        ((CategoryTheory.GradedObject.Monoidal.singleTensorIso 0 (Additive.ofMul h) U U).hom ≫
          (CategoryTheory.GradedObject.single (0 + Additive.ofMul h)).map (λ_ U).hom) ≫
        eqToHom (congrArg (fun k ↦ (CategoryTheory.GradedObject.single k).obj U)
          (zero_add (Additive.ofMul h))) =
      (CategoryTheory.GradedObject.Monoidal.leftUnitor
        ((CategoryTheory.GradedObject.single (Additive.ofMul h)).obj U)).hom := by
    rw [CategoryTheory.GradedObject.Monoidal.whiskerRight,
      CategoryTheory.GradedObject.Monoidal.id_tensorHom_id, Category.id_comp, Category.assoc]
    exact CategoryTheory.GradedObject.Monoidal.singleTensorIso_leftUnitor (Additive.ofMul h) U
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [heq_fn (one_mul h)]
  exact hgoal

/-- Right unit normalization of `deltaTensorIso`: composing `delta g ◁ deltaOneIso` with
`deltaTensorIso g 1` recovers the right unitor `ρ_ (delta g)`. -/
theorem deltaTensorIso_one_right (g : G) :
    delta (c := c) g ◁ (deltaOneIso (c := c)).hom ≫ (deltaTensorIso g 1).hom ≫
        eqToHom (congrArg (delta (c := c)) (mul_one g)) =
      (ρ_ (delta (c := c) g)).hom := by
  apply ObjectProperty.hom_ext
  let U : ModuleCat.{u} R := 𝟙_ (ModuleCat.{u} R)
  have heq_fn : ∀ {x y : G} (e : x = y),
      (eqToHom (congrArg (delta (c := c)) e)).hom =
        (eqToHom (congrArg (fun k ↦ (CategoryTheory.GradedObject.single k).obj U)
            (congrArg Additive.ofMul e)) :
          (CategoryTheory.GradedObject.single (Additive.ofMul x)).obj U ⟶
            (CategoryTheory.GradedObject.single (Additive.ofMul y)).obj U) :=
    fun {x y} e ↦ by subst e; rfl
  have hgoal :
      CategoryTheory.GradedObject.Monoidal.whiskerLeft
          ((CategoryTheory.GradedObject.single (Additive.ofMul g)).obj U)
          (𝟙 ((CategoryTheory.GradedObject.single (0 : Additive G)).obj U)) ≫
        ((CategoryTheory.GradedObject.Monoidal.singleTensorIso (Additive.ofMul g) 0 U U).hom ≫
          (CategoryTheory.GradedObject.single (Additive.ofMul g + 0)).map (λ_ U).hom) ≫
        eqToHom (congrArg (fun k ↦ (CategoryTheory.GradedObject.single k).obj U)
          (add_zero (Additive.ofMul g))) =
      (CategoryTheory.GradedObject.Monoidal.rightUnitor
        ((CategoryTheory.GradedObject.single (Additive.ofMul g)).obj U)).hom := by
    rw [CategoryTheory.GradedObject.Monoidal.whiskerLeft,
      CategoryTheory.GradedObject.Monoidal.id_tensorHom_id, Category.id_comp, Category.assoc,
      MonoidalCategory.unitors_equal]
    exact CategoryTheory.GradedObject.Monoidal.singleTensorIso_rightUnitor
      (Additive.ofMul g) (𝟙_ (ModuleCat.{u} R))
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [heq_fn (mul_one g)]
  exact hgoal

/-- The associator of `VecTwisted R G c` acts on `(delta g ⊗ delta h) ⊗ delta l` by the cocycle
scalar `c.ω (Additive.ofMul g) (Additive.ofMul h) (Additive.ofMul l)`. -/
theorem associator_hom_delta (g h l : G) :
    (α_ (delta (c := c) g) (delta h) (delta l)).hom ≫
        delta g ◁ (deltaTensorIso h l).hom ≫
        (deltaTensorIso g (h * l)).hom ≫
        eqToHom (congrArg (delta (c := c)) (mul_assoc g h l).symm) =
      (c.ω (Additive.ofMul g) (Additive.ofMul h) (Additive.ofMul l) : R) •
        ((deltaTensorIso g h).hom ▷ delta l ≫ (deltaTensorIso (g * h) l).hom) := by
  apply ObjectProperty.hom_ext
  set i := Additive.ofMul g
  set j := Additive.ofMul h
  set k := Additive.ofMul l
  set U := 𝟙_ (ModuleCat.{u} R)
  have heq_fn : ∀ {x y : G} (e : x = y),
      (eqToHom (congrArg (delta (c := c)) e)).hom =
        (eqToHom (congrArg (fun m ↦ (CategoryTheory.GradedObject.single m).obj U)
            (congrArg Additive.ofMul e)) :
          (CategoryTheory.GradedObject.single (Additive.ofMul x)).obj U ⟶
            (CategoryTheory.GradedObject.single (Additive.ofMul y)).obj U) :=
    fun {x y} e ↦ by subst e; rfl
  have hnat_eq : ∀ {A B : ModuleCat.{u} R} (f : A ⟶ B) {m n : Additive G} (e : m = n),
      (CategoryTheory.GradedObject.single m).map f ≫
          eqToHom (congrArg (fun t ↦ (CategoryTheory.GradedObject.single t).obj B) e) =
        eqToHom (congrArg (fun t ↦ (CategoryTheory.GradedObject.single t).obj A) e) ≫
          (CategoryTheory.GradedObject.single n).map f := by
    intro A B f m n e; subst e; simp
  have hwl : ∀ {Y₁ Y₂ Y₃ : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R)}
      (f : Y₁ ⟶ Y₂) (f' : Y₂ ⟶ Y₃),
      CategoryTheory.GradedObject.Monoidal.whiskerLeft
          ((CategoryTheory.GradedObject.single i).obj U) (f ≫ f') =
        CategoryTheory.GradedObject.Monoidal.whiskerLeft
            ((CategoryTheory.GradedObject.single i).obj U) f ≫
          CategoryTheory.GradedObject.Monoidal.whiskerLeft
            ((CategoryTheory.GradedObject.single i).obj U) f' := fun f f' ↦
    @MonoidalCategory.whiskerLeft_comp (TwistedGradedObject c (ModuleCat.{u} R)) _ _
      ((CategoryTheory.GradedObject.single i).obj U) _ _ _ f f'
  have hwr : ∀ {X₁ X₂ X₃ : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R)}
      (f : X₁ ⟶ X₂) (f' : X₂ ⟶ X₃),
      CategoryTheory.GradedObject.Monoidal.whiskerRight (f ≫ f')
          ((CategoryTheory.GradedObject.single k).obj U) =
        CategoryTheory.GradedObject.Monoidal.whiskerRight f
            ((CategoryTheory.GradedObject.single k).obj U) ≫
          CategoryTheory.GradedObject.Monoidal.whiskerRight f'
            ((CategoryTheory.GradedObject.single k).obj U) := fun f f' ↦
    @MonoidalCategory.comp_whiskerRight (TwistedGradedObject c (ModuleCat.{u} R)) _ _ _ _ _
      f f' ((CategoryTheory.GradedObject.single k).obj U)
  have hgoal :
      (CategoryTheory.GradedObject.Monoidal.twistedAssociator c.ω
          ((CategoryTheory.GradedObject.single i).obj U)
          ((CategoryTheory.GradedObject.single j).obj U)
          ((CategoryTheory.GradedObject.single k).obj U)).hom ≫
        CategoryTheory.GradedObject.Monoidal.whiskerLeft
          ((CategoryTheory.GradedObject.single i).obj U)
          ((CategoryTheory.GradedObject.Monoidal.singleTensorIso j k U U).hom ≫
            (CategoryTheory.GradedObject.single (j + k)).map (λ_ U).hom) ≫
        ((CategoryTheory.GradedObject.Monoidal.singleTensorIso i (j + k) U U).hom ≫
          (CategoryTheory.GradedObject.single (i + (j + k))).map (λ_ U).hom) ≫
        eqToHom (congrArg (fun m ↦ (CategoryTheory.GradedObject.single m).obj U)
          (add_assoc i j k).symm) =
      (c.ω i j k : R) •
        (CategoryTheory.GradedObject.Monoidal.whiskerRight
            ((CategoryTheory.GradedObject.Monoidal.singleTensorIso i j U U).hom ≫
              (CategoryTheory.GradedObject.single (i + j)).map (λ_ U).hom)
            ((CategoryTheory.GradedObject.single k).obj U) ≫
          (CategoryTheory.GradedObject.Monoidal.singleTensorIso (i + j) k U U).hom ≫
          (CategoryTheory.GradedObject.single (i + j + k)).map (λ_ U).hom) := by
    rw [hwl, Category.assoc, Category.assoc,
      CategoryTheory.GradedObject.Monoidal.whiskerLeft_single_map_singleTensorIso_hom_assoc,
      ← Functor.map_comp_assoc, hnat_eq _ (add_assoc i j k).symm]
    have hassoc := CategoryTheory.GradedObject.Monoidal.singleTensorIso_twistedAssociator_hom
      c.ω i j k U U U
    have h1 := congrArg (· ≫ (CategoryTheory.GradedObject.single (i + j + k)).map
      ((U ◁ (λ_ U).hom) ≫ (λ_ U).hom)) hassoc
    simp only [Category.assoc, Linear.smul_comp, ← Functor.map_comp] at h1
    rw [h1]
    congr 1
    rw [hwr, Category.assoc,
      CategoryTheory.GradedObject.Monoidal.whiskerRight_single_map_singleTensorIso_hom_assoc,
      ← Functor.map_comp]
    congr 2
    rw [MonoidalCategory.triangle_assoc, MonoidalCategory.unitors_equal]
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.smul_hom]
  rw [heq_fn (mul_assoc g h l).symm]
  exact hgoal

/-! ### Biproduct decompositions -/

/-- Canonical inclusion of the degree-`g` component `single g (X.obj (Additive.ofMul g))` into
`X`. -/
def singleIncl (X : VecTwisted R G c) (g : G) :
    single (c := c) g (X.obj (Additive.ofMul g)) ⟶ X :=
  (singleHomEquiv g (X.obj (Additive.ofMul g)) X).symm (𝟙 _)

/-- Canonical projection from `X` onto its degree-`g` component
`single g (X.obj (Additive.ofMul g))`. -/
def singleProj (X : VecTwisted R G c) (g : G) :
    X ⟶ single (c := c) g (X.obj (Additive.ofMul g)) :=
  ObjectProperty.homMk fun i ↦
    if h : i = Additive.ofMul g then
      eqToHom (congrArg X.obj h) ≫
        (CategoryTheory.GradedObject.singleObjApplyIsoOfEq
          (Additive.ofMul g) (X.obj (Additive.ofMul g)) i h).inv
    else
      0

@[simp]
theorem singleIncl_hom_self (X : VecTwisted R G c) (g : G) :
    (singleIncl X g).hom (Additive.ofMul g) =
      (singleEvalIso (c := c) g (X.obj (Additive.ofMul g))).hom := by
  simp [singleIncl]

@[simp]
theorem singleProj_hom_self (X : VecTwisted R G c) (g : G) :
    (singleProj X g).hom (Additive.ofMul g) =
      (singleEvalIso (c := c) g (X.obj (Additive.ofMul g))).inv := by
  change (if h : Additive.ofMul g = Additive.ofMul g then
      eqToHom (congrArg X.obj h) ≫
        (CategoryTheory.GradedObject.singleObjApplyIsoOfEq
          (Additive.ofMul g) (X.obj (Additive.ofMul g)) (Additive.ofMul g) h).inv
    else 0) = (CategoryTheory.GradedObject.singleObjApplyIso
      (Additive.ofMul g) (X.obj (Additive.ofMul g))).inv
  simp [CategoryTheory.GradedObject.singleObjApplyIso]

@[simp]
theorem singleIncl_comp_singleProj_self (X : VecTwisted R G c) (g : G) :
    singleIncl X g ≫ singleProj X g = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  funext i
  by_cases h : i = Additive.ofMul g
  · subst i
    -- Composition of morphisms in `VecTwisted` is computed pointwise on degrees.
    change (singleIncl X g).hom (Additive.ofMul g) ≫
      (singleProj X g).hom (Additive.ofMul g) = 𝟙 _
    simp
  · exact (CategoryTheory.GradedObject.isInitialSingleObjApply
      (Additive.ofMul g) (X.obj (Additive.ofMul g)) i h).hom_ext _ _

theorem singleIncl_comp_singleProj_ne (X : VecTwisted R G c) {g h : G} (hgh : g ≠ h) :
    singleIncl X g ≫ singleProj X h = 0 := by
  apply ObjectProperty.hom_ext
  funext i
  by_cases hi : i = Additive.ofMul g
  · subst i
    have hne : Additive.ofMul g ≠ Additive.ofMul h := fun heq ↦
      hgh (Additive.ofMul.injective heq)
    -- Composition of morphisms in `VecTwisted` is computed pointwise on degrees.
    change (singleIncl X g).hom (Additive.ofMul g) ≫ (singleProj X h).hom (Additive.ofMul g) = 0
    have h0 : (singleProj X h).hom (Additive.ofMul g) = 0 := by
      -- The defining `if` vanishes outside degree `h`.
      change (if h' : Additive.ofMul g = Additive.ofMul h then _ else 0) = 0
      simp [hne]
    rw [h0, Limits.comp_zero]
  · exact (CategoryTheory.GradedObject.isInitialSingleObjApply
      (Additive.ofMul g) (X.obj (Additive.ofMul g)) i hi).hom_ext _ _

/-- Every object of `VecTwisted R G c` is canonically isomorphic to the finite biproduct of its
single-degree components over any injective finite indexing family covering its support. -/
def isoBiproductSingle (X : VecTwisted R G c) {ι : Type*} [Finite ι] (f : ι → G)
    (hf : Function.Injective f)
    (hs : ∀ g, g ∉ Set.range f → IsZero (X.obj (Additive.ofMul g))) :
    X ≅ ⨁ fun i : ι ↦ single (c := c) (f i) (X.obj (Additive.ofMul (f i))) where
  hom := biproduct.lift fun i ↦ singleProj X (f i)
  inv := biproduct.desc fun i ↦ singleIncl X (f i)
  hom_inv_id := by
    classical
    have : Fintype ι := Fintype.ofFinite ι
    rw [biproduct.lift_desc]
    apply ObjectProperty.hom_ext
    let X' : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) := X.obj
    let f' (i : ι) : X' ⟶ X' := (singleProj X (f i) ≫ singleIncl X (f i)).hom
    have hsum : (∑ i : ι, singleProj X (f i) ≫ singleIncl X (f i)).hom =
        ∑ i : ι, f' i :=
      Functor.map_sum (objects R G c).ι
        (fun i : ι ↦ singleProj X (f i) ≫ singleIncl X (f i)) Finset.univ
    rw [hsum]
    funext d
    -- Applying `eval d` commutes with finite sums of graded morphisms.
    change (CategoryTheory.GradedObject.eval d).map (∑ i : ι, f' i) = 𝟙 (X' d)
    rw [Functor.map_sum]
    by_cases hmem : d.toMul ∈ Set.range f
    · obtain ⟨i₀, hi₀⟩ := hmem
      have hd : d = Additive.ofMul (f i₀) := by rw [hi₀]; rfl
      subst d
      rw [Finset.sum_eq_single i₀]
      · -- Evaluate the `i₀` summand at degree `f i₀`.
        change (singleProj X (f i₀)).hom (Additive.ofMul (f i₀)) ≫
          (singleIncl X (f i₀)).hom (Additive.ofMul (f i₀)) = 𝟙 _
        simp
      · intro i _ hne
        have hne' : Additive.ofMul (f i₀) ≠ Additive.ofMul (f i) := fun heq ↦
          hne (hf (Additive.ofMul.injective heq)).symm
        -- Off-diagonal summands vanish at degree `f i₀`.
        have h0 : (singleProj X (f i)).hom (Additive.ofMul (f i₀)) = 0 := by
          change (if h' : Additive.ofMul (f i₀) = Additive.ofMul (f i) then _ else 0) = 0
          simp [hne']
        change (singleProj X (f i)).hom (Additive.ofMul (f i₀)) ≫
          (singleIncl X (f i)).hom (Additive.ofMul (f i₀)) = 0
        rw [h0, Limits.zero_comp]
      · intro h; exact absurd (Finset.mem_univ i₀) h
    · exact (hs d.toMul hmem).eq_of_src _ _
  inv_hom_id := by
    classical
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    simp only [Category.assoc, biproduct.ι_desc_assoc, biproduct.lift_π, Category.comp_id]
    rw [biproduct.ι_π]
    by_cases hij : i = j
    · subst hij
      simp
    · simp only [hij, ↓reduceDIte]
      exact singleIncl_comp_singleProj_ne X (fun heq ↦ hij (hf heq))

/-- A single-degree object whose module component has a finite basis `b : Module.Basis ι R M`
splits as the biproduct of copies of `delta g` indexed by `ι`. -/
def singleIsoBiproductDelta {ι : Type*} [Finite ι] (g : G) (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Projective R M] (b : Module.Basis ι R M) :
    single (c := c) g M ≅ ⨁ fun (_ : ι) ↦ delta (c := c) g :=
  let p (i : ι) : single (c := c) g M ⟶ delta (c := c) g :=
    singleMap g (ModuleCat.ofHom (b.coord i))
  let q (i : ι) : delta (c := c) g ⟶ single (c := c) g M :=
    singleMap g (ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i)))
  { hom := biproduct.lift p
    inv := biproduct.desc q
    hom_inv_id := by
      classical
      have : Fintype ι := Fintype.ofFinite ι
      rw [biproduct.lift_desc]
      have hsum : ∑ i : ι, (ModuleCat.ofHom (b.coord i) ≫
          ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i))) = 𝟙 M := by
        apply ModuleCat.hom_ext
        ext m
        have hlin : (∑ i : ι, ModuleCat.ofHom (b.coord i) ≫
            ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i))).hom =
            ∑ i : ι, (ModuleCat.ofHom (b.coord i) ≫
              ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i))).hom :=
          map_sum ModuleCat.homAddEquiv _ Finset.univ
        rw [hlin, LinearMap.sum_apply]
        simp [LinearMap.toSpanSingleton_apply]
      have hmap : ∑ i : ι, p i ≫ q i = singleMap (c := c) g (𝟙 M) := by
        rw [← hsum, singleMap_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        exact (singleMap_comp g (ModuleCat.ofHom (b.coord i))
          (ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i)))).symm
      exact hmap.trans (singleMap_id g M)
    inv_hom_id := by
      classical
      apply biproduct.hom_ext'
      intro i
      apply biproduct.hom_ext
      intro j
      simp only [Category.assoc, biproduct.ι_desc_assoc, biproduct.lift_π, Category.comp_id]
      rw [biproduct.ι_π]
      have hcomp : q i ≫ p j =
          singleMap (c := c) g
            (ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i)) ≫
              ModuleCat.ofHom (b.coord j)) :=
        (singleMap_comp g (ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i)))
          (ModuleCat.ofHom (b.coord j))).symm
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceDIte, eqToHom_refl]
        have hid : ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i)) ≫
            ModuleCat.ofHom (b.coord i) = 𝟙 (ModuleCat.of R R) := by
          ext : 1
          apply LinearMap.ext_ring
          simp
        exact hcomp.trans (by rw [hid, singleMap_id]; rfl)
      · simp only [hij, ↓reduceDIte]
        have hzero : ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i)) ≫
            ModuleCat.ofHom (b.coord j) = 0 := by
          ext : 1
          apply LinearMap.ext_ring
          simp [Finsupp.single_eq_of_ne (Ne.symm hij)]
        exact hcomp.trans (by rw [hzero, singleMap_zero]; rfl) }

/-- Every object of `VecTwisted R G c` whose homogeneous components are free `R`-modules is
isomorphic to a finite biproduct of `delta` objects indexed by a finite type in `Type`. -/
theorem exists_iso_biproduct_delta_of_free (X : VecTwisted R G c)
    [∀ g, Module.Free R (X.obj g)] :
    ∃ (κ : Type) (_ : Fintype κ) (f : κ → G),
      Nonempty (X ≅ ⨁ (delta (c := c) ∘ f)) := by
  obtain ⟨s, hs⟩ :=
    (CategoryTheory.GradedObject.hasFiniteSupport_iff X.obj).mp X.hasFiniteSupport
  let e : ↥s ≃ Fin (Fintype.card ↥s) := Fintype.equivFin ↥s
  let g : Fin (Fintype.card ↥s) → G := fun i ↦ (e.symm i).1.toMul
  have hg_inj : Function.Injective g := fun i j hij ↦ by
    apply e.symm.injective
    apply Subtype.ext
    exact Additive.toMul.injective hij
  have hsupp : ∀ x : G, x ∉ Set.range g → IsZero (X.obj (Additive.ofMul x)) := by
    intro x hx
    apply hs
    intro hmem
    exact hx ⟨e ⟨Additive.ofMul x, hmem⟩, by simp [g]⟩
  have iso₁ : X ≅ ⨁ fun i : Fin (Fintype.card ↥s) ↦
      single (c := c) (g i) (X.obj (Additive.ofMul (g i))) :=
    isoBiproductSingle X g hg_inj hsupp
  let n : Fin (Fintype.card ↥s) → ℕ := fun i ↦
    Fintype.card (Module.Free.ChooseBasisIndex R (X.obj (Additive.ofMul (g i))))
  let b (i : Fin (Fintype.card ↥s)) :
      Module.Basis (Fin (n i)) R (X.obj (Additive.ofMul (g i))) :=
    (Module.Free.chooseBasis R (X.obj (Additive.ofMul (g i)))).reindex
      (Fintype.equivFin (Module.Free.ChooseBasisIndex R (X.obj (Additive.ofMul (g i)))))
  refine ⟨Σ i : Fin (Fintype.card ↥s), Fin (n i), inferInstance, fun p ↦ g p.1, ⟨?_⟩⟩
  refine iso₁.trans ?_
  refine (biproduct.mapIso fun i ↦ singleIsoBiproductDelta (g i) _ (b i)).trans ?_
  exact biproductBiproductIso (fun i ↦ Fin (n i)) (fun i _ ↦ delta (c := c) (g i))

end SingleDelta

/-! ### Gauge equivalences between cohomologous cocycles -/

section Gauge

variable {c d : GradedObject.TwistingCocycle (Additive G) R}

/-- The defining object property of `VecTwisted` is invariant under gauge equivalence. -/
theorem objects_inverseImage_gauge (g : GradedObject.TwistingCocycle.Gauge c d) :
    (objects R G d).inverseImage (g.equivalence (ModuleCat.{u} R)).functor = objects R G c := by
  ext X
  -- `g.equivalence.functor` is `g.functor`, which acts as the identity on graded modules.
  change objects R G d ((g.equivalence (ModuleCat.{u} R)).functor.obj X) ↔ objects R G c X
  rw [GradedObject.TwistingCocycle.Gauge.equivalence_functor]
  rfl

/-- A gauge transformation between normalized `3`-cocycles restricts to an equivalence between the
corresponding categories `VecTwisted R G c ≌ VecTwisted R G d`. -/
def gaugeEquivalence (g : GradedObject.TwistingCocycle.Gauge c d) :
    VecTwisted R G c ≌ VecTwisted R G d :=
  (g.equivalence (ModuleCat.{u} R)).congrFullSubcategory (objects_inverseImage_gauge g)

/-- The forward functor of `gaugeEquivalence` is additive. -/
instance gaugeEquivalence_functor_additive (g : GradedObject.TwistingCocycle.Gauge c d) :
    (gaugeEquivalence g).functor.Additive where
  map_add := ((g.equivalence (ModuleCat.{u} R)).congrFullSubcategory
    (objects_inverseImage_gauge g)).functor.map_add

/-- The inverse functor of `gaugeEquivalence` is additive. -/
instance gaugeEquivalence_inverse_additive (g : GradedObject.TwistingCocycle.Gauge c d) :
    (gaugeEquivalence g).inverse.Additive where
  map_add := ((g.equivalence (ModuleCat.{u} R)).congrFullSubcategory
    (objects_inverseImage_gauge g)).inverse.map_add

/-- The forward functor of `gaugeEquivalence` is `R`-linear. -/
instance gaugeEquivalence_functor_linear (g : GradedObject.TwistingCocycle.Gauge c d) :
    (gaugeEquivalence g).functor.Linear R where
  map_smul f r := ((g.equivalence (ModuleCat.{u} R)).congrFullSubcategory
    (objects_inverseImage_gauge g)).functor.map_smul r f

/-- The inverse functor of `gaugeEquivalence` is `R`-linear. -/
instance gaugeEquivalence_inverse_linear (g : GradedObject.TwistingCocycle.Gauge c d) :
    (gaugeEquivalence g).inverse.Linear R where
  map_smul f r := ((g.equivalence (ModuleCat.{u} R)).congrFullSubcategory
    (objects_inverseImage_gauge g)).inverse.map_smul r f

@[simp]
theorem gaugeEquivalence_functor_obj_obj (g : GradedObject.TwistingCocycle.Gauge c d)
    (X : VecTwisted R G c) :
    ((gaugeEquivalence g).functor.obj X).obj = X.obj := by
  -- Unfold `gaugeEquivalence` to apply `congrFullSubcategory_functor_obj_obj`.
  change (((g.equivalence (ModuleCat.{u} R)).congrFullSubcategory
    (objects_inverseImage_gauge g)).functor.obj X).obj = X.obj
  rw [Equivalence.congrFullSubcategory_functor_obj_obj,
    GradedObject.TwistingCocycle.Gauge.equivalence_functor]
  rfl

private theorem eqToHom_comp_mid {C : Type*} [Category* C]
    {A B E F X Y : C} (f : X ⟶ Y)
    (hAE : A = E) (hEX : E = X) (hYF : Y = F) (hFB : F = B) :
    eqToHom hAE ≫ (eqToHom hEX ≫ f ≫ eqToHom hYF) ≫ eqToHom hFB =
      eqToHom (hAE.trans hEX) ≫ f ≫ eqToHom (hYF.trans hFB) := by
  subst hAE hEX hYF hFB; simp

theorem gaugeEquivalence_functor_map_hom (g : GradedObject.TwistingCocycle.Gauge c d)
    {X Y : VecTwisted R G c} (f : X ⟶ Y) :
    ((gaugeEquivalence g).functor.map f).hom =
      eqToHom (gaugeEquivalence_functor_obj_obj g X) ≫ f.hom ≫
        eqToHom (gaugeEquivalence_functor_obj_obj g Y).symm := by
  let A : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) :=
    ((gaugeEquivalence g).functor.obj X).obj
  let B : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) :=
    ((gaugeEquivalence g).functor.obj Y).obj
  let E : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) :=
    (g.equivalence (ModuleCat.{u} R)).functor.obj X.obj
  let F : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) :=
    (g.equivalence (ModuleCat.{u} R)).functor.obj Y.obj
  let X' : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) := X.obj
  let Y' : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) := Y.obj
  have hAE : A = E := (g.equivalence (ModuleCat.{u} R)).congrFullSubcategory_functor_obj_obj
    (objects_inverseImage_gauge g) X
  have hFB : F = B := ((g.equivalence (ModuleCat.{u} R)).congrFullSubcategory_functor_obj_obj
    (objects_inverseImage_gauge g) Y).symm
  have hEX : E = X' := g.equivalence_functor_obj (ModuleCat.{u} R) X.obj
  have hYF : Y' = F := (g.equivalence_functor_obj (ModuleCat.{u} R) Y.obj).symm
  have h1 : (((gaugeEquivalence g).functor.map f).hom : A ⟶ B) =
      (eqToHom hAE : A ⟶ E) ≫
        ((g.equivalence (ModuleCat.{u} R)).functor.map f.hom : E ⟶ F) ≫
        (eqToHom hFB : F ⟶ B) :=
    (g.equivalence (ModuleCat.{u} R)).congrFullSubcategory_functor_map_hom
      (objects_inverseImage_gauge g) f
  have h2 : ((g.equivalence (ModuleCat.{u} R)).functor.map f.hom : E ⟶ F) =
      (eqToHom hEX : E ⟶ X') ≫ (f.hom : X' ⟶ Y') ≫ (eqToHom hYF : Y' ⟶ F) :=
    g.equivalence_functor_map (ModuleCat.{u} R) f.hom
  exact (h1.trans (congrArg (fun k : E ⟶ F ↦ eqToHom hAE ≫ k ≫ eqToHom hFB) h2)).trans
    (eqToHom_comp_mid (f.hom : X' ⟶ Y') hAE hEX hYF hFB)

@[simp]
theorem gaugeEquivalence_inverse_obj_obj (g : GradedObject.TwistingCocycle.Gauge c d)
    (X : VecTwisted R G d) :
    ((gaugeEquivalence g).inverse.obj X).obj = X.obj := by
  -- Unfold `gaugeEquivalence` to apply `congrFullSubcategory_inverse_obj_obj`.
  change (((g.equivalence (ModuleCat.{u} R)).congrFullSubcategory
    (objects_inverseImage_gauge g)).inverse.obj X).obj = X.obj
  rw [Equivalence.congrFullSubcategory_inverse_obj_obj,
    GradedObject.TwistingCocycle.Gauge.equivalence_inverse]
  rfl

theorem gaugeEquivalence_inverse_map_hom (g : GradedObject.TwistingCocycle.Gauge c d)
    {X Y : VecTwisted R G d} (f : X ⟶ Y) :
    ((gaugeEquivalence g).inverse.map f).hom =
      eqToHom (gaugeEquivalence_inverse_obj_obj g X) ≫ f.hom ≫
        eqToHom (gaugeEquivalence_inverse_obj_obj g Y).symm := by
  let A : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) :=
    ((gaugeEquivalence g).inverse.obj X).obj
  let B : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) :=
    ((gaugeEquivalence g).inverse.obj Y).obj
  let E : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) :=
    (g.equivalence (ModuleCat.{u} R)).inverse.obj X.obj
  let F : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) :=
    (g.equivalence (ModuleCat.{u} R)).inverse.obj Y.obj
  let X' : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) := X.obj
  let Y' : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) := Y.obj
  have hAE : A = E := (g.equivalence (ModuleCat.{u} R)).congrFullSubcategory_inverse_obj_obj
    (objects_inverseImage_gauge g) X
  have hFB : F = B := ((g.equivalence (ModuleCat.{u} R)).congrFullSubcategory_inverse_obj_obj
    (objects_inverseImage_gauge g) Y).symm
  have hEX : E = X' := g.equivalence_inverse_obj (ModuleCat.{u} R) X.obj
  have hYF : Y' = F := (g.equivalence_inverse_obj (ModuleCat.{u} R) Y.obj).symm
  have h1 : (((gaugeEquivalence g).inverse.map f).hom : A ⟶ B) =
      (eqToHom hAE : A ⟶ E) ≫
        ((g.equivalence (ModuleCat.{u} R)).inverse.map f.hom : E ⟶ F) ≫
        (eqToHom hFB : F ⟶ B) :=
    (g.equivalence (ModuleCat.{u} R)).congrFullSubcategory_inverse_map_hom
      (objects_inverseImage_gauge g) f
  have h2 : ((g.equivalence (ModuleCat.{u} R)).inverse.map f.hom : E ⟶ F) =
      (eqToHom hEX : E ⟶ X') ≫ (f.hom : X' ⟶ Y') ≫ (eqToHom hYF : Y' ⟶ F) :=
    g.equivalence_inverse_map (ModuleCat.{u} R) f.hom
  exact (h1.trans (congrArg (fun k : E ⟶ F ↦ eqToHom hAE ≫ k ≫ eqToHom hFB) h2)).trans
    (eqToHom_comp_mid (f.hom : X' ⟶ Y') hAE hEX hYF hFB)

variable [DecidableEq G]

/-- The forward functor of `gaugeEquivalence` is strong monoidal. -/
instance gaugeEquivalenceFunctorMonoidal (g : GradedObject.TwistingCocycle.Gauge c d) :
    (gaugeEquivalence g).functor.Monoidal :=
  inferInstanceAs
    ((g.equivalence (ModuleCat.{u} R)).congrFullSubcategory
      (objects_inverseImage_gauge g)).functor.Monoidal

/-- The inverse functor of `gaugeEquivalence` is strong monoidal. -/
instance gaugeEquivalenceInverseMonoidal (g : GradedObject.TwistingCocycle.Gauge c d) :
    (gaugeEquivalence g).inverse.Monoidal :=
  inferInstanceAs
    ((g.equivalence (ModuleCat.{u} R)).congrFullSubcategory
      (objects_inverseImage_gauge g)).inverse.Monoidal

/-- `gaugeEquivalence` is a monoidal equivalence. -/
instance gaugeEquivalence_isMonoidal (g : GradedObject.TwistingCocycle.Gauge c d) :
    (gaugeEquivalence g).IsMonoidal :=
  inferInstanceAs
    ((g.equivalence (ModuleCat.{u} R)).congrFullSubcategory
      (objects_inverseImage_gauge g)).IsMonoidal

@[simp]
theorem gaugeEquivalence_functor_obj_single (g : GradedObject.TwistingCocycle.Gauge c d)
    (x : G) (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Projective R M] :
    (gaugeEquivalence g).functor.obj (single (c := c) x M) = single (c := d) x M := by
  ext
  exact gaugeEquivalence_functor_obj_obj g (single (c := c) x M)

@[simp]
theorem gaugeEquivalence_functor_obj_delta (g : GradedObject.TwistingCocycle.Gauge c d)
    (x : G) :
    (gaugeEquivalence g).functor.obj (delta (c := c) x) = delta (c := d) x :=
  gaugeEquivalence_functor_obj_single g x (ModuleCat.of R R)

theorem gaugeEquivalence_functor_ε_hom (g : GradedObject.TwistingCocycle.Gauge c d) :
    (Functor.LaxMonoidal.ε (gaugeEquivalence g).functor).hom =
      eqToHom ((tensorUnit_obj (c := d)).trans
        ((tensorUnit_obj (c := c)).symm.trans
          (gaugeEquivalence_functor_obj_obj g (𝟙_ _)).symm)) := by
  -- Unfold `gaugeEquivalence` and its monoidal instance to `congrFullSubcategory`.
  change (Functor.LaxMonoidal.ε
    ((g.equivalence (ModuleCat.{u} R)).congrFullSubcategory
      (objects_inverseImage_gauge g)).functor).hom = _
  rw [Equivalence.congrFullSubcategory_functor_ε_hom]
  exact g.equivalence_functor_ε (ModuleCat.{u} R)

theorem gaugeEquivalence_functor_μ_hom (g : GradedObject.TwistingCocycle.Gauge c d)
    (X Y : VecTwisted R G c) :
    (Functor.LaxMonoidal.μ (gaugeEquivalence g).functor X Y).hom =
      eqToHom (by rw [tensorObj_obj, gaugeEquivalence_functor_obj_obj,
        gaugeEquivalence_functor_obj_obj]) ≫
        CategoryTheory.GradedObject.Monoidal.scaleTensorObj X.obj Y.obj
          (fun i j ↦ (g.u i j : R)) ≫
        eqToHom ((tensorObj_obj X Y).symm.trans
          (gaugeEquivalence_functor_obj_obj g (X ⊗ Y)).symm) := by
  -- Unfold `gaugeEquivalence` and its monoidal instance to `congrFullSubcategory`.
  change (Functor.LaxMonoidal.μ
    ((g.equivalence (ModuleCat.{u} R)).congrFullSubcategory
      (objects_inverseImage_gauge g)).functor X Y).hom = _
  rw [Equivalence.congrFullSubcategory_functor_μ_hom]
  exact g.equivalence_functor_μ (ModuleCat.{u} R) X.obj Y.obj

/-- On two single-degree objects, the tensorator of `gaugeEquivalence g` is scalar multiplication
by `g.u (Additive.ofMul x) (Additive.ofMul y)`. -/
theorem gaugeEquivalence_functor_μ_single_hom (g : GradedObject.TwistingCocycle.Gauge c d)
    (x y : G) (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] :
    (Functor.LaxMonoidal.μ (gaugeEquivalence g).functor
        (single (c := c) x M) (single (c := c) y N)).hom =
      (g.u (Additive.ofMul x) (Additive.ofMul y) : R) •
        eqToHom (by
          rw [tensorObj_obj, gaugeEquivalence_functor_obj_obj, gaugeEquivalence_functor_obj_obj,
            gaugeEquivalence_functor_obj_obj, tensorObj_obj]) := by
  -- Unfold `gaugeEquivalence` and its monoidal instance to `congrFullSubcategory`.
  change (Functor.LaxMonoidal.μ
    ((g.equivalence (ModuleCat.{u} R)).congrFullSubcategory
      (objects_inverseImage_gauge g)).functor
    (single (c := c) x M) (single (c := c) y N)).hom = _
  rw [Equivalence.congrFullSubcategory_functor_μ_hom]
  exact g.equivalence_functor_μ_single (Additive.ofMul x) (Additive.ofMul y) M N

omit [DecidableEq G] in
private theorem tensorObj_congr
    {X₁ X₂ Y₁ Y₂ : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R)}
    (hX : X₁ = X₂) (hY : Y₁ = Y₂) :
    CategoryTheory.GradedObject.Monoidal.tensorObj X₁ Y₁ =
      CategoryTheory.GradedObject.Monoidal.tensorObj X₂ Y₂ := by
  subst hX hY; rfl

/-- On two rank-one objects `delta x` and `delta y`, the tensorator of `gaugeEquivalence g`
scales `deltaTensorIso` by `g.u (Additive.ofMul x) (Additive.ofMul y)`. -/
theorem gaugeEquivalence_functor_μ_comp_deltaTensorIso
    (g : GradedObject.TwistingCocycle.Gauge c d) (x y : G) :
    eqToHom (by rw [gaugeEquivalence_functor_obj_delta, gaugeEquivalence_functor_obj_delta]) ≫
        Functor.LaxMonoidal.μ (gaugeEquivalence g).functor
          (delta (c := c) x) (delta (c := c) y) ≫
        (gaugeEquivalence g).functor.map (deltaTensorIso (c := c) x y).hom ≫
        eqToHom (gaugeEquivalence_functor_obj_delta g (x * y)) =
      (g.u (Additive.ofMul x) (Additive.ofMul y) : R) • (deltaTensorIso (c := d) x y).hom := by
  apply ObjectProperty.hom_ext
  let U : ModuleCat.{u} R := ModuleCat.of R R
  let S0 : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) :=
    CategoryTheory.GradedObject.Monoidal.tensorObj
      ((CategoryTheory.GradedObject.single (Additive.ofMul x)).obj U)
      ((CategoryTheory.GradedObject.single (Additive.ofMul y)).obj U)
  let S1 : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) :=
    (CategoryTheory.GradedObject.single (Additive.ofMul (x * y))).obj U
  let core : S0 ⟶ S1 :=
    (CategoryTheory.GradedObject.Monoidal.singleTensorIso
        (Additive.ofMul x) (Additive.ofMul y) U U).hom ≫
      (CategoryTheory.GradedObject.single (Additive.ofMul (x * y))).map (λ_ U).hom
  let A0 : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) :=
    (delta (c := d) x ⊗ delta (c := d) y).obj
  let A1 : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) :=
    ((gaugeEquivalence g).functor.obj (delta (c := c) x) ⊗
      (gaugeEquivalence g).functor.obj (delta (c := c) y)).obj
  let A2 : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) :=
    ((gaugeEquivalence g).functor.obj (delta (c := c) x ⊗ delta (c := c) y)).obj
  let A3 : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) :=
    ((gaugeEquivalence g).functor.obj (delta (c := c) (x * y))).obj
  let A4 : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) :=
    (delta (c := d) (x * y)).obj
  let B0 : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) :=
    (delta (c := c) x ⊗ delta (c := c) y).obj
  let B1 : CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R) :=
    (delta (c := c) (x * y)).obj
  let eL : delta (c := d) x ⊗ delta (c := d) y =
      (gaugeEquivalence g).functor.obj (delta (c := c) x) ⊗
        (gaugeEquivalence g).functor.obj (delta (c := c) y) := by
    rw [gaugeEquivalence_functor_obj_delta, gaugeEquivalence_functor_obj_delta]
  let eR : (gaugeEquivalence g).functor.obj (delta (c := c) (x * y)) = delta (c := d) (x * y) :=
    gaugeEquivalence_functor_obj_delta g (x * y)
  have h01 : A0 = A1 := congrArg ObjectProperty.FullSubcategory.obj eL
  have hx_obj : (((gaugeEquivalence g).functor.obj (delta (c := c) x)).obj :
      CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R)) = (delta (c := c) x).obj :=
    gaugeEquivalence_functor_obj_obj g (delta (c := c) x)
  have hy_obj : (((gaugeEquivalence g).functor.obj (delta (c := c) y)).obj :
      CategoryTheory.GradedObject (Additive G) (ModuleCat.{u} R)) = (delta (c := c) y).obj :=
    gaugeEquivalence_functor_obj_obj g (delta (c := c) y)
  have h12 : A1 = A2 :=
    (tensorObj_obj _ _).trans <|
      (tensorObj_congr hx_obj hy_obj).trans <|
      (tensorObj_obj (delta (c := c) x) (delta (c := c) y)).symm.trans
        (gaugeEquivalence_functor_obj_obj g (delta (c := c) x ⊗ delta (c := c) y)).symm
  have h2B0 : A2 = B0 := gaugeEquivalence_functor_obj_obj g _
  have hB0S0 : B0 = S0 :=
    (tensorObj_obj (delta (c := c) x) (delta (c := c) y)).trans
      (tensorObj_congr (delta_obj (c := c) x) (delta_obj (c := c) y))
  have hS1B1 : S1 = B1 := (delta_obj (c := c) (x * y)).symm
  have hB13 : B1 = A3 := (gaugeEquivalence_functor_obj_obj g _).symm
  have h34 : A3 = A4 := congrArg ObjectProperty.FullSubcategory.obj eR
  have hA0S0 : A0 = S0 :=
    (tensorObj_obj (delta (c := d) x) (delta (c := d) y)).trans
      (tensorObj_congr (delta_obj (c := d) x) (delta_obj (c := d) y))
  have hS1A4 : S1 = A4 := (delta_obj (c := d) (x * y)).symm
  have hμ : ((Functor.LaxMonoidal.μ (gaugeEquivalence g).functor
      (delta (c := c) x) (delta (c := c) y)).hom : A1 ⟶ A2) =
      (g.u (Additive.ofMul x) (Additive.ofMul y) : R) • eqToHom h12 :=
    gaugeEquivalence_functor_μ_single_hom g x y U U
  have hmap : (((gaugeEquivalence g).functor.map (deltaTensorIso (c := c) x y).hom).hom :
      A2 ⟶ A3) = eqToHom h2B0 ≫ (eqToHom hB0S0 ≫ core ≫ eqToHom hS1B1) ≫ eqToHom hB13 :=
    (gaugeEquivalence_functor_map_hom g (deltaTensorIso (c := c) x y).hom).trans
      (congrArg (fun k : B0 ⟶ B1 ↦ eqToHom h2B0 ≫ k ≫ eqToHom hB13)
        (deltaTensorIso_hom_hom (c := c) x y))
  have hrhs : ((deltaTensorIso (c := d) x y).hom.hom : A0 ⟶ A4) =
      eqToHom hA0S0 ≫ core ≫ eqToHom hS1A4 :=
    deltaTensorIso_hom_hom (c := d) x y
  have hchain : (eqToHom h01 : A0 ⟶ A1) ≫
      ((g.u (Additive.ofMul x) (Additive.ofMul y) : R) • (eqToHom h12 : A1 ⟶ A2)) ≫
      (eqToHom h2B0 ≫ (eqToHom hB0S0 ≫ core ≫ eqToHom hS1B1) ≫ eqToHom hB13) ≫
      (eqToHom h34 : A3 ⟶ A4) =
      (g.u (Additive.ofMul x) (Additive.ofMul y) : R) •
        (eqToHom hA0S0 ≫ core ≫ eqToHom hS1A4) := by
    simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc, eqToHom_trans,
      eqToHom_trans_assoc]
  have hgoal :
      ((eqToHom eL ≫ Functor.LaxMonoidal.μ (gaugeEquivalence g).functor
          (delta (c := c) x) (delta (c := c) y) ≫
          (gaugeEquivalence g).functor.map (deltaTensorIso (c := c) x y).hom ≫
          eqToHom eR).hom : A0 ⟶ A4) =
      (((g.u (Additive.ofMul x) (Additive.ofMul y) : R) •
          (deltaTensorIso (c := d) x y).hom).hom : A0 ⟶ A4) := by
    have hlhs : ((eqToHom eL ≫ Functor.LaxMonoidal.μ (gaugeEquivalence g).functor
          (delta (c := c) x) (delta (c := c) y) ≫
          (gaugeEquivalence g).functor.map (deltaTensorIso (c := c) x y).hom ≫
          eqToHom eR).hom : A0 ⟶ A4) =
        (eqToHom h01 : A0 ⟶ A1) ≫
          ((Functor.LaxMonoidal.μ (gaugeEquivalence g).functor
            (delta (c := c) x) (delta (c := c) y)).hom : A1 ⟶ A2) ≫
          (((gaugeEquivalence g).functor.map (deltaTensorIso (c := c) x y).hom).hom : A2 ⟶ A3) ≫
          (eqToHom h34 : A3 ⟶ A4) := by
      simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.eqToHom_hom]
      rfl
    rw [hlhs, hμ, hmap, ObjectProperty.smul_hom, hrhs]
    exact hchain
  exact hgoal

end Gauge

end VecTwisted

end TauCeti
