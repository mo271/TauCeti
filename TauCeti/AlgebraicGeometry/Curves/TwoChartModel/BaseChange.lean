/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.AlgHom
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Curve
public import TauCeti.AlgebraicGeometry.Geometrically.Reduced
public import TauCeti.AlgebraicGeometry.Geometrically.Regular
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.FractionField

import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Classification
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.AlgebraicGeometry.Pullback.SpecMap
import TauCeti.RingTheory.Localization.FractionRing

/-!
# Whole-model geometric properties and base change of the two-chart model

Let `F / k` be an algebraic function field of one variable and `x ∈ F` transcendental over `k`, and
let `X = twoChartModel hF hx` be its regular proper two-chart model over `k`. This file
characterizes geometric reducedness, geometric integrality, geometric regularity, and smoothness on
`X`, and compares the base change `X ×_k Spec K` along an arbitrary field extension `K / k`
(algebraic or transcendental) with the two-chart model of the extended function field
`Frac(F ⊗[k] K)`.

Because `X` is integral and locally of finite type over `k`, its geometric reducedness and geometric
integrality depend only on `F`: `X` is geometrically reduced over `k` iff `F` is geometrically
reduced over `k`, and geometrically integral over `k` iff `k` is integrally closed in `F` and `F` is
geometrically reduced over `k` (in particular whenever `F / k` has exact constants and a separating
element, or whenever `k` is perfect with exact constants). By contrast, smoothness of `X` over `k`
is equivalent to geometric regularity of `X` over `k` (`smooth_iff_geometricallyRegular`), which is
strictly stronger over imperfect fields (`TauCeti.GenusDrop.not_geometricallyRegular_curveModel`).

When `X` is geometrically integral over `k`, `F ⊗[k] K` is a domain for every field extension
`K / k`. Any fraction field `F_K` of `F ⊗[k] K` is an algebraic function field over `K` in which
`algebraMap F F_K x` remains transcendental, and for any pullback square `Y = X ×_k Spec K` we
construct the canonical `K`-algebra equivalence `Y.functionField ≃ₐ[K] F_K` sending the pullback of
`z ∈ F` along `Y ⟶ X` to `algebraMap F F_K z`, proving that `Y` is a proper integral curve over `K`.

When `X` is moreover smooth (equivalently, geometrically regular) over `k`, the base change `Y` is
smooth over `K`, hence regular. Classification of regular proper curves (`Scheme.isoTwoChartModel`)
then yields the canonical `K`-scheme isomorphism `Y ≅ twoChartModel hF_K hx_K` characterized by its
action on rational functions, and transfers smoothness and geometric integrality over `K` to the
two-chart model of `F_K`.

## Main declarations

* `TauCeti.AlgebraicGeometry.twoChartModel.isRegular`: the two-chart model is a regular scheme.
* `TauCeti.AlgebraicGeometry.twoChartModel.geometricallyReduced_iff`,
  `geometricallyIntegral_iff`, and `smooth_iff_geometricallyRegular`: whole-model criteria on the
  two-chart model.
* `TauCeti.AlgebraicGeometry.twoChartModel.functionFieldEquivOfIsPullback`: canonical `K`-algebra
  equivalence `Y.functionField ≃ₐ[K] F_K` for any pullback `Y = twoChartModel hF hx ×_k Spec K` and
  any fraction field `F_K` of `F ⊗[k] K`.
* `TauCeti.AlgebraicGeometry.twoChartModel.isCurveOver_of_isPullback`: the base change `Y` is a
  curve over `K`.
* `TauCeti.AlgebraicGeometry.twoChartModel.isoTwoChartModelOfIsPullback` and
  `pullbackIsoTwoChartModel`: canonical `K`-scheme isomorphism between the base change of a smooth
  geometrically integral two-chart model and the two-chart model of `Frac(F ⊗[k] K)`.

## References

* A. Grothendieck, *Éléments de géométrie algébrique* IV₂, §4.6; IV₄, §17.5.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6 and Appendix B.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford GTM 6, 2002, Chapter 7.
-/

public section

open CategoryTheory Limits _root_.AlgebraicGeometry
open scoped TensorProduct IntermediateField

namespace TauCeti.AlgebraicGeometry.twoChartModel

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

universe u

section ModelPredicates

variable {k F : Type u} [Field k] [Field F] [Algebra k F] {hF : IsFunctionField k F} {x : F}
  {hx : x ≠ 0}

/-- **The two-chart model is a regular scheme**: it is Noetherian and all of its stalks are regular
local rings. -/
instance isRegular : IsRegular (twoChartModel hF hx) :=
  ⟨fun _ ↦ inferInstance⟩

/-- **Smoothness on the two-chart model is geometric regularity.** -/
theorem smooth_iff_geometricallyRegular :
    Smooth (twoChartModel hF hx ↘ Spec (.of k)) ↔
      GeometricallyRegular (twoChartModel hF hx ↘ Spec (.of k)) :=
  TauCeti.AlgebraicGeometry.smooth_iff_geometricallyRegular _

/-- For `x` transcendental over `k`, smoothness of `twoChartModel hF hx` over `k` gives smoothness
of relative dimension one. -/
theorem smoothOfRelativeDimension_one_of_smooth (hxt : Transcendental k x)
    [Smooth (twoChartModel hF hx ↘ Spec (.of k))] :
    SmoothOfRelativeDimension 1 (twoChartModel hF hx ↘ Spec (.of k)) :=
  smoothOfRelativeDimension_of_topologicalKrullDim_eq _ (topologicalKrullDim_eq_one hxt)

/-- For `x` transcendental over `k`, `twoChartModel hF hx` is smooth of relative dimension one over
`k` if and only if it is geometrically regular over `k`. -/
theorem smoothOfRelativeDimension_one_iff_geometricallyRegular (hxt : Transcendental k x) :
    SmoothOfRelativeDimension 1 (twoChartModel hF hx ↘ Spec (.of k)) ↔
      GeometricallyRegular (twoChartModel hF hx ↘ Spec (.of k)) :=
  ⟨fun _ ↦ by
    have := SmoothOfRelativeDimension.smooth 1 (twoChartModel hF hx ↘ Spec (.of k))
    infer_instance,
   fun _ ↦ by
    have := (smooth_iff_geometricallyRegular (hF := hF) (hx := hx)).mpr inferInstance
    exact smoothOfRelativeDimension_one_of_smooth hxt⟩

/-- **The two-chart model is geometrically reduced over `k` if and only if `F` is geometrically
reduced over `k`**, for `x` transcendental over `k`. -/
theorem geometricallyReduced_iff (hxt : Transcendental k x) :
    GeometricallyReduced (twoChartModel hF hx ↘ Spec (.of k)) ↔
      Algebra.IsGeometricallyReduced k F :=
  (geometricallyReduced_iff_isGeometricallyReduced_functionField
    (X := twoChartModel hF hx)).trans
    ⟨fun _ ↦ .of_injective (functionFieldEquiv hxt).symm.toAlgHom
        (functionFieldEquiv hxt).symm.injective,
     fun _ ↦ .of_injective (functionFieldEquiv hxt).toAlgHom (functionFieldEquiv hxt).injective⟩

/-- **The two-chart model is geometrically integral over `k` if and only if `k` is integrally closed
in `F` and `F` is geometrically reduced over `k`**, for `x` transcendental over `k`. -/
theorem geometricallyIntegral_iff (hxt : Transcendental k x) :
    GeometricallyIntegral (twoChartModel hF hx ↘ Spec (.of k)) ↔
      IsIntegrallyClosedIn k F ∧ Algebra.IsGeometricallyReduced k F := by
  rw [geometricallyIntegral_iff_isIntegrallyClosedIn_and_isGeometricallyReduced,
    (functionFieldEquiv hxt).isIntegrallyClosedIn]
  exact and_congr_right'
    ⟨fun _ ↦ .of_injective (functionFieldEquiv hxt).symm.toAlgHom
        (functionFieldEquiv hxt).symm.injective,
     fun _ ↦ .of_injective (functionFieldEquiv hxt).toAlgHom (functionFieldEquiv hxt).injective⟩

/-- **A separably generated function field with exact constants has a geometrically integral
two-chart model.** Here `y` may be any separating element of `F / k`, not necessarily `x`. -/
theorem geometricallyIntegral_of_separating (hxt : Transcendental k x)
    (hk : IsIntegrallyClosedIn k F) {y : F} (hy : Transcendental k y)
    [Algebra.IsSeparable k⟮y⟯ F] :
    GeometricallyIntegral (twoChartModel hF hx ↘ Spec (.of k)) :=
  (geometricallyIntegral_iff hxt).mpr ⟨hk, isGeometricallyReduced_of_separating hy⟩

/-- Over a perfect field `k`, the two-chart model of a function field with exact constants `k` is
geometrically integral over `k`. -/
theorem geometricallyIntegral_of_perfectField [PerfectField k] (hxt : Transcendental k x)
    (hk : IsIntegrallyClosedIn k F) :
    GeometricallyIntegral (twoChartModel hF hx ↘ Spec (.of k)) :=
  (geometricallyIntegral_iff hxt).mpr ⟨hk, inferInstance⟩

/-- A geometrically regular two-chart model whose function field has exact constants `k` is
geometrically integral over `k`. -/
theorem geometricallyIntegral_of_geometricallyRegular (hxt : Transcendental k x)
    (hk : IsIntegrallyClosedIn k F)
    [GeometricallyRegular (twoChartModel hF hx ↘ Spec (.of k))] :
    GeometricallyIntegral (twoChartModel hF hx ↘ Spec (.of k)) :=
  (geometricallyIntegral_iff hxt).mpr ⟨hk, (geometricallyReduced_iff hxt).mp inferInstance⟩

end ModelPredicates

/-! ### Helper lemmas on tensor subrings and dominant pullbacks -/

section Helpers

private noncomputable abbrev finiteChartRing (k F : Type u) [Field k] [Field F] [Algebra k F]
    (x : F) : Type u :=
  holomorphyRing {P : Place k F | x ∈ P.integers}

@[instance_reducible]
private noncomputable def tensorSubringAlgebra {k A F K F_K : Type u} [CommRing k] [CommRing A]
    [CommRing F] [CommRing K] [CommRing F_K] [Algebra k A] [Algebra k F] [Algebra A F]
    [IsScalarTower k A F] [Algebra k K] [Algebra (F ⊗[k] K) F_K] :
    Algebra (A ⊗[k] K) F_K :=
  ((algebraMap (F ⊗[k] K) F_K).comp
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A F) (AlgHom.id k K)).toRingHom).toAlgebra

private theorem isFractionRing_tensorSubring {k A F K F_K : Type u} [Field k] [CommRing A]
    [IsDomain A] [Field F] [Field K] [Field F_K] [Algebra k A] [Algebra k F] [Algebra A F]
    [IsScalarTower k A F] [IsFractionRing A F] [Algebra k K] [IsDomain (F ⊗[k] K)]
    [Algebra (F ⊗[k] K) F_K] [IsFractionRing (F ⊗[k] K) F_K] :
    letI := tensorSubringAlgebra (k := k) (A := A) (F := F) (K := K) (F_K := F_K)
    IsFractionRing (A ⊗[k] K) F_K := by
  let _ := tensorSubringAlgebra (k := k) (A := A) (F := F) (K := K) (F_K := F_K)
  let φ : A ⊗[k] K →ₐ[k] F ⊗[k] K :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A F) (AlgHom.id k K)
  algebraize [φ.toRingHom]
  have : IsScalarTower A (A ⊗[k] K) (F ⊗[k] K) := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra, φ]
  have : IsScalarTower (A ⊗[k] K) (F ⊗[k] K) F_K := .of_algebraMap_eq' rfl
  have : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[k] K) (nonZeroDivisors A)) (F ⊗[k] K) :=
    IsLocalization.tensorProduct_tensorProduct k K (nonZeroDivisors A) F
      (by ext; simp [RingHom.algebraMap_toAlgebra, φ])
  have hinj : Function.Injective (algebraMap A (A ⊗[k] K)) :=
    Algebra.TensorProduct.includeLeft_injective (S := k) (algebraMap k K).injective
  have hφ : Function.Injective φ :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := K)
      (IsScalarTower.toAlgHom k A F).toLinearMap (IsFractionRing.injective A F)
  have : IsDomain (A ⊗[k] K) := Function.Injective.isDomain φ.toRingHom hφ
  exact TauCeti.IsFractionRing.of_isLocalization_of_isFractionRing
    (Algebra.algebraMapSubmonoid (A ⊗[k] K) (nonZeroDivisors A)) (F ⊗[k] K) F_K
    (map_le_nonZeroDivisors_of_injective _ hinj le_rfl)

/-- For any pullback `Y = X ×_k Spec K` over a field extension `K / k`, the projection `g : Y ⟶ X`
is dominant. -/
theorem isDominant_of_isPullback {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of K))] {g : Y ⟶ X}
    (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) : IsDominant g := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : IsDominant s := isDominant_iff_genericPoint_eq.mpr (Subsingleton.elim _ _)
  have hopen : IsOpenMap (X ↘ Spec (.of k)) := fun _ _ ↦ isOpen_discrete _
  have : IsDominant (pullback.fst (X ↘ Spec (.of k)) s) :=
    IsDominant.pullback_fst_of_isOpenMap _ _ hopen
  rw [← H.isoPullback_hom_fst]
  infer_instance

end Helpers

/-! ### Base change along an arbitrary field extension -/

section BaseChange

variable {k F K F_K : Type u} [Field k] [Field F] [Field K] [Field F_K]
  [Algebra k F] [Algebra k K]
  {hF : IsFunctionField k F} {x : F} {hx : x ≠ 0}

/-- When `twoChartModel hF hx` is geometrically integral over `k`, the tensor product `F ⊗[k] K` is
a domain for every field extension `K / k`. -/
theorem isDomain_tensorProduct (hxt : Transcendental k x)
    [GeometricallyIntegral (twoChartModel hF hx ↘ Spec (.of k))] (K : Type u) [Field K]
    [Algebra k K] : IsDomain (F ⊗[k] K) := by
  obtain ⟨hk, _⟩ := (geometricallyIntegral_iff (hF := hF) (hx := hx) hxt).mp inferInstance
  exact isDomain_tensorProduct_of_isGeometricallyReduced hk K

/-- The parameter `x ≠ 0` remains nonzero in `F_K`. -/
theorem algebraMap_param_ne_zero [Algebra F F_K] (hx : x ≠ 0) : algebraMap F F_K x ≠ 0 := by
  simpa using (algebraMap F F_K).injective.ne hx

/-- In any fraction field `F_K` of a domain tensor product `F ⊗[k] K`, a transcendental element
`x ∈ F` over `k` remains transcendental over `K`. -/
theorem transcendental_algebraMap [Algebra (F ⊗[k] K) F_K] [Algebra k F_K] [Algebra F F_K]
    [Algebra K F_K] [IsScalarTower k (F ⊗[k] K) F_K] [IsScalarTower F (F ⊗[k] K) F_K]
    [IsScalarTower K (F ⊗[k] K) F_K] [IsScalarTower k F F_K] [IsScalarTower k K F_K]
    [IsFractionRing (F ⊗[k] K) F_K] (hxt : Transcendental k x) :
    Transcendental K (algebraMap F F_K x) :=
  (linearDisjoint_of_isFractionRing_tensorProduct (k := k)).transcendental_algebraMap hxt

variable {Y : Scheme.{u}} [Y.Over (Spec (.of K))] {g : Y ⟶ twoChartModel hF hx}

/-- The canonical open immersion `Spec (𝒪_x ⊗[k] K) ⟶ Y` induced by pulling back the finite chart
`ιFinite hF hx` along `H`. -/
private noncomputable def pullbackFiniteChart
    (H : IsPullback g (Y ↘ Spec (.of K)) (twoChartModel hF hx ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    Spec (.of (finiteChartRing k F x ⊗[k] K)) ⟶ Y :=
  (pullbackSpecIso k (finiteChartRing k F x) K).inv ≫
    (pullback.congrHom (ιFinite_over hF hx).symm rfl).hom ≫
    (pullbackRightPullbackFstIso _ _ _).inv ≫ pullback.snd _ _ ≫ H.isoPullback.inv

private instance isOpenImmersion_pullbackFiniteChart
    (H : IsPullback g (Y ↘ Spec (.of K)) (twoChartModel hF hx ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    IsOpenImmersion (pullbackFiniteChart H) := by
  unfold pullbackFiniteChart
  infer_instance

private theorem pullbackFiniteChart_over
    (H : IsPullback g (Y ↘ Spec (.of K)) (twoChartModel hF hx ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    pullbackFiniteChart H ≫ (Y ↘ Spec (.of K)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (finiteChartRing k F x ⊗[k] K))) := by
  simp [pullbackFiniteChart]
  rfl

private theorem pullbackFiniteChart_comp_fst
    (H : IsPullback g (Y ↘ Spec (.of K)) (twoChartModel hF hx ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    pullbackFiniteChart H ≫ g =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ ιFinite hF hx := by
  simp [pullbackFiniteChart]

private theorem image_pullbackFiniteChart_top_le_preimage
    (H : IsPullback g (Y ↘ Spec (.of K)) (twoChartModel hF hx ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    pullbackFiniteChart H ''ᵁ ⊤ ≤ g ⁻¹ᵁ (ιFinite hF hx ''ᵁ ⊤) := by
  rintro _ ⟨p, -, rfl⟩
  change (pullbackFiniteChart H ≫ g) p ∈ ιFinite hF hx ''ᵁ ⊤
  rw [pullbackFiniteChart_comp_fst H]
  exact ⟨_, trivial, rfl⟩

private noncomputable def pullbackFiniteChartSectionsEquiv
    (H : IsPullback g (Y ↘ Spec (.of K)) (twoChartModel hF hx ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    Γ(Y, pullbackFiniteChart H ''ᵁ ⊤) ≃+* finiteChartRing k F x ⊗[k] K :=
  (((pullbackFiniteChart H).appIso ⊤) ≪≫
    Scheme.ΓSpecIso (.of (finiteChartRing k F x ⊗[k] K))).commRingCatIsoToRingEquiv

@[simp]
private theorem pullbackFiniteChartSectionsEquiv_apply
    (H : IsPullback g (Y ↘ Spec (.of K)) (twoChartModel hF hx ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (a : Γ(Y, pullbackFiniteChart H ''ᵁ ⊤)) :
    pullbackFiniteChartSectionsEquiv H a =
      (Scheme.ΓSpecIso (.of (finiteChartRing k F x ⊗[k] K))).hom
        (((pullbackFiniteChart H).appIso ⊤).hom a) :=
  (rfl)

private theorem pullbackFiniteChartSectionsEquiv_appLE_over
    (H : IsPullback g (Y ↘ Spec (.of K)) (twoChartModel hF hx ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (c : Γ(Spec (.of K), ⊤)) :
    pullbackFiniteChartSectionsEquiv H
      ((Y ↘ Spec (.of K)).appLE ⊤ (pullbackFiniteChart H ''ᵁ ⊤) le_top c) =
      algebraMap K (finiteChartRing k F x ⊗[k] K) ((Scheme.ΓSpecIso (.of K)).hom c) := by
  suffices hs : (Y ↘ Spec (.of K)).appLE ⊤ (pullbackFiniteChart H ''ᵁ ⊤) le_top ≫
      ((pullbackFiniteChart H).appIso ⊤).hom ≫ (Scheme.ΓSpecIso _).hom =
      (Scheme.ΓSpecIso (.of K)).hom ≫
        CommRingCat.ofHom (algebraMap K (finiteChartRing k F x ⊗[k] K)) from
    congr($hs c)
  rw [← cancel_epi (Scheme.ΓSpecIso (.of K)).inv, Iso.inv_hom_id_assoc, Scheme.Hom.appIso_hom',
    reassoc_of% Scheme.Hom.appLE_comp_appLE (pullbackFiniteChart H) (Y ↘ Spec (.of K)) ⊤
      (pullbackFiniteChart H ''ᵁ ⊤) ⊤ le_top (Scheme.Hom.preimage_image_eq _ _).ge]
  generalize_proofs _ pf
  revert pf
  rw [pullbackFiniteChart_over H]
  intro pf
  rw [show Scheme.Hom.appLE _ ⊤ ⊤ pf = Scheme.Hom.appTop _ from Scheme.Hom.appLE_eq_app _,
    Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

private theorem pullbackFiniteChartSectionsEquiv_appLE_fst
    (H : IsPullback g (Y ↘ Spec (.of K)) (twoChartModel hF hx ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (s : Γ(twoChartModel hF hx, ιFinite hF hx ''ᵁ ⊤)) :
    pullbackFiniteChartSectionsEquiv H
      (g.appLE _ _ (image_pullbackFiniteChart_top_le_preimage H) s) =
      (finiteChartSectionsEquiv hF hx s) ⊗ₜ[k] 1 := by
  let iL : finiteChartRing k F x →+* finiteChartRing k F x ⊗[k] K :=
    Algebra.TensorProduct.includeLeftRingHom
  suffices e : g.appLE _ _ (image_pullbackFiniteChart_top_le_preimage H) ≫
      ((pullbackFiniteChart H).appIso ⊤).hom ≫ (Scheme.ΓSpecIso _).hom =
      ((ιFinite hF hx).appIso ⊤).hom ≫ (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom iL by
    simpa only [pullbackFiniteChartSectionsEquiv_apply, finiteChartSectionsEquiv_apply,
      CategoryTheory.comp_apply, CommRingCat.hom_ofHom, iL,
      Algebra.TensorProduct.includeLeftRingHom_apply] using congr($e s)
  have appLE_eq {X₁ X₂ : Scheme.{u}} {f₁ f₂ : X₁ ⟶ X₂} (hfg : f₁ = f₂) (U V e) :
      f₁.appLE U V e = f₂.appLE U V (hfg ▸ e) := by
    subst hfg
    rfl
  have hle : ⊤ ≤ (Spec.map (CommRingCat.ofHom iL) ≫ ιFinite hF hx) ⁻¹ᵁ
      (ιFinite hF hx ''ᵁ ⊤) := by
    rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq]
    exact le_top
  calc _ = (pullbackFiniteChart H ≫ g).appLE (ιFinite hF hx ''ᵁ ⊤) ⊤
          (pullbackFiniteChart_comp_fst H ▸ hle) ≫ (Scheme.ΓSpecIso _).hom := by
        rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE_assoc]
    _ = (Spec.map (CommRingCat.ofHom iL) ≫ ιFinite hF hx).appLE
          (ιFinite hF hx ''ᵁ ⊤) ⊤ hle ≫ (Scheme.ΓSpecIso _).hom := by
        rw [appLE_eq (pullbackFiniteChart_comp_fst H)]
    _ = ((ιFinite hF hx).appIso ⊤).hom ≫
          (Spec.map (CommRingCat.ofHom iL)).appTop ≫ (Scheme.ΓSpecIso _).hom := by
        rw [← Scheme.Hom.appLE_comp_appLE (Spec.map _) (ιFinite hF hx) _ ⊤ ⊤
            (Scheme.Hom.preimage_image_eq _ _).ge le_top, Category.assoc,
          show Scheme.Hom.appLE _ ⊤ ⊤ le_top = Scheme.Hom.appTop _ from
            Scheme.Hom.appLE_eq_app _,
          Scheme.Hom.appIso_hom']
    _ = _ := by rw [Scheme.ΓSpecIso_naturality]

section PullbackFunctionField

variable [Algebra (F ⊗[k] K) F_K] [Algebra K F_K] [IsScalarTower K (F ⊗[k] K) F_K]
  [IsFractionRing (F ⊗[k] K) F_K]
  [GeometricallyIntegral (twoChartModel hF hx ↘ Spec (.of k))]

/-- **The function field of the base change of `twoChartModel hF hx` to any field extension `K / k`
is canonically `F_K = Frac(F ⊗[k] K)`** as a `K`-algebra. -/
noncomputable def functionFieldEquivOfIsPullback (hxt : Transcendental k x)
    (H : IsPullback g (Y ↘ Spec (.of K)) (twoChartModel hF hx ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
    Y.functionField ≃ₐ[K] F_K :=
  haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  haveI := isFractionRing_holomorphyRing_setOf_mem hF hxt
  haveI := isDomain_tensorProduct (hF := hF) (hx := hx) hxt K
  letI : Algebra (finiteChartRing k F x ⊗[k] K) F_K :=
    tensorSubringAlgebra (k := k) (F := F) (K := K) (F_K := F_K)
  haveI : IsScalarTower K (finiteChartRing k F x ⊗[k] K) F_K :=
    .of_algebraMap_eq fun c ↦ IsScalarTower.algebraMap_apply K (F ⊗[k] K) F_K c
  haveI : IsFractionRing (finiteChartRing k F x ⊗[k] K) F_K :=
    isFractionRing_tensorSubring (k := k) (F := F) (K := K) (F_K := F_K)
  haveI : Nontrivial (finiteChartRing k F x ⊗[k] K) :=
    (IsFractionRing.nontrivial_iff_nontrivial (finiteChartRing k F x ⊗[k] K) F_K).mpr inferInstance
  haveI : Nonempty (pullbackFiniteChart H ''ᵁ ⊤) :=
    ⟨⟨pullbackFiniteChart H (Classical.arbitrary _), ⟨_, trivial, rfl⟩⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen Y (pullbackFiniteChart H ''ᵁ ⊤)
    ((isAffineOpen_top _).image_of_isOpenImmersion (pullbackFiniteChart H))
  AlgEquiv.ofRingEquiv
    (f := IsFractionRing.ringEquivOfRingEquiv (pullbackFiniteChartSectionsEquiv H))
    fun c ↦ by
      rw [Scheme.algebraMap_functionField_eq_baseRingToFunctionField,
        Scheme.baseRingToFunctionField_eq_comp_appLE K Y (pullbackFiniteChart H ''ᵁ ⊤),
        RingHom.comp_apply]
      refine (IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _).trans ?_
      rw [CommRingCat.comp_apply, pullbackFiniteChartSectionsEquiv_appLE_over H,
        Iso.inv_hom_id_apply]
      exact (IsScalarTower.algebraMap_apply K (finiteChartRing k F x ⊗[k] K) F_K c).symm

private theorem functionFieldEquivOfIsPullback_germToFunctionField (hxt : Transcendental k x)
    (H : IsPullback g (Y ↘ Spec (.of K)) (twoChartModel hF hx ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hU : Nonempty (pullbackFiniteChart H ''ᵁ ⊤))
    (a : Γ(Y, pullbackFiniteChart H ''ᵁ ⊤)) :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
    letI : Algebra (finiteChartRing k F x ⊗[k] K) F_K :=
      tensorSubringAlgebra (k := k) (F := F) (K := K) (F_K := F_K)
    functionFieldEquivOfIsPullback (F_K := F_K) hxt H (Y.germToFunctionField _ a) =
      algebraMap (finiteChartRing k F x ⊗[k] K) F_K
        (pullbackFiniteChartSectionsEquiv H a) := by
  have := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  have := isFractionRing_holomorphyRing_setOf_mem hF hxt
  have := isDomain_tensorProduct (hF := hF) (hx := hx) hxt K
  let _ : Algebra (finiteChartRing k F x ⊗[k] K) F_K :=
    tensorSubringAlgebra (k := k) (F := F) (K := K) (F_K := F_K)
  have : IsFractionRing (finiteChartRing k F x ⊗[k] K) F_K :=
    isFractionRing_tensorSubring (k := k) (F := F) (K := K) (F_K := F_K)
  have := functionField_isFractionRing_of_isAffineOpen Y (pullbackFiniteChart H ''ᵁ ⊤)
    ((isAffineOpen_top _).image_of_isOpenImmersion (pullbackFiniteChart H))
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a

/-- **Under `functionFieldEquivOfIsPullback`, pulling a rational function `z ∈ F` back along
`g : Y ⟶ twoChartModel hF hx` gives `algebraMap F F_K z`.** -/
@[simp]
theorem functionFieldEquivOfIsPullback_functionFieldMap [Algebra F F_K]
    [IsScalarTower F (F ⊗[k] K) F_K] (hxt : Transcendental k x)
    (H : IsPullback g (Y ↘ Spec (.of K)) (twoChartModel hF hx ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (z : F) :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
    haveI := isDominant_of_isPullback H
    functionFieldEquivOfIsPullback (F_K := F_K) hxt H
      (g.functionFieldMap ((functionFieldEquiv hxt).symm z)) = algebraMap F F_K z := by
  have := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  have := isDominant_of_isPullback H
  have := isFractionRing_holomorphyRing_setOf_mem hF hxt
  have := isDomain_tensorProduct (hF := hF) (hx := hx) hxt K
  let _ : Algebra (finiteChartRing k F x ⊗[k] K) F_K :=
    tensorSubringAlgebra (k := k) (F := F) (K := K) (F_K := F_K)
  have : IsFractionRing (finiteChartRing k F x ⊗[k] K) F_K :=
    isFractionRing_tensorSubring (k := k) (F := F) (K := K) (F_K := F_K)
  have : Nontrivial (finiteChartRing k F x ⊗[k] K) :=
    (IsFractionRing.nontrivial_iff_nontrivial (finiteChartRing k F x ⊗[k] K) F_K).mpr inferInstance
  have hU : Nonempty (pullbackFiniteChart H ''ᵁ ⊤) :=
    ⟨⟨pullbackFiniteChart H (Classical.arbitrary _), ⟨_, trivial, rfl⟩⟩⟩
  have hsec (s : Γ(twoChartModel hF hx, ιFinite hF hx ''ᵁ ⊤)) :
      functionFieldEquivOfIsPullback (F_K := F_K) hxt H
        (g.functionFieldMap
          ((functionFieldEquiv hxt).symm (finiteChartSectionsEquiv hF hx s))) =
        algebraMap F F_K (finiteChartSectionsEquiv hF hx s) := by
    have hgerm : (functionFieldEquiv hxt).symm (finiteChartSectionsEquiv hF hx s : F) =
        (twoChartModel hF hx).germToFunctionField _ s := by
      rw [← functionFieldEquiv_germToFunctionField hxt s, AlgEquiv.symm_apply_apply]
    have hmap := congr($(Scheme.Hom.germToFunctionField_functionFieldMap g
      (ιFinite hF hx ''ᵁ ⊤)) s)
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hmap
    have hres : Y.germToFunctionField _ (g.app (ιFinite hF hx ''ᵁ ⊤) s) =
        Y.germToFunctionField _
          (g.appLE _ _ (image_pullbackFiniteChart_top_le_preimage H) s) := by
      rw [Scheme.Hom.appLE, CategoryTheory.comp_apply, TopCat.Presheaf.germ_res_apply]
    rw [hgerm, hmap, hres, functionFieldEquivOfIsPullback_germToFunctionField hxt H hU,
      pullbackFiniteChartSectionsEquiv_appLE_fst H]
    exact (IsScalarTower.algebraMap_apply F (F ⊗[k] K) F_K
      (finiteChartSectionsEquiv hF hx s : F)).symm
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := finiteChartRing k F x) z
  obtain ⟨s, rfl⟩ := (finiteChartSectionsEquiv hF hx).surjective a
  obtain ⟨t, rfl⟩ := (finiteChartSectionsEquiv hF hx).surjective b
  simp only [map_div₀, Subalgebra.algebraMap_apply, hsec]

omit [Algebra (F ⊗[k] K) F_K] [Algebra K F_K] [IsScalarTower K (F ⊗[k] K) F_K]
  [IsFractionRing (F ⊗[k] K) F_K] in
/-- **The base change of a geometrically integral two-chart model to any field extension `K / k` is
a curve over `K`.** -/
theorem isCurveOver_of_isPullback (hxt : Transcendental k x)
    (H : IsPullback g (Y ↘ Spec (.of K)) (twoChartModel hF hx ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    Y.IsCurveOver K := by
  have := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  have : IsProper (Y ↘ Spec (.of K)) :=
    MorphismProperty.of_isPullback (P := @IsProper) H inferInstance
  have := isDomain_tensorProduct (hF := hF) (hx := hx) hxt K
  let e := functionFieldEquivOfIsPullback (F_K := FractionRing (F ⊗[k] K)) hxt H
  have hFK : IsFunctionField K (FractionRing (F ⊗[k] K)) := hF.of_isFractionRing_tensorProduct
  have hY : IsFunctionField K Y.functionField := by
    have : Algebra.EssFiniteType K Y.functionField := essFiniteType_functionField K
    rw [isFunctionField_iff_trdeg_eq_one, e.trdeg_eq, hFK.trdeg_eq_one]
  exact ⟨(isFunctionField_functionField_iff K).mp hY⟩

include hF hx in
/-- **Exact constants persist under arbitrary field extension**: for any field extension `K / k`
(algebraic or transcendental) and any fraction field `F_K` of `F ⊗[k] K`, `K` is integrally closed
in `F_K`. -/
theorem isIntegrallyClosedIn_of_isFractionRing_tensorProduct (hxt : Transcendental k x) :
    IsIntegrallyClosedIn K F_K := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let _ : (pullback (twoChartModel hF hx ↘ Spec (.of k)) s).Over (Spec (.of K)) :=
    ⟨pullback.snd _ _⟩
  have H : IsPullback (pullback.fst _ _)
      (pullback (twoChartModel hF hx ↘ Spec (.of k)) s ↘ Spec (.of K))
      (twoChartModel hF hx ↘ Spec (.of k)) s := IsPullback.of_hasPullback _ _
  have := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  have : GeometricallyIntegral (pullback (twoChartModel hF hx ↘ Spec (.of k)) s ↘ Spec (.of K)) :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H inferInstance
  let e := functionFieldEquivOfIsPullback (F_K := F_K) hxt H
  exact isIntegrallyClosedIn_functionField_of_geometricallyIntegral.of_ringEquiv
    (RingEquiv.refl K) e.toRingEquiv e.commutes

include hF hx in
/-- Geometric reducedness of the function field persists in any fraction field `F_K` of `F ⊗[k] K`
for any field extension `K / k`. -/
theorem isGeometricallyReduced_of_isFractionRing_tensorProduct (hxt : Transcendental k x) :
    Algebra.IsGeometricallyReduced K F_K := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let _ : (pullback (twoChartModel hF hx ↘ Spec (.of k)) s).Over (Spec (.of K)) :=
    ⟨pullback.snd _ _⟩
  have H : IsPullback (pullback.fst _ _)
      (pullback (twoChartModel hF hx ↘ Spec (.of k)) s ↘ Spec (.of K))
      (twoChartModel hF hx ↘ Spec (.of k)) s := IsPullback.of_hasPullback _ _
  have := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  have : GeometricallyIntegral (pullback (twoChartModel hF hx ↘ Spec (.of k)) s ↘ Spec (.of K)) :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H inferInstance
  have : GeometricallyReduced (pullback (twoChartModel hF hx ↘ Spec (.of k)) s ↘ Spec (.of K)) :=
    inferInstance
  have := isGeometricallyReduced_functionField_of_geometricallyReduced (k := K)
    (X := pullback (twoChartModel hF hx ↘ Spec (.of k)) s)
  let e := functionFieldEquivOfIsPullback (F_K := F_K) hxt H
  exact .of_injective e.symm.toAlgHom e.symm.injective

/-- The two-chart model of `F_K = Frac(F ⊗[k] K)` over `K` remains geometrically integral over `K`,
for any field extension `K / k`. -/
theorem geometricallyIntegral_of_isFractionRing_tensorProduct [Algebra k F_K] [Algebra F F_K]
    [IsScalarTower k (F ⊗[k] K) F_K] [IsScalarTower F (F ⊗[k] K) F_K]
    [IsScalarTower k F F_K] [IsScalarTower k K F_K] (hxt : Transcendental k x) :
    GeometricallyIntegral
      (twoChartModel (hF.of_isFractionRing_tensorProduct (k := k) (K := K) (Q := F_K))
        (algebraMap_param_ne_zero (F_K := F_K) hx) ↘ Spec (.of K)) :=
  (geometricallyIntegral_iff (transcendental_algebraMap (k := k) (F_K := F_K) hxt)).mpr
    ⟨isIntegrallyClosedIn_of_isFractionRing_tensorProduct
       (k := k) (F_K := F_K) (hF := hF) (hx := hx) hxt,
     isGeometricallyReduced_of_isFractionRing_tensorProduct
       (k := k) (F_K := F_K) (hF := hF) (hx := hx) hxt⟩

end PullbackFunctionField

/-! ### Conservative smooth-model base change -/

section SmoothBaseChange

variable [Algebra (F ⊗[k] K) F_K] [Algebra k F_K] [Algebra F F_K] [Algebra K F_K]
  [IsScalarTower k (F ⊗[k] K) F_K] [IsScalarTower F (F ⊗[k] K) F_K]
  [IsScalarTower K (F ⊗[k] K) F_K] [IsScalarTower k F F_K] [IsScalarTower k K F_K]
  [IsFractionRing (F ⊗[k] K) F_K]
  [GeometricallyIntegral (twoChartModel hF hx ↘ Spec (.of k))]
  [Smooth (twoChartModel hF hx ↘ Spec (.of k))]

/-- **Conservative smooth-model base change**: when `twoChartModel hF hx` is smooth (equivalently,
geometrically regular) and geometrically integral over `k`, any base change `Y = X ×_k Spec K` along
an arbitrary field extension `K / k` is canonically `K`-isomorphic to the two-chart model of
`F_K = Frac(F ⊗[k] K)` built from `algebraMap F F_K x`. -/
noncomputable def isoTwoChartModelOfIsPullback (hxt : Transcendental k x)
    (H : IsPullback g (Y ↘ Spec (.of K)) (twoChartModel hF hx ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    Y ≅ twoChartModel (hF.of_isFractionRing_tensorProduct (k := k) (K := K) (Q := F_K))
      (algebraMap_param_ne_zero (F_K := F_K) hx) := by
  haveI := isCurveOver_of_isPullback hxt H
  haveI : Smooth (Y ↘ Spec (.of K)) := MorphismProperty.of_isPullback (P := @Smooth) H inferInstance
  haveI : IsRegular Y := IsRegular.of_smooth (Y ↘ Spec (.of K))
  exact Scheme.isoOfFunctionFieldAlgEquiv (Scheme.IsCurveOver.valuationRing_stalk K Y)
    valuationRing_stalk
    ((functionFieldEquiv (transcendental_algebraMap (k := k) (F_K := F_K) hxt)).trans
      (functionFieldEquivOfIsPullback (F_K := F_K) hxt H).symm)

/-- The forward morphism of `isoTwoChartModelOfIsPullback` is a morphism over `Spec K`. -/
instance isOver_isoTwoChartModelOfIsPullback_hom (hxt : Transcendental k x)
    (H : IsPullback g (Y ↘ Spec (.of K)) (twoChartModel hF hx ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    (isoTwoChartModelOfIsPullback (F_K := F_K) hxt H).hom.IsOver (Spec (.of K)) := by
  rw [isoTwoChartModelOfIsPullback]
  infer_instance

/-- The inverse morphism of `isoTwoChartModelOfIsPullback` is a morphism over `Spec K`. -/
instance isOver_isoTwoChartModelOfIsPullback_inv (hxt : Transcendental k x)
    (H : IsPullback g (Y ↘ Spec (.of K)) (twoChartModel hF hx ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    (isoTwoChartModelOfIsPullback (F_K := F_K) hxt H).inv.IsOver (Spec (.of K)) := by
  rw [isoTwoChartModelOfIsPullback]
  infer_instance

/-- Pulling back a rational function `w ∈ F_K` along `(isoTwoChartModelOfIsPullback hxt H).hom`
agrees with `(functionFieldEquivOfIsPullback hxt H).symm w`. -/
@[simp]
theorem functionFieldMap_isoTwoChartModelOfIsPullback_hom (hxt : Transcendental k x)
    (H : IsPullback g (Y ↘ Spec (.of K)) (twoChartModel hF hx ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (w : F_K) :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
    (isoTwoChartModelOfIsPullback (F_K := F_K) hxt H).hom.functionFieldMap
      ((functionFieldEquiv (transcendental_algebraMap (k := k) (F_K := F_K) hxt)).symm w) =
      (functionFieldEquivOfIsPullback (F_K := F_K) hxt H).symm w := by
  simp [isoTwoChartModelOfIsPullback]

/-- Pulling back a rational function `z ∈ F` from `twoChartModel hF hx` to `Y` and then along
`(isoTwoChartModelOfIsPullback hxt H).inv` gives `algebraMap F F_K z`. -/
@[simp]
theorem functionFieldEquiv_functionFieldMap_isoTwoChartModelOfIsPullback_inv
    (hxt : Transcendental k x)
    (H : IsPullback g (Y ↘ Spec (.of K)) (twoChartModel hF hx ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (z : F) :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
    haveI := isDominant_of_isPullback H
    functionFieldEquiv (transcendental_algebraMap (k := k) (F_K := F_K) hxt)
      ((isoTwoChartModelOfIsPullback (F_K := F_K) hxt H).inv.functionFieldMap
        (g.functionFieldMap ((functionFieldEquiv hxt).symm z))) = algebraMap F F_K z := by
  simp [isoTwoChartModelOfIsPullback]

/-- **Uniqueness of the smooth-model base-change isomorphism**: a dominant `K`-morphism from `Y` to
the two-chart model of `F_K` equals `(isoTwoChartModelOfIsPullback hxt H).hom` if and only if its
pullback of rational functions agrees with `(functionFieldEquivOfIsPullback hxt H).symm`. -/
theorem eq_isoTwoChartModelOfIsPullback_hom_iff (hxt : Transcendental k x)
    (H : IsPullback g (Y ↘ Spec (.of K)) (twoChartModel hF hx ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (f : Y ⟶ twoChartModel (hF.of_isFractionRing_tensorProduct (k := k) (K := K) (Q := F_K))
      (algebraMap_param_ne_zero (F_K := F_K) hx))
    [f.IsOver (Spec (.of K))] [IsDominant f] :
    haveI := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
    f = (isoTwoChartModelOfIsPullback (F_K := F_K) hxt H).hom ↔
      ∀ w : F_K, f.functionFieldMap
        ((functionFieldEquiv (transcendental_algebraMap (k := k) (F_K := F_K) hxt)).symm w) =
        (functionFieldEquivOfIsPullback (F_K := F_K) hxt H).symm w := by
  have := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  refine ⟨fun hf ↦ hf ▸ functionFieldMap_isoTwoChartModelOfIsPullback_hom hxt H, fun hf ↦ ?_⟩
  refine Scheme.Hom.ext_of_functionFieldMap_eq (Spec (.of K)) ?_
  ext a
  obtain ⟨w, rfl⟩ :=
    (functionFieldEquiv (transcendental_algebraMap (k := k) (F_K := F_K) hxt)).symm.surjective a
  rw [hf, functionFieldMap_isoTwoChartModelOfIsPullback_hom]

/-- When `twoChartModel hF hx` is smooth and geometrically integral over `k`, the two-chart model of
`F_K = Frac(F ⊗[k] K)` is smooth over `K`, for any field extension `K / k`. -/
theorem smooth_of_isFractionRing_tensorProduct (hxt : Transcendental k x) :
    Smooth (twoChartModel (hF.of_isFractionRing_tensorProduct (k := k) (K := K) (Q := F_K))
      (algebraMap_param_ne_zero (F_K := F_K) hx) ↘ Spec (.of K)) := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let _ : (pullback (twoChartModel hF hx ↘ Spec (.of k)) s).Over (Spec (.of K)) :=
    ⟨pullback.snd _ _⟩
  have H : IsPullback (pullback.fst _ _)
      (pullback (twoChartModel hF hx ↘ Spec (.of k)) s ↘ Spec (.of K))
      (twoChartModel hF hx ↘ Spec (.of k)) s := IsPullback.of_hasPullback _ _
  have : Smooth (pullback (twoChartModel hF hx ↘ Spec (.of k)) s ↘ Spec (.of K)) :=
    MorphismProperty.of_isPullback (P := @Smooth) H inferInstance
  let e := isoTwoChartModelOfIsPullback (F_K := F_K) hxt H
  have he : e.inv ≫ (pullback (twoChartModel hF hx ↘ Spec (.of k)) s ↘ Spec (.of K)) =
      (twoChartModel (hF.of_isFractionRing_tensorProduct (k := k) (K := K) (Q := F_K))
        (algebraMap_param_ne_zero (F_K := F_K) hx) ↘ Spec (.of K)) :=
    (Scheme.Hom.isOver_iff (Spec (.of K))).mp inferInstance
  rw [← he]
  infer_instance

/-- When `twoChartModel hF hx` is smooth and geometrically integral over `k`, the two-chart model of
`F_K = Frac(F ⊗[k] K)` is smooth of relative dimension one over `K`. -/
theorem smoothOfRelativeDimension_one_of_isFractionRing_tensorProduct (hxt : Transcendental k x) :
    SmoothOfRelativeDimension 1
      (twoChartModel (hF.of_isFractionRing_tensorProduct (k := k) (K := K) (Q := F_K))
        (algebraMap_param_ne_zero (F_K := F_K) hx) ↘ Spec (.of K)) := by
  have := smooth_of_isFractionRing_tensorProduct (k := k) (K := K) (F_K := F_K) (hF := hF)
    (hx := hx) hxt
  exact smoothOfRelativeDimension_one_of_smooth
    (transcendental_algebraMap (k := k) (F_K := F_K) hxt)

omit [Algebra (F ⊗[k] K) F_K] [Algebra k F_K] [Algebra F F_K] [Algebra K F_K]
  [IsScalarTower k (F ⊗[k] K) F_K] [IsScalarTower F (F ⊗[k] K) F_K]
  [IsScalarTower K (F ⊗[k] K) F_K] [IsScalarTower k F F_K] [IsScalarTower k K F_K]
  [IsFractionRing (F ⊗[k] K) F_K] in
/-- Explicit canonical isomorphism between
`pullback (twoChartModel hF hx ↘ Spec k) (Spec K ⟶ Spec k)` and the two-chart model of
`FractionRing (F ⊗[k] K)`. -/
noncomputable def pullbackIsoTwoChartModel (hxt : Transcendental k x) (K : Type u) [Field K]
    [Algebra k K] :
    letI := isDomain_tensorProduct (hF := hF) (hx := hx) hxt K
    pullback (twoChartModel hF hx ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≅
      twoChartModel
        (hF.of_isFractionRing_tensorProduct (k := k) (K := K) (Q := FractionRing (F ⊗[k] K)))
        (algebraMap_param_ne_zero (F_K := FractionRing (F ⊗[k] K)) hx) :=
  letI := isDomain_tensorProduct (hF := hF) (hx := hx) hxt K
  let _ : (pullback (twoChartModel hF hx ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Over (Spec (.of K)) :=
    ⟨pullback.snd _ _⟩
  isoTwoChartModelOfIsPullback (F_K := FractionRing (F ⊗[k] K)) hxt
    (IsPullback.of_hasPullback _ _)

end SmoothBaseChange

end BaseChange

end TauCeti.AlgebraicGeometry.twoChartModel
