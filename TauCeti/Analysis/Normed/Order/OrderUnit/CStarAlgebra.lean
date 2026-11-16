/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Space
public import TauCeti.Analysis.Normed.Order.OrderUnit.State
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic

/-!
# Self-adjoint parts of C⋆-algebras as order-unit spaces and the state dictionary

For a nonzero unital C⋆-algebra `A` equipped with its `StarOrderedRing` order, the real Banach
space `selfAdjoint A` of self-adjoint elements is a complete order-unit space with order unit `1`
(`TauCeti.OrderUnit.IsOrderUnitNorm.one_selfAdjoint`): a self-adjoint element `a` satisfies
`‖a‖ ≤ r` (for `0 ≤ r`) if and only if `-r • 1 ≤ a ≤ r • 1`.

Furthermore, states of `A` in the C⋆-algebra sense (`TauCeti.stateSpace A ⊆ WeakDual ℂ A`, or
equivalently positive complex-linear functionals `ω : A →P[ℂ] ℂ` normalized by `ω 1 = 1`) correspond
bijectively and weak-* homeomorphically to order-unit states of `(selfAdjoint A, 1)`
(`TauCeti.OrderUnit.stateSpace (1 : selfAdjoint A) ⊆ WeakDual ℝ (selfAdjoint A)`):

* `TauCeti.OrderUnit.restrictToSelfAdjoint`: weak-* continuous real-linear map
  `WeakDual ℂ A →L[ℝ] WeakDual ℝ (selfAdjoint A)` taking `ψ` to `a ↦ (ψ a).re` (which agrees with
  `ψ a` in `ℂ` whenever `ψ` is positive).
* `TauCeti.OrderUnit.complexifyFromSelfAdjoint`: weak-* continuous real-linear map
  `WeakDual ℝ (selfAdjoint A) →L[ℝ] WeakDual ℂ A` extending `φ` to the unique complex-linear
  functional `x ↦ φ (ℜ x) + I * φ (ℑ x)` agreeing with `φ` on `selfAdjoint A`.
* `TauCeti.OrderUnit.cstarStateSpaceHomeomorph`: the induced weak-* homeomorphism
  `TauCeti.stateSpace A ≃ₜ TauCeti.OrderUnit.stateSpace (1 : selfAdjoint A)`, preserving point
  evaluations on `selfAdjoint A`, real convex combinations, and pullbacks along unital star
  homomorphisms.
* `TauCeti.OrderUnit.cstarPositiveFunctionalEquivStateSpace`: equivalence between
  `{ω : A →P[ℂ] ℂ // ω 1 = 1}` and `TauCeti.OrderUnit.stateSpace (1 : selfAdjoint A)`.

## References

* R. V. Kadison, *A representation theory for commutative topological algebra*, Mem. Amer. Math.
  Soc. 7 (1951).
* M. A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), 559–600.
* M. A. Rieffel, *Gromov–Hausdorff distance for quantum metric spaces*, Mem. Amer. Math. Soc. 168
  (2004), no. 796.
-/

public section

open Complex Set WeakDual
open scoped ComplexOrder ComplexStarModule

namespace TauCeti.OrderUnit

/-! ### Order-unit norm on `selfAdjoint A` -/

section OrderUnitNorm

/-- **Self-adjoint part of a unital C⋆-algebra as an order-unit space.** For every nonzero unital
C⋆-algebra `A` with its C⋆-order, `(1 : selfAdjoint A)` satisfies `IsOrderUnitNorm`. -/
theorem IsOrderUnitNorm.one_selfAdjoint {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [Nontrivial A] :
    IsOrderUnitNorm (1 : selfAdjoint A) where
  norm_e := by
    rw [← AddSubgroup.norm_coe, selfAdjoint.val_one, norm_one]
  norm_le_iff a r hr := by
    rw [← AddSubgroup.norm_coe]
    refine ⟨fun hnr => ⟨?_, ?_⟩, fun ⟨hlow, hupp⟩ => ?_⟩
    · rw [← Subtype.coe_le_coe]
      have h1 : -(algebraMap ℝ A ‖(a : A)‖) ≤ (a : A) := a.2.neg_algebraMap_norm_le_self
      have h2 : (r : ℝ) • (1 : A) ≥ ‖(a : A)‖ • (1 : A) :=
        smul_le_smul_of_nonneg_right hnr zero_le_one
      rw [Algebra.algebraMap_eq_smul_one] at h1
      simpa [neg_smul] using (neg_le_neg h2).trans h1
    · rw [← Subtype.coe_le_coe]
      have h1 : (a : A) ≤ algebraMap ℝ A ‖(a : A)‖ := a.2.le_algebraMap_norm_self
      rw [Algebra.algebraMap_eq_smul_one] at h1
      exact h1.trans (smul_le_smul_of_nonneg_right hnr zero_le_one)
    · rw [← Subtype.coe_le_coe] at hlow hupp
      have hbound : ‖(a : A)‖ ≤ max ‖((-r • (1 : selfAdjoint A) : selfAdjoint A) : A)‖
          ‖((r • (1 : selfAdjoint A) : selfAdjoint A) : A)‖ :=
        a.2.norm_le_max_of_le_of_le hlow hupp
      have hnorm_pos : ‖((r • (1 : selfAdjoint A) : selfAdjoint A) : A)‖ = r := by
        rw [selfAdjoint.val_smul, selfAdjoint.val_one, norm_smul, Real.norm_of_nonneg hr,
          norm_one, mul_one]
      have hnorm_neg : ‖((-r • (1 : selfAdjoint A) : selfAdjoint A) : A)‖ = r := by
        rw [neg_smul, AddSubgroup.coe_neg, norm_neg, hnorm_pos]
      rwa [hnorm_neg, hnorm_pos, max_self] at hbound

end OrderUnitNorm

/-! ### Restriction and complexification between `WeakDual ℂ A` and `WeakDual ℝ (selfAdjoint A)` -/

section WeakDualDictionary

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Restrict a functional in `WeakDual ℂ A` to `selfAdjoint A` by taking real parts, as a weak-*
continuous real-linear map `WeakDual ℂ A →L[ℝ] WeakDual ℝ (selfAdjoint A)`. On positive functionals
the imaginary part vanishes on `selfAdjoint A`, so this is literally restriction of scalars. -/
noncomputable def restrictToSelfAdjoint (A : Type*) [NonUnitalCStarAlgebra A] :
    WeakDual ℂ A →L[ℝ] WeakDual ℝ (selfAdjoint A) where
  toFun ψ := StrongDual.toWeakDual <|
    Complex.reCLM.comp
      (((toStrongDual ψ).restrictScalars ℝ).comp
        ⟨(selfAdjoint.submodule ℝ A).subtype, continuous_subtype_val⟩)
  map_add' _ _ := rfl
  map_smul' r ψ := DFunLike.ext _ _ fun a => by
    simp
  cont := continuous_of_continuous_eval fun a =>
    Complex.continuous_re.comp (eval_continuous (a : A))

@[simp]
theorem restrictToSelfAdjoint_apply (ψ : WeakDual ℂ A) (a : selfAdjoint A) :
    restrictToSelfAdjoint A ψ a = (ψ (a : A)).re :=
  (rfl)

private noncomputable def complexifyStrongDual (φ : StrongDual ℝ (selfAdjoint A)) :
    StrongDual ℂ A :=
  LinearMap.mkContinuous
    { toFun := fun x => (φ (ℜ x) : ℂ) + I * (φ (ℑ x) : ℂ)
      map_add' := fun x y => by
        simp only [map_add, ofReal_add]
        ring
      map_smul' := fun z x => by
        apply Complex.ext
        · simp [realPart_smul, imaginaryPart_smul]
        · simp [realPart_smul, imaginaryPart_smul] }
    (2 * ‖φ‖)
    fun x => by
      have hre : ‖(φ (ℜ x) : ℂ)‖ ≤ ‖φ‖ * ‖x‖ := by
        rw [Complex.norm_real]
        exact (φ.le_opNorm (ℜ x)).trans
          (mul_le_mul_of_nonneg_left (realPart.norm_le x) (norm_nonneg φ))
      have him : ‖I * (φ (ℑ x) : ℂ)‖ ≤ ‖φ‖ * ‖x‖ := by
        rw [norm_mul, norm_I, one_mul, Complex.norm_real]
        exact (φ.le_opNorm (ℑ x)).trans
          (mul_le_mul_of_nonneg_left (imaginaryPart.norm_le x) (norm_nonneg φ))
      calc
        ‖(φ (ℜ x) : ℂ) + I * (φ (ℑ x) : ℂ)‖
          ≤ ‖(φ (ℜ x) : ℂ)‖ + ‖I * (φ (ℑ x) : ℂ)‖ := norm_add_le _ _
        _ ≤ ‖φ‖ * ‖x‖ + ‖φ‖ * ‖x‖ := add_le_add hre him
        _ = 2 * ‖φ‖ * ‖x‖ := by ring

@[simp]
private theorem complexifyStrongDual_apply (φ : StrongDual ℝ (selfAdjoint A)) (x : A) :
    complexifyStrongDual φ x = (φ (ℜ x) : ℂ) + I * (φ (ℑ x) : ℂ) :=
  rfl

/-- Extend a real functional `φ ∈ WeakDual ℝ (selfAdjoint A)` to the complex-linear functional
`x ↦ φ (ℜ x) + I * φ (ℑ x)` in `WeakDual ℂ A`, as a weak-* continuous real-linear map. -/
noncomputable def complexifyFromSelfAdjoint (A : Type*) [NonUnitalCStarAlgebra A] :
    WeakDual ℝ (selfAdjoint A) →L[ℝ] WeakDual ℂ A where
  toFun φ := StrongDual.toWeakDual (complexifyStrongDual (toStrongDual φ))
  map_add' φ₁ φ₂ := DFunLike.ext _ _ fun x => by
    simp only [StrongDual.toWeakDual_apply, complexifyStrongDual_apply, map_add, add_apply,
      ofReal_add]
    ring
  map_smul' r φ := DFunLike.ext _ _ fun x => by
    simp only [StrongDual.toWeakDual_apply, complexifyStrongDual_apply, map_smul,
      RingHom.id_apply, smul_apply, smul_eq_mul, ofReal_mul, Complex.real_smul]
    ring
  cont := WeakDual.continuous_of_continuous_eval_re fun x => by
    have hre : (fun φ : WeakDual ℝ (selfAdjoint A) =>
        RCLike.re (StrongDual.toWeakDual (complexifyStrongDual (toStrongDual φ)) x)) =
        fun φ => φ (ℜ x) := by
      ext φ
      simp
    rw [hre]
    exact eval_continuous (ℜ x)

@[simp]
theorem complexifyFromSelfAdjoint_apply (φ : WeakDual ℝ (selfAdjoint A)) (x : A) :
    complexifyFromSelfAdjoint A φ x = (φ (ℜ x) : ℂ) + I * (φ (ℑ x) : ℂ) :=
  (rfl)

theorem complexifyFromSelfAdjoint_apply_selfAdjoint (φ : WeakDual ℝ (selfAdjoint A))
    (a : selfAdjoint A) :
    complexifyFromSelfAdjoint A φ (a : A) = φ a := by
  simp

@[simp]
theorem restrictToSelfAdjoint_complexifyFromSelfAdjoint (φ : WeakDual ℝ (selfAdjoint A)) :
    restrictToSelfAdjoint A (complexifyFromSelfAdjoint A φ) = φ := by
  refine DFunLike.ext _ _ fun a => ?_
  simp

/-- **Uniqueness of the complex-linear extension.** Any `ℂ`-linear functional `ψ` on `A` that agrees
with `φ` on `selfAdjoint A` equals `complexifyFromSelfAdjoint A φ`. -/
theorem eq_complexifyFromSelfAdjoint_of_forall_selfAdjoint (φ : WeakDual ℝ (selfAdjoint A))
    (ψ : WeakDual ℂ A) (h : ∀ a : selfAdjoint A, ψ (a : A) = φ a) :
    ψ = complexifyFromSelfAdjoint A φ := by
  refine DFunLike.ext _ _ fun x => ?_
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart x]
  rw [map_add, map_smul, smul_eq_mul, h (ℜ x), h (ℑ x), complexifyFromSelfAdjoint_apply]

/-- A positive functional `ψ ∈ WeakDual ℂ A` on a C⋆-algebra takes real values on
`selfAdjoint A`. -/
theorem im_apply_selfAdjoint_eq_zero_of_map_nonneg [PartialOrder A] [StarOrderedRing A]
    {ψ : WeakDual ℂ A} (hψ : ∀ x : A, 0 ≤ x → 0 ≤ ψ x) (a : selfAdjoint A) :
    (ψ (a : A)).im = 0 :=
  Complex.im_eq_zero_iff_isSelfAdjoint _ |>.mpr <|
    a.2.map' (PositiveLinearMap.mk₀ (toStrongDual ψ).toLinearMap hψ)

/-- On a positive functional `ψ ∈ WeakDual ℂ A`, `restrictToSelfAdjoint A ψ a` recovers `ψ a` in
`ℂ`. -/
theorem coe_restrictToSelfAdjoint_apply_of_map_nonneg [PartialOrder A] [StarOrderedRing A]
    {ψ : WeakDual ℂ A} (hψ : ∀ x : A, 0 ≤ x → 0 ≤ ψ x) (a : selfAdjoint A) :
    (restrictToSelfAdjoint A ψ a : ℂ) = ψ (a : A) := by
  apply Complex.ext
  · simp [restrictToSelfAdjoint_apply]
  · simp [im_apply_selfAdjoint_eq_zero_of_map_nonneg hψ a]

theorem complexifyFromSelfAdjoint_restrictToSelfAdjoint_of_map_nonneg [PartialOrder A]
    [StarOrderedRing A] {ψ : WeakDual ℂ A} (hψ : ∀ x : A, 0 ≤ x → 0 ≤ ψ x) :
    complexifyFromSelfAdjoint A (restrictToSelfAdjoint A ψ) = ψ :=
  (eq_complexifyFromSelfAdjoint_of_forall_selfAdjoint _ ψ fun a =>
    (coe_restrictToSelfAdjoint_apply_of_map_nonneg hψ a).symm).symm

end WeakDualDictionary

/-! ### Homeomorphism between C⋆-algebra states and order-unit states of `selfAdjoint A` -/

section UnitalStateDictionary

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Restricting a C⋆-algebra state `ψ ∈ TauCeti.stateSpace A` to `selfAdjoint A` produces an
order-unit state in `TauCeti.OrderUnit.stateSpace (1 : selfAdjoint A)`. -/
theorem mapsTo_restrictToSelfAdjoint_stateSpace :
    MapsTo (restrictToSelfAdjoint A) (TauCeti.stateSpace A)
      (stateSpace (1 : selfAdjoint A)) := by
  intro ψ hψ
  rw [mem_stateSpace_iff_map_nonneg]
  refine ⟨fun a ha => ?_, ?_⟩
  · rw [← Subtype.coe_le_coe, AddSubgroup.coe_zero] at ha
    rw [restrictToSelfAdjoint_apply]
    exact (Complex.nonneg_iff.mp (TauCeti.map_nonneg_of_mem_stateSpace hψ ha)).1
  · simp [TauCeti.map_one_of_mem_stateSpace hψ]

/-- Complexifying an order-unit state `φ ∈ TauCeti.OrderUnit.stateSpace (1 : selfAdjoint A)`
produces a C⋆-algebra state in `TauCeti.stateSpace A`. -/
theorem mapsTo_complexifyFromSelfAdjoint_stateSpace :
    MapsTo (complexifyFromSelfAdjoint A) (stateSpace (1 : selfAdjoint A))
      (TauCeti.stateSpace A) := by
  intro φ hφ
  rw [TauCeti.mem_stateSpace_iff_map_one]
  refine ⟨fun x hx => ?_, ?_⟩
  · have hx_sa : IsSelfAdjoint x := .of_nonneg hx
    have hre_nonneg : 0 ≤ (ℜ x : selfAdjoint A) := by
      rw [← Subtype.coe_le_coe, AddSubgroup.coe_zero, hx_sa.coe_realPart]
      exact hx
    rw [complexifyFromSelfAdjoint_apply, hx_sa.imaginaryPart, map_zero, ofReal_zero, mul_zero,
      add_zero, Complex.nonneg_iff]
    exact ⟨map_nonneg_of_mem_stateSpace hφ hre_nonneg, rfl⟩
  · rw [← selfAdjoint.val_one, complexifyFromSelfAdjoint_apply_selfAdjoint,
      apply_orderUnit_of_mem_stateSpace hφ, ofReal_one]

/-- **Weak-* homeomorphism between C⋆-algebra states and order-unit states of `selfAdjoint A`.** -/
noncomputable def cstarStateSpaceHomeomorph (A : Type*) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] :
    TauCeti.stateSpace A ≃ₜ stateSpace (1 : selfAdjoint A) where
  toFun ψ := ⟨restrictToSelfAdjoint A ψ.1, mapsTo_restrictToSelfAdjoint_stateSpace ψ.2⟩
  invFun φ := ⟨complexifyFromSelfAdjoint A φ.1, mapsTo_complexifyFromSelfAdjoint_stateSpace φ.2⟩
  left_inv ψ := Subtype.ext <|
    complexifyFromSelfAdjoint_restrictToSelfAdjoint_of_map_nonneg
      (fun _ hx => TauCeti.map_nonneg_of_mem_stateSpace ψ.2 hx)
  right_inv φ := Subtype.ext (restrictToSelfAdjoint_complexifyFromSelfAdjoint φ.1)
  continuous_toFun :=
    ((restrictToSelfAdjoint A).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((complexifyFromSelfAdjoint A).continuous.comp continuous_subtype_val).subtype_mk _

theorem coe_cstarStateSpaceHomeomorph_apply (ψ : TauCeti.stateSpace A) (a : selfAdjoint A) :
    ((cstarStateSpaceHomeomorph A ψ).1 a : ℂ) = ψ.1 (a : A) :=
  coe_restrictToSelfAdjoint_apply_of_map_nonneg
    (fun _ hx => TauCeti.map_nonneg_of_mem_stateSpace ψ.2 hx) a

@[simp]
theorem cstarStateSpaceHomeomorph_apply_re (ψ : TauCeti.stateSpace A) (a : selfAdjoint A) :
    (cstarStateSpaceHomeomorph A ψ).1 a = (ψ.1 (a : A)).re :=
  restrictToSelfAdjoint_apply ψ.1 a

@[simp]
theorem cstarStateSpaceHomeomorph_symm_apply (φ : stateSpace (1 : selfAdjoint A)) (x : A) :
    ((cstarStateSpaceHomeomorph A).symm φ).1 x = (φ.1 (ℜ x) : ℂ) + I * (φ.1 (ℑ x) : ℂ) :=
  (rfl)

theorem cstarStateSpaceHomeomorph_symm_apply_selfAdjoint (φ : stateSpace (1 : selfAdjoint A))
    (a : selfAdjoint A) :
    ((cstarStateSpaceHomeomorph A).symm φ).1 (a : A) = φ.1 a := by
  simp

/-- Equivalence between normalized positive complex-linear functionals `{ω : A →P[ℂ] ℂ // ω 1 = 1}`
and order-unit states `stateSpace (1 : selfAdjoint A)`. -/
noncomputable def cstarPositiveFunctionalEquivStateSpace (A : Type*) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] :
    {ω : A →P[ℂ] ℂ // ω 1 = 1} ≃ stateSpace (1 : selfAdjoint A) :=
  { toFun := fun ω =>
      cstarStateSpaceHomeomorph A
        ⟨StrongDual.toWeakDual (ω.1 : A →L[ℂ] ℂ),
          TauCeti.mem_stateSpace_iff_map_one.mpr ⟨fun _ hx => ω.1.map_nonneg hx, ω.2⟩⟩
    invFun := fun φ =>
      let ψ := (cstarStateSpaceHomeomorph A).symm φ
      ⟨.mk₀ (toStrongDual ψ.1) fun _ hx => TauCeti.map_nonneg_of_mem_stateSpace ψ.2 hx,
        TauCeti.map_one_of_mem_stateSpace ψ.2⟩
    left_inv := fun ω => by
      apply Subtype.ext
      apply PositiveContinuousLinearMap.ext
      intro x
      have hψ : StrongDual.toWeakDual (ω.1 : A →L[ℂ] ℂ) ∈ TauCeti.stateSpace A :=
        TauCeti.mem_stateSpace_iff_map_one.mpr ⟨fun _ hx => ω.1.map_nonneg hx, ω.2⟩
      exact DFunLike.congr_fun
        (congrArg Subtype.val ((cstarStateSpaceHomeomorph A).symm_apply_apply ⟨_, hψ⟩)) x
    right_inv := fun φ => (cstarStateSpaceHomeomorph A).apply_symm_apply φ }

@[simp]
theorem coe_cstarPositiveFunctionalEquivStateSpace_apply (ω : {ω : A →P[ℂ] ℂ // ω 1 = 1})
    (a : selfAdjoint A) :
    ((cstarPositiveFunctionalEquivStateSpace A ω).1 a : ℂ) = ω.1 (a : A) :=
  coe_cstarStateSpaceHomeomorph_apply _ a

@[simp]
theorem cstarPositiveFunctionalEquivStateSpace_symm_apply_selfAdjoint
    (φ : stateSpace (1 : selfAdjoint A)) (a : selfAdjoint A) :
    ((cstarPositiveFunctionalEquivStateSpace A).symm φ).1 (a : A) = φ.1 a :=
  cstarStateSpaceHomeomorph_symm_apply_selfAdjoint φ a

end UnitalStateDictionary

end TauCeti.OrderUnit

namespace PositiveLinearMap

/-- Restrict an order-preserving `ℂ`-linear map `f : A → B` between C⋆-algebras (including positive
linear maps and star-algebra homomorphisms) to a real positive linear map
`selfAdjoint A →ₚ[ℝ] selfAdjoint B`. -/
def selfAdjointMap {A B F : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [FunLike F A B] [LinearMapClass F ℂ A B] [OrderHomClass F A B]
    (f : F) :
    selfAdjoint A →ₚ[ℝ] selfAdjoint B where
  toFun a := ⟨f (a : A), a.2.map' f⟩
  map_add' a b := Subtype.ext (map_add f (a : A) (b : A))
  map_smul' r a := Subtype.ext (by simp [← Complex.coe_smul])
  monotone' a b hab := by
    rw [← Subtype.coe_le_coe] at hab ⊢
    exact OrderHomClass.mono f hab

@[simp]
theorem coe_selfAdjointMap_apply {A B F : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [FunLike F A B] [LinearMapClass F ℂ A B] [OrderHomClass F A B]
    (f : F) (a : selfAdjoint A) :
    (selfAdjointMap f a : B) = f (a : A) :=
  (rfl)

end PositiveLinearMap

namespace TauCeti.OrderUnit

/-- **Naturality of the C⋆-state dictionary under unital star homomorphisms.** Restricting states to
`selfAdjoint` commutes with pulling back along a unital star homomorphism `f : A → B`. -/
theorem restrictToSelfAdjoint_pullbackFunctional
    {A B F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Nontrivial B]
    [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B] (f : F) (ψ : WeakDual ℂ B) :
    restrictToSelfAdjoint A (TauCeti.pullbackFunctional A f ψ) =
      pullbackFunctional
        (IsOrderUnitNorm.one_selfAdjoint (A := A))
        (IsOrderUnitNorm.one_selfAdjoint (A := B))
        (PositiveLinearMap.selfAdjointMap f)
        (restrictToSelfAdjoint B ψ) := by
  refine DFunLike.ext _ _ fun a => ?_
  simp

end TauCeti.OrderUnit
