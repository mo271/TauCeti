/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.RingTheory.Flat.Basic
import TauCeti.RingTheory.Flat.TensorProduct

/-!
# The fraction field of a tensor product of fields

If `F ⊗[k] K` is a domain, its fraction field is a compositum of the two factors,
with linearly disjoint images. Unlike the existential construction
`IntermediateField.LinearDisjoint.exists_field_of_isDomain`, these statements retain
an arbitrary specified fraction field and its scalar maps. This is useful when the
same fraction field must also be compared with localizations or geometric base change.

The right-factor algebra is Mathlib's `Algebra.TensorProduct.rightAlgebra`, installed
locally together with `right_isScalarTower`; all maps to the fraction field are the
usual scalar-tower maps. The linear-disjointness argument follows Jz Pan's
`Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective` in Mathlib,
using `Subalgebra.LinearDisjoint.include_range` and transport along the fraction map.

Under flatness hypotheses that are automatic over a base field `k`, injective algebra
maps `f : A₁ →ₐ[S] A₂` and `g : B₁ →ₐ[k] B₂` induce a canonical `S`-algebra map
`Q₁ →ₐ[S] Q₂` from any fraction ring `Q₁` of `A₁ ⊗[k] B₁` to any field `Q₂`
containing `A₂ ⊗[k] B₂` faithfully (in particular, any fraction field of
`A₂ ⊗[k] B₂`). It is uniquely characterized by its restrictions to the two tensor
factors, respects identity and composition, and specializes both to an `A`-algebra map
when the left factor `A` is fixed (`S = A`, `f = id`) and to a `K`-algebra map
`fractionRingTensorProductMapLeftAlgHom` when the right factor `K` is fixed (`g = id`,
requiring flatness of `K` over `k` alone).

## Main definitions

* `TauCeti.fractionRingTensorProductMapAlgHom`: the induced `S`-algebra map `Q₁ →ₐ[S] Q₂` on
  fraction rings from injective maps `f : A₁ →ₐ[S] A₂` and `g : B₁ →ₐ[k] B₂`.
* `TauCeti.fractionRingTensorProductMapLeftAlgHom`: the induced `K`-algebra map `Q₁ →ₐ[K] Q₂`
  from an injective `k`-algebra map `f : A₁ →ₐ[k] A₂` when the right factor `K` is fixed.

## Main results

* `TauCeti.adjoin_range_right_eq_top_of_isFractionRing_tensorProduct`: the two factors
  generate the fraction field as a field.
* `TauCeti.linearDisjoint_of_isFractionRing_tensorProduct`: the images of two field
  factors in a fraction field of their tensor product are linearly disjoint.
* `TauCeti.ringHom_eq_fractionRingTensorProductMapAlgHom` and
  `TauCeti.algHom_eq_fractionRingTensorProductMapAlgHom`: uniqueness of the induced
  fraction-ring map from agreement on the left and right scalar maps.
* `TauCeti.fractionRingTensorProductMapAlgHom_id` and
  `TauCeti.fractionRingTensorProductMapAlgHom_comp`: functoriality of
  `fractionRingTensorProductMapAlgHom` (and similarly for
  `fractionRingTensorProductMapLeftAlgHom`).

## References

* S. Lang, *Algebra*, the construction of linearly disjoint composita by tensor products.
-/

public section

open scoped TensorProduct

namespace TauCeti

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

section Generation

variable {k F K Q : Type*} [CommRing k] [Field F] [CommRing K] [Field Q]
  [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q]
  [Algebra F Q] [Algebra K Q]
  [IsScalarTower F (F ⊗[k] K) Q] [IsScalarTower K (F ⊗[k] K) Q]
  [IsFractionRing (F ⊗[k] K) Q]

include k in
/-- The two factors generate the fraction field of their tensor product as a field.
No algebraicity assumption on either factor is needed. -/
theorem adjoin_range_right_eq_top_of_isFractionRing_tensorProduct :
    IntermediateField.adjoin F (Set.range (algebraMap K Q)) = ⊤ := by
  have hleft : (algebraMap (F ⊗[k] K) Q) ∘
      (Algebra.TensorProduct.includeLeft : F →ₐ[k] F ⊗[k] K) = algebraMap F Q := by
    exact congrArg DFunLike.coe (IsScalarTower.algebraMap_eq F (F ⊗[k] K) Q).symm
  have hright : (algebraMap (F ⊗[k] K) Q) ∘
      (Algebra.TensorProduct.includeRight : K →ₐ[k] F ⊗[k] K) = algebraMap K Q := by
    exact congrArg DFunLike.coe (IsScalarTower.algebraMap_eq K (F ⊗[k] K) Q).symm
  have hs : (algebraMap (F ⊗[k] K) Q).range =
      Subring.closure (Set.range (algebraMap F Q) ∪ Set.range (algebraMap K Q)) := by
    rw [RingHom.range_eq_map,
      ← Algebra.TensorProduct.closure_range_union_range_eq_top k F K,
      RingHom.map_closure, Set.image_union, ← Set.range_comp, ← Set.range_comp,
      hleft, hright]
  have h := IsFractionRing.ringHom_fieldRange_eq_of_comp_eq_of_range_eq
    (f := RingHom.id Q) (g := algebraMap (F ⊗[k] K) Q) rfl hs
  apply IntermediateField.toSubfield_injective
  rw [IntermediateField.adjoin_toSubfield, ← h]
  exact RingHom.fieldRange_eq_top_iff.mpr Function.surjective_id

end Generation

section LinearDisjoint

variable {k F K Q : Type*} [Field k] [Field F] [Field K] [Field Q]
  [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q]
  [Algebra k Q] [Algebra F Q] [Algebra K Q]
  [IsScalarTower F (F ⊗[k] K) Q] [IsScalarTower K (F ⊗[k] K) Q]
  [IsScalarTower k F Q] [IsScalarTower k K Q]
  [IsFractionRing (F ⊗[k] K) Q]

/-- The images of the two factors in a fraction field of their tensor product are
linearly disjoint. This is the concrete fraction-field form of Mathlib's
`Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective`. -/
theorem linearDisjoint_of_isFractionRing_tensorProduct :
    (IsScalarTower.toAlgHom k K Q).fieldRange.LinearDisjoint F := by
  have : IsScalarTower k (F ⊗[k] K) Q := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k F Q, IsScalarTower.algebraMap_apply F (F ⊗[k] K) Q,
      ← IsScalarTower.algebraMap_apply k F (F ⊗[k] K)]
  let i := IsScalarTower.toAlgHom k (F ⊗[k] K) Q
  have hi : Function.Injective i := IsFractionRing.injective (F ⊗[k] K) Q
  have H := (Subalgebra.LinearDisjoint.include_range k F K).map i hi
  rw [IntermediateField.linearDisjoint_iff, AlgHom.fieldRange_toSubalgebra]
  have hleft : i.comp Algebra.TensorProduct.includeLeft = IsScalarTower.toAlgHom k F Q := by
    apply AlgHom.toRingHom_injective
    exact (IsScalarTower.algebraMap_eq F (F ⊗[k] K) Q).symm
  have hright : i.comp Algebra.TensorProduct.includeRight = IsScalarTower.toAlgHom k K Q := by
    apply AlgHom.toRingHom_injective
    exact (IsScalarTower.algebraMap_eq K (F ⊗[k] K) Q).symm
  simpa only [← AlgHom.range_comp, hleft, hright] using H.symm

end LinearDisjoint

section Functoriality

variable {k S A₁ B₁ A₂ B₂ : Type*} [CommRing k] [CommSemiring S] [Algebra k S]
  [CommRing A₁] [CommRing B₁] [CommRing A₂] [CommRing B₂]
  [Algebra k A₁] [Algebra S A₁] [IsScalarTower k S A₁] [Algebra k B₁]
  [Algebra k A₂] [Algebra S A₂] [IsScalarTower k S A₂] [Algebra k B₂]
  [Module.Flat k A₂] [Module.Flat k B₁]

private theorem comp_map_injective (Q₂ : Type*) [CommSemiring Q₂]
    [Algebra (A₂ ⊗[k] B₂) Q₂] [FaithfulSMul (A₂ ⊗[k] B₂) Q₂]
    [Algebra S Q₂] [IsScalarTower S (A₂ ⊗[k] B₂) Q₂]
    (f : A₁ →ₐ[S] A₂) (g : B₁ →ₐ[k] B₂)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective
      ((IsScalarTower.toAlgHom S (A₂ ⊗[k] B₂) Q₂).comp (Algebra.TensorProduct.map f g)) :=
  (FaithfulSMul.algebraMap_injective (A₂ ⊗[k] B₂) Q₂).comp
    (Algebra.TensorProduct.map_injective_of_flat_flat f g hf hg)

/-- Given injective algebra maps `f : A₁ →ₐ[S] A₂` and `g : B₁ →ₐ[k] B₂` (under
flatness conditions that hold automatically when `k` is a field), any fraction ring `Q₁` of
`A₁ ⊗[k] B₁` maps canonically as an `S`-algebra to any field `Q₂` faithfully containing
`A₂ ⊗[k] B₂` (in particular, any fraction field of `A₂ ⊗[k] B₂`). Taking `S = A` and
`f = AlgHom.id A A` gives an `A`-algebra map when the left factor `A` is fixed. -/
noncomputable def fractionRingTensorProductMapAlgHom (Q₁ Q₂ : Type*) [CommRing Q₁] [Field Q₂]
    [Algebra (A₁ ⊗[k] B₁) Q₁] [Algebra S Q₁] [IsScalarTower S (A₁ ⊗[k] B₁) Q₁]
    [IsFractionRing (A₁ ⊗[k] B₁) Q₁]
    [Algebra (A₂ ⊗[k] B₂) Q₂] [FaithfulSMul (A₂ ⊗[k] B₂) Q₂]
    [Algebra S Q₂] [IsScalarTower S (A₂ ⊗[k] B₂) Q₂]
    (f : A₁ →ₐ[S] A₂) (g : B₁ →ₐ[k] B₂)
    (hf : Function.Injective f) (hg : Function.Injective g) : Q₁ →ₐ[S] Q₂ :=
  let ψ : A₁ ⊗[k] B₁ →ₐ[S] Q₂ :=
    (IsScalarTower.toAlgHom S (A₂ ⊗[k] B₂) Q₂).comp (Algebra.TensorProduct.map f g)
  have hψ : Function.Injective ψ := comp_map_injective Q₂ f g hf hg
  IsLocalization.liftAlgHom (M := nonZeroDivisors (A₁ ⊗[k] B₁)) (S := Q₁) (f := ψ)
    fun y ↦ by
      have : Nontrivial (A₁ ⊗[k] B₁) := ψ.toRingHom.domain_nontrivial
      exact (map_ne_zero_of_mem_nonZeroDivisors ψ hψ y.2).isUnit

section Properties

variable (Q₁ Q₂ : Type*) [CommRing Q₁] [Field Q₂]
  [Algebra (A₁ ⊗[k] B₁) Q₁] [Algebra S Q₁] [IsScalarTower S (A₁ ⊗[k] B₁) Q₁]
  [IsFractionRing (A₁ ⊗[k] B₁) Q₁]
  [Algebra (A₂ ⊗[k] B₂) Q₂] [FaithfulSMul (A₂ ⊗[k] B₂) Q₂]
  [Algebra S Q₂] [IsScalarTower S (A₂ ⊗[k] B₂) Q₂]
  (f : A₁ →ₐ[S] A₂) (g : B₁ →ₐ[k] B₂)
  (hf : Function.Injective f) (hg : Function.Injective g)

@[simp]
theorem fractionRingTensorProductMapAlgHom_algebraMap (x : A₁ ⊗[k] B₁) :
    fractionRingTensorProductMapAlgHom Q₁ Q₂ f g hf hg (algebraMap (A₁ ⊗[k] B₁) Q₁ x) =
      algebraMap (A₂ ⊗[k] B₂) Q₂ (Algebra.TensorProduct.map f g x) := by
  simp [fractionRingTensorProductMapAlgHom]

theorem fractionRingTensorProductMapAlgHom_algebraMap_tmul (a : A₁) (b : B₁) :
    fractionRingTensorProductMapAlgHom Q₁ Q₂ f g hf hg
        (algebraMap (A₁ ⊗[k] B₁) Q₁ (a ⊗ₜ[k] b)) =
      algebraMap (A₂ ⊗[k] B₂) Q₂ (f a ⊗ₜ[k] g b) := by
  rw [fractionRingTensorProductMapAlgHom_algebraMap, Algebra.TensorProduct.map_tmul]

@[simp]
theorem fractionRingTensorProductMapAlgHom_algebraMap_left [Algebra A₁ Q₁]
    [IsScalarTower A₁ (A₁ ⊗[k] B₁) Q₁] [Algebra A₂ Q₂]
    [IsScalarTower A₂ (A₂ ⊗[k] B₂) Q₂] (a : A₁) :
    fractionRingTensorProductMapAlgHom Q₁ Q₂ f g hf hg (algebraMap A₁ Q₁ a) =
      algebraMap A₂ Q₂ (f a) := by
  rw [IsScalarTower.algebraMap_apply A₁ (A₁ ⊗[k] B₁) Q₁,
    fractionRingTensorProductMapAlgHom_algebraMap,
    IsScalarTower.algebraMap_apply A₂ (A₂ ⊗[k] B₂) Q₂]
  simp

@[simp]
theorem fractionRingTensorProductMapAlgHom_algebraMap_right [Algebra B₁ Q₁]
    [IsScalarTower B₁ (A₁ ⊗[k] B₁) Q₁] [Algebra B₂ Q₂]
    [IsScalarTower B₂ (A₂ ⊗[k] B₂) Q₂] (b : B₁) :
    fractionRingTensorProductMapAlgHom Q₁ Q₂ f g hf hg (algebraMap B₁ Q₁ b) =
      algebraMap B₂ Q₂ (g b) := by
  rw [IsScalarTower.algebraMap_apply B₁ (A₁ ⊗[k] B₁) Q₁,
    fractionRingTensorProductMapAlgHom_algebraMap,
    IsScalarTower.algebraMap_apply B₂ (A₂ ⊗[k] B₂) Q₂]
  simp [Algebra.TensorProduct.right_algebraMap_apply]

theorem fractionRingTensorProductMapAlgHom_injective :
    Function.Injective (fractionRingTensorProductMapAlgHom Q₁ Q₂ f g hf hg) := by
  rw [fractionRingTensorProductMapAlgHom, IsLocalization.coe_liftAlgHom,
    IsLocalization.lift_injective_iff]
  intro x y
  exact (IsFractionRing.injective (A₁ ⊗[k] B₁) Q₁).eq_iff.trans
    (comp_map_injective Q₂ f g hf hg).eq_iff.symm

/-- **Uniqueness of the induced map on fraction rings of tensor products.** Any ring
homomorphism `Q₁ →+* Q₂` whose restrictions to `A₁` and `B₁` agree with `f` and `g` equals
`fractionRingTensorProductMapAlgHom`. -/
theorem ringHom_eq_fractionRingTensorProductMapAlgHom
    [Algebra A₁ Q₁] [IsScalarTower A₁ (A₁ ⊗[k] B₁) Q₁]
    [Algebra B₁ Q₁] [IsScalarTower B₁ (A₁ ⊗[k] B₁) Q₁]
    [Algebra A₂ Q₂] [IsScalarTower A₂ (A₂ ⊗[k] B₂) Q₂]
    [Algebra B₂ Q₂] [IsScalarTower B₂ (A₂ ⊗[k] B₂) Q₂]
    {Φ : Q₁ →+* Q₂}
    (hA : ∀ a : A₁, Φ (algebraMap A₁ Q₁ a) = algebraMap A₂ Q₂ (f a))
    (hB : ∀ b : B₁, Φ (algebraMap B₁ Q₁ b) = algebraMap B₂ Q₂ (g b)) :
    Φ = (fractionRingTensorProductMapAlgHom Q₁ Q₂ f g hf hg).toRingHom := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (A₁ ⊗[k] B₁)) <|
    Algebra.TensorProduct.ringHom_ext
      (f := Φ.comp (algebraMap (A₁ ⊗[k] B₁) Q₁))
      (g := (fractionRingTensorProductMapAlgHom Q₁ Q₂ f g hf hg).toRingHom.comp
        (algebraMap (A₁ ⊗[k] B₁) Q₁))
      (RingHom.ext fun a ↦ ?_) (RingHom.ext fun b ↦ ?_)
  · simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeLeftRingHom_apply,
      fractionRingTensorProductMapAlgHom_algebraMap_tmul, map_one,
      IsScalarTower.algebraMap_apply A₁ (A₁ ⊗[k] B₁) Q₁,
      IsScalarTower.algebraMap_apply A₂ (A₂ ⊗[k] B₂) Q₂,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] using hA a
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply,
      ← Algebra.TensorProduct.right_algebraMap_apply,
      ← IsScalarTower.algebraMap_apply B₁ (A₁ ⊗[k] B₁) Q₁,
      fractionRingTensorProductMapAlgHom_algebraMap_right, hB b]

/-- Any `S`-algebra map `Q₁ →ₐ[S] Q₂` agreeing with `f` on `A₁` and `g` on `B₁` equals
`fractionRingTensorProductMapAlgHom`. -/
theorem algHom_eq_fractionRingTensorProductMapAlgHom
    [Algebra A₁ Q₁] [IsScalarTower A₁ (A₁ ⊗[k] B₁) Q₁]
    [Algebra B₁ Q₁] [IsScalarTower B₁ (A₁ ⊗[k] B₁) Q₁]
    [Algebra A₂ Q₂] [IsScalarTower A₂ (A₂ ⊗[k] B₂) Q₂]
    [Algebra B₂ Q₂] [IsScalarTower B₂ (A₂ ⊗[k] B₂) Q₂]
    {Φ : Q₁ →ₐ[S] Q₂}
    (hA : ∀ a : A₁, Φ (algebraMap A₁ Q₁ a) = algebraMap A₂ Q₂ (f a))
    (hB : ∀ b : B₁, Φ (algebraMap B₁ Q₁ b) = algebraMap B₂ Q₂ (g b)) :
    Φ = fractionRingTensorProductMapAlgHom Q₁ Q₂ f g hf hg :=
  AlgHom.toRingHom_injective (ringHom_eq_fractionRingTensorProductMapAlgHom Q₁ Q₂ f g hf hg hA hB)

end Properties

@[simp]
theorem fractionRingTensorProductMapAlgHom_id [Module.Flat k A₁] (Q : Type*) [Field Q]
    [Algebra (A₁ ⊗[k] B₁) Q] [Algebra S Q] [IsScalarTower S (A₁ ⊗[k] B₁) Q]
    [IsFractionRing (A₁ ⊗[k] B₁) Q]
    {hf : Function.Injective (AlgHom.id S A₁)} {hg : Function.Injective (AlgHom.id k B₁)} :
    fractionRingTensorProductMapAlgHom Q Q (AlgHom.id S A₁) (AlgHom.id k B₁) hf hg =
      AlgHom.id S Q :=
  AlgHom.toRingHom_injective <|
    IsLocalization.ringHom_ext (nonZeroDivisors (A₁ ⊗[k] B₁)) <| RingHom.ext fun x ↦ by simp

theorem fractionRingTensorProductMapAlgHom_comp {A₃ B₃ : Type*} [CommRing A₃] [CommRing B₃]
    [Algebra k A₃] [Algebra S A₃] [IsScalarTower k S A₃] [Algebra k B₃]
    [Module.Flat k A₃] [Module.Flat k B₂]
    (Q₁ Q₂ Q₃ : Type*) [CommRing Q₁] [Field Q₂] [Field Q₃]
    [Algebra (A₁ ⊗[k] B₁) Q₁] [Algebra S Q₁] [IsScalarTower S (A₁ ⊗[k] B₁) Q₁]
    [IsFractionRing (A₁ ⊗[k] B₁) Q₁]
    [Algebra (A₂ ⊗[k] B₂) Q₂] [Algebra S Q₂] [IsScalarTower S (A₂ ⊗[k] B₂) Q₂]
    [IsFractionRing (A₂ ⊗[k] B₂) Q₂]
    [Algebra (A₃ ⊗[k] B₃) Q₃] [FaithfulSMul (A₃ ⊗[k] B₃) Q₃]
    [Algebra S Q₃] [IsScalarTower S (A₃ ⊗[k] B₃) Q₃]
    (f₁ : A₁ →ₐ[S] A₂) (g₁ : B₁ →ₐ[k] B₂)
    (f₂ : A₂ →ₐ[S] A₃) (g₂ : B₂ →ₐ[k] B₃)
    (hf₁ : Function.Injective f₁) (hg₁ : Function.Injective g₁)
    (hf₂ : Function.Injective f₂) (hg₂ : Function.Injective g₂) :
    (fractionRingTensorProductMapAlgHom Q₂ Q₃ f₂ g₂ hf₂ hg₂).comp
        (fractionRingTensorProductMapAlgHom Q₁ Q₂ f₁ g₁ hf₁ hg₁) =
      fractionRingTensorProductMapAlgHom Q₁ Q₃ (f₂.comp f₁) (g₂.comp g₁)
        ((AlgHom.coe_comp f₂ f₁).symm ▸ hf₂.comp hf₁)
        ((AlgHom.coe_comp g₂ g₁).symm ▸ hg₂.comp hg₁) :=
  AlgHom.toRingHom_injective <|
    IsLocalization.ringHom_ext (nonZeroDivisors (A₁ ⊗[k] B₁)) <| RingHom.ext fun x ↦ by
      simp [Algebra.TensorProduct.map_comp]

end Functoriality

section FixedRight

variable {k A₁ A₂ : Type*} [CommRing k] [CommRing A₁] [CommRing A₂]
  [Algebra k A₁] [Algebra k A₂]

private def mapLeftAlgHom (K : Type*) [CommRing K] [Algebra k K] (f : A₁ →ₐ[k] A₂) :
    A₁ ⊗[k] K →ₐ[K] A₂ ⊗[k] K :=
  { (Algebra.TensorProduct.map f (AlgHom.id k K)).toRingHom with
    commutes' := fun c ↦ by simp [Algebra.TensorProduct.right_algebraMap_apply] }

@[simp]
private theorem mapLeftAlgHom_apply (K : Type*) [CommRing K] [Algebra k K]
    (f : A₁ →ₐ[k] A₂) (x : A₁ ⊗[k] K) :
    mapLeftAlgHom K f x = Algebra.TensorProduct.map f (AlgHom.id k K) x := rfl

private theorem comp_mapLeftAlgHom_injective (K Q₂ : Type*) [CommRing K] [Algebra k K]
    [Module.Flat k K] [CommSemiring Q₂] [Algebra (A₂ ⊗[k] K) Q₂] [FaithfulSMul (A₂ ⊗[k] K) Q₂]
    [Algebra K Q₂] [IsScalarTower K (A₂ ⊗[k] K) Q₂]
    (f : A₁ →ₐ[k] A₂) (hf : Function.Injective f) :
    Function.Injective ((IsScalarTower.toAlgHom K (A₂ ⊗[k] K) Q₂).comp (mapLeftAlgHom K f)) := by
  refine (FaithfulSMul.algebraMap_injective (A₂ ⊗[k] K) Q₂).comp ?_
  have hmap : Function.Injective (Algebra.TensorProduct.map f (AlgHom.id k K)) := by
    rw [← AlgHom.coe_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      TensorProduct.AlgebraTensorModule.map_eq]
    exact Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf
  exact hmap

/-- When the right factor `K` is fixed, an injective `k`-algebra map `f : A₁ →ₐ[k] A₂`
induces a `K`-algebra map `Q₁ →ₐ[K] Q₂` on fraction rings (requiring flatness of `K` over
`k` alone), even though `f` itself is only `k`-linear. -/
noncomputable def fractionRingTensorProductMapLeftAlgHom (K Q₁ Q₂ : Type*) [CommRing K]
    [Algebra k K] [Module.Flat k K] [CommRing Q₁] [Field Q₂]
    [Algebra (A₁ ⊗[k] K) Q₁] [Algebra K Q₁] [IsScalarTower K (A₁ ⊗[k] K) Q₁]
    [IsFractionRing (A₁ ⊗[k] K) Q₁]
    [Algebra (A₂ ⊗[k] K) Q₂] [FaithfulSMul (A₂ ⊗[k] K) Q₂]
    [Algebra K Q₂] [IsScalarTower K (A₂ ⊗[k] K) Q₂]
    (f : A₁ →ₐ[k] A₂) (hf : Function.Injective f) : Q₁ →ₐ[K] Q₂ :=
  let ψ : A₁ ⊗[k] K →ₐ[K] Q₂ :=
    (IsScalarTower.toAlgHom K (A₂ ⊗[k] K) Q₂).comp (mapLeftAlgHom K f)
  have hψ : Function.Injective ψ := comp_mapLeftAlgHom_injective K Q₂ f hf
  IsLocalization.liftAlgHom (M := nonZeroDivisors (A₁ ⊗[k] K)) (S := Q₁) (f := ψ)
    fun y ↦ by
      have : Nontrivial (A₁ ⊗[k] K) := ψ.toRingHom.domain_nontrivial
      exact (map_ne_zero_of_mem_nonZeroDivisors ψ hψ y.2).isUnit

section Properties

variable (K Q₁ Q₂ : Type*) [CommRing K] [Algebra k K] [Module.Flat k K]
  [CommRing Q₁] [Field Q₂]
  [Algebra (A₁ ⊗[k] K) Q₁] [Algebra K Q₁] [IsScalarTower K (A₁ ⊗[k] K) Q₁]
  [IsFractionRing (A₁ ⊗[k] K) Q₁]
  [Algebra (A₂ ⊗[k] K) Q₂] [FaithfulSMul (A₂ ⊗[k] K) Q₂]
  [Algebra K Q₂] [IsScalarTower K (A₂ ⊗[k] K) Q₂]
  (f : A₁ →ₐ[k] A₂) (hf : Function.Injective f)

@[simp]
theorem fractionRingTensorProductMapLeftAlgHom_algebraMap (x : A₁ ⊗[k] K) :
    fractionRingTensorProductMapLeftAlgHom K Q₁ Q₂ f hf (algebraMap (A₁ ⊗[k] K) Q₁ x) =
      algebraMap (A₂ ⊗[k] K) Q₂ (Algebra.TensorProduct.map f (AlgHom.id k K) x) := by
  simp [fractionRingTensorProductMapLeftAlgHom]

theorem fractionRingTensorProductMapLeftAlgHom_algebraMap_tmul (a : A₁) (c : K) :
    fractionRingTensorProductMapLeftAlgHom K Q₁ Q₂ f hf
        (algebraMap (A₁ ⊗[k] K) Q₁ (a ⊗ₜ[k] c)) =
      algebraMap (A₂ ⊗[k] K) Q₂ (f a ⊗ₜ[k] c) := by
  rw [fractionRingTensorProductMapLeftAlgHom_algebraMap, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply]

@[simp]
theorem fractionRingTensorProductMapLeftAlgHom_algebraMap_left [Algebra A₁ Q₁]
    [IsScalarTower A₁ (A₁ ⊗[k] K) Q₁] [Algebra A₂ Q₂]
    [IsScalarTower A₂ (A₂ ⊗[k] K) Q₂] (a : A₁) :
    fractionRingTensorProductMapLeftAlgHom K Q₁ Q₂ f hf (algebraMap A₁ Q₁ a) =
      algebraMap A₂ Q₂ (f a) := by
  rw [IsScalarTower.algebraMap_apply A₁ (A₁ ⊗[k] K) Q₁,
    fractionRingTensorProductMapLeftAlgHom_algebraMap,
    IsScalarTower.algebraMap_apply A₂ (A₂ ⊗[k] K) Q₂]
  simp

theorem coe_fractionRingTensorProductMapLeftAlgHom [Module.Flat k A₂]
    [Algebra k Q₁] [IsScalarTower k (A₁ ⊗[k] K) Q₁]
    [Algebra k Q₂] [IsScalarTower k (A₂ ⊗[k] K) Q₂] :
    ⇑(fractionRingTensorProductMapLeftAlgHom K Q₁ Q₂ f hf) =
      ⇑(fractionRingTensorProductMapAlgHom Q₁ Q₂ f (AlgHom.id k K) hf
        ((AlgHom.coe_id k K).symm ▸ Function.injective_id)) :=
  congrArg DFunLike.coe <|
    IsLocalization.ringHom_ext (nonZeroDivisors (A₁ ⊗[k] K)) <| RingHom.ext fun x ↦ by simp

theorem fractionRingTensorProductMapLeftAlgHom_injective :
    Function.Injective (fractionRingTensorProductMapLeftAlgHom K Q₁ Q₂ f hf) := by
  rw [fractionRingTensorProductMapLeftAlgHom, IsLocalization.coe_liftAlgHom,
    IsLocalization.lift_injective_iff]
  intro x y
  exact (IsFractionRing.injective (A₁ ⊗[k] K) Q₁).eq_iff.trans
    (comp_mapLeftAlgHom_injective K Q₂ f hf).eq_iff.symm

/-- Any `K`-algebra map `Q₁ →ₐ[K] Q₂` agreeing with `f` on `A₁` equals
`fractionRingTensorProductMapLeftAlgHom`. -/
theorem algHom_eq_fractionRingTensorProductMapLeftAlgHom [Algebra A₁ Q₁]
    [IsScalarTower A₁ (A₁ ⊗[k] K) Q₁] [Algebra A₂ Q₂]
    [IsScalarTower A₂ (A₂ ⊗[k] K) Q₂] {Φ : Q₁ →ₐ[K] Q₂}
    (hA : ∀ a : A₁, Φ (algebraMap A₁ Q₁ a) = algebraMap A₂ Q₂ (f a)) :
    Φ = fractionRingTensorProductMapLeftAlgHom K Q₁ Q₂ f hf := by
  refine AlgHom.toRingHom_injective <|
    IsLocalization.ringHom_ext (nonZeroDivisors (A₁ ⊗[k] K)) <|
      Algebra.TensorProduct.ringHom_ext
        (f := Φ.toRingHom.comp (algebraMap (A₁ ⊗[k] K) Q₁))
        (g := (fractionRingTensorProductMapLeftAlgHom K Q₁ Q₂ f hf).toRingHom.comp
          (algebraMap (A₁ ⊗[k] K) Q₁))
        (RingHom.ext fun a ↦ ?_) (RingHom.ext fun c ↦ ?_)
  · simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeLeftRingHom_apply,
      fractionRingTensorProductMapLeftAlgHom_algebraMap_tmul,
      IsScalarTower.algebraMap_apply A₁ (A₁ ⊗[k] K) Q₁,
      IsScalarTower.algebraMap_apply A₂ (A₂ ⊗[k] K) Q₂,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] using hA a
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply,
      ← Algebra.TensorProduct.right_algebraMap_apply,
      ← IsScalarTower.algebraMap_apply K (A₁ ⊗[k] K) Q₁, AlgHom.commutes]

end Properties

@[simp]
theorem fractionRingTensorProductMapLeftAlgHom_id (K Q : Type*) [CommRing K]
    [Algebra k K] [Module.Flat k K] [Field Q]
    [Algebra (A₁ ⊗[k] K) Q] [Algebra K Q] [IsScalarTower K (A₁ ⊗[k] K) Q]
    [IsFractionRing (A₁ ⊗[k] K) Q]
    {hf : Function.Injective (AlgHom.id k A₁)} :
    fractionRingTensorProductMapLeftAlgHom K Q Q (AlgHom.id k A₁) hf = AlgHom.id K Q :=
  AlgHom.toRingHom_injective <|
    IsLocalization.ringHom_ext (nonZeroDivisors (A₁ ⊗[k] K)) <| RingHom.ext fun x ↦ by simp

theorem fractionRingTensorProductMapLeftAlgHom_comp {A₃ : Type*} [CommRing A₃] [Algebra k A₃]
    (K Q₁ Q₂ Q₃ : Type*) [CommRing K] [Algebra k K] [Module.Flat k K]
    [CommRing Q₁] [Field Q₂] [Field Q₃]
    [Algebra (A₁ ⊗[k] K) Q₁] [Algebra K Q₁] [IsScalarTower K (A₁ ⊗[k] K) Q₁]
    [IsFractionRing (A₁ ⊗[k] K) Q₁]
    [Algebra (A₂ ⊗[k] K) Q₂] [Algebra K Q₂] [IsScalarTower K (A₂ ⊗[k] K) Q₂]
    [IsFractionRing (A₂ ⊗[k] K) Q₂]
    [Algebra (A₃ ⊗[k] K) Q₃] [FaithfulSMul (A₃ ⊗[k] K) Q₃]
    [Algebra K Q₃] [IsScalarTower K (A₃ ⊗[k] K) Q₃]
    (f₁ : A₁ →ₐ[k] A₂) (f₂ : A₂ →ₐ[k] A₃)
    (hf₁ : Function.Injective f₁) (hf₂ : Function.Injective f₂) :
    (fractionRingTensorProductMapLeftAlgHom K Q₂ Q₃ f₂ hf₂).comp
        (fractionRingTensorProductMapLeftAlgHom K Q₁ Q₂ f₁ hf₁) =
      fractionRingTensorProductMapLeftAlgHom K Q₁ Q₃ (f₂.comp f₁)
        ((AlgHom.coe_comp f₂ f₁).symm ▸ hf₂.comp hf₁) :=
  AlgHom.toRingHom_injective <|
    IsLocalization.ringHom_ext (nonZeroDivisors (A₁ ⊗[k] K)) <| RingHom.ext fun x ↦ by
      simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.comp_apply,
        fractionRingTensorProductMapLeftAlgHom_algebraMap]
      rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp]

end FixedRight

end TauCeti
