/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.NumberTheory.ClassGroup.Equiv
public import TauCeti.NumberTheory.Padics.TensorPrimaryComponent
public import TauCeti.RingTheory.ClassGroup.Galois
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import TauCeti.NumberTheory.NumberField.ClassNumber.RingEquiv
import TauCeti.NumberTheory.NumberField.Cyclotomic.Galois
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport

/-!
# Scalar-extended cyclotomic class modules and Galois action

For a rational cyclotomic extension `K / ℚ` of conductor `m` (`IsCyclotomicExtension {m} ℚ K`) and
a commutative ring `R`, the scalar-extended ideal class module

`R ⊗[ℤ] Additive (ClassGroup (𝓞 K))`

carries a covariant `R`-linear action of `(ZMod m)ˣ`: a residue unit `a : (ZMod m)ˣ` corresponds via
`(IsCyclotomicExtension.Rat.galEquivZMod m K).symm` to the Galois automorphism raising every `m`-th
root of unity to the `a`-th power, restricts to a ring automorphism of `𝓞 K`, pushes ideal classes
forward via `ClassGroup.mulEquivHom`, and extends `R`-linearly to the tensor product. Specializing
`K` to `CyclotomicField m ℚ` gives `TauCeti.cyclotomicClassAction`.

When `R = ℤ_[p]` for a prime `p`, `TauCeti.AddCommGroup.primaryComponentLinearEquivPadicIntTensor`
identifies `ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))` `ℤ_[p]`-linearly and `(ZMod m)ˣ`-equivariantly
with the `p`-primary subgroup `AddCommGroup.primaryComponent (Additive (ClassGroup (𝓞 K))) p`, while
classes of order prime to `p` vanish in the tensor product.

For an extension of number fields `K → L`, scalar extension of `ClassGroup.extendedHom` and
`ClassGroup.relNorm` defines `R`-linear maps `TauCeti.classGroupExtendedLinearMap` and
`TauCeti.classGroupRelNormLinearMap` satisfying `relNorm ∘ extended = [L : K] • id` and, when
`L / K` is Galois, the orbit-sum identity `extended ∘ relNorm = ∑_{g ∈ Gal(L/K)} g`. In a
cyclotomic tower (`m ∣ n`), both maps intertwine the `(ZMod n)ˣ` and `(ZMod m)ˣ` actions along
`ZMod.unitsMap`.

## Main definitions

* `TauCeti.fieldAutClassAction R e`: the `R`-linear endomorphism of
  `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))` induced by a field automorphism `e : K ≃+* K`.
* `TauCeti.cyclotomicFieldClassAction R m K a`, `TauCeti.cyclotomicClassAction R m a`: the
  `R`-linear action of `a : (ZMod m)ˣ` on `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))` and on
  `R ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField m ℚ)))`.
* `TauCeti.cyclotomicFieldClassRep R m K`, `TauCeti.cyclotomicClassRep R m`: the action bundled as
  a `Representation R (ZMod m)ˣ`.
* `TauCeti.cyclotomicClassPrimaryEquiv p m`: the `ℤ_[p]`-linear equivalence between the `p`-primary
  component of `Additive (ClassGroup (𝓞 (CyclotomicField m ℚ)))` and its `ℤ_[p]`-tensor product.
* `TauCeti.classGroupExtendedLinearMap R K L`, `TauCeti.classGroupRelNormLinearMap R K L`:
  scalar-extended class-group extension and relative norm maps for `K → L`.

## Main results

* `TauCeti.cyclotomicClassAction_one`, `TauCeti.cyclotomicClassAction_mul`: identity and covariant
  multiplication laws `cyclotomicClassAction R m (a * b) = ... a * ... b`.
* `TauCeti.cyclotomicClassPrimaryEquiv_symm_action`: `(ZMod m)ˣ`-equivariance of the `p`-primary
  identification.
* `TauCeti.classGroupRelNormLinearMap_comp_extendedLinearMap`,
  `TauCeti.classGroupExtendedLinearMap_comp_relNormLinearMap`: the `[L : K]`-multiplication and
  Galois orbit-sum composite identities.
* `TauCeti.cyclotomicFieldClassAction_extendedLinearMap`,
  `TauCeti.cyclotomicFieldClassAction_relNormLinearMap`: equivariance of extension and norm in a
  cyclotomic tower along `ZMod.unitsMap`.
* `TauCeti.subsingleton_cyclotomicClassTensor_one`,
  `TauCeti.subsingleton_cyclotomicClassTensor_two`: triviality at conductors `1` and `2`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §§1.5, 4.3, 6.3, 10.1.
* R. Sharifi, *Iwasawa Theory*, §§1.3, 2.8.
-/

public section

open NumberField TensorProduct IsCyclotomicExtension.Rat
open scoped nonZeroDivisors

namespace TauCeti

/-- The native cyclotomic field has its canonical cyclotomic-extension structure. -/
local instance instIsCyclotomicExtensionSingletonCyclotomicField (m : ℕ) [NeZero m] :
    IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
  CyclotomicField.isCyclotomicExtension m ℚ

/-! ### Field-automorphism action and tower maps on scalar-extended class groups -/

section NumberFieldGeneral

attribute [local instance] FractionRing.liftAlgebra

local instance instIsScalarTowerRat (K L : Type*) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    [Algebra K L] : IsScalarTower ℚ K L :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

local instance instFiniteDimensionalOfNumberField (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] : FiniteDimensional K L :=
  Module.Finite.right ℚ K L

/-- The `R`-linear endomorphism of `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))` induced covariantly by a
ring automorphism `e : K ≃+* K`. -/
noncomputable def fieldAutClassAction (R : Type*) [CommRing R] {K : Type*} [Field K]
    (e : K ≃+* K) : Module.End R (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :=
  LinearMap.baseChange R
    (ClassGroup.mulEquivHom
      (RingOfIntegers.mapRingEquiv e)).toAdditive.toAddMonoidHom.toIntLinearMap

@[simp]
theorem fieldAutClassAction_tmul (R : Type*) [CommRing R] {K : Type*} [Field K]
    (e : K ≃+* K) (r : R) (c : ClassGroup (𝓞 K)) :
    fieldAutClassAction R e (r ⊗ₜ[ℤ] Additive.ofMul c) =
      r ⊗ₜ[ℤ] Additive.ofMul (ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv e) c) := by
  simp [fieldAutClassAction]

@[simp]
theorem fieldAutClassAction_one (R : Type*) [CommRing R] (K : Type*) [Field K] :
    fieldAutClassAction R (1 : K ≃+* K) = 1 := by
  refine LinearMap.ext fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    change fieldAutClassAction R (RingEquiv.refl K) (r ⊗ₜ[ℤ] Additive.ofMul (Additive.toMul a)) = _
    rw [fieldAutClassAction_tmul, RingOfIntegers.mapRingEquiv_refl, ClassGroup.mulEquiv_refl]
    simp
  | add x y hx hy => simp [map_add, hx, hy]

@[simp]
theorem fieldAutClassAction_mul (R : Type*) [CommRing R] {K : Type*} [Field K]
    (e₁ e₂ : K ≃+* K) :
    fieldAutClassAction R (e₁ * e₂) = fieldAutClassAction R e₁ * fieldAutClassAction R e₂ := by
  have hmap : RingOfIntegers.mapRingEquiv (e₁ * e₂) =
      RingOfIntegers.mapRingEquiv e₁ * RingOfIntegers.mapRingEquiv e₂ :=
    RingOfIntegers.mapRingEquiv_trans e₂ e₁
  refine LinearMap.ext fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    change fieldAutClassAction R (e₁ * e₂) (r ⊗ₜ[ℤ] Additive.ofMul (Additive.toMul a)) =
      fieldAutClassAction R e₁
        (fieldAutClassAction R e₂ (r ⊗ₜ[ℤ] Additive.ofMul (Additive.toMul a)))
    rw [fieldAutClassAction_tmul, fieldAutClassAction_tmul, fieldAutClassAction_tmul, hmap]
    simp [← ClassGroup.mulEquivHom_apply, map_mul]
  | add x y hx hy => simp [map_add, hx, hy]

/-- Scalar-extended ideal-class extension map `R ⊗[ℤ] Cl(𝓞 K) →ₗ[R] R ⊗[ℤ] Cl(𝓞 L)` for an
extension of fields `K → L`. -/
noncomputable def classGroupExtendedLinearMap (R K L : Type*) [CommRing R]
    [Field K] [Field L] [Algebra K L] :
    (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) →ₗ[R] (R ⊗[ℤ] Additive (ClassGroup (𝓞 L))) :=
  LinearMap.baseChange R (ClassGroup.extendedHom (𝓞 K) (𝓞 L)).toAdditive.toIntLinearMap

@[simp]
theorem classGroupExtendedLinearMap_tmul (R K L : Type*) [CommRing R]
    [Field K] [Field L] [Algebra K L]
    (r : R) (c : ClassGroup (𝓞 K)) :
    classGroupExtendedLinearMap R K L (r ⊗ₜ[ℤ] Additive.ofMul c) =
      r ⊗ₜ[ℤ] Additive.ofMul (ClassGroup.extendedHom (𝓞 K) (𝓞 L) c) := by
  simp [classGroupExtendedLinearMap]

/-- Scalar-extended relative norm map `R ⊗[ℤ] Cl(𝓞 L) →ₗ[R] R ⊗[ℤ] Cl(𝓞 K)` for an extension of
number fields `K → L`. -/
noncomputable def classGroupRelNormLinearMap (R K L : Type*) [CommRing R]
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    (R ⊗[ℤ] Additive (ClassGroup (𝓞 L))) →ₗ[R] (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :=
  LinearMap.baseChange R (ClassGroup.relNorm (𝓞 K)).toAdditive.toIntLinearMap

@[simp]
theorem classGroupRelNormLinearMap_tmul (R K L : Type*) [CommRing R]
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (r : R) (c : ClassGroup (𝓞 L)) :
    classGroupRelNormLinearMap R K L (r ⊗ₜ[ℤ] Additive.ofMul c) =
      r ⊗ₜ[ℤ] Additive.ofMul (ClassGroup.relNorm (𝓞 K) c) := by
  simp [classGroupRelNormLinearMap]

/-- **Extend then norm multiplies by `[L : K]`** on scalar-extended class modules. -/
theorem classGroupRelNormLinearMap_comp_extendedLinearMap (R K L : Type*) [CommRing R]
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    (classGroupRelNormLinearMap R K L).comp (classGroupExtendedLinearMap R K L) =
      Module.finrank K L • LinearMap.id := by
  have hfin : Module.finrank (𝓞 K) (𝓞 L) = Module.finrank K L :=
    (IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L).symm
  refine LinearMap.ext fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    change classGroupRelNormLinearMap R K L
        (classGroupExtendedLinearMap R K L (r ⊗ₜ[ℤ] Additive.ofMul (Additive.toMul a))) = _
    rw [classGroupExtendedLinearMap_tmul, classGroupRelNormLinearMap_tmul,
      ClassGroup.relNorm_extendedHom, hfin, ofMul_pow, LinearMap.smul_apply, LinearMap.id_apply,
      ← tmul_smul, ofMul_toMul]
  | add x y hx hy => simp [map_add, hx, hy]

/-- Pointwise form of `classGroupRelNormLinearMap_comp_extendedLinearMap`. -/
theorem classGroupRelNormLinearMap_extendedLinearMap (R K L : Type*) [CommRing R]
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (x : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :
    classGroupRelNormLinearMap R K L (classGroupExtendedLinearMap R K L x) =
      Module.finrank K L • x :=
  DFunLike.congr_fun (classGroupRelNormLinearMap_comp_extendedLinearMap R K L) x

/-- Every `K`-automorphism of `L` fixes the image of `classGroupExtendedLinearMap R K L`. -/
@[simp]
theorem fieldAutClassAction_extendedLinearMap (R K L : Type*) [CommRing R]
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (g : Gal(L/K)) (x : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :
    fieldAutClassAction R g.toRingEquiv (classGroupExtendedLinearMap R K L x) =
      classGroupExtendedLinearMap R K L x := by
  have hg : RingOfIntegers.mapRingEquiv g.toRingEquiv =
      (galRestrict (𝓞 K) K L (𝓞 L) g).toRingEquiv := by
    ext z
    exact (algebraMap_galRestrict_apply (𝓞 K) g z).symm
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    change fieldAutClassAction R g.toRingEquiv
        (classGroupExtendedLinearMap R K L (r ⊗ₜ[ℤ] Additive.ofMul (Additive.toMul a))) = _
    rw [classGroupExtendedLinearMap_tmul, fieldAutClassAction_tmul, hg,
      ClassGroup.mulEquiv_algEquiv_extendedHom, ← classGroupExtendedLinearMap_tmul, ofMul_toMul]
  | add x y hx hy => simp [map_add, hx, hy]

/-- `classGroupRelNormLinearMap R K L` is invariant under every `K`-automorphism of `L`. -/
@[simp]
theorem classGroupRelNormLinearMap_fieldAutClassAction (R K L : Type*) [CommRing R]
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (g : Gal(L/K)) (x : R ⊗[ℤ] Additive (ClassGroup (𝓞 L))) :
    classGroupRelNormLinearMap R K L (fieldAutClassAction R g.toRingEquiv x) =
      classGroupRelNormLinearMap R K L x := by
  have hg : RingOfIntegers.mapRingEquiv g.toRingEquiv =
      (galRestrict (𝓞 K) K L (𝓞 L) g).toRingEquiv := by
    ext z
    exact (algebraMap_galRestrict_apply (𝓞 K) g z).symm
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    change classGroupRelNormLinearMap R K L
        (fieldAutClassAction R g.toRingEquiv (r ⊗ₜ[ℤ] Additive.ofMul (Additive.toMul a))) = _
    rw [fieldAutClassAction_tmul, classGroupRelNormLinearMap_tmul, hg,
      ClassGroup.relNorm_mulEquiv_algEquiv, ← classGroupRelNormLinearMap_tmul, ofMul_toMul]
  | add x y hx hy => simp [map_add, hx, hy]

/-- **Norm then extend is the Galois orbit sum** on scalar-extended class modules for any Galois
extension of number fields `L / K`. -/
theorem classGroupExtendedLinearMap_comp_relNormLinearMap (R K L : Type*) [CommRing R]
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    (classGroupExtendedLinearMap R K L).comp (classGroupRelNormLinearMap R K L) =
      ∑ g : Gal(L/K), fieldAutClassAction R g.toRingEquiv := by
  have : IsGalois (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) :=
    IsGalois.of_equiv_equiv (f := (FractionRing.algEquiv (𝓞 K) K).toRingEquiv.symm)
      (g := (FractionRing.algEquiv (𝓞 L) L).toRingEquiv.symm) <|
      RingHom.ext fun z ↦ IsFractionRing.algEquiv_commutes
        (FractionRing.algEquiv (𝓞 K) K).symm (FractionRing.algEquiv (𝓞 L) L).symm z
  have hg (g : Gal(L/K)) : (galRestrict (𝓞 K) K L (𝓞 L) g).toRingEquiv =
      RingOfIntegers.mapRingEquiv g.toRingEquiv := by
    ext z
    exact algebraMap_galRestrict_apply (𝓞 K) g z
  refine LinearMap.ext fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    change classGroupExtendedLinearMap R K L
        (classGroupRelNormLinearMap R K L (r ⊗ₜ[ℤ] Additive.ofMul (Additive.toMul a))) = _
    rw [classGroupRelNormLinearMap_tmul, classGroupExtendedLinearMap_tmul,
      ClassGroup.extendedHom_relNorm, ← (galRestrict (𝓞 K) K L (𝓞 L)).toEquiv.prod_comp]
    simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, hg, ofMul_prod, tmul_sum,
      LinearMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    change _ =
      fieldAutClassAction R g.toRingEquiv (r ⊗ₜ[ℤ] Additive.ofMul (Additive.toMul a))
    rw [fieldAutClassAction_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

/-- Pointwise form of `classGroupExtendedLinearMap_comp_relNormLinearMap`. -/
theorem classGroupExtendedLinearMap_relNormLinearMap (R K L : Type*) [CommRing R]
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (x : R ⊗[ℤ] Additive (ClassGroup (𝓞 L))) :
    classGroupExtendedLinearMap R K L (classGroupRelNormLinearMap R K L x) =
      ∑ g : Gal(L/K), fieldAutClassAction R g.toRingEquiv x := by
  simpa [LinearMap.coe_sum, Finset.sum_apply] using
    DFunLike.congr_fun (classGroupExtendedLinearMap_comp_relNormLinearMap R K L) x

/-- When `ClassGroup (𝓞 K)` is a subsingleton (equivalently `classNumber K = 1`), any scalar
extension `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))` is a subsingleton. -/
theorem subsingleton_tensor_classGroup_of_classNumber_eq_one (R K : Type*) [CommRing R]
    [Field K] [NumberField K] (hK : classNumber K = 1) :
    Subsingleton (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) := by
  have : Subsingleton (ClassGroup (𝓞 K)) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq hK)
  have : Subsingleton (Additive (ClassGroup (𝓞 K))) :=
    Additive.ofMul.symm.injective.subsingleton
  refine ⟨fun x y ↦ ?_⟩
  have hzero (z : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) : z = 0 := by
    induction z using TensorProduct.inductionOn with
    | tmul r a => rw [Subsingleton.elim a 0, tmul_zero]
    | add u v hu hv => rw [hu, hv, add_zero]
  rw [hzero x, hzero y]

/-- Any number field of degree `1` over `ℚ` has class number `1`. -/
theorem classNumber_eq_one_of_finrank_eq_one {K : Type*} [Field K] [NumberField K]
    (hfin : Module.finrank ℚ K = 1) : classNumber K = 1 := by
  let e : ℚ ≃ₐ[ℚ] K :=
    AlgEquiv.ofBijective (Algebra.ofId ℚ K)
      (Module.Free.bijective_algebraMap_of_finrank_eq_one hfin)
  rw [← e.toRingEquiv.classNumber_eq, Rat.classNumber_eq]

end NumberFieldGeneral

/-! ### Cyclotomic Galois action on scalar-extended class modules -/

section CyclotomicAction

private theorem algEquiv_mul_toRingEquiv {F E : Type*} [Field F] [Field E] [Algebra F E]
    (σ τ : E ≃ₐ[F] E) : (σ * τ).toRingEquiv = σ.toRingEquiv * τ.toRingEquiv :=
  rfl

/-- Scalar extension of the covariant `(ZMod m)ˣ` Galois action on the ideal class group of any
`m`-th rational cyclotomic field `K`. -/
noncomputable def cyclotomicFieldClassAction (R : Type*) [CommRing R] (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K] (a : (ZMod m)ˣ) :
    Module.End R (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :=
  LinearMap.baseChange R
    (ClassGroup.mulEquivHom
      (RingOfIntegers.mapRingEquiv
        ((galEquivZMod m K).symm a).toRingEquiv)).toAdditive.toAddMonoidHom.toIntLinearMap

/-- Scalar extension of the native covariant `(ZMod m)ˣ` action on ideal classes of
`CyclotomicField m ℚ`. -/
noncomputable def cyclotomicClassAction (R : Type*) [CommRing R] (m : ℕ) [NeZero m]
    (a : (ZMod m)ˣ) :
    Module.End R (R ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField m ℚ)))) :=
  LinearMap.baseChange R
    ((ClassGroup.mulEquivHom
      (RingOfIntegers.mapRingEquiv
        (((IsCyclotomicExtension.Rat.galEquivZMod m
          (CyclotomicField m ℚ)).symm a).toRingEquiv))).toAdditive.toAddMonoidHom.toIntLinearMap)

theorem cyclotomicClassAction_eq_cyclotomicFieldClassAction (R : Type*) [CommRing R]
    (m : ℕ) [NeZero m] (a : (ZMod m)ˣ) :
    cyclotomicClassAction R m a = cyclotomicFieldClassAction R m (CyclotomicField m ℚ) a :=
  (rfl)

theorem cyclotomicFieldClassAction_eq_fieldAutClassAction (R : Type*) [CommRing R]
    (m : ℕ) [NeZero m] (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (a : (ZMod m)ˣ) :
    cyclotomicFieldClassAction R m K a =
      fieldAutClassAction R ((galEquivZMod m K).symm a).toRingEquiv :=
  (rfl)

@[simp]
theorem cyclotomicFieldClassAction_tmul (R : Type*) [CommRing R] (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (a : (ZMod m)ˣ) (r : R) (c : ClassGroup (𝓞 K)) :
    cyclotomicFieldClassAction R m K a (r ⊗ₜ[ℤ] Additive.ofMul c) =
      r ⊗ₜ[ℤ] Additive.ofMul
        (ClassGroup.mulEquiv
          (RingOfIntegers.mapRingEquiv ((galEquivZMod m K).symm a).toRingEquiv) c) := by
  simp [cyclotomicFieldClassAction]

@[simp]
theorem cyclotomicClassAction_tmul (R : Type*) [CommRing R] (m : ℕ) [NeZero m]
    (a : (ZMod m)ˣ) (r : R) (c : ClassGroup (𝓞 (CyclotomicField m ℚ))) :
    cyclotomicClassAction R m a (r ⊗ₜ[ℤ] Additive.ofMul c) =
      r ⊗ₜ[ℤ] Additive.ofMul
        (ClassGroup.mulEquiv
          (RingOfIntegers.mapRingEquiv
            ((galEquivZMod m (CyclotomicField m ℚ)).symm a).toRingEquiv) c) := by
  simp [cyclotomicClassAction]

/-- On the class of a nonzero integral ideal `I`, `cyclotomicClassAction R m a` pushes `I`
covariantly along the integer automorphism attached to `a : (ZMod m)ˣ`. -/
theorem cyclotomicClassAction_tmul_mk0 (R : Type*) [CommRing R] (m : ℕ) [NeZero m]
    (a : (ZMod m)ˣ) (r : R) (I : (Ideal (𝓞 (CyclotomicField m ℚ)))⁰) :
    let e := RingOfIntegers.mapRingEquiv
      ((galEquivZMod m (CyclotomicField m ℚ)).symm a).toRingEquiv
    cyclotomicClassAction R m a (r ⊗ₜ[ℤ] Additive.ofMul (ClassGroup.mk0 I)) =
      r ⊗ₜ[ℤ] Additive.ofMul (ClassGroup.mk0 ⟨I.1.map e, mem_nonZeroDivisors_iff_ne_zero.mpr <|
        (Ideal.map_eq_bot_iff_of_injective e.injective).not.mpr
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2)⟩) := by
  intro e
  rw [cyclotomicClassAction_tmul, ClassGroup.mulEquiv_mk0]

@[simp]
theorem cyclotomicFieldClassAction_one (R : Type*) [CommRing R] (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K] :
    cyclotomicFieldClassAction R m K 1 = 1 := by
  rw [cyclotomicFieldClassAction_eq_fieldAutClassAction, map_one]
  exact fieldAutClassAction_one R K

@[simp]
theorem cyclotomicClassAction_one (R : Type*) [CommRing R] (m : ℕ) [NeZero m] :
    cyclotomicClassAction R m 1 = 1 :=
  cyclotomicFieldClassAction_one R m (CyclotomicField m ℚ)

@[simp]
theorem cyclotomicFieldClassAction_mul (R : Type*) [CommRing R] (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    (a b : (ZMod m)ˣ) :
    cyclotomicFieldClassAction R m K (a * b) =
      cyclotomicFieldClassAction R m K a * cyclotomicFieldClassAction R m K b := by
  rw [cyclotomicFieldClassAction_eq_fieldAutClassAction, map_mul, algEquiv_mul_toRingEquiv,
    fieldAutClassAction_mul]
  rfl

@[simp]
theorem cyclotomicClassAction_mul (R : Type*) [CommRing R] (m : ℕ) [NeZero m]
    (a b : (ZMod m)ˣ) :
    cyclotomicClassAction R m (a * b) =
      cyclotomicClassAction R m a * cyclotomicClassAction R m b :=
  cyclotomicFieldClassAction_mul R m (CyclotomicField m ℚ) a b

theorem cyclotomicClassAction_apply_mul (R : Type*) [CommRing R] (m : ℕ) [NeZero m]
    (a b : (ZMod m)ˣ) (x : R ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField m ℚ)))) :
    cyclotomicClassAction R m (a * b) x =
      cyclotomicClassAction R m a (cyclotomicClassAction R m b x) :=
  DFunLike.congr_fun (cyclotomicClassAction_mul R m a b) x

/-- The covariant `(ZMod m)ˣ` action on `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))` bundled as a
`Representation`. -/
noncomputable def cyclotomicFieldClassRep (R : Type*) [CommRing R] (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K] :
    Representation R (ZMod m)ˣ (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) where
  toFun := cyclotomicFieldClassAction R m K
  map_one' := cyclotomicFieldClassAction_one R m K
  map_mul' := cyclotomicFieldClassAction_mul R m K

/-- The covariant `(ZMod m)ˣ` action on `R ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField m ℚ)))`
bundled as a `Representation`. -/
noncomputable def cyclotomicClassRep (R : Type*) [CommRing R] (m : ℕ) [NeZero m] :
    Representation R (ZMod m)ˣ
      (R ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField m ℚ)))) where
  toFun := cyclotomicClassAction R m
  map_one' := cyclotomicClassAction_one R m
  map_mul' := cyclotomicClassAction_mul R m

@[simp]
theorem cyclotomicFieldClassRep_apply (R : Type*) [CommRing R] (m : ℕ) [NeZero m]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K] (a : (ZMod m)ˣ) :
    cyclotomicFieldClassRep R m K a = cyclotomicFieldClassAction R m K a :=
  (rfl)

@[simp]
theorem cyclotomicClassRep_apply (R : Type*) [CommRing R] (m : ℕ) [NeZero m] (a : (ZMod m)ˣ) :
    cyclotomicClassRep R m a = cyclotomicClassAction R m a :=
  (rfl)

/-- Conductor-`1` triviality: `R ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField 1 ℚ)))` is a
subsingleton. -/
theorem subsingleton_cyclotomicClassTensor_one (R : Type*) [CommRing R] :
    Subsingleton (R ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField 1 ℚ)))) :=
  subsingleton_tensor_classGroup_of_classNumber_eq_one R (CyclotomicField 1 ℚ) <|
    classNumber_eq_one_of_finrank_eq_one <| by
      rw [IsCyclotomicExtension.Rat.finrank 1 (CyclotomicField 1 ℚ), Nat.totient_one]

/-- Conductor-`2` triviality: `R ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField 2 ℚ)))` is a
subsingleton because `ℚ(ζ₂) = ℚ` has class number `1`. -/
theorem subsingleton_cyclotomicClassTensor_two (R : Type*) [CommRing R] :
    Subsingleton (R ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField 2 ℚ)))) :=
  subsingleton_tensor_classGroup_of_classNumber_eq_one R (CyclotomicField 2 ℚ) <|
    classNumber_eq_one_of_finrank_eq_one <| by
      rw [IsCyclotomicExtension.Rat.finrank 2 (CyclotomicField 2 ℚ), Nat.totient_two]

end CyclotomicAction

/-! ### The `p`-primary cyclotomic class module over `ℤ_[p]` -/

section PadicPrimary

variable (p : ℕ) [Fact p.Prime]

/-- The `ℤ_[p]`-linear equivalence identifying the `p`-primary subgroup of
`Additive (ClassGroup (𝓞 K))` with `ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))` for any number field
`K`. -/
noncomputable def numberFieldClassPrimaryEquiv (K : Type*) [Field K] [NumberField K] :
    AddCommGroup.primaryComponent (Additive (ClassGroup (𝓞 K))) p ≃ₗ[ℤ_[p]]
      ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K)) :=
  TauCeti.AddCommGroup.primaryComponentLinearEquivPadicIntTensor p
    (Additive (ClassGroup (𝓞 K))) AddMonoid.ExponentExists.of_finite

/-- The `ℤ_[p]`-linear equivalence identifying the `p`-primary subgroup of
`Additive (ClassGroup (𝓞 (CyclotomicField m ℚ)))` with
`ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField m ℚ)))`. -/
noncomputable def cyclotomicClassPrimaryEquiv (m : ℕ) :
    AddCommGroup.primaryComponent (Additive (ClassGroup (𝓞 (CyclotomicField m ℚ)))) p ≃ₗ[ℤ_[p]]
      ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField m ℚ))) :=
  numberFieldClassPrimaryEquiv p (CyclotomicField m ℚ)

@[simp]
theorem cyclotomicClassPrimaryEquiv_apply (m : ℕ)
    (x : AddCommGroup.primaryComponent (Additive (ClassGroup (𝓞 (CyclotomicField m ℚ)))) p) :
    cyclotomicClassPrimaryEquiv p m x =
      (1 : ℤ_[p]) ⊗ₜ[ℤ] (x : Additive (ClassGroup (𝓞 (CyclotomicField m ℚ)))) :=
  TauCeti.AddCommGroup.primaryComponentLinearEquivPadicIntTensor_apply
    AddMonoid.ExponentExists.of_finite x

/-- **Galois equivariance of the `p`-primary tensor identification**: `cyclotomicClassPrimaryEquiv`
intertwines the native `(ZMod m)ˣ` action on the `p`-primary subgroup with
`cyclotomicClassAction`. -/
theorem cyclotomicClassPrimaryEquiv_symm_action (m : ℕ) [NeZero m] (a : (ZMod m)ˣ)
    (t : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField m ℚ)))) :
    (cyclotomicClassPrimaryEquiv p m).symm (cyclotomicClassAction ℤ_[p] m a t) =
      TauCeti.AddCommGroup.primaryComponentLinearMap p
        ((ClassGroup.mulEquivHom
          (RingOfIntegers.mapRingEquiv
            ((galEquivZMod m (CyclotomicField m ℚ)).symm a).toRingEquiv)).toAdditive.toAddMonoidHom)
        ((cyclotomicClassPrimaryEquiv p m).symm t) :=
  TauCeti.AddCommGroup.primaryComponentLinearEquivPadicIntTensor_symm_baseChange
    AddMonoid.ExponentExists.of_finite AddMonoid.ExponentExists.of_finite _ t

/-- An ideal class whose order is prime to `p` vanishes in
`ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))`. -/
theorem tmul_classGroup_eq_zero_of_pow_eq_one {K : Type*} [Field K]
    {k : ℕ} (hk : ¬ p ∣ k) {c : ClassGroup (𝓞 K)} (hc : c ^ k = 1) (a : ℤ_[p]) :
    a ⊗ₜ[ℤ] Additive.ofMul c = 0 :=
  TauCeti.AddCommGroup.tmul_eq_zero_of_nsmul_eq_zero hk
    (by rw [← ofMul_pow, hc, ofMul_one]) a

/-- When `p` does not divide `classNumber K`, the `p`-primary scalar-extended class module
`ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))` is trivial. -/
theorem subsingleton_padicClassTensor_of_not_dvd_classNumber {K : Type*} [Field K] [NumberField K]
    (hdiv : ¬ p ∣ classNumber K) :
    Subsingleton (ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))) := by
  refine ⟨fun x y ↦ ?_⟩
  have hzero (z : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))) : z = 0 := by
    induction z using TensorProduct.inductionOn with
    | tmul a c =>
      exact tmul_classGroup_eq_zero_of_pow_eq_one p hdiv
        (pow_card_eq_one (x := Additive.toMul c)) a
    | add u v hu hv => rw [hu, hv, add_zero]
  rw [hzero x, hzero y]

end PadicPrimary

/-! ### Cyclotomic tower norm and extension equivariance -/

section CyclotomicTower

local instance (K L : Type*) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] [Algebra K L] :
    IsScalarTower ℚ K L :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

/-- Existence of a `ℚ`-algebra embedding `K →ₐ[ℚ] L` between models of the `m`-th and `n`-th
cyclotomic fields whenever `m ∣ n`. -/
theorem nonempty_cyclotomicAlgHom_of_dvd {m n : ℕ} [NeZero m] [NeZero n] (hmn : m ∣ n)
    (K L : Type*) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    [IsCyclotomicExtension {m} ℚ K] [IsCyclotomicExtension {n} ℚ L] :
    Nonempty (K →ₐ[ℚ] L) := by
  obtain ⟨k, hk⟩ := hmn
  have hξ : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ L ^ k) m :=
    IsPrimitiveRoot.pow (NeZero.pos n) (IsCyclotomicExtension.zeta_spec n ℚ L)
      (mul_comm m k ▸ hk)
  exact ⟨((IsCyclotomicExtension.zeta_spec m ℚ K).embeddingsEquivPrimitiveRoots L
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))).symm
    ⟨_, (mem_primitiveRoots (NeZero.pos m)).mpr hξ⟩⟩

/-- Restriction of `(galEquivZMod n L).symm a` to a sub-cyclotomic field `K` (`m ∣ n`) equals
`(galEquivZMod m K).symm (ZMod.unitsMap hmn a)`. -/
theorem restrictNormal_galEquivZMod_symm {m n : ℕ} [NeZero m] [NeZero n] (hmn : m ∣ n)
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ K] [IsCyclotomicExtension {n} ℚ L] [Algebra K L] [Normal ℚ K]
    (a : (ZMod n)ˣ) :
    ((galEquivZMod n L).symm a).restrictNormal K =
      (galEquivZMod m K).symm (ZMod.unitsMap hmn a) := by
  apply (galEquivZMod m K).injective
  rw [MulEquiv.apply_symm_apply]
  refine AlgEquiv.galEquivZMod_restrictNormal ((galEquivZMod n L).symm a) (ZMod.unitsMap hmn a)
    fun z hz ↦ ?_
  have hzn : z ^ n = 1 := by
    obtain ⟨k, rfl⟩ := hmn
    rw [pow_mul, hz, one_pow]
  rw [galEquivZMod_apply_of_pow_eq n L _ hzn, MulEquiv.apply_symm_apply]
  have hmod : (a : ZMod n).val ≡ (ZMod.unitsMap hmn a : ZMod m).val [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, ZMod.unitsMap_val,
      ← ZMod.castHom_apply (h := hmn)]
    conv_rhs => rw [← ZMod.natCast_zmod_val (a : ZMod n), map_natCast]
  exact pow_eq_pow_of_modEq hmod hz

/-- **Tower equivariance of class-group extension**: in a cyclotomic tower `K → L` (`m ∣ n`),
extending classes from `K` to `L` intertwines `ZMod.unitsMap hmn a` with `a`. -/
theorem cyclotomicFieldClassAction_extendedLinearMap (R : Type*) [CommRing R]
    {m n : ℕ} [NeZero m] [NeZero n] (hmn : m ∣ n)
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ K] [IsCyclotomicExtension {n} ℚ L] [Algebra K L]
    (a : (ZMod n)ˣ) (x : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :
    cyclotomicFieldClassAction R n L a (classGroupExtendedLinearMap R K L x) =
      classGroupExtendedLinearMap R K L
        (cyclotomicFieldClassAction R m K (ZMod.unitsMap hmn a) x) := by
  have : Normal ℚ K := (IsCyclotomicExtension.isGalois {m} ℚ K).to_normal
  set τ := (galEquivZMod n L).symm a
  have hres := restrictNormal_galEquivZMod_symm hmn K L a
  have hcomm : (algebraMap (𝓞 K) (𝓞 L)).comp
      (RingOfIntegers.mapRingEquiv (τ.restrictNormal K).toRingEquiv).toRingHom =
      (RingOfIntegers.mapRingEquiv τ.toRingEquiv).toRingHom.comp (algebraMap (𝓞 K) (𝓞 L)) := by
    ext z
    exact τ.restrictNormal_commutes K (z : K)
  induction x using TensorProduct.inductionOn with
  | tmul r b =>
    rw [← ofMul_toMul b, classGroupExtendedLinearMap_tmul, cyclotomicFieldClassAction_tmul,
      cyclotomicFieldClassAction_tmul, classGroupExtendedLinearMap_tmul, ← hres,
      ClassGroup.mulEquiv_extendedHom _ _ hcomm]
  | add u v hu hv => simp [map_add, hu, hv]

/-- **Tower equivariance of class-group relative norm**: in a cyclotomic tower `K → L` (`m ∣ n`),
taking the relative norm from `L` to `K` intertwines `a` with `ZMod.unitsMap hmn a`. -/
theorem cyclotomicFieldClassAction_relNormLinearMap (R : Type*) [CommRing R]
    {m n : ℕ} [NeZero m] [NeZero n] (hmn : m ∣ n)
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ K] [IsCyclotomicExtension {n} ℚ L] [Algebra K L]
    (a : (ZMod n)ˣ) (x : R ⊗[ℤ] Additive (ClassGroup (𝓞 L))) :
    cyclotomicFieldClassAction R m K (ZMod.unitsMap hmn a)
        (classGroupRelNormLinearMap R K L x) =
      classGroupRelNormLinearMap R K L (cyclotomicFieldClassAction R n L a x) := by
  have : Normal ℚ K := (IsCyclotomicExtension.isGalois {m} ℚ K).to_normal
  set τ := (galEquivZMod n L).symm a
  have hres := restrictNormal_galEquivZMod_symm hmn K L a
  have hcomm : (algebraMap (𝓞 K) (𝓞 L)).comp
      (RingOfIntegers.mapRingEquiv (τ.restrictNormal K).toRingEquiv).toRingHom =
      (RingOfIntegers.mapRingEquiv τ.toRingEquiv).toRingHom.comp (algebraMap (𝓞 K) (𝓞 L)) := by
    ext z
    exact τ.restrictNormal_commutes K (z : K)
  induction x using TensorProduct.inductionOn with
  | tmul r b =>
    rw [← ofMul_toMul b, classGroupRelNormLinearMap_tmul, cyclotomicFieldClassAction_tmul,
      cyclotomicFieldClassAction_tmul, classGroupRelNormLinearMap_tmul, ← hres,
      ClassGroup.mulEquiv_relNorm _ _ hcomm]
  | add u v hu hv => simp [map_add, hu, hv]

end CyclotomicTower

end TauCeti
