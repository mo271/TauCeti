/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.FractionField
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.Field.Equiv
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Tensor presentations over an extended parameter field

Let `F' = F · K` be a linearly disjoint extension of constants of `F/k`, and let `C` be
an intermediate field with `F/C` algebraic. Multiplication identifies
`(C · K) ⊗[C] F` with `F'`, as algebras over `C · K`. In particular, when `F` is an
algebraic extension of `RatFunc k` over `k` and `RatFunc.X` acts compatibly on
`RatFunc K`, `F`, and `F'`, basis transport gives
`RatFunc K ⊗[RatFunc k] F ≃ₐ[RatFunc K] F'`. Because `RatFunc K` carries no global
`Algebra (RatFunc k) (RatFunc K)` instance, statements involving
`RatFunc K ⊗[RatFunc k] F` take a `k`-compatible `RatFunc k`-algebra structure on
`RatFunc K` satisfying `algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X`.
The extension `K/k` can be transcendental, and `F/C` need only be algebraic (not
necessarily separable or finite).

The same construction applies to any specified fraction field `F'` of a domain tensor
product `F ⊗[k] K` without requiring a pre-supplied `k`-algebra structure on `F'`.
When `F` is algebraic over `RatFunc k`, `F ⊗[k] K` is a domain (for instance when `F/k`
is geometrically reduced with exact constants), and `RatFunc K` is equipped with a
`k`-algebra map from `RatFunc k` fixing `RatFunc.X`, the tensor product
`RatFunc K ⊗[RatFunc k] F` is itself a field, and `F'` is canonically isomorphic as a
`K`-algebra to `RatFunc K ⊗[RatFunc k] F` via `TauCeti.fractionFieldEquivRatFuncTensor`,
without assuming that `F ⊗[k] K` is a field.

The construction uses `constantExtensionBasisOfLinearDisjoint` and
`ratFuncConstantExtensionBasis` for basis transport, together with Mathlib's
`Module.Basis.baseChange` and `AlgHom.liftEquiv` for the tensor algebra.

## Main definitions and results

* `TauCeti.constantExtensionTensorEquiv`, `IntermediateField.fractionFieldParameterEquiv`:
  the `(C · K)`-algebra isomorphism `(C · K) ⊗[C] F ≃ₐ[C · K] F'` for an intermediate
  field `C` with `F/C` algebraic.
* `TauCeti.ratFuncConstantExtensionTensorEquiv`, `TauCeti.ratFuncFractionFieldEquiv`:
  the `RatFunc K`-algebra isomorphism `RatFunc K ⊗[RatFunc k] F ≃ₐ[RatFunc K] F'` (for a
  `k`-compatible `RatFunc k`-algebra structure on `RatFunc K` fixing `RatFunc.X`).
* `TauCeti.fractionFieldEquivRatFuncTensor`: the canonical `K`-algebra equivalence
  `F' ≃ₐ[K] RatFunc K ⊗[RatFunc k] F` for any fraction field `F'` of `F ⊗[k] K`, with
  explicit formulas on pure tensors and rational functions in both directions.
* `TauCeti.isField_ratFunc_tensorProduct_of_isDomain_tensorProduct`,
  `TauCeti.isField_ratFunc_tensorProduct_of_isGeometricallyReduced`: when `F ⊗[k] K` is
  a domain and `RatFunc k → RatFunc K` fixes `RatFunc.X`, `RatFunc K ⊗[RatFunc k] F` is
  a field.

## References

* S. Lang, *Algebra*, the theory of linearly disjoint field extensions.
* S. Lang, *Introduction to Algebraic Geometry*, Chapter III, Section 1.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
-/

public section

open scoped TensorProduct IntermediateField Polynomial

namespace TauCeti

private theorem bijective_liftEquiv_of_basis {R S A B ι : Type*} [CommSemiring R]
    [CommSemiring S] [Semiring A] [Semiring B] [Algebra R S] [Algebra R A] [Algebra R B]
    [Algebra S B] [IsScalarTower R S B] (f : A →ₐ[R] B)
    (b : Module.Basis ι R A) (b' : Module.Basis ι S B) (hb : ∀ i, b' i = f (b i)) :
    Function.Bijective (AlgHom.liftEquiv R S A B f) := by
  let e := (b.baseChange S).equiv b' (Equiv.refl _)
  have he : (AlgHom.liftEquiv R S A B f).toLinearMap = e.toLinearMap := by
    apply (b.baseChange S).ext
    intro i
    simp only [AlgHom.toLinearMap_apply, LinearEquiv.coe_toLinearMap, e,
      (b.baseChange S).equiv_apply, Equiv.refl_apply, hb i]
    simp [AlgHom.liftEquiv_tmul]
  have hbij : Function.Bijective (AlgHom.liftEquiv R S A B f).toLinearMap := by
    rw [he]
    exact e.bijective
  exact hbij

variable {k K F F' : Type*} [Field k] [Field K] [Field F] [Field F']
  [Algebra k K] [Algebra k F] [Algebra k F'] [Algebra K F'] [Algebra F F']
  [IsScalarTower k K F'] [IsScalarTower k F F']

/-- A basis transported to the compositum, with scalars viewed as an extension of `C`. -/
private noncomputable def parameterBasis
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] {ι : Type*} (b : Module.Basis ι C F) :
    Module.Basis ι (constantCompositum C K F') F' :=
  (constantExtensionBasisOfLinearDisjoint H h C b).mapCoeffs
    (RingEquiv.subfieldCongr (_root_.IntermediateField.constantCompositum_toSubfield C).symm)
    (fun _ _ ↦ rfl)

/-- Multiplication over the enlarged intermediate field is bijective. -/
private theorem bijective_parameterLift
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] :
    Function.Bijective
      (AlgHom.liftEquiv C (constantCompositum C K F') F F'
        (IsScalarTower.toAlgHom C F F')) :=
  let b := Module.Basis.ofVectorSpace C F
  bijective_liftEquiv_of_basis _ b (parameterBasis H h C b) fun i ↦
    ((constantExtensionBasisOfLinearDisjoint H h C b).mapCoeffs_apply _ _ i).trans
      (constantExtensionBasisOfLinearDisjoint_apply H h C b i)

/-- **The tensor presentation over an extended intermediate field.** If `F' = F · K`
linearly disjointly over `k`, and `F/C` is algebraic, multiplication gives an algebra
isomorphism `(C · K) ⊗[C] F ≃ₐ[C · K] F'`. For a function field and `C = k(t)`,
this presents the extended field as a finite algebra over `K(t)`. -/
noncomputable def constantExtensionTensorEquiv
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] :
    (constantCompositum C K F') ⊗[C] F ≃ₐ[constantCompositum C K F'] F' :=
  AlgEquiv.ofBijective
    (AlgHom.liftEquiv C (constantCompositum C K F') F F' (IsScalarTower.toAlgHom C F F'))
    (bijective_parameterLift H h C)

/-- On pure tensors the presentation is multiplication in the ambient field. -/
@[simp]
theorem constantExtensionTensorEquiv_tmul
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] (a : constantCompositum C K F') (f : F) :
    constantExtensionTensorEquiv H h C (a ⊗ₜ[C] f) = (a : F') * algebraMap F F' f := by
  simp [constantExtensionTensorEquiv, AlgHom.liftEquiv_tmul, Algebra.smul_def]

/-- The inverse presentation sends a product of the two scalar images to a pure tensor. -/
@[simp]
theorem constantExtensionTensorEquiv_symm_mul
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] (a : constantCompositum C K F') (f : F) :
    (constantExtensionTensorEquiv H h C).symm ((a : F') * algebraMap F F' f) = a ⊗ₜ[C] f := by
  apply (constantExtensionTensorEquiv H h C).injective
  simp

section FractionField

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

omit [Algebra k F'] [IsScalarTower k K F'] [IsScalarTower k F F']

variable [Algebra (F ⊗[k] K) F']
  [IsScalarTower F (F ⊗[k] K) F'] [IsScalarTower K (F ⊗[k] K) F']
  [IsFractionRing (F ⊗[k] K) F']

/-- **A tensor presentation of the fraction field after extension of constants.**
For any specified fraction field `F'` of the domain `F ⊗[k] K`, and any intermediate
field `C` with `F/C` algebraic, multiplication identifies `(C · K) ⊗[C] F` with `F'`.
For a transcendental parameter `t` of a function field, take `C = k(t)`; the
coefficient field is `K(t)` by `constantCompositum_adjoin_simple_toSubfield`.
No algebraicity or separability of `K/k` is required. -/
noncomputable def _root_.IntermediateField.fractionFieldParameterEquiv (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] :
    (constantCompositum C K F') ⊗[C] F ≃ₐ[constantCompositum C K F'] F' :=
  let : Algebra k F' := ((algebraMap (F ⊗[k] K) F').comp (algebraMap k (F ⊗[k] K))).toAlgebra
  have : IsScalarTower k (F ⊗[k] K) F' := .of_algebraMap_eq' rfl
  have : IsScalarTower k F F' := .to₁₂₄ k F (F ⊗[k] K) F'
  have : IsScalarTower k K F' := .to₁₂₄ k K (F ⊗[k] K) F'
  constantExtensionTensorEquiv (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k)) C

/-- The fraction-field presentation respects the specified maps of the two factors. -/
@[simp]
theorem _root_.IntermediateField.fractionFieldParameterEquiv_tmul (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] (a : constantCompositum C K F') (f : F) :
    C.fractionFieldParameterEquiv (a ⊗ₜ[C] f) = (a : F') * algebraMap F F' f := by
  simp only [IntermediateField.fractionFieldParameterEquiv, constantExtensionTensorEquiv_tmul]

/-- The inverse fraction-field presentation recovers pure tensors from products. -/
@[simp]
theorem _root_.IntermediateField.fractionFieldParameterEquiv_symm_mul (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] (a : constantCompositum C K F') (f : F) :
    (C.fractionFieldParameterEquiv).symm ((a : F') * algebraMap F F' f) = a ⊗ₜ[C] f := by
  apply (C.fractionFieldParameterEquiv).injective
  simp

end FractionField

section RatFunc

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]
  [Algebra.IsAlgebraic (RatFunc k) F]

section TensorEquiv

variable [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']

/-- **Tensor presentation over `RatFunc K` of a linearly disjoint constant extension.**
If `F' = F · K` linearly disjointly over `k`, `F` is algebraic over `RatFunc k`, and
`RatFunc K` carries a `k`-compatible `RatFunc k`-algebra structure fixing `RatFunc.X` with
`RatFunc.X` acting compatibly on `F'`, multiplication identifies
`RatFunc K ⊗[RatFunc k] F` with `F'` as `RatFunc K`-algebras. -/
noncomputable def ratFuncConstantExtensionTensorEquiv
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X) :
    RatFunc K ⊗[RatFunc k] F ≃ₐ[RatFunc K] F' :=
  let : Algebra (RatFunc k) F' :=
    ((algebraMap F F').comp (algebraMap (RatFunc k) F)).toAlgebra
  have : IsScalarTower (RatFunc k) F F' := .of_algebraMap_eq' rfl
  have : IsScalarTower (RatFunc k) (RatFunc K) F' :=
    .of_algebraMap_eq fun r ↦ (algebraMap_ratFunc_eq_algebraMap hX hXF' r).symm
  let b := Module.Basis.ofVectorSpace (RatFunc k) F
  AlgEquiv.ofBijective
    (AlgHom.liftEquiv (RatFunc k) (RatFunc K) F F'
      (IsScalarTower.toAlgHom (RatFunc k) F F'))
    (bijective_liftEquiv_of_basis _ b (ratFuncConstantExtensionBasis H h hXF' b)
      (ratFuncConstantExtensionBasis_apply H h hXF' b))

/-- `ratFuncConstantExtensionTensorEquiv` evaluates a pure tensor by multiplying in `F'`. -/
@[simp]
theorem ratFuncConstantExtensionTensorEquiv_tmul
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (r : RatFunc K) (f : F) :
    ratFuncConstantExtensionTensorEquiv H h hX hXF' (r ⊗ₜ[RatFunc k] f) =
      algebraMap (RatFunc K) F' r * algebraMap F F' f := by
  simp [ratFuncConstantExtensionTensorEquiv, AlgHom.liftEquiv_tmul, Algebra.smul_def]

/-- The inverse of `ratFuncConstantExtensionTensorEquiv` sends products to pure tensors. -/
@[simp]
theorem ratFuncConstantExtensionTensorEquiv_symm_mul
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (r : RatFunc K) (f : F) :
    (ratFuncConstantExtensionTensorEquiv H h hX hXF').symm
        (algebraMap (RatFunc K) F' r * algebraMap F F' f) =
      r ⊗ₜ[RatFunc k] f := by
  apply (ratFuncConstantExtensionTensorEquiv H h hX hXF').injective
  simp

/-- The inverse of `ratFuncConstantExtensionTensorEquiv` sends `algebraMap F F' f` to
`1 ⊗ₜ f`. -/
@[simp]
theorem ratFuncConstantExtensionTensorEquiv_symm_algebraMap
    (H : (IsScalarTower.toAlgHom k K F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F K F' = ⊤)
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (f : F) :
    (ratFuncConstantExtensionTensorEquiv H h hX hXF').symm (algebraMap F F' f) =
      1 ⊗ₜ[RatFunc k] f := by
  apply (ratFuncConstantExtensionTensorEquiv H h hX hXF').injective
  simp

end TensorEquiv

section RatFuncFractionField

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

omit [Algebra k F'] [IsScalarTower k K F'] [IsScalarTower k F F']

section Equiv

variable [Algebra (F ⊗[k] K) F']
  [IsScalarTower F (F ⊗[k] K) F'] [IsScalarTower K (F ⊗[k] K) F']
  [IsFractionRing (F ⊗[k] K) F']
  [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']

/-- **The `RatFunc K`-algebra isomorphism `RatFunc K ⊗[RatFunc k] F ≃ₐ[RatFunc K] F'`** for
any fraction field `F'` of `F ⊗[k] K` equipped with a compatible `RatFunc K`-algebra
structure, where `RatFunc K` carries a `k`-compatible `RatFunc k`-algebra structure sending
`RatFunc.X` to `RatFunc.X`. -/
noncomputable def ratFuncFractionFieldEquiv
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X) :
    RatFunc K ⊗[RatFunc k] F ≃ₐ[RatFunc K] F' :=
  let : Algebra k F' := ((algebraMap (F ⊗[k] K) F').comp (algebraMap k (F ⊗[k] K))).toAlgebra
  have : IsScalarTower k (F ⊗[k] K) F' := .of_algebraMap_eq' rfl
  have : IsScalarTower k F F' := .to₁₂₄ k F (F ⊗[k] K) F'
  have : IsScalarTower k K F' := .to₁₂₄ k K (F ⊗[k] K) F'
  ratFuncConstantExtensionTensorEquiv
    (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
    (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k))
    hX hXF'

@[simp]
theorem ratFuncFractionFieldEquiv_tmul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (r : RatFunc K) (f : F) :
    ratFuncFractionFieldEquiv hX hXF' (r ⊗ₜ[RatFunc k] f) =
      algebraMap (RatFunc K) F' r * algebraMap F F' f := by
  simp only [ratFuncFractionFieldEquiv, ratFuncConstantExtensionTensorEquiv_tmul]

@[simp]
theorem ratFuncFractionFieldEquiv_symm_mul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (r : RatFunc K) (f : F) :
    (ratFuncFractionFieldEquiv hX hXF').symm
        (algebraMap (RatFunc K) F' r * algebraMap F F' f) =
      r ⊗ₜ[RatFunc k] f := by
  apply (ratFuncFractionFieldEquiv hX hXF').injective
  simp

@[simp]
theorem ratFuncFractionFieldEquiv_symm_algebraMap
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X)
    (hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X)
    (f : F) :
    (ratFuncFractionFieldEquiv hX hXF').symm (algebraMap F F' f) = 1 ⊗ₜ[RatFunc k] f := by
  apply (ratFuncFractionFieldEquiv hX hXF').injective
  simp

end Equiv

section CanonicalEquiv

variable [Algebra (F ⊗[k] K) F']
  [IsScalarTower F (F ⊗[k] K) F'] [IsScalarTower K (F ⊗[k] K) F']
  [IsFractionRing (F ⊗[k] K) F']

variable (F F') in
/-- **Canonical `K`-algebra equivalence `F' ≃ₐ[K] RatFunc K ⊗[RatFunc k] F`** for any fraction
field `F'` of `F ⊗[k] K`, when `F` is algebraic over `RatFunc k` and `RatFunc K` carries a
`k`-compatible `RatFunc k`-algebra structure sending `RatFunc.X` to `RatFunc.X`. No prior
`RatFunc K`-algebra structure on `F'` is needed: the equivalence sends `algebraMap F F' f` to
`1 ⊗ₜ f`, while its inverse evaluates pure tensors by multiplying in `F'` with `RatFunc.X`
acting as `algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)`. -/
noncomputable def fractionFieldEquivRatFuncTensor
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) :
    F' ≃ₐ[K] RatFunc K ⊗[RatFunc k] F :=
  let hx' : Transcendental K (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) :=
    transcendental_algebraMap_X_of_isFractionRing_tensorProduct (k := k)
  let : Algebra (RatFunc K) F' := ratFuncAlgebraOfTranscendental hx'
  have : IsScalarTower K (RatFunc K) F' := isScalarTower_ratFuncAlgebraOfTranscendental hx'
  have : IsScalarTower K (RatFunc K) (RatFunc K ⊗[RatFunc k] F) := .of_algebraMap_eq fun _ ↦ by simp
  have hXF' : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) F' RatFunc.X :=
    (algebraMap_ratFuncAlgebraOfTranscendental_X hx').symm
  ((ratFuncFractionFieldEquiv (k := k) hX hXF').restrictScalars K).symm

/-- On a polynomial in `K[X]` tensored with `f ∈ F`, the inverse of
`fractionFieldEquivRatFuncTensor` evaluates the polynomial at the image of `RatFunc.X` in `F'`
and multiplies by `algebraMap F F' f`. -/
@[simp]
theorem fractionFieldEquivRatFuncTensor_symm_algebraMap_polynomial_tmul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (p : K[X]) (f : F) :
    (fractionFieldEquivRatFuncTensor F F' hX).symm
        (algebraMap K[X] (RatFunc K) p ⊗ₜ[RatFunc k] f) =
      Polynomial.aeval (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) p *
        algebraMap F F' f := by
  let hx' : Transcendental K (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) :=
    transcendental_algebraMap_X_of_isFractionRing_tensorProduct (k := k)
  let : Algebra (RatFunc K) F' := ratFuncAlgebraOfTranscendental hx'
  have : IsScalarTower K (RatFunc K) F' := isScalarTower_ratFuncAlgebraOfTranscendental hx'
  have hp : algebraMap (RatFunc K) F' (algebraMap K[X] (RatFunc K) p) =
      Polynomial.aeval (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) p := by
    rw [← algebraMap_ratFuncAlgebraOfTranscendental_X hx', Polynomial.aeval_algebraMap_apply,
      RatFunc.aeval_X_left_eq_algebraMap]
  simp only [fractionFieldEquivRatFuncTensor, AlgEquiv.symm_symm, AlgEquiv.coe_restrictScalars,
    ratFuncFractionFieldEquiv_tmul]
  rw [hp]

@[simp]
theorem fractionFieldEquivRatFuncTensor_symm_one_tmul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (f : F) :
    (fractionFieldEquivRatFuncTensor F F' hX).symm (1 ⊗ₜ[RatFunc k] f) =
      algebraMap F F' f := by
  rw [← map_one (algebraMap K[X] (RatFunc K)),
    fractionFieldEquivRatFuncTensor_symm_algebraMap_polynomial_tmul, map_one, one_mul]

/-- On a constant `RatFunc.C c` tensored with `f ∈ F`, the inverse of
`fractionFieldEquivRatFuncTensor` multiplies `algebraMap K F' c` by `algebraMap F F' f`. -/
@[simp]
theorem fractionFieldEquivRatFuncTensor_symm_C_tmul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (c : K) (f : F) :
    (fractionFieldEquivRatFuncTensor F F' hX).symm (RatFunc.C c ⊗ₜ[RatFunc k] f) =
      algebraMap K F' c * algebraMap F F' f := by
  rw [← RatFunc.algebraMap_C, fractionFieldEquivRatFuncTensor_symm_algebraMap_polynomial_tmul,
    Polynomial.aeval_C]

@[simp]
theorem fractionFieldEquivRatFuncTensor_symm_X_tmul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (f : F) :
    (fractionFieldEquivRatFuncTensor F F' hX).symm (RatFunc.X ⊗ₜ[RatFunc k] f) =
      algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) * algebraMap F F' f := by
  rw [← RatFunc.algebraMap_X, fractionFieldEquivRatFuncTensor_symm_algebraMap_polynomial_tmul,
    Polynomial.aeval_X]

/-- On a fraction of polynomials in `K[X]` tensored with `f ∈ F`, the inverse of
`fractionFieldEquivRatFuncTensor` evaluates numerator and denominator at the parameter in
`F'`. -/
theorem fractionFieldEquivRatFuncTensor_symm_div_algebraMap_polynomial_tmul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (p q : K[X]) (f : F) :
    (fractionFieldEquivRatFuncTensor F F' hX).symm
        ((algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) ⊗ₜ[RatFunc k] f) =
      (Polynomial.aeval (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) p /
        Polynomial.aeval (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) q) *
        algebraMap F F' f := by
  let φ : RatFunc K →+* F' :=
    (fractionFieldEquivRatFuncTensor F F' hX).symm.toRingHom.comp
      Algebra.TensorProduct.includeLeftRingHom
  have hmul (r : RatFunc K) :
      (fractionFieldEquivRatFuncTensor F F' hX).symm (r ⊗ₜ[RatFunc k] f) =
        φ r * (fractionFieldEquivRatFuncTensor F F' hX).symm (1 ⊗ₜ[RatFunc k] f) := by
    simp only [φ, RingEquiv.toRingHom_eq_coe, RingHom.comp_apply, RingHom.coe_coe,
      AlgEquiv.coe_toRingEquiv, Algebra.TensorProduct.includeLeftRingHom_apply]
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hφ (g : K[X]) :
      φ (algebraMap K[X] (RatFunc K) g) =
        Polynomial.aeval (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) g := by
    simp [φ]
  rw [hmul, fractionFieldEquivRatFuncTensor_symm_one_tmul, map_div₀ φ, hφ, hφ]

/-- On an arbitrary pure tensor `r ⊗ₜ[RatFunc k] f`, the inverse of
`fractionFieldEquivRatFuncTensor` evaluates `r.num` and `r.denom` at the parameter in `F'`
and multiplies their quotient by `algebraMap F F' f`. -/
theorem fractionFieldEquivRatFuncTensor_symm_tmul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (r : RatFunc K) (f : F) :
    (fractionFieldEquivRatFuncTensor F F' hX).symm (r ⊗ₜ[RatFunc k] f) =
      (Polynomial.aeval (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) r.num /
        Polynomial.aeval (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) r.denom) *
        algebraMap F F' f := by
  conv_lhs => rw [← RatFunc.num_div_denom r]
  exact fractionFieldEquivRatFuncTensor_symm_div_algebraMap_polynomial_tmul hX r.num r.denom f

/-- `fractionFieldEquivRatFuncTensor` sends an element from `F` to `1 ⊗ₜ f`. -/
@[simp]
theorem fractionFieldEquivRatFuncTensor_algebraMap_left
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (f : F) :
    fractionFieldEquivRatFuncTensor F F' hX (algebraMap F F' f) = 1 ⊗ₜ[RatFunc k] f := by
  apply (fractionFieldEquivRatFuncTensor F F' hX).symm.injective
  simp

/-- On the image of a pure tensor `f ⊗ₜ[k] c` in `F'`, `fractionFieldEquivRatFuncTensor` is
`RatFunc.C c ⊗ₜ[RatFunc k] f`. -/
@[simp]
theorem fractionFieldEquivRatFuncTensor_algebraMap_tmul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (f : F) (c : K) :
    fractionFieldEquivRatFuncTensor F F' hX (algebraMap (F ⊗[k] K) F' (f ⊗ₜ[k] c)) =
      RatFunc.C c ⊗ₜ[RatFunc k] f := by
  have hfc :
      algebraMap (F ⊗[k] K) F' (f ⊗ₜ[k] c) = algebraMap F F' f * algebraMap K F' c := by
    rw [IsScalarTower.algebraMap_apply F (F ⊗[k] K) F' f,
      IsScalarTower.algebraMap_apply K (F ⊗[k] K) F' c, ← map_mul]
    simp [Algebra.TensorProduct.right_algebraMap_apply]
  apply (fractionFieldEquivRatFuncTensor F F' hX).symm.injective
  simp [hfc, mul_comm]

end CanonicalEquiv

section DomainAndField

omit [Field F'] [Algebra K F'] [Algebra F F']

/-- **When `F ⊗[k] K` is a domain and `F` is algebraic over `RatFunc k`, the base-changed
algebra `RatFunc K ⊗[RatFunc k] F` is a field** (for any `k`-compatible `RatFunc k`-algebra
structure on `RatFunc K` sending `RatFunc.X` to `RatFunc.X`). -/
theorem isField_ratFunc_tensorProduct_of_isDomain_tensorProduct
    [IsDomain (F ⊗[k] K)]
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) :
    IsField (RatFunc K ⊗[RatFunc k] F) :=
  MulEquiv.isField (Field.toIsField (FractionRing (F ⊗[k] K)))
    (fractionFieldEquivRatFuncTensor F (FractionRing (F ⊗[k] K)) hX).symm.toMulEquiv

/-- For a geometrically reduced extension `F/k` with exact constants that is algebraic over
`RatFunc k`, the base-changed algebra `RatFunc K ⊗[RatFunc k] F` is a field for every field
extension `K/k` and every `k`-compatible `RatFunc k`-algebra structure on `RatFunc K` sending
`RatFunc.X` to `RatFunc.X`. -/
theorem isField_ratFunc_tensorProduct_of_isGeometricallyReduced
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) :
    IsField (RatFunc K ⊗[RatFunc k] F) := by
  have := isDomain_tensorProduct_of_isGeometricallyReduced hex K
  exact isField_ratFunc_tensorProduct_of_isDomain_tensorProduct hX

end DomainAndField

end RatFuncFractionField

end RatFunc

end TauCeti
