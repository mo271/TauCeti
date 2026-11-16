/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.LinearDisjoint
public import TauCeti.FieldTheory.Separable.Regular
public import TauCeti.RingTheory.TensorProduct.FractionRing

/-!
# Constant extension through the fraction field of a tensor product

Suppose `F ⊗[k] K` is a domain. Its fraction field, with the scalar maps from both
factors, is the linearly disjoint compositum `F · K`. If `F/k` is a one-variable
function field, it is therefore a one-variable function field over `K` too,
transcendental and separating parameters of `F/k` remain transcendental and separating
in `Frac(F ⊗[k] K)` over `K`, and `[Frac(F ⊗[k] K) : K(x)] = [F : k(x)]` for every
`x ∈ F` (as well as `[Frac(F ⊗[k] K) : K(X)] = [F : k(X)]` for compatible
`RatFunc`-algebra structures). The extension `K/k` need not be algebraic.

We retain the actual fraction-field carrier rather than asserting that the tensor
product itself is a field; the results apply to any specified fraction field with
compatible scalar maps from `F` and `K`, without requiring a pre-supplied `k`-algebra
structure on the fraction field.

## Main results

* `TauCeti.constantCompositum_eq_top_of_isFractionRing_tensorProduct`: the images of `F`
  and `K` generate any fraction field `Q` of `F ⊗[k] K` as a compositum `F · K = ⊤`.
* `Transcendental.algebraMap_of_isFractionRing_tensorProduct`,
  `TauCeti.isSeparable_adjoin_image_of_isFractionRing_tensorProduct`,
  `TauCeti.isSeparable_adjoin_simple_of_isFractionRing_tensorProduct`: persistence of
  transcendental and separating generators in `Frac(F ⊗[k] K)`.
* `TauCeti.IsFunctionField.of_isFractionRing_tensorProduct`,
  `TauCeti.finrank_over_adjoin_simple_eq_of_isFractionRing_tensorProduct`: preservation
  of the function-field property and degree over any `x ∈ F`.
* `TauCeti.transcendental_algebraMap_X_of_isFractionRing_tensorProduct`,
  `TauCeti.finiteDimensional_ratFunc_of_isFractionRing_tensorProduct`,
  `TauCeti.isSeparable_ratFunc_of_isFractionRing_tensorProduct`,
  `TauCeti.finrank_ratFunc_eq_of_isFractionRing_tensorProduct`: the corresponding
  persistence and degree-preservation statements over `RatFunc`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
* S. Lang, *Introduction to Algebraic Geometry*, Chapter III, Section 1.
* S. Lang, *Algebra*, the theory of linearly disjoint field extensions.
-/

public section

open scoped TensorProduct IntermediateField

namespace TauCeti

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

section CommRing

variable {k F K Q : Type*} [CommRing k] [Field F] [Field K] [Field Q]
  [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q]
  [Algebra F Q] [Algebra K Q]
  [IsScalarTower F (F ⊗[k] K) Q] [IsScalarTower K (F ⊗[k] K) Q]
  [IsFractionRing (F ⊗[k] K) Q]

include k in
/-- Any fraction field `Q` of `F ⊗[k] K` is the field compositum `F · K` of its two
factors. -/
theorem constantCompositum_eq_top_of_isFractionRing_tensorProduct :
    constantCompositum F K Q = ⊤ := by
  rw [constantCompositum_def]
  exact adjoin_range_right_eq_top_of_isFractionRing_tensorProduct (k := k)

end CommRing

variable {k F K Q : Type*} [Field k] [Field F] [Field K] [Field Q]
  [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q]
  [Algebra F Q] [Algebra K Q]
  [IsScalarTower F (F ⊗[k] K) Q] [IsScalarTower K (F ⊗[k] K) Q]

private theorem with_baseAlgebra {P : Prop}
    (h : ∀ (_ : Algebra k Q), @IsScalarTower k F Q _ _ _ → @IsScalarTower k K Q _ _ _ → P) :
    P := by
  let : Algebra k Q := ((algebraMap (F ⊗[k] K) Q).comp (algebraMap k (F ⊗[k] K))).toAlgebra
  have : IsScalarTower k (F ⊗[k] K) Q := .of_algebraMap_eq' rfl
  have hF : IsScalarTower k F Q := .to₁₂₄ k F (F ⊗[k] K) Q
  have hK : IsScalarTower k K Q := .to₁₂₄ k K (F ⊗[k] K) Q
  exact h ‹_› hF hK

variable [IsFractionRing (F ⊗[k] K) Q]

/-- If `F` is separable algebraic over `k(S)`, then any fraction field `Q` of `F ⊗[k] K`
is separable algebraic over `K(S)`. -/
theorem isSeparable_adjoin_image_of_isFractionRing_tensorProduct {S : Set F}
    [Algebra.IsSeparable (IntermediateField.adjoin k S) F] :
    Algebra.IsSeparable (IntermediateField.adjoin K (algebraMap F Q '' S)) Q :=
  with_baseAlgebra (k := k) (F := F) (K := K) (Q := Q) fun _ _ _ ↦
    isSeparable_adjoin_image_of_constantCompositum_eq_top (k := k)
      (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k))

/-- A separating parameter `x` of `F/k` remains separating over `K` in any fraction
field `Q` of `F ⊗[k] K`. -/
theorem isSeparable_adjoin_simple_of_isFractionRing_tensorProduct (x : F)
    [Algebra.IsSeparable k⟮x⟯ F] :
    Algebra.IsSeparable K⟮algebraMap F Q x⟯ Q := by
  have h := isSeparable_adjoin_image_of_isFractionRing_tensorProduct
    (k := k) (K := K) (Q := Q) (S := {x})
  rwa [Set.image_singleton] at h

/-- An element of `F` transcendental over `k` remains transcendental over `K` in any
fraction field `Q` of `F ⊗[k] K`. -/
theorem _root_.Transcendental.algebraMap_of_isFractionRing_tensorProduct {x : F}
    (hx : Transcendental k x) : Transcendental K (algebraMap F Q x) :=
  with_baseAlgebra (k := k) (F := F) (K := K) (Q := Q) fun _ _ _ ↦
    (linearDisjoint_of_isFractionRing_tensorProduct (k := k)).transcendental_algebraMap hx

/-- A fraction field of a domain tensor product is a one-variable function field
over the enlarged constants. -/
theorem IsFunctionField.of_isFractionRing_tensorProduct (hF : IsFunctionField k F) :
    IsFunctionField K Q :=
  with_baseAlgebra (k := k) (F := F) (K := K) (Q := Q) fun _ _ _ ↦
    hF.of_constantCompositum_eq_top_of_linearDisjoint
      (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
      (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k))

/-- Tensor-fraction-field extension of constants preserves the degree over any element
`x ∈ F`. Neither the constants nor the relative extension need be separable or finite. -/
theorem finrank_over_adjoin_simple_eq_of_isFractionRing_tensorProduct (x : F) :
    Module.finrank K⟮algebraMap F Q x⟯ Q = Module.finrank k⟮x⟯ F :=
  with_baseAlgebra (k := k) (F := F) (K := K) (Q := Q) fun _ _ _ ↦
    finrank_over_adjoin_simple_eq_of_linearDisjoint
      (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
      (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k)) x

/-- If `F/k` is a geometrically reduced one-variable function field with exact constants,
then the fraction field of `F ⊗[k] K` is a one-variable function field over `K`.
The enlarged constant field may be transcendental over the original one. -/
theorem IsFunctionField.fractionRing_tensorProduct (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F] :
    letI := isDomain_tensorProduct_of_isGeometricallyReduced hex K
    IsFunctionField K (FractionRing (F ⊗[k] K)) := by
  have := isDomain_tensorProduct_of_isGeometricallyReduced hex K
  exact hF.of_isFractionRing_tensorProduct

/-- If `F/k` is a one-variable function field with exact constants and a separating
element `x`, then the fraction field of `F ⊗[k] K` is a one-variable function field over
`K` for every field extension `K/k`. -/
theorem IsFunctionField.fractionRing_tensorProduct_of_separating (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {x : F} [Algebra.IsSeparable k⟮x⟯ F] :
    letI := isDomain_tensorProduct_of_separating hex (x := x) K
    IsFunctionField K (FractionRing (F ⊗[k] K)) := by
  have := isDomain_tensorProduct_of_separating hex (x := x) K
  exact hF.of_isFractionRing_tensorProduct

section RatFunc

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]

/-- In any fraction field `Q` of `F ⊗[k] K`, the image of `RatFunc.X` from `F` is
transcendental over `K`. -/
theorem transcendental_algebraMap_X_of_isFractionRing_tensorProduct :
    Transcendental K (algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X)) :=
  with_baseAlgebra (k := k) (F := F) (K := K) (Q := Q) fun _ _ _ ↦
    (linearDisjoint_of_isFractionRing_tensorProduct (k := k)).transcendental_algebraMap_X

variable [Algebra (RatFunc K) Q] [IsScalarTower K (RatFunc K) Q]

/-- If `F` is finite over `RatFunc k`, then any fraction field `Q` of `F ⊗[k] K` with a
compatible `RatFunc K`-algebra structure is finite over `RatFunc K`. -/
theorem finiteDimensional_ratFunc_of_isFractionRing_tensorProduct
    [FiniteDimensional (RatFunc k) F]
    (hXQ : algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) Q RatFunc.X) :
    FiniteDimensional (RatFunc K) Q :=
  with_baseAlgebra (k := k) (F := F) (K := K) (Q := Q) fun _ _ _ ↦
    finiteDimensional_ratFunc_of_constantCompositum_eq_top (k := k)
      (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k)) hXQ

/-- If `F` is separable over `RatFunc k`, then any fraction field `Q` of `F ⊗[k] K` with a
compatible `RatFunc K`-algebra structure is separable over `RatFunc K`. -/
theorem isSeparable_ratFunc_of_isFractionRing_tensorProduct
    [Algebra.IsSeparable (RatFunc k) F]
    (hXQ : algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) Q RatFunc.X) :
    Algebra.IsSeparable (RatFunc K) Q :=
  with_baseAlgebra (k := k) (F := F) (K := K) (Q := Q) fun _ _ _ ↦
    isSeparable_ratFunc_of_constantCompositum_eq_top (k := k)
      (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k)) hXQ

/-- Tensor-fraction-field extension of constants preserves the degree over `RatFunc`:
`[Q : K(X)] = [F : k(X)]`. Neither `K/k` nor `F/k(X)` need be algebraic or separable. -/
theorem finrank_ratFunc_eq_of_isFractionRing_tensorProduct
    (hXQ : algebraMap F Q (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc K) Q RatFunc.X) :
    Module.finrank (RatFunc K) Q = Module.finrank (RatFunc k) F :=
  with_baseAlgebra (k := k) (F := F) (K := K) (Q := Q) fun _ _ _ ↦
    finrank_ratFunc_eq_of_linearDisjoint
      (linearDisjoint_of_isFractionRing_tensorProduct (k := k))
      (constantCompositum_eq_top_of_isFractionRing_tensorProduct (k := k)) hXQ

end RatFunc

end TauCeti
