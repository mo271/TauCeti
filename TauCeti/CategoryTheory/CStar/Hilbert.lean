/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Analysis.InnerProductSpace.Category
public import TauCeti.CategoryTheory.CStar.Basic

/-!
# Complex Hilbert spaces as a C⋆-category

`TauCeti.HilbertCat.{0, v} ℂ` is a C⋆-category under the operator norm on `X →L[ℂ] Y` and the
Hilbert-space adjoint. Via `TauCeti.HilbertCat.endStarAlgEquiv`, the categorical spectral order on
`End X` agrees with Mathlib's Loewner order (`ContinuousLinearMap.IsPositive`) on `X →L[ℂ] X`.

## Main declarations

* `TauCeti.HilbertCat.instCStarCategory`: `CStarCategory (HilbertCat.{0, v} ℂ)`.
* `TauCeti.HilbertCat.end_le_iff`, `TauCeti.HilbertCat.end_nonneg_iff`: the spectral order on
  `End X` agrees with Mathlib's Loewner order and `ContinuousLinearMap.IsPositive`.

## References

* P. Ghez, R. Lima, and J. E. Roberts, *W⋆-categories*, Pacific J. Math. 120 (1985), 79–109.
-/

public section

noncomputable section

open CategoryTheory

universe v

namespace TauCeti.HilbertCat

instance instCStarCategory : CStarCategory (HilbertCat.{0, v} ℂ) where
  homNorm X Y := inferInstanceAs (Norm (X ⟶ Y))
  homMetricSpace X Y := inferInstanceAs (MetricSpace (X ⟶ Y))
  homCompleteSpace X Y := inferInstanceAs (CompleteSpace (X ⟶ Y))
  norm_smul_le c f := norm_smul_le c (f : _ →L[ℂ] _)
  norm_comp_le f g := ContinuousLinearMap.opNorm_comp_le g f
  norm_mul_self_le f := (ContinuousLinearMap.norm_adjoint_comp_self (f : _ →L[ℂ] _)).ge
  exists_comp_dagger_eq {X Y} f := by
    have hpos := ContinuousLinearMap.isPositive_adjoint_comp_self (f : X →L[ℂ] Y)
    obtain ⟨p, hp_sa, -, hp_sq⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
      hpos.isSelfAdjoint hpos.spectrumRestricts
    have hp_adj : ContinuousLinearMap.adjoint p = p :=
      ContinuousLinearMap.star_eq_adjoint p ▸ hp_sa.star_eq
    refine ⟨p, ?_⟩
    simpa [comp_eq_comp, dagger_eq_adjoint, sq, ContinuousLinearMap.mul_def, hp_adj]
      using hp_sq.symm

/-- The spectral order on `End X` agrees with the Loewner partial order on `X →L[ℂ] X`. -/
theorem end_le_iff {X : HilbertCat.{0, v} ℂ} {f g : End X} :
    f ≤ g ↔ ConcreteCategory.hom f.asHom ≤ ConcreteCategory.hom g.asHom := by
  simpa [hom_eq] using
    (NonUnitalStarAlgHom.map_le_map_iff (endStarAlgEquiv X) (endStarAlgEquiv X).injective).symm

/-- Nonnegativity in `End X` agrees with `ContinuousLinearMap.IsPositive` on `X →L[ℂ] X`. -/
theorem end_nonneg_iff {X : HilbertCat.{0, v} ℂ} {f : End X} :
    0 ≤ f ↔ (ConcreteCategory.hom f.asHom).IsPositive := by
  rw [end_le_iff, ContinuousLinearMap.le_def]
  simp

end TauCeti.HilbertCat
