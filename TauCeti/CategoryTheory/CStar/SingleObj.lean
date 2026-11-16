/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.CStar.Basic
public import TauCeti.CategoryTheory.Dagger.SingleObj

/-!
# Single-object C⋆-categories

Every unital complex C⋆-algebra `A` gives rise to a single-object C⋆-category
`CategoryTheory.SingleObj A` whose unique Hom space is definitionally `A` with its C⋆-algebra norm,
opposite multiplication for categorical composition, and `star` for the dagger involution.

## Main declarations

* `CategoryTheory.SingleObj.instCStarCategory`: `CStarCategory (SingleObj A)` for
  `[CStarAlgebra A]`.
-/

public section

open CategoryTheory TauCeti

universe u

namespace CategoryTheory.SingleObj

/-- A unital complex C⋆-algebra `A` viewed as a single-object C⋆-category, with Hom spaces
definitionally equal to `A` carrying its C⋆-algebra norm. -/
instance instCStarCategory (A : Type u) [CStarAlgebra A] : CStarCategory (SingleObj A) where
  homNorm _ _ := inferInstanceAs (Norm A)
  homMetricSpace _ _ := inferInstanceAs (MetricSpace A)
  homCompleteSpace _ _ := inferInstanceAs (CompleteSpace A)
  dist_eq f g := dist_eq_norm_neg_add (f : A) (g : A)
  norm_smul_le r f := norm_smul_le r (f : A)
  norm_comp_le f g := norm_mul_le (g : A) (f : A)
  norm_mul_self_le f := (CStarRing.norm_star_mul_self (x := (f : A))).ge
  exists_comp_dagger_eq f := ⟨(f : A), rfl⟩

end CategoryTheory.SingleObj
