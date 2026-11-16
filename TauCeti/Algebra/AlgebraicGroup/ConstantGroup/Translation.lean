/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Translation

/-!
# Right translations on finite constant groups

Under `TauCeti.ConstantGroup.functionAlgEquiv`, right translation on the coordinate Hopf algebra
`TauCeti.ConstantGroup.coordinateRing R G` of a finite group `G` by the rational point of `g ∈ G`
sends a function `f : G → R` to `h ↦ f (h * g)`. Summing all right translates over `G` therefore
produces the constant function equal to `∑ g : G, f g`.

## Main declarations

* `TauCeti.ConstantGroup.functionAlgEquiv_rightTranslationAlgHom_toPoints_apply`: right translation
  by `toPoints R G g` acts on functions as `h ↦ f (h * g)`.
* `TauCeti.ConstantGroup.sum_rightTranslationAlgHom_toPoints`: summing all right translates over `G`
  equals `algebraMap R (coordinateRing R G) (∑ g : G, functionAlgEquiv R G a g)`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 3.3.
* J. S. Milne, *Algebraic Groups* (2017), Section 2.a.
-/

public section

namespace TauCeti.ConstantGroup

universe u v

variable {R : Type u} [CommRing R]

/-- Under `functionAlgEquiv`, right translation on the coordinate ring of a finite constant group
by the rational point of `g` acts as `h ↦ f (h * g)`. -/
theorem functionAlgEquiv_rightTranslationAlgHom_toPoints_apply {G : Type v} [Group G] [Finite G]
    (g : G) (a : coordinateRing R G) (h : G) :
    functionAlgEquiv R G (HopfAlgebra.rightTranslationAlgHom (toPoints R G g) a) h =
      functionAlgEquiv R G a (h * g) := by
  rw [← eval_apply, ← toPoints_apply, HopfAlgebra.ofConv_rightTranslationAlgHom, ← map_mul,
    toPoints_apply, eval_apply]

/-- Summing all right translates of a coordinate function on a finite constant group yields the
constant function equal to the sum of its values over `G`. -/
theorem sum_rightTranslationAlgHom_toPoints {G : Type v} [Group G] [Fintype G]
    (a : coordinateRing R G) :
    ∑ g : G, HopfAlgebra.rightTranslationAlgHom (toPoints R G g) a =
      algebraMap R (coordinateRing R G) (∑ g : G, functionAlgEquiv R G a g) := by
  apply (functionAlgEquiv R G).injective
  ext h
  rw [AlgEquiv.commutes, Pi.algebraMap_apply, Algebra.algebraMap_self_apply, map_sum,
    Fintype.sum_apply]
  simp_rw [functionAlgEquiv_rightTranslationAlgHom_toPoints_apply]
  exact Equiv.sum_comp (Equiv.mulLeft h) (functionAlgEquiv R G a)

end TauCeti.ConstantGroup
