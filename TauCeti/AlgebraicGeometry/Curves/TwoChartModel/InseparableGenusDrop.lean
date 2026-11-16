/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.BaseChange
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Genus
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.InseparableGenusDrop

import TauCeti.AlgebraicGeometry.Curves.Genus.ConstantExtension

/-!
# A regular proper geometrically integral curve that is not geometrically regular

Over a perfect field every regular proper curve is smooth
(`TauCeti.AlgebraicGeometry.twoChartModel.smoothOfRelativeDimension_one_of_perfectField`). Over an
imperfect field, regularity and geometric integrality do not imply geometric regularity or
smoothness. This file constructs the
canonical scheme-theoretic counterexample by forming the two-chart model `curveModel p` of Deuring's
function field `F = k(x, y)` defined by `y ^ 2 = x ^ p - t` over `k = 𝔽_p(t)`
(`TauCeti.GenusDrop.curveField p`) for an odd prime `p`.

For every odd prime `p`, `curveModel p` is a regular, proper, geometrically integral curve over
`k = 𝔽_p(t)` of genus `(p - 1) / 2`. However, after the purely inseparable constant extension
`k' = 𝔽_p(s)` with `s ^ p = t` (`RatFunc (ZMod p)`), the compositum `F · k' = 𝔽_p(s)(w)` has genus
`0 < (p - 1) / 2`. Consequently, the base-changed curve `curveModel p ×_k Spec k'` is an integral
proper curve over `k'` that is **not regular** (`not_isRegular_baseChangeCurveModel`): its local
ring above `y = 0, x = s` has normalization `k'[w]_{(w)}` with cusp-like conductor `(w ^ (p - 1))`.
Hence `curveModel p` is neither geometrically regular nor smooth over `k`.

## Main declarations

* `TauCeti.GenusDrop.curveModel`: the regular proper two-chart model of `y ^ 2 = x ^ p - t` over
  `k = 𝔽_p(t)`.
* `TauCeti.GenusDrop.geometricallyIntegral_curveModel`: for `p ≠ 2`, `curveModel p` is geometrically
  integral (and geometrically reduced) over `k`.
* `TauCeti.GenusDrop.genus_curveModel`: for `p ≠ 2`,
  `(curveModel p).genus (constants p) = (p - 1) / 2`.
* `TauCeti.GenusDrop.not_isRegular_of_isPullback_curveModel` and
  `not_isRegular_baseChangeCurveModel`: for `p ≠ 2`, the base change of `curveModel p` to `𝔽_p(s)`
  is a curve over `𝔽_p(s)` that is not regular.
* `TauCeti.GenusDrop.not_geometricallyRegular_curveModel` and `not_smooth_curveModel`: for `p ≠ 2`,
  `curveModel p` is neither geometrically regular nor smooth over `k`.

## References

* M. Deuring, *Reduktion algebraischer Funktionenkörper nach Primdivisoren des Konstantenkörpers*,
  Math. Z. 47 (1942), 643–654.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.6.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford GTM 6, 2002, Example 4.3.20 and
  Section 7.5.
-/

public section

open CategoryTheory Limits _root_.AlgebraicGeometry TauCeti.AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti.GenusDrop

variable (p : ℕ) [hp : Fact p.Prime]

/-- `curveField p` is an algebraic function field of transcendence degree one over `constants p`. -/
theorem isFunctionField_curveField : IsFunctionField (constants p) (curveField p) := by
  have hrank := finrank_ratFunc_eq_two_of_sq_eq
    (irreducible_X_pow_sub_C_radicand p).squarefree
    (by rw [Polynomial.natDegree_X_pow_sub_C]; exact hp.out.pos)
    (adjoin_genY'_eq_top p) (sq_genY' p)
  have : FiniteDimensional (RatFunc (constants p)) (curveField p) :=
    Module.finite_of_finrank_pos (by omega)
  exact isFunctionField_iff_functionField.mpr inferInstance

/-- The coordinate `x = genX' p` in `curveField p` is nonzero. -/
theorem genX'_ne_zero : genX' p ≠ 0 :=
  (transcendental_genX' p).ne_zero

/-- **The regular proper curve model of `y ^ 2 = x ^ p - t` over `k = 𝔽_p(t)`**, constructed as the
two-chart normalization model associated to `x = genX' p`. -/
noncomputable abbrev curveModel : Scheme.{0} :=
  twoChartModel (isFunctionField_curveField p) (genX'_ne_zero p)

/-- `curveModel p` is a proper integral curve over `constants p`. -/
instance isCurveOver_curveModel : (curveModel p).IsCurveOver (constants p) :=
  twoChartModel.isCurveOver (transcendental_genX' p)

/-- Away from characteristic two, `curveField p` is geometrically reduced over `constants p`: it is
a separable quadratic extension of the rational function field `RatFunc (constants p)`. -/
theorem isGeometricallyReduced_curveField (h2 : p ≠ 2) :
    Algebra.IsGeometricallyReduced (constants p) (curveField p) := by
  obtain ⟨_, _⟩ := finiteDimensional_and_isSeparable_of_sq_eq
    (CharP.cast_ne_zero_of_ne_of_prime (constants p) Nat.prime_two h2)
    (irreducible_X_pow_sub_C_radicand p).squarefree
    (by rw [Polynomial.natDegree_X_pow_sub_C]; exact hp.out.pos)
    (adjoin_genY'_eq_top p) (sq_genY' p)
  rw [Algebra.isGeometricallyReduced_field_iff]
  have := isReduced_tensorProduct_of_isReduced_of_isSeparable (constants p)
    (E := RatFunc (constants p)) (F := curveField p) (AlgebraicClosure (constants p))
  exact isReduced_of_injective
    (Algebra.TensorProduct.comm (constants p) (AlgebraicClosure (constants p)) (curveField p))
    (Algebra.TensorProduct.comm (constants p) (AlgebraicClosure (constants p))
      (curveField p)).injective

/-- **For `p ≠ 2`, `curveModel p` is geometrically integral over `k = 𝔽_p(t)`.** -/
theorem geometricallyIntegral_curveModel (h2 : p ≠ 2) :
    GeometricallyIntegral (curveModel p ↘ Spec (.of (constants p))) :=
  (twoChartModel.geometricallyIntegral_iff (transcendental_genX' p)).mpr
    ⟨isIntegrallyClosedIn_curveField p h2, isGeometricallyReduced_curveField p h2⟩

/-- For `p ≠ 2`, `curveModel p` is geometrically reduced over `k = 𝔽_p(t)`. -/
theorem geometricallyReduced_curveModel (h2 : p ≠ 2) :
    GeometricallyReduced (curveModel p ↘ Spec (.of (constants p))) := by
  have := geometricallyIntegral_curveModel p h2
  infer_instance

/-- **For `p ≠ 2`, the cohomological genus `dim_k H¹(curveModel p, 𝒪)` is `(p - 1) / 2`.** -/
theorem genus_curveModel (h2 : p ≠ 2) :
    haveI := finiteDimensional_cohomology_one_trivial_of_isProper (constants p)
      (X := curveModel p) (twoChartModel.topologicalKrullDim_eq_one (transcendental_genX' p))
    (curveModel p).genus (constants p) = (p - 1) / 2 := by
  rw [twoChartModel.genus_eq_genus (transcendental_genX' p) (isIntegrallyClosedIn_curveField p h2),
    genus_curveField p h2]

/-- **Any pullback of `curveModel p` (`p ≠ 2`) to `k' = 𝔽_p(s)` is non-regular**, because the genus
drops from `(p - 1) / 2` to `0`. -/
theorem not_isRegular_of_isPullback_curveModel (h2 : p ≠ 2) {Y : Scheme.{0}}
    [Y.Over (Spec (.of (RatFunc (ZMod p))))] {g : Y ⟶ curveModel p}
    (H : IsPullback g (Y ↘ Spec (.of (RatFunc (ZMod p))))
      (curveModel p ↘ Spec (.of (constants p)))
      (Spec.map (CommRingCat.ofHom (algebraMap (constants p) (RatFunc (ZMod p)))))) :
    ¬ IsRegular Y := by
  have := geometricallyIntegral_curveModel p h2
  exact not_isRegular_of_isPullback_of_genus_lt_of_algEquiv H
    (twoChartModel.functionFieldEquiv (transcendental_genX' p)).symm
    (constantCompositum_eq_top p h2) (genus_lt_genus p h2)

/-- The explicit base change `curveModel p ×_k Spec 𝔽_p(s)` over `𝔽_p(s)`. -/
noncomputable abbrev baseChangeCurveModel : Scheme.{0} :=
  pullback (curveModel p ↘ Spec (.of (constants p)))
    (Spec.map (CommRingCat.ofHom (algebraMap (constants p) (RatFunc (ZMod p)))))

/-- For `p ≠ 2`, `baseChangeCurveModel p` is a proper integral curve over `𝔽_p(s)`. -/
theorem isCurveOver_baseChangeCurveModel (h2 : p ≠ 2) :
    letI : (baseChangeCurveModel p).Over (Spec (.of (RatFunc (ZMod p)))) := ⟨pullback.snd _ _⟩
    (baseChangeCurveModel p).IsCurveOver (RatFunc (ZMod p)) := by
  let _ : (baseChangeCurveModel p).Over (Spec (.of (RatFunc (ZMod p)))) := ⟨pullback.snd _ _⟩
  have := geometricallyIntegral_curveModel p h2
  exact twoChartModel.isCurveOver_of_isPullback (transcendental_genX' p)
    (IsPullback.of_hasPullback (curveModel p ↘ Spec (.of (constants p)))
      (Spec.map (CommRingCat.ofHom (algebraMap (constants p) (RatFunc (ZMod p))))))

/-- **For `p ≠ 2`, `baseChangeCurveModel p` is a curve over `𝔽_p(s)` that is not regular.** -/
theorem not_isRegular_baseChangeCurveModel (h2 : p ≠ 2) :
    ¬ IsRegular (baseChangeCurveModel p) := by
  let _ : (baseChangeCurveModel p).Over (Spec (.of (RatFunc (ZMod p)))) := ⟨pullback.snd _ _⟩
  exact not_isRegular_of_isPullback_curveModel p h2
    (IsPullback.of_hasPullback (curveModel p ↘ Spec (.of (constants p)))
      (Spec.map (CommRingCat.ofHom (algebraMap (constants p) (RatFunc (ZMod p))))))

/-- **For `p ≠ 2`, `curveModel p` is regular and geometrically integral over `𝔽_p(t)`, but NOT
geometrically regular over `𝔽_p(t)`.** -/
theorem not_geometricallyRegular_curveModel (h2 : p ≠ 2) :
    ¬ GeometricallyRegular (curveModel p ↘ Spec (.of (constants p))) := fun hgeom ↦
  not_isRegular_baseChangeCurveModel p h2
    (hgeom.geometrically_isRegular _ _ _
      (IsPullback.of_hasPullback (curveModel p ↘ Spec (.of (constants p)))
        (Spec.map (CommRingCat.ofHom (algebraMap (constants p) (RatFunc (ZMod p)))))))

/-- **For `p ≠ 2`, `curveModel p` is not smooth over `𝔽_p(t)`.** -/
theorem not_smooth_curveModel (h2 : p ≠ 2) :
    ¬ Smooth (curveModel p ↘ Spec (.of (constants p))) := by
  rw [twoChartModel.smooth_iff_geometricallyRegular]
  exact not_geometricallyRegular_curveModel p h2

end TauCeti.GenusDrop
