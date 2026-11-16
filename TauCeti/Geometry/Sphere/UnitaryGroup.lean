/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.Geometry.Sphere.LinearIsometry
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic

/-!
# Action of unitary and special unitary matrix groups on the unit sphere

Through `Matrix.UnitaryGroup.toLinearIsometryEquiv`, a unitary matrix over `𝕜` (`ℝ` or `ℂ`) acts as
a linear isometry equivalence of `EuclideanSpace 𝕜 ι`, and therefore restricts to an isometric,
jointly continuous action on the unit sphere `Metric.sphere (0 : EuclideanSpace 𝕜 ι) 1`. Restricting
along the inclusion `Matrix.specialUnitaryGroup_le_unitaryGroup` gives the corresponding action of
`Matrix.specialUnitaryGroup ι 𝕜`; for `𝕜 = ℝ` these are the actions of `O(ι)` and `SO(ι)` on the
Euclidean unit sphere.

In dimension at least two, `SO(ι)` still acts transitively on the Euclidean unit sphere: `O(ι)`
acts transitively, and if an orthogonal matrix moving a basis vector `e₀` to `y` has determinant
`-1`, precomposing with the diagonal reflection negating a distinct coordinate flips the determinant
to `1` without moving `e₀`.

## Main declarations

* `Matrix.UnitaryGroup.instMulActionUnitSphere`: the action of `unitaryGroup ι 𝕜` on
  `Metric.sphere (0 : EuclideanSpace 𝕜 ι) 1`, with `IsIsometricSMul`, `ContinuousSMul`,
  `SMulCommClass` with unit scalars, and `MulAction.IsPretransitive`.
* `Matrix.specialUnitaryGroup.instMulActionUnitSphere`: the restricted action of
  `specialUnitaryGroup ι 𝕜` (for `𝕜 = ℝ`, `specialOrthogonalGroup ι ℝ`) on the unit sphere, with
  `IsIsometricSMul`, `ContinuousSMul`, and `SMulCommClass`.
* `Matrix.SpecialOrthogonalGroup.isPretransitive_unitSphere_of_two_le_card` and
  `Matrix.SpecialOrthogonalGroup.instIsPretransitiveUnitSphereFinAddTwo`: transitivity of
  `specialOrthogonalGroup` on the Euclidean unit sphere in dimension at least two.
* `Matrix.UnitaryGroup.smul_unitSphere_eq_iff` and
  `Matrix.specialUnitaryGroup.smul_unitSphere_eq_iff`: equality on the unit sphere read in raw
  matrix-vector coordinates.
-/

public section

open Metric

namespace Matrix

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

namespace UnitaryGroup

/-- The unitary matrix group acts on the Euclidean unit sphere via
`Matrix.UnitaryGroup.toLinearIsometryEquiv`. For `𝕜 = ℝ` this is the action of the orthogonal group
`Matrix.orthogonalGroup ι ℝ`. -/
noncomputable instance instMulActionUnitSphere :
    MulAction (unitaryGroup ι 𝕜) (sphere (0 : EuclideanSpace 𝕜 ι) 1) :=
  MulAction.compHom _ toLinearIsometryEquiv

/-- Acting on the unit sphere through `toLinearIsometryEquiv` agrees with the `unitaryGroup`
action. -/
@[simp]
theorem toLinearIsometryEquiv_smul_unitSphere (g : unitaryGroup ι 𝕜)
    (x : sphere (0 : EuclideanSpace 𝕜 ι) 1) :
    toLinearIsometryEquiv g • x = g • x :=
  (rfl)

/-- Coercing `g • x` from the unit sphere to `EuclideanSpace 𝕜 ι` applies matrix-vector
multiplication in coordinates. -/
@[simp]
theorem coe_smul_unitSphere (g : unitaryGroup ι 𝕜) (x : sphere (0 : EuclideanSpace 𝕜 ι) 1) :
    ((g • x : sphere (0 : EuclideanSpace 𝕜 ι) 1) : EuclideanSpace 𝕜 ι) =
      WithLp.toLp 2 ((g : Matrix ι ι 𝕜) *ᵥ x.1.ofLp) := by
  rw [← toLinearIsometryEquiv_smul_unitSphere, LinearIsometryEquiv.coe_smul_unitSphere,
    toLinearIsometryEquiv_apply]

/-- Reading `g • x` in coordinate functions `ι → 𝕜` gives `(g : Matrix ι ι 𝕜) *ᵥ x.1.ofLp`. -/
@[simp]
theorem ofLp_coe_smul_unitSphere (g : unitaryGroup ι 𝕜) (x : sphere (0 : EuclideanSpace 𝕜 ι) 1) :
    ((g • x : sphere (0 : EuclideanSpace 𝕜 ι) 1) : EuclideanSpace 𝕜 ι).ofLp =
      (g : Matrix ι ι 𝕜) *ᵥ x.1.ofLp := by
  rw [coe_smul_unitSphere, WithLp.ofLp_toLp]

/-- Two points of the unit sphere satisfy `g • x = y` if and only if `(g : Matrix ι ι 𝕜) *ᵥ x = y`
in coordinate functions. -/
theorem smul_unitSphere_eq_iff (g : unitaryGroup ι 𝕜)
    (x y : sphere (0 : EuclideanSpace 𝕜 ι) 1) :
    g • x = y ↔ (g : Matrix ι ι 𝕜) *ᵥ x.1.ofLp = y.1.ofLp := by
  rw [Subtype.ext_iff, ← (WithLp.ofLp_injective 2).eq_iff, ofLp_coe_smul_unitSphere]

/-- Unitary matrices act on the Euclidean unit sphere by isometries. -/
instance instIsIsometricSMulUnitSphere :
    IsIsometricSMul (unitaryGroup ι 𝕜) (sphere (0 : EuclideanSpace 𝕜 ι) 1) :=
  ⟨fun g ↦ isometry_smul _ (toLinearIsometryEquiv g)⟩

/-- The action of unitary matrices on the Euclidean unit sphere is jointly continuous. -/
instance instContinuousSMulUnitSphere :
    ContinuousSMul (unitaryGroup ι 𝕜) (sphere (0 : EuclideanSpace 𝕜 ι) 1) :=
  ⟨continuous_toLinearIsometryEquiv_smul_unitSphere⟩

/-- The action of `unitaryGroup ι 𝕜` on the Euclidean unit sphere commutes with multiplication by
unit scalars. -/
instance instSMulCommClassUnitSphere :
    SMulCommClass (unitaryGroup ι 𝕜) (sphere (0 : 𝕜) 1) (sphere (0 : EuclideanSpace 𝕜 ι) 1) where
  smul_comm g c x := smul_comm (toLinearIsometryEquiv g) c x

/-- Unitary matrices commute with the antipodal map on the unit sphere. -/
@[simp]
theorem smul_neg_unitSphere (g : unitaryGroup ι 𝕜) (x : sphere (0 : EuclideanSpace 𝕜 ι) 1) :
    g • (-x) = -(g • x) :=
  Subtype.ext <| by simp [Matrix.mulVec_neg]

/-- The unitary matrix group acts transitively on the Euclidean unit sphere. -/
instance instIsPretransitiveUnitSphere :
    MulAction.IsPretransitive (unitaryGroup ι 𝕜) (sphere (0 : EuclideanSpace 𝕜 ι) 1) where
  exists_smul_eq x y := by
    obtain ⟨e, he⟩ := MulAction.exists_smul_eq (EuclideanSpace 𝕜 ι ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι) x y
    obtain ⟨g, rfl⟩ := toLinearIsometryEquiv_surjective e
    exact ⟨g, he⟩

end UnitaryGroup

namespace specialUnitaryGroup

/-- The special unitary matrix group acts on the Euclidean unit sphere through its inclusion in the
unitary group. For `𝕜 = ℝ` this is the action of `Matrix.specialOrthogonalGroup ι ℝ`. -/
noncomputable instance instMulActionUnitSphere :
    MulAction (specialUnitaryGroup ι 𝕜) (sphere (0 : EuclideanSpace 𝕜 ι) 1) :=
  MulAction.compHom _ (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup)

/-- Acting by `g : specialUnitaryGroup ι 𝕜` on the unit sphere agrees with acting by `g` viewed in
`unitaryGroup ι 𝕜`. -/
theorem inclusion_smul_unitSphere (g : specialUnitaryGroup ι 𝕜)
    (x : sphere (0 : EuclideanSpace 𝕜 ι) 1) :
    Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup g • x = g • x :=
  (rfl)

/-- Coercing `g • x` from the unit sphere to `EuclideanSpace 𝕜 ι` applies matrix-vector
multiplication in coordinates. -/
@[simp]
theorem coe_smul_unitSphere (g : specialUnitaryGroup ι 𝕜) (x : sphere (0 : EuclideanSpace 𝕜 ι) 1) :
    ((g • x : sphere (0 : EuclideanSpace 𝕜 ι) 1) : EuclideanSpace 𝕜 ι) =
      WithLp.toLp 2 ((g : Matrix ι ι 𝕜) *ᵥ x.1.ofLp) := by
  rw [← inclusion_smul_unitSphere, UnitaryGroup.coe_smul_unitSphere]
  rfl

/-- Reading `g • x` in coordinate functions `ι → 𝕜` gives `(g : Matrix ι ι 𝕜) *ᵥ x.1.ofLp`. -/
@[simp]
theorem ofLp_coe_smul_unitSphere (g : specialUnitaryGroup ι 𝕜)
    (x : sphere (0 : EuclideanSpace 𝕜 ι) 1) :
    ((g • x : sphere (0 : EuclideanSpace 𝕜 ι) 1) : EuclideanSpace 𝕜 ι).ofLp =
      (g : Matrix ι ι 𝕜) *ᵥ x.1.ofLp := by
  rw [coe_smul_unitSphere, WithLp.ofLp_toLp]

/-- Two points of the unit sphere satisfy `g • x = y` if and only if `(g : Matrix ι ι 𝕜) *ᵥ x = y`
in coordinate functions. -/
theorem smul_unitSphere_eq_iff (g : specialUnitaryGroup ι 𝕜)
    (x y : sphere (0 : EuclideanSpace 𝕜 ι) 1) :
    g • x = y ↔ (g : Matrix ι ι 𝕜) *ᵥ x.1.ofLp = y.1.ofLp := by
  rw [Subtype.ext_iff, ← (WithLp.ofLp_injective 2).eq_iff, ofLp_coe_smul_unitSphere]

/-- Special unitary matrices act on the Euclidean unit sphere by isometries. -/
instance instIsIsometricSMulUnitSphere :
    IsIsometricSMul (specialUnitaryGroup ι 𝕜) (sphere (0 : EuclideanSpace 𝕜 ι) 1) :=
  ⟨fun g ↦ isometry_smul _ (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup g)⟩

/-- The action of special unitary matrices on the Euclidean unit sphere is jointly continuous. -/
instance instContinuousSMulUnitSphere :
    ContinuousSMul (specialUnitaryGroup ι 𝕜) (sphere (0 : EuclideanSpace 𝕜 ι) 1) where
  continuous_smul := UnitaryGroup.continuous_toLinearIsometryEquiv_smul_unitSphere.comp <|
    ((continuous_subtype_val.subtype_mk _).comp continuous_fst).prodMk continuous_snd

/-- The action of `specialUnitaryGroup ι 𝕜` on the Euclidean unit sphere commutes with
multiplication by unit scalars. -/
instance instSMulCommClassUnitSphere :
    SMulCommClass (specialUnitaryGroup ι 𝕜) (sphere (0 : 𝕜) 1)
      (sphere (0 : EuclideanSpace 𝕜 ι) 1) where
  smul_comm g c x :=
    smul_comm (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup g) c x

/-- Special unitary matrices commute with the antipodal map on the unit sphere. -/
@[simp]
theorem smul_neg_unitSphere (g : specialUnitaryGroup ι 𝕜) (x : sphere (0 : EuclideanSpace 𝕜 ι) 1) :
    g • (-x) = -(g • x) :=
  Subtype.ext <| by simp [Matrix.mulVec_neg]

end specialUnitaryGroup

namespace SpecialOrthogonalGroup

/-- **The special orthogonal group acts transitively on the Euclidean unit sphere in dimension at
least two.** If an orthogonal matrix moving a standard basis vector `e₀` to `y` has determinant
`-1`, precomposing with the diagonal reflection negating a second coordinate flips the determinant
to `1` while still fixing `e₀`. -/
theorem isPretransitive_unitSphere_of_two_le_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : 2 ≤ Fintype.card ι) :
    MulAction.IsPretransitive (specialOrthogonalGroup ι ℝ) (sphere (0 : EuclideanSpace ℝ ι) 1) where
  exists_smul_eq x y := by
    have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp hι
    obtain ⟨i₀, i₁, hi⟩ := exists_pair_ne ι
    let e₀ : sphere (0 : EuclideanSpace ℝ ι) 1 := ⟨EuclideanSpace.single i₀ 1, by simp⟩
    let r : orthogonalGroup ι ℝ := TauCeti.orthogonalDiagonalReflection ℝ i₁
    have hr : r • e₀ = e₀ := by
      rw [UnitaryGroup.smul_unitSphere_eq_iff]
      have he₀ : e₀.1.ofLp = Pi.single i₀ (1 : ℝ) := rfl
      ext j
      rw [TauCeti.coe_orthogonalDiagonalReflection, mulVec_diagonal, he₀]
      by_cases hj : j = i₀
      · subst hj
        simp [hi]
      · simp [hj]
    have horbit (z : sphere (0 : EuclideanSpace ℝ ι) 1) :
        ∃ g : specialOrthogonalGroup ι ℝ, g • e₀ = z := by
      obtain ⟨U, hU⟩ := MulAction.exists_smul_eq (orthogonalGroup ι ℝ) e₀ z
      rcases TauCeti.det_eq_one_or_neg_one_of_mem_orthogonalGroup U.2 with hdet | hdet
      · exact ⟨⟨U.1, mem_specialOrthogonalGroup_iff.2 ⟨U.2, hdet⟩⟩, hU⟩
      · have hdet_Ur : (U * r).1.det = 1 := by
          rw [Submonoid.coe_mul, det_mul, hdet, TauCeti.det_orthogonalDiagonalReflection]
          norm_num
        refine ⟨⟨(U * r).1, mem_specialOrthogonalGroup_iff.2 ⟨(U * r).2, hdet_Ur⟩⟩, ?_⟩
        rw [← specialUnitaryGroup.inclusion_smul_unitSphere]
        have hUr : Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup
            ⟨(U * r).1, mem_specialOrthogonalGroup_iff.2 ⟨(U * r).2, hdet_Ur⟩⟩ = U * r :=
          Subtype.ext rfl
        rw [hUr, mul_smul, hr, hU]
    obtain ⟨g₁, rfl⟩ := horbit x
    obtain ⟨g₂, rfl⟩ := horbit y
    exact ⟨g₂ * g₁⁻¹, by simp [mul_smul]⟩

/-- `SO(m + 2)` acts transitively on the unit sphere of `ℝᵐ⁺²`. -/
instance instIsPretransitiveUnitSphereFinAddTwo (m : ℕ) :
    MulAction.IsPretransitive (specialOrthogonalGroup (Fin (m + 2)) ℝ)
      (sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1) :=
  isPretransitive_unitSphere_of_two_le_card (by simp)

end SpecialOrthogonalGroup

end Matrix
