/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import TauCeti.Analysis.InnerProductSpace.RangeProjection
public import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreservingEquiv
public import TauCeti.Statistics.Semiparametric.TangentSpace

/-!
# Pullback isometry, conditional expectation operator, and score operators

For a measurable map `m : Y → X` and a measure `η` on `Y`, precomposition with `m` defines a linear
isometry `TauCeti.pullbackL2 η m hm : Lp ℝ 2 (η.map m) →L[ℝ] Lp ℝ 2 η` whose range is the subspace
`lpMeas ℝ ℝ (MeasurableSpace.comap m inferInstance) 2 η` of `σ(m)`-measurable `L²` classes. Its
Hilbert-space adjoint `TauCeti.condExpOperator η m hm : Lp ℝ 2 η →L[ℝ] Lp ℝ 2 (η.map m)` reads the
conditional expectation given `m` directly on the image space `X`:

* `TauCeti.pullbackL2_condExpOperator_eq_condExpL2`: for an arbitrary measure `η`, pulling back
  `condExpOperator η m hm b` along `m` yields Mathlib's `condExpL2 ℝ ℝ hm.comap_le b`.
* `TauCeti.pullbackL2_condExpOperator_ae_eq_of_integrable` and
  `TauCeti.pullbackL2_condExpOperator_ae_eq`: when `η.trim hm.comap_le` is σ-finite and `b` is
  integrable (automatic when `η` is a finite measure),
  `pullbackL2 η m hm (condExpOperator η m hm b)` agrees `η`-a.e. with
  `η[b | MeasurableSpace.comap m inferInstance]`.
* `TauCeti.condExpOperator_comp_pullbackL2`, `TauCeti.condExpOperator_surjective`,
  `TauCeti.norm_condExpOperator_le`, and `TauCeti.map_condExpOperator_meanZeroL2`: `condExpOperator`
  is a contractive left inverse of `pullbackL2`, hence surjective, and on a finite measure space it
  maps `meanZeroL2 η` onto `meanZeroL2 (η.map m)`.

The second half of the file treats a general score operator `A : H →L[ℝ] Lp ℝ 2 P` out of a real
Hilbert space `H`: the orthogonal complement of `tangentSpace P (Set.range A)` is `(A†).ker` (so a
score equals its efficient score relative to `Set.range A` iff `A† ℓ = 0`), and when the information
operator `A† A` is invertible, `tangentSpace P (Set.range A)` equals `A.range` with no further
closure needed and its orthogonal projection is `A (A† A)⁻¹ A†`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, §§25.2, 25.5.
* P. J. Bickel, C. A. J. Klaassen, Y. Ritov, and J. A. Wellner, *Efficient and Adaptive Estimation
  for Semiparametric Models*, Johns Hopkins University Press, 1993, §3.4, Appendix A.4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace

namespace TauCeti

section PullbackAndCondExp

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Precomposition with a measurable map `m : Y → X`, packaged as a continuous linear isometry
`Lp ℝ 2 (η.map m) →L[ℝ] Lp ℝ 2 η`. -/
def pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    Lp ℝ 2 (η.map m) →L[ℝ] Lp ℝ 2 η :=
  (Lp.compMeasurePreservingₗᵢ ℝ m (hm.measurePreserving η)).toContinuousLinearMap

/-- Unfolding identity for `pullbackL2`. -/
theorem pullbackL2_def (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    pullbackL2 η m hm =
      (Lp.compMeasurePreservingₗᵢ ℝ m (hm.measurePreserving η)).toContinuousLinearMap := (rfl)

/-- `pullbackL2 η m hm` is an isometry. -/
theorem isometry_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    Isometry (pullbackL2 η m hm) :=
  (Lp.compMeasurePreservingₗᵢ ℝ m (hm.measurePreserving η)).isometry

/-- `pullbackL2 η m hm` is injective. -/
theorem injective_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    Function.Injective (pullbackL2 η m hm) :=
  (isometry_pullbackL2 η m hm).injective

/-- `pullbackL2 η m hm` preserves `L²` norms. -/
@[simp]
theorem norm_pullbackL2_apply (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (f : Lp ℝ 2 (η.map m)) : ‖pullbackL2 η m hm f‖ = ‖f‖ :=
  (Lp.compMeasurePreservingₗᵢ ℝ m (hm.measurePreserving η)).norm_map f

/-- `pullbackL2 η m hm` preserves `L²` inner products. -/
@[simp]
theorem inner_pullbackL2_apply (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (f g : Lp ℝ 2 (η.map m)) :
    ⟪pullbackL2 η m hm f, pullbackL2 η m hm g⟫_ℝ = ⟪f, g⟫_ℝ :=
  (Lp.compMeasurePreservingₗᵢ ℝ m (hm.measurePreserving η)).inner_map_map f g

/-- Pointwise `η`-a.e. action of `pullbackL2 η m hm` by precomposition with `m`. -/
theorem coeFn_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (f : Lp ℝ 2 (η.map m)) :
    (pullbackL2 η m hm f : Y → ℝ) =ᵐ[η] fun y ↦ f (m y) :=
  Lp.coeFn_compMeasurePreserving f (hm.measurePreserving η)

/-- The range of `pullbackL2 η m hm` is the closed subspace `lpMeas` of `σ(m)`-measurable elements
of `Lp ℝ 2 η`. -/
theorem range_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    (pullbackL2 η m hm).range = lpMeas ℝ ℝ (MeasurableSpace.comap m inferInstance) 2 η := by
  ext u
  exact (Lp.mem_range_compMeasurePreservingₗᵢ_iff (𝕜 := ℝ) (hm.measurePreserving η) u).trans
    mem_lpMeas_iff_aestronglyMeasurable.symm

/-- On a finite measure space, `pullbackL2 η m hm` sends constant functions to constant
functions. -/
@[simp]
theorem pullbackL2_const (η : Measure Y) [IsFiniteMeasure η] (m : Y → X) (hm : Measurable m)
    (c : ℝ) :
    pullbackL2 η m hm (Lp.const 2 (η.map m) c) = Lp.const 2 η c := by
  rw [← indicatorConstLp_univ, pullbackL2_def, LinearIsometry.coe_toContinuousLinearMap,
    Lp.compMeasurePreservingₗᵢ_apply, Lp.indicatorConstLp_compMeasurePreserving]
  simp

/-- `pullbackL2 η m hm` preserves Bochner integrals for any measure `η`. -/
@[simp]
theorem integral_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (f : Lp ℝ 2 (η.map m)) :
    ∫ y, pullbackL2 η m hm f y ∂η = ∫ x, f x ∂η.map m :=
  (integral_congr_ae (coeFn_pullbackL2 η m hm f)).trans
    (integral_map hm.aemeasurable (Lp.aestronglyMeasurable f)).symm

/-- On a finite measure space, `pullbackL2 η m hm f` has mean zero under `η` if and only if `f` has
mean zero under `η.map m`. -/
theorem pullbackL2_mem_meanZeroL2_iff (η : Measure Y) [IsFiniteMeasure η] (m : Y → X)
    (hm : Measurable m) (f : Lp ℝ 2 (η.map m)) :
    pullbackL2 η m hm f ∈ meanZeroL2 η ↔ f ∈ meanZeroL2 (η.map m) := by
  rw [mem_meanZeroL2_iff, mem_meanZeroL2_iff, integral_pullbackL2]

/-- The conditional expectation operator `Lp ℝ 2 η →L[ℝ] Lp ℝ 2 (η.map m)` given a measurable map
`m : Y → X`, defined as the Hilbert-space adjoint of `pullbackL2 η m hm`. -/
def condExpOperator (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    Lp ℝ 2 η →L[ℝ] Lp ℝ 2 (η.map m) :=
  ContinuousLinearMap.adjoint (pullbackL2 η m hm)

/-- Unfolding identity for `condExpOperator`. -/
theorem condExpOperator_def (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    condExpOperator η m hm = ContinuousLinearMap.adjoint (pullbackL2 η m hm) := (rfl)

/-- Adjointness relation `⟪condExpOperator b, f⟫ = ⟪b, pullbackL2 f⟫`. -/
theorem inner_condExpOperator_left (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (b : Lp ℝ 2 η) (f : Lp ℝ 2 (η.map m)) :
    ⟪condExpOperator η m hm b, f⟫_ℝ = ⟪b, pullbackL2 η m hm f⟫_ℝ :=
  ContinuousLinearMap.adjoint_inner_left (pullbackL2 η m hm) f b

/-- Adjointness relation `⟪f, condExpOperator b⟫ = ⟪pullbackL2 f, b⟫`. -/
theorem inner_condExpOperator_right (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (f : Lp ℝ 2 (η.map m)) (b : Lp ℝ 2 η) :
    ⟪f, condExpOperator η m hm b⟫_ℝ = ⟪pullbackL2 η m hm f, b⟫_ℝ :=
  ContinuousLinearMap.adjoint_inner_right (pullbackL2 η m hm) f b

/-- Pulling back `condExpOperator η m hm` along `m` gives the orthogonal projection onto `lpMeas`
for the comap σ-algebra of `m`. -/
theorem pullbackL2_comp_condExpOperator_eq_starProjection (η : Measure Y) (m : Y → X)
    (hm : Measurable m) :
    haveI : Fact (MeasurableSpace.comap m inferInstance ≤ ‹MeasurableSpace Y›) := ⟨hm.comap_le⟩
    pullbackL2 η m hm ∘L condExpOperator η m hm =
      (lpMeas ℝ ℝ (MeasurableSpace.comap m inferInstance) 2 η).starProjection := by
  have : Fact (MeasurableSpace.comap m inferInstance ≤ ‹MeasurableSpace Y›) := ⟨hm.comap_le⟩
  have : (pullbackL2 η m hm).range.HasOrthogonalProjection := by
    rw [range_pullbackL2]
    infer_instance
  rw [condExpOperator_def,
    (pullbackL2 η m hm).comp_adjoint_eq_starProjection_range (isometry_pullbackL2 η m hm)]
  congr! 1
  exact range_pullbackL2 η m hm

/-- For an arbitrary measure `η`, pulling back `condExpOperator η m hm b` along `m` yields
Mathlib's `L²` conditional expectation `condExpL2 ℝ ℝ hm.comap_le b`. -/
theorem pullbackL2_condExpOperator_eq_condExpL2 (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (b : Lp ℝ 2 η) :
    pullbackL2 η m hm (condExpOperator η m hm b) = (condExpL2 ℝ ℝ hm.comap_le b : Lp ℝ 2 η) := by
  have : Fact (MeasurableSpace.comap m inferInstance ≤ ‹MeasurableSpace Y›) := ⟨hm.comap_le⟩
  have hproj := congr_fun (congr_arg DFunLike.coe
    (pullbackL2_comp_condExpOperator_eq_starProjection η m hm)) b
  simpa only [ContinuousLinearMap.comp_apply, condExpL2,
    Submodule.coe_orthogonalProjectionOnto_apply] using hproj

/-- When `η` trimmed to `σ(m)` is σ-finite and `b : Lp ℝ 2 η` is integrable, pulling back
`condExpOperator η m hm b` along `m` agrees `η`-a.e. with `η[b | σ(m)]`. -/
theorem pullbackL2_condExpOperator_ae_eq_of_integrable (η : Measure Y) (m : Y → X)
    (hm : Measurable m) [SigmaFinite (η.trim hm.comap_le)] (b : Lp ℝ 2 η)
    (hb : Integrable (b : Y → ℝ) η) :
    (pullbackL2 η m hm (condExpOperator η m hm b) : Y → ℝ) =ᵐ[η]
      η[(b : Y → ℝ) | MeasurableSpace.comap m inferInstance] := by
  rw [pullbackL2_condExpOperator_eq_condExpL2]
  have h := (Lp.memLp b).condExpL2_ae_eq_condExp' (𝕜 := ℝ) hm.comap_le hb
  rwa [Lp.toLp_coeFn] at h

/-- On a finite measure space, pulling back `condExpOperator η m hm b` along `m` agrees `η`-a.e.
with the conditional expectation `η[b | σ(m)]`. -/
theorem pullbackL2_condExpOperator_ae_eq (η : Measure Y) [IsFiniteMeasure η] (m : Y → X)
    (hm : Measurable m) (b : Lp ℝ 2 η) :
    (pullbackL2 η m hm (condExpOperator η m hm b) : Y → ℝ) =ᵐ[η]
      η[(b : Y → ℝ) | MeasurableSpace.comap m inferInstance] :=
  pullbackL2_condExpOperator_ae_eq_of_integrable η m hm b ((Lp.memLp b).integrable one_le_two)

/-- `condExpOperator η m hm` is a left inverse of the isometry `pullbackL2 η m hm`. -/
@[simp]
theorem condExpOperator_comp_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    condExpOperator η m hm ∘L pullbackL2 η m hm = ContinuousLinearMap.id ℝ (Lp ℝ 2 (η.map m)) :=
  (ContinuousLinearMap.isometry_iff_adjoint_comp_self (pullbackL2 η m hm)).mp
    (isometry_pullbackL2 η m hm)

/-- Applying `condExpOperator η m hm` to `pullbackL2 η m hm f` recovers `f`. -/
@[simp]
theorem condExpOperator_pullbackL2_apply (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (f : Lp ℝ 2 (η.map m)) :
    condExpOperator η m hm (pullbackL2 η m hm f) = f :=
  congr_fun (congr_arg DFunLike.coe (condExpOperator_comp_pullbackL2 η m hm)) f

/-- `condExpOperator η m hm` is surjective onto `Lp ℝ 2 (η.map m)`. -/
theorem condExpOperator_surjective (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    Function.Surjective (condExpOperator η m hm) :=
  fun f ↦ ⟨pullbackL2 η m hm f, condExpOperator_pullbackL2_apply η m hm f⟩

/-- `condExpOperator η m hm` is a contraction (`‖condExpOperator η m hm‖ ≤ 1`). -/
theorem norm_condExpOperator_le (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    ‖condExpOperator η m hm‖ ≤ 1 := by
  rw [condExpOperator_def, ContinuousLinearMap.adjoint.norm_map]
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ by simp

/-- On a finite measure space, `condExpOperator η m hm` fixes constant functions. -/
@[simp]
theorem condExpOperator_const (η : Measure Y) [IsFiniteMeasure η] (m : Y → X) (hm : Measurable m)
    (c : ℝ) :
    condExpOperator η m hm (Lp.const 2 η c) = Lp.const 2 (η.map m) c := by
  rw [← pullbackL2_const η m hm c, condExpOperator_pullbackL2_apply]

/-- On a finite measure space, `condExpOperator η m hm` preserves expectations. -/
@[simp]
theorem integral_condExpOperator (η : Measure Y) [IsFiniteMeasure η] (m : Y → X)
    (hm : Measurable m) (b : Lp ℝ 2 η) :
    ∫ x, condExpOperator η m hm b x ∂η.map m = ∫ y, b y ∂η := by
  rw [← L2.inner_const_one_left, inner_condExpOperator_right, pullbackL2_const,
    L2.inner_const_one_left]

/-- On a finite measure space, `condExpOperator η m hm b` has mean zero under `η.map m` if and only
if `b` has mean zero under `η`. -/
theorem condExpOperator_mem_meanZeroL2_iff (η : Measure Y) [IsFiniteMeasure η] (m : Y → X)
    (hm : Measurable m) (b : Lp ℝ 2 η) :
    condExpOperator η m hm b ∈ meanZeroL2 (η.map m) ↔ b ∈ meanZeroL2 η := by
  rw [mem_meanZeroL2_iff, mem_meanZeroL2_iff, integral_condExpOperator]

/-- On a finite measure space, `condExpOperator η m hm` maps mean-zero elements to mean-zero
elements. -/
theorem condExpOperator_mem_meanZeroL2 {η : Measure Y} [IsFiniteMeasure η] {m : Y → X}
    (hm : Measurable m) {b : Lp ℝ 2 η} (hb : b ∈ meanZeroL2 η) :
    condExpOperator η m hm b ∈ meanZeroL2 (η.map m) :=
  (condExpOperator_mem_meanZeroL2_iff η m hm b).mpr hb

/-- On a finite measure space, `condExpOperator η m hm` maps `meanZeroL2 η` onto
`meanZeroL2 (η.map m)`. -/
theorem map_condExpOperator_meanZeroL2 (η : Measure Y) [IsFiniteMeasure η] (m : Y → X)
    (hm : Measurable m) :
    (meanZeroL2 η).map (condExpOperator η m hm : Lp ℝ 2 η →ₗ[ℝ] Lp ℝ 2 (η.map m)) =
      meanZeroL2 (η.map m) := by
  refine le_antisymm ?_ fun f hf ↦ ?_
  · rintro _ ⟨b, hb, rfl⟩
    exact condExpOperator_mem_meanZeroL2 hm hb
  · exact ⟨pullbackL2 η m hm f, (pullbackL2_mem_meanZeroL2_iff η m hm f).mpr hf,
      condExpOperator_pullbackL2_apply η m hm f⟩

end PullbackAndCondExp

/-! ### Score operators and projection onto their range -/

section ScoreOperator

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- For any score operator `A : H →L[ℝ] Lp ℝ 2 P` out of a real Hilbert space `H`, the orthogonal
complement of `tangentSpace P (Set.range A)` is the kernel of `A†` (even when `A` does not have
closed range). -/
theorem orthogonal_toSubmodule_tangentSpace_range (P : Measure X) (A : H →L[ℝ] Lp ℝ 2 P) :
    (tangentSpace P (range A)).toSubmoduleᗮ = (ContinuousLinearMap.adjoint A).ker := by
  rw [tangentSpace_range, ClosedSubmodule.orthogonal_closure]
  exact A.orthogonal_range

/-- Relative to the range of a nuisance score operator `A : H →L[ℝ] Lp ℝ 2 P`, a score `ℓ` equals
its efficient score if and only if `A† ℓ = 0`. -/
theorem efficientScore_range_eq_self_iff {P : Measure X} (A : H →L[ℝ] Lp ℝ 2 P)
    (ℓ : Lp ℝ 2 P) :
    efficientScore P (range A) ℓ = ℓ ↔ ContinuousLinearMap.adjoint A ℓ = 0 := by
  rw [efficientScore_eq_starProjection_orthogonal, Submodule.starProjection_eq_self_iff,
    orthogonal_toSubmodule_tangentSpace_range, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]

/-- For a score operator `A : H →L[ℝ] Lp ℝ 2 P` out of a real Hilbert space `H` whose information
operator `A† A` is invertible, `tangentSpace P (Set.range A)` has underlying submodule `A.range`. -/
theorem toSubmodule_tangentSpace_range_of_isUnit_adjoint_comp {P : Measure X}
    (A : H →L[ℝ] Lp ℝ 2 P) (hA : IsUnit (ContinuousLinearMap.adjoint A ∘L A)) :
    (tangentSpace P (range A)).toSubmodule = A.range :=
  toSubmodule_tangentSpace_range_of_isClosed A (A.isClosed_range_of_isUnit_adjoint_comp hA)

/-- For a score operator `A : H →L[ℝ] Lp ℝ 2 P` out of a real Hilbert space `H` whose information
operator `A† A` is invertible, the orthogonal projection onto `tangentSpace P (Set.range A)` is
`A (A† A)⁻¹ A†`. -/
theorem starProjection_closure_range_eq {P : Measure X}
    (A : H →L[ℝ] Lp ℝ 2 P) (hA : IsUnit (ContinuousLinearMap.adjoint A ∘L A)) :
    (tangentSpace P (range A)).toSubmodule.starProjection =
      A ∘L Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) ∘L ContinuousLinearMap.adjoint A := by
  have : A.range.HasOrthogonalProjection :=
    Submodule.hasOrthogonalProjection_iff_isClosed.mpr (A.isClosed_range_of_isUnit_adjoint_comp hA)
  rw [← A.starProjection_range_eq hA]
  congr! 1
  exact toSubmodule_tangentSpace_range_of_isUnit_adjoint_comp A hA

end ScoreOperator

end TauCeti
