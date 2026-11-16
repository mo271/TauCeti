/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.Probability.Moments.Variance
public import TauCeti.Analysis.InnerProductSpace.Gram.Projection
public import TauCeti.Analysis.InnerProductSpace.Projection.Completeness
public import TauCeti.Probability.Moments.Variance

/-!
# Hilbert geometry of scores, tangent spaces, and efficient information

For a measure `P` on a measurable space `X`, scores and influence functions in semiparametric
statistics live in the real Hilbert space `Lp ℝ 2 P` with inner product
`⟪f, g⟫_ℝ = ∫ x, f x * g x ∂P`. This file develops the Hilbert-space geometry of score spaces:

* `TauCeti.meanZeroL2 P`: for a finite measure `P`, the closed subspace `L²₀(P)` of mean-zero
  square-integrable classes, defined as the orthogonal complement of the constant functions
  `Submodule.span ℝ {Lp.const 2 P 1}`. On a probability space, orthogonal projection onto
  `meanZeroL2 P` subtracts the expectation and has squared norm equal to the variance; bounded
  mean-zero classes (and, on a normal Borel space with a weakly regular measure, bounded continuous
  mean-zero classes) are dense in `meanZeroL2 P`.
* `TauCeti.tangentSpace P T`: the closed linear span of a tangent set `T : Set (Lp ℝ 2 P)`,
  packaged as a `ClosedSubmodule ℝ (Lp ℝ 2 P)`. The tangent space of a union `T ∪ T'` is the
  supremum `tangentSpace P T ⊔ tangentSpace P T'` in `ClosedSubmodule`, i.e. the topological closure
  of their algebraic sum; when the two tangent spaces are orthogonal, it equals their algebraic sum
  and the orthogonal projections add.
* `TauCeti.efficientScore P N ℓ`: the residual `ℓ - Π_N ℓ` of a score `ℓ` after orthogonal
  projection onto the nuisance tangent space `tangentSpace P N`, together with its continuous
  linear packaging `TauCeti.efficientScoreCLM P N`.
* `TauCeti.informationMatrix P ℓ` and `TauCeti.efficientInformationMatrix P N ℓ`: the Gram matrices
  of an indexed family of scores and of its efficient scores, together with the matrix
  information-loss inequality (`informationMatrix P ℓ - efficientInformationMatrix P N ℓ` is
  positive semidefinite and vanishes if and only if every `ℓ i` is orthogonal to `N`, the algebraic
  adaptation criterion) and monotonicity of efficient information under enlarging `N`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, §§25.2, 25.4.
* P. J. Bickel, C. A. J. Klaassen, Y. Ritov, and J. A. Wellner, *Efficient and Adaptive Estimation
  for Semiparametric Models*, Johns Hopkins University Press, 1993, §§2.1–2.4, 3.2–3.4.

Nuisance tangent spaces and efficient scores in `Lp ℝ 2` also appear in
`CKSD/Asymptotics/Statistics.lean` of `lean-CKSD` (Apache-2.0). The definitions and proofs here are
built directly on Mathlib's `ClosedSubmodule`, `Submodule.starProjection`, and `Matrix.gram`.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction ComplexOrder ENNReal InnerProductSpace

namespace TauCeti

variable {X : Type*} [MeasurableSpace X]

/-! ### Mean-zero `L²` and constants -/

/-- The closed subspace `L²₀(P)` of mean-zero elements of `Lp ℝ 2 P` for a finite measure `P`,
defined as the orthogonal complement of the span of the constant function `1`. -/
def meanZeroL2 (P : Measure X) [IsFiniteMeasure P] : Submodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ {Lp.const 2 P (1 : ℝ)})ᗮ

/-- Unfolding identity for `meanZeroL2`. -/
theorem meanZeroL2_def (P : Measure X) [IsFiniteMeasure P] :
    meanZeroL2 P = (Submodule.span ℝ {Lp.const 2 P (1 : ℝ)})ᗮ := (rfl)

/-- `meanZeroL2 P` is a closed subspace of `Lp ℝ 2 P`. -/
theorem isClosed_meanZeroL2 (P : Measure X) [IsFiniteMeasure P] :
    IsClosed (meanZeroL2 P : Set (Lp ℝ 2 P)) :=
  Submodule.isClosed_orthogonal _

/-- `meanZeroL2 P` admits an orthogonal projection in the Hilbert space `Lp ℝ 2 P`. -/
instance (P : Measure X) [IsFiniteMeasure P] : (meanZeroL2 P).HasOrthogonalProjection :=
  Submodule.hasOrthogonalProjection_iff_isClosed.mpr (isClosed_meanZeroL2 P)

/-- `Lp ℝ 2 P` splits as the direct sum of the constant functions and `meanZeroL2 P`. -/
theorem isCompl_span_const_meanZeroL2 (P : Measure X) [IsFiniteMeasure P] :
    IsCompl (Submodule.span ℝ {Lp.const 2 P (1 : ℝ)}) (meanZeroL2 P) := by
  have : FiniteDimensional ℝ (Submodule.span ℝ {Lp.const 2 P (1 : ℝ)}) :=
    FiniteDimensional.span_of_finite ℝ (finite_singleton _)
  exact Submodule.isCompl_orthogonal _

/-- An element of `Lp ℝ 2 P` belongs to `meanZeroL2 P` if and only if its integral is `0`. -/
@[simp]
theorem mem_meanZeroL2_iff {P : Measure X} [IsFiniteMeasure P] {f : Lp ℝ 2 P} :
    f ∈ meanZeroL2 P ↔ ∫ x, f x ∂P = 0 := by
  rw [meanZeroL2_def, Submodule.mem_orthogonal_singleton_iff_inner_right, L2.inner_const_one_left]

/-- For `g : X → ℝ` in `ℒ²(P)`, `hg.toLp g` lies in `meanZeroL2 P` if and only if `∫ g ∂P = 0`. -/
theorem toLp_mem_meanZeroL2_iff {P : Measure X} [IsFiniteMeasure P] {g : X → ℝ}
    (hg : MemLp g 2 P) : hg.toLp g ∈ meanZeroL2 P ↔ ∫ x, g x ∂P = 0 := by
  rw [mem_meanZeroL2_iff, integral_congr_ae hg.coeFn_toLp]

/-- On a nonzero finite measure space, a constant belongs to `meanZeroL2 P` if and only if it is
zero. -/
theorem const_mem_meanZeroL2_iff (P : Measure X) [IsFiniteMeasure P] [NeZero P] (c : ℝ) :
    Lp.const 2 P c ∈ meanZeroL2 P ↔ c = 0 := by
  rw [mem_meanZeroL2_iff, integral_congr_ae (Lp.coeFn_const 2 P c)]
  simp only [Function.const_apply, integral_const, smul_eq_mul, mul_eq_zero]
  have hP : P.real univ ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨Measure.measure_univ_eq_zero.not.mpr (NeZero.ne P),
      measure_ne_top P univ⟩
  exact or_iff_right hP

/-- On the zero measure, `meanZeroL2 0` is the whole trivial space `⊤`. -/
@[simp]
theorem meanZeroL2_zero : meanZeroL2 (0 : Measure X) = ⊤ := by
  ext f
  simp

/-- For a Dirac measure `Measure.dirac x₀`, the only mean-zero element of `L²` is `0`. -/
@[simp]
theorem meanZeroL2_dirac (x₀ : X) : meanZeroL2 (Measure.dirac x₀) = ⊥ := by
  ext f
  rw [mem_meanZeroL2_iff, Submodule.mem_bot]
  refine ⟨fun hf ↦ ?_, fun hf ↦ by simp [hf]⟩
  rw [integral_dirac' _ x₀ (Lp.stronglyMeasurable f)] at hf
  have hnorm : ‖f‖ ^ 2 = 0 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq,
      integral_dirac' (fun x ↦ ‖(f : X → ℝ) x‖ ^ 2) x₀
        (((Lp.stronglyMeasurable f).norm).pow 2),
      hf, norm_zero, zero_pow two_ne_zero]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)

/-- On a finite measure space, the orthogonal projection onto `meanZeroL2 P` subtracts the
normalized expectation `(∫ f ∂P) / P.real Set.univ` (which is `0` when `P = 0`). -/
theorem starProjection_meanZeroL2_of_isFiniteMeasure (P : Measure X) [IsFiniteMeasure P]
    (f : Lp ℝ 2 P) :
    (meanZeroL2 P).starProjection f = f - Lp.const 2 P ((∫ x, f x ∂P) / P.real univ) := by
  set c := (∫ x, f x ∂P) / P.real univ
  refine Submodule.eq_starProjection_of_mem_orthogonal (K := meanZeroL2 P) ?_ ?_
  · rw [mem_meanZeroL2_iff, ← L2.inner_const_one_left, inner_sub_right, L2.inner_const_one_left,
      L2.inner_const_one_left, integral_congr_ae (Lp.coeFn_const 2 P c)]
    simp only [Function.const_apply, integral_const, smul_eq_mul]
    by_cases hP : P.real univ = 0
    · have hP0 : P = 0 := by
        rw [← Measure.measure_univ_eq_zero]
        exact ((ENNReal.toReal_eq_zero_iff _).mp hP).resolve_right (measure_ne_top P univ)
      simp [hP0]
    · rw [mul_div_cancel₀ _ hP, sub_self]
  · rw [sub_sub_cancel, meanZeroL2_def]
    have hc : Lp.const 2 P c = c • Lp.const 2 P (1 : ℝ) := by
      simpa only [Lp.constₗ_apply, smul_eq_mul, mul_one] using
        (Lp.constₗ 2 P ℝ).map_smul c (1 : ℝ)
    rw [hc]
    exact Submodule.le_orthogonal_orthogonal _
      (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _))

/-- On a probability space, orthogonal projection onto `meanZeroL2 P` subtracts `∫ f ∂P`. -/
theorem starProjection_meanZeroL2 (P : Measure X) [IsProbabilityMeasure P] (f : Lp ℝ 2 P) :
    (meanZeroL2 P).starProjection f = f - Lp.const 2 P (∫ x, f x ∂P) := by
  rw [starProjection_meanZeroL2_of_isFiniteMeasure, probReal_univ, div_one]

/-- Pointwise a.e. form of `starProjection_meanZeroL2`. -/
theorem coeFn_starProjection_meanZeroL2 (P : Measure X) [IsProbabilityMeasure P] (f : Lp ℝ 2 P) :
    ((meanZeroL2 P).starProjection f : X → ℝ) =ᵐ[P] fun x ↦ f x - ∫ y, f y ∂P := by
  rw [starProjection_meanZeroL2]
  exact (Lp.coeFn_sub _ _).trans (EventuallyEq.rfl.sub (Lp.coeFn_const 2 P _))

/-- On a probability space, the squared `L²` norm of the projection of `f` onto `meanZeroL2 P` is
the variance of `f`. -/
theorem norm_starProjection_meanZeroL2_sq (P : Measure X) [IsProbabilityMeasure P]
    (f : Lp ℝ 2 P) : ‖(meanZeroL2 P).starProjection f‖ ^ 2 = variance f P := by
  rw [starProjection_meanZeroL2, Lp.norm_sub_const_integral_sq]

/-- On a finite measure space, essentially bounded mean-zero classes are dense in `meanZeroL2 P`. -/
theorem meanZeroL2_subset_closure_bounded (P : Measure X) [IsFiniteMeasure P] :
    (meanZeroL2 P : Set (Lp ℝ 2 P)) ⊆
      closure {u | u ∈ meanZeroL2 P ∧ ∃ C, ∀ᵐ x ∂P, |u x| ≤ C} := by
  intro u hu
  set P₀ := (meanZeroL2 P).starProjection with hP₀
  have hd : Dense (Lp.simpleFunc ℝ 2 P : Set (Lp ℝ 2 P)) :=
    Lp.simpleFunc.dense (by simp : (2 : ℝ≥0∞) ≠ ∞)
  have hu' : P₀ u ∈ closure (P₀ '' (Lp.simpleFunc ℝ 2 P : Set (Lp ℝ 2 P))) :=
    image_closure_subset_closure_image P₀.continuous ⟨u, hd u, rfl⟩
  rw [hP₀, (meanZeroL2 P).starProjection_eq_self_iff.mpr hu] at hu'
  refine closure_mono ?_ hu'
  rintro _ ⟨v, hv, rfl⟩
  let s : Lp.simpleFunc ℝ 2 P := ⟨v, hv⟩
  let g : SimpleFunc X ℝ := Lp.simpleFunc.toSimpleFunc s
  obtain ⟨M, hM⟩ := (g.finite_range.image abs).bddAbove
  set c := (∫ x, v x ∂P) / P.real univ
  refine ⟨(meanZeroL2 P).starProjection_apply_mem v, M + |c|, ?_⟩
  have hsub : ((meanZeroL2 P).starProjection v : X → ℝ) =ᵐ[P] fun x ↦ g x - c := by
    rw [starProjection_meanZeroL2_of_isFiniteMeasure]
    exact (Lp.coeFn_sub _ _).trans
      ((Lp.simpleFunc.toSimpleFunc_eq_toFun s).symm.sub (Lp.coeFn_const 2 P c))
  filter_upwards [hsub] with x hx
  rw [hx]
  exact (abs_sub _ _).trans (add_le_add (hM ⟨g x, mem_range_self x, rfl⟩) le_rfl)

/-- On a normal Borel space with a weakly regular finite measure `P`, mean-zero classes represented
by bounded continuous functions are dense in `meanZeroL2 P`. -/
theorem meanZeroL2_subset_closure_boundedContinuous (P : Measure X) [IsFiniteMeasure P]
    [TopologicalSpace X] [NormalSpace X] [BorelSpace X] [P.WeaklyRegular] :
    (meanZeroL2 P : Set (Lp ℝ 2 P)) ⊆
      closure {u | u ∈ meanZeroL2 P ∧ ∃ g : X →ᵇ ℝ, (u : X → ℝ) =ᵐ[P] g} := by
  intro u hu
  set P₀ := (meanZeroL2 P).starProjection with hP₀
  set ι := (BoundedContinuousFunction.toLp 2 P ℝ : (X →ᵇ ℝ) →L[ℝ] Lp ℝ 2 P)
  have hd : Dense (range ι) :=
    BoundedContinuousFunction.toLp_denseRange ℝ P ℝ (by simp : (2 : ℝ≥0∞) ≠ ∞)
  have hu' : P₀ u ∈ closure (P₀ '' range ι) :=
    image_closure_subset_closure_image P₀.continuous ⟨u, hd u, rfl⟩
  rw [hP₀, (meanZeroL2 P).starProjection_eq_self_iff.mpr hu] at hu'
  refine closure_mono ?_ hu'
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  set c := (∫ x, ι g x ∂P) / P.real univ
  refine ⟨(meanZeroL2 P).starProjection_apply_mem (ι g), g - BoundedContinuousFunction.const X c,
    ?_⟩
  rw [starProjection_meanZeroL2_of_isFiniteMeasure]
  filter_upwards [Lp.coeFn_sub (ι g) (Lp.const 2 P c),
    BoundedContinuousFunction.coeFn_toLp 2 P ℝ g, Lp.coeFn_const 2 P c] with x hsub hg hc
  rw [hsub, Pi.sub_apply, hg, hc]
  simp

/-! ### Tangent spaces -/

/-- The tangent space generated by a tangent set `T ⊆ Lp ℝ 2 P`: the topological closure of its
real linear span, packaged as a `ClosedSubmodule ℝ (Lp ℝ 2 P)`. -/
def tangentSpace (P : Measure X) (T : Set (Lp ℝ 2 P)) : ClosedSubmodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ T).closure

/-- Unfolding identity for `tangentSpace`. -/
theorem tangentSpace_def (P : Measure X) (T : Set (Lp ℝ 2 P)) :
    tangentSpace P T = (Submodule.span ℝ T).closure := (rfl)

/-- The underlying submodule of `tangentSpace P T` is the topological closure of `span ℝ T`. -/
theorem toSubmodule_tangentSpace (P : Measure X) (T : Set (Lp ℝ 2 P)) :
    (tangentSpace P T).toSubmodule = (Submodule.span ℝ T).topologicalClosure := (rfl)

/-- Every generator in `T` belongs to `tangentSpace P T`. -/
theorem subset_tangentSpace (P : Measure X) (T : Set (Lp ℝ 2 P)) :
    T ⊆ (tangentSpace P T : Set (Lp ℝ 2 P)) :=
  (Submodule.subset_span (R := ℝ)).trans (Submodule.span ℝ T).le_topologicalClosure

/-- Membership of a generator in `tangentSpace P T`. -/
theorem mem_tangentSpace_of_mem {P : Measure X} {T : Set (Lp ℝ 2 P)} {g : Lp ℝ 2 P} (hg : g ∈ T) :
    g ∈ tangentSpace P T :=
  subset_tangentSpace P T hg

/-- The algebraic span of `T` is contained in `tangentSpace P T`. -/
theorem span_le_tangentSpace (P : Measure X) (T : Set (Lp ℝ 2 P)) :
    Submodule.span ℝ T ≤ (tangentSpace P T).toSubmodule :=
  (Submodule.span ℝ T).le_topologicalClosure

/-- Universal property of `tangentSpace`: it is the smallest closed submodule containing `T`. -/
@[simp]
theorem tangentSpace_le_iff {P : Measure X} {T : Set (Lp ℝ 2 P)}
    {K : ClosedSubmodule ℝ (Lp ℝ 2 P)} :
    tangentSpace P T ≤ K ↔ T ⊆ (K : Set (Lp ℝ 2 P)) := by
  rw [tangentSpace_def, Submodule.closure_le, Submodule.span_le]
  rfl

/-- `tangentSpace P T` is monotone in the generating set `T`. -/
theorem tangentSpace_mono {P : Measure X} {T T' : Set (Lp ℝ 2 P)} (h : T ⊆ T') :
    tangentSpace P T ≤ tangentSpace P T' :=
  tangentSpace_le_iff.mpr (h.trans (subset_tangentSpace P T'))

/-- The tangent space of the empty set is `⊥`. -/
@[simp]
theorem tangentSpace_empty (P : Measure X) : tangentSpace P ∅ = ⊥ :=
  le_bot_iff.mp (tangentSpace_le_iff.mpr (empty_subset _))

/-- The tangent space of `{0}` is `⊥`. -/
@[simp]
theorem tangentSpace_singleton_zero (P : Measure X) : tangentSpace P {0} = ⊥ :=
  le_bot_iff.mp (tangentSpace_le_iff.mpr (singleton_subset_iff.mpr (zero_mem _)))

/-- Taking `tangentSpace` of the carrier of a closed submodule recovers that closed submodule. -/
@[simp]
theorem tangentSpace_coe_closedSubmodule (P : Measure X) (K : ClosedSubmodule ℝ (Lp ℝ 2 P)) :
    tangentSpace P (K : Set (Lp ℝ 2 P)) = K :=
  le_antisymm (tangentSpace_le_iff.mpr Subset.rfl) (subset_tangentSpace P _)

/-- If `U` is a closed submodule of `Lp ℝ 2 P`, the tangent space of `U` has underlying submodule
`U`. -/
theorem toSubmodule_tangentSpace_of_isClosed {P : Measure X} (U : Submodule ℝ (Lp ℝ 2 P))
    (hU : IsClosed (U : Set (Lp ℝ 2 P))) :
    (tangentSpace P (U : Set (Lp ℝ 2 P))).toSubmodule = U :=
  congr_arg ClosedSubmodule.toSubmodule (tangentSpace_coe_closedSubmodule P ⟨U, hU⟩)

/-- The tangent space generated by the range of a linear map `A` into `Lp ℝ 2 P` is the closure of
`LinearMap.range (A : M →ₗ[ℝ] Lp ℝ 2 P)`. -/
@[simp]
theorem tangentSpace_range {M F : Type*} [AddCommMonoid M] [Module ℝ M] (P : Measure X)
    [FunLike F M (Lp ℝ 2 P)] [LinearMapClass F ℝ M (Lp ℝ 2 P)] (A : F) :
    tangentSpace P (range A) = (LinearMap.range (A : M →ₗ[ℝ] Lp ℝ 2 P)).closure := by
  rw [tangentSpace_def, ← LinearMap.coe_ofClass (f := A), ← LinearMap.coe_range, Submodule.span_eq]

/-- If a linear map `A` into `Lp ℝ 2 P` has closed range, the tangent space of its range has
underlying submodule `LinearMap.range (A : M →ₗ[ℝ] Lp ℝ 2 P)` with no further closure needed. -/
theorem toSubmodule_tangentSpace_range_of_isClosed {M F : Type*} [AddCommMonoid M] [Module ℝ M]
    {P : Measure X} [FunLike F M (Lp ℝ 2 P)] [LinearMapClass F ℝ M (Lp ℝ 2 P)] (A : F)
    (hA : IsClosed (range A)) :
    (tangentSpace P (range A)).toSubmodule = LinearMap.range (A : M →ₗ[ℝ] Lp ℝ 2 P) :=
  toSubmodule_tangentSpace_of_isClosed (LinearMap.range (A : M →ₗ[ℝ] Lp ℝ 2 P)) hA

/-- If every generator in `T` has mean zero, then `tangentSpace P T ≤ meanZeroL2 P`. -/
theorem tangentSpace_le_meanZeroL2 {P : Measure X} [IsFiniteMeasure P] {T : Set (Lp ℝ 2 P)}
    (hT : T ⊆ (meanZeroL2 P : Set (Lp ℝ 2 P))) :
    (tangentSpace P T).toSubmodule ≤ meanZeroL2 P :=
  tangentSpace_le_iff (K := ⟨meanZeroL2 P, isClosed_meanZeroL2 P⟩) |>.mpr hT

/-- The orthogonal complement of `tangentSpace P T` coincides with `(span ℝ T)ᗮ`. -/
@[simp]
theorem orthogonal_toSubmodule_tangentSpace (P : Measure X) (T : Set (Lp ℝ 2 P)) :
    (tangentSpace P T).toSubmoduleᗮ = (Submodule.span ℝ T)ᗮ :=
  ClosedSubmodule.orthogonal_closure (Submodule.span ℝ T)

/-- An element `ℓ` is orthogonal to `tangentSpace P T` if and only if it is orthogonal to every
generator `g ∈ T`. -/
theorem mem_orthogonal_tangentSpace_iff {P : Measure X} {T : Set (Lp ℝ 2 P)} {ℓ : Lp ℝ 2 P} :
    ℓ ∈ (tangentSpace P T)ᗮ ↔ ∀ g ∈ T, ⟪g, ℓ⟫_ℝ = 0 := by
  rw [← ClosedSubmodule.mem_orthogonal_toSubmodule_iff, orthogonal_toSubmodule_tangentSpace]
  refine ⟨fun h g hg ↦ (Submodule.mem_orthogonal _ _).mp h g (Submodule.subset_span hg),
    fun h ↦ (Submodule.mem_orthogonal _ _).mpr fun u hu ↦ ?_⟩
  have hle : Submodule.span ℝ T ≤ (Submodule.span ℝ {ℓ})ᗮ :=
    Submodule.span_le.mpr fun g hg ↦
      Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (h g hg)
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hle hu)

/-- In the lattice of `ClosedSubmodule`s, the tangent space of `T ∪ T'` is the supremum of the two
tangent spaces. -/
theorem tangentSpace_union (P : Measure X) (T T' : Set (Lp ℝ 2 P)) :
    tangentSpace P (T ∪ T') = tangentSpace P T ⊔ tangentSpace P T' := by
  refine le_antisymm ?_ (sup_le (tangentSpace_mono subset_union_left)
    (tangentSpace_mono subset_union_right))
  rw [tangentSpace_le_iff, union_subset_iff]
  exact ⟨(subset_tangentSpace P T).trans (le_sup_left : tangentSpace P T ≤ _),
    (subset_tangentSpace P T').trans (le_sup_right : tangentSpace P T' ≤ _)⟩

/-- The underlying submodule of `tangentSpace P (T ∪ T')` is the topological closure of the sum of
the two tangent spaces. -/
theorem toSubmodule_tangentSpace_union (P : Measure X) (T T' : Set (Lp ℝ 2 P)) :
    (tangentSpace P (T ∪ T')).toSubmodule =
      ((tangentSpace P T).toSubmodule ⊔ (tangentSpace P T').toSubmodule).topologicalClosure := by
  rw [tangentSpace_union, ClosedSubmodule.toSubmodule_sup]
  rfl

/-- When `tangentSpace P T` and `tangentSpace P T'` are orthogonal, the tangent space of `T ∪ T'`
is their algebraic sum (already closed without taking a further closure). -/
theorem toSubmodule_tangentSpace_union_of_isOrtho {P : Measure X} {T T' : Set (Lp ℝ 2 P)}
    (h : (tangentSpace P T).toSubmodule ⟂ (tangentSpace P T').toSubmodule) :
    (tangentSpace P (T ∪ T')).toSubmodule =
      (tangentSpace P T).toSubmodule ⊔ (tangentSpace P T').toSubmodule := by
  rw [toSubmodule_tangentSpace_union]
  exact h.isClosed_sup.submodule_topologicalClosure_eq

/-- When `tangentSpace P T` and `tangentSpace P T'` are orthogonal, the orthogonal projection onto
`tangentSpace P (T ∪ T')` is the sum of the orthogonal projections onto the two factors. -/
theorem starProjection_tangentSpace_union_of_isOrtho {P : Measure X} {T T' : Set (Lp ℝ 2 P)}
    (h : (tangentSpace P T).toSubmodule ⟂ (tangentSpace P T').toSubmodule) :
    (tangentSpace P (T ∪ T')).toSubmodule.starProjection =
      (tangentSpace P T).toSubmodule.starProjection +
        (tangentSpace P T').toSubmodule.starProjection := by
  have :
      ((tangentSpace P T).toSubmodule ⊔ (tangentSpace P T').toSubmodule).HasOrthogonalProjection :=
    h.hasOrthogonalProjection_sup
  rw [← h.starProjection_sup]
  congr! 1
  exact toSubmodule_tangentSpace_union_of_isOrtho h

/-! ### Efficient scores and information matrices -/

/-- The efficient score of `ℓ` relative to a nuisance tangent set `N`: the residual of `ℓ` after
orthogonal projection onto the nuisance tangent space `tangentSpace P N`. -/
def efficientScore (P : Measure X) (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) : Lp ℝ 2 P :=
  ℓ - (tangentSpace P N).toSubmodule.starProjection ℓ

/-- Unfolding identity for `efficientScore`. -/
theorem efficientScore_def (P : Measure X) (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N ℓ = ℓ - (tangentSpace P N).toSubmodule.starProjection ℓ := (rfl)

/-- `efficientScore P N ℓ` is the orthogonal projection of `ℓ` onto `(tangentSpace P N)ᗮ`. -/
theorem efficientScore_eq_starProjection_orthogonal (P : Measure X) (N : Set (Lp ℝ 2 P))
    (ℓ : Lp ℝ 2 P) :
    efficientScore P N ℓ = (tangentSpace P N).toSubmoduleᗮ.starProjection ℓ := by
  rw [efficientScore_def, Submodule.starProjection_orthogonal_val]

/-- Continuous linear map sending a score `ℓ` to its efficient score `efficientScore P N ℓ`. -/
def efficientScoreCLM (P : Measure X) (N : Set (Lp ℝ 2 P)) : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P :=
  ContinuousLinearMap.id ℝ (Lp ℝ 2 P) - (tangentSpace P N).toSubmodule.starProjection

/-- Applying `efficientScoreCLM P N` evaluates `efficientScore P N`. -/
@[simp]
theorem efficientScoreCLM_apply (P : Measure X) (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScoreCLM P N ℓ = efficientScore P N ℓ := (rfl)

/-- The efficient score of `0` is `0`. -/
@[simp]
theorem efficientScore_zero (P : Measure X) (N : Set (Lp ℝ 2 P)) :
    efficientScore P N 0 = 0 :=
  map_zero (efficientScoreCLM P N)

/-- `efficientScore P N` preserves addition. -/
@[simp]
theorem efficientScore_add (P : Measure X) (N : Set (Lp ℝ 2 P)) (ℓ₁ ℓ₂ : Lp ℝ 2 P) :
    efficientScore P N (ℓ₁ + ℓ₂) = efficientScore P N ℓ₁ + efficientScore P N ℓ₂ :=
  map_add (efficientScoreCLM P N) ℓ₁ ℓ₂

/-- `efficientScore P N` preserves subtraction. -/
@[simp]
theorem efficientScore_sub (P : Measure X) (N : Set (Lp ℝ 2 P)) (ℓ₁ ℓ₂ : Lp ℝ 2 P) :
    efficientScore P N (ℓ₁ - ℓ₂) = efficientScore P N ℓ₁ - efficientScore P N ℓ₂ :=
  map_sub (efficientScoreCLM P N) ℓ₁ ℓ₂

/-- `efficientScore P N` commutes with negation. -/
@[simp]
theorem efficientScore_neg (P : Measure X) (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N (-ℓ) = -efficientScore P N ℓ :=
  map_neg (efficientScoreCLM P N) ℓ

/-- `efficientScore P N` commutes with scalar multiplication. -/
@[simp]
theorem efficientScore_smul (P : Measure X) (N : Set (Lp ℝ 2 P)) (c : ℝ) (ℓ : Lp ℝ 2 P) :
    efficientScore P N (c • ℓ) = c • efficientScore P N ℓ :=
  map_smul (efficientScoreCLM P N) c ℓ

/-- The efficient score lies in the orthogonal complement of `tangentSpace P N`. -/
theorem efficientScore_mem_orthogonal (P : Measure X) (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N ℓ ∈ (tangentSpace P N)ᗮ := by
  rw [← ClosedSubmodule.mem_orthogonal_toSubmodule_iff, efficientScore_def]
  exact Submodule.sub_starProjection_mem_orthogonal ℓ

/-- The efficient score is orthogonal to every nuisance score `g ∈ tangentSpace P N`. -/
theorem inner_efficientScore_of_mem_tangentSpace {P : Measure X} {N : Set (Lp ℝ 2 P)}
    {g : Lp ℝ 2 P} (hg : g ∈ tangentSpace P N) (ℓ : Lp ℝ 2 P) :
    ⟪g, efficientScore P N ℓ⟫_ℝ = 0 :=
  (ClosedSubmodule.mem_orthogonal _ _).mp (efficientScore_mem_orthogonal P N ℓ) g hg

/-- The efficient score is orthogonal to every nuisance generator `g ∈ N`. -/
theorem inner_efficientScore_of_mem {P : Measure X} {N : Set (Lp ℝ 2 P)} {g : Lp ℝ 2 P}
    (hg : g ∈ N) (ℓ : Lp ℝ 2 P) :
    ⟪g, efficientScore P N ℓ⟫_ℝ = 0 :=
  inner_efficientScore_of_mem_tangentSpace (mem_tangentSpace_of_mem hg) ℓ

/-- `efficientScore P N ℓ` equals `ℓ` if and only if `ℓ` is orthogonal to every `g ∈ N`. -/
theorem efficientScore_eq_self_iff {P : Measure X} {N : Set (Lp ℝ 2 P)} {ℓ : Lp ℝ 2 P} :
    efficientScore P N ℓ = ℓ ↔ ∀ g ∈ N, ⟪g, ℓ⟫_ℝ = 0 := by
  rw [efficientScore_eq_starProjection_orthogonal, Submodule.starProjection_eq_self_iff,
    ClosedSubmodule.mem_orthogonal_toSubmodule_iff, mem_orthogonal_tangentSpace_iff]

/-- `efficientScore P N ℓ` vanishes if and only if `ℓ` lies in the nuisance tangent space. -/
@[simp]
theorem efficientScore_eq_zero_iff {P : Measure X} {N : Set (Lp ℝ 2 P)} {ℓ : Lp ℝ 2 P} :
    efficientScore P N ℓ = 0 ↔ ℓ ∈ tangentSpace P N := by
  rw [efficientScore_def, sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff]
  rfl

/-- Taking the efficient score is idempotent. -/
@[simp]
theorem efficientScore_efficientScore (P : Measure X) (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N (efficientScore P N ℓ) = efficientScore P N ℓ :=
  efficientScore_eq_self_iff.mpr fun _ hg ↦ inner_efficientScore_of_mem hg ℓ

/-- Relative to an empty nuisance set, the efficient score is the score itself. -/
@[simp]
theorem efficientScore_empty (P : Measure X) (ℓ : Lp ℝ 2 P) :
    efficientScore P ∅ ℓ = ℓ := by
  simp [efficientScore_def]

/-- If `ℓ` and every nuisance score in `N` have mean zero, so does `efficientScore P N ℓ`. -/
theorem efficientScore_mem_meanZeroL2 {P : Measure X} [IsFiniteMeasure P] {N : Set (Lp ℝ 2 P)}
    {ℓ : Lp ℝ 2 P} (hN : N ⊆ (meanZeroL2 P : Set (Lp ℝ 2 P))) (hℓ : ℓ ∈ meanZeroL2 P) :
    efficientScore P N ℓ ∈ meanZeroL2 P :=
  (meanZeroL2 P).sub_mem hℓ
    (tangentSpace_le_meanZeroL2 hN ((tangentSpace P N).toSubmodule.starProjection_apply_mem ℓ))

/-- Pythagorean decomposition of a score into its efficient score and its nuisance projection. -/
theorem norm_sq_eq_norm_efficientScore_sq_add (P : Measure X) (N : Set (Lp ℝ 2 P))
    (ℓ : Lp ℝ 2 P) :
    ‖ℓ‖ ^ 2 =
      ‖efficientScore P N ℓ‖ ^ 2 + ‖(tangentSpace P N).toSubmodule.starProjection ℓ‖ ^ 2 := by
  rw [efficientScore_eq_starProjection_orthogonal, add_comm]
  exact Submodule.norm_sq_eq_add_norm_sq_starProjection ℓ (tangentSpace P N).toSubmodule

/-- Orthogonal projection onto the nuisance tangent space can only shrink the norm of `ℓ`. -/
theorem norm_efficientScore_le (P : Measure X) (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    ‖efficientScore P N ℓ‖ ≤ ‖ℓ‖ := by
  rw [efficientScore_eq_starProjection_orthogonal]
  exact ((tangentSpace P N).toSubmoduleᗮ.starProjection.le_opNorm ℓ).trans
    (mul_le_of_le_one_left (norm_nonneg ℓ) (Submodule.starProjection_norm_le _))

/-- The information matrix `Iᵢⱼ = ⟪ℓ i, ℓ j⟫_ℝ` of an indexed family of scores in `Lp ℝ 2 P`. -/
def informationMatrix {ι : Type*} (P : Measure X) (ℓ : ι → Lp ℝ 2 P) : Matrix ι ι ℝ :=
  Matrix.gram ℝ ℓ

/-- `informationMatrix P ℓ` is the Gram matrix of `ℓ`. -/
theorem informationMatrix_eq_gram {ι : Type*} (P : Measure X) (ℓ : ι → Lp ℝ 2 P) :
    informationMatrix P ℓ = Matrix.gram ℝ ℓ := (rfl)

/-- Entry `(i, j)` of `informationMatrix P ℓ` is `⟪ℓ i, ℓ j⟫_ℝ`. -/
@[simp]
theorem informationMatrix_apply {ι : Type*} (P : Measure X) (ℓ : ι → Lp ℝ 2 P) (i j : ι) :
    informationMatrix P ℓ i j = ⟪ℓ i, ℓ j⟫_ℝ := (rfl)

/-- The efficient information matrix `(i, j) ↦ ⟪efficientScore P N (ℓ i), efficientScore P N (ℓ j)⟫`
of an indexed family of scores relative to a nuisance tangent set `N`. -/
def efficientInformationMatrix {ι : Type*} (P : Measure X) (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) : Matrix ι ι ℝ :=
  Matrix.gram ℝ fun i ↦ efficientScore P N (ℓ i)

/-- `efficientInformationMatrix P N ℓ` is the Gram matrix of `i ↦ efficientScore P N (ℓ i)`. -/
theorem efficientInformationMatrix_eq_gram {ι : Type*} (P : Measure X) (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) :
    efficientInformationMatrix P N ℓ = Matrix.gram ℝ (fun i ↦ efficientScore P N (ℓ i)) := (rfl)

/-- `efficientInformationMatrix P N ℓ` is `informationMatrix P` applied to the efficient scores. -/
theorem efficientInformationMatrix_eq_informationMatrix {ι : Type*} (P : Measure X)
    (N : Set (Lp ℝ 2 P)) (ℓ : ι → Lp ℝ 2 P) :
    efficientInformationMatrix P N ℓ = informationMatrix P (fun i ↦ efficientScore P N (ℓ i)) :=
  (rfl)

/-- Entry `(i, j)` of `efficientInformationMatrix P N ℓ` is the inner product of the efficient
scores of `ℓ i` and `ℓ j`. -/
@[simp]
theorem efficientInformationMatrix_apply {ι : Type*} (P : Measure X) (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) (i j : ι) :
    efficientInformationMatrix P N ℓ i j =
      ⟪efficientScore P N (ℓ i), efficientScore P N (ℓ j)⟫_ℝ := (rfl)

/-- With no nuisance scores, the efficient information matrix equals the information matrix. -/
@[simp]
theorem efficientInformationMatrix_empty {ι : Type*} (P : Measure X) (ℓ : ι → Lp ℝ 2 P) :
    efficientInformationMatrix P ∅ ℓ = informationMatrix P ℓ := by
  ext i j
  simp

/-- The information matrix is symmetric. -/
theorem isSymm_informationMatrix {ι : Type*} (P : Measure X) (ℓ : ι → Lp ℝ 2 P) :
    (informationMatrix P ℓ).IsSymm := by
  rw [Matrix.IsSymm, informationMatrix_eq_gram, ← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact (Matrix.isHermitian_gram ℝ ℓ).eq

/-- The efficient information matrix is symmetric. -/
theorem isSymm_efficientInformationMatrix {ι : Type*} (P : Measure X) (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) : (efficientInformationMatrix P N ℓ).IsSymm :=
  isSymm_informationMatrix P _

/-- The information matrix of any family of scores is positive semidefinite. -/
theorem posSemidef_informationMatrix {ι : Type*} (P : Measure X) (ℓ : ι → Lp ℝ 2 P) :
    (informationMatrix P ℓ).PosSemidef :=
  Matrix.posSemidef_gram ℝ ℓ

/-- The efficient information matrix of any family of scores is positive semidefinite. -/
theorem posSemidef_efficientInformationMatrix {ι : Type*} (P : Measure X) (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) : (efficientInformationMatrix P N ℓ).PosSemidef :=
  Matrix.posSemidef_gram ℝ _

/-- `informationMatrix P ℓ` is positive definite if and only if the scores `ℓ` are linearly
independent in `Lp ℝ 2 P`. -/
theorem posDef_informationMatrix_iff {ι : Type*} {P : Measure X}
    {ℓ : ι → Lp ℝ 2 P} :
    (informationMatrix P ℓ).PosDef ↔ LinearIndependent ℝ ℓ :=
  Matrix.posDef_gram_iff_linearIndependent

/-- `efficientInformationMatrix P N ℓ` is positive definite if and only if the efficient scores
`i ↦ efficientScore P N (ℓ i)` are linearly independent in `Lp ℝ 2 P`. -/
theorem posDef_efficientInformationMatrix_iff {ι : Type*} {P : Measure X}
    {N : Set (Lp ℝ 2 P)} {ℓ : ι → Lp ℝ 2 P} :
    (efficientInformationMatrix P N ℓ).PosDef ↔
      LinearIndependent ℝ (fun i ↦ efficientScore P N (ℓ i)) :=
  Matrix.posDef_gram_iff_linearIndependent

private theorem efficientScore_comp_eq_starProjection_orthogonal {ι : Type*} (P : Measure X)
    (N : Set (Lp ℝ 2 P)) (ℓ : ι → Lp ℝ 2 P) :
    (fun i ↦ efficientScore P N (ℓ i)) =
      (tangentSpace P N).toSubmoduleᗮ.starProjection ∘ ℓ :=
  funext fun i ↦ efficientScore_eq_starProjection_orthogonal P N (ℓ i)

/-- The information lost to the nuisance set `N` is the Gram matrix of the nuisance projections
`i ↦ Π_N (ℓ i)`. -/
theorem informationMatrix_sub_efficientInformationMatrix {ι : Type*} (P : Measure X)
    (N : Set (Lp ℝ 2 P)) (ℓ : ι → Lp ℝ 2 P) :
    informationMatrix P ℓ - efficientInformationMatrix P N ℓ =
      Matrix.gram ℝ ((tangentSpace P N).toSubmodule.starProjection ∘ ℓ) := by
  rw [informationMatrix_eq_gram, efficientInformationMatrix_eq_gram,
    efficientScore_comp_eq_starProjection_orthogonal]
  exact (tangentSpace P N).toSubmodule.gram_sub_gram_starProjection_orthogonal ℓ

/-- Information-loss inequality: `informationMatrix P ℓ - efficientInformationMatrix P N ℓ` is
positive semidefinite. -/
theorem posSemidef_informationMatrix_sub_efficient {ι : Type*} (P : Measure X)
    (N : Set (Lp ℝ 2 P)) (ℓ : ι → Lp ℝ 2 P) :
    (informationMatrix P ℓ - efficientInformationMatrix P N ℓ).PosSemidef := by
  rw [informationMatrix_eq_gram, efficientInformationMatrix_eq_gram,
    efficientScore_comp_eq_starProjection_orthogonal]
  exact (tangentSpace P N).toSubmodule.posSemidef_gram_sub_gram_starProjection_orthogonal ℓ

/-- Algebraic adaptation criterion: there is no loss of information
(`efficientInformationMatrix P N ℓ = informationMatrix P ℓ`) if and only if every score `ℓ i` is
orthogonal to every nuisance score `g ∈ N`. -/
theorem efficientInformationMatrix_eq_informationMatrix_iff {ι : Type*} {P : Measure X}
    {N : Set (Lp ℝ 2 P)} {ℓ : ι → Lp ℝ 2 P} :
    efficientInformationMatrix P N ℓ = informationMatrix P ℓ ↔
      ∀ i, ∀ g ∈ N, ⟪g, ℓ i⟫_ℝ = 0 := by
  rw [informationMatrix_eq_gram, efficientInformationMatrix_eq_gram,
    efficientScore_comp_eq_starProjection_orthogonal,
    (tangentSpace P N).toSubmodule.gram_starProjection_orthogonal_eq_gram_iff]
  simp only [ClosedSubmodule.mem_orthogonal_toSubmodule_iff, mem_orthogonal_tangentSpace_iff]

/-- For nested nuisance sets `N ⊆ N'`, the drop in efficient information
`efficientInformationMatrix P N ℓ - efficientInformationMatrix P N' ℓ` is the Gram matrix of
`i ↦ (Π_{N'} - Π_N) (ℓ i)`. -/
theorem efficientInformationMatrix_sub_of_subset {ι : Type*} {P : Measure X}
    {N N' : Set (Lp ℝ 2 P)} (h : N ⊆ N') (ℓ : ι → Lp ℝ 2 P) :
    efficientInformationMatrix P N ℓ - efficientInformationMatrix P N' ℓ =
      Matrix.gram ℝ
        (⇑((tangentSpace P N').toSubmodule.starProjection -
          (tangentSpace P N).toSubmodule.starProjection) ∘ ℓ) := by
  rw [efficientInformationMatrix_eq_gram, efficientInformationMatrix_eq_gram,
    efficientScore_comp_eq_starProjection_orthogonal,
    efficientScore_comp_eq_starProjection_orthogonal]
  exact Submodule.gram_starProjection_orthogonal_sub_of_le (tangentSpace_mono h) ℓ

/-- Enlarging the nuisance tangent set from `N` to `N'` lowers the efficient information matrix in
the positive-semidefinite order. -/
theorem posSemidef_efficientInformationMatrix_sub_of_subset {ι : Type*} {P : Measure X}
    {N N' : Set (Lp ℝ 2 P)} (h : N ⊆ N') (ℓ : ι → Lp ℝ 2 P) :
    (efficientInformationMatrix P N ℓ - efficientInformationMatrix P N' ℓ).PosSemidef := by
  rw [efficientInformationMatrix_eq_gram, efficientInformationMatrix_eq_gram,
    efficientScore_comp_eq_starProjection_orthogonal,
    efficientScore_comp_eq_starProjection_orthogonal]
  exact Submodule.posSemidef_gram_starProjection_orthogonal_sub_of_le (tangentSpace_mono h) ℓ

end TauCeti
