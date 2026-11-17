/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Trace
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Basic
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.ExteriorSquare
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback
public import TauCeti.Geometry.Manifold.Riemannian.Scaling
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Bound
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Metric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Pinching
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Trace

/-!
# Norms of the Riemann curvature tensor and curvature operator conversions

Let `∇` be a smooth connection on the tangent bundle of a Riemannian manifold `M` of real
dimension `n`. The squared Hilbert–Schmidt norm of its pointwise `(1, 3)` curvature tensor at
`x : M` is

`|Rm|² = ∑ᵢ ∑ⱼ ∑ₖ ‖R(eᵢ, eⱼ) eₖ‖² = ∑ᵢ ∑ⱼ ∑ₖ ∑ₗ ⟪R(eᵢ, eⱼ) eₖ, eₗ⟫²`,

evaluated in any orthonormal basis `(eᵢ)` of `Tₓ M`, and its Hilbert–Schmidt norm is
`|Rm| = √(|Rm|²)`. The definition is independent of the choice of orthonormal basis and requires
neither metric compatibility nor vanishing torsion.

When `∇` is compatible with the metric, `CovariantDerivative.curvatureEndomorphism` realizes `Rm`
as a linear endomorphism `Rop` of `⋀² Tₓ M` with `⟪Rop(u ∧ v), w ∧ z⟫ = ⟪R(u, v)z, w⟫`. Because
ordered wedges `eᵢ ∧ eⱼ` count each basis bivector twice
(`OrthonormalBasis.sum_sq_inner_apply_ιMulti_two`), the full tensor norm and the Frobenius /
Hilbert–Schmidt norm of `Rop` satisfy the exact identity

`|Rm|² = 4 ‖Rop‖_F²`, `|Rm| = 2 ‖Rop‖_F`.

This file records the exact conversions between `|Rm|`, `‖Rop‖_F`, the operator norm `‖Rop‖_op`,
eigenvalues of `Rop`, the trilinear operator bound on `R(u, v)w`, sectional curvature, and scalar
curvature:

* `‖Rop‖_op ≤ ‖Rop‖_F = |Rm| / 2`, and `|Rm| ≤ √(2 n (n - 1)) ‖Rop‖_op`.
* `|⟪Rop z, z⟫| ≤ ‖Rop‖_op ‖z‖² ≤ (|Rm| / 2) ‖z‖²`, so every eigenvalue `μ` of `Rop` satisfies
  `|μ| ≤ ‖Rop‖_op ≤ |Rm| / 2`.
* `‖R(u, v) w‖ ≤ ‖Rop‖_op ‖u‖ ‖v‖ ‖w‖ ≤ (|Rm| / 2) ‖u‖ ‖v‖ ‖w‖` (sharp on round spheres);
  conversely `‖R(u, v) w‖ ≤ C ‖u‖ ‖v‖ ‖w‖` gives `|Rm|² ≤ n (n - 1) n C²`.
* `|K(u, v)| ≤ ‖Rop‖_op ≤ |Rm| / 2` for linearly independent tangent vectors `u, v`.
* `|Scal| ≤ √(n (n - 1) / 2) |Rm|` (sharp on space forms), and a lower bound `Rop ≥ α Id` yields
  `n (n - 1) α ≤ Scal`.
* On constant sectional curvature `κ`, `|Rm|² = 2 n (n - 1) κ²` and `|Rm| = √(2 n (n - 1)) |κ|`.

For a smooth Riemannian metric `g`, the file defines `g.curvatureTensorNorm` and establishes its
boundedness on compact sets, its invariance under local Riemannian isometries and pullbacks, its
additivity on Riemannian products (`|Rm_{g₁ × g₂}|²(x, y) = |Rm_{g₁}|²(x) + |Rm_{g₂}|²(y)`), and
its scaling laws under constant positive rescaling `c g` (`c > 0`):

* `Rop_{c g} = c⁻¹ Rop_g`, so eigenvalues and quadratic-form bounds scale by `c⁻¹`,
* `|Rm_{c g}|² = c⁻² |Rm_g|²` and `|Rm_{c g}| = c⁻¹ |Rm_g|`.

## Main definitions

* `CovariantDerivative.curvatureTensorNormSq`: the squared Hilbert–Schmidt norm `|Rm|²` at `x`.
* `CovariantDerivative.curvatureTensorNorm`: the Hilbert–Schmidt norm `|Rm| = √(|Rm|²)` at `x`.
* `Bundle.ContMDiffRiemannianMetric.curvatureTensorNorm`: the curvature tensor norm of a smooth
  Riemannian metric `g`.
* `Bundle.ContMDiffRiemannianMetric.HasCurvatureOperatorLowerBoundAt`: pointwise lower bound
  `Rop_g(x) ≥ α • Id` on the curvature operator of a smooth Riemannian metric `g`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 7–8 (curvature tensor, curvature operator, and contractions).
* P. Petersen, *Riemannian Geometry*, 3rd ed., Springer GTM 171 (2016), Chapter 9.
* J. W. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Mathematics
  Monographs 3 (2007), Chapter 4 (curvature norms and curvature-operator conventions).
-/

public section

open Bundle Manifold Module TauCeti.UnitarilyInvariantSeminorm
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace CovariantDerivative

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

/-- The squared Hilbert–Schmidt norm of the curvature tensor of `cov` at `x`, defined in the
standard orthonormal basis of `Tₓ M`; independent of the choice of orthonormal basis by
`CovariantDerivative.curvatureTensorNormSq_eq_sum`. -/
def curvatureTensorNormSq (x : M) : ℝ :=
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  ∑ i, ∑ j, ∑ k, ‖cov.curvatureTensor x (b i) (b j) (b k)‖ ^ 2

/-- The Hilbert–Schmidt norm `|Rm|` of the curvature tensor of `cov` at `x`. -/
def curvatureTensorNorm (x : M) : ℝ :=
  Real.sqrt (cov.curvatureTensorNormSq x)

/-- The squared curvature tensor norm `|Rm|²` is nonnegative. -/
theorem curvatureTensorNormSq_nonneg (x : M) : 0 ≤ cov.curvatureTensorNormSq x := by
  unfold curvatureTensorNormSq
  positivity

/-- The curvature tensor norm `|Rm|` is nonnegative. -/
theorem curvatureTensorNorm_nonneg (x : M) : 0 ≤ cov.curvatureTensorNorm x :=
  Real.sqrt_nonneg _

/-- Squaring `|Rm|` recovers `|Rm|²`. -/
@[simp]
theorem sq_curvatureTensorNorm (x : M) :
    cov.curvatureTensorNorm x ^ 2 = cov.curvatureTensorNormSq x :=
  Real.sq_sqrt (cov.curvatureTensorNormSq_nonneg x)

/-- Any orthonormal basis `(bᵢ)` computes the same squared Hilbert–Schmidt norm of a trilinear
map `T : V →ₗ V →ₗ V →ₗ V`. -/
private theorem sum_norm_sq_trilinear_indep {V ι ι' : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Fintype ι] [Fintype ι']
    (T : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V) (b : OrthonormalBasis ι ℝ V) (c : OrthonormalBasis ι' ℝ V) :
    ∑ i, ∑ j, ∑ k, ‖T (b i) (b j) (b k)‖ ^ 2 = ∑ i, ∑ j, ∑ k, ‖T (c i) (c j) (c k)‖ ^ 2 := by
  have h1 : ∀ u v : V, ∑ k, ‖T u v (b k)‖ ^ 2 = ∑ k, ‖T u v (c k)‖ ^ 2 := fun u v ↦
    (T u v).sum_norm_apply_sq_eq_sum_norm_apply_sq b c
  have h2 : ∀ u w : V, ∑ j, ‖T u (b j) w‖ ^ 2 = ∑ j, ‖T u (c j) w‖ ^ 2 := fun u w ↦ by
    let A : V →ₗ[ℝ] V := (T u).flip w
    simpa [A] using A.sum_norm_apply_sq_eq_sum_norm_apply_sq b c
  have h3 : ∀ v w : V, ∑ i, ‖T (b i) v w‖ ^ 2 = ∑ i, ‖T (c i) v w‖ ^ 2 := fun v w ↦ by
    let A : V →ₗ[ℝ] V :=
      { toFun := fun u ↦ T u v w
        map_add' := fun u₁ u₂ ↦ by simp
        map_smul' := fun r u ↦ by simp }
    simpa [A] using A.sum_norm_apply_sq_eq_sum_norm_apply_sq b c
  calc ∑ i, ∑ j, ∑ k, ‖T (b i) (b j) (b k)‖ ^ 2
      = ∑ i, ∑ j, ∑ k, ‖T (b i) (b j) (c k)‖ ^ 2 := by simp_rw [h1]
    _ = ∑ i, ∑ k, ∑ j, ‖T (b i) (b j) (c k)‖ ^ 2 :=
          Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ j, ‖T (b i) (c j) (c k)‖ ^ 2 := by simp_rw [h2]
    _ = ∑ k, ∑ i, ∑ j, ‖T (b i) (c j) (c k)‖ ^ 2 := Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, ‖T (b i) (c j) (c k)‖ ^ 2 :=
          Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, ‖T (c i) (c j) (c k)‖ ^ 2 := by simp_rw [h3]
    _ = ∑ k, ∑ i, ∑ j, ‖T (c i) (c j) (c k)‖ ^ 2 :=
          Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ j, ‖T (c i) (c j) (c k)‖ ^ 2 := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, ‖T (c i) (c j) (c k)‖ ^ 2 :=
          Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm

/-- The squared curvature tensor norm may be computed in any orthonormal basis of `Tₓ M`. -/
theorem curvatureTensorNormSq_eq_sum {ι : Type*} [Fintype ι] (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.curvatureTensorNormSq x = ∑ i, ∑ j, ∑ k, ‖cov.curvatureTensor x (b i) (b j) (b k)‖ ^ 2 :=
  sum_norm_sq_trilinear_indep (cov.curvatureTensor x) (stdOrthonormalBasis ℝ (TangentSpace I x)) b

/-- The squared curvature tensor norm is the quadruple sum of squared components of the
metric-lowered Riemann tensor in any orthonormal basis of `Tₓ M`. -/
theorem curvatureTensorNormSq_eq_sum_inner {ι : Type*} [Fintype ι] (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.curvatureTensorNormSq x =
      ∑ i, ∑ j, ∑ k, ∑ l, ⟪cov.curvatureTensor x (b i) (b j) (b k), b l⟫ ^ 2 := by
  rw [cov.curvatureTensorNormSq_eq_sum x b]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun k _ ↦ ?_
  simpa only [real_inner_comm (b _)] using
    (b.sum_sq_inner_right (cov.curvatureTensor x (b i) (b j) (b k))).symm

/-- The curvature tensor norm in terms of `riemannCurvatureTensor` components. -/
theorem curvatureTensorNormSq_eq_sum_riemannCurvatureTensor {ι : Type*} [Fintype ι] (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.curvatureTensorNormSq x =
      ∑ i, ∑ j, ∑ k, ∑ l, cov.riemannCurvatureTensor x (b i) (b j) (b k) (b l) ^ 2 := by
  rw [cov.curvatureTensorNormSq_eq_sum_inner x b]
  simp only [CovariantDerivative.riemannCurvatureTensor_apply]

/-- The squared curvature norm vanishes when the curvature tensor vanishes at `x`. -/
@[simp]
theorem curvatureTensorNormSq_eq_zero_of_curvatureTensor_eq_zero {x : M}
    (h : cov.curvatureTensor x = 0) : cov.curvatureTensorNormSq x = 0 := by
  simp [curvatureTensorNormSq, h]

/-- The curvature norm vanishes when the curvature tensor vanishes at `x`. -/
@[simp]
theorem curvatureTensorNorm_eq_zero_of_curvatureTensor_eq_zero {x : M}
    (h : cov.curvatureTensor x = 0) : cov.curvatureTensorNorm x = 0 := by
  simp [curvatureTensorNorm, h]

/-- A pointwise curvature tensor norm vanishes in dimension at most one. -/
theorem curvatureTensorNorm_eq_zero_of_finrank_le_one (hdim : finrank ℝ E ≤ 1) (x : M) :
    cov.curvatureTensorNorm x = 0 :=
  cov.curvatureTensorNorm_eq_zero_of_curvatureTensor_eq_zero
    (cov.curvatureTensor_eq_zero_of_finrank_le_one x hdim)

/-- **Conversion from a trilinear operator bound to the squared tensor norm.** If
`‖R(u, v) w‖ ≤ C ‖u‖ ‖v‖ ‖w‖`, then `|Rm|² ≤ n (n - 1) n C²` (using `R(eᵢ, eᵢ) = 0` to remove
diagonal pairs). -/
theorem curvatureTensorNormSq_le_of_forall_norm_curvatureTensor_le {x : M} {C : ℝ}
    (h : ∀ u v w : TangentSpace I x, ‖cov.curvatureTensor x u v w‖ ≤ C * ‖u‖ * ‖v‖ * ‖w‖) :
    cov.curvatureTensorNormSq x ≤
      (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) - 1) * (finrank ℝ E : ℝ) * C ^ 2 := by
  classical
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [cov.curvatureTensorNormSq_eq_sum x b]
  have hterm : ∀ i j k, ‖cov.curvatureTensor x (b i) (b j) (b k)‖ ^ 2 ≤
      if i = j then 0 else C ^ 2 := fun i j k ↦ by
    split_ifs with hij
    · subst hij
      simp [cov.curvatureTensor_self]
    · have h1 := h (b i) (b j) (b k)
      simp only [b.orthonormal.1, mul_one] at h1
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc ∑ i, ∑ j, ∑ k, ‖cov.curvatureTensor x (b i) (b j) (b k)‖ ^ 2
      ≤ ∑ i : Fin (finrank ℝ (TangentSpace I x)),
          ∑ j : Fin (finrank ℝ (TangentSpace I x)),
            ∑ _k : Fin (finrank ℝ (TangentSpace I x)), (if i = j then (0 : ℝ) else C ^ 2) :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
          Finset.sum_le_sum fun k _ ↦ hterm i j k
    _ = (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) - 1) * (finrank ℝ E : ℝ) * C ^ 2 := by
        have hdim : finrank ℝ (TangentSpace I x) = finrank ℝ E := rfl
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hcard : ∀ i : Fin (finrank ℝ (TangentSpace I x)),
            (Finset.univ.filter fun j ↦ ¬i = j).card =
              finrank ℝ (TangentSpace I x) - 1 := fun i ↦ by
          have : (Finset.univ.filter fun j : Fin (finrank ℝ (TangentSpace I x)) ↦ ¬i = j) =
              Finset.univ.erase i := by
            ext j; simp [eq_comm]
          rw [this, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
            Fintype.card_fin]
        simp_rw [mul_ite, mul_zero, Finset.sum_ite, Finset.sum_const_zero, zero_add,
          Finset.sum_const, nsmul_eq_mul, hcard, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, hdim]
        cases hn : finrank ℝ E with
        | zero => simp
        | succ m =>
          push_cast
          ring

/-- On a compact set, the Hilbert–Schmidt curvature tensor norm is uniformly bounded. -/
theorem exists_curvatureTensorNorm_le_of_isCompact
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] {K : Set M}
    (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, cov.curvatureTensorNorm x ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_curvatureTensor_le_of_isCompact (F := E)
    (V := fun x : M ↦ TangentSpace I x) cov hK
  set C₀ := max C 0
  have hC₀ : 0 ≤ C₀ := le_max_right _ _
  refine ⟨Real.sqrt ((finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) - 1) * (finrank ℝ E : ℝ)) * C₀,
    by positivity, fun x hx ↦ ?_⟩
  rw [curvatureTensorNorm, ← Real.sqrt_sq hC₀, ← Real.sqrt_mul]
  · apply Real.sqrt_le_sqrt
    exact cov.curvatureTensorNormSq_le_of_forall_norm_curvatureTensor_le fun u v w ↦
      (hC x hx u v w).trans (by gcongr; exact le_max_left _ _)
  · cases hn : finrank ℝ E with
    | zero => simp
    | succ m =>
      push_cast
      rw [add_sub_cancel_right]
      positivity

end Basic

section MetricCompatible

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]
  (hcov : CovariantDerivative.IsMetricCompatible
    (V := fun x : M ↦ TangentSpace I x) cov)

/-- **Exact conversion between the full tensor norm and the Frobenius norm of `Rop`.**
`|Rm|² = 4 ‖Rop‖_F²`. -/
theorem curvatureTensorNormSq_eq_four_mul_sq_frobenius_curvatureEndomorphism (x : M) :
    cov.curvatureTensorNormSq x =
      4 * frobenius ℝ (⋀[ℝ]^2 (TangentSpace I x)) (⋀[ℝ]^2 (TangentSpace I x))
        (cov.curvatureEndomorphism hcov x) ^ 2 := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  let c := stdOrthonormalBasis ℝ (⋀[ℝ]^2 (TangentSpace I x))
  let T := cov.curvatureEndomorphism hcov x
  have htrace : LinearMap.trace ℝ (⋀[ℝ]^2 (TangentSpace I x)) (LinearMap.adjoint T ∘ₗ T) =
      frobenius ℝ (⋀[ℝ]^2 (TangentSpace I x)) (⋀[ℝ]^2 (TangentSpace I x)) T ^ 2 := by
    rw [sq_frobenius_apply c T]
    simpa using T.trace_adjoint_comp_self_eq_sum_norm_apply_sq c
  rw [← htrace, ← b.sum_sq_inner_apply_ιMulti_two T, cov.curvatureTensorNormSq_eq_sum_inner x b]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  simp only [T, cov.inner_curvatureEndomorphism_ιMulti, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Exact conversion between `|Rm|` and `‖Rop‖_F`**: `|Rm| = 2 ‖Rop‖_F`. -/
theorem curvatureTensorNorm_eq_two_mul_frobenius_curvatureEndomorphism (x : M) :
    cov.curvatureTensorNorm x =
      2 * frobenius ℝ (⋀[ℝ]^2 (TangentSpace I x)) (⋀[ℝ]^2 (TangentSpace I x))
        (cov.curvatureEndomorphism hcov x) := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [curvatureTensorNorm,
    cov.curvatureTensorNormSq_eq_four_mul_sq_frobenius_curvatureEndomorphism hcov x,
    Real.sqrt_mul (by norm_num), Real.sqrt_sq (apply_nonneg _ _), h4]

/-- On the finite-dimensional exterior square, the Frobenius seminorm of `Rop` equals its
`ContinuousLinearMap.hilbertSchmidtNorm`. -/
theorem frobenius_curvatureEndomorphism_eq_hilbertSchmidtNorm (x : M) :
    frobenius ℝ (⋀[ℝ]^2 (TangentSpace I x)) (⋀[ℝ]^2 (TangentSpace I x))
        (cov.curvatureEndomorphism hcov x) =
      (LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)).hilbertSchmidtNorm := by
  let b := (stdOrthonormalBasis ℝ (⋀[ℝ]^2 (TangentSpace I x))).toHilbertBasis
  rw [ContinuousLinearMap.hilbertSchmidtNorm_eq_sqrt _ b,
    ContinuousLinearMap.hilbertSchmidtEnergy_eq_ofReal_sq_frobenius _ b,
    ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq (apply_nonneg _ _)]
  rfl

/-- The operator norm of `Rop` is at most its Frobenius norm `‖Rop‖_F`. -/
theorem opNorm_curvatureEndomorphism_le_frobenius (x : M) :
    ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ ≤
      frobenius ℝ (⋀[ℝ]^2 (TangentSpace I x)) (⋀[ℝ]^2 (TangentSpace I x))
        (cov.curvatureEndomorphism hcov x) := by
  rw [cov.frobenius_curvatureEndomorphism_eq_hilbertSchmidtNorm hcov x]
  let b := (stdOrthonormalBasis ℝ (⋀[ℝ]^2 (TangentSpace I x))).toHilbertBasis
  refine ContinuousLinearMap.norm_le_hilbertSchmidtNorm _ b ?_
  rw [ContinuousLinearMap.hilbertSchmidtEnergy_eq_ofReal_sq_frobenius _ b]
  exact ENNReal.ofReal_ne_top

/-- **Operator norm bound from `|Rm|`:** `‖Rop‖_op ≤ |Rm| / 2`. -/
theorem opNorm_curvatureEndomorphism_le_half_curvatureTensorNorm (x : M) :
    ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ ≤
      cov.curvatureTensorNorm x / 2 := by
  rw [cov.curvatureTensorNorm_eq_two_mul_frobenius_curvatureEndomorphism hcov x]
  linarith [cov.opNorm_curvatureEndomorphism_le_frobenius hcov x]

private theorem two_mul_choose_two_eq (n : ℕ) :
    (2 : ℝ) * ((n.choose 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
  have hnat : 2 * n.choose 2 = n * (n - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]
  cases n with
  | zero => simp
  | succ m =>
    have : ((2 * (m + 1).choose 2 : ℕ) : ℝ) = (((m + 1) * m : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at this ⊢
    linarith

/-- **Frobenius-to-operator bound on `Rop`:** `‖Rop‖_F ≤ √(n.choose 2) ‖Rop‖_op`. -/
theorem frobenius_curvatureEndomorphism_le_sqrt_mul_opNorm (x : M) :
    frobenius ℝ (⋀[ℝ]^2 (TangentSpace I x)) (⋀[ℝ]^2 (TangentSpace I x))
        (cov.curvatureEndomorphism hcov x) ≤
      Real.sqrt ((finrank ℝ E).choose 2 : ℝ) *
        ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ := by
  let b := stdOrthonormalBasis ℝ (⋀[ℝ]^2 (TangentSpace I x))
  let T := LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)
  have hdim : finrank ℝ (TangentSpace I x) = finrank ℝ E := rfl
  have hfin : finrank ℝ (⋀[ℝ]^2 (TangentSpace I x)) = (finrank ℝ E).choose 2 := by
    rw [exteriorPower.finrank_eq, hdim]
  have hsq : frobenius ℝ (⋀[ℝ]^2 (TangentSpace I x)) (⋀[ℝ]^2 (TangentSpace I x))
        (cov.curvatureEndomorphism hcov x) ^ 2 ≤
      ((finrank ℝ E).choose 2 : ℝ) * ‖T‖ ^ 2 := by
    rw [sq_frobenius_apply b]
    calc ∑ i, ‖cov.curvatureEndomorphism hcov x (b i)‖ ^ 2
        ≤ ∑ _i : Fin (finrank ℝ (⋀[ℝ]^2 (TangentSpace I x))), ‖T‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have h1 : ‖T (b i)‖ ≤ ‖T‖ * ‖b i‖ := T.le_opNorm (b i)
          rw [b.orthonormal.1 i, mul_one] at h1
          exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = ((finrank ℝ E).choose 2 : ℝ) * ‖T‖ ^ 2 := by
          simp [hfin]
  have hnonneg : 0 ≤ Real.sqrt ((finrank ℝ E).choose 2 : ℝ) * ‖T‖ := by positivity
  refine (sq_le_sq₀ (apply_nonneg _ _) hnonneg).1 ?_
  rwa [mul_pow, Real.sq_sqrt (by positivity)]

/-- **Tensor-to-operator bound:** `|Rm| ≤ √(2 n (n - 1)) ‖Rop‖_op`. -/
theorem curvatureTensorNorm_le_sqrt_mul_opNorm_curvatureEndomorphism (x : M) :
    cov.curvatureTensorNorm x ≤
      Real.sqrt (2 * (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) - 1)) *
        ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ := by
  rw [cov.curvatureTensorNorm_eq_two_mul_frobenius_curvatureEndomorphism hcov x]
  have h := mul_le_mul_of_nonneg_left
    (cov.frobenius_curvatureEndomorphism_le_sqrt_mul_opNorm hcov x)
    (by norm_num : (0 : ℝ) ≤ 2)
  refine h.trans_eq ?_
  rw [← mul_assoc]
  congr 1
  have h2 := two_mul_choose_two_eq (finrank ℝ E)
  have hnonneg : 0 ≤ 2 * (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) - 1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) ((finrank ℝ E).choose 2)]
  refine (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).1 ?_
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hnonneg]
  linarith

/-- Quadratic-form bound from the operator norm: `|⟪Rop z, z⟫| ≤ ‖Rop‖_op ‖z‖²`. -/
theorem abs_inner_curvatureEndomorphism_le_opNorm (x : M) (z : ⋀[ℝ]^2 (TangentSpace I x)) :
    |⟪cov.curvatureEndomorphism hcov x z, z⟫| ≤
      ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ * ‖z‖ ^ 2 := by
  let T := LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)
  calc |⟪cov.curvatureEndomorphism hcov x z, z⟫|
      ≤ ‖cov.curvatureEndomorphism hcov x z‖ * ‖z‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖T‖ * ‖z‖) * ‖z‖ :=
        mul_le_mul_of_nonneg_right (T.le_opNorm z) (norm_nonneg z)
    _ = ‖T‖ * ‖z‖ ^ 2 := by ring

/-- Quadratic-form bound from `|Rm|`: `|⟪Rop z, z⟫| ≤ (|Rm| / 2) ‖z‖²`. -/
theorem abs_inner_curvatureEndomorphism_le_half_curvatureTensorNorm (x : M)
    (z : ⋀[ℝ]^2 (TangentSpace I x)) :
    |⟪cov.curvatureEndomorphism hcov x z, z⟫| ≤
      (cov.curvatureTensorNorm x / 2) * ‖z‖ ^ 2 :=
  (cov.abs_inner_curvatureEndomorphism_le_opNorm hcov x z).trans
    (mul_le_mul_of_nonneg_right
      (cov.opNorm_curvatureEndomorphism_le_half_curvatureTensorNorm hcov x) (sq_nonneg _))

/-- Pointwise quadratic-form lower bound from `|Rm|`: `-(|Rm| / 2) ‖z‖² ≤ ⟪Rop z, z⟫`. -/
theorem neg_half_curvatureTensorNorm_le_inner_curvatureEndomorphism (x : M)
    (z : ⋀[ℝ]^2 (TangentSpace I x)) :
    -(cov.curvatureTensorNorm x / 2) * ‖z‖ ^ 2 ≤
      ⟪cov.curvatureEndomorphism hcov x z, z⟫ := by
  have h := (abs_le.1 (cov.abs_inner_curvatureEndomorphism_le_half_curvatureTensorNorm hcov x z)).1
  linarith

/-- Every eigenvalue `μ` of `Rop` satisfies `|μ| ≤ ‖Rop‖_op`. -/
theorem abs_le_opNorm_curvatureEndomorphism_of_hasEigenvalue {x : M} {μ : ℝ}
    (hμ : (cov.curvatureEndomorphism hcov x).HasEigenvalue μ) :
    |μ| ≤ ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  let T := LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)
  have h1 := T.le_opNorm v
  have h2 : ‖T v‖ = |μ| * ‖v‖ := by
    change ‖cov.curvatureEndomorphism hcov x v‖ = |μ| * ‖v‖
    rw [hv.apply_eq_smul, norm_smul, Real.norm_eq_abs]
  rw [h2] at h1
  exact le_of_mul_le_mul_right h1 (norm_pos_iff.2 hv.2)

/-- Every eigenvalue `μ` of `Rop` satisfies `|μ| ≤ |Rm| / 2`. -/
theorem abs_le_half_curvatureTensorNorm_of_hasEigenvalue {x : M} {μ : ℝ}
    (hμ : (cov.curvatureEndomorphism hcov x).HasEigenvalue μ) :
    |μ| ≤ cov.curvatureTensorNorm x / 2 :=
  (cov.abs_le_opNorm_curvatureEndomorphism_of_hasEigenvalue hcov hμ).trans
    (cov.opNorm_curvatureEndomorphism_le_half_curvatureTensorNorm hcov x)

/-- **Sharp trilinear bound from `‖Rop‖_op`:** `‖R(u, v) w‖ ≤ ‖Rop‖_op ‖u‖ ‖v‖ ‖w‖`.
Equality holds on the round sphere. -/
theorem norm_curvatureTensor_le_opNorm_curvatureEndomorphism (x : M)
    (u v w : TangentSpace I x) :
    ‖cov.curvatureTensor x u v w‖ ≤
      ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ *
        ‖u‖ * ‖v‖ * ‖w‖ := by
  let T := LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)
  set r := cov.curvatureTensor x u v w
  by_cases hr : r = 0
  · rw [hr, norm_zero]
    positivity
  have hrpos : 0 < ‖r‖ := norm_pos_iff.2 hr
  have hinner : ‖r‖ ^ 2 =
      ⟪cov.curvatureEndomorphism hcov x (exteriorPower.ιMulti ℝ 2 ![u, v]),
        exteriorPower.ιMulti ℝ 2 ![r, w]⟫ := by
    rw [cov.inner_curvatureEndomorphism_ιMulti hcov x ![u, v] ![r, w]]
    simp [r]
  have hle : ‖r‖ ^ 2 ≤ (‖T‖ * ‖u‖ * ‖v‖ * ‖w‖) * ‖r‖ := by
    calc ‖r‖ ^ 2
        = ⟪cov.curvatureEndomorphism hcov x (exteriorPower.ιMulti ℝ 2 ![u, v]),
            exteriorPower.ιMulti ℝ 2 ![r, w]⟫ := hinner
      _ ≤ ‖cov.curvatureEndomorphism hcov x (exteriorPower.ιMulti ℝ 2 ![u, v])‖ *
            ‖exteriorPower.ιMulti ℝ 2 ![r, w]‖ := real_inner_le_norm _ _
      _ ≤ (‖T‖ * ‖exteriorPower.ιMulti ℝ 2 ![u, v]‖) *
            ‖exteriorPower.ιMulti ℝ 2 ![r, w]‖ :=
          mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg _)
      _ ≤ (‖T‖ * (‖u‖ * ‖v‖)) * (‖r‖ * ‖w‖) := by
          gcongr
          · exact exteriorPower.norm_ιMulti_two_le u v
          · exact exteriorPower.norm_ιMulti_two_le r w
      _ = (‖T‖ * ‖u‖ * ‖v‖ * ‖w‖) * ‖r‖ := by ring
  rw [sq] at hle
  exact le_of_mul_le_mul_right hle hrpos

include hcov in
/-- **Trilinear bound from `|Rm|`:** `‖R(u, v) w‖ ≤ (|Rm| / 2) ‖u‖ ‖v‖ ‖w‖`. -/
theorem norm_curvatureTensor_le_half_curvatureTensorNorm (x : M)
    (u v w : TangentSpace I x) :
    ‖cov.curvatureTensor x u v w‖ ≤
      (cov.curvatureTensorNorm x / 2) * ‖u‖ * ‖v‖ * ‖w‖ :=
  (cov.norm_curvatureTensor_le_opNorm_curvatureEndomorphism hcov x u v w).trans (by
    gcongr
    exact cov.opNorm_curvatureEndomorphism_le_half_curvatureTensorNorm hcov x)

/-- Sectional curvature is bounded in absolute value by `‖Rop‖_op`. -/
theorem abs_sectionalCurvature_le_opNorm_curvatureEndomorphism (x : M)
    (u v : TangentSpace I x) :
    |cov.sectionalCurvature hcov x u v| ≤
      ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ := by
  rw [cov.sectionalCurvature_eq_curvatureEndomorphism hcov x u v, real_inner_self_eq_norm_sq,
    abs_div, abs_of_nonneg (sq_nonneg ‖exteriorPower.ιMulti ℝ 2 ![u, v]‖)]
  by_cases h0 : ‖exteriorPower.ιMulti ℝ 2 ![u, v]‖ ^ 2 = 0
  · rw [h0, div_zero]
    exact norm_nonneg (LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x))
  · rw [div_le_iff₀ (lt_of_le_of_ne (sq_nonneg _) (Ne.symm h0))]
    exact cov.abs_inner_curvatureEndomorphism_le_opNorm hcov x _

/-- Sectional curvature is bounded in absolute value by `|Rm| / 2`. -/
theorem abs_sectionalCurvature_le_half_curvatureTensorNorm (x : M)
    (u v : TangentSpace I x) :
    |cov.sectionalCurvature hcov x u v| ≤ cov.curvatureTensorNorm x / 2 :=
  (cov.abs_sectionalCurvature_le_opNorm_curvatureEndomorphism hcov x u v).trans
    (cov.opNorm_curvatureEndomorphism_le_half_curvatureTensorNorm hcov x)

include hcov in
/-- **Sharp Cauchy–Schwarz bound on scalar curvature:**
`|Scal| ≤ √(n (n - 1) / 2) |Rm|`. Equality holds on every space form. -/
theorem abs_scalarCurvature_le_mul_curvatureTensorNorm (x : M) :
    |cov.scalarCurvature x| ≤
      Real.sqrt ((finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) - 1) / 2) *
        cov.curvatureTensorNorm x := by
  let b := stdOrthonormalBasis ℝ (⋀[ℝ]^2 (TangentSpace I x))
  let T := cov.curvatureEndomorphism hcov x
  have hdim0 : finrank ℝ (TangentSpace I x) = finrank ℝ E := rfl
  have hfin : finrank ℝ (⋀[ℝ]^2 (TangentSpace I x)) = (finrank ℝ E).choose 2 := by
    rw [exteriorPower.finrank_eq, hdim0]
  have htr : LinearMap.trace ℝ (⋀[ℝ]^2 (TangentSpace I x)) T = ∑ i, ⟪b i, T (b i)⟫ := by
    simpa using LinearMap.trace_eq_sum_inner T b
  have hcs : (LinearMap.trace ℝ (⋀[ℝ]^2 (TangentSpace I x)) T) ^ 2 ≤
      ((finrank ℝ E).choose 2 : ℝ) *
        frobenius ℝ (⋀[ℝ]^2 (TangentSpace I x)) (⋀[ℝ]^2 (TangentSpace I x)) T ^ 2 := by
    rw [htr, sq_frobenius_apply b T]
    calc (∑ i, ⟪b i, T (b i)⟫) ^ 2
        = (∑ i, (1 : ℝ) * ⟪b i, T (b i)⟫) ^ 2 := by simp
      _ ≤ (∑ _i : Fin (finrank ℝ (⋀[ℝ]^2 (TangentSpace I x))), (1 : ℝ) ^ 2) *
            (∑ i, ⟪b i, T (b i)⟫ ^ 2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ ((finrank ℝ E).choose 2 : ℝ) * ∑ i, ‖T (b i)‖ ^ 2 := by
          simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            mul_one, hfin]
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ ?_) (by positivity)
          have h1 : |⟪b i, T (b i)⟫| ≤ ‖b i‖ * ‖T (b i)‖ := abs_real_inner_le_norm _ _
          rw [b.orthonormal.1 i, one_mul] at h1
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hdim : (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) - 1) / 2 = ((finrank ℝ E).choose 2 : ℝ) := by
    linarith [two_mul_choose_two_eq (finrank ℝ E)]
  rw [hdim, cov.scalarCurvature_eq_two_mul_trace_curvatureEndomorphism hcov x,
    cov.curvatureTensorNorm_eq_two_mul_frobenius_curvatureEndomorphism hcov x, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hnonneg : 0 ≤ Real.sqrt ((finrank ℝ E).choose 2 : ℝ) *
      frobenius ℝ (⋀[ℝ]^2 (TangentSpace I x)) (⋀[ℝ]^2 (TangentSpace I x)) T := by
    exact mul_nonneg (Real.sqrt_nonneg _) (apply_nonneg _ _)
  have hle : |LinearMap.trace ℝ (⋀[ℝ]^2 (TangentSpace I x)) T| ≤
      Real.sqrt ((finrank ℝ E).choose 2 : ℝ) *
        frobenius ℝ (⋀[ℝ]^2 (TangentSpace I x)) (⋀[ℝ]^2 (TangentSpace I x)) T := by
    refine (sq_le_sq₀ (abs_nonneg _) hnonneg).1 ?_
    rwa [sq_abs, mul_pow, Real.sq_sqrt (by positivity)]
  linarith

/-- A quadratic-form lower bound `Rop ≥ α Id` on the curvature endomorphism implies
`n (n - 1) α ≤ Scal`. In dimension three with `α = -1`, this gives `-6 ≤ Scal`. -/
theorem le_scalarCurvature_of_le_curvatureEndomorphism (x : M) {α : ℝ}
    (hα : ∀ z : ⋀[ℝ]^2 (TangentSpace I x),
      α * ‖z‖ ^ 2 ≤ ⟪cov.curvatureEndomorphism hcov x z, z⟫) :
    (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) - 1) * α ≤ cov.scalarCurvature x := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have hdim : finrank ℝ (TangentSpace I x) = finrank ℝ E := rfl
  rw [cov.scalarCurvature_eq_sum x b]
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦
    cov.le_ricciTensor_self_of_le_curvatureEndomorphism hcov x hα (b i)
  refine le_trans ?_ hs
  simp only [b.orthonormal.1, one_pow, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, hdim]
  exact le_of_eq (by ring)

/-- If every eigenvalue of the curvature endomorphism is at least `α`, then `n (n - 1) α ≤ Scal`. -/
theorem le_scalarCurvature_of_le_eigenvalues_curvatureEndomorphism
    (ht : cov.torsion = 0) (x : M) {α : ℝ}
    (hα : ∀ μ : ℝ, (cov.curvatureEndomorphism hcov x).HasEigenvalue μ → α ≤ μ) :
    (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) - 1) * α ≤ cov.scalarCurvature x := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have hdim : finrank ℝ (TangentSpace I x) = finrank ℝ E := rfl
  rw [cov.scalarCurvature_eq_sum x b]
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦
    cov.le_ricciTensor_self_of_le_eigenvalues_curvatureEndomorphism hcov ht x hα (b i)
  refine le_trans ?_ hs
  simp only [b.orthonormal.1, one_pow, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, hdim]
  exact le_of_eq (by ring)

/-- Constant sectional curvature `κ` gives `|Rm|² = 2 n (n - 1) κ²`. -/
theorem HasSectionalCurvatureAt.curvatureTensorNormSq_eq {cov}
    {hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov} [ContMDiffCovariantDerivative cov ∞]
    {x : M} {κ : ℝ} (h : cov.HasSectionalCurvatureAt hcov x κ) (ht : cov.torsion = 0) :
    cov.curvatureTensorNormSq x =
      2 * (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) - 1) * κ ^ 2 := by
  let b := stdOrthonormalBasis ℝ (⋀[ℝ]^2 (TangentSpace I x))
  have hdim : finrank ℝ (TangentSpace I x) = finrank ℝ E := rfl
  have hfin : finrank ℝ (⋀[ℝ]^2 (TangentSpace I x)) = (finrank ℝ E).choose 2 := by
    rw [exteriorPower.finrank_eq, hdim]
  rw [cov.curvatureTensorNormSq_eq_four_mul_sq_frobenius_curvatureEndomorphism hcov x,
    h.curvatureEndomorphism_eq_smul_id ht, sq_frobenius_apply b]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, norm_smul, Real.norm_eq_abs,
    b.orthonormal.1, mul_one, sq_abs, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, hfin]
  have h2 := two_mul_choose_two_eq (finrank ℝ E)
  nlinarith

/-- Constant sectional curvature `κ` gives `|Rm| = √(2 n (n - 1)) |κ|`. -/
theorem HasSectionalCurvatureAt.curvatureTensorNorm_eq {cov}
    {hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov} [ContMDiffCovariantDerivative cov ∞]
    {x : M} {κ : ℝ} (h : cov.HasSectionalCurvatureAt hcov x κ) (ht : cov.torsion = 0) :
    cov.curvatureTensorNorm x =
      Real.sqrt (2 * (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) - 1)) * |κ| := by
  rw [curvatureTensorNorm, h.curvatureTensorNormSq_eq ht, Real.sqrt_mul, Real.sqrt_sq_eq_abs]
  have h2 := two_mul_choose_two_eq (finrank ℝ E)
  nlinarith [Nat.cast_nonneg (α := ℝ) ((finrank ℝ E).choose 2)]

end MetricCompatible

end CovariantDerivative

namespace TauCeti.IsLocalRiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {f : M → N}

/-- A local Riemannian isometry preserves the squared Hilbert–Schmidt norm of the curvature
tensor. -/
theorem curvatureTensorNormSq_map (hf : IsLocalRiemannianIsometry I J f) (x : M) :
    (CovariantDerivative.leviCivitaConnection J N).curvatureTensorNormSq (f x) =
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensorNormSq x := by
  obtain ⟨e, he⟩ := hf.exists_linearIsometryEquiv_eq_mfderiv x
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [(CovariantDerivative.leviCivitaConnection I M).curvatureTensorNormSq_eq_sum x b,
    (CovariantDerivative.leviCivitaConnection J N).curvatureTensorNormSq_eq_sum (f x) (b.map e)]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [OrthonormalBasis.map_apply, he]
  rw [← hf.mfderiv_curvatureTensor x (b i) (b j) (b k), ← he, e.norm_map]

/-- A local Riemannian isometry preserves the Hilbert–Schmidt norm `|Rm|` of the curvature
tensor. -/
theorem curvatureTensorNorm_map (hf : IsLocalRiemannianIsometry I J f) (x : M) :
    (CovariantDerivative.leviCivitaConnection J N).curvatureTensorNorm (f x) =
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensorNorm x := by
  simp only [CovariantDerivative.curvatureTensorNorm, hf.curvatureTensorNormSq_map x]

/-- A local Riemannian isometry preserves quadratic-form lower bounds on the curvature
endomorphism. -/
theorem le_inner_curvatureEndomorphism_iff (hf : IsLocalRiemannianIsometry I J f) (x : M)
    (α : ℝ) :
    (∀ z : ⋀[ℝ]^2 (TangentSpace J (f x)),
        α * ‖z‖ ^ 2 ≤
          ⟪(CovariantDerivative.leviCivitaConnection J N).curvatureEndomorphism
            (CovariantDerivative.isMetricCompatible_leviCivitaConnection J) (f x) z, z⟫) ↔
      (∀ z : ⋀[ℝ]^2 (TangentSpace I x),
        α * ‖z‖ ^ 2 ≤
          ⟪(CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
            (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x z, z⟫) := by
  obtain ⟨e, he⟩ := hf.exists_linearIsometryEquiv_eq_mfderiv x
  let φ : ⋀[ℝ]^2 (TangentSpace I x) ≃ₗ[ℝ] ⋀[ℝ]^2 (TangentSpace J (f x)) :=
    e.toLinearEquiv.exteriorPower 2
  have hinner (a b : ⋀[ℝ]^2 (TangentSpace I x)) : ⟪φ a, φ b⟫ = ⟪a, b⟫ := by
    have heI : e.toLinearIsometry.toLinearMap = e.toLinearEquiv.toLinearMap := by ext v; simp
    simpa only [φ, ← LinearEquiv.coe_toLinearMap, LinearEquiv.exteriorPower_toLinearMap, heI] using
      exteriorPower.inner_map_map e.toLinearIsometry a b
  have hnorm (a : ⋀[ℝ]^2 (TangentSpace I x)) : ‖φ a‖ ^ 2 = ‖a‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hinner]
  have hmap (a : ⋀[ℝ]^2 (TangentSpace I x)) :
      (CovariantDerivative.leviCivitaConnection J N).curvatureEndomorphism
          (CovariantDerivative.isMetricCompatible_leviCivitaConnection J) (f x) (φ a) =
        φ ((CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
          (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x a) := by
    have heL : e.toLinearEquiv.toLinearMap = (mfderiv I J f x).toLinearMap := LinearMap.ext he
    simpa only [φ, ← LinearEquiv.coe_toLinearMap, LinearEquiv.exteriorPower_toLinearMap, heL] using
      (hf.map_curvatureEndomorphism x a).symm
  constructor
  · intro h a
    have ha := h (φ a)
    rwa [hmap, hinner, hnorm] at ha
  · intro h b
    obtain ⟨a, rfl⟩ := φ.surjective b
    rw [hmap, hinner, hnorm]
    exact h a

end TauCeti.IsLocalRiemannianIsometry

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- The squared Hilbert–Schmidt norm `|Rm|²` of the Riemann curvature tensor of a smooth metric
`g` at `x`. -/
def curvatureTensorNormSq (x : M) : ℝ :=
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  (CovariantDerivative.leviCivitaConnection I M).curvatureTensorNormSq x

/-- The Hilbert–Schmidt norm `|Rm|` of the Riemann curvature tensor of a smooth metric `g` at
`x`. -/
def curvatureTensorNorm (x : M) : ℝ :=
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  (CovariantDerivative.leviCivitaConnection I M).curvatureTensorNorm x

/-- The squared curvature tensor norm `|Rm|²` of a smooth metric `g` is nonnegative. -/
theorem curvatureTensorNormSq_nonneg (x : M) : 0 ≤ g.curvatureTensorNormSq x := by
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  exact (CovariantDerivative.leviCivitaConnection I M).curvatureTensorNormSq_nonneg x

/-- The curvature tensor norm `|Rm|` of a smooth metric `g` is nonnegative. -/
theorem curvatureTensorNorm_nonneg (x : M) : 0 ≤ g.curvatureTensorNorm x := by
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  exact (CovariantDerivative.leviCivitaConnection I M).curvatureTensorNorm_nonneg x

/-- The curvature tensor norm equals the square root of the squared norm. -/
theorem curvatureTensorNorm_eq_sqrt (x : M) :
    g.curvatureTensorNorm x = Real.sqrt (g.curvatureTensorNormSq x) :=
  (rfl)

/-- Squaring `g.curvatureTensorNorm x` recovers `g.curvatureTensorNormSq x`. -/
@[simp]
theorem sq_curvatureTensorNorm (x : M) :
    g.curvatureTensorNorm x ^ 2 = g.curvatureTensorNormSq x :=
  Real.sq_sqrt (g.curvatureTensorNormSq_nonneg x)

/-- Under any installed `RiemannianBundle` equal to `g`, `g.curvatureTensorNorm` agrees with the
curvature tensor norm of the Levi-Civita connection. -/
theorem curvatureTensorNorm_eq_curvatureTensorNorm_leviCivitaConnection
    [inst : RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hg : RiemannianBundle.g = g.toRiemannianMetric) (x : M) :
    g.curvatureTensorNorm x =
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensorNorm x := by
  obtain ⟨_⟩ := inst
  subst hg
  rfl

/-- Pointwise lower bound `Rop_g(x) ≥ α • Id` on the curvature operator of a smooth metric `g`:
`α * ‖z‖² ≤ ⟪Rop_g(x) z, z⟫` for every bivector `z : ⋀² T_x M`. -/
def HasCurvatureOperatorLowerBoundAt (x : M) (α : ℝ) : Prop :=
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  ∀ z : ⋀[ℝ]^2 (TangentSpace I x),
    α * ‖z‖ ^ 2 ≤
      ⟪(CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x z, z⟫

/-- Explicit unfolding of `HasCurvatureOperatorLowerBoundAt`. -/
theorem hasCurvatureOperatorLowerBoundAt_iff (x : M) (α : ℝ) :
    g.HasCurvatureOperatorLowerBoundAt x α ↔
      letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
      ∀ z : ⋀[ℝ]^2 (TangentSpace I x),
        α * ‖z‖ ^ 2 ≤
          ⟪(CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
            (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x z, z⟫ :=
  Iff.rfl

/-- Lower bounds on the curvature operator are antitone in the threshold `α`. -/
theorem HasCurvatureOperatorLowerBoundAt.mono {g :
    ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {x : M} {α β : ℝ}
    (h : g.HasCurvatureOperatorLowerBoundAt x β) (hαβ : α ≤ β) :
    g.HasCurvatureOperatorLowerBoundAt x α := by
  rw [hasCurvatureOperatorLowerBoundAt_iff] at h ⊢
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  intro z
  exact (mul_le_mul_of_nonneg_right hαβ (sq_nonneg ‖z‖)).trans (h z)

/-- A pointwise curvature tensor norm bound `|Rm_g(x)| ≤ C` yields the curvature-operator lower
bound `Rop_g(x) ≥ -(C / 2) • Id`. -/
theorem hasCurvatureOperatorLowerBoundAt_of_curvatureTensorNorm_le {x : M} {C : ℝ}
    (hC : g.curvatureTensorNorm x ≤ C) :
    g.HasCurvatureOperatorLowerBoundAt x (-(C / 2)) := by
  rw [hasCurvatureOperatorLowerBoundAt_iff]
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  have _ : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
    Bundle.instIsContMDiffRiemannianBundle g
  intro z
  have h1 := (CovariantDerivative.leviCivitaConnection I M)
    |>.neg_half_curvatureTensorNorm_le_inner_curvatureEndomorphism
      (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x z
  have h2 : (CovariantDerivative.leviCivitaConnection I M).curvatureTensorNorm x ≤ C := by
    rw [← g.curvatureTensorNorm_eq_curvatureTensorNorm_leviCivitaConnection rfl x]
    exact hC
  nlinarith [sq_nonneg ‖z‖]

/-- On a manifold of dimension at most one, the curvature tensor norm of every smooth metric
vanishes identically. -/
theorem curvatureTensorNorm_eq_zero_of_finrank_le_one (hdim : finrank ℝ E ≤ 1) (x : M) :
    g.curvatureTensorNorm x = 0 := by
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  exact (CovariantDerivative.leviCivitaConnection I M)
    |>.curvatureTensorNorm_eq_zero_of_finrank_le_one hdim x

/-- Constant-curvature metric `g` with parameter `κ` has `|Rm| = √(2 n (n - 1)) |κ|`. -/
theorem IsConstantCurvatureTensor.curvatureTensorNorm_eq {g :
    ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {κ : ℝ}
    (hg : g.IsConstantCurvatureTensor κ) (x : M) :
    g.curvatureTensorNorm x =
      Real.sqrt (2 * (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) - 1)) * |κ| := by
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  have hsec := (CovariantDerivative.leviCivitaConnection I M)
    |>.hasConstantSectionalCurvature_of_curvatureTensor_eq_smul_inner_sub
      (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) κ
      (g.isConstantCurvatureTensor_iff κ |>.1 hg)
  have hat := (CovariantDerivative.hasConstantSectionalCurvature_iff
    (cov := CovariantDerivative.leviCivitaConnection I M)
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) κ).1 hsec x
  exact hat.curvatureTensorNorm_eq (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I)

/-- On a compact set `K`, `|Rm|` of a smooth metric `g` is uniformly bounded. -/
theorem exists_curvatureTensorNorm_le_of_isCompact {K : Set M} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, g.curvatureTensorNorm x ≤ C := by
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun y : M ↦ TangentSpace I y) :=
    Bundle.instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  exact (CovariantDerivative.leviCivitaConnection I M).exists_curvatureTensorNorm_le_of_isCompact hK

/-- On a compact manifold, `|Rm|` of a smooth metric `g` is globally bounded. -/
theorem exists_curvatureTensorNorm_le [CompactSpace M] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M, g.curvatureTensorNorm x ≤ C := by
  obtain ⟨C, hC0, hC⟩ := g.exists_curvatureTensorNorm_le_of_isCompact isCompact_univ
  exact ⟨C, hC0, fun x ↦ hC x (Set.mem_univ x)⟩

section Scaling

variable {c : ℝ} (hc : 0 < c)

omit [T2Space M] in
/-- Multiplying a smooth metric by a positive constant `c` multiplies the inner product on
`⋀² (TangentSpace I x)` by `c²`. -/
theorem inner_exteriorPower_two_rescale_const (x : M) (a b : ⋀[ℝ]^2 (TangentSpace I x)) :
    (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      ⟪a, b⟫) =
    c ^ 2 * (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      ⟪a, b⟫) := by
  let B₁ : ⋀[ℝ]^2 (TangentSpace I x) →ₗ[ℝ] ⋀[ℝ]^2 (TangentSpace I x) →ₗ[ℝ] ℝ :=
    letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
      ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
    innerₗ (⋀[ℝ]^2 (TangentSpace I x))
  let B₂ : ⋀[ℝ]^2 (TangentSpace I x) →ₗ[ℝ] ⋀[ℝ]^2 (TangentSpace I x) →ₗ[ℝ] ℝ :=
    letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    innerₗ (⋀[ℝ]^2 (TangentSpace I x))
  suffices h : B₁ a b = c ^ 2 * B₂ a b by exact h
  have key (u v : Fin 2 → TangentSpace I x) :
      B₁ (exteriorPower.ιMulti ℝ 2 u) (exteriorPower.ιMulti ℝ 2 v) =
        c ^ 2 * B₂ (exteriorPower.ιMulti ℝ 2 u) (exteriorPower.ιMulti ℝ 2 v) := by
    have h1 : B₁ (exteriorPower.ιMulti ℝ 2 u) (exteriorPower.ιMulti ℝ 2 v) =
        (Matrix.of fun i j : Fin 2 ↦ c * g.inner x (u j) (v i)).det := by
      let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
      change ⟪exteriorPower.ιMulti ℝ 2 u, exteriorPower.ιMulti ℝ 2 v⟫ = _
      simp [exteriorPower.inner_ιMulti_ιMulti, inner_riemannianBundle, rescale_inner]
    have h2 : B₂ (exteriorPower.ιMulti ℝ 2 u) (exteriorPower.ιMulti ℝ 2 v) =
        (Matrix.of fun i j : Fin 2 ↦ g.inner x (u j) (v i)).det := by
      let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
      change ⟪exteriorPower.ιMulti ℝ 2 u, exteriorPower.ιMulti ℝ 2 v⟫ = _
      simp [exteriorPower.inner_ιMulti_ιMulti, inner_riemannianBundle]
    rw [h1, h2, Matrix.det_fin_two, Matrix.det_fin_two]
    simp only [Matrix.of_apply]
    ring
  have ha : a ∈ Submodule.span ℝ (Set.range (exteriorPower.ιMulti ℝ 2)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨u, rfl⟩ := ha
    have hb : b ∈ Submodule.span ℝ (Set.range (exteriorPower.ιMulti ℝ 2)) := by
      rw [exteriorPower.ιMulti_span]; trivial
    induction hb using Submodule.span_induction with
    | mem b hb => obtain ⟨v, rfl⟩ := hb; exact key u v
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, mul_add, hy, hz]
    | smul r y _ hy => simp only [map_smul, smul_eq_mul, hy]; ring
  | zero => simp
  | add y z _ _ hy hz => simp only [map_add, LinearMap.add_apply, mul_add, hy, hz]
  | smul r y _ hy => simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hy]; ring

/-- **Scaling of the curvature endomorphism.** Multiplying a smooth metric by a positive constant
`c` scales the curvature endomorphism on `⋀² (Tₓ M)` by `c⁻¹`. -/
theorem curvatureEndomorphism_leviCivitaConnection_rescale_const (x : M) :
    (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x) =
    c⁻¹ • (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x) := by
  let A : Module.End ℝ (⋀[ℝ]^2 (TangentSpace I x)) :=
    letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    (CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
      (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
    ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
  rw [CovariantDerivative.curvatureEndomorphism_eq_iff]
  intro u v
  rw [LinearMap.smul_apply, real_inner_smul_left,
    g.inner_exteriorPower_two_rescale_const hc x (A (exteriorPower.ιMulti ℝ 2 u))
      (exteriorPower.ιMulti ℝ 2 v)]
  have hA : (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      ⟪A (exteriorPower.ιMulti ℝ 2 u), exteriorPower.ιMulti ℝ 2 v⟫) =
      g.inner x ((letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x)
          (u 0) (u 1) (v 1)) (v 0) := by
    let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    exact (CovariantDerivative.leviCivitaConnection I M).inner_curvatureEndomorphism_ιMulti
      (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x u v
  rw [hA, inner_riemannianBundle, rescale_inner,
    g.curvatureTensor_leviCivitaConnection_rescale_const hc x]
  field_simp [hc.ne']

/-- Multiplying a smooth metric by `c > 0` scales the eigenvalues of the curvature endomorphism
by `c⁻¹`: `μ` is an eigenvalue for `c g` iff `c * μ` is an eigenvalue for `g`. -/
@[simp]
theorem hasEigenvalue_curvatureEndomorphism_rescale_const_iff (x : M) (μ : ℝ) :
    (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      ((CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x).HasEigenvalue μ) ↔
    (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      ((CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x).HasEigenvalue
        (c * μ)) := by
  rw [g.curvatureEndomorphism_leviCivitaConnection_rescale_const hc x]
  set T : Module.End ℝ (⋀[ℝ]^2 (TangentSpace I x)) :=
    letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    (CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
      (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x
  constructor
  · intro hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv.2⟩
    rw [Module.End.mem_eigenspace_iff]
    have h1 : c⁻¹ • T v = μ • v := by simpa [LinearMap.smul_apply] using hv.apply_eq_smul
    have h2 := congrArg (c • ·) h1
    simpa [smul_smul, hc.ne'] using h2
  · intro hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv.2⟩
    rw [Module.End.mem_eigenspace_iff, LinearMap.smul_apply]
    have h1 : T v = (c * μ) • v := hv.apply_eq_smul
    have h2 := congrArg (c⁻¹ • ·) h1
    simpa [smul_smul, hc.ne'] using h2

/-- **Scaling of quadratic-form lower bounds on `Rop`.** For `c > 0`, `Rop_{c g} ≥ α Id` iff
`Rop_g ≥ (c * α) Id`. -/
theorem le_inner_curvatureEndomorphism_rescale_const_iff (x : M) (α : ℝ) :
    (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      ∀ z : ⋀[ℝ]^2 (TangentSpace I x),
        α * ‖z‖ ^ 2 ≤
          ⟪(CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
            (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x z, z⟫) ↔
    (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      ∀ z : ⋀[ℝ]^2 (TangentSpace I x),
        (c * α) * ‖z‖ ^ 2 ≤
          ⟪(CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
            (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x z, z⟫) := by
  refine forall_congr' fun z ↦ ?_
  have hnorm1 : (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      ‖z‖ ^ 2) = (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      ⟪z, z⟫) := by
    let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
      ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
    exact (real_inner_self_eq_norm_sq z).symm
  have hnorm2 : (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      ‖z‖ ^ 2) = (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      ⟪z, z⟫) := by
    let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    exact (real_inner_self_eq_norm_sq z).symm
  have hnorm : (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      ‖z‖ ^ 2) =
    c ^ 2 * (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      ‖z‖ ^ 2) := by
    rw [hnorm1, hnorm2]
    exact g.inner_exteriorPower_two_rescale_const hc x z z
  set w : ⋀[ℝ]^2 (TangentSpace I x) :=
    (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x) z
  have hrop : (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      ⟪(CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x z, z⟫) =
    c * (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      ⟪w, z⟫) := by
    rw [g.curvatureEndomorphism_leviCivitaConnection_rescale_const hc x]
    have hsm : (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      ⟪c⁻¹ • w, z⟫) = c⁻¹ * (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      ⟪w, z⟫) := by
      let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
      exact real_inner_smul_left w z c⁻¹
    change (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      ⟪c⁻¹ • w, z⟫) = _
    rw [hsm, g.inner_exteriorPower_two_rescale_const hc x w z]
    field_simp [hc.ne']
  rw [hnorm, hrop]
  constructor
  · intro h
    have h' : c * (c * α * (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨g.toRiemannianMetric⟩; ‖z‖ ^ 2)) ≤
        c * (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
          ⟨g.toRiemannianMetric⟩; ⟪w, z⟫) := by
      linarith
    exact le_of_mul_le_mul_left h' hc
  · intro h
    have := mul_le_mul_of_nonneg_left h hc.le
    linarith

/-- **Scaling of `|Rm|²`:** multiplying a smooth metric by `c > 0` scales `|Rm|²` by `c⁻²`. -/
@[simp]
theorem curvatureTensorNormSq_rescale_const (x : M) :
    (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).curvatureTensorNormSq x =
      c⁻¹ ^ 2 * g.curvatureTensorNormSq x := by
  let b : (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
      OrthonormalBasis (Fin (finrank ℝ (TangentSpace I x))) ℝ (TangentSpace I x)) :=
    letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    stdOrthonormalBasis ℝ (TangentSpace I x)
  obtain ⟨b', hb'⟩ := g.exists_orthonormalBasis_rescale (f := fun _ ↦ c) contMDiff_const
    (fun _ ↦ hc) b
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  rw [curvatureTensorNormSq, curvatureTensorNormSq]
  have h1 := (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
      ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
    (CovariantDerivative.leviCivitaConnection I M).curvatureTensorNormSq_eq_sum x b')
  have h2 := (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
    (CovariantDerivative.leviCivitaConnection I M).curvatureTensorNormSq_eq_sum x b)
  rw [h1, h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hnorm (v : TangentSpace I x) :
      (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
          ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
        ‖v‖ ^ 2) =
      c * (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
        ‖v‖ ^ 2) := by
    have hn1 : (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
          ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
        ‖v‖ ^ 2) = c * g.inner x v v := by
      let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩
      rw [← real_inner_self_eq_norm_sq, inner_riemannianBundle, rescale_inner]
    have hn2 : (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩;
        ‖v‖ ^ 2) = g.inner x v v := by
      let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
      rw [← real_inner_self_eq_norm_sq, inner_riemannianBundle]
    rw [hn1, hn2]
  simp only [hb', g.curvatureTensor_leviCivitaConnection_rescale_const hc x, map_smul,
    LinearMap.smul_apply]
  rw [hnorm]
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hsqrt), mul_pow, inv_pow]
  field_simp [hc.ne', hsqrt.ne']
  rw [show Real.sqrt c ^ 6 = (Real.sqrt c ^ 2) ^ 3 by ring, hsq]

/-- **Scaling of `|Rm|`:** multiplying a smooth metric by `c > 0` scales `|Rm|` by `c⁻¹`. -/
@[simp]
theorem curvatureTensorNorm_rescale_const (x : M) :
    (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).curvatureTensorNorm x =
      c⁻¹ * g.curvatureTensorNorm x := by
  rw [curvatureTensorNorm_eq_sqrt, curvatureTensorNorm_eq_sqrt,
    g.curvatureTensorNormSq_rescale_const hc x,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.2 hc.le)]

/-- Constant positive rescaling scales pointwise curvature-operator lower bounds by `c⁻¹`. -/
@[simp]
theorem hasCurvatureOperatorLowerBoundAt_rescale_const_iff (x : M) (α : ℝ) :
    (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).HasCurvatureOperatorLowerBoundAt x α ↔
      g.HasCurvatureOperatorLowerBoundAt x (c * α) :=
  g.le_inner_curvatureEndomorphism_rescale_const_iff hc x α

end Scaling

section Pullback

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- The curvature tensor norm of a pullback along a local diffeomorphism `f` is `|Rm_g| ∘ f`. -/
theorem curvatureTensorNorm_pullback_of_isInvertible
    (g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)) {f : M → N}
    (hf : ContMDiff I J (∞ + 1) f) (hinv : ∀ x, (mfderiv I J f x).IsInvertible) (x : M) :
    (g.pullback f hf fun x ↦ (hinv x).injective).curvatureTensorNorm x =
      g.curvatureTensorNorm (f x) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.pullback f hf fun x ↦ (hinv x).injective).toRiemannianMetric⟩
  let _ : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
  exact ((isLocalRiemannianIsometry_pullback_of_isInvertible g hf hinv)
    |>.curvatureTensorNorm_map x).symm

/-- Along a diffeomorphism `Φ`, `|Rm_{Φ^* g}| = |Rm_g| ∘ Φ`. -/
@[simp]
theorem curvatureTensorNorm_pullback
    (g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y))
    (Φ : M ≃ₘ^∞⟮I, J⟯ N) (hf : ContMDiff I J (∞ + 1) Φ)
    (hinj : ∀ x, Function.Injective (mfderiv I J Φ x)) (x : M) :
    (g.pullback Φ hf hinj).curvatureTensorNorm x = g.curvatureTensorNorm (Φ x) :=
  curvatureTensorNorm_pullback_of_isInvertible g hf (fun _ ↦ Φ.isInvertible_mfderiv (by simp)) x

/-- Pulling back along a local diffeomorphism preserves quadratic-form lower bounds on the
curvature endomorphism. -/
theorem le_inner_curvatureEndomorphism_pullback_of_isInvertible_iff
    (g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)) {f : M → N}
    (hf : ContMDiff I J (∞ + 1) f) (hinv : ∀ x, (mfderiv I J f x).IsInvertible)
    (x : M) (α : ℝ) :
    (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(g.pullback f hf fun y ↦ (hinv y).injective).toRiemannianMetric⟩;
      ∀ z : ⋀[ℝ]^2 (TangentSpace I x),
        α * ‖z‖ ^ 2 ≤
          ⟪(CovariantDerivative.leviCivitaConnection I M).curvatureEndomorphism
            (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x z, z⟫) ↔
    (letI : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩;
      ∀ z : ⋀[ℝ]^2 (TangentSpace J (f x)),
        α * ‖z‖ ^ 2 ≤
          ⟪(CovariantDerivative.leviCivitaConnection J N).curvatureEndomorphism
            (CovariantDerivative.isMetricCompatible_leviCivitaConnection J) (f x) z, z⟫) := by
  let _ : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
    ⟨(g.pullback f hf fun y ↦ (hinv y).injective).toRiemannianMetric⟩
  let _ : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
  exact ((isLocalRiemannianIsometry_pullback_of_isInvertible g hf hinv)
    |>.le_inner_curvatureEndomorphism_iff x α).symm

/-- Pulling back along a local diffeomorphism preserves `HasCurvatureOperatorLowerBoundAt`. -/
theorem hasCurvatureOperatorLowerBoundAt_pullback_of_isInvertible_iff
    (g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)) {f : M → N}
    (hf : ContMDiff I J (∞ + 1) f) (hinv : ∀ x, (mfderiv I J f x).IsInvertible)
    (x : M) (α : ℝ) :
    (g.pullback f hf fun y ↦ (hinv y).injective).HasCurvatureOperatorLowerBoundAt x α ↔
      g.HasCurvatureOperatorLowerBoundAt (f x) α :=
  le_inner_curvatureEndomorphism_pullback_of_isInvertible_iff g hf hinv x α

/-- Along a diffeomorphism `Φ`, `HasCurvatureOperatorLowerBoundAt` pulls back pointwise. -/
@[simp]
theorem hasCurvatureOperatorLowerBoundAt_pullback_iff
    (g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y))
    (Φ : M ≃ₘ^∞⟮I, J⟯ N) (hf : ContMDiff I J (∞ + 1) Φ)
    (hinj : ∀ x, Function.Injective (mfderiv I J Φ x)) (x : M) (α : ℝ) :
    (g.pullback Φ hf hinj).HasCurvatureOperatorLowerBoundAt x α ↔
      g.HasCurvatureOperatorLowerBoundAt (Φ x) α :=
  hasCurvatureOperatorLowerBoundAt_pullback_of_isInvertible_iff g hf
    (fun _ ↦ Φ.isInvertible_mfderiv (by simp)) x α

end Pullback

section Product

open scoped TauCeti

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace G N] [IsManifold J ∞ N]

/-- The squared curvature tensor norm of a Riemannian product is the sum of the squared curvature
tensor norms of its factors: `|Rm_{M × N}|²(x, y) = |Rm_M|²(x) + |Rm_N|²(y)`. -/
theorem _root_.TauCeti.Manifold.curvatureTensorNormSq_leviCivitaConnection_prod
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
    [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
    (p : M × N) :
    (CovariantDerivative.leviCivitaConnection (I.prod J) (M × N)).curvatureTensorNormSq p =
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensorNormSq p.1 +
        (CovariantDerivative.leviCivitaConnection J N).curvatureTensorNormSq p.2 := by
  let b₁ := stdOrthonormalBasis ℝ (TangentSpace I p.1)
  let b₂ := stdOrthonormalBasis ℝ (TangentSpace J p.2)
  let e := TauCeti.Manifold.tangentSpaceProdLinearIsometryEquiv (I := I) (J := J) p
  let b := (b₁.prod b₂).map e.symm
  rw [(CovariantDerivative.leviCivitaConnection (I.prod J) (M × N)).curvatureTensorNormSq_eq_sum
      p b,
    (CovariantDerivative.leviCivitaConnection I M).curvatureTensorNormSq_eq_sum p.1 b₁,
    (CovariantDerivative.leviCivitaConnection J N).curvatureTensorNormSq_eq_sum p.2 b₂]
  have hterm : ∀ i j k,
      ‖(CovariantDerivative.leviCivitaConnection (I.prod J) (M × N)).curvatureTensor p
          (b i) (b j) (b k)‖ ^ 2 =
        ‖(CovariantDerivative.leviCivitaConnection I M).curvatureTensor p.1
            (TauCeti.Manifold.tangentSpaceProdEquiv p (b i)).1
            (TauCeti.Manifold.tangentSpaceProdEquiv p (b j)).1
            (TauCeti.Manifold.tangentSpaceProdEquiv p (b k)).1‖ ^ 2 +
          ‖(CovariantDerivative.leviCivitaConnection J N).curvatureTensor p.2
            (TauCeti.Manifold.tangentSpaceProdEquiv p (b i)).2
            (TauCeti.Manifold.tangentSpaceProdEquiv p (b j)).2
            (TauCeti.Manifold.tangentSpaceProdEquiv p (b k)).2‖ ^ 2 := fun i j k ↦ by
    rw [← e.norm_map,
      TauCeti.Manifold.tangentSpaceProdLinearIsometryEquiv_apply,
      TauCeti.Manifold.tangentSpaceProdEquiv_curvatureTensor_leviCivitaConnection_prod,
      WithLp.prod_norm_sq_eq_of_L2]
    rfl
  simp_rw [hterm]
  simp only [b, e, OrthonormalBasis.map_apply,
    TauCeti.Manifold.tangentSpaceProdLinearIsometryEquiv_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply, Fintype.sum_sum_type, OrthonormalBasis.prod_apply,
    Sum.elim_inl, Sum.elim_inr, Function.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
    map_zero, LinearMap.zero_apply, norm_zero, zero_pow two_ne_zero, add_zero, zero_add,
    Finset.sum_const_zero]

/-- **Squared curvature tensor norm of a product metric:**
`|Rm_{g₁ × g₂}|²(x, y) = |Rm_{g₁}|²(x) + |Rm_{g₂}|²(y)`. -/
@[simp]
theorem curvatureTensorNormSq_prodTangentSpace
    (g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (g₂ : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)) (p : M × N) :
    (g₁.prodTangentSpace g₂).curvatureTensorNormSq p =
      g₁.curvatureTensorNormSq p.1 + g₂.curvatureTensorNormSq p.2 := by
  rw [curvatureTensorNormSq, curvatureTensorNormSq, curvatureTensorNormSq]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩
  let _ : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g₂.toRiemannianMetric⟩
  have hg : (⟨(g₁.prodTangentSpace g₂).toRiemannianMetric⟩ :
      RiemannianBundle (fun p : M × N ↦ TangentSpace (I.prod J) p)) =
      TauCeti.Manifold.instRiemannianBundleProd := by
    rw [prodTangentSpace_toRiemannianMetric]
    exact congrArg RiemannianBundle.mk TauCeti.Manifold.riemannianBundleProd_g.symm
  convert TauCeti.Manifold.curvatureTensorNormSq_leviCivitaConnection_prod (I := I) (J := J) p
    using 3

/-- **Curvature tensor norm of a product metric:**
`|Rm_{g₁ × g₂}|(x, y) = √(|Rm_{g₁}|²(x) + |Rm_{g₂}|²(y))`. -/
theorem curvatureTensorNorm_prodTangentSpace
    (g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (g₂ : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)) (p : M × N) :
    (g₁.prodTangentSpace g₂).curvatureTensorNorm p =
      Real.sqrt (g₁.curvatureTensorNormSq p.1 + g₂.curvatureTensorNormSq p.2) := by
  rw [curvatureTensorNorm_eq_sqrt, curvatureTensorNormSq_prodTangentSpace]

/-- The product of two flat metrics is flat: if `|Rm_{g₁}| = 0` and `|Rm_{g₂}| = 0`, then
`|Rm_{g₁ × g₂}| = 0`. -/
theorem curvatureTensorNorm_prodTangentSpace_eq_zero
    (g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (g₂ : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)) {p : M × N}
    (h₁ : g₁.curvatureTensorNorm p.1 = 0) (h₂ : g₂.curvatureTensorNorm p.2 = 0) :
    (g₁.prodTangentSpace g₂).curvatureTensorNorm p = 0 := by
  rw [curvatureTensorNorm_prodTangentSpace, ← g₁.sq_curvatureTensorNorm,
    ← g₂.sq_curvatureTensorNorm, h₁, h₂]
  simp

end Product

end Bundle.ContMDiffRiemannianMetric

end
