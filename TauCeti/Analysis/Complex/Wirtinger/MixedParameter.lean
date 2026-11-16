/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Compactness.LocallyCompact
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Analysis.Complex.Runge.FiniteRankOperator
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import TauCeti.Analysis.Complex.Wirtinger.Potential
import TauCeti.Analysis.Normed.Module.Exhaustion

/-!
# Global solutions of the planar `\bar∂`-equation with smooth and holomorphic parameters

Let `P` be a finite-dimensional real normed space, `Q` a finite-dimensional complex normed space,
`F` a complex Banach space, and let `U_P ⊆ P`, `U_Q ⊆ Q` and `Ω ⊆ ℂ` be open sets, without any
connectivity, boundedness or product-disc restriction on `U_Q` or `Ω`. Given a map
`f : (P × Q) × ℂ → F` that is jointly `C^∞` on `(U_P ×ˢ U_Q) ×ˢ Ω` and holomorphic in `q ∈ U_Q` for
every `(p, z) ∈ U_P ×ˢ Ω`, this file constructs a jointly `C^∞` map `u : (P × Q) × ℂ → F` on
`(U_P ×ˢ U_Q) ×ˢ Ω`, still holomorphic in `q ∈ U_Q`, that solves the inhomogeneous Cauchy–Riemann
equation

`conjWirtingerDeriv (fun w ↦ u ((p, q), w)) z 1 = f ((p, q), z)`

everywhere on `(U_P ×ˢ U_Q) ×ˢ Ω`
(`TauCeti.exists_contDiffOn_differentiableOn_conjWirtingerDeriv_apply_one_eq`). Specializing one or
both parameter spaces to `{0}` gives the global `\bar∂`-lemma on any open subset of `ℂ`
(`IsOpen.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq`), the smooth-parameter solver on
`U_P ×ˢ Ω`, and the holomorphic-parameter solver on `U_Q ×ˢ Ω`.

## Mathematical overview

1. **Slicewise holomorphy and total derivative bounds.** If `H : R × ℂ → F` is `C^∞` on `s ×ˢ V`
   and holomorphic in the second variable on `V`, symmetry of second Fréchet derivatives commutes
   the conjugate Wirtinger derivative in `z` past `fderiv ℝ` in the parameter `r ∈ s`, showing that
   every iterated parameter derivative `z ↦ iteratedFDeriv ℝ m (fun r ↦ H (r, z)) r` remains
   holomorphic on `V` (`TauCeti.differentiableOn_iteratedFDeriv_prod_left`). Cauchy's estimate on
   circles in `V` then controls `‖iteratedFDeriv ℝ k H (r₀, z₀)‖` purely in terms of the parameter
   derivatives `‖iteratedFDeriv ℝ m (fun r ↦ H (r, z)) r₀‖` (`m ≤ k`) on `V`, with explicit
   constant `(1 + r⁻¹) ^ k` when `ball z₀ ((2k + 1) r) ⊆ V`
   (`TauCeti.norm_iteratedFDeriv_prod_le_of_differentiableOn_snd`).
2. **Filled exhaustion and finite-rank Runge Mittag-Leffler correction.** Exhaust `Ω` by compact
   sets `C k ⊆ interior (C (k + 1))` filled in `Ω` (`IsOpen.exists_isFilledIn_compact_exhaustion`)
   and `U_P ×ˢ U_Q` by compact sets `B k ⊆ interior (B (k + 1))`. On each `C (k + 1)`, the
   cut-off Cauchy transform
   (`TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eventually_eq_with_holomorphic_param`)
   produces a local potential `h k`, jointly `C^∞` on `(U_P ×ˢ U_Q) ×ˢ univ` and holomorphic in
   `U_Q`, with `\bar∂_z (h k) = f` near `C (k + 1)`. Consecutive differences
   `d k = h (k + 1) - h k` are therefore holomorphic in `z` on an open neighbourhood of `C (k + 1)`.
   Applying the universe-polymorphic finite-rank Runge operator
   (`TauCeti.IsFilledIn.exists_norm_sub_sum_mul_smul_le`) to `d k` with tolerance chosen against
   the supremum of parameter derivatives through order `k` on `B k` times a compact collar produces
   a correction `P k`, holomorphic in `z` on all of `Ω` and in `q` on `U_Q`, such that all total
   derivatives of `d k - P k` through order `k` have norm at most `2⁻ᵏ` on `B k ×ˢ C k`.
   The telescoping series `h 0 + ∑' k, (d k - P k)` converges in `C^∞` on `(U_P ×ˢ U_Q) ×ˢ Ω`,
   remains holomorphic in `U_Q` by uniform convergence on compacta, and solves `\bar∂_z u = f`.

## Main results

* `TauCeti.differentiableOn_fderiv_prod_left` and
  `TauCeti.differentiableOn_iteratedFDeriv_prod_left`: first and iterated parameter derivatives of
  a smooth family holomorphic in `z` remain holomorphic in `z`.
* `TauCeti.norm_iteratedFDeriv_prod_le_of_differentiableOn_snd`: explicit Cauchy bound on total
  Fréchet derivatives from parameter derivatives alone.
* `TauCeti.exists_contDiffOn_differentiableOn_conjWirtingerDeriv_apply_one_eq`: global `\bar∂`
  solver on `(U_P ×ˢ U_Q) ×ˢ Ω` preserving smooth dependence on `P` and holomorphic dependence on
  `Q`.
* `IsOpen.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq`: parameterless global `\bar∂` solver
  on any open `Ω ⊆ ℂ`, together with the smooth-parameter and holomorphic-parameter specializations
  `TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_with_param` and
  `TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_with_holomorphic_param`.

## References

* A. Rainer, *Advanced Complex Analysis*, lecture notes, Theorem 11.1 and Theorem 12.2.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.2.2 and Theorem 1.4.4.
* F. Trèves, *Hypo-Analytic Structures: Local Theory*, Princeton University Press, 1992.
-/

public noncomputable section

open Complex Filter Function Metric Set
open scoped Real Topology ContDiff

namespace TauCeti

/-! ### Total Fréchet derivatives of smooth families holomorphic in the plane variable -/

section ParameterDerivatives

universe u v

/-- Pointwise evaluation at `u : R` as a continuous `ℂ`-linear map `(R →L[ℝ] F) →L[ℂ] F`. -/
private def evalCLM {R F : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (u : R) : (R →L[ℝ] F) →L[ℂ] F :=
  LinearMap.mkContinuous
    { toFun L := L u
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    ‖u‖ fun L ↦ by simpa [mul_comm] using L.le_opNorm u

@[simp]
private theorem evalCLM_apply {R F : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (u : R) (L : R →L[ℝ] F) :
    evalCLM u L = L u := rfl

/-- Currying on the right as a continuous `ℂ`-linear equivalence between real multilinear maps into
a complex normed space `F`. -/
private def curryRightComplexCLE {R F : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (m : ℕ) :
    (R [×(m + 1)]→L[ℝ] F) ≃L[ℂ] (R [×m]→L[ℝ] (R →L[ℝ] F)) :=
  LinearIsometryEquiv.toContinuousLinearEquiv
    ({ toFun := continuousMultilinearCurryRightEquiv' ℝ m R F
       invFun := (continuousMultilinearCurryRightEquiv' ℝ m R F).symm
       left_inv := (continuousMultilinearCurryRightEquiv' ℝ m R F).left_inv
       right_inv := (continuousMultilinearCurryRightEquiv' ℝ m R F).right_inv
       map_add' _ _ := map_add (continuousMultilinearCurryRightEquiv' ℝ m R F) _ _
       map_smul' _ _ := by
         refine ContinuousMultilinearMap.ext fun v ↦ ContinuousLinearMap.ext fun u ↦ rfl
       norm_map' := (continuousMultilinearCurryRightEquiv' ℝ m R F).norm_map } :
      (R [×(m + 1)]→L[ℝ] F) ≃ₗᵢ[ℂ] (R [×m]→L[ℝ] (R →L[ℝ] F)))

@[simp]
private theorem curryRightComplexCLE_symm_apply {R F : Type*} [NormedAddCommGroup R]
    [NormedSpace ℝ R] [NormedAddCommGroup F] [NormedSpace ℂ F] (m : ℕ)
    (L : R [×m]→L[ℝ] (R →L[ℝ] F)) :
    (curryRightComplexCLE (R := R) (F := F) m).symm L =
      (continuousMultilinearCurryRightEquiv' ℝ m R F).symm L := rfl

/-- Zero-order currying as a continuous `ℂ`-linear equivalence `F ≃L[ℂ] (R [×0]→L[ℝ] F)`. -/
private def uncurryFin0ComplexCLE {R F : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    [NormedAddCommGroup F] [NormedSpace ℂ F] :
    F ≃L[ℂ] (R [×0]→L[ℝ] F) :=
  LinearIsometryEquiv.toContinuousLinearEquiv
    ({ toFun := (continuousMultilinearCurryFin0 ℝ R F).symm
       invFun := continuousMultilinearCurryFin0 ℝ R F
       left_inv := (continuousMultilinearCurryFin0 ℝ R F).right_inv
       right_inv := (continuousMultilinearCurryFin0 ℝ R F).left_inv
       map_add' _ _ := map_add (continuousMultilinearCurryFin0 ℝ R F).symm _ _
       map_smul' _ _ := by
         refine ContinuousMultilinearMap.ext fun v ↦ rfl
       norm_map' := (continuousMultilinearCurryFin0 ℝ R F).symm.norm_map } :
      F ≃ₗᵢ[ℂ] (R [×0]→L[ℝ] F))

@[simp]
private theorem uncurryFin0ComplexCLE_apply {R F : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (y : F) :
    uncurryFin0ComplexCLE (R := R) (F := F) y = (continuousMultilinearCurryFin0 ℝ R F).symm y := rfl

/-- Universe-lifting isometric `ℂ`-linear embedding `F →ₗᵢ[ℂ] ((R × ℝ) →L[ℝ] F)` sending `y` to
`(r, t) ↦ t • y`, landing in `Type (max u v)` so induction on `F` closed under `R →L[ℝ] ·` stays in
a single universe. -/
private def liftLI (R : Type u) [NormedAddCommGroup R] [NormedSpace ℝ R]
    (F : Type v) [NormedAddCommGroup F] [NormedSpace ℂ F] :
    F →ₗᵢ[ℂ] ((R × ℝ) →L[ℝ] F) where
  toFun y := (ContinuousLinearMap.toSpanSingleton ℝ y).comp (ContinuousLinearMap.snd ℝ R ℝ)
  map_add' y₁ y₂ := ContinuousLinearMap.ext fun ⟨_, t⟩ ↦ smul_add t y₁ y₂
  map_smul' c y := ContinuousLinearMap.ext fun ⟨_, t⟩ ↦ smul_comm t c y
  norm_map' y := by
    refine le_antisymm ?_ ?_
    · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg y) fun x ↦ ?_
      -- Unfold the underlying linear map evaluation to `x.2 • y`.
      change ‖x.2 • y‖ ≤ ‖y‖ * ‖x‖
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_snd_le x) (norm_nonneg y)
    · have h1 := ((ContinuousLinearMap.toSpanSingleton ℝ y).comp
        (ContinuousLinearMap.snd ℝ R ℝ)).le_opNorm ((0 : R), (1 : ℝ))
      have hnorm01 : ‖((0 : R), (1 : ℝ))‖ = 1 := by
        rw [Prod.norm_mk, norm_zero, norm_one, max_eq_right zero_le_one]
      simpa [hnorm01] using h1

/-- Continuous `ℂ`-linear postcomposition of `R [×m]→L[ℝ] ((R × ℝ) →L[ℝ] F)` with evaluation at
`(0, 1)`, retracting `liftLI`. -/
private def unliftMultilinearCLM (R : Type u) [NormedAddCommGroup R] [NormedSpace ℝ R]
    (F : Type v) [NormedAddCommGroup F] [NormedSpace ℂ F] (m : ℕ) :
    (R [×m]→L[ℝ] ((R × ℝ) →L[ℝ] F)) →L[ℂ] (R [×m]→L[ℝ] F) :=
  let ev01 : ((R × ℝ) →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F ((0 : R), (1 : ℝ))
  LinearMap.mkContinuous
    ({ toFun L := ev01.compContinuousMultilinearMap L
       map_add' _ _ := rfl
       map_smul' _ _ := ContinuousMultilinearMap.ext fun _ ↦ rfl } :
      (R [×m]→L[ℝ] ((R × ℝ) →L[ℝ] F)) →ₗ[ℂ] (R [×m]→L[ℝ] F))
    ‖ev01‖ fun L ↦ ev01.norm_compContinuousMultilinearMap_le L

@[simp]
private theorem unliftMultilinearCLM_apply {R : Type u} [NormedAddCommGroup R] [NormedSpace ℝ R]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F] (m : ℕ)
    (L : R [×m]→L[ℝ] ((R × ℝ) →L[ℝ] F)) (w : Fin m → R) :
    unliftMultilinearCLM R F m L w = L w ((0 : R), (1 : ℝ)) := rfl

/-- Precomposition with `Prod.fst` as a norm-nonincreasing continuous `ℝ`-linear map. -/
private def precompFstCLM (R : Type*) [NormedAddCommGroup R] [NormedSpace ℝ R]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (R →L[ℝ] F) →L[ℝ] (R × ℂ →L[ℝ] F) :=
  LinearMap.mkContinuous
    ({ toFun A := A.comp (ContinuousLinearMap.fst ℝ R ℂ)
       map_add' _ _ := ContinuousLinearMap.ext fun _ ↦ rfl
       map_smul' _ _ := ContinuousLinearMap.ext fun _ ↦ rfl } :
      (R →L[ℝ] F) →ₗ[ℝ] (R × ℂ →L[ℝ] F))
    1 fun A ↦ by
      rw [one_mul]
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun x ↦ ?_
      calc ‖A x.1‖ ≤ ‖A‖ * ‖x.1‖ := A.le_opNorm x.1
        _ ≤ ‖A‖ * ‖x‖ := mul_le_mul_of_nonneg_left (norm_fst_le x) (norm_nonneg A)

private theorem norm_precompFstCLM_le (R F : Type*) [NormedAddCommGroup R] [NormedSpace ℝ R]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ‖precompFstCLM R F‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Embedding `y : F` as `(u, v) ↦ v • y` on `R × ℂ`, a norm-nonincreasing continuous `ℝ`-linear
map. -/
private def spanSndCLM (R : Type*) [NormedAddCommGroup R] [NormedSpace ℝ R]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] :
    F →L[ℝ] (R × ℂ →L[ℝ] F) :=
  LinearMap.mkContinuous
    ({ toFun y := ((ContinuousLinearMap.toSpanSingleton ℂ y).restrictScalars ℝ).comp
         (ContinuousLinearMap.snd ℝ R ℂ)
       map_add' y₁ y₂ := ContinuousLinearMap.ext fun ⟨_, v⟩ ↦ smul_add v y₁ y₂
       map_smul' c y := ContinuousLinearMap.ext fun ⟨_, v⟩ ↦ smul_comm v c y } :
      F →ₗ[ℝ] (R × ℂ →L[ℝ] F))
    1 fun y ↦ by
      rw [one_mul]
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg y) fun x ↦ ?_
      -- Unfold `((toSpanSingleton ℂ y).restrictScalars ℝ ∘L snd ℝ R ℂ) x` to `x.2 • y`.
      change ‖x.2 • y‖ ≤ ‖y‖ * ‖x‖
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_snd_le x) (norm_nonneg y)

private theorem norm_spanSndCLM_le (R F : Type*) [NormedAddCommGroup R] [NormedSpace ℝ R]
    [NormedAddCommGroup F] [NormedSpace ℂ F] :
    ‖spanSndCLM R F‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- For a `C^∞` map `H : R × ℂ → F` on an open product `s ×ˢ V`, differentiating first in `r ∈ R`
along `u` and then in `z ∈ ℂ` along `w` agrees with differentiating in the opposite order. -/
private theorem fderiv_snd_fderiv_fst_comm {R F : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set R} {V : Set ℂ} {H : R × ℂ → F}
    (hs : IsOpen s) (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H (s ×ˢ V))
    {r₀ : R} (hr₀ : r₀ ∈ s) {z₀ : ℂ} (hz₀ : z₀ ∈ V) (u : R) (w : ℂ) :
    fderiv ℝ (fun z ↦ fderiv ℝ (fun r ↦ H (r, z)) r₀ u) z₀ w =
      fderiv ℝ (fun r ↦ fderiv ℝ (fun z ↦ H (r, z)) z₀ w) r₀ u := by
  have hopen : IsOpen (s ×ˢ V) := hs.prod hV
  have hmem : (r₀, z₀) ∈ s ×ˢ V := ⟨hr₀, hz₀⟩
  have hslice_r :
      (fun z ↦ fderiv ℝ (fun r ↦ H (r, z)) r₀ u) =ᶠ[𝓝 z₀]
        fun z ↦ fderiv ℝ H (r₀, z) (u, 0) := by
    filter_upwards [hV.mem_nhds hz₀] with z hz
    have hd : DifferentiableAt ℝ H (r₀, z) :=
      (hH.contDiffAt (hopen.mem_nhds ⟨hr₀, hz⟩)).differentiableAt (by simp)
    exact DFunLike.congr_fun
      ((hd.hasFDerivAt.comp r₀ (hasFDerivAt_prodMk_left (𝕜 := ℝ) r₀ z)).fderiv) u
  have hslice_z :
      (fun r ↦ fderiv ℝ (fun z ↦ H (r, z)) z₀ w) =ᶠ[𝓝 r₀]
        fun r ↦ fderiv ℝ H (r, z₀) (0, w) := by
    filter_upwards [hs.mem_nhds hr₀] with r hr
    have hd : DifferentiableAt ℝ H (r, z₀) :=
      (hH.contDiffAt (hopen.mem_nhds ⟨hr, hz₀⟩)).differentiableAt (by simp)
    exact DFunLike.congr_fun
      ((hd.hasFDerivAt.comp z₀ (hasFDerivAt_prodMk_right (𝕜 := ℝ) r z₀)).fderiv) w
  rw [hslice_r.fderiv_eq, hslice_z.fderiv_eq]
  have hDH : DifferentiableAt ℝ (fderiv ℝ H) (r₀, z₀) :=
    ((hH.fderiv_of_isOpen (m := ∞) hopen (by simp)).contDiffAt
      (hopen.mem_nhds hmem)).differentiableAt (by simp)
  let ev_u : (R × ℂ →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F (u, 0)
  let ev_w : (R × ℂ →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F (0, w)
  have h1 := ((ev_u.hasFDerivAt.comp (r₀, z₀) hDH.hasFDerivAt).comp z₀
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) r₀ z₀)).fderiv
  have h2 := ((ev_w.hasFDerivAt.comp (r₀, z₀) hDH.hasFDerivAt).comp r₀
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) r₀ z₀)).fderiv
  have hlhs : fderiv ℝ (fun z ↦ fderiv ℝ H (r₀, z) (u, 0)) z₀ w =
      fderiv ℝ (fderiv ℝ H) (r₀, z₀) (0, w) (u, 0) := DFunLike.congr_fun h1 w
  have hrhs : fderiv ℝ (fun r ↦ fderiv ℝ H (r, z₀) (0, w)) r₀ u =
      fderiv ℝ (fderiv ℝ H) (r₀, z₀) (u, 0) (0, w) := DFunLike.congr_fun h2 u
  rw [hlhs, hrhs]
  exact (hH.contDiffAt (hopen.mem_nhds hmem)).isSymmSndFDerivAt (by simp) (0, w) (u, 0)

/-- If `H : R × ℂ → F` is `C^∞` on an open product `s ×ˢ V` and holomorphic in the second variable
on `V`, then its first parameter derivative `z ↦ fderiv ℝ (fun r ↦ H (r, z)) r₀` is also
holomorphic on `V`. -/
theorem differentiableOn_fderiv_prod_left {R F : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {s : Set R} {V : Set ℂ} {H : R × ℂ → F}
    (hs : IsOpen s) (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H (s ×ˢ V))
    (hhol : ∀ r ∈ s, DifferentiableOn ℂ (fun z ↦ H (r, z)) V) {r₀ : R} (hr₀ : r₀ ∈ s) :
    DifferentiableOn ℂ (fun z ↦ fderiv ℝ (fun r ↦ H (r, z)) r₀) V := by
  have hopen : IsOpen (s ×ˢ V) := hs.prod hV
  have hH₁ : ContDiffOn ℝ ∞ (fun p : R × ℂ ↦ fderiv ℝ (fun r ↦ H (r, p.2)) p.1) (s ×ˢ V) :=
    hH.fderiv_partial_of_isOpen (m := ∞) hopen
  intro z₀ hz₀
  have hd_real : DifferentiableAt ℝ (fun z ↦ fderiv ℝ (fun r ↦ H (r, z)) r₀) z₀ :=
    ((hH₁.contDiffAt (hopen.mem_nhds ⟨hr₀, hz₀⟩)).comp z₀
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  refine ((differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero hd_real).2 ?_)
    |>.differentiableWithinAt
  ext u
  have hev : conjWirtingerDeriv (fun z ↦ (evalCLM u) (fderiv ℝ (fun r ↦ H (r, z)) r₀)) z₀ 1 =
      evalCLM u (conjWirtingerDeriv (fun z ↦ fderiv ℝ (fun r ↦ H (r, z)) r₀) z₀ 1) := by
    have hcomp := conjWirtingerDeriv_comp (φ := evalCLM (R := R) (F := F) u)
      (g := fun z ↦ fderiv ℝ (fun r ↦ H (r, z)) r₀) (x := z₀)
      (evalCLM (R := R) (F := F) u).differentiableAt hd_real
    simpa [Function.comp_def] using DFunLike.congr_fun hcomp 1
  rw [← evalCLM_apply, ← hev]
  simp only [evalCLM_apply, conjWirtingerDeriv_apply, smul_eq_mul, mul_one]
  rw [fderiv_snd_fderiv_fst_comm hs hV hH hr₀ hz₀ u 1,
    fderiv_snd_fderiv_fst_comm hs hV hH hr₀ hz₀ u I]
  have hDH : DifferentiableAt ℝ (fderiv ℝ H) (r₀, z₀) :=
    ((hH.fderiv_of_isOpen (m := ∞) hopen (by simp)).contDiffAt
      (hopen.mem_nhds ⟨hr₀, hz₀⟩)).differentiableAt (by simp)
  have hd_r1 : DifferentiableAt ℝ (fun r ↦ fderiv ℝ (fun z ↦ H (r, z)) z₀ 1) r₀ := by
    have hcongr : (fun r ↦ fderiv ℝ (fun z ↦ H (r, z)) z₀ 1) =ᶠ[𝓝 r₀]
        fun r ↦ fderiv ℝ H (r, z₀) (0, 1) := by
      filter_upwards [hs.mem_nhds hr₀] with r hr
      have hd : DifferentiableAt ℝ H (r, z₀) :=
        (hH.contDiffAt (hopen.mem_nhds ⟨hr, hz₀⟩)).differentiableAt (by simp)
      exact DFunLike.congr_fun
        ((hd.hasFDerivAt.comp z₀ (hasFDerivAt_prodMk_right (𝕜 := ℝ) r z₀)).fderiv) 1
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hcongr
    exact ((ContinuousLinearMap.apply ℝ F (0, 1)).differentiableAt.comp (r₀, z₀) hDH).comp r₀
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) r₀ z₀).differentiableAt
  have hd_rI : DifferentiableAt ℝ (fun r ↦ fderiv ℝ (fun z ↦ H (r, z)) z₀ I) r₀ := by
    have hcongr : (fun r ↦ fderiv ℝ (fun z ↦ H (r, z)) z₀ I) =ᶠ[𝓝 r₀]
        fun r ↦ fderiv ℝ H (r, z₀) (0, I) := by
      filter_upwards [hs.mem_nhds hr₀] with r hr
      have hd : DifferentiableAt ℝ H (r, z₀) :=
        (hH.contDiffAt (hopen.mem_nhds ⟨hr, hz₀⟩)).differentiableAt (by simp)
      exact DFunLike.congr_fun
        ((hd.hasFDerivAt.comp z₀ (hasFDerivAt_prodMk_right (𝕜 := ℝ) r z₀)).fderiv) I
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hcongr
    exact ((ContinuousLinearMap.apply ℝ F (0, I)).differentiableAt.comp (r₀, z₀) hDH).comp r₀
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) r₀ z₀).differentiableAt
  have hdbar_zero : (fun r ↦ conjWirtingerDeriv (fun z ↦ H (r, z)) z₀ 1) =ᶠ[𝓝 r₀] 0 := by
    filter_upwards [hs.mem_nhds hr₀] with r hr
    simp [((hhol r hr).differentiableAt (hV.mem_nhds hz₀)).conjWirtingerDeriv_eq_zero]
  have hf_zero : fderiv ℝ (fun r ↦ conjWirtingerDeriv (fun z ↦ H (r, z)) z₀ 1) r₀ u = 0 := by
    rw [hdbar_zero.fderiv_eq]
    simp
  have hlin :
      (fun r ↦ conjWirtingerDeriv (fun z ↦ H (r, z)) z₀ 1) =
        fun r ↦ (2 : ℂ)⁻¹ • (fderiv ℝ (fun z ↦ H (r, z)) z₀ 1 +
          I • fderiv ℝ (fun z ↦ H (r, z)) z₀ I) := by
    ext r
    simp [conjWirtingerDeriv_apply]
  rw [hlin] at hf_zero
  have hsmulI : DifferentiableAt ℝ (fun r ↦ I • fderiv ℝ (fun z ↦ H (r, z)) z₀ I) r₀ :=
    hd_rI.const_smul I
  let L2 : F →L[ℝ] F := (ContinuousLinearMap.lsmul ℂ ℂ (2 : ℂ)⁻¹).restrictScalars ℝ
  let LI : F →L[ℝ] F := (ContinuousLinearMap.lsmul ℂ ℂ I).restrictScalars ℝ
  have hI_eq : fderiv ℝ (fun r ↦ I • fderiv ℝ (fun z ↦ H (r, z)) z₀ I) r₀ =
      LI.comp (fderiv ℝ (fun r ↦ fderiv ℝ (fun z ↦ H (r, z)) z₀ I) r₀) :=
    (LI.hasFDerivAt.comp r₀ hd_rI.hasFDerivAt).fderiv
  have h2_eq : fderiv ℝ (fun r ↦ (2 : ℂ)⁻¹ • (fderiv ℝ (fun z ↦ H (r, z)) z₀ 1 +
      I • fderiv ℝ (fun z ↦ H (r, z)) z₀ I)) r₀ =
      L2.comp (fderiv ℝ (fun r ↦ fderiv ℝ (fun z ↦ H (r, z)) z₀ 1 +
        I • fderiv ℝ (fun z ↦ H (r, z)) z₀ I) r₀) :=
    (L2.hasFDerivAt.comp r₀ (hd_r1.add hsmulI).hasFDerivAt).fderiv
  rw [h2_eq, ContinuousLinearMap.comp_apply, fderiv_fun_add hd_r1 hsmulI, add_apply, hI_eq]
    at hf_zero
  exact hf_zero

private theorem differentiableOn_iteratedFDeriv_prod_left_aux {R : Type u} {F : Type (max u v)}
    [NormedAddCommGroup R] [NormedSpace ℝ R] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {s : Set R} {V : Set ℂ} {H : R × ℂ → F}
    (hs : IsOpen s) (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H (s ×ˢ V))
    (hhol : ∀ r ∈ s, DifferentiableOn ℂ (fun z ↦ H (r, z)) V) (m : ℕ) {r₀ : R} (hr₀ : r₀ ∈ s) :
    DifferentiableOn ℂ (fun z ↦ iteratedFDeriv ℝ m (fun r ↦ H (r, z)) r₀) V := by
  induction m generalizing F with
  | zero =>
    refine ((uncurryFin0ComplexCLE (R := R) (F := F)).differentiable.comp_differentiableOn
      (hhol r₀ hr₀)).congr fun z _ ↦ ContinuousMultilinearMap.ext fun _ ↦ ?_
    simp
  | succ m ih =>
    have hH₁ : ContDiffOn ℝ ∞ (fun p : R × ℂ ↦ fderiv ℝ (fun r ↦ H (r, p.2)) p.1) (s ×ˢ V) :=
      hH.fderiv_partial_of_isOpen (m := ∞) (hs.prod hV)
    have hhol₁ : ∀ r ∈ s, DifferentiableOn ℂ (fun z ↦ fderiv ℝ (fun r' ↦ H (r', z)) r) V :=
      fun r hr ↦ differentiableOn_fderiv_prod_left hs hV hH hhol hr
    refine ((curryRightComplexCLE (R := R) (F := F) m).symm.differentiable.comp_differentiableOn
      (ih hH₁ hhol₁)).congr fun z _ ↦ ContinuousMultilinearMap.ext fun w ↦ ?_
    simp [iteratedFDeriv_succ_eq_comp_right]

/-- **Every iterated parameter derivative remains holomorphic in the plane variable.** If
`H : R × ℂ → F` is `C^∞` on an open product `s ×ˢ V` and holomorphic in the second variable on `V`,
then `z ↦ iteratedFDeriv ℝ m (fun r ↦ H (r, z)) r₀` is holomorphic on `V` for every `m : ℕ` and
`r₀ ∈ s`. -/
theorem differentiableOn_iteratedFDeriv_prod_left {R : Type u} {F : Type v}
    [NormedAddCommGroup R] [NormedSpace ℝ R] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {s : Set R} {V : Set ℂ} {H : R × ℂ → F}
    (hs : IsOpen s) (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H (s ×ˢ V))
    (hhol : ∀ r ∈ s, DifferentiableOn ℂ (fun z ↦ H (r, z)) V) (m : ℕ) {r₀ : R} (hr₀ : r₀ ∈ s) :
    DifferentiableOn ℂ (fun z ↦ iteratedFDeriv ℝ m (fun r ↦ H (r, z)) r₀) V := by
  let ι : F →L[ℂ] ((R × ℝ) →L[ℝ] F) := (liftLI R F).toContinuousLinearMap
  let H' : R × ℂ → ((R × ℝ) →L[ℝ] F) := fun p ↦ ι (H p)
  have hH' : ContDiffOn ℝ ∞ H' (s ×ˢ V) :=
    ((ι.restrictScalars ℝ).contDiff.comp_contDiffOn hH).congr fun _ _ ↦ rfl
  have hhol' : ∀ r ∈ s, DifferentiableOn ℂ (fun z ↦ H' (r, z)) V :=
    fun r hr ↦ (ι.differentiable.comp_differentiableOn (hhol r hr)).congr fun _ _ ↦ rfl
  have haux := differentiableOn_iteratedFDeriv_prod_left_aux hs hV hH' hhol' m hr₀
  refine ((unliftMultilinearCLM R F m).differentiable.comp_differentiableOn haux).congr
    fun z hz ↦ ContinuousMultilinearMap.ext fun w ↦ ?_
  have hcd : ContDiffAt ℝ m (fun r ↦ H (r, z)) r₀ :=
    (((hH.contDiffAt ((hs.prod hV).mem_nhds ⟨hr₀, hz⟩)).comp r₀
      (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp))
  have hit := (ι.restrictScalars ℝ).iteratedFDeriv_comp_left hcd le_rfl
  simp only [Function.comp_apply, unliftMultilinearCLM_apply]
  have hit' : iteratedFDeriv ℝ m (fun r ↦ H' (r, z)) r₀ =
      (ι.restrictScalars ℝ).compContinuousMultilinearMap
        (iteratedFDeriv ℝ m (fun r ↦ H (r, z)) r₀) := hit
  rw [hit']
  simp [ι, liftLI]

/-- For a map `g : ℂ → F` complex differentiable at `z`, its complex derivative `deriv g z` equals
`fderiv ℝ g z 1`. -/
private theorem deriv_eq_fderiv_real_apply_one {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {g : ℂ → F} {z : ℂ} (hg : DifferentiableAt ℂ g z) :
    deriv g z = fderiv ℝ g z 1 := by
  have hf := hg.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  simpa using (DFunLike.congr_fun hf.fderiv (1 : ℂ)).symm

/-- Iterated parameter differentiation commutes with `deriv` in the plane variable for a jointly
`C^∞` map `H : R × ℂ → F` that is holomorphic in the plane variable. -/
private theorem iteratedFDeriv_prod_left_deriv_snd {R : Type u} {F : Type (max u v)}
    [NormedAddCommGroup R] [NormedSpace ℝ R] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {s : Set R} {V : Set ℂ} {H : R × ℂ → F}
    (hs : IsOpen s) (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H (s ×ˢ V))
    (hhol : ∀ r ∈ s, DifferentiableOn ℂ (fun z ↦ H (r, z)) V)
    (m : ℕ) {r₀ : R} (hr₀ : r₀ ∈ s) {z₀ : ℂ} (hz₀ : z₀ ∈ V) :
    iteratedFDeriv ℝ m (fun r ↦ deriv (fun z ↦ H (r, z)) z₀) r₀ =
      deriv (fun z ↦ iteratedFDeriv ℝ m (fun r ↦ H (r, z)) r₀) z₀ := by
  have hopen : IsOpen (s ×ˢ V) := hs.prod hV
  have hcongr_r :
      (fun r ↦ deriv (fun z ↦ H (r, z)) z₀) =ᶠ[𝓝 r₀]
        fun r ↦ fderiv ℝ (fun z ↦ H (r, z)) z₀ 1 := by
    filter_upwards [hs.mem_nhds hr₀] with r hr
    exact deriv_eq_fderiv_real_apply_one ((hhol r hr).differentiableAt (hV.mem_nhds hz₀))
  rw [(hcongr_r.iteratedFDeriv ℝ m).self_of_nhds,
    deriv_eq_fderiv_real_apply_one
      ((differentiableOn_iteratedFDeriv_prod_left hs hV hH hhol m hr₀).differentiableAt
        (hV.mem_nhds hz₀))]
  clear hcongr_r
  induction m generalizing F with
  | zero =>
    let L : F ≃ₗᵢ[ℝ] (R [×0]→L[ℝ] F) := (continuousMultilinearCurryFin0 ℝ R F).symm
    have hL := DFunLike.congr_fun (L.comp_fderiv (f := fun z ↦ H (r₀, z)) (x := z₀)) 1
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def] at hL ⊢
    exact hL.symm
  | succ m ih =>
    let H₁ : R × ℂ → R →L[ℝ] F := fun p ↦ fderiv ℝ (fun r ↦ H (r, p.2)) p.1
    have hH₁ : ContDiffOn ℝ ∞ H₁ (s ×ˢ V) := hH.fderiv_partial_of_isOpen (m := ∞) hopen
    have hhol₁ : ∀ r ∈ s, DifferentiableOn ℂ (fun z ↦ H₁ (r, z)) V :=
      fun r hr ↦ differentiableOn_fderiv_prod_left hs hV hH hhol hr
    have hcomm₁ :
        (fun r ↦ fderiv ℝ (fun z ↦ H₁ (r, z)) z₀ 1) =ᶠ[𝓝 r₀]
          fderiv ℝ (fun r ↦ fderiv ℝ (fun z ↦ H (r, z)) z₀ 1) := by
      filter_upwards [hs.mem_nhds hr₀] with r hr
      ext u
      have hd_z : DifferentiableAt ℝ (fun z ↦ H₁ (r, z)) z₀ :=
        ((hhol₁ r hr).differentiableAt (hV.mem_nhds hz₀)).restrictScalars ℝ
      let ev_u : (R →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F u
      have hev := DFunLike.congr_fun ((ev_u.hasFDerivAt.comp z₀ hd_z.hasFDerivAt).fderiv) 1
      dsimp only [ev_u, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
        Function.comp_def, H₁] at hev
      rw [← hev]
      exact fderiv_snd_fderiv_fst_comm hs hV hH hr hz₀ u 1
    let U : (R [×m]→L[ℝ] (R →L[ℝ] F)) ≃ₗᵢ[ℝ] (R [×(m + 1)]→L[ℝ] F) :=
      (continuousMultilinearCurryRightEquiv' ℝ m R F).symm
    have hU := DFunLike.congr_fun
      (U.comp_fderiv (f := fun z ↦ iteratedFDeriv ℝ m (fun r ↦ H₁ (r, z)) r₀) (x := z₀)) 1
    have hstep := ih hH₁ hhol₁
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
      ← (hcomm₁.iteratedFDeriv ℝ m).self_of_nhds, hstep]
    simpa [U, H₁, iteratedFDeriv_succ_eq_comp_right, Function.comp_def] using hU.symm

private theorem norm_iteratedFDeriv_prod_le_of_differentiableOn_snd_aux
    {R : Type u} {F : Type (max u v)}
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {s : Set R} {V : Set ℂ} {H : R × ℂ → F}
    (hs : IsOpen s) (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H (s ×ˢ V))
    (hhol : ∀ r ∈ s, DifferentiableOn ℂ (fun z ↦ H (r, z)) V)
    {r₀ : R} (hr₀ : r₀ ∈ s) {z₀ : ℂ} {r δ : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ) (k : ℕ)
    (hball : ball z₀ ((2 * (k : ℝ) + 1) * r) ⊆ V)
    (hbd : ∀ m ≤ k, ∀ z ∈ V, ‖iteratedFDeriv ℝ m (fun r ↦ H (r, z)) r₀‖ ≤ δ) :
    ‖iteratedFDeriv ℝ k H (r₀, z₀)‖ ≤ (1 + r⁻¹) ^ k * δ := by
  induction k generalizing F V δ with
  | zero =>
    have hz₀ : z₀ ∈ V := hball (mem_ball_self (by positivity))
    simpa [norm_iteratedFDeriv_zero] using hbd 0 le_rfl z₀ hz₀
  | succ k ih =>
    set V' : Set ℂ := ball z₀ ((2 * (k : ℝ) + 2) * r)
    have hV' : IsOpen V' := isOpen_ball
    have hV'V : V' ⊆ V :=
      (ball_subset_ball (by push_cast; linarith)).trans hball
    have hball' : ball z₀ ((2 * (k : ℝ) + 1) * r) ⊆ V' :=
      ball_subset_ball (by linarith)
    let H₁ : R × ℂ → R →L[ℝ] F := fun p ↦ fderiv ℝ (fun q ↦ H (q, p.2)) p.1
    let H₂ : R × ℂ → F := fun p ↦ deriv (fun z ↦ H (p.1, z)) p.2
    have hopen : IsOpen (s ×ˢ V) := hs.prod hV
    have hH₁_smooth : ContDiffOn ℝ ∞ H₁ (s ×ˢ V') :=
      (hH.mono (prod_mono_right hV'V)).fderiv_partial_of_isOpen (m := ∞) (hs.prod hV')
    have hH₁_hol : ∀ q ∈ s, DifferentiableOn ℂ (fun z ↦ H₁ (q, z)) V' :=
      fun q hq ↦ (differentiableOn_fderiv_prod_left hs hV hH hhol hq).mono hV'V
    have hH₁_bd : ∀ m ≤ k, ∀ z ∈ V', ‖iteratedFDeriv ℝ m (fun q ↦ H₁ (q, z)) r₀‖ ≤ δ := by
      intro m hm z hz
      have hsucc : iteratedFDeriv ℝ (m + 1) (fun q ↦ H (q, z)) r₀ =
          (continuousMultilinearCurryRightEquiv' ℝ m R F).symm
            (iteratedFDeriv ℝ m (fun q ↦ H₁ (q, z)) r₀) := by
        simp [H₁, iteratedFDeriv_succ_eq_comp_right]
      have hnorm : ‖iteratedFDeriv ℝ m (fun q ↦ H₁ (q, z)) r₀‖ =
          ‖iteratedFDeriv ℝ (m + 1) (fun q ↦ H (q, z)) r₀‖ := by
        rw [hsucc, LinearIsometryEquiv.norm_map]
      rw [hnorm]
      exact hbd (m + 1) (Nat.add_le_add_right hm 1) z (hV'V hz)
    have hIH₁ : ‖iteratedFDeriv ℝ k H₁ (r₀, z₀)‖ ≤ (1 + r⁻¹) ^ k * δ :=
      ih hV' hH₁_smooth hH₁_hol hδ hball' hH₁_bd
    -- On `s ×ˢ V`, `H₂ p = fderiv ℝ H p (0, 1)`, so `H₂` is `C^∞`.
    have hH₂_eq_on : EqOn H₂ (fun p ↦ fderiv ℝ H p (0, 1)) (s ×ˢ V) := by
      rintro ⟨q, z⟩ ⟨hq, hz⟩
      dsimp only [H₂]
      rw [deriv_eq_fderiv_real_apply_one ((hhol q hq).differentiableAt (hV.mem_nhds hz))]
      have hd : DifferentiableAt ℝ H (q, z) :=
        (hH.contDiffAt (hopen.mem_nhds ⟨hq, hz⟩)).differentiableAt (by simp)
      exact DFunLike.congr_fun
        ((hd.hasFDerivAt.comp z (hasFDerivAt_prodMk_right (𝕜 := ℝ) q z)).fderiv) 1
    have hH₂_smooth : ContDiffOn ℝ ∞ H₂ (s ×ˢ V') := by
      have hDH : ContDiffOn ℝ ∞ (fun p ↦ fderiv ℝ H p (0, 1)) (s ×ˢ V) :=
        ((ContinuousLinearMap.apply ℝ F (0, 1)).contDiff.comp_contDiffOn
          (hH.fderiv_of_isOpen (m := ∞) hopen (by simp))).congr fun _ _ ↦ rfl
      exact (hDH.congr hH₂_eq_on).mono (prod_mono_right hV'V)
    have hH₂_hol : ∀ q ∈ s, DifferentiableOn ℂ (fun z ↦ H₂ (q, z)) V' :=
      fun q hq ↦ ((hhol q hq).deriv hV).mono hV'V
    have hH₂_bd :
        ∀ m ≤ k, ∀ z ∈ V', ‖iteratedFDeriv ℝ m (fun q ↦ H₂ (q, z)) r₀‖ ≤ r⁻¹ * δ := by
      intro m hm w hw
      rw [iteratedFDeriv_prod_left_deriv_snd hs hV hH hhol m hr₀ (hV'V hw)]
      have hcb : closedBall w r ⊆ V := by
        refine Subset.trans (fun ζ hζ ↦ ?_) hball
        rw [mem_ball]
        have hw' : dist w z₀ < (2 * (k : ℝ) + 2) * r := mem_ball.1 hw
        have hζ' : dist ζ w ≤ r := mem_closedBall.1 hζ
        push_cast
        linarith [dist_triangle ζ w z₀]
      have hψ := differentiableOn_iteratedFDeriv_prod_left hs hV hH hhol m hr₀
      have hdiff_cl : DiffContOnCl ℂ (fun z ↦ iteratedFDeriv ℝ m (fun q ↦ H (q, z)) r₀)
          (ball w r) :=
        (hψ.mono (closure_ball_subset_closedBall.trans hcb)).diffContOnCl
      have hsph : ∀ ζ ∈ sphere w r,
          ‖iteratedFDeriv ℝ m (fun q ↦ H (q, ζ)) r₀‖ ≤ δ := fun ζ hζ ↦
        hbd m (hm.trans (Nat.le_succ k)) ζ (hcb (sphere_subset_closedBall hζ))
      have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdiff_cl hsph
      rwa [div_eq_inv_mul] at hcauchy
    have hIH₂ : ‖iteratedFDeriv ℝ k H₂ (r₀, z₀)‖ ≤ (1 + r⁻¹) ^ k * (r⁻¹ * δ) :=
      ih hV' hH₂_smooth hH₂_hol (by positivity) hball' hH₂_bd
    -- Decompose `fderiv ℝ H` near `(r₀, z₀)` into `precompFstCLM ∘ H₁ + spanSndCLM ∘ H₂`.
    have hz₀V' : z₀ ∈ V' := hball' (mem_ball_self (by positivity))
    have hfderiv_decomp :
        fderiv ℝ H =ᶠ[𝓝 (r₀, z₀)]
          (⇑(precompFstCLM R F) ∘ H₁) + (⇑(spanSndCLM R F) ∘ H₂) := by
      filter_upwards [(hs.prod hV').mem_nhds ⟨hr₀, hz₀V'⟩] with ⟨q, w⟩ ⟨hq, hw⟩
      have hd : DifferentiableAt ℝ H (q, w) :=
        (hH.contDiffAt (hopen.mem_nhds ⟨hq, hV'V hw⟩)).differentiableAt (by simp)
      have hd_w_cplx : HasDerivAt (fun z ↦ H (q, z)) (H₂ (q, w)) w :=
        ((hhol q hq).differentiableAt (hV.mem_nhds (hV'V hw))).hasDerivAt
      have hd_w : HasFDerivAt (fun z ↦ H (q, z))
          ((ContinuousLinearMap.toSpanSingleton ℂ (H₂ (q, w))).restrictScalars ℝ) w :=
        hd_w_cplx.hasFDerivAt.restrictScalars ℝ
      have hfst_eq : fderiv ℝ H (q, w) ∘L ContinuousLinearMap.inl ℝ R ℂ = H₁ (q, w) :=
        ((hd.hasFDerivAt.comp q (hasFDerivAt_prodMk_left (𝕜 := ℝ) q w)).fderiv).symm
      have hsnd_eq : fderiv ℝ H (q, w) ∘L ContinuousLinearMap.inr ℝ R ℂ =
          (ContinuousLinearMap.toSpanSingleton ℂ (H₂ (q, w))).restrictScalars ℝ :=
        (hd.hasFDerivAt.comp w (hasFDerivAt_prodMk_right (𝕜 := ℝ) q w)).unique hd_w
      refine ContinuousLinearMap.ext fun ⟨u, v⟩ ↦ ?_
      have hsplit : (u, v) = ContinuousLinearMap.inl ℝ R ℂ u + ContinuousLinearMap.inr ℝ R ℂ v := by
        ext <;> simp
      calc fderiv ℝ H (q, w) (u, v)
          = fderiv ℝ H (q, w) (ContinuousLinearMap.inl ℝ R ℂ u) +
              fderiv ℝ H (q, w) (ContinuousLinearMap.inr ℝ R ℂ v) := by
            conv_lhs => rw [hsplit]
            exact map_add _ _ _
        _ = H₁ (q, w) u +
              ((ContinuousLinearMap.toSpanSingleton ℂ (H₂ (q, w))).restrictScalars ℝ) v := by
            rw [← ContinuousLinearMap.comp_apply, hfst_eq, ← ContinuousLinearMap.comp_apply,
              hsnd_eq]
        _ = (precompFstCLM R F (H₁ (q, w)) + spanSndCLM R F (H₂ (q, w))) (u, v) := rfl
    have hcH₁ : ContDiffAt ℝ k H₁ (r₀, z₀) :=
      (hH₁_smooth.contDiffAt ((hs.prod hV').mem_nhds ⟨hr₀, hz₀V'⟩)).of_le (by simp)
    have hcH₂ : ContDiffAt ℝ k H₂ (r₀, z₀) :=
      (hH₂_smooth.contDiffAt ((hs.prod hV').mem_nhds ⟨hr₀, hz₀V'⟩)).of_le (by simp)
    have hc₁ : ContDiffAt ℝ k (⇑(precompFstCLM R F) ∘ H₁) (r₀, z₀) :=
      (precompFstCLM R F).contDiff.contDiffAt.comp (r₀, z₀) hcH₁
    have hc₂ : ContDiffAt ℝ k (⇑(spanSndCLM R F) ∘ H₂) (r₀, z₀) :=
      (spanSndCLM R F).contDiff.contDiffAt.comp (r₀, z₀) hcH₂
    rw [← norm_iteratedFDeriv_fderiv, (hfderiv_decomp.iteratedFDeriv ℝ k).self_of_nhds,
      iteratedFDeriv_add_apply hc₁ hc₂,
      (precompFstCLM R F).iteratedFDeriv_comp_left hcH₁ le_rfl,
      (spanSndCLM R F).iteratedFDeriv_comp_left hcH₂ le_rfl]
    have hb₁ : ‖(precompFstCLM R F).compContinuousMultilinearMap
        (iteratedFDeriv ℝ k H₁ (r₀, z₀))‖ ≤ (1 + r⁻¹) ^ k * δ := by
      calc ‖(precompFstCLM R F).compContinuousMultilinearMap (iteratedFDeriv ℝ k H₁ (r₀, z₀))‖
          ≤ ‖precompFstCLM R F‖ * ‖iteratedFDeriv ℝ k H₁ (r₀, z₀)‖ :=
            ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
        _ ≤ 1 * ((1 + r⁻¹) ^ k * δ) :=
            mul_le_mul (norm_precompFstCLM_le R F) hIH₁ (norm_nonneg _) zero_le_one
        _ = (1 + r⁻¹) ^ k * δ := one_mul _
    have hb₂ : ‖(spanSndCLM R F).compContinuousMultilinearMap
        (iteratedFDeriv ℝ k H₂ (r₀, z₀))‖ ≤ (1 + r⁻¹) ^ k * (r⁻¹ * δ) := by
      calc ‖(spanSndCLM R F).compContinuousMultilinearMap (iteratedFDeriv ℝ k H₂ (r₀, z₀))‖
          ≤ ‖spanSndCLM R F‖ * ‖iteratedFDeriv ℝ k H₂ (r₀, z₀)‖ :=
            ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
        _ ≤ 1 * ((1 + r⁻¹) ^ k * (r⁻¹ * δ)) :=
            mul_le_mul (norm_spanSndCLM_le R F) hIH₂ (norm_nonneg _) zero_le_one
        _ = (1 + r⁻¹) ^ k * (r⁻¹ * δ) := one_mul _
    calc ‖(precompFstCLM R F).compContinuousMultilinearMap (iteratedFDeriv ℝ k H₁ (r₀, z₀)) +
            (spanSndCLM R F).compContinuousMultilinearMap (iteratedFDeriv ℝ k H₂ (r₀, z₀))‖
        ≤ ‖(precompFstCLM R F).compContinuousMultilinearMap (iteratedFDeriv ℝ k H₁ (r₀, z₀))‖ +
            ‖(spanSndCLM R F).compContinuousMultilinearMap (iteratedFDeriv ℝ k H₂ (r₀, z₀))‖ :=
          ContinuousMultilinearMap.opNorm_add_le _ _
      _ ≤ (1 + r⁻¹) ^ k * δ + (1 + r⁻¹) ^ k * (r⁻¹ * δ) := add_le_add hb₁ hb₂
      _ = (1 + r⁻¹) ^ (k + 1) * δ := by ring

/-- **Total Fréchet derivative bound from parameter derivatives.** If `H : R × ℂ → F` into a complex
Banach space is `C^∞` on `s ×ˢ V` and holomorphic in the plane variable on `V`, and
`ball z₀ ((2k + 1) r) ⊆ V` with `r > 0`, then a bound `δ ≥ 0` on the parameter derivatives
`‖iteratedFDeriv ℝ m (fun r ↦ H (r, z)) r₀‖` (`m ≤ k`, `z ∈ V`) at the single point `r₀ ∈ s`
controls the total `k`-th Fréchet derivative at `(r₀, z₀)`:
`‖iteratedFDeriv ℝ k H (r₀, z₀)‖ ≤ (1 + r⁻¹) ^ k * δ`. -/
theorem norm_iteratedFDeriv_prod_le_of_differentiableOn_snd {R : Type u} {F : Type v}
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {s : Set R} {V : Set ℂ} {H : R × ℂ → F}
    (hs : IsOpen s) (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H (s ×ˢ V))
    (hhol : ∀ r ∈ s, DifferentiableOn ℂ (fun z ↦ H (r, z)) V)
    {r₀ : R} (hr₀ : r₀ ∈ s) {z₀ : ℂ} {r δ : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ) (k : ℕ)
    (hball : ball z₀ ((2 * (k : ℝ) + 1) * r) ⊆ V)
    (hbd : ∀ m ≤ k, ∀ z ∈ V, ‖iteratedFDeriv ℝ m (fun r ↦ H (r, z)) r₀‖ ≤ δ) :
    ‖iteratedFDeriv ℝ k H (r₀, z₀)‖ ≤ (1 + r⁻¹) ^ k * δ := by
  let ι : F →ₗᵢ[ℂ] ((R × ℝ) →L[ℝ] F) := liftLI R F
  let ιℝ : F →ₗᵢ[ℝ] ((R × ℝ) →L[ℝ] F) :=
    { toLinearMap := ι.toLinearMap.restrictScalars ℝ
      norm_map' := ι.norm_map }
  have hH' : ContDiffOn ℝ ∞ (ιℝ ∘ H) (s ×ˢ V) := ιℝ.contDiff.comp_contDiffOn hH
  have hhol' : ∀ q ∈ s, DifferentiableOn ℂ (fun z ↦ (ιℝ ∘ H) (q, z)) V :=
    fun q hq ↦ (ι.toContinuousLinearMap.differentiable.comp_differentiableOn (hhol q hq)).congr
      fun _ _ ↦ rfl
  have hz₀ : z₀ ∈ V := hball (mem_ball_self (by positivity))
  have hcd_tot : ContDiffAt ℝ k H (r₀, z₀) :=
    (hH.contDiffAt ((hs.prod hV).mem_nhds ⟨hr₀, hz₀⟩)).of_le (by simp)
  rw [← ιℝ.norm_iteratedFDeriv_comp_left hcd_tot le_rfl]
  refine norm_iteratedFDeriv_prod_le_of_differentiableOn_snd_aux hs hV hH' hhol' hr₀ hr hδ k hball
    fun m hm z hz ↦ ?_
  have hcd_r : ContDiffAt ℝ m (fun q ↦ H (q, z)) r₀ :=
    (((hH.contDiffAt ((hs.prod hV).mem_nhds ⟨hr₀, hz⟩)).comp r₀
      (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp))
  have hit := ιℝ.norm_iteratedFDeriv_comp_left hcd_r le_rfl
  exact hit.trans_le (hbd m hm z hz)

end ParameterDerivatives

/-! ### Smooth convergence of series on open subsets from eventual derivative bounds -/

section SmoothSeriesOn

/-- A series `∑' k, G k x` of maps `C^∞` on an open set `O` of a finite-dimensional real normed
space into a Banach space is `C^∞` on `O` whenever, for every derivative order `m`, its `m`-th
iterated derivatives on `O` are eventually bounded by `(1 / 2) ^ k`. -/
private theorem contDiffOn_tsum_of_eventually_geometric {X F : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {O : Set X} (hO : IsOpen O) {G : ℕ → X → F}
    (hG : ∀ k, ContDiffOn ℝ ∞ (G k) O)
    (hbd : ∀ m : ℕ, ∀ᶠ k in atTop, ∀ x ∈ O, ‖iteratedFDeriv ℝ m (G k) x‖ ≤ (1 / 2 : ℝ) ^ k) :
    ContDiffOn ℝ ∞ (fun x ↦ ∑' k, G k x) O := by
  intro x₀ hx₀
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hO x₀ hx₀
  let θ : ContDiffBump x₀ := ⟨ρ / 4, ρ / 2, by positivity, by linarith⟩
  have hθ_supp : tsupport θ ⊆ O := by
    rw [θ.tsupport_eq]
    exact (closedBall_subset_ball (by dsimp [θ]; linarith)).trans hball
  have hθ_cpt : IsCompact (tsupport θ) := by
    rw [θ.tsupport_eq]
    exact isCompact_closedBall x₀ (ρ / 2)
  have hθ_smooth : ContDiff ℝ ∞ θ := θ.contDiff
  let G' : ℕ → X → F := fun k x ↦ θ x • G k x
  have hG'_smooth : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (G' k) := fun k ↦
    (hG k).contDiff_smul_of_tsupport_subset hO hθ_smooth.contDiffOn hθ_supp
  let Bθ : ℕ → ℝ := fun i ↦ max 0 (sSup ((fun x ↦ ‖iteratedFDeriv ℝ i θ x‖) '' tsupport θ))
  have hBθ_nonneg : ∀ i, 0 ≤ Bθ i := fun i ↦ le_max_left 0 _
  have hBθ_le : ∀ i, ∀ x ∈ tsupport θ, ‖iteratedFDeriv ℝ i θ x‖ ≤ Bθ i := by
    intro i x hx
    refine le_trans ?_ (le_max_right 0 _)
    have hcont : ContinuousOn (fun y ↦ ‖iteratedFDeriv ℝ i θ y‖) (tsupport θ) :=
      (hθ_smooth.continuous_iteratedFDeriv (m := i) (by simp)).norm.continuousOn
    exact le_csSup (hθ_cpt.bddAbove_image hcont) (mem_image_of_mem _ hx)
  let A : ℕ → ℝ := fun m ↦ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Bθ i
  have hA_nonneg : ∀ m, 0 ≤ A m := fun m ↦
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (Nat.cast_nonneg _) (hBθ_nonneg i)
  let v : ℕ → ℕ → ℝ := fun m k ↦ A m * (1 / 2 : ℝ) ^ k
  have hv_sum : ∀ m : ℕ, (m : ℕ∞) ≤ (⊤ : ℕ∞) → Summable (v m) := fun m _ ↦ by
    simpa [v, one_div] using summable_geometric_two.mul_left (A m)
  have hv_bd : ∀ m : ℕ, (m : ℕ∞) ≤ (⊤ : ℕ∞) →
      ∀ᶠ k in (Filter.cofinite : Filter ℕ), ∀ x : X, ‖iteratedFDeriv ℝ m (G' k) x‖ ≤ v m k := by
    intro m _
    rw [Nat.cofinite_eq_atTop]
    have hall : ∀ᶠ k in atTop, ∀ i ∈ Finset.range (m + 1), ∀ x ∈ O,
        ‖iteratedFDeriv ℝ (m - i) (G k) x‖ ≤ (1 / 2 : ℝ) ^ k :=
      (eventually_all_finset (Finset.range (m + 1))).2 fun i _ ↦ hbd (m - i)
    filter_upwards [hall] with k hk x
    by_cases hx : x ∈ tsupport θ
    · have hxO : x ∈ O := hθ_supp hx
      have hsmul := norm_iteratedFDerivWithin_smul_le (N := ∞) (n := m) hθ_smooth.contDiffOn
        (hG k) hO.uniqueDiffOn hxO (by simp)
      rw [iteratedFDerivWithin_of_isOpen m hO hxO] at hsmul
      refine hsmul.trans ?_
      simp only [v, A, Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi ↦ ?_
      rw [iteratedFDerivWithin_of_isOpen i hO hxO, iteratedFDerivWithin_of_isOpen (m - i) hO hxO]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hBθ_le i x hx) (Nat.cast_nonneg _))
        (hk i hi x hxO) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hBθ_nonneg i))
    · have hzero : G' k =ᶠ[𝓝 x] 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
        simp [G', hy]
      rw [(hzero.iteratedFDeriv ℝ m).self_of_nhds, iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
      exact mul_nonneg (hA_nonneg m) (by positivity)
  have hsum_smooth : ContDiff ℝ ∞ (fun x ↦ ∑' k, G' k x) :=
    contDiff_tsum_of_eventually hG'_smooth hv_sum hv_bd
  have heq : (fun x ↦ ∑' k, G k x) =ᶠ[𝓝 x₀] fun x ↦ ∑' k, G' k x := by
    filter_upwards [ball_mem_nhds x₀ (show 0 < ρ / 4 by positivity)] with x hx
    have hθ1 : θ x = 1 := θ.one_of_mem_closedBall (ball_subset_closedBall hx)
    simp [G', hθ1]
  exact ((hsum_smooth.contDiffAt).congr_of_eventuallyEq heq).contDiffWithinAt

end SmoothSeriesOn

/-! ### Global mixed-parameter `\bar∂` solver on normed spaces -/

section NormedParameterSolver

universe uP uQ uF

/-- Telescoping identity for `h 0 + ∑ k ∈ range K, (h (k + 1) - h k - P k)`. -/
private theorem add_sum_range_sub_sub {F : Type*} [AddCommGroup F]
    (a : ℕ → F) (b : ℕ → F) (K : ℕ) :
    a 0 + ∑ k ∈ Finset.range K, (a (k + 1) - a k - b k) =
      a K - ∑ k ∈ Finset.range K, b k := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← add_assoc, ih]
    abel

/-- **Global planar `\bar∂` solver with smooth and holomorphic parameters.** Let `P` be a
finite-dimensional real normed space, `Q` a finite-dimensional complex normed space, and `F` a
complex Banach space, and let `U_P ⊆ P`, `U_Q ⊆ Q` and `Ω ⊆ ℂ` be arbitrary open sets. For every
`f : (P × Q) × ℂ → F` that is jointly `C^∞` on `(U_P ×ˢ U_Q) ×ˢ Ω` and holomorphic in `q ∈ U_Q` for
every `(p, z) ∈ U_P ×ˢ Ω`, there exists `u : (P × Q) × ℂ → F` jointly `C^∞` on
`(U_P ×ˢ U_Q) ×ˢ Ω`, holomorphic in `q ∈ U_Q` for every `(p, z) ∈ U_P ×ˢ Ω`, and solving
`conjWirtingerDeriv (fun w ↦ u ((p, q), w)) z 1 = f ((p, q), z)` at every point of
`(U_P ×ˢ U_Q) ×ˢ Ω`. -/
theorem exists_contDiffOn_differentiableOn_conjWirtingerDeriv_apply_one_eq
    {P : Type uP} {Q : Type uQ} {F : Type uF}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℂ Q] [FiniteDimensional ℂ Q]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U_P : Set P} {U_Q : Set Q} {Ω : Set ℂ} {f : (P × Q) × ℂ → F}
    (hUP : IsOpen U_P) (hUQ : IsOpen U_Q) (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ ∞ f ((U_P ×ˢ U_Q) ×ˢ Ω))
    (hfq : ∀ p ∈ U_P, ∀ z ∈ Ω, DifferentiableOn ℂ (fun q ↦ f ((p, q), z)) U_Q) :
    ∃ u : (P × Q) × ℂ → F,
      ContDiffOn ℝ ∞ u ((U_P ×ˢ U_Q) ×ˢ Ω) ∧
      (∀ p ∈ U_P, ∀ z ∈ Ω, DifferentiableOn ℂ (fun q ↦ u ((p, q), z)) U_Q) ∧
      ∀ p ∈ U_P, ∀ q ∈ U_Q, ∀ z ∈ Ω,
        conjWirtingerDeriv (fun w ↦ u ((p, q), w)) z 1 = f ((p, q), z) := by
  set s : Set (P × Q) := U_P ×ˢ U_Q
  have hs : IsOpen s := hUP.prod hUQ
  -- Step 1: Exhaust `s = U_P ×ˢ U_Q` by compacta `B k` and `Ω` by filled compacta `C k`.
  obtain ⟨B, hB_cpt, hB_int, hB_union, -⟩ := hs.exists_isFilledIn_compact_exhaustion
  have hB_mono : Monotone B := monotone_nat_of_le_succ fun n ↦ (hB_int n).trans interior_subset
  have hBs : ∀ n, B n ⊆ s := fun n ↦ (subset_iUnion B n).trans hB_union.subset
  obtain ⟨C, hC_cpt, hC_int, hC_union, hC_fill⟩ := hΩ.exists_isFilledIn_compact_exhaustion
  have hC_mono : Monotone C := monotone_nat_of_le_succ fun n ↦ (hC_int n).trans interior_subset
  have hCΩ : ∀ n, C n ⊆ Ω := fun n ↦ (subset_iUnion C n).trans hC_union.subset
  have hexh : ∀ r₀ ∈ s, ∀ z₀ ∈ Ω, ∃ N, r₀ ∈ interior (B N) ∧ z₀ ∈ interior (C N) := by
    intro r₀ hr₀ z₀ hz₀
    obtain ⟨n₁, hn₁⟩ := mem_iUnion.1 (hB_union ▸ hr₀)
    obtain ⟨n₂, hn₂⟩ := mem_iUnion.1 (hC_union ▸ hz₀)
    exact ⟨max n₁ n₂ + 1, hB_int _ (hB_mono (le_max_left n₁ n₂) hn₁),
      hC_int _ (hC_mono (le_max_right n₁ n₂) hn₂)⟩
  -- Step 2: Construct local smooth potentials `h k` solving `\bar∂_z (h k r) = f (r, ·)` near
  -- `C (k + 1)` and holomorphic in `q ∈ U_Q` everywhere on `ℂ`.
  have hfq_at : ∀ r ∈ s, ∀ z ∈ Ω, DifferentiableAt ℂ (fun q ↦ f ((r.1, q), z)) r.2 :=
    fun r hr z hz ↦ (hfq r.1 hr.1 z hz).differentiableAt (hUQ.mem_nhds hr.2)
  choose h hh_smooth hh_nhds hh_hol_q using fun k : ℕ ↦
    exists_contDiffOn_conjWirtingerDeriv_apply_one_eventually_eq_with_holomorphic_param
      (f := fun r z ↦ f (r, z)) (s := s) (U := Ω) (K := C (k + 1)) (n := (⊤ : ℕ∞))
      (by simp) hs hΩ (hC_cpt (k + 1)) (hCΩ (k + 1)) hf hfq_at
  have hexW : ∀ k : ℕ, ∃ W : Set ℂ, IsOpen W ∧ C (k + 1) ⊆ W ∧ W ⊆ Ω ∧
      ∀ z ∈ W, ∀ r ∈ s, conjWirtingerDeriv (h k r) z 1 = f (r, z) := by
    intro k
    obtain ⟨W₀, hW₀_open, hCW₀, hW₀_eq⟩ := mem_nhdsSet_iff_exists.1 (hh_nhds k)
    exact ⟨W₀ ∩ Ω, hW₀_open.inter hΩ, subset_inter hCW₀ (hCΩ (k + 1)), inter_subset_right,
      fun z hz r hr ↦ hW₀_eq hz.1 r hr⟩
  choose W hW_open hCW hWΩ hW_eq using hexW
  -- Step 3: Consecutive differences `d k r z = h (k + 1) r z - h k r z` are holomorphic in `z` on
  -- `V k = W k ∩ W (k + 1) ⊇ C (k + 1)`.
  let V : ℕ → Set ℂ := fun k ↦ W k ∩ W (k + 1)
  have hV_open : ∀ k, IsOpen (V k) := fun k ↦ (hW_open k).inter (hW_open (k + 1))
  have hCV : ∀ k, C (k + 1) ⊆ V k := fun k ↦
    subset_inter (hCW k) (((hC_int (k + 1)).trans interior_subset).trans (hCW (k + 1)))
  let d : ℕ → (P × Q) → ℂ → F := fun k r z ↦ h (k + 1) r z - h k r z
  have hd_smooth : ∀ k, ContDiffOn ℝ ∞ ↿(d k) (s ×ˢ univ) :=
    fun k ↦ (hh_smooth (k + 1)).sub (hh_smooth k)
  have hd_hol_z : ∀ k, ∀ r ∈ s, DifferentiableOn ℂ (d k r) (V k) := by
    intro k r hr z hz
    have hd1 : DifferentiableAt ℝ (h (k + 1) r) z :=
      (((hh_smooth (k + 1)).contDiffAt ((hs.prod isOpen_univ).mem_nhds ⟨hr, mem_univ z⟩)).comp z
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    have hd0 : DifferentiableAt ℝ (h k r) z :=
      (((hh_smooth k).contDiffAt ((hs.prod isOpen_univ).mem_nhds ⟨hr, mem_univ z⟩)).comp z
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    refine ((differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero (hd1.sub hd0)).2 ?_)
      |>.differentiableWithinAt
    rw [conjWirtingerDeriv_sub hd1 hd0, sub_apply,
      hW_eq (k + 1) z hz.2 r hr, hW_eq k z hz.1 r hr, sub_self]
  have hd_hol_q : ∀ k, ∀ p ∈ U_P, ∀ w, DifferentiableOn ℂ (fun q ↦ d k (p, q) w) U_Q :=
    fun k p hp w q hq ↦
      ((hh_hol_q (k + 1) (p, q) ⟨hp, hq⟩ w).sub (hh_hol_q k (p, q) ⟨hp, hq⟩ w))
        |>.differentiableWithinAt
  -- Step 4: Choose compact collars `L k` (`C (k + 1) ⊆ interior (L k)`, `L k ⊆ V k`), ball radii
  -- `ρ k` inside `interior (C (k + 1))`, and uniform bounds `M k` on parameter derivatives of
  -- `d k` of order `≤ k` on `B k ×ˢ L k`.
  choose L hL_cpt hCL_int hLV using fun k ↦
    exists_compact_between (hC_cpt (k + 1)) (hV_open k) (hCV k)
  choose δ hδ_pos hδ_sub using fun k ↦
    (hC_cpt k).exists_thickening_subset_open isOpen_interior (hC_int k)
  let ρ : ℕ → ℝ := fun k ↦ δ k / (2 * (k : ℝ) + 1)
  have hρ_pos : ∀ k, 0 < ρ k := fun k ↦ div_pos (hδ_pos k) (by positivity)
  have hball_C : ∀ k m, m ≤ k → ∀ z ∈ C k,
      ball z ((2 * (m : ℝ) + 1) * ρ k) ⊆ interior (C (k + 1)) := by
    intro k m hm z hz ζ hζ
    refine hδ_sub k (mem_thickening_iff.2 ⟨z, hz, ?_⟩)
    have hle : (2 * (m : ℝ) + 1) * ρ k ≤ δ k := by
      have hm' : (m : ℝ) ≤ k := Nat.cast_le.2 hm
      have hpos : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
      calc (2 * (m : ℝ) + 1) * (δ k / (2 * (k : ℝ) + 1))
          ≤ (2 * (k : ℝ) + 1) * (δ k / (2 * (k : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right (by linarith) (hρ_pos k).le
        _ = δ k := mul_div_cancel₀ _ hpos.ne'
    exact (mem_ball.1 hζ).trans_le hle
  let Mm : ℕ → ℕ → ℝ := fun k m ↦
    max 0 (sSup ((fun p : (P × Q) × ℂ ↦
      ‖iteratedFDeriv ℝ m (fun r ↦ d k r p.2) p.1‖) '' (B k ×ˢ L k)))
  have hMm_nonneg : ∀ k m, 0 ≤ Mm k m := fun k m ↦ le_max_left 0 _
  let M : ℕ → ℝ := fun k ↦ ∑ m ∈ Finset.range (k + 1), Mm k m
  have hM_nonneg : ∀ k, 0 ≤ M k := fun k ↦ Finset.sum_nonneg fun m _ ↦ hMm_nonneg k m
  have hM_bd : ∀ k m, m ≤ k → ∀ r ∈ B k, ∀ z ∈ L k,
      ‖iteratedFDeriv ℝ m (fun r' ↦ d k r' z) r‖ ≤ M k := by
    intro k m hm r hr z hz
    have hcont : ContinuousOn
        (fun p : (P × Q) × ℂ ↦ ‖iteratedFDeriv ℝ m (fun r' ↦ d k r' p.2) p.1‖) (B k ×ˢ L k) :=
      (((hd_smooth k).continuousOn_iteratedFDeriv_partial (hs.prod isOpen_univ)
        (k := m) (by simp)).norm).mono (prod_mono (hBs k) (subset_univ _))
    have hle_Mm : ‖iteratedFDeriv ℝ m (fun r' ↦ d k r' z) r‖ ≤ Mm k m := by
      let φ : (P × Q) × ℂ → ℝ := fun p ↦ ‖iteratedFDeriv ℝ m (fun r' ↦ d k r' p.2) p.1‖
      have hmem : φ (r, z) ∈ φ '' (B k ×ˢ L k) := mem_image_of_mem φ (mk_mem_prod hr hz)
      exact le_trans (le_csSup (((hB_cpt k).prod (hL_cpt k)).bddAbove_image hcont) hmem)
        (le_max_right 0 _)
    exact hle_Mm.trans (Finset.single_le_sum (fun i _ ↦ hMm_nonneg k i)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hm)))
  -- Step 5: Apply the finite-rank Runge operator to `(Ω, C (k + 1), interior (L k))` with
  -- tolerance `ε k` chosen so total derivatives up to order `k` are `≤ 2⁻ᵏ` on `B k ×ˢ C k`.
  have h1ρ_pos : ∀ k, 0 < 1 + (ρ k)⁻¹ :=
    fun k ↦ add_pos_of_pos_of_nonneg one_pos (inv_nonneg.2 (hρ_pos k).le)
  have hM1_pos : ∀ k, 0 < M k + 1 :=
    fun k ↦ add_pos_of_nonneg_of_pos (hM_nonneg k) one_pos
  have hdenom_pos : ∀ k, 0 < (1 + (ρ k)⁻¹) ^ k * (M k + 1) :=
    fun k ↦ mul_pos (pow_pos (h1ρ_pos k) k) (hM1_pos k)
  let ε : ℕ → ℝ := fun k ↦ (1 / 2 : ℝ) ^ k / ((1 + (ρ k)⁻¹) ^ k * (M k + 1))
  have hε_pos : ∀ k, 0 < ε k := fun k ↦ div_pos (by positivity) (hdenom_pos k)
  choose nk ζk wk gk _ hgk_hol hRunge using fun k : ℕ ↦
    (hC_fill (k + 1)).exists_norm_sub_sum_mul_smul_le.{max uP uQ uF} hΩ (hC_cpt (k + 1))
      (hCΩ (k + 1)) isOpen_interior (hCL_int k) (hε_pos k)
  let Pk : ℕ → (P × Q) × ℂ → F :=
    fun k p ↦ ∑ i : Fin (nk k), (wk k i * gk k i p.2) • d k p.1 (ζk k i)
  let ek : ℕ → (P × Q) × ℂ → F := fun k p ↦ d k p.1 p.2 - Pk k p
  have hPk_hol_z : ∀ k r, DifferentiableOn ℂ (fun z ↦ Pk k (r, z)) Ω :=
    fun k r ↦ differentiableOn_sum_mul_smul (wk k) (hgk_hol k) (fun i ↦ d k r (ζk k i))
  have hPk_smooth : ∀ k, ContDiffOn ℝ ∞ (Pk k) (s ×ˢ Ω) := by
    intro k
    refine contDiffOn_sum_mul_smul_prod (n := ∞) (s := s) (v := fun i r ↦ d k r (ζk k i))
      hΩ (wk k) (hgk_hol k) fun i ↦ ?_
    exact (hd_smooth k).comp (contDiffOn_id.prodMk contDiffOn_const)
      fun r hr ↦ ⟨hr, mem_univ _⟩
  have hek_smooth : ∀ k, ContDiffOn ℝ ∞ (ek k) (s ×ˢ Ω) := fun k ↦
    ((hd_smooth k).mono (prod_mono_right (subset_univ Ω))).sub (hPk_smooth k)
  have hek_hol_z : ∀ k, ∀ r ∈ s, DifferentiableOn ℂ (fun z ↦ ek k (r, z)) (V k) :=
    fun k r hr ↦ (hd_hol_z k r hr).sub ((hPk_hol_z k r).mono ((inter_subset_left).trans (hWΩ k)))
  have hek_hol_q : ∀ k, ∀ p ∈ U_P, ∀ z, DifferentiableOn ℂ (fun q ↦ ek k ((p, q), z)) U_Q := by
    intro k p hp z
    exact (hd_hol_q k p hp z).sub
      (differentiableOn_sum_mul_smul_param (wk k) (gk k) (fun i ↦ hd_hol_q k p hp (ζk k i)) z)
  -- Key derivative estimate: for `m ≤ k`, `r ∈ B k`, `z ∈ C k`, `‖D^m (ek k) (r, z)‖ ≤ (1/2)^k`.
  have hek_deriv_le : ∀ k m, m ≤ k → ∀ r ∈ B k, ∀ z ∈ C k,
      ‖iteratedFDeriv ℝ m (ek k) (r, z)‖ ≤ (1 / 2 : ℝ) ^ k := by
    intro k m hm r hr z hz
    have hr_s : r ∈ s := hBs k hr
    have hint_sub_C : interior (C (k + 1)) ⊆ C (k + 1) := interior_subset
    have hint_sub_V : interior (C (k + 1)) ⊆ V k := hint_sub_C.trans (hCV k)
    have hint_sub_Ω : interior (C (k + 1)) ⊆ Ω := hint_sub_C.trans (hCΩ (k + 1))
    have hparam_bd : ∀ j ≤ m, ∀ ζ ∈ interior (C (k + 1)),
        ‖iteratedFDeriv ℝ j (fun r' ↦ ek k (r', ζ)) r‖ ≤ ε k * M k := by
      intro j hj ζ hζ
      have hj_k : j ≤ k := hj.trans hm
      have hv_cd : ∀ i : Fin (nk k), ContDiffOn ℝ j (fun r' ↦ d k r' (ζk k i)) s := fun i ↦
        ((hd_smooth k).of_le (by simp)).comp (contDiffOn_id.prodMk contDiffOn_const)
          fun r' hr' ↦ ⟨hr', mem_univ _⟩
      have hd_cd : ContDiffAt ℝ j (fun r' ↦ d k r' ζ) r :=
        (((hd_smooth k).contDiffAt ((hs.prod isOpen_univ).mem_nhds ⟨hr_s, mem_univ ζ⟩)).comp r
          (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp)
      have hP_cd : ContDiffAt ℝ j (fun r' ↦ Pk k (r', ζ)) r :=
        (((hPk_smooth k).contDiffAt
          ((hs.prod hΩ).mem_nhds ⟨hr_s, hint_sub_Ω hζ⟩)).comp r
          (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp)
      have heq_sub :
          iteratedFDeriv ℝ j (fun r' ↦ ek k (r', ζ)) r =
            iteratedFDeriv ℝ j (fun r' ↦ d k r' ζ) r -
              ∑ i : Fin (nk k), (wk k i * gk k i ζ) •
                iteratedFDeriv ℝ j (fun r' ↦ d k r' (ζk k i)) r := by
        -- Unfold `ek k` as the function difference `(fun r' ↦ d k r' ζ) - fun r' ↦ Pk k (r', ζ)`.
        change iteratedFDeriv ℝ j ((fun r' ↦ d k r' ζ) - fun r' ↦ Pk k (r', ζ)) r = _
        rw [iteratedFDeriv_sub_apply hd_cd hP_cd,
          iteratedFDeriv_sum_mul_smul_param hs (wk k) (gk k) hv_cd hr_s ζ]
      rw [heq_sub]
      have hψ_hol : DifferentiableOn ℂ
          (fun w ↦ iteratedFDeriv ℝ j (fun r' ↦ d k r' w) r) (interior (L k)) :=
        (differentiableOn_iteratedFDeriv_prod_left hs (hV_open k)
          ((hd_smooth k).mono (prod_mono_right (subset_univ _))) (hd_hol_z k) j hr_s).mono
          (interior_subset.trans (hLV k))
      have hψ_bd : ∀ w ∈ interior (L k),
          ‖iteratedFDeriv ℝ j (fun r' ↦ d k r' w) r‖ ≤ M k :=
        fun w hw ↦ hM_bd k j hj_k r hr w (interior_subset hw)
      exact hRunge k (fun w ↦ iteratedFDeriv ℝ j (fun r' ↦ d k r' w) r) (M k)
        hψ_hol hψ_bd ζ (hint_sub_C hζ)
    have htot := norm_iteratedFDeriv_prod_le_of_differentiableOn_snd hs isOpen_interior
      ((hek_smooth k).mono (prod_mono_right hint_sub_Ω))
      (fun r' hr' ↦ (hek_hol_z k r' hr').mono hint_sub_V) hr_s (hρ_pos k)
      (mul_nonneg (hε_pos k).le (hM_nonneg k)) m (hball_C k m hm z hz) hparam_bd
    refine htot.trans ?_
    have hpow_le : (1 + (ρ k)⁻¹) ^ m ≤ (1 + (ρ k)⁻¹) ^ k :=
      pow_le_pow_right₀ (by linarith [inv_nonneg.2 (hρ_pos k).le]) hm
    calc (1 + (ρ k)⁻¹) ^ m * (ε k * M k)
        ≤ (1 + (ρ k)⁻¹) ^ k * (ε k * (M k + 1)) := by
          refine mul_le_mul hpow_le
            (mul_le_mul_of_nonneg_left (by linarith) (hε_pos k).le)
            (mul_nonneg (hε_pos k).le (hM_nonneg k)) (pow_nonneg (h1ρ_pos k).le k)
      _ = (1 / 2 : ℝ) ^ k * (((1 + (ρ k)⁻¹) ^ k * (M k + 1)) /
            ((1 + (ρ k)⁻¹) ^ k * (M k + 1))) := by
          dsimp only [ε]
          ring
      _ = (1 / 2 : ℝ) ^ k := by rw [div_self (hdenom_pos k).ne', mul_one]
  -- Step 6: Assemble `u p = h 0 p.1 p.2 + ∑' k, ek k p` and verify smoothness, `Q`-holomorphy,
  -- and `\bar∂_z u = f`.
  let u : (P × Q) × ℂ → F := fun p ↦ h 0 p.1 p.2 + ∑' k, ek k p
  have hu_smooth : ContDiffOn ℝ ∞ u (s ×ˢ Ω) := by
    refine ((hh_smooth 0).mono (prod_mono_right (subset_univ Ω))).add ?_
    intro ⟨r₀, z₀⟩ ⟨hr₀, hz₀⟩
    obtain ⟨N, hrN, hzN⟩ := hexh r₀ hr₀ z₀ hz₀
    set O_N : Set ((P × Q) × ℂ) := interior (B N) ×ˢ interior (C N)
    have hON_open : IsOpen O_N := isOpen_interior.prod isOpen_interior
    have hON_sub : O_N ⊆ s ×ˢ Ω :=
      prod_mono (interior_subset.trans (hBs N)) (interior_subset.trans (hCΩ N))
    have htsum_ON : ContDiffOn ℝ ∞ (fun p ↦ ∑' k, ek k p) O_N := by
      refine contDiffOn_tsum_of_eventually_geometric hON_open
        (fun k ↦ (hek_smooth k).mono hON_sub) fun m ↦ ?_
      filter_upwards [eventually_ge_atTop (max m N)] with k hk ⟨r, z⟩ ⟨hr, hz⟩
      exact hek_deriv_le k m ((le_max_left m N).trans hk)
        r (hB_mono ((le_max_right m N).trans hk) (interior_subset hr))
        z (hC_mono ((le_max_right m N).trans hk) (interior_subset hz))
    exact (htsum_ON.contDiffAt (hON_open.mem_nhds ⟨hrN, hzN⟩)).contDiffWithinAt
  have hu_hol_q : ∀ p ∈ U_P, ∀ z ∈ Ω, DifferentiableOn ℂ (fun q ↦ u ((p, q), z)) U_Q := by
    intro p₀ hp₀ z₀ hz₀ q₀ hq₀
    obtain ⟨N, hrN, hzN⟩ := hexh (p₀, q₀) ⟨hp₀, hq₀⟩ z₀ hz₀
    let O_Q : Set Q := (fun q ↦ (p₀, q)) ⁻¹' interior (B N)
    have hOQ_open : IsOpen O_Q := isOpen_interior.preimage (Continuous.prodMk_right p₀)
    have hq₀_OQ : q₀ ∈ O_Q := hrN
    have hOQ_sub : O_Q ⊆ U_Q := fun q hq ↦ (hBs N (interior_subset hq)).2
    have hnorm_ek : ∀ k, N ≤ k → ∀ q ∈ O_Q, ‖ek k ((p₀, q), z₀)‖ ≤ (1 / 2 : ℝ) ^ k := by
      intro k hk q hq
      simpa only [norm_iteratedFDeriv_zero] using
        hek_deriv_le k 0 (Nat.zero_le k) (p₀, q) (hB_mono hk (interior_subset hq))
          z₀ (hC_mono hk (interior_subset hzN))
    let T : Finset ℕ := Finset.range N
    have hsum_q : ∀ q ∈ O_Q, Summable (fun k ↦ ek k ((p₀, q), z₀)) := by
      intro q hq
      refine Summable.of_norm_bounded_eventually
        (by simpa [one_div] using summable_geometric_two :
          Summable fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) ?_
      rw [Nat.cofinite_eq_atTop]
      filter_upwards [eventually_ge_atTop N] with k hk
      exact hnorm_ek k hk q hq
    have hsplit_q : EqOn (fun q ↦ u ((p₀, q), z₀))
        (fun q ↦ h 0 (p₀, q) z₀ + (∑ k ∈ T, ek k ((p₀, q), z₀)) +
          ∑' k : {k // k ∉ T}, ek k.1 ((p₀, q), z₀)) O_Q := by
      intro q hq
      simp only [u, add_assoc]
      congr 1
      exact ((hsum_q q hq).sum_add_tsum_subtype_compl T).symm
    have htail_unif : TendstoUniformlyOn
        (fun (F' : Finset {k // k ∉ T}) q ↦ ∑ k ∈ F', ek k.1 ((p₀, q), z₀))
        (fun q ↦ ∑' k : {k // k ∉ T}, ek k.1 ((p₀, q), z₀)) atTop O_Q := by
      refine tendstoUniformlyOn_tsum
        ((by simpa [one_div] using summable_geometric_two :
          Summable fun k : ℕ ↦ (1 / 2 : ℝ) ^ k).subtype _)
        fun k q hq ↦ hnorm_ek k.1 (Nat.le_of_not_lt (Finset.mem_range.not.1 k.2)) q hq
    have htail_hol : DifferentiableOn ℂ
        (fun q ↦ ∑' k : {k // k ∉ T}, ek k.1 ((p₀, q), z₀)) O_Q :=
      htail_unif.differentiableOn
        (Eventually.of_forall fun F' ↦ DifferentiableOn.fun_sum fun k _ ↦
          (hek_hol_q k.1 p₀ hp₀ z₀).mono hOQ_sub) hOQ_open
    have hh0_hol : DifferentiableOn ℂ (fun q ↦ h 0 (p₀, q) z₀) O_Q :=
      fun q hq ↦ (hh_hol_q 0 (p₀, q) ⟨hp₀, hOQ_sub hq⟩ z₀).differentiableWithinAt
    have hfin_hol : DifferentiableOn ℂ (fun q ↦ ∑ k ∈ T, ek k ((p₀, q), z₀)) O_Q :=
      DifferentiableOn.fun_sum fun k _ ↦ (hek_hol_q k p₀ hp₀ z₀).mono hOQ_sub
    have hu_OQ : DifferentiableOn ℂ (fun q ↦ u ((p₀, q), z₀)) O_Q :=
      ((hh0_hol.add hfin_hol).add htail_hol).congr hsplit_q
    exact (hu_OQ.differentiableAt (hOQ_open.mem_nhds hq₀_OQ)).differentiableWithinAt
  refine ⟨u, hu_smooth, hu_hol_q, fun p₀ hp₀ q₀ hq₀ z₀ hz₀ ↦ ?_⟩
  set r₀ : P × Q := (p₀, q₀)
  have hr₀ : r₀ ∈ s := ⟨hp₀, hq₀⟩
  obtain ⟨N, hrN, hzN⟩ := hexh r₀ hr₀ z₀ hz₀
  set U₀ : Set ℂ := interior (C N)
  have hU₀_open : IsOpen U₀ := isOpen_interior
  let T : Finset ℕ := Finset.range N
  have hnorm_z : ∀ k, N ≤ k → ∀ z ∈ U₀, ‖ek k (r₀, z)‖ ≤ (1 / 2 : ℝ) ^ k := by
    intro k hk z hz
    simpa only [norm_iteratedFDeriv_zero] using
      hek_deriv_le k 0 (Nat.zero_le k) r₀ (hB_mono hk (interior_subset hrN))
        z (hC_mono hk (interior_subset hz))
  have hsum_z : ∀ z ∈ U₀, Summable (fun k ↦ ek k (r₀, z)) := by
    intro z hz
    refine Summable.of_norm_bounded_eventually
      (by simpa [one_div] using summable_geometric_two :
        Summable fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop N] with k hk
    exact hnorm_z k hk z hz
  let Psum : ℂ → F := fun z ↦ ∑ k ∈ T, Pk k (r₀, z)
  let tail : ℂ → F := fun z ↦ ∑' k : {k // k ∉ T}, ek k.1 (r₀, z)
  have hu_decomp : (fun w ↦ u (r₀, w)) =ᶠ[𝓝 z₀] fun w ↦ h N r₀ w - Psum w + tail w := by
    filter_upwards [hU₀_open.mem_nhds hzN] with w hw
    have hts : (∑' k, ek k (r₀, w)) = (∑ k ∈ T, ek k (r₀, w)) + tail w :=
      ((hsum_z w hw).sum_add_tsum_subtype_compl T).symm
    have htel := add_sum_range_sub_sub (fun k ↦ h k r₀ w) (fun k ↦ Pk k (r₀, w)) N
    dsimp only [u, ek, d, Psum, tail, T] at htel hts ⊢
    rw [hts, ← add_assoc, htel]
  have htail_unif : TendstoUniformlyOn
      (fun (F' : Finset {k // k ∉ T}) z ↦ ∑ k ∈ F', ek k.1 (r₀, z)) tail atTop U₀ :=
    tendstoUniformlyOn_tsum
      ((by simpa [one_div] using summable_geometric_two :
        Summable fun k : ℕ ↦ (1 / 2 : ℝ) ^ k).subtype _)
      fun k z hz ↦ hnorm_z k.1 (Nat.le_of_not_lt (Finset.mem_range.not.1 k.2)) z hz
  have htail_hol : DifferentiableOn ℂ tail U₀ := by
    refine htail_unif.differentiableOn (Eventually.of_forall fun F' ↦ ?_) hU₀_open
    refine DifferentiableOn.fun_sum fun k _ ↦ (hek_hol_z k.1 r₀ hr₀).mono ?_
    have hkN : N ≤ k.1 := Nat.le_of_not_lt (Finset.mem_range.not.1 k.2)
    exact (interior_subset.trans (hC_mono (hkN.trans (Nat.le_succ k.1)))).trans (hCV k.1)
  have htail_diff : DifferentiableAt ℂ tail z₀ := htail_hol.differentiableAt (hU₀_open.mem_nhds hzN)
  have hPsum_diff : DifferentiableAt ℂ Psum z₀ :=
    (DifferentiableOn.fun_sum fun k _ ↦ hPk_hol_z k r₀).differentiableAt (hΩ.mem_nhds hz₀)
  have hhN_diff : DifferentiableAt ℝ (h N r₀) z₀ :=
    (((hh_smooth N).contDiffAt ((hs.prod isOpen_univ).mem_nhds ⟨hr₀, mem_univ z₀⟩)).comp z₀
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  rw [hu_decomp.conjWirtingerDeriv_eq]
  -- Rewrite the pointwise expression as the function sum `((h N r₀ - Psum) + tail)`.
  change conjWirtingerDeriv ((h N r₀ - Psum) + tail) z₀ 1 = f (r₀, z₀)
  rw [conjWirtingerDeriv_add (hhN_diff.sub (hPsum_diff.restrictScalars ℝ))
    (htail_diff.restrictScalars ℝ), add_apply,
    conjWirtingerDeriv_sub hhN_diff (hPsum_diff.restrictScalars ℝ),
    sub_apply, hPsum_diff.conjWirtingerDeriv_eq_zero,
    htail_diff.conjWirtingerDeriv_eq_zero]
  simp only [zero_apply, sub_zero, add_zero]
  exact hW_eq N z₀ (hCW N (hC_mono (Nat.le_succ N) (interior_subset hzN))) r₀ hr₀

/-- **Global `\bar∂`-lemma on any open subset of `ℂ`.** Every `C^∞` map `f : ℂ → F` on an open set
`Ω ⊆ ℂ` with values in a complex Banach space `F` has a `C^∞` potential `u : ℂ → F` on `Ω`
satisfying `conjWirtingerDeriv u z 1 = f z` for every `z ∈ Ω`. -/
theorem _root_.IsOpen.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → F} (hf : ContDiffOn ℝ ∞ f Ω) :
    ∃ u : ℂ → F, ContDiffOn ℝ ∞ u Ω ∧ ∀ z ∈ Ω, conjWirtingerDeriv u z 1 = f z := by
  obtain ⟨u₀, hu₀_smooth, -, hu₀_dbar⟩ :=
    exists_contDiffOn_differentiableOn_conjWirtingerDeriv_apply_one_eq
      (P := ℝ) (Q := ℂ) (U_P := univ) (U_Q := univ) (f := fun p ↦ f p.2)
      isOpen_univ isOpen_univ hΩ (hf.comp contDiffOn_snd fun _ hp ↦ hp.2)
      (fun _ _ z _ ↦ differentiableOn_const (f z))
  refine ⟨fun z ↦ u₀ ((0, 0), z), hu₀_smooth.comp (contDiffOn_const.prodMk contDiffOn_id)
    fun z hz ↦ ⟨⟨mem_univ _, mem_univ _⟩, hz⟩,
    fun z hz ↦ hu₀_dbar 0 (mem_univ _) 0 (mem_univ _) z hz⟩

/-- **Global planar `\bar∂` solver with smooth parameters.** For a finite-dimensional real normed
space `P`, a complex Banach space `F`, open sets `s ⊆ P` and `Ω ⊆ ℂ`, and `f : P → ℂ → F` jointly
`C^∞` on `s ×ˢ Ω`, there exists `u : P → ℂ → F` jointly `C^∞` on `s ×ˢ Ω` with
`conjWirtingerDeriv (u p) z 1 = f p z` everywhere on `s ×ˢ Ω`. -/
theorem exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_with_param
    {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {s : Set P} {Ω : Set ℂ} {f : P → ℂ → F}
    (hs : IsOpen s) (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ ↿f (s ×ˢ Ω)) :
    ∃ u : P → ℂ → F, ContDiffOn ℝ ∞ ↿u (s ×ˢ Ω) ∧
      ∀ p ∈ s, ∀ z ∈ Ω, conjWirtingerDeriv (u p) z 1 = f p z := by
  obtain ⟨u₀, hu₀_smooth, -, hu₀_dbar⟩ :=
    exists_contDiffOn_differentiableOn_conjWirtingerDeriv_apply_one_eq
      (P := P) (Q := ℂ) (U_P := s) (U_Q := univ) (f := fun q ↦ f q.1.1 q.2)
      hs isOpen_univ hΩ
      (hf.comp ((contDiffOn_fst.comp contDiffOn_fst (mapsTo_univ _ _)).prodMk contDiffOn_snd)
        fun _ hq ↦ ⟨hq.1.1, hq.2⟩)
      (fun p _ z _ ↦ differentiableOn_const (f p z))
  refine ⟨fun p z ↦ u₀ ((p, 0), z), ?_, fun p hp z hz ↦ hu₀_dbar p hp 0 (mem_univ _) z hz⟩
  exact hu₀_smooth.comp ((contDiffOn_fst.prodMk contDiffOn_const).prodMk contDiffOn_snd)
    fun _ hp ↦ ⟨⟨hp.1, mem_univ _⟩, hp.2⟩

/-- **Global planar `\bar∂` solver with holomorphic parameters.** For a finite-dimensional complex
normed space `Q`, a complex Banach space `F`, open sets `s ⊆ Q` and `Ω ⊆ ℂ`, and `f : Q → ℂ → F`
jointly `C^∞` on `s ×ˢ Ω` and holomorphic in `q ∈ s` for every `z ∈ Ω`, there exists
`u : Q → ℂ → F` jointly `C^∞` on `s ×ˢ Ω`, holomorphic in `q ∈ s` for every `z ∈ Ω`, and solving
`conjWirtingerDeriv (u q) z 1 = f q z` everywhere on `s ×ˢ Ω`. -/
theorem exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_with_holomorphic_param
    {Q F : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] [FiniteDimensional ℂ Q]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {s : Set Q} {Ω : Set ℂ} {f : Q → ℂ → F}
    (hs : IsOpen s) (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ ↿f (s ×ˢ Ω))
    (hfq : ∀ z ∈ Ω, DifferentiableOn ℂ (fun q ↦ f q z) s) :
    ∃ u : Q → ℂ → F, ContDiffOn ℝ ∞ ↿u (s ×ˢ Ω) ∧
      (∀ z ∈ Ω, DifferentiableOn ℂ (fun q ↦ u q z) s) ∧
      ∀ q ∈ s, ∀ z ∈ Ω, conjWirtingerDeriv (u q) z 1 = f q z := by
  obtain ⟨u₀, hu₀_smooth, hu₀_hol, hu₀_dbar⟩ :=
    exists_contDiffOn_differentiableOn_conjWirtingerDeriv_apply_one_eq
      (P := ℝ) (Q := Q) (U_P := univ) (U_Q := s) (f := fun r ↦ f r.1.2 r.2)
      isOpen_univ hs hΩ
      (hf.comp ((contDiffOn_snd.comp contDiffOn_fst (mapsTo_univ _ _)).prodMk contDiffOn_snd)
        fun _ hr ↦ ⟨hr.1.2, hr.2⟩)
      (fun _ _ z hz ↦ hfq z hz)
  refine ⟨fun q z ↦ u₀ ((0, q), z), ?_, fun z hz ↦ hu₀_hol 0 (mem_univ _) z hz,
    fun q hq z hz ↦ hu₀_dbar 0 (mem_univ _) q hq z hz⟩
  exact hu₀_smooth.comp ((contDiffOn_const.prodMk contDiffOn_fst).prodMk contDiffOn_snd)
    fun _ hq ↦ ⟨⟨mem_univ _, hq.1⟩, hq.2⟩

end NormedParameterSolver

end TauCeti
