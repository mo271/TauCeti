/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import TauCeti.Analysis.Fredholm.SeparableKernel

/-!
# Separable integral operators on `L²`

For finite families `f, g : ι → Lp 𝕜 2 μ` on an arbitrary measure space `(α, μ)` over an `RCLike`
scalar field `𝕜`, the Hilbert-space separable operator
`TauCeti.hilbertSeparableOperator 𝕜 f g : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ` sends `u` to
`∑ j, ⟪g j, u⟫_𝕜 • f j` using Mathlib's conjugate-first inner product
`⟪g j, u⟫_𝕜 = ∫ y, conj (g j y) * u y ∂μ`.

Without any continuity or finiteness assumption on `μ`, `f j`, or `g j`, this operator:
* agrees `μ`-almost everywhere with integration against the separable kernel
  `k(x, y) = ∑ j, f j x * conj (g j y)` (`TauCeti.coeFn_hilbertSeparableOperator`), and on a
  restricted measure `μ.restrict s` (such as a finite interval `s = Set.Icc a b`) with the set
  integral `∫ y in s, (∑ j, f j x * conj (g j y)) * u y ∂μ`
  (`TauCeti.coeFn_hilbertSeparableOperator_restrict`);
* inherits the operator-norm bound `‖hilbertSeparableOperator 𝕜 f g‖ ≤ ∑ j, ‖f j‖ * ‖g j‖`, finite
  rank, Fredholmness of `1 + hilbertSeparableOperator 𝕜 f g` with index `0`, and the Hilbert
  Fredholm alternative (`TauCeti.alternative_one_add_hilbertSeparableOperator`) from
  `TauCeti.Analysis.Fredholm.SeparableKernel`;
* reduces `(1 + hilbertSeparableOperator 𝕜 f g) u = h` to the finite integral moment system
  `c i + ∑ j, (∫ y, conj (g i y) * f j y ∂μ) * c j = ∫ y, conj (g i y) * h y ∂μ` with
  `c i = ∫ y, conj (g i y) * u y ∂μ` and `u = h - ∑ j, c j • f j`
  (`TauCeti.one_add_hilbertSeparableOperator_lp_eq_iff`), with integral-form compatibility
  conditions (`TauCeti.exists_one_add_hilbertSeparableOperator_lp_eq_iff` and
  `TauCeti.exists_one_add_hilbertSeparableOperator_lp_eq_iff_forall_integral_eq_zero`);
* intertwines with `TauCeti.continuousSesqSeparableOperator` along `ContinuousMap.toLp 2 μ 𝕜` on any
  compact finite Borel measure space (`TauCeti.toLp_continuousSesqSeparableOperator`).

We also record the concrete rank-one probability-measure checks (applicable in particular to
`volume : Measure unitInterval` on `[0, 1]`): the constant factor `f = g = const i` yields
`K u = const (∫ u)` and bijective `1 + K` sending `const c` to `const (2 * c)`, while `f = const 1`
and `g = const (-1)` satisfy `1 + ⟪g 0, f 0⟫ = 0`, `ker (1 + K) = 𝕜 ∙ const 1`, Fredholm index `0`,
and exact solvability `(∃ u, (1 + K) u = h) ↔ ∫ y, h y ∂μ = 0`.

## Main declarations

* `TauCeti.integrable_separableKernel_mul`: integrability of
  `y ↦ (∑ j, f j x * conj (g j y)) * u y` for every `x : α` and `f j, g j, u ∈ Lp 𝕜 2 μ`.
* `TauCeti.coeFn_hilbertSeparableOperator`, `TauCeti.coeFn_hilbertSeparableOperator_restrict`:
  almost-everywhere integral and set-integral representations of `hilbertSeparableOperator 𝕜 f g u`.
* `TauCeti.one_add_hilbertSeparableOperator_lp_eq_iff`: finite integral moment reduction and
  reconstruction `u = h - ∑ j, c j • f j` without continuity hypotheses.
* `TauCeti.exists_one_add_hilbertSeparableOperator_lp_eq_iff`,
  `TauCeti.exists_one_add_hilbertSeparableOperator_lp_eq_iff_forall_integral_eq_zero`: matrix and
  adjoint-kernel integral compatibility conditions on `Lp 𝕜 2 μ`.
* `TauCeti.toLp_continuousSesqSeparableOperator`: intertwining of
  `continuousSesqSeparableOperator` and `hilbertSeparableOperator` via `ContinuousMap.toLp`.
* `TauCeti.hilbertSeparableOperator_const_I_prob`,
  `TauCeti.one_add_hilbertSeparableOperator_const_one_neg_one_prob`: rank-one checks for
  `f = g = const i` and `f = const 1, g = const (-1)` on a probability space (such as `[0, 1]`).

## References

* F. Riesz, B. Sz.-Nagy, *Functional Analysis*, §§69–71.
* R. Kress, *Linear Integral Equations*, 3rd ed., Chapter 3, §3.1 and §3.3.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Chapter 6.
-/

public section

noncomputable section

open MeasureTheory ContinuousLinearMap
open scoped InnerProduct InnerProductSpace ComplexConjugate

namespace TauCeti

section ArbitraryMeasure

variable {α 𝕜 ι : Type*} [MeasurableSpace α] {μ : Measure α} [RCLike 𝕜]

/-- On `Lp 𝕜 2 μ`, the conjugate-first inner product is `⟪g, u⟫_𝕜 = ∫ y, conj (g y) * u y ∂μ`. -/
theorem inner_lp_eq_integral (g u : Lp 𝕜 2 μ) :
    ⟪g, u⟫_𝕜 = ∫ y, conj (g y) * u y ∂μ := by
  simp_rw [L2.inner_def, RCLike.inner_apply']

/-- For `g, u ∈ Lp 𝕜 2 μ`, the pointwise product `y ↦ conj (g y) * u y` is `μ`-integrable. -/
theorem integrable_conj_mul_lp (g u : Lp 𝕜 2 μ) :
    Integrable (fun y ↦ conj (g y) * u y) μ := by
  simpa only [RCLike.inner_apply'] using L2.integrable_inner (𝕜 := 𝕜) g u

/-- Entrywise integral formula for `TauCeti.hilbertSeparableMatrix` on `Lp 𝕜 2 μ`. -/
theorem hilbertSeparableMatrix_lp_apply (f g : ι → Lp 𝕜 2 μ) (i j : ι) :
    hilbertSeparableMatrix 𝕜 f g i j = ∫ y, conj (g i y) * f j y ∂μ := by
  rw [hilbertSeparableMatrix_apply, inner_lp_eq_integral]

section Fintype

variable [Fintype ι]

/-- For `f, g : ι → Lp 𝕜 2 μ`, `u : Lp 𝕜 2 μ`, and every point `x : α`, the separable-kernel
integrand `y ↦ (∑ j, f j x * conj (g j y)) * u y` is `μ`-integrable. -/
theorem integrable_separableKernel_mul (f g : ι → Lp 𝕜 2 μ) (u : Lp 𝕜 2 μ) (x : α) :
    Integrable (fun y ↦ (∑ j, f j x * conj (g j y)) * u y) μ := by
  have hEq : (fun y ↦ (∑ j, f j x * conj (g j y)) * u y) =
      fun y ↦ ∑ j, f j x * (conj (g j y) * u y) := by
    ext y
    simp_rw [Finset.sum_mul, mul_assoc]
  rw [hEq]
  exact integrable_finsetSum _ fun j _ ↦ (integrable_conj_mul_lp (g j) u).const_mul (f j x)

/-- **Almost-everywhere integral representation on `Lp 𝕜 2 μ`.** For `f, g : ι → Lp 𝕜 2 μ` and
`u : Lp 𝕜 2 μ`, `hilbertSeparableOperator 𝕜 f g u` agrees `μ`-almost everywhere with integration
against `∑ j, f j x * conj (g j y)`, with no continuity or finiteness assumption on `μ`. -/
theorem coeFn_hilbertSeparableOperator (f g : ι → Lp 𝕜 2 μ) (u : Lp 𝕜 2 μ) :
    ∀ᵐ x ∂μ, hilbertSeparableOperator 𝕜 f g u x =
      ∫ y, (∑ j, f j x * conj (g j y)) * u y ∂μ := by
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ (fun j ↦ ⟪g j, u⟫_𝕜 • f j)
  have hsmul : ∀ᵐ x ∂μ, ∀ j, (⟪g j, u⟫_𝕜 • f j) x = ⟪g j, u⟫_𝕜 * f j x :=
    Filter.eventually_all.mpr fun j ↦ Lp.coeFn_smul _ (f j)
  filter_upwards [hsum, hsmul] with x hx_sum hx_smul
  rw [hilbertSeparableOperator_apply, hx_sum]
  calc ∑ j, (⟪g j, u⟫_𝕜 • f j) x
      = ∑ j, f j x * ∫ y, conj (g j y) * u y ∂μ :=
        Finset.sum_congr rfl fun j _ ↦ by rw [hx_smul j, inner_lp_eq_integral, mul_comm]
    _ = ∑ j, ∫ y, f j x * (conj (g j y) * u y) ∂μ :=
        Finset.sum_congr rfl fun j _ ↦ (integral_const_mul _ _).symm
    _ = ∫ y, ∑ j, f j x * (conj (g j y) * u y) ∂μ :=
        (integral_finsetSum _ fun j _ ↦
          (integrable_conj_mul_lp (g j) u).const_mul (f j x)).symm
    _ = ∫ y, (∑ j, f j x * conj (g j y)) * u y ∂μ := by
        congr 1 with y
        simp_rw [Finset.sum_mul, mul_assoc]

/-- **Set-integral representation on `Lp 𝕜 2 (μ.restrict s)`.** In particular, for `s = Set.Icc a b`
this gives the `L²[a, b]` integral representation on a finite interval. -/
theorem coeFn_hilbertSeparableOperator_restrict (s : Set α)
    (f g : ι → Lp 𝕜 2 (μ.restrict s)) (u : Lp 𝕜 2 (μ.restrict s)) :
    ∀ᵐ x ∂μ.restrict s, hilbertSeparableOperator 𝕜 f g u x =
      ∫ y in s, (∑ j, f j x * conj (g j y)) * u y ∂μ :=
  coeFn_hilbertSeparableOperator f g u

/-- If `(1 + hilbertSeparableOperator 𝕜 f g) u = h` in `Lp 𝕜 2 μ`, then the moments
`c i = ∫ y, conj (g i y) * u y ∂μ` satisfy the finite linear system
`c i + ∑ j, (∫ y, conj (g i y) * f j y ∂μ) * c j = ∫ y, conj (g i y) * h y ∂μ` and reconstruct
`u = h - ∑ j, c j • f j`. -/
theorem moment_eq_of_one_add_hilbertSeparableOperator_lp_eq {f g : ι → Lp 𝕜 2 μ}
    {u h : Lp 𝕜 2 μ} (hu : (1 + hilbertSeparableOperator 𝕜 f g) u = h) :
    (∀ i, (∫ y, conj (g i y) * u y ∂μ) +
        ∑ j, (∫ y, conj (g i y) * f j y ∂μ) * (∫ y, conj (g j y) * u y ∂μ) =
      ∫ y, conj (g i y) * h y ∂μ) ∧
      u = h - ∑ j, (∫ y, conj (g j y) * u y ∂μ) • f j := by
  simpa only [inner_lp_eq_integral] using
    inner_eq_of_one_add_hilbertSeparableOperator_eq hu

/-- **Finite integral moment reduction on `Lp 𝕜 2 μ` without continuity.** -/
theorem one_add_hilbertSeparableOperator_lp_eq_iff (f g : ι → Lp 𝕜 2 μ) (u h : Lp 𝕜 2 μ) :
    (1 + hilbertSeparableOperator 𝕜 f g) u = h ↔
      ∃ c : ι → 𝕜,
        (∀ i, c i + ∑ j, (∫ y, conj (g i y) * f j y ∂μ) * c j = ∫ y, conj (g i y) * h y ∂μ) ∧
        u = h - ∑ j, c j • f j := by
  simpa only [inner_lp_eq_integral] using
    one_add_hilbertSeparableOperator_eq_iff 𝕜 f g u h

/-- **Matrix-form solvability condition on `Lp 𝕜 2 μ` without continuity.** -/
theorem exists_one_add_hilbertSeparableOperator_lp_eq_iff (f g : ι → Lp 𝕜 2 μ)
    (h : Lp 𝕜 2 μ) :
    (∃ u, (1 + hilbertSeparableOperator 𝕜 f g) u = h) ↔
      ∀ d : ι → 𝕜,
        (∀ j, d j + ∑ i, d i * (∫ y, conj (g i y) * f j y ∂μ) = 0) →
        ∑ i, d i * (∫ y, conj (g i y) * h y ∂μ) = 0 := by
  simpa only [inner_lp_eq_integral] using
    exists_one_add_hilbertSeparableOperator_eq_iff_matrix 𝕜 f g h

/-- **Adjoint-kernel integral compatibility condition on `Lp 𝕜 2 μ` without continuity.** Because
`Lp 𝕜 2 μ` is complete and `(1 + hilbertSeparableOperator 𝕜 f g)† =
1 + hilbertSeparableOperator 𝕜 g f`, `(1 + hilbertSeparableOperator 𝕜 f g) u = h` is solvable in
`Lp 𝕜 2 μ` if and only if `∫ y, conj (z y) * h y ∂μ = 0` for every `z` in
`ker (1 + hilbertSeparableOperator 𝕜 g f)`. -/
theorem exists_one_add_hilbertSeparableOperator_lp_eq_iff_forall_integral_eq_zero
    (f g : ι → Lp 𝕜 2 μ) (h : Lp 𝕜 2 μ) :
    (∃ u, (1 + hilbertSeparableOperator 𝕜 f g) u = h) ↔
      ∀ z ∈ LinearMap.ker
          ((1 + hilbertSeparableOperator 𝕜 g f : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ) :
            Lp 𝕜 2 μ →ₗ[𝕜] Lp 𝕜 2 μ),
        ∫ y, conj (z y) * h y ∂μ = 0 := by
  simpa only [inner_lp_eq_integral] using
    exists_one_add_hilbertSeparableOperator_eq_iff_ker_adjoint 𝕜 f g h

end Fintype

end ArbitraryMeasure

section Intertwining

variable {X 𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι]
  [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- On a compact space equipped with a finite Borel measure `μ`, `ContinuousMap.toLp 2 μ 𝕜`
intertwines the conjugate-first continuous separable integral operator
`TauCeti.continuousSesqSeparableOperator` with `TauCeti.hilbertSeparableOperator`. -/
theorem toLp_continuousSesqSeparableOperator (μ : Measure X) [IsFiniteMeasure μ]
    (a g : ι → C(X, 𝕜)) (u : C(X, 𝕜)) :
    ContinuousMap.toLp 2 μ 𝕜 (continuousSesqSeparableOperator μ a g u) =
      hilbertSeparableOperator 𝕜 (fun j ↦ ContinuousMap.toLp 2 μ 𝕜 (a j))
        (fun j ↦ ContinuousMap.toLp 2 μ 𝕜 (g j)) (ContinuousMap.toLp 2 μ 𝕜 u) := by
  rw [continuousSesqSeparableOperator_apply, hilbertSeparableOperator_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul, ContinuousMap.inner_toLp]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun y ↦ mul_comm _ _)

end Intertwining

section ProbabilityChecks

variable {α 𝕜 : Type*} [MeasurableSpace α] (μ : Measure α) [RCLike 𝕜]

/-- Every `Lp 𝕜 2 μ` function on a finite-measure space is `μ`-integrable. -/
theorem integrable_of_lp_two [IsFiniteMeasure μ] (u : Lp 𝕜 2 μ) : Integrable u μ := by
  refine (integrable_conj_mul_lp (Lp.const 2 μ (1 : 𝕜)) u).congr ?_
  filter_upwards [Lp.coeFn_const 2 μ (1 : 𝕜)] with y hy
  rw [hy, Function.const_apply, map_one, one_mul]

/-- Pairing a constant `Lp 𝕜 2 μ` function on a finite-measure space against `u : Lp 𝕜 2 μ` extracts
`conj c * ∫ y, u y ∂μ`. -/
theorem inner_lp_const_left [IsFiniteMeasure μ] (c : 𝕜) (u : Lp 𝕜 2 μ) :
    ⟪Lp.const 2 μ c, u⟫_𝕜 = conj c * ∫ y, u y ∂μ := by
  rw [inner_lp_eq_integral, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_const 2 μ c] with y hy
  rw [hy, Function.const_apply]

/-- Inner product of two constant `Lp 𝕜 2 μ` functions on a finite-measure space. -/
theorem inner_lp_const_const [IsFiniteMeasure μ] (c d : 𝕜) :
    ⟪Lp.const 2 μ c, Lp.const 2 μ d⟫_𝕜 = μ.real Set.univ * (conj c * d) := by
  rw [inner_lp_const_left]
  have hint : ∫ y, (Lp.const 2 μ d) y ∂μ = μ.real Set.univ * d := by
    calc ∫ y, (Lp.const 2 μ d) y ∂μ
        = ∫ _, d ∂μ := integral_congr_ae (Lp.coeFn_const 2 μ d)
      _ = μ.real Set.univ • d := integral_const d
      _ = μ.real Set.univ * d := RCLike.real_smul_eq_coe_mul _ _
  rw [hint]
  ring

/-- **Constant-`i` check on `L²` of a probability space (such as `[0, 1]`).** For
`f = fun _ : Fin 1 ↦ Lp.const 2 μ Complex.I` on a probability space `(α, μ)`, the conjugate-first
separable operator satisfies `K u = Lp.const 2 μ (∫ y, u y ∂μ)`, so `1 + K` sends `Lp.const 2 μ c`
to `Lp.const 2 μ (2 * c)` and is bijective. -/
theorem hilbertSeparableOperator_const_I_prob [IsProbabilityMeasure μ] :
    let f : Fin 1 → Lp ℂ 2 μ := fun _ ↦ Lp.const 2 μ Complex.I
    (∀ u : Lp ℂ 2 μ, hilbertSeparableOperator ℂ f f u = Lp.const 2 μ (∫ y, u y ∂μ)) ∧
      (∀ c : ℂ, (1 + hilbertSeparableOperator ℂ f f) (Lp.const 2 μ c) =
        Lp.const 2 μ (2 * c)) ∧
      Function.Bijective
        (1 + hilbertSeparableOperator ℂ f f : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := by
  intro f
  have hK (u : Lp ℂ 2 μ) : hilbertSeparableOperator ℂ f f u = Lp.const 2 μ (∫ y, u y ∂μ) := by
    rw [hilbertSeparableOperator_apply, Finset.univ_unique, Finset.sum_singleton]
    simp only [f, inner_lp_const_left, Complex.conj_I]
    calc (-Complex.I * ∫ y, u y ∂μ) • Lp.const 2 μ Complex.I
        = Lp.const 2 μ ((-Complex.I * ∫ y, u y ∂μ) * Complex.I) := by
          simpa only [Lp.constₗ_apply, smul_eq_mul] using
            ((Lp.constₗ 2 μ ℂ).map_smul (-Complex.I * ∫ y, u y ∂μ) Complex.I).symm
      _ = Lp.const 2 μ (∫ y, u y ∂μ) := by
          congr 1
          calc (-Complex.I * ∫ y, u y ∂μ) * Complex.I
              = -(Complex.I * Complex.I) * ∫ y, u y ∂μ := by ring
            _ = ∫ y, u y ∂μ := by simp
  have hconst (c : ℂ) : (1 + hilbertSeparableOperator ℂ f f) (Lp.const 2 μ c) =
      Lp.const 2 μ (2 * c) := by
    rw [add_apply, one_apply_eq_self, hK]
    have hint : ∫ y, (Lp.const 2 μ c) y ∂μ = c := by
      calc ∫ y, (Lp.const 2 μ c) y ∂μ
          = ∫ _, c ∂μ := integral_congr_ae (Lp.coeFn_const 2 μ c)
        _ = c := by simp [probReal_univ]
    rw [hint, ← map_add (Lp.const 2 μ) c c, two_mul]
  have hdet : (1 + hilbertSeparableMatrix ℂ f f).det ≠ 0 := by
    rw [Matrix.det_unique, Matrix.add_apply, Matrix.one_apply_eq, hilbertSeparableMatrix_apply]
    dsimp only [f]
    rw [inner_lp_const_const, probReal_univ]
    norm_num
  exact ⟨hK, hconst,
    (bijective_one_add_hilbertSeparableOperator_iff_det_ne_zero ℂ f f).mpr hdet⟩

/-- **Resonant rank-one check `f = const 1`, `g = const (-1)` on `L²` of a probability space (such
as `[0, 1]`).** Here `1 + ⟪g 0, f 0⟫_𝕜 = 0`, the kernel of `1 + K` is the `1`-dimensional line
`𝕜 ∙ Lp.const 2 μ 1`, the Fredholm index of `1 + K` is `0`, and `(1 + K) u = h` is solvable in
`Lp 𝕜 2 μ` if and only if `∫ y, h y ∂μ = 0`. -/
theorem one_add_hilbertSeparableOperator_const_one_neg_one_prob [IsProbabilityMeasure μ] :
    let f : Fin 1 → Lp 𝕜 2 μ := fun _ ↦ Lp.const 2 μ 1
    let g : Fin 1 → Lp 𝕜 2 μ := fun _ ↦ Lp.const 2 μ (-1)
    1 + ⟪g 0, f 0⟫_𝕜 = 0 ∧
      LinearMap.ker
          ((1 + hilbertSeparableOperator 𝕜 f g : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ) :
            Lp 𝕜 2 μ →ₗ[𝕜] Lp 𝕜 2 μ) =
        (𝕜 ∙ Lp.const 2 μ (1 : 𝕜)) ∧
      ContinuousLinearMap.index (1 + hilbertSeparableOperator 𝕜 f g) = 0 ∧
      ∀ h : Lp 𝕜 2 μ, (∃ u, (1 + hilbertSeparableOperator 𝕜 f g) u = h) ↔
        ∫ y, h y ∂μ = 0 := by
  intro f g
  have hgf : 1 + ⟪g 0, f 0⟫_𝕜 = 0 := by
    dsimp only [f, g]
    rw [inner_lp_const_const, probReal_univ]
    simp
  have happly (u : Lp 𝕜 2 μ) :
      (1 + hilbertSeparableOperator 𝕜 f g) u = u - (∫ y, u y ∂μ) • Lp.const 2 μ 1 := by
    rw [add_apply, one_apply_eq_self, hilbertSeparableOperator_apply, Finset.univ_unique,
      Finset.sum_singleton]
    dsimp only [f, g]
    rw [inner_lp_const_left, map_neg, map_one, neg_one_mul, neg_smul, sub_eq_add_neg]
  have hconst_int (c : 𝕜) : ∫ y, (c • Lp.const 2 μ (1 : 𝕜)) y ∂μ = c := by
    have hc : c • Lp.const 2 μ (1 : 𝕜) = Lp.const 2 μ c := by
      simpa only [Lp.constₗ_apply, smul_eq_mul, mul_one] using
        ((Lp.constₗ 2 μ 𝕜).map_smul c (1 : 𝕜)).symm
    rw [hc]
    calc ∫ y, (Lp.const 2 μ c) y ∂μ
        = ∫ _, c ∂μ := integral_congr_ae (Lp.coeFn_const 2 μ c)
      _ = c := by simp [probReal_univ]
  have hker : LinearMap.ker
      ((1 + hilbertSeparableOperator 𝕜 f g : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ) :
        Lp 𝕜 2 μ →ₗ[𝕜] Lp 𝕜 2 μ) = (𝕜 ∙ Lp.const 2 μ (1 : 𝕜)) := by
    ext u
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, happly, sub_eq_zero,
      Submodule.mem_span_singleton]
    refine ⟨fun hu ↦ ⟨∫ y, u y ∂μ, hu.symm⟩, ?_⟩
    rintro ⟨c, rfl⟩
    rw [hconst_int c]
  refine ⟨hgf, hker, index_one_add_hilbertSeparableOperator 𝕜 f g, fun h ↦ ?_⟩
  refine ⟨?_, fun hh ↦ ⟨h, by rw [happly, hh, zero_smul, sub_zero]⟩⟩
  rintro ⟨u, rfl⟩
  rw [happly]
  have hsub : ∫ y, (u - (∫ z, u z ∂μ) • Lp.const 2 μ (1 : 𝕜)) y ∂μ =
      (∫ y, u y ∂μ) - ∫ y, ((∫ z, u z ∂μ) • Lp.const 2 μ (1 : 𝕜)) y ∂μ :=
    (integral_congr_ae (Lp.coeFn_sub _ _)).trans
      (integral_sub (integrable_of_lp_two μ u) (integrable_of_lp_two μ _))
  rw [hsub, hconst_int, sub_self]

end ProbabilityChecks

end TauCeti

end
