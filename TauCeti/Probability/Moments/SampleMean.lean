/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Moments.Covariance
public import TauCeti.MeasureTheory.Function.L2Space
public import TauCeti.Analysis.Convex.FiniteMean

/-!
# Second moments of sample means

Let `X₁, …, X_r` be pairwise independent, square-integrable random vectors in a real Hilbert space
with a common mean `m`. Their sample mean `S = r⁻¹ ∑ₖ Xₖ` has mean-square error

`∫ ‖S - m‖² dP = r⁻² ∑ₖ ∫ ‖Xₖ - m‖² dP`,

so that averaging `r` samples with a common per-sample error `γ` divides it by `r`. Together with
Chebyshev's inequality for the second moment, `TauCeti.meas_ge_le_integral_norm_sq_div_sq` in
`TauCeti.Probability.Moments.Chebyshev`, this is the scale `1 / r` behind the elementary
concentration of empirical moments.

The identity rests on Bienaymé's identity for random vectors: the squared norm of a sum of
pairwise independent, centered, square-integrable random vectors has expectation equal to the
sum of the expected squared norms. Only pairwise independence is used, through the factorization
`∫ ⟪Xᵢ, Xⱼ⟫ = ⟪∫ Xᵢ, ∫ Xⱼ⟫` of `ProbabilityTheory.IndepFun.integral_bilin`, which makes every
cross term vanish. The sample mean is `TauCeti.finiteMean`, and the scalar statement is the
case `E = ℝ`.

For pairwise cross-uncorrelated real families `X` and `Y`, the bilinear König–Huygens identity
yields the exact expectation of the centered cross-product sum
`∑ᵢ (Xᵢ - finiteMean ℝ X) * (Yᵢ - finiteMean ℝ Y)` and, with Bessel's divisor `r - 1` when `X` has
a common mean across `i`, unbiasedness of the sample covariance and sample variance.

## Main statements

* `TauCeti.integral_norm_sum_sq_of_pairwise_indepFun`: Bienaymé's identity for random vectors.
* `TauCeti.integral_norm_finiteMean_sub_sq`: the mean-square error of a sample mean.
* `TauCeti.integral_finiteMean_sub_sq`: the same identity for real random variables.
* `TauCeti.integral_norm_finiteMean_sub_sq_of_forall_eq` and
  `TauCeti.integral_norm_finiteMean_sub_sq_le_of_forall_le`: the mean-square error is `γ / r`
  when every per-sample error equals `γ`, and at most `γ / r` when every one is at most `γ`.
* `TauCeti.integral_sum_sub_finiteMean_mul` and
  `TauCeti.integral_inv_card_sub_one_mul_sum_sub_finiteMean_mul`: the expected centered
  cross-product sum of two pairwise cross-uncorrelated real families, and unbiasedness with
  divisor `card ι - 1`.

## References

* R. Vershynin, *High-Dimensional Probability* (2018), §1.3: the variance of sums of independent
  random variables.
-/

public section

open MeasureTheory ProbabilityTheory Finset
open scoped RealInnerProductSpace

namespace TauCeti

variable {Ω ι E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

section Hilbert

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

/-- **Bienaymé's identity for random vectors.** If the random vectors `X i`, `i ∈ s`, in a real
Hilbert space are square-integrable, centered and pairwise independent, then the expected squared
norm of their sum is the sum of their expected squared norms. -/
theorem integral_norm_sum_sq_of_pairwise_indepFun [IsFiniteMeasure μ] {X : ι → Ω → E}
    {s : Finset ι} (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hmean : ∀ i ∈ s, μ[X i] = 0)
    (hindep : Set.Pairwise ↑s fun i j ↦ X i ⟂ᵢ[μ] X j) :
    ∫ ω, ‖∑ i ∈ s, X i ω‖ ^ 2 ∂μ = ∑ i ∈ s, ∫ ω, ‖X i ω‖ ^ 2 ∂μ := by
  -- Over `ℝ`, `innerSL ℝ` is linear only up to `starRingEnd ℝ = RingHom.id ℝ`, so its applications
  -- below are not syntactically `⟪·, ·⟫` and `simp` cannot rewrite them with
  -- `innerSL_apply_apply`; they agree with `⟪·, ·⟫` by that lemma, which is `rfl`.
  -- Pairwise independence makes every cross term `∫ ⟪X i, X j⟫` vanish.
  have hcross : ∀ i ∈ s, ∀ j ∈ s, j ≠ i → ∫ ω, ⟪X i ω, X j ω⟫ ∂μ = 0 := by
    intro i hi j hj hji
    have h := (hindep hi hj hji.symm).integral_bilin ((hX i hi).integrable one_le_two)
      ((hX j hj).integrable one_le_two) (innerSL ℝ)
    rw [hmean i hi, map_zero, zero_apply] at h
    exact h
  exact integral_norm_sum_sq_of_pairwise_integral_inner_eq_zero
    (fun i hi j hj ↦ (hX i hi).integrable_inner (hX j hj))
    (fun i hi j hj hij ↦ hcross i hi j hj hij.symm)

variable [Fintype ι] [Nonempty ι]

/-- **The mean-square error of a sample mean.** If the random vectors `X i` in a real Hilbert space
are square-integrable, pairwise independent and have a common mean `m`, then their sample mean
`S` satisfies `∫ ‖S - m‖² = r⁻² ∑ᵢ ∫ ‖X i - m‖²`, where `r` is the number of samples. -/
theorem integral_norm_finiteMean_sub_sq [IsProbabilityMeasure μ] {X : ι → Ω → E} {m : E}
    (hX : ∀ i, MemLp (X i) 2 μ) (hmean : ∀ i, μ[X i] = m)
    (hindep : Pairwise fun i j ↦ X i ⟂ᵢ[μ] X j) :
    ∫ ω, ‖finiteMean ℝ (X · ω) - m‖ ^ 2 ∂μ =
      ((Fintype.card ι : ℝ) ^ 2)⁻¹ * ∑ i, ∫ ω, ‖X i ω - m‖ ^ 2 ∂μ := by
  -- The deviation of the sample mean is the sample mean of the deviations.
  simp_rw [← finiteMean_sub_const, finiteMean_eq_inv_smul_sum, norm_smul, mul_pow, norm_inv,
    Real.norm_natCast, inv_pow]
  rw [integral_const_mul, integral_norm_sum_sq_of_pairwise_indepFun (X := fun i ω ↦ X i ω - m)
    (fun i _ ↦ (hX i).sub (memLp_const m)) (fun i _ ↦ ?_)
    (fun i _ j _ hij ↦ (hindep hij).comp (measurable_sub_const m) (measurable_sub_const m))]
  simp [integral_sub ((hX i).integrable one_le_two) (integrable_const m), hmean i]

/-- **The mean-square error of a sample mean of real random variables.** If the real random
variables `Z i` are square-integrable, pairwise independent and have a common mean `c`, then their
sample mean `S` satisfies `∫ (S - c)² = r⁻² ∑ᵢ ∫ (Z i - c)²`, where `r` is the number of
samples. -/
theorem integral_finiteMean_sub_sq [IsProbabilityMeasure μ] {Z : ι → Ω → ℝ} {c : ℝ}
    (hZ : ∀ i, MemLp (Z i) 2 μ) (hmean : ∀ i, μ[Z i] = c)
    (hindep : Pairwise fun i j ↦ Z i ⟂ᵢ[μ] Z j) :
    ∫ ω, (finiteMean ℝ (Z · ω) - c) ^ 2 ∂μ =
      ((Fintype.card ι : ℝ) ^ 2)⁻¹ * ∑ i, ∫ ω, (Z i ω - c) ^ 2 ∂μ := by
  simpa only [Real.norm_eq_abs, sq_abs] using integral_norm_finiteMean_sub_sq hZ hmean hindep

/-- If, in addition to the hypotheses of `TauCeti.integral_norm_finiteMean_sub_sq`, every sample
has the same mean-square error `γ`, then the sample mean has mean-square error `γ / r`, where `r`
is the number of samples. -/
theorem integral_norm_finiteMean_sub_sq_of_forall_eq [IsProbabilityMeasure μ] {X : ι → Ω → E}
    {m : E} (hX : ∀ i, MemLp (X i) 2 μ) (hmean : ∀ i, μ[X i] = m)
    (hindep : Pairwise fun i j ↦ X i ⟂ᵢ[μ] X j) {γ : ℝ}
    (hγ : ∀ i, ∫ ω, ‖X i ω - m‖ ^ 2 ∂μ = γ) :
    ∫ ω, ‖finiteMean ℝ (X · ω) - m‖ ^ 2 ∂μ = γ / Fintype.card ι := by
  have hr : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [integral_norm_finiteMean_sub_sq hX hmean hindep, sum_congr rfl fun i _ ↦ hγ i, sum_const,
    card_univ, nsmul_eq_mul]
  field_simp

/-- If, in addition to the hypotheses of `TauCeti.integral_norm_finiteMean_sub_sq`, every sample
has mean-square error at most `γ`, then the sample mean has mean-square error at most `γ / r`,
where `r` is the number of samples. -/
theorem integral_norm_finiteMean_sub_sq_le_of_forall_le [IsProbabilityMeasure μ]
    {X : ι → Ω → E} {m : E} (hX : ∀ i, MemLp (X i) 2 μ) (hmean : ∀ i, μ[X i] = m)
    (hindep : Pairwise fun i j ↦ X i ⟂ᵢ[μ] X j) {γ : ℝ}
    (hγ : ∀ i, ∫ ω, ‖X i ω - m‖ ^ 2 ∂μ ≤ γ) :
    ∫ ω, ‖finiteMean ℝ (X · ω) - m‖ ^ 2 ∂μ ≤ γ / Fintype.card ι := by
  have hr : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  rw [integral_norm_finiteMean_sub_sq hX hmean hindep]
  calc ((Fintype.card ι : ℝ) ^ 2)⁻¹ * ∑ i, ∫ ω, ‖X i ω - m‖ ^ 2 ∂μ
      ≤ ((Fintype.card ι : ℝ) ^ 2)⁻¹ * ∑ _i : ι, γ := by gcongr with i; exact hγ i
    _ = γ / Fintype.card ι := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        field_simp

end Hilbert

section SampleCovariance

variable [Fintype ι] [IsProbabilityMeasure μ]

/-- **Expectation of the centered sample cross-product sum.** For two finite families `X` and `Y`
of square-integrable real random variables whose off-diagonal cross-covariances vanish, the
expectation of `∑ i, (X i - finiteMean ℝ X) * (Y i - finiteMean ℝ Y)` equals `(1 - r⁻¹)` times the
sum of the diagonal covariances plus the deterministic centered cross-product sum of the means,
where `r = Fintype.card ι`. -/
theorem integral_sum_sub_finiteMean_mul {X Y : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ)
    (hcov : Pairwise fun i j ↦ cov[X i, Y j; μ] = 0) :
    ∫ ω, ∑ i, (X i ω - finiteMean ℝ (X · ω)) * (Y i ω - finiteMean ℝ (Y · ω)) ∂μ =
      (1 - (Fintype.card ι : ℝ)⁻¹) * ∑ i, cov[X i, Y i; μ] +
        ∑ i, (μ[X i] - finiteMean ℝ fun j ↦ μ[X j]) *
          (μ[Y i] - finiteMean ℝ fun j ↦ μ[Y j]) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have hr : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  set U : ι → Ω → ℝ := fun i ω ↦ X i ω - μ[X i]
  set V : ι → Ω → ℝ := fun i ω ↦ Y i ω - μ[Y i]
  have hU : ∀ i, MemLp (U i) 2 μ := fun i ↦ (hX i).sub (memLp_const _)
  have hV : ∀ i, MemLp (V i) 2 μ := fun i ↦ (hY i).sub (memLp_const _)
  have hU_int : ∀ i, μ[U i] = 0 := fun i ↦ by
    simp [U, integral_sub ((hX i).integrable one_le_two) (integrable_const _)]
  have hV_int : ∀ i, μ[V i] = 0 := fun i ↦ by
    simp [V, integral_sub ((hY i).integrable one_le_two) (integrable_const _)]
  have hUV_int : ∀ i j, ∫ ω, U i ω * V j ω ∂μ = if i = j then cov[X i, Y i; μ] else 0 := by
    intro i j
    split_ifs with hij
    · subst hij; rfl
    · exact hcov hij
  have hbarU : ∀ ω, finiteMean ℝ (X · ω) - finiteMean ℝ (fun i ↦ μ[X i]) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, U i ω := fun ω ↦ by
    simp [U, finiteMean_eq_inv_smul_sum, sum_sub_distrib, mul_sub]
  have hbarV : ∀ ω, finiteMean ℝ (Y · ω) - finiteMean ℝ (fun i ↦ μ[Y i]) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, V i ω := fun ω ↦ by
    simp [V, finiteMean_eq_inv_smul_sum, sum_sub_distrib, mul_sub]
  -- Split about the deterministic grand means via König–Huygens, then integrate `U`, `V` away.
  set dX : ι → ℝ := fun i ↦ μ[X i] - finiteMean ℝ fun j ↦ μ[X j]
  set dY : ι → ℝ := fun i ↦ μ[Y i] - finiteMean ℝ fun j ↦ μ[Y j]
  have hpt : ∀ ω, ∑ i, (X i ω - finiteMean ℝ (X · ω)) * (Y i ω - finiteMean ℝ (Y · ω)) =
      ∑ i, (U i ω * V i ω + U i ω * dY i + dX i * V i ω + dX i * dY i) -
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, ∑ j, U i ω * V j ω := by
    intro ω
    have hkh := sum_sub_mul_sub_eq_sum_sub_finiteMean_mul (X · ω) (Y · ω)
      (finiteMean ℝ fun j ↦ μ[X j]) (finiteMean ℝ fun j ↦ μ[Y j])
    have hterm : ∀ i, (X i ω - finiteMean ℝ fun j ↦ μ[X j]) *
        (Y i ω - finiteMean ℝ fun j ↦ μ[Y j]) =
        U i ω * V i ω + U i ω * dY i + dX i * V i ω + dX i * dY i :=
      fun i ↦ by dsimp [U, V, dX, dY]; ring
    have hbarUV : (Fintype.card ι : ℝ) *
        ((finiteMean ℝ (X · ω) - finiteMean ℝ fun j ↦ μ[X j]) *
          (finiteMean ℝ (Y · ω) - finiteMean ℝ fun j ↦ μ[Y j])) =
        (Fintype.card ι : ℝ)⁻¹ * ∑ i, ∑ j, U i ω * V j ω := by
      rw [hbarU ω, hbarV ω, ← sum_mul_sum]
      field_simp
    simp_rw [hterm, hbarUV] at hkh
    linarith
  have hUV : ∀ i j, Integrable (fun ω ↦ U i ω * V j ω) μ := fun i j ↦ (hU i).integrable_mul (hV j)
  have hint_diag : ∀ i, Integrable
      (fun ω ↦ U i ω * V i ω + U i ω * dY i + dX i * V i ω + dX i * dY i) μ :=
    fun i ↦ (((hUV i i).add (((hU i).integrable one_le_two).mul_const _)).add
      (((hV i).integrable one_le_two).const_mul _)).add (integrable_const _)
  have hint_grid : Integrable (fun ω ↦ ∑ i, ∑ j, U i ω * V j ω) μ :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hUV i j
  simp_rw [hpt]
  rw [integral_sub (integrable_finsetSum _ fun i _ ↦ hint_diag i) (hint_grid.const_mul _),
    integral_finsetSum _ fun i _ ↦ hint_diag i, integral_const_mul,
    integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hUV i j]
  have h1 : ∀ i, ∫ ω, U i ω * V i ω + U i ω * dY i + dX i * V i ω + dX i * dY i ∂μ =
      cov[X i, Y i; μ] + dX i * dY i := by
    intro i
    have hUi := ((hU i).integrable one_le_two).mul_const (dY i)
    have hVi := ((hV i).integrable one_le_two).const_mul (dX i)
    rw [integral_add (f := fun ω ↦ U i ω * V i ω + U i ω * dY i + dX i * V i ω)
        (((hUV i i).add hUi).add hVi) (integrable_const _),
      integral_add (f := fun ω ↦ U i ω * V i ω + U i ω * dY i) ((hUV i i).add hUi) hVi,
      integral_add (hUV i i) hUi, integral_mul_const, integral_const_mul, hU_int i, hV_int i,
      integral_const, probReal_univ, one_smul]
    simp [covariance, U, V]
  have h2 : ∀ i, ∫ ω, ∑ j, U i ω * V j ω ∂μ = cov[X i, Y i; μ] := by
    intro i
    rw [integral_finsetSum _ fun j _ ↦ hUV i j]
    simp [hUV_int i]
  simp_rw [h1, h2, sum_add_distrib]
  ring

/-- **Unbiasedness of the Bessel-corrected sample cross-covariance.** For at least two
square-integrable real random variables `X i` with a common mean across `i` and `Y i` pairwise
cross-uncorrelated with `X` of common diagonal covariance `γ`, the Bessel-corrected sample
covariance `(r - 1)⁻¹ ∑ i, (X i - finiteMean ℝ X) * (Y i - finiteMean ℝ Y)` has expectation `γ`. -/
theorem integral_inv_card_sub_one_mul_sum_sub_finiteMean_mul {X Y : ι → Ω → ℝ} {γ : ℝ}
    (hcard : 2 ≤ Fintype.card ι) (hX : ∀ i, MemLp (X i) 2 μ) (hY : ∀ i, MemLp (Y i) 2 μ)
    (hmean : ∀ i j, μ[X i] = μ[X j]) (hcov : Pairwise fun i j ↦ cov[X i, Y j; μ] = 0)
    (hcov_diag : ∀ i, cov[X i, Y i; μ] = γ) :
    ∫ ω, ((Fintype.card ι : ℝ) - 1)⁻¹ *
        ∑ i, (X i ω - finiteMean ℝ (X · ω)) * (Y i ω - finiteMean ℝ (Y · ω)) ∂μ = γ := by
  have hne : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨i₀⟩ := hne
  have hr0 : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hr1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ Fintype.card ι := Nat.ofNat_le_cast.2 hcard
    linarith
  have hmean_eq : (fun j ↦ μ[X j]) = fun _ ↦ μ[X i₀] := funext fun j ↦ hmean j i₀
  have hbar : finiteMean ℝ (fun j ↦ μ[X j]) = μ[X i₀] := by
    rw [hmean_eq, finiteMean_eq_inv_smul_sum, sum_const, card_univ, nsmul_eq_mul, smul_eq_mul,
      inv_mul_cancel_left₀ hr0]
  rw [integral_const_mul, integral_sum_sub_finiteMean_mul hX hY hcov, hbar]
  simp only [hmean _ i₀, sub_self, zero_mul, sum_const_zero, add_zero, hcov_diag,
    sum_const, card_univ, nsmul_eq_mul]
  field_simp

end SampleCovariance

end TauCeti
