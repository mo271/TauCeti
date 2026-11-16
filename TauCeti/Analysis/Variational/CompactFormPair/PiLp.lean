/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Variational.CompactFormPair.Basic

/-!
# Finite orthogonal sums of compact form pairs

Given a finite family `P : ∀ i : ι, CompactFormPair 𝕜 (E i) (H i)` of compact form pairs,
`CompactFormPair.piLp P` constructs their `ℓ²`-orthogonal direct sum on `PiLp 2 E` and `PiLp 2 H`:

* the inclusion acts coordinatewise by `(u ↦ fun i => (P i).inclusion (u i))`;
* the sesquilinear form is the finite sum `∑ i, (P i).form (u i) (v i)`;
* the quadratic energy is `∑ i, (P i).energy (u i)`.

When `ι` is nonempty and each `(P i)` satisfies `HasShiftedLowerBound (c i) (ω i)`, the sum pair
satisfies `HasShiftedLowerBound (Finset.univ.inf' _ c) (Finset.univ.sup' _ ω)` — taking the
minimum coercivity constant and maximum shift across the summands.

## References

* V. Ivrii, *Partial Differential Equations*, §13.1.
* J. K. Hunter, *Notes on Partial Differential Equations*, §4.8.
-/

public section

noncomputable section

namespace TauCeti.CompactFormPair

section PiLp

variable {𝕜 ι : Type*} [RCLike 𝕜]
  {E H : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace 𝕜 (H i)]

section Inclusion

private def piLpInclusion (P : ∀ i, CompactFormPair 𝕜 (E i) (H i)) :
    PiLp 2 E →L[𝕜] PiLp 2 H :=
  (PiLp.continuousLinearEquiv 2 𝕜 H).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => ((P i).inclusion).comp (PiLp.proj (𝕜 := 𝕜) 2 E i))

private theorem piLpInclusion_dense (P : ∀ i, CompactFormPair 𝕜 (E i) (H i)) :
    DenseRange (piLpInclusion P) := by
  have hd₁ : DenseRange (Pi.map fun i => (P i).inclusion) :=
    DenseRange.piMap fun i => (P i).dense
  have hd₂ :
      DenseRange (ContinuousLinearMap.pi fun i =>
        ((P i).inclusion).comp (PiLp.proj (𝕜 := 𝕜) 2 E i)) :=
    hd₁.comp (PiLp.continuousLinearEquiv 2 𝕜 E).surjective.denseRange
      (continuous_pi fun i => (P i).inclusion.continuous.comp (continuous_apply i))
  exact (PiLp.continuousLinearEquiv 2 𝕜 H).symm.surjective.denseRange.comp hd₂
    (PiLp.continuousLinearEquiv 2 𝕜 H).symm.continuous

variable [Finite ι]

private theorem piLpInclusion_compact (P : ∀ i, CompactFormPair 𝕜 (E i) (H i)) :
    IsCompactOperator (piLpInclusion P) := by
  classical
  cases nonempty_fintype ι
  let S : ι → PiLp 2 E →L[𝕜] PiLp 2 H := fun i =>
    (PiLp.continuousLinearEquiv 2 𝕜 H).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.single (R := 𝕜) (φ := H) i).comp
        (((P i).inclusion).comp (PiLp.proj (𝕜 := 𝕜) 2 E i)))
  have hS : ∀ i, IsCompactOperator (S i) := fun i =>
    (((P i).compact.comp_clm (PiLp.proj (𝕜 := 𝕜) 2 E i)).clm_comp
      (ContinuousLinearMap.single (R := 𝕜) (φ := H) i)).clm_comp
      (PiLp.continuousLinearEquiv 2 𝕜 H).symm.toContinuousLinearMap
  have hsum : IsCompactOperator ⇑(∑ i : ι, S i) :=
    Finset.sum_induction S (fun T => IsCompactOperator ⇑T)
      (fun _ _ hf hg => hf.add hg) isCompactOperator_zero (fun i _ => hS i)
  have heq : (∑ i : ι, S i) = piLpInclusion P := by
    ext u j
    simp [S, piLpInclusion]
  rwa [heq] at hsum

end Inclusion

variable [Fintype ι]

private theorem piLp_bound_aux [Nonempty ι] {P : ∀ i, CompactFormPair 𝕜 (E i) (H i)}
    {c ω : ι → ℝ} (h : ∀ i, (P i).HasShiftedLowerBound (c i) (ω i)) :
    let c₀ : ℝ := Finset.univ.inf' Finset.univ_nonempty c
    let ω₀ : ℝ := Finset.univ.sup' Finset.univ_nonempty ω
    0 < c₀ ∧ ∀ u : PiLp 2 E,
      c₀ * ‖u‖ ^ 2 ≤ (∑ i : ι, (P i).energy (u i)) + ω₀ * ‖piLpInclusion P u‖ ^ 2 := by
  intro c₀ ω₀
  refine ⟨(Finset.lt_inf'_iff Finset.univ_nonempty).2 fun i _ => (h i).pos, fun u => ?_⟩
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have hci : c₀ ≤ c i := Finset.inf'_le c hi
  have hωi : ω i ≤ ω₀ := Finset.le_sup' ω hi
  calc
    c₀ * ‖u i‖ ^ 2 ≤ c i * ‖u i‖ ^ 2 := by gcongr
    _ ≤ (P i).energy (u i) + ω i * ‖(P i).inclusion (u i)‖ ^ 2 := (h i).bound (u i)
    _ ≤ (P i).energy (u i) + ω₀ * ‖piLpInclusion P u i‖ ^ 2 := by
      change (P i).energy (u i) + ω i * ‖(P i).inclusion (u i)‖ ^ 2 ≤
        (P i).energy (u i) + ω₀ * ‖(P i).inclusion (u i)‖ ^ 2
      gcongr

/-- Finite `ℓ²`-orthogonal sum of a family of compact form pairs on `PiLp 2 E` and `PiLp 2 H`. -/
def piLp (P : ∀ i, CompactFormPair 𝕜 (E i) (H i)) :
    CompactFormPair 𝕜 (PiLp 2 E) (PiLp 2 H) where
  inclusion := piLpInclusion P
  injective u v huv := by
    ext i
    exact (P i).injective (congrFun (congrArg WithLp.ofLp huv) i)
  dense := piLpInclusion_dense P
  compact := piLpInclusion_compact P
  form := ∑ i : ι, ((P i).form).bilinearComp
    (PiLp.proj (𝕜 := 𝕜) 2 E i) (PiLp.proj (𝕜 := 𝕜) 2 E i)
  hermitian u v := by
    simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.bilinearComp_apply,
      PiLp.proj_apply, star_sum]
    exact Finset.sum_congr rfl fun i _ => (P i).hermitian (u i) (v i)
  exists_shifted_lower_bound := by
    rcases isEmpty_or_nonempty ι with hEmpty | hNonempty
    · refine ⟨1, 0, zero_lt_one, fun u => ?_⟩
      obtain rfl : u = 0 := Subsingleton.elim u 0
      simp
    · obtain ⟨hc₀, hbound₀⟩ :=
        piLp_bound_aux fun i => (P i).hasShiftedLowerBound_coercivityConstant_shift
      refine ⟨Finset.univ.inf' Finset.univ_nonempty fun i => (P i).coercivityConstant,
        Finset.univ.sup' Finset.univ_nonempty fun i => (P i).shift, hc₀, fun u => ?_⟩
      simpa [energy_def] using hbound₀ u

/-- Coordinatewise evaluation of `(piLp P).inclusion`. -/
@[simp]
theorem inclusion_piLp_apply (P : ∀ i, CompactFormPair 𝕜 (E i) (H i)) (u : PiLp 2 E) (i : ι) :
    (piLp P).inclusion u i = (P i).inclusion (u i) :=
  (rfl)

/-- Sesquilinear form of `piLp P` is the finite sum of summand forms. -/
@[simp]
theorem form_piLp_apply (P : ∀ i, CompactFormPair 𝕜 (E i) (H i)) (u v : PiLp 2 E) :
    (piLp P).form u v = ∑ i : ι, (P i).form (u i) (v i) := by
  simp [piLp]

/-- Quadratic energy of `piLp P` is the finite sum of summand energies. -/
@[simp]
theorem energy_piLp (P : ∀ i, CompactFormPair 𝕜 (E i) (H i)) (u : PiLp 2 E) :
    (piLp P).energy u = ∑ i : ι, (P i).energy (u i) := by
  simp [energy_def]

/-- Coordinatewise behavior of `CompactFormPair.piLp` on a single-summand vector
`PiLp.single 2 i u`. -/
@[simp]
theorem inclusion_piLp_single [DecidableEq ι] (P : ∀ i, CompactFormPair 𝕜 (E i) (H i))
    (i : ι) (u : E i) :
    (piLp P).inclusion (PiLp.single 2 i u) = PiLp.single 2 i ((P i).inclusion u) := by
  ext j
  by_cases hij : j = i
  · subst hij
    simp
  · simp [Pi.single_eq_of_ne hij]

/-- Evaluating `(piLp P).form` against `PiLp.single 2 i u` on the left isolates the `i`-th
summand. -/
theorem form_piLp_single_left [DecidableEq ι] (P : ∀ i, CompactFormPair 𝕜 (E i) (H i))
    (i : ι) (u : E i) (v : PiLp 2 E) :
    (piLp P).form (PiLp.single 2 i u) v = (P i).form u (v i) := by
  rw [form_piLp_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [PiLp.ofLp_single, Pi.single_eq_of_ne hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- Evaluating `(piLp P).form` against `PiLp.single 2 i v` on the right isolates the `i`-th
summand. -/
theorem form_piLp_single_right [DecidableEq ι] (P : ∀ i, CompactFormPair 𝕜 (E i) (H i))
    (u : PiLp 2 E) (i : ι) (v : E i) :
    (piLp P).form u (PiLp.single 2 i v) = (P i).form (u i) v := by
  rw [form_piLp_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [PiLp.ofLp_single, Pi.single_eq_of_ne hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- Evaluating `(piLp P).energy` on `PiLp.single 2 i u` recovers `(P i).energy u`. -/
theorem energy_piLp_single [DecidableEq ι] (P : ∀ i, CompactFormPair 𝕜 (E i) (H i))
    (i : ι) (u : E i) :
    (piLp P).energy (PiLp.single 2 i u) = (P i).energy u := by
  rw [energy_def, form_piLp_single_left, PiLp.single_eq_same, ← energy_def]

/-- Shifting a finite orthogonal sum by `α` shifts each summand pair by `α`. -/
theorem shiftForm_piLp (P : ∀ i, CompactFormPair 𝕜 (E i) (H i)) (α : ℝ) :
    (piLp P).shiftForm α = piLp (fun i => (P i).shiftForm α) := by
  refine CompactFormPair.ext ?_ ?_
  · ext u i
    simp
  · ext u v
    simp [PiLp.inner_apply, Finset.mul_sum, Finset.sum_add_distrib]

/-- For a nonempty finite family with lower-bound witnesses `(c i, ω i)`, the orthogonal sum
`piLp P` satisfies `HasShiftedLowerBound` with coercivity constant `min_i (c i)` and shift
`max_i (ω i)`. -/
theorem hasShiftedLowerBound_piLp [Nonempty ι] {P : ∀ i, CompactFormPair 𝕜 (E i) (H i)}
    {c ω : ι → ℝ} (h : ∀ i, (P i).HasShiftedLowerBound (c i) (ω i)) :
    (piLp P).HasShiftedLowerBound
      (Finset.univ.inf' Finset.univ_nonempty c)
      (Finset.univ.sup' Finset.univ_nonempty ω) := by
  obtain ⟨hc₀, hbound₀⟩ := piLp_bound_aux h
  rw [hasShiftedLowerBound_iff]
  refine ⟨hc₀, fun u => ?_⟩
  rw [energy_piLp]
  exact hbound₀ u

end PiLp

end TauCeti.CompactFormPair

end
