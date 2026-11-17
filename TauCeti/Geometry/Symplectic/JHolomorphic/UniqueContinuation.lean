/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.VariableStructure
import TauCeti.Geometry.Symplectic.JHolomorphic.Linearization
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Local unique continuation for `J`-holomorphic curves

Let `V` be a finite-dimensional real normed space, `W ⊆ V` open, and `J : V → V →L[ℝ] V` a `C¹`
field of complex structures on `W` (`J(x)² = -1`). A map `u : ℂ → V` into `W` is `J`-holomorphic
on an open set `Ω ⊆ ℂ` when it satisfies the nonlinear Cauchy–Riemann equation

`∂ₛu + J(u) ∂ₜu = 0`

(equivalently `∂ₜu = J(u) ∂ₛu`, or `du(i w) = J(u) (du w)` for all `w ∈ ℂ`).

This file proves the local-coordinate unique continuation and isolatedness theorems of
McDuff–Salamon, Section 2.4 (Lemma 2.4.1 and its consequences):

* **Pointwise complex-linear algebra.** A real-linear map `L : ℂ →ₗ[ℝ] F` intertwining `i · _` with
  an endomorphism `A` squaring to `-1` vanishes iff `L 1 = 0`, and is injective iff it is nonzero
  (`LinearMap.eq_zero_iff_apply_one_eq_zero_of_apply_I_mul_eq`,
  `LinearMap.injective_iff_ne_zero_of_apply_I_mul_eq`).
* **Two `C¹` `J`-holomorphic curves.** Near any coincidence point `z₀` where `u₁ z₀ = u₂ z₀`,
  the curves stay inside a convex ball in `W`, and the fundamental theorem of calculus along the
  segment from `u₂ z` to `u₁ z` rewrites the difference equation as a linear Cauchy–Riemann system
  `∂ₛξ + J(u₁) ∂ₜξ + C ξ = 0` for `ξ = u₁ - u₂` with continuous real-linear coefficient `C`. The
  variable-structure similarity principle
  (`TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation.VariableStructure`) applies locally,
  and a clopen connectedness argument propagates equality across any connected open `Ω` without
  assuming convexity of `W`:
  * `TauCeti.JHolomorphic.eventually_eq_or_eventually_ne_of_eq`: local dichotomy at a coincidence
    point.
  * `TauCeti.JHolomorphic.eqOn_of_eqOn` and `TauCeti.JHolomorphic.eqOn_of_eventuallyEq`:
    agreement on a nonempty open subset implies agreement on `Ω`.
  * `TauCeti.JHolomorphic.eqOn_of_forall_isBigO`: agreement to infinite order at one point implies
    agreement on `Ω`.
  * `TauCeti.JHolomorphic.setOf_ne_mem_codiscreteWithin`: distinct curves have isolated
    coincidences (`{z | u₁ z ≠ u₂ z} ∈ codiscreteWithin Ω`).
  * `TauCeti.JHolomorphic.setOf_ne_const_mem_codiscreteWithin`: a nonconstant curve has isolated
    point-preimages.
* **Critical points of a `C²` `J`-holomorphic curve.** Differentiating the Cauchy–Riemann equation
  via `TauCeti.cauchyRiemannLinearization_fderiv_apply` shows that `ξ z = ∂ₛu(z)` solves
  `∂ₛξ + J(u) ∂ₜξ + (DJ(u) ξ)(∂ₜu) = 0` on all of `Ω` with continuous coefficient. Consequently:
  * `TauCeti.JHolomorphic.fderiv_eqOn_zero_of_fderiv_eqOn_zero`,
    `TauCeti.JHolomorphic.eqOn_const_of_fderiv_eqOn_zero`, and
    `TauCeti.JHolomorphic.eqOn_const_of_fderiv_eventually_zero`: vanishing derivative on a nonempty
    open subset implies `u` is constant on `Ω`.
  * `TauCeti.JHolomorphic.eqOn_const_of_fderiv_forall_isBigO`: an infinite-order critical point
    implies `u` is constant on `Ω`.
  * `TauCeti.JHolomorphic.setOf_fderiv_ne_zero_mem_codiscreteWithin`: a nonconstant `C²` curve has
    isolated critical points (`{z | fderiv ℝ u z ≠ 0} ∈ codiscreteWithin Ω`).
  * `TauCeti.JHolomorphic.setOf_injective_fderiv_mem_codiscreteWithin`: the injective-differential
    points are codiscrete within `Ω`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.4 (Lemma 2.4.1).
* C. Wendl, *Lectures on Holomorphic Curves in Symplectic and Contact Geometry*, Section 2.5.
-/

public noncomputable section

open Asymptotics Complex Filter Function MeasureTheory Metric Set Topology

namespace LinearMap

/-- A real-linear map `L : ℂ →ₗ[ℝ] F` intertwining multiplication by `I` with an endomorphism `A`
vanishes everywhere if and only if it vanishes at `1`. -/
theorem eq_zero_iff_apply_one_eq_zero_of_apply_I_mul_eq {F : Type*} [AddCommMonoid F] [Module ℝ F]
    (L : ℂ →ₗ[ℝ] F) {A : F →ₗ[ℝ] F} (hL : ∀ w, L (I * w) = A (L w)) :
    L = 0 ↔ L 1 = 0 := by
  refine ⟨fun h ↦ by simp [h], fun h1 ↦ ?_⟩
  ext z
  rw [L.apply_eq_re_smul_one_add_im_smul_I z, ← mul_one I, hL 1, h1, map_zero, smul_zero,
    smul_zero, add_zero, LinearMap.zero_apply]

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

/-- For a real-linear endomorphism `A` squaring to `-1`, the Cauchy–Riemann form
`L 1 + A (L I) = 0` is equivalent to `L I = A (L 1)`. -/
theorem add_apply_I_eq_zero_iff_apply_I_eq (L : ℂ →ₗ[ℝ] F) {A : F →ₗ[ℝ] F}
    (hA : ∀ v, A (A v) = -v) : L 1 + A (L I) = 0 ↔ L I = A (L 1) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [eq_neg_of_add_eq_zero_left h, map_neg, hA, neg_neg]
  · rw [h, hA, add_neg_cancel]

/-- A real-linear map `L : ℂ →ₗ[ℝ] F` intertwining multiplication by `I` with an endomorphism `A`
squaring to `-1` is injective if and only if it is nonzero. -/
theorem injective_iff_ne_zero_of_apply_I_mul_eq (L : ℂ →ₗ[ℝ] F) {A : F →ₗ[ℝ] F}
    (hA : ∀ v, A (A v) = -v) (hL : ∀ w, L (I * w) = A (L w)) :
    Injective L ↔ L ≠ 0 := by
  refine ⟨fun hinj h0 ↦ one_ne_zero (hinj (by simp [h0])), fun hne ↦ ?_⟩
  have h1 : L 1 ≠ 0 := fun h ↦ hne ((L.eq_zero_iff_apply_one_eq_zero_of_apply_I_mul_eq hL).2 h)
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hI : L I = A (L 1) := by simpa only [mul_one] using hL 1
  have hre : z.re • L 1 + z.im • A (L 1) = 0 := by
    rw [← hI, ← L.apply_eq_re_smul_one_add_im_smul_I z, hz]
  have him : z.re • A (L 1) - z.im • L 1 = 0 := by
    have := congrArg A hre
    simp only [map_add, map_smul, map_zero, hA, smul_neg] at this
    simpa only [sub_eq_add_neg] using this
  have hsq : (z.re ^ 2 + z.im ^ 2) • L 1 = 0 := by
    calc (z.re ^ 2 + z.im ^ 2) • L 1
        = z.re • (z.re • L 1 + z.im • A (L 1)) - z.im • (z.re • A (L 1) - z.im • L 1) := by
          rw [smul_add, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul, add_smul]
          ring_nf
          abel
      _ = 0 := by rw [hre, him, smul_zero, smul_zero, sub_self]
  have hnorm : z.re ^ 2 + z.im ^ 2 = 0 := (smul_eq_zero.1 hsq).resolve_right h1
  apply Complex.ext
  · simp only [zero_re]
    nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  · simp only [zero_im]
    nlinarith [sq_nonneg z.re, sq_nonneg z.im]

end LinearMap

namespace TauCeti.JHolomorphic

section Algebraic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- For a continuous real-linear map `L : ℂ →L[ℝ] V` and an endomorphism `A : V →L[ℝ] V` squaring
to `-1`, `L` intertwines `I * _` with `A` if and only if `L 1 + A (L I) = 0`. -/
theorem forall_apply_I_mul_eq_iff {L : ℂ →L[ℝ] V} {A : V →L[ℝ] V}
    (hA : A ∘L A = -ContinuousLinearMap.id ℝ V) :
    (∀ w : ℂ, L (I * w) = A (L w)) ↔ L 1 + A (L I) = 0 :=
  L.toLinearMap.forall_apply_I_mul_eq_iff (A := A.toLinearMap) fun v ↦ by
    simpa using congrArg (fun T : V →L[ℝ] V ↦ T v) hA

/-- For a continuous real-linear map `L : ℂ →L[ℝ] V` and an endomorphism `A : V →L[ℝ] V` squaring
to `-1`, the Cauchy–Riemann relation `L 1 + A (L I) = 0` is equivalent to `L I = A (L 1)`. -/
theorem add_apply_I_eq_zero_iff_apply_I_eq {L : ℂ →L[ℝ] V} {A : V →L[ℝ] V}
    (hA : A ∘L A = -ContinuousLinearMap.id ℝ V) :
    L 1 + A (L I) = 0 ↔ L I = A (L 1) :=
  L.toLinearMap.add_apply_I_eq_zero_iff_apply_I_eq (A := A.toLinearMap) fun v ↦ by
    simpa using congrArg (fun T : V →L[ℝ] V ↦ T v) hA

/-- A continuous real-linear map `L : ℂ →L[ℝ] V` satisfying `L 1 + A (L I) = 0` with `A² = -1`
vanishes if and only if `L 1 = 0`. -/
theorem eq_zero_iff_apply_one_eq_zero {L : ℂ →L[ℝ] V} {A : V →L[ℝ] V}
    (hA : A ∘L A = -ContinuousLinearMap.id ℝ V) (hL : L 1 + A (L I) = 0) :
    L = 0 ↔ L 1 = 0 := by
  have hI := (forall_apply_I_mul_eq_iff hA).2 hL
  refine ⟨fun h ↦ by simp [h], fun h1 ↦ ContinuousLinearMap.ext fun z ↦ ?_⟩
  have h0 : L.toLinearMap = 0 :=
    (L.toLinearMap.eq_zero_iff_apply_one_eq_zero_of_apply_I_mul_eq (A := A.toLinearMap) hI).2 h1
  simpa using congrArg (fun T : ℂ →ₗ[ℝ] V ↦ T z) h0

/-- A continuous real-linear map `L : ℂ →L[ℝ] V` satisfying `L 1 + A (L I) = 0` with `A² = -1`
is injective if and only if it is nonzero. -/
theorem injective_iff_ne_zero {L : ℂ →L[ℝ] V} {A : V →L[ℝ] V}
    (hA : A ∘L A = -ContinuousLinearMap.id ℝ V) (hL : L 1 + A (L I) = 0) :
    Injective L ↔ L ≠ 0 := by
  have hI := (forall_apply_I_mul_eq_iff hA).2 hL
  have hA' : ∀ v, A (A v) = -v := fun v ↦ by simpa using congrArg (fun T : V →L[ℝ] V ↦ T v) hA
  have h := L.toLinearMap.injective_iff_ne_zero_of_apply_I_mul_eq (A := A.toLinearMap) hA' hI
  refine h.trans ⟨fun hne h0 ↦ hne (by simp [h0]), fun hne h0 ↦ hne ?_⟩
  exact ContinuousLinearMap.ext fun z ↦ by simpa using congrArg (fun T : ℂ →ₗ[ℝ] V ↦ T z) h0

end Algebraic

/-! ### Continuity of a unit-interval parametric integral -/

private theorem continuousOn_intervalIntegral_unit {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {B : Set ℂ} (hB : IsOpen B) {F : ℂ → ℝ → E}
    (hF : ContinuousOn (fun p : ℂ × ℝ ↦ F p.1 p.2) (B ×ˢ Icc (0 : ℝ) 1)) :
    ContinuousOn (fun z ↦ ∫ t in (0 : ℝ)..1, F z t) B := by
  intro z hz
  obtain ⟨δ, hδ, hδB⟩ := Metric.isOpen_iff.1 hB z hz
  have hKsub : closedBall z (δ / 2) ⊆ B :=
    (closedBall_subset_ball (half_lt_self hδ)).trans hδB
  have hKcomp : IsCompact (closedBall z (δ / 2) ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall z (δ / 2)).prod isCompact_Icc
  obtain ⟨M, hM⟩ := hKcomp.exists_bound_of_continuousOn
    (hF.mono (Set.prod_mono hKsub Subset.rfl))
  have hca : ContinuousAt (fun z ↦ ∫ t in (0 : ℝ)..1, F z t) z := by
    refine intervalIntegral.continuousAt_of_dominated_interval
      (bound := fun _ ↦ M) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [hB.mem_nhds hz] with w hw
      have hwF : ContinuousOn (F w) (Icc (0 : ℝ) 1) :=
        hF.comp (continuous_const.prodMk continuous_id).continuousOn fun t ht ↦ ⟨hw, ht⟩
      exact (hwF.mono (by
        rw [uIoc_of_le zero_le_one]
        exact Ioc_subset_Icc_self)).aestronglyMeasurable measurableSet_uIoc
    · filter_upwards [closedBall_mem_nhds z (half_pos hδ)] with w hw
      refine ae_of_all _ fun t ht ↦ ?_
      rw [uIoc_of_le zero_le_one] at ht
      exact hM (w, t) ⟨hw, Ioc_subset_Icc_self ht⟩
    · refine ae_of_all _ fun t ht ↦ ?_
      rw [uIoc_of_le zero_le_one] at ht
      have hct : ContinuousOn (fun w ↦ F w t) B :=
        hF.comp (continuous_id.prodMk continuous_const).continuousOn
          fun w hw ↦ ⟨hw, Ioc_subset_Icc_self ht⟩
      exact hct.continuousAt (hB.mem_nhds hz)
  exact hca.continuousWithinAt

/-! ### Difference of two `C¹` `J`-holomorphic curves -/

section TwoCurves

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Set V} {Ω : Set ℂ} {J : V → V →L[ℝ] V} {u₁ u₂ : ℂ → V}

/-- Local Hadamard reduction near a coincidence point `z₀ ∈ Ω` (`u₁ z₀ = u₂ z₀`).
On a ball `B = ball z₀ r ⊆ Ω` whose images under `u₁` and `u₂` lie in a convex ball inside `W`,
the difference `ξ = u₁ - u₂` solves a linear Cauchy–Riemann equation
`∂ₛξ + J(u₁) ∂ₜξ + C ξ = 0` with a continuous real-linear coefficient `C` on `B`. -/
private theorem exists_ball_linearCR_sub
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 1 J W)
    (hΩ : IsOpen Ω) (hu₁ : ContDiffOn ℝ 1 u₁ Ω) (hu₂ : ContDiffOn ℝ 1 u₂ Ω)
    (hm₁ : MapsTo u₁ Ω W)
    (hCR₁ : ∀ z ∈ Ω, fderiv ℝ u₁ z 1 + J (u₁ z) (fderiv ℝ u₁ z I) = 0)
    (hCR₂ : ∀ z ∈ Ω, fderiv ℝ u₂ z 1 + J (u₂ z) (fderiv ℝ u₂ z I) = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (heq₀ : u₁ z₀ = u₂ z₀) :
    ∃ r > 0, ball z₀ r ⊆ Ω ∧ ∃ C : ℂ → V →L[ℝ] V,
      ContinuousOn C (ball z₀ r) ∧
      ∀ z ∈ ball z₀ r, fderiv ℝ (u₁ - u₂) z 1 + J (u₁ z) (fderiv ℝ (u₁ - u₂) z I) +
        C z ((u₁ - u₂) z) = 0 := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have hy₀ : u₁ z₀ ∈ W := hm₁ hz₀
  obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.1 hW (u₁ z₀) hy₀
  have hcont₁ : ContinuousAt u₁ z₀ := hu₁.continuousOn.continuousAt (hΩ.mem_nhds hz₀)
  have hcont₂ : ContinuousAt u₂ z₀ := hu₂.continuousOn.continuousAt (hΩ.mem_nhds hz₀)
  have hnhds : Ω ∩ (u₁ ⁻¹' ball (u₁ z₀) ρ ∩ u₂ ⁻¹' ball (u₁ z₀) ρ) ∈ 𝓝 z₀ :=
    Filter.inter_mem (hΩ.mem_nhds hz₀)
      (Filter.inter_mem (hcont₁.preimage_mem_nhds (Metric.ball_mem_nhds _ hρ))
        (hcont₂.preimage_mem_nhds (heq₀ ▸ Metric.ball_mem_nhds _ hρ)))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.1 hnhds
  set B := ball z₀ r
  have hBΩ : B ⊆ Ω := fun z hz ↦ (hrsub hz).1
  have hseg : ∀ z ∈ B, ∀ t ∈ Icc (0 : ℝ) 1, u₂ z + t • (u₁ z - u₂ z) ∈ ball (u₁ z₀) ρ := by
    intro z hz t ht
    have hmem : (1 - t) • u₂ z + t • u₁ z ∈ ball (u₁ z₀) ρ :=
      convex_ball (u₁ z₀) ρ (hrsub hz).2.2 (hrsub hz).2.1 (sub_nonneg.2 ht.2) ht.1
        (sub_add_cancel 1 t)
    convert hmem using 1
    rw [sub_smul, one_smul, smul_sub]
    abel
  -- Evaluation bilinear map `ev v L = L v`.
  let ev : V →L[ℝ] (V →L[ℝ] V) →L[ℝ] V := (ContinuousLinearMap.id ℝ (V →L[ℝ] V)).flip
  let F : ℂ → ℝ → V →L[ℝ] V := fun z t ↦
    (ev (fderiv ℝ u₂ z I)).comp (fderiv ℝ J (u₂ z + t • (u₁ z - u₂ z)))
  let C : ℂ → V →L[ℝ] V := fun z ↦ ∫ t in (0 : ℝ)..1, F z t
  have hDJ : ContinuousOn (fderiv ℝ J) W := hJ.continuousOn_fderiv_of_isOpen hW le_rfl
  have hDu₂ : ContinuousOn (fun z ↦ fderiv ℝ u₂ z I) B :=
    ((hu₂.continuousOn_fderiv_of_isOpen hΩ le_rfl).mono hBΩ).clm_apply continuousOn_const
  have hFcont : ContinuousOn (fun p : ℂ × ℝ ↦ F p.1 p.2) (B ×ˢ Icc (0 : ℝ) 1) := by
    have hfst : MapsTo Prod.fst (B ×ˢ Icc (0 : ℝ) 1) B := fun _ hp ↦ hp.1
    have hu₁p : ContinuousOn (fun p : ℂ × ℝ ↦ u₁ p.1) (B ×ˢ Icc (0 : ℝ) 1) :=
      (hu₁.continuousOn.mono hBΩ).comp continuous_fst.continuousOn hfst
    have hu₂p : ContinuousOn (fun p : ℂ × ℝ ↦ u₂ p.1) (B ×ˢ Icc (0 : ℝ) 1) :=
      (hu₂.continuousOn.mono hBΩ).comp continuous_fst.continuousOn hfst
    have hγ : ContinuousOn (fun p : ℂ × ℝ ↦ u₂ p.1 + p.2 • (u₁ p.1 - u₂ p.1))
        (B ×ˢ Icc (0 : ℝ) 1) :=
      hu₂p.add (continuous_snd.continuousOn.smul (hu₁p.sub hu₂p))
    have h1 : ContinuousOn (fun p : ℂ × ℝ ↦ ev (fderiv ℝ u₂ p.1 I)) (B ×ˢ Icc (0 : ℝ) 1) :=
      ev.continuous.comp_continuousOn (hDu₂.comp continuous_fst.continuousOn hfst)
    have h2 : ContinuousOn (fun p : ℂ × ℝ ↦ fderiv ℝ J (u₂ p.1 + p.2 • (u₁ p.1 - u₂ p.1)))
        (B ×ˢ Icc (0 : ℝ) 1) :=
      hDJ.comp hγ fun p hp ↦ hρW (hseg p.1 hp.1 p.2 hp.2)
    exact h1.clm_comp h2
  have hFcont_t (w : ℂ) (hw : w ∈ B) : ContinuousOn (F w) (Icc (0 : ℝ) 1) :=
    hFcont.comp (continuous_const.prodMk continuous_id).continuousOn fun t ht ↦ ⟨hw, ht⟩
  have hCcont : ContinuousOn C B := continuousOn_intervalIntegral_unit isOpen_ball hFcont
  refine ⟨r, hr, hBΩ, C, hCcont, fun z hz ↦ ?_⟩
  have hzΩ : z ∈ Ω := hBΩ hz
  have hd₁ : DifferentiableAt ℝ u₁ z :=
    (hu₁.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hzΩ)
  have hd₂ : DifferentiableAt ℝ u₂ z :=
    (hu₂.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hzΩ)
  have hsub_fderiv : fderiv ℝ (u₁ - u₂) z = fderiv ℝ u₁ z - fderiv ℝ u₂ z :=
    (hd₁.hasFDerivAt.sub hd₂.hasFDerivAt).fderiv
  -- Evaluate `C z (u₁ z - u₂ z)` via the fundamental theorem of calculus on `[0, 1]`.
  have hCz : C z ((u₁ - u₂) z) = (J (u₁ z) - J (u₂ z)) (fderiv ℝ u₂ z I) := by
    have hint : IntervalIntegrable (F z) volume 0 1 :=
      (hFcont_t z hz).intervalIntegrable_of_Icc zero_le_one
    have happ := ContinuousLinearMap.intervalIntegral_apply hint ((u₁ - u₂) z)
    rw [show C z ((u₁ - u₂) z) = ∫ t in (0 : ℝ)..1, F z t ((u₁ - u₂) z) from happ]
    let g : ℝ → V := fun t ↦ J (u₂ z + t • (u₁ z - u₂ z)) (fderiv ℝ u₂ z I)
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt g (F z t (u₁ z - u₂ z)) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hJdiff : DifferentiableAt ℝ J (u₂ z + t • (u₁ z - u₂ z)) :=
        (hJ.differentiableOn one_ne_zero).differentiableAt (hW.mem_nhds (hρW (hseg z hz t ht)))
      have hline : HasDerivAt (fun s : ℝ ↦ u₂ z + s • (u₁ z - u₂ z)) (u₁ z - u₂ z) t := by
        simpa using ((hasDerivAt_id t).smul_const (u₁ z - u₂ z)).const_add (u₂ z)
      exact ((ev (fderiv ℝ u₂ z I)).hasFDerivAt.comp _ hJdiff.hasFDerivAt).comp_hasDerivAt t hline
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (((hFcont_t z hz).clm_apply continuousOn_const).intervalIntegrable_of_Icc zero_le_one)
    simpa [g, Pi.sub_apply] using hFTC
  rw [hsub_fderiv, sub_apply, sub_apply, hCz, sub_apply, map_sub]
  have h1 := hCR₁ z hzΩ
  have h2 := hCR₂ z hzΩ
  calc fderiv ℝ u₁ z 1 - fderiv ℝ u₂ z 1 +
        (J (u₁ z) (fderiv ℝ u₁ z I) - J (u₁ z) (fderiv ℝ u₂ z I)) +
        (J (u₁ z) (fderiv ℝ u₂ z I) - J (u₂ z) (fderiv ℝ u₂ z I))
      = (fderiv ℝ u₁ z 1 + J (u₁ z) (fderiv ℝ u₁ z I)) -
          (fderiv ℝ u₂ z 1 + J (u₂ z) (fderiv ℝ u₂ z I)) := by abel
    _ = 0 := by rw [h1, h2, sub_self]

omit [FiniteDimensional ℝ V] in
/-- Helper producing `AEStronglyMeasurable` and local norm bounds for a continuous field `C`
on an open set `B`. -/
private theorem continuousOn_ae_and_locally_bounded {B : Set ℂ} {C : ℂ → V →L[ℝ] V}
    (hB : IsOpen B) (hC : ContinuousOn C B) :
    AEStronglyMeasurable C (volume.restrict B) ∧
      ∀ z ∈ B, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M :=
  ⟨hC.aestronglyMeasurable hB.measurableSet, fun z hz ↦
    ⟨‖C z‖ + 1, ((hC.continuousAt (hB.mem_nhds hz)).norm.eventually
      (gt_mem_nhds (lt_add_one _))).mono fun _ h ↦ h.le⟩⟩

/-- **Local dichotomy at a coincidence point.** If two `C¹` `J`-holomorphic curves agree at
`z₀ ∈ Ω`, then either they agree on a neighbourhood of `z₀`, or they are distinct on a punctured
neighbourhood of `z₀`. -/
theorem eventually_eq_or_eventually_ne_of_eq
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 1 J W)
    (hJJ : ∀ x ∈ W, J x ∘L J x = -ContinuousLinearMap.id ℝ V)
    (hΩ : IsOpen Ω) (hu₁ : ContDiffOn ℝ 1 u₁ Ω) (hu₂ : ContDiffOn ℝ 1 u₂ Ω)
    (hm₁ : MapsTo u₁ Ω W)
    (hCR₁ : ∀ z ∈ Ω, fderiv ℝ u₁ z 1 + J (u₁ z) (fderiv ℝ u₁ z I) = 0)
    (hCR₂ : ∀ z ∈ Ω, fderiv ℝ u₂ z 1 + J (u₂ z) (fderiv ℝ u₂ z I) = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (heq₀ : u₁ z₀ = u₂ z₀) :
    (∀ᶠ z in 𝓝 z₀, u₁ z = u₂ z) ∨ (∀ᶠ z in 𝓝[≠] z₀, u₁ z ≠ u₂ z) := by
  obtain ⟨r, hr, hBΩ, C, hC, heq⟩ :=
    exists_ball_linearCR_sub hW hJ hΩ hu₁ hu₂ hm₁ hCR₁ hCR₂ hz₀ heq₀
  by_cases hall : ∀ z ∈ ball z₀ r, u₁ z = u₂ z
  · left
    exact Filter.eventually_of_mem (Metric.ball_mem_nhds z₀ hr) hall
  · right
    push Not at hall
    obtain ⟨z₁, hz₁, hne⟩ := hall
    obtain ⟨hCm, hCb⟩ := continuousOn_ae_and_locally_bounded isOpen_ball hC
    have hdisc := setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_complexStructure
      (J := J ∘ u₁) (C := C) (ξ := u₁ - u₂) isOpen_ball (convex_ball z₀ r).isPreconnected
      (hJ.comp (hu₁.mono hBΩ) (hm₁.mono_left hBΩ))
      (fun z hz ↦ hJJ (u₁ z) (hm₁ (hBΩ hz)))
      ((hu₁.sub hu₂).mono hBΩ) hCm hCb heq ⟨z₁, hz₁, sub_ne_zero.2 hne⟩
    have hmem : ∀ᶠ z in 𝓝[≠] z₀, z ∉ ball z₀ r \ {z | (u₁ - u₂) z ≠ 0} :=
      disjoint_principal_right.1 (mem_codiscreteWithin.1 hdisc z₀ (mem_ball_self hr))
    filter_upwards [hmem, nhdsWithin_le_nhds (Metric.ball_mem_nhds z₀ hr)] with z hz hzB
    by_contra h
    exact hz ⟨hzB, fun hne' ↦ hne' (sub_eq_zero.2 h)⟩

/-- **Unique continuation from a nonempty open set.** Two `C¹` `J`-holomorphic curves on a
connected open set `Ω ⊆ ℂ` that agree on a nonempty open subset of `Ω` agree on all of `Ω`.
No convexity assumption on `W` is required. -/
theorem eqOn_of_eqOn
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 1 J W)
    (hJJ : ∀ x ∈ W, J x ∘L J x = -ContinuousLinearMap.id ℝ V)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hu₁ : ContDiffOn ℝ 1 u₁ Ω) (hu₂ : ContDiffOn ℝ 1 u₂ Ω)
    (hm₁ : MapsTo u₁ Ω W)
    (hCR₁ : ∀ z ∈ Ω, fderiv ℝ u₁ z 1 + J (u₁ z) (fderiv ℝ u₁ z I) = 0)
    (hCR₂ : ∀ z ∈ Ω, fderiv ℝ u₂ z 1 + J (u₂ z) (fderiv ℝ u₂ z I) = 0)
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (heq : EqOn u₁ u₂ U) :
    EqOn u₁ u₂ Ω := by
  let S : Set ℂ := Ω ∩ interior {z | u₁ z = u₂ z}
  have hSopen : IsOpen S := hΩ.inter isOpen_interior
  have hSsub : S ⊆ {z | u₁ z = u₂ z} := fun _ hz ↦ interior_subset hz.2
  have hUS : U ⊆ S := subset_inter hUΩ (interior_maximal heq hU)
  -- Show `S` is relatively closed in `Ω`: any `z₀ ∈ Ω ∩ closure S` satisfies `u₁ z₀ = u₂ z₀`,
  -- and local unique continuation on a ball around `z₀` forces `z₀ ∈ S`.
  have hSclosed : Ω ∩ closure S ⊆ S := by
    intro z₀ ⟨hz₀Ω, hz₀cl⟩
    have hcont₁ : ContinuousAt u₁ z₀ := hu₁.continuousOn.continuousAt (hΩ.mem_nhds hz₀Ω)
    have hcont₂ : ContinuousAt u₂ z₀ := hu₂.continuousOn.continuousAt (hΩ.mem_nhds hz₀Ω)
    have heq₀ : u₁ z₀ = u₂ z₀ := by
      by_contra hne
      have hopen_ne : {z | u₁ z ≠ u₂ z} ∈ 𝓝 z₀ :=
        ((hcont₁.sub hcont₂).eventually_ne (sub_ne_zero.2 hne)).mono fun _ h ↦ sub_ne_zero.1 h
      obtain ⟨w, hwne, hwS⟩ := mem_closure_iff_nhds.1 hz₀cl _ hopen_ne
      exact hwne (hSsub hwS)
    obtain ⟨r, hr, hBΩ, C, hC, heqB⟩ :=
      exists_ball_linearCR_sub hW hJ hΩ hu₁ hu₂ hm₁ hCR₁ hCR₂ hz₀Ω heq₀
    obtain ⟨w, hwB, hwS⟩ := mem_closure_iff_nhds.1 hz₀cl (ball z₀ r) (Metric.ball_mem_nhds z₀ hr)
    obtain ⟨hCm, hCb⟩ := continuousOn_ae_and_locally_bounded isOpen_ball hC
    have hzero : EqOn (u₁ - u₂) 0 (ball z₀ r) :=
      eqOn_zero_of_contDiffOn_of_eqOn_zero_of_complexStructure
        (J := J ∘ u₁) (C := C) isOpen_ball (convex_ball z₀ r).isPreconnected
        (hJ.comp (hu₁.mono hBΩ) (hm₁.mono_left hBΩ))
        (fun z hz ↦ hJJ (u₁ z) (hm₁ (hBΩ hz)))
        ((hu₁.sub hu₂).mono hBΩ) hCm hCb heqB
        (isOpen_ball.inter hSopen) ⟨w, hwB, hwS⟩ inter_subset_left
        fun z hz ↦ sub_eq_zero.2 (hSsub hz.2)
    refine ⟨hz₀Ω, mem_interior.2 ⟨ball z₀ r, fun z hz ↦ sub_eq_zero.1 (hzero hz),
      isOpen_ball, mem_ball_self hr⟩⟩
  -- Connectedness of `Ω` forces `Ω ⊆ S`.
  have hΩS : Ω ⊆ S := by
    by_contra hnot
    obtain ⟨z, hzΩ, hzS⟩ := Set.not_subset.1 hnot
    obtain ⟨u₀, hu₀⟩ := hUne
    have hcov : Ω ⊆ S ∪ (closure S)ᶜ := fun x hx ↦ by
      by_cases h : x ∈ closure S
      · exact Or.inl (hSclosed ⟨hx, h⟩)
      · exact Or.inr h
    have hdisj : (Ω ∩ (S ∩ (closure S)ᶜ)).Nonempty :=
      hΩc S (closure S)ᶜ hSopen isClosed_closure.isOpen_compl hcov
        ⟨u₀, hUΩ hu₀, hUS hu₀⟩ ⟨z, hzΩ, fun hcl ↦ hzS (hSclosed ⟨hzΩ, hcl⟩)⟩
    obtain ⟨w, -, hwS, hwnc⟩ := hdisj
    exact hwnc (subset_closure hwS)
  exact fun z hz ↦ hSsub (hΩS hz)

/-- **Unique continuation from a germ.** Two `C¹` `J`-holomorphic curves on a connected open set
`Ω ⊆ ℂ` that agree on a neighbourhood of a point `z₀ ∈ Ω` agree on all of `Ω`. -/
theorem eqOn_of_eventuallyEq
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 1 J W)
    (hJJ : ∀ x ∈ W, J x ∘L J x = -ContinuousLinearMap.id ℝ V)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hu₁ : ContDiffOn ℝ 1 u₁ Ω) (hu₂ : ContDiffOn ℝ 1 u₂ Ω)
    (hm₁ : MapsTo u₁ Ω W)
    (hCR₁ : ∀ z ∈ Ω, fderiv ℝ u₁ z 1 + J (u₁ z) (fderiv ℝ u₁ z I) = 0)
    (hCR₂ : ∀ z ∈ Ω, fderiv ℝ u₂ z 1 + J (u₂ z) (fderiv ℝ u₂ z I) = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (heq : u₁ =ᶠ[𝓝 z₀] u₂) :
    EqOn u₁ u₂ Ω := by
  obtain ⟨U, hUsub, hUopen, hz₀U⟩ := _root_.mem_nhds_iff.1 (Filter.inter_mem heq (hΩ.mem_nhds hz₀))
  exact eqOn_of_eqOn hW hJ hJJ hΩ hΩc hu₁ hu₂ hm₁ hCR₁ hCR₂ hUopen ⟨z₀, hz₀U⟩
    (fun _ hz ↦ (hUsub hz).2) (fun _ hz ↦ (hUsub hz).1)

/-- **Unique continuation from infinite-order contact.** Two `C¹` `J`-holomorphic curves on a
connected open set `Ω ⊆ ℂ` that agree to infinite order at a point `z₀ ∈ Ω` agree on all of `Ω`. -/
theorem eqOn_of_forall_isBigO
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 1 J W)
    (hJJ : ∀ x ∈ W, J x ∘L J x = -ContinuousLinearMap.id ℝ V)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hu₁ : ContDiffOn ℝ 1 u₁ Ω) (hu₂ : ContDiffOn ℝ 1 u₂ Ω)
    (hm₁ : MapsTo u₁ Ω W)
    (hCR₁ : ∀ z ∈ Ω, fderiv ℝ u₁ z 1 + J (u₁ z) (fderiv ℝ u₁ z I) = 0)
    (hCR₂ : ∀ z ∈ Ω, fderiv ℝ u₂ z 1 + J (u₂ z) (fderiv ℝ u₂ z I) = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (h₀ : ∀ n : ℕ, (u₁ - u₂) =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) :
    EqOn u₁ u₂ Ω := by
  have heq₀ : u₁ z₀ = u₂ z₀ := by
    obtain ⟨c, hc⟩ := (h₀ 1).bound
    have hmem := hc.self_of_nhds
    simp only [Pi.sub_apply, pow_one, sub_self, norm_zero, mul_zero] at hmem
    exact sub_eq_zero.1 (norm_le_zero_iff.1 hmem)
  obtain ⟨r, hr, hBΩ, C, hC, heqB⟩ :=
    exists_ball_linearCR_sub hW hJ hΩ hu₁ hu₂ hm₁ hCR₁ hCR₂ hz₀ heq₀
  obtain ⟨hCm, hCb⟩ := continuousOn_ae_and_locally_bounded isOpen_ball hC
  have hzero : EqOn (u₁ - u₂) 0 (ball z₀ r) :=
    eqOn_zero_of_contDiffOn_of_forall_isBigO_of_complexStructure
      (J := J ∘ u₁) (C := C) isOpen_ball (convex_ball z₀ r).isPreconnected
      (hJ.comp (hu₁.mono hBΩ) (hm₁.mono_left hBΩ))
      (fun z hz ↦ hJJ (u₁ z) (hm₁ (hBΩ hz)))
      ((hu₁.sub hu₂).mono hBΩ) hCm hCb heqB (mem_ball_self hr) h₀
  exact eqOn_of_eqOn hW hJ hJJ hΩ hΩc hu₁ hu₂ hm₁ hCR₁ hCR₂ isOpen_ball
    ⟨z₀, mem_ball_self hr⟩ hBΩ fun z hz ↦ sub_eq_zero.1 (hzero hz)

/-- **Isolated coincidences.** On a connected open set `Ω ⊆ ℂ`, two `C¹` `J`-holomorphic curves
that differ at some point of `Ω` differ on a codiscrete subset of `Ω` (their coincidences are
isolated in `Ω`). -/
theorem setOf_ne_mem_codiscreteWithin
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 1 J W)
    (hJJ : ∀ x ∈ W, J x ∘L J x = -ContinuousLinearMap.id ℝ V)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hu₁ : ContDiffOn ℝ 1 u₁ Ω) (hu₂ : ContDiffOn ℝ 1 u₂ Ω)
    (hm₁ : MapsTo u₁ Ω W)
    (hCR₁ : ∀ z ∈ Ω, fderiv ℝ u₁ z 1 + J (u₁ z) (fderiv ℝ u₁ z I) = 0)
    (hCR₂ : ∀ z ∈ Ω, fderiv ℝ u₂ z 1 + J (u₂ z) (fderiv ℝ u₂ z I) = 0)
    (hne : ∃ z ∈ Ω, u₁ z ≠ u₂ z) :
    {z | u₁ z ≠ u₂ z} ∈ codiscreteWithin Ω := by
  rw [mem_codiscreteWithin]
  intro z₀ hz₀
  have hcont₁ : ContinuousAt u₁ z₀ := hu₁.continuousOn.continuousAt (hΩ.mem_nhds hz₀)
  have hcont₂ : ContinuousAt u₂ z₀ := hu₂.continuousOn.continuousAt (hΩ.mem_nhds hz₀)
  have hgoal : ∀ᶠ z in 𝓝[≠] z₀, u₁ z ≠ u₂ z := by
    by_cases heq₀ : u₁ z₀ = u₂ z₀
    · refine (eventually_eq_or_eventually_ne_of_eq hW hJ hJJ hΩ hu₁ hu₂ hm₁ hCR₁ hCR₂ hz₀
        heq₀).resolve_left fun hev ↦ ?_
      obtain ⟨z₁, hz₁, hz₁ne⟩ := hne
      exact hz₁ne (eqOn_of_eventuallyEq hW hJ hJJ hΩ hΩc hu₁ hu₂ hm₁ hCR₁ hCR₂ hz₀ hev hz₁)
    · exact nhdsWithin_le_nhds
        (((hcont₁.sub hcont₂).eventually_ne (sub_ne_zero.2 heq₀)).mono fun _ h ↦ sub_ne_zero.1 h)
  exact disjoint_principal_right.2 (hgoal.mono fun z hz ⟨_, hnot⟩ ↦ hnot hz)

/-- **Isolated point-preimages.** On a connected open set `Ω ⊆ ℂ`, every fibre `{z ∈ Ω | u z = y}`
of a nonconstant `C¹` `J`-holomorphic curve is discrete in `Ω`. No assumption `y ∈ W` is needed. -/
theorem setOf_ne_const_mem_codiscreteWithin
    {u : ℂ → V} (hW : IsOpen W) (hJ : ContDiffOn ℝ 1 J W)
    (hJJ : ∀ x ∈ W, J x ∘L J x = -ContinuousLinearMap.id ℝ V)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hu : ContDiffOn ℝ 1 u Ω) (hm : MapsTo u Ω W)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z 1 + J (u z) (fderiv ℝ u z I) = 0)
    (hnc : ∃ z₁ ∈ Ω, ∃ z₂ ∈ Ω, u z₁ ≠ u z₂) (y : V) :
    {z | u z ≠ y} ∈ codiscreteWithin Ω := by
  have hne : ∃ z ∈ Ω, u z ≠ (fun _ ↦ y) z := by
    obtain ⟨z₁, hz₁, z₂, hz₂, h12⟩ := hnc
    by_cases h1 : u z₁ = y
    · exact ⟨z₂, hz₂, fun h2 ↦ h12 (h1.trans h2.symm)⟩
    · exact ⟨z₁, hz₁, h1⟩
  exact setOf_ne_mem_codiscreteWithin hW hJ hJJ hΩ hΩc hu contDiffOn_const hm hCR
    (fun z _ ↦ by simp) hne

end TwoCurves

/-! ### Critical points of a `C²` `J`-holomorphic curve -/

section CriticalPoints

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Set V} {Ω : Set ℂ} {J : V → V →L[ℝ] V} {u : ℂ → V}

omit [FiniteDimensional ℝ V] in
/-- For a `C²` `J`-holomorphic curve on an open set `Ω ⊆ ℂ`, the partial derivative
`ξ z = fderiv ℝ u z 1` solves the linear Cauchy–Riemann equation
`∂ₛξ + J(u) ∂ₜξ + C ξ = 0` on `Ω`, where `C z v = fderiv ℝ J (u z) v (fderiv ℝ u z I)` is
continuous on `Ω`. -/
private theorem partial_one_linearCR
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 1 J W)
    (hJJ : ∀ x ∈ W, J x ∘L J x = -ContinuousLinearMap.id ℝ V)
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω) (hm : MapsTo u Ω W)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z 1 + J (u z) (fderiv ℝ u z I) = 0) :
    let ξ : ℂ → V := fun z ↦ fderiv ℝ u z 1
    let C : ℂ → V →L[ℝ] V := fun z ↦
      ((ContinuousLinearMap.id ℝ (V →L[ℝ] V)).flip (fderiv ℝ u z I)).comp (fderiv ℝ J (u z))
    ContDiffOn ℝ 1 ξ Ω ∧ ContinuousOn C Ω ∧
      ∀ z ∈ Ω, fderiv ℝ ξ z 1 + J (u z) (fderiv ℝ ξ z I) + C z (ξ z) = 0 := by
  intro ξ C
  have hξ : ContDiffOn ℝ 1 ξ Ω :=
    (hu.fderiv_of_isOpen hΩ (by norm_num)).clm_apply contDiffOn_const
  have hC : ContinuousOn C Ω := by
    let ev : V →L[ℝ] (V →L[ℝ] V) →L[ℝ] V := (ContinuousLinearMap.id ℝ (V →L[ℝ] V)).flip
    have h1 : ContinuousOn (fun z ↦ ev (fderiv ℝ u z I)) Ω :=
      ev.continuous.comp_continuousOn
        ((hu.continuousOn_fderiv_of_isOpen hΩ (by norm_num)).clm_apply continuousOn_const)
    have h2 : ContinuousOn (fun z ↦ fderiv ℝ J (u z)) Ω :=
      (hJ.continuousOn_fderiv_of_isOpen hW le_rfl).comp hu.continuousOn hm
    exact h1.clm_comp h2
  refine ⟨hξ, hC, fun z hz ↦ ?_⟩
  let j : ℂ →L[ℝ] ℂ := I • ContinuousLinearMap.id ℝ ℂ
  have hhol : ∀ᶠ y in 𝓝 z, cauchyRiemannOperator j J u y = 0 := by
    filter_upwards [hΩ.mem_nhds hz] with y hy
    ext w
    simp only [cauchyRiemannOperator_apply, zero_apply, sub_eq_zero, j,
      smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    exact (forall_apply_I_mul_eq_iff (hJJ (u y) (hm hy))).2 (hCR y hy) w
  have hlin := cauchyRiemannLinearization_fderiv_apply j J u (fun _ ↦ (1 : ℂ)) z I
    (hu.contDiffAt (hΩ.mem_nhds hz)) (differentiableAt_const (1 : ℂ))
    ((hJ.differentiableOn one_ne_zero).differentiableAt (hW.mem_nhds (hm hz))) hhol
  simp only [cauchyRiemannLinearization_apply, j, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, I_mul_I, map_neg] at hlin
  change fderiv ℝ ξ z 1 + J (u z) (fderiv ℝ ξ z I) +
      fderiv ℝ J (u z) (ξ z) (fderiv ℝ u z I) = 0
  have hlin' : -fderiv ℝ ξ z 1 - J (u z) (fderiv ℝ ξ z I) -
      fderiv ℝ J (u z) (ξ z) (fderiv ℝ u z I) = 0 := by
    simpa [ξ] using hlin
  calc fderiv ℝ ξ z 1 + J (u z) (fderiv ℝ ξ z I) + fderiv ℝ J (u z) (ξ z) (fderiv ℝ u z I)
      = -(-fderiv ℝ ξ z 1 - J (u z) (fderiv ℝ ξ z I) -
          fderiv ℝ J (u z) (ξ z) (fderiv ℝ u z I)) := by abel
    _ = 0 := by rw [hlin', neg_zero]

/-- If the derivative of a `C²` `J`-holomorphic curve on a connected open set `Ω ⊆ ℂ` vanishes
on a nonempty open subset of `Ω`, then it vanishes everywhere on `Ω`. -/
theorem fderiv_eqOn_zero_of_fderiv_eqOn_zero
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 1 J W)
    (hJJ : ∀ x ∈ W, J x ∘L J x = -ContinuousLinearMap.id ℝ V)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hm : MapsTo u Ω W)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z 1 + J (u z) (fderiv ℝ u z I) = 0)
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω)
    (hzero : ∀ z ∈ U, fderiv ℝ u z = 0) :
    ∀ z ∈ Ω, fderiv ℝ u z = 0 := by
  obtain ⟨hξ, hC, heq⟩ := partial_one_linearCR hW hJ hJJ hΩ hu hm hCR
  obtain ⟨hCm, hCb⟩ := continuousOn_ae_and_locally_bounded hΩ hC
  have hξ0 : EqOn (fun z ↦ fderiv ℝ u z 1) 0 Ω :=
    eqOn_zero_of_contDiffOn_of_eqOn_zero_of_complexStructure
      (J := J ∘ u) hΩ hΩc (hJ.comp (hu.of_le (by norm_num)) hm)
      (fun z hz ↦ hJJ (u z) (hm hz)) hξ hCm hCb heq hU hUne hUΩ
      fun z hz ↦ by simp [hzero z hz]
  intro z hz
  exact (eq_zero_iff_apply_one_eq_zero (hJJ (u z) (hm hz)) (hCR z hz)).2 (hξ0 hz)

/-- A `C²` `J`-holomorphic curve on a connected open set `Ω ⊆ ℂ` whose derivative vanishes on a
nonempty open subset of `Ω` is constant on `Ω`. -/
theorem eqOn_const_of_fderiv_eqOn_zero
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 1 J W)
    (hJJ : ∀ x ∈ W, J x ∘L J x = -ContinuousLinearMap.id ℝ V)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hm : MapsTo u Ω W)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z 1 + J (u z) (fderiv ℝ u z I) = 0)
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω)
    (hzero : ∀ z ∈ U, fderiv ℝ u z = 0) {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ Ω) (hz₂ : z₂ ∈ Ω) :
    u z₁ = u z₂ :=
  hΩ.is_const_of_fderiv_eq_zero hΩc (hu.differentiableOn two_ne_zero)
    (fderiv_eqOn_zero_of_fderiv_eqOn_zero hW hJ hJJ hΩ hΩc hu hm hCR hU hUne hUΩ hzero)
    hz₁ hz₂

/-- A `C²` `J`-holomorphic curve on a connected open set `Ω ⊆ ℂ` whose derivative vanishes on a
neighbourhood of a point `z₀ ∈ Ω` is constant on `Ω`. -/
theorem eqOn_const_of_fderiv_eventually_zero
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 1 J W)
    (hJJ : ∀ x ∈ W, J x ∘L J x = -ContinuousLinearMap.id ℝ V)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hm : MapsTo u Ω W)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z 1 + J (u z) (fderiv ℝ u z I) = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hzero : ∀ᶠ z in 𝓝 z₀, fderiv ℝ u z = 0)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ Ω) (hz₂ : z₂ ∈ Ω) :
    u z₁ = u z₂ := by
  obtain ⟨U, hUsub, hUopen, hz₀U⟩ :=
    _root_.mem_nhds_iff.1 (Filter.inter_mem hzero (hΩ.mem_nhds hz₀))
  exact eqOn_const_of_fderiv_eqOn_zero hW hJ hJJ hΩ hΩc hu hm hCR hUopen ⟨z₀, hz₀U⟩
    (fun _ hz ↦ (hUsub hz).2) (fun _ hz ↦ (hUsub hz).1) hz₁ hz₂

/-- A `C²` `J`-holomorphic curve on a connected open set `Ω ⊆ ℂ` whose derivative vanishes to
infinite order at a point `z₀ ∈ Ω` is constant on `Ω`. -/
theorem eqOn_const_of_fderiv_forall_isBigO
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 1 J W)
    (hJJ : ∀ x ∈ W, J x ∘L J x = -ContinuousLinearMap.id ℝ V)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hm : MapsTo u Ω W)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z 1 + J (u z) (fderiv ℝ u z I) = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ n : ℕ, (fun z ↦ fderiv ℝ u z) =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ Ω) (hz₂ : z₂ ∈ Ω) :
    u z₁ = u z₂ := by
  obtain ⟨hξ, hC, heq⟩ := partial_one_linearCR hW hJ hJJ hΩ hu hm hCR
  obtain ⟨hCm, hCb⟩ := continuousOn_ae_and_locally_bounded hΩ hC
  have hξ0 : EqOn (fun z ↦ fderiv ℝ u z 1) 0 Ω :=
    eqOn_zero_of_contDiffOn_of_forall_isBigO_of_complexStructure
      (J := J ∘ u) hΩ hΩc (hJ.comp (hu.of_le (by norm_num)) hm)
      (fun z hz ↦ hJJ (u z) (hm hz)) hξ hCm hCb heq hz₀ fun n ↦ by
        refine (IsBigO.of_bound 1 ?_).trans (h₀ n)
        exact Filter.Eventually.of_forall fun z ↦ by
          simpa using (fderiv ℝ u z).le_opNorm (1 : ℂ)
  refine hΩ.is_const_of_fderiv_eq_zero hΩc (hu.differentiableOn two_ne_zero) (fun z hz ↦ ?_)
    hz₁ hz₂
  exact (eq_zero_iff_apply_one_eq_zero (hJJ (u z) (hm hz)) (hCR z hz)).2 (hξ0 hz)

/-- **Isolated critical points.** On a connected open set `Ω ⊆ ℂ`, the critical points of a
nonconstant `C²` `J`-holomorphic curve are isolated in `Ω`: `{z | fderiv ℝ u z ≠ 0}` is
codiscrete within `Ω`. -/
theorem setOf_fderiv_ne_zero_mem_codiscreteWithin
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 1 J W)
    (hJJ : ∀ x ∈ W, J x ∘L J x = -ContinuousLinearMap.id ℝ V)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hm : MapsTo u Ω W)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z 1 + J (u z) (fderiv ℝ u z I) = 0)
    (hnc : ∃ z₁ ∈ Ω, ∃ z₂ ∈ Ω, u z₁ ≠ u z₂) :
    {z | fderiv ℝ u z ≠ 0} ∈ codiscreteWithin Ω := by
  obtain ⟨hξ, hC, heq⟩ := partial_one_linearCR hW hJ hJJ hΩ hu hm hCR
  obtain ⟨hCm, hCb⟩ := continuousOn_ae_and_locally_bounded hΩ hC
  have hne : ∃ z ∈ Ω, fderiv ℝ u z 1 ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨z₁, hz₁, z₂, hz₂, h12⟩ := hnc
    refine h12 (hΩ.is_const_of_fderiv_eq_zero hΩc (hu.differentiableOn two_ne_zero) ?_ hz₁ hz₂)
    intro z hz
    exact (eq_zero_iff_apply_one_eq_zero (hJJ (u z) (hm hz)) (hCR z hz)).2 (hall z hz)
  have hdisc := setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_complexStructure
    (J := J ∘ u) hΩ hΩc (hJ.comp (hu.of_le (by norm_num)) hm)
    (fun z hz ↦ hJJ (u z) (hm hz)) hξ hCm hCb heq hne
  refine Filter.mem_of_superset (Filter.inter_mem hdisc (self_mem_codiscreteWithin Ω)) ?_
  intro z ⟨hz1, _⟩
  exact mt (fun h ↦ by simp [h]) hz1

/-- On a connected open set `Ω ⊆ ℂ`, the points where the differential of a nonconstant `C²`
`J`-holomorphic curve is injective are codiscrete within `Ω`. -/
theorem setOf_injective_fderiv_mem_codiscreteWithin
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 1 J W)
    (hJJ : ∀ x ∈ W, J x ∘L J x = -ContinuousLinearMap.id ℝ V)
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hm : MapsTo u Ω W)
    (hCR : ∀ z ∈ Ω, fderiv ℝ u z 1 + J (u z) (fderiv ℝ u z I) = 0)
    (hnc : ∃ z₁ ∈ Ω, ∃ z₂ ∈ Ω, u z₁ ≠ u z₂) :
    {z | Injective (fderiv ℝ u z)} ∈ codiscreteWithin Ω := by
  have hdisc := setOf_fderiv_ne_zero_mem_codiscreteWithin hW hJ hJJ hΩ hΩc hu hm hCR hnc
  refine Filter.mem_of_superset (Filter.inter_mem hdisc (self_mem_codiscreteWithin Ω)) ?_
  rintro z ⟨hne, hzΩ⟩
  exact (injective_iff_ne_zero (hJJ (u z) (hm hzΩ)) (hCR z hzΩ)).2 hne

end CriticalPoints

end TauCeti.JHolomorphic
