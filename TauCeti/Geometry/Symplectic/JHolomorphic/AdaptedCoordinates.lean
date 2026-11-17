/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Calculus.FDeriv.PullbackEnd
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy
import TauCeti.Geometry.Symplectic.JHolomorphic.UniqueContinuation
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Adapted coordinates near a non-critical point of a `J`-holomorphic curve

Let `V` be a finite-dimensional real normed space, `W ⊆ V` open, and `J : V → V →L[ℝ] V` a `C^ℓ`
field of complex structures on `W` (`J(x)² = -1`, `1 ≤ ℓ`). Let `u₀ : ℂ → V` be a `C^ℓ`
`J`-holomorphic curve on an open set `Ω ⊆ ℂ` mapping into `W`, with non-vanishing differential
`fderiv ℝ u₀ z₀ ≠ 0` at a point `z₀ ∈ Ω`.

This file constructs local adapted coordinates (McDuff–Salamon, Lemma 2.4.2): a `C^ℓ` open partial
homeomorphism `e : OpenPartialHomeomorph (ℂ × EuclideanSpace ℂ (Fin m)) V` around `(z₀, 0)` with
`C^ℓ` inverse and `e.target ⊆ W`, such that:

* `e (a, 0) = u₀ a` for every `a : ℂ` (so `u₀` becomes the axis `a ↦ (a, 0)`);
* the pulled-back almost complex structure `J' = e.pullbackEnd J` equals multiplication by `i`
  along the entire axis `(a, 0) ∈ e.source`: `J' (a, 0) = I • id`;
* `J'` squares to `-1` on `e.source`, and is `C^n` whenever `n + 1 ≤ ℓ`.

The construction avoids losing any derivatives in the coordinate change `e` itself: choosing a
real-linear equivalence `T : (ℂ × ℂ^m) ≃L[ℝ] V` intertwining `i` with `J₀ = J (u₀ z₀)` and sending
`(1, 0)` to `∂ₛu₀(z₀)`, we set

`Ψ(a) w = ½ (T(0, w) - J(u₀ a) (J₀ (T(0, w))))`
`Φ(a, w) = u₀(a) + Ψ(a) w`.

Because `Ψ` uses only `J ∘ u₀` (and not `∂ₛu₀`), `Φ` retains the full `C^ℓ` regularity of `J` and
`u₀`. Moreover `J(u₀ a) ∘ Ψ(a) = Ψ(a) ∘ (i · _)`, and at any axis point `(a, 0)` the derivative of
`Φ` is `(δa, δw) ↦ du₀(a) δa + Ψ(a) δw`, which intertwines `i` with `J(u₀ a)` everywhere along the
axis and equals `T` at `(z₀, 0)`.

When `2 ≤ ℓ`, the pulled-back structure `J' = e.pullbackEnd J` is `C¹` on `e.source`, and the mean
value inequality on a compact ball `closedBall (z₀, 0) r ⊆ e.source` yields the transverse
Lipschitz estimate `‖J' (a, w) - I • id‖ ≤ C * ‖w‖`
(`TauCeti.JHolomorphic.exists_closedBall_norm_pullbackEnd_sub_I_le`).

## Main results

* `TauCeti.JHolomorphic.exists_continuousLinearEquiv_prod_euclideanSpace`: complex-linear model
  `T : (ℂ × EuclideanSpace ℂ (Fin m)) ≃L[ℝ] V` intertwining `i` with `J₀` and sending `(1, 0)` to
  a prescribed nonzero vector `v₁`.
* `TauCeti.JHolomorphic.exists_adaptedCoordinates`: existence of the `C^ℓ` adapted coordinate chart
  `e` around `(z₀, 0)` (McDuff–Salamon, Lemma 2.4.2).
* `TauCeti.JHolomorphic.exists_closedBall_norm_pullbackEnd_sub_I_le`: transverse estimate
  `‖e.pullbackEnd J (a, w) - I • id‖ ≤ C * ‖w‖` on a closed ball around `(z₀, 0)` when `2 ≤ ℓ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.4 (Lemma 2.4.2).
-/

public noncomputable section

open Complex Filter Function Metric Set Topology
open scoped ContDiff

namespace TauCeti.JHolomorphic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Given a complex structure `J₀` on a finite-dimensional real normed space `V` (`J₀² = -1`) and
a nonzero vector `v₁ : V`, there exist `m : ℕ` and a real-linear topological isomorphism
`T : (ℂ × EuclideanSpace ℂ (Fin m)) ≃L[ℝ] V` intertwining multiplication by `I` with `J₀` and
sending `(1, 0)` to `v₁`. Works uniformly for all positive even real dimensions, including `m = 0`
when `dim_ℝ V = 2`. -/
theorem exists_continuousLinearEquiv_prod_euclideanSpace {J₀ : V →L[ℝ] V}
    (hJ₀ : J₀ ∘L J₀ = -ContinuousLinearMap.id ℝ V) {v₁ : V} (hv₁ : v₁ ≠ 0) :
    ∃ (m : ℕ) (T : (ℂ × EuclideanSpace ℂ (Fin m)) ≃L[ℝ] V),
      (∀ p, J₀ (T p) = T (I • p)) ∧ T (1, 0) = v₁ := by
  obtain ⟨n, Φ, hΦ⟩ := J₀.exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul hJ₀
  set e₁ : EuclideanSpace ℂ (Fin n) := Φ.symm v₁
  have he₁ : e₁ ≠ 0 := by
    intro h
    exact hv₁ (by simpa [e₁] using congrArg Φ h)
  let K : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := Submodule.span ℂ {e₁}
  set m : ℕ := Module.finrank ℂ Kᗮ
  let ψ : EuclideanSpace ℂ (Fin m) ≃L[ℂ] Kᗮ :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin
  let eK : ℂ ≃ₗ[ℂ] K := LinearEquiv.toSpanNonzeroSingleton ℂ _ e₁ he₁
  let eProd : (ℂ × EuclideanSpace ℂ (Fin m)) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    (eK.prodCongr ψ.toLinearEquiv).trans (K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal)
  let S : (ℂ × EuclideanSpace ℂ (Fin m)) ≃L[ℝ] EuclideanSpace ℂ (Fin n) :=
    (eProd.restrictScalars ℝ).toContinuousLinearEquiv
  let T : (ℂ × EuclideanSpace ℂ (Fin m)) ≃L[ℝ] V := S.trans Φ
  refine ⟨m, T, fun p ↦ ?_, ?_⟩
  · have hΦ' : ∀ x, J₀ (Φ x) = Φ (I • x) := fun x ↦ by
      simpa using congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] V ↦ L x) hΦ
    change J₀ (Φ (eProd p)) = Φ (eProd (I • p))
    rw [hΦ', ← eProd.map_smul I p]
  · change Φ (eProd (1, 0)) = v₁
    have hK1 : (eK 1 : EuclideanSpace ℂ (Fin n)) = e₁ := by
      change (1 : ℂ) • e₁ = e₁
      exact one_smul ℂ e₁
    change Φ ((eK 1 : EuclideanSpace ℂ (Fin n)) + (ψ 0 : EuclideanSpace ℂ (Fin n))) = v₁
    rw [map_zero, ZeroMemClass.coe_zero, add_zero, hK1]
    exact Φ.apply_symm_apply v₁

/-- **Adapted coordinates near a non-critical point** (McDuff–Salamon, Lemma 2.4.2).
Let `J` be a `C^ℓ` field (`1 ≤ ℓ`) of complex structures on an open set `W ⊆ V`, and let
`u₀ : ℂ → V` be a `C^ℓ` `J`-holomorphic curve on an open set `Ω ⊆ ℂ` mapping into `W` with
`fderiv ℝ u₀ z₀ ≠ 0` at `z₀ ∈ Ω`. Then there exist `m : ℕ` and an open partial homeomorphism
`e : OpenPartialHomeomorph (ℂ × EuclideanSpace ℂ (Fin m)) V` such that:

1. `(z₀, 0) ∈ e.source`, `e.source ⊆ Ω ×ˢ Set.univ`, and `e.target ⊆ W`;
2. `e` is `C^ℓ` on `e.source` and `e.symm` is `C^ℓ` on `e.target`;
3. `e (a, 0) = u₀ a` for every `a : ℂ`;
4. `e.pullbackEnd J (a, 0) = I • ContinuousLinearMap.id ℝ _` for every `a` with `(a, 0) ∈ e.source`;
5. `e.pullbackEnd J p ∘L e.pullbackEnd J p = -ContinuousLinearMap.id ℝ _` for every `p ∈ e.source`;
6. `e.pullbackEnd J` is `C^n` on `e.source` for every `n : ℕ∞ω` with `n + 1 ≤ ℓ`. -/
theorem exists_adaptedCoordinates {W : Set V} {Ω : Set ℂ} {J : V → V →L[ℝ] V} {u₀ : ℂ → V}
    {ℓ : ℕ∞ω} (hℓ : 1 ≤ ℓ) (hW : IsOpen W) (hJ : ContDiffOn ℝ ℓ J W)
    (hJJ : ∀ x ∈ W, J x ∘L J x = -ContinuousLinearMap.id ℝ V)
    (hΩ : IsOpen Ω) (hu₀ : ContDiffOn ℝ ℓ u₀ Ω) (hm₀ : MapsTo u₀ Ω W)
    (hCR₀ : ∀ z ∈ Ω, fderiv ℝ u₀ z 1 + J (u₀ z) (fderiv ℝ u₀ z I) = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hnd : fderiv ℝ u₀ z₀ ≠ 0) :
    ∃ (m : ℕ) (e : OpenPartialHomeomorph (ℂ × EuclideanSpace ℂ (Fin m)) V),
      (z₀, 0) ∈ e.source ∧
      e.source ⊆ Ω ×ˢ Set.univ ∧
      e.target ⊆ W ∧
      ContDiffOn ℝ ℓ e e.source ∧
      ContDiffOn ℝ ℓ e.symm e.target ∧
      (∀ a : ℂ, e (a, 0) = u₀ a) ∧
      (∀ a : ℂ, (a, 0) ∈ e.source →
        e.pullbackEnd J (a, 0) =
          I • ContinuousLinearMap.id ℝ (ℂ × EuclideanSpace ℂ (Fin m))) ∧
      (∀ p ∈ e.source, e.pullbackEnd J p ∘L e.pullbackEnd J p =
        -ContinuousLinearMap.id ℝ (ℂ × EuclideanSpace ℂ (Fin m))) ∧
      (∀ {n : ℕ∞ω}, n + 1 ≤ ℓ → ContDiffOn ℝ n (e.pullbackEnd J) e.source) := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; exact absurd hℓ (by simp)
  have hv₁ : fderiv ℝ u₀ z₀ 1 ≠ 0 :=
    mt (eq_zero_iff_apply_one_eq_zero (hJJ (u₀ z₀) (hm₀ hz₀)) (hCR₀ z₀ hz₀)).2 hnd
  let J₀ : V →L[ℝ] V := J (u₀ z₀)
  have hJ₀sq : J₀ ∘L J₀ = -ContinuousLinearMap.id ℝ V := hJJ (u₀ z₀) (hm₀ hz₀)
  have hJ₀sq' (v : V) : J₀ (J₀ v) = -v := by
    simpa using congrArg (fun L : V →L[ℝ] V ↦ L v) hJ₀sq
  obtain ⟨m, T, hTI, hT1⟩ := exists_continuousLinearEquiv_prod_euclideanSpace hJ₀sq hv₁
  let E := ℂ × EuclideanSpace ℂ (Fin m)
  let T₂ : EuclideanSpace ℂ (Fin m) →L[ℝ] V :=
    T.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ ℂ (EuclideanSpace ℂ (Fin m)))
  -- Normal frame `Ψ a w = ½ (T(0, w) - J(u₀ a) (J₀ (T(0, w))))`, retaining full `C^ℓ` regularity.
  let Ψ : ℂ → EuclideanSpace ℂ (Fin m) →L[ℝ] V := fun a ↦
    ((2 : ℝ)⁻¹ • (ContinuousLinearMap.id ℝ V - (J (u₀ a)).comp J₀)).comp T₂
  let Φ : E → V := fun p ↦ u₀ p.1 + Ψ p.1 p.2
  have hΨ_z₀ : Ψ z₀ = T₂ := by
    refine ContinuousLinearMap.ext fun w ↦ ?_
    change (2 : ℝ)⁻¹ • (T₂ w - J₀ (J₀ (T₂ w))) = T₂ w
    rw [hJ₀sq', sub_neg_eq_add, ← two_smul ℝ, smul_smul]
    norm_num
  have hΨ_intertwine (a : ℂ) (ha : a ∈ Ω) (w : EuclideanSpace ℂ (Fin m)) :
      J (u₀ a) (Ψ a w) = Ψ a (I • w) := by
    have hJasq : ∀ v, J (u₀ a) (J (u₀ a) v) = -v := fun v ↦ by
      simpa using congrArg (fun L : V →L[ℝ] V ↦ L v) (hJJ (u₀ a) (hm₀ ha))
    have hT₂I : T₂ (I • w) = J₀ (T₂ w) := by
      have := (hTI (0, w)).symm
      simpa [T₂] using this
    simp only [Ψ, ContinuousLinearMap.comp_apply, smul_apply,
      sub_apply, ContinuousLinearMap.id_apply, map_smul, map_sub,
      hJasq, hT₂I, hJ₀sq', map_neg, sub_neg_eq_add]
    congr 1
    abel
  have hΨ_contDiff : ContDiffOn ℝ ℓ Ψ Ω := by
    have hJu : ContDiffOn ℝ ℓ (fun a ↦ J (u₀ a)) Ω := hJ.comp hu₀ hm₀
    have hsub : ContDiffOn ℝ ℓ (fun a ↦ ContinuousLinearMap.id ℝ V - (J (u₀ a)).comp J₀) Ω :=
      contDiffOn_const.sub (hJu.clm_comp contDiffOn_const)
    exact (hsub.const_smul (2 : ℝ)⁻¹).clm_comp contDiffOn_const
  have hfst : MapsTo Prod.fst (Ω ×ˢ (Set.univ : Set (EuclideanSpace ℂ (Fin m)))) Ω :=
    fun _ hp ↦ hp.1
  have hΦ_contDiff : ContDiffOn ℝ ℓ Φ (Ω ×ˢ Set.univ) :=
    (hu₀.comp contDiffOn_fst hfst).add
      ((hΨ_contDiff.comp contDiffOn_fst hfst).clm_apply contDiffOn_snd)
  -- Restrict to the open set `s = (Ω ×ˢ univ) ∩ Φ ⁻¹' W` so that `e.target ⊆ W`.
  let s : Set E := (Ω ×ˢ Set.univ) ∩ Φ ⁻¹' W
  have hs_open : IsOpen s :=
    hΦ_contDiff.continuousOn.isOpen_inter_preimage (hΩ.prod isOpen_univ) hW
  have hz₀_mem : (z₀, (0 : EuclideanSpace ℂ (Fin m))) ∈ s := by
    refine ⟨⟨hz₀, mem_univ _⟩, ?_⟩
    simpa [Φ] using hm₀ hz₀
  -- Derivative of `Φ` at any point `(a, 0)` with `a ∈ Ω`.
  have hΦ_deriv (a : ℂ) (ha : a ∈ Ω) :
      HasFDerivAt Φ
        ((fderiv ℝ u₀ a).comp (ContinuousLinearMap.fst ℝ ℂ (EuclideanSpace ℂ (Fin m))) +
          (Ψ a).comp (ContinuousLinearMap.snd ℝ ℂ (EuclideanSpace ℂ (Fin m))))
        (a, (0 : EuclideanSpace ℂ (Fin m))) := by
    let p₀ : E := (a, 0)
    have hdu_at : HasFDerivAt u₀ (fderiv ℝ u₀ a) p₀.1 :=
      ((hu₀.differentiableOn hℓ0).differentiableAt (hΩ.mem_nhds ha)).hasFDerivAt
    have hdu : HasFDerivAt (fun p : E ↦ u₀ p.1)
        ((fderiv ℝ u₀ a).comp (ContinuousLinearMap.fst ℝ ℂ (EuclideanSpace ℂ (Fin m)))) p₀ :=
      hdu_at.comp p₀ (hasFDerivAt_fst (𝕜 := ℝ) (p := p₀))
    have hdΨ_at : HasFDerivAt Ψ (fderiv ℝ Ψ a) p₀.1 :=
      ((hΨ_contDiff.differentiableOn hℓ0).differentiableAt (hΩ.mem_nhds ha)).hasFDerivAt
    have hdΨ : HasFDerivAt (fun p : E ↦ Ψ p.1)
        ((fderiv ℝ Ψ a).comp (ContinuousLinearMap.fst ℝ ℂ (EuclideanSpace ℂ (Fin m)))) p₀ :=
      hdΨ_at.comp p₀ (hasFDerivAt_fst (𝕜 := ℝ) (p := p₀))
    have hdprod : HasFDerivAt (fun p : E ↦ Ψ p.1 p.2)
        ((Ψ a).comp (ContinuousLinearMap.snd ℝ ℂ (EuclideanSpace ℂ (Fin m)))) p₀ := by
      have h := hdΨ.clm_apply (hasFDerivAt_snd (𝕜 := ℝ) (p := p₀))
      convert h using 1
      refine ContinuousLinearMap.ext fun q ↦ ?_
      simp [p₀]
    exact hdu.add hdprod
  have hΦ_fderiv_z₀ : (T : E →L[ℝ] V) = fderiv ℝ Φ (z₀, 0) := by
    rw [(hΦ_deriv z₀ hz₀).fderiv]
    refine ContinuousLinearMap.ext fun ⟨δa, δw⟩ ↦ ?_
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', hΨ_z₀]
    have hT1' : T (δa, 0) = fderiv ℝ u₀ z₀ δa := by
      have hcr : ∀ w : ℂ, fderiv ℝ u₀ z₀ (I * w) = J₀ (fderiv ℝ u₀ z₀ w) :=
        (forall_apply_I_mul_eq_iff hJ₀sq).2 (hCR₀ z₀ hz₀)
      have hTI_one : T (I, 0) = fderiv ℝ u₀ z₀ I := by
        have h1 : (I, (0 : EuclideanSpace ℂ (Fin m))) = I • (1, 0) := by simp
        rw [h1, ← hTI (1, 0), hT1, ← mul_one I, hcr 1]
      have hlin : (T.toContinuousLinearMap.comp
          (ContinuousLinearMap.inl ℝ ℂ (EuclideanSpace ℂ (Fin m)))).toLinearMap δa =
          (fderiv ℝ u₀ z₀).toLinearMap δa := by
        rw [LinearMap.apply_eq_re_smul_one_add_im_smul_I _ δa,
          LinearMap.apply_eq_re_smul_one_add_im_smul_I _ δa]
        simp [hT1, hTI_one]
      exact hlin
    have hsplit : (δa, δw) = (δa, (0 : EuclideanSpace ℂ (Fin m))) + (0, δw) := by simp
    change T (δa, δw) = fderiv ℝ u₀ z₀ δa + T₂ δw
    conv_lhs => rw [hsplit, map_add]
    rw [hT1']
    rfl
  obtain ⟨e, he_fun, hz₀_e, he_sub, he_symm_cd⟩ :=
    TauCeti.ContDiffOn.exists_openPartialHomeomorph (hΦ_contDiff.mono inter_subset_left) hs_open
      hz₀_mem hℓ hΦ_fderiv_z₀
  have he_src_Ω : e.source ⊆ Ω ×ˢ Set.univ := he_sub.trans inter_subset_left
  have he_tgt_W : e.target ⊆ W := fun y hy ↦ by
    have hmem := he_sub (e.map_target hy)
    have hval : Φ (e.symm y) = y := by rw [← he_fun]; exact e.right_inv hy
    exact hval ▸ hmem.2
  have he_cd : ContDiffOn ℝ ℓ e e.source := by
    rw [he_fun]
    exact hΦ_contDiff.mono he_src_Ω
  have he_diff (p : E) (hp : p ∈ e.source) : DifferentiableAt ℝ e p :=
    (he_cd.differentiableOn hℓ0).differentiableAt (e.open_source.mem_nhds hp)
  have hes_diff (p : E) (hp : p ∈ e.source) : DifferentiableAt ℝ e.symm (e p) :=
    (he_symm_cd.differentiableOn hℓ0).differentiableAt (e.open_target.mem_nhds (e.map_source hp))
  refine ⟨m, e, hz₀_e, he_src_Ω, he_tgt_W, he_cd, he_symm_cd, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [he_fun]
    simp [Φ]
  · intro a ha
    have haΩ : a ∈ Ω := (he_src_Ω ha).1
    have hfe : fderiv ℝ e (a, 0) =
        (fderiv ℝ u₀ a).comp (ContinuousLinearMap.fst ℝ ℂ (EuclideanSpace ℂ (Fin m))) +
          (Ψ a).comp (ContinuousLinearMap.snd ℝ ℂ (EuclideanSpace ℂ (Fin m))) := by
      rw [he_fun]
      exact (hΦ_deriv a haΩ).fderiv
    have hcr_a := (forall_apply_I_mul_eq_iff (hJJ (u₀ a) (hm₀ haΩ))).2 (hCR₀ a haΩ)
    refine ContinuousLinearMap.ext fun ⟨δa, δw⟩ ↦ ?_
    rw [OpenPartialHomeomorph.pullbackEnd_apply, smul_apply, ContinuousLinearMap.id_apply]
    have hea : e (a, 0) = u₀ a := by rw [he_fun]; simp [Φ]
    have hinter : J (e (a, 0)) (fderiv ℝ e (a, 0) (δa, δw)) =
        fderiv ℝ e (a, 0) (I • (δa, δw)) := by
      rw [hea, hfe]
      change J (u₀ a) (fderiv ℝ u₀ a δa + Ψ a δw) =
        fderiv ℝ u₀ a (I * δa) + Ψ a (I • δw)
      rw [map_add, hcr_a δa, hΨ_intertwine a haΩ δw]
    rw [hinter, e.fderiv_symm_apply_fderiv_apply_of_mem_source ha (he_diff _ ha) (hes_diff _ ha)]
  · intro p hp
    refine ContinuousLinearMap.ext fun v ↦ ?_
    have hsq : ∀ w, J (e p) (J (e p) w) = -w := fun w ↦ by
      simpa using congrArg (fun L : V →L[ℝ] V ↦ L w) (hJJ (e p) (he_tgt_W (e.map_source hp)))
    simpa using e.pullbackEnd_apply_pullbackEnd_apply hp (he_diff p hp) (hes_diff p hp) hsq v
  · intro n hn
    exact e.contDiffOn_pullbackEnd he_cd he_symm_cd
      ((hJ.mono he_tgt_W).of_le (le_self_add.trans hn)) hn

omit [FiniteDimensional ℝ V] in
/-- **Transverse Lipschitz estimate for the pulled-back structure.** When `e.pullbackEnd J` is `C¹`
on `e.source` and equals `I • id` along the axis `(a, 0)`, on a sufficiently small closed ball
`closedBall (z₀, 0) r ⊆ e.source` around `(z₀, 0)` it satisfies
`‖e.pullbackEnd J (a, w) - I • id‖ ≤ C * ‖w‖`. -/
theorem exists_closedBall_norm_pullbackEnd_sub_I_le {m : ℕ} {J : V → V →L[ℝ] V}
    {e : OpenPartialHomeomorph (ℂ × EuclideanSpace ℂ (Fin m)) V} {z₀ : ℂ}
    (hz₀ : (z₀, (0 : EuclideanSpace ℂ (Fin m))) ∈ e.source)
    (hJtilde : ContDiffOn ℝ 1 (e.pullbackEnd J) e.source)
    (haxis : ∀ a : ℂ, (a, (0 : EuclideanSpace ℂ (Fin m))) ∈ e.source →
      e.pullbackEnd J (a, 0) =
        I • ContinuousLinearMap.id ℝ (ℂ × EuclideanSpace ℂ (Fin m))) :
    ∃ r > 0, closedBall (z₀, (0 : EuclideanSpace ℂ (Fin m))) r ⊆ e.source ∧
      ∃ C ≥ 0, ∀ p ∈ closedBall (z₀, (0 : EuclideanSpace ℂ (Fin m))) r,
        ‖e.pullbackEnd J p - I • ContinuousLinearMap.id ℝ (ℂ × EuclideanSpace ℂ (Fin m))‖ ≤
          C * ‖p.2‖ := by
  obtain ⟨R, hR, hRe⟩ := Metric.isOpen_iff.1 e.open_source (z₀, (0 : EuclideanSpace ℂ (Fin m))) hz₀
  set r : ℝ := R / 2
  have hr : 0 < r := half_pos hR
  have hsub : closedBall (z₀, (0 : EuclideanSpace ℂ (Fin m))) r ⊆ e.source :=
    (closedBall_subset_ball (half_lt_self hR)).trans hRe
  have hK : IsCompact (closedBall (z₀, (0 : EuclideanSpace ℂ (Fin m))) r) :=
    isCompact_closedBall _ _
  have hcont : ContinuousOn (fderiv ℝ (e.pullbackEnd J))
      (closedBall (z₀, (0 : EuclideanSpace ℂ (Fin m))) r) :=
    (hJtilde.continuousOn_fderiv_of_isOpen e.open_source le_rfl).mono hsub
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  set C : ℝ := max M 0
  have hC0 : 0 ≤ C := le_max_right M 0
  refine ⟨r, hr, hsub, C, hC0, fun p hp ↦ ?_⟩
  have hp0 : (p.1, (0 : EuclideanSpace ℂ (Fin m))) ∈
      closedBall (z₀, (0 : EuclideanSpace ℂ (Fin m))) r := by
    rw [mem_closedBall, Prod.dist_eq] at hp ⊢
    simp only [dist_self, max_eq_left dist_nonneg]
    exact le_trans (le_max_left _ _) hp
  have hconv := convex_closedBall (z₀, (0 : EuclideanSpace ℂ (Fin m))) r
  have hmv := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le (C := C)
    (f' := fderiv ℝ (e.pullbackEnd J))
    (fun q hq ↦ ((hJtilde.differentiableOn one_ne_zero).differentiableAt
      (e.open_source.mem_nhds (hsub hq))).hasFDerivAt.hasFDerivWithinAt)
    (fun q hq ↦ (hM q hq).trans (le_max_left M 0)) hp0 hp
  rw [haxis p.1 (hsub hp0)] at hmv
  have hnorm_sub : ‖p - (p.1, (0 : EuclideanSpace ℂ (Fin m)))‖ = ‖p.2‖ := by
    rw [Prod.norm_def]
    simp
  rwa [hnorm_sub] at hmv

end TauCeti.JHolomorphic
