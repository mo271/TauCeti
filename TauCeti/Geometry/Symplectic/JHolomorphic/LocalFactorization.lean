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
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import TauCeti.Analysis.Complex.CauchyRiemann.Similarity
import TauCeti.Analysis.InnerProductSpace.RankOne
import TauCeti.Geometry.Symplectic.JHolomorphic.AdaptedCoordinates
import TauCeti.Geometry.Symplectic.JHolomorphic.UniqueContinuation
import TauCeti.MeasureTheory.Function.RankOne
import TauCeti.Topology.Algebra.Module.ComplexSmulI

/-!
# Local factorization of `J`-holomorphic curves

Let `V` be a finite-dimensional real normed space, `W ⊆ V` open, and `J : V → V →L[ℝ] V` a `C²`
field of complex structures on `W` (`J(x)² = -1`). Suppose `u₀ : ℂ → V` is a `C²` `J`-holomorphic
curve on an open set `Ω₀ ⊆ ℂ` mapping into `W` with non-vanishing differential at `z₀ ∈ Ω₀`, and
`u₁ : ℂ → V` is a `C¹` `J`-holomorphic curve on an open set `Ω₁ ⊆ ℂ` (possibly critical at `ζ₀`)
with `u₀ z₀ = u₁ ζ₀`.

This file proves the local accumulation-to-factorization lemma (McDuff–Salamon, Lemma 2.4.3): if
`(z₀, ζ₀)` lies in the closure of `{p : ℂ × ℂ | p.2 ≠ ζ₀ ∧ u₀ p.1 = u₁ p.2}` (for instance, if
there exist sequences `z ν → z₀` and `ζ ν → ζ₀` with `ζ ν ≠ ζ₀` and `u₀ (z ν) = u₁ (ζ ν)`), then
on an open neighbourhood `U ⊆ Ω₁` of `ζ₀` there exists a holomorphic map `φ : ℂ → ℂ` sending `ζ₀`
to `z₀` and `U` into `Ω₀` such that `u₁ ζ = u₀ (φ ζ)` for all `ζ ∈ U`.

## Proof outline

1. Choose `C²` adapted coordinates `e : OpenPartialHomeomorph (ℂ × ℂ^m) V` around `(z₀, 0)`
   (`TauCeti.JHolomorphic.exists_adaptedCoordinates`) in which `u₀(a) = e(a, 0)` and the
   pulled-back structure `J' = e.pullbackEnd J` is `C¹` and equals `i` along the axis `(a, 0)`.
   The transverse estimate (`TauCeti.JHolomorphic.exists_closedBall_norm_pullbackEnd_sub_I_le`)
   gives `‖J'(a, w) - i‖ ≤ C ‖w‖` on `closedBall (z₀, 0) r ⊆ e.source`.
2. Write `v = e.symm ∘ u₁ = (a, b)` on a small disc `U = ball ζ₀ δ ⊆ Ω₁` where `‖∂ₜv‖ ≤ M`.
   Because `v` satisfies `∂ₛv + J'(v) ∂ₜv = 0`, its transverse component `b : ℂ → ℂ^m` satisfies
   `‖∂ₛb + i ∂ₜb‖ ≤ (C * M) * ‖b‖`.
3. Absorb the defect `-(∂ₛb + i ∂ₜb)` via the normalized rank-one operator
   `K(ζ) = (rankOneDivNormSq ℂ (-(∂ₛb + i ∂ₜb)) (b ζ)).restrictScalars ℝ`
   (`TauCeti.rankOneDivNormSq`). Then `K` is strongly measurable and uniformly bounded by `C * M`
   on `U`, and `∂ₛb + i ∂ₜb + K b = 0` everywhere on `U` (including where `b = 0`).
4. By Carleman's similarity principle (`TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn`),
   if `b` did not vanish identically on `U`, its zeros would be isolated, contradicting the
   accumulation of coincidences `u₀(z) = u₁(ζ)` (which force `b(ζ) = 0`).
5. Hence `b ≡ 0` on `U`, so `u₁ ζ = e (a ζ, 0) = u₀ (a ζ)` and `J' (v ζ) = i` on `U`, which makes
   `∂ₛa + i ∂ₜa = 0` and therefore `a` holomorphic on `U`.

## Main results

* `TauCeti.JHolomorphic.exists_holomorphic_factorization_of_mem_closure`: closure form of the
  local factorization lemma (McDuff–Salamon, Lemma 2.4.3).
* `TauCeti.JHolomorphic.exists_holomorphic_factorization_of_tendsto`: sequential form of the
  local factorization lemma.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.4 (Lemma 2.4.3).
-/

public noncomputable section

open Complex Filter Function MeasureTheory Metric Set Topology
open scoped ContDiff

namespace TauCeti.JHolomorphic

/-- If a `C¹` map `b : ℂ → E` on a connected open set `U` into a finite-dimensional complex inner
product space satisfies the differential inequality `‖∂ₛb + i ∂ₜb‖ ≤ L * ‖b‖`, and is not
identically zero on `U`, then its zeros are isolated within `U`. -/
private theorem setOf_ne_zero_mem_codiscreteWithin_of_norm_add_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U) {b : ℂ → E}
    (hb : ContDiffOn ℝ 1 b U) {L : ℝ} (hL : 0 ≤ L)
    (hineq : ∀ ζ ∈ U, ‖fderiv ℝ b ζ 1 + I • fderiv ℝ b ζ I‖ ≤ L * ‖b ζ‖)
    (hne : ∃ ζ ∈ U, b ζ ≠ 0) :
    {ζ | b ζ ≠ 0} ∈ codiscreteWithin U := by
  let y : ℂ → E := fun ζ ↦ -(fderiv ℝ b ζ 1 + I • fderiv ℝ b ζ I)
  let K : ℂ → E →L[ℝ] E := fun ζ ↦
    (TauCeti.rankOneDivNormSq ℂ (y ζ) (b ζ)).restrictScalars ℝ
  have hy_cont : ContinuousOn y U := by
    have h1 : ContinuousOn (fun ζ ↦ fderiv ℝ b ζ 1) U :=
      (hb.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
    have h2 : ContinuousOn (fun ζ ↦ fderiv ℝ b ζ I) U :=
      (hb.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
    exact (h1.add (continuousOn_const.smul h2)).neg
  have hKm : AEStronglyMeasurable K (volume.restrict U) :=
    (ContinuousLinearMap.continuous_restrictScalars (𝕜 := ℂ) (𝕜' := ℝ)
      (E := E) (F := E)).comp_aestronglyMeasurable
      ((hy_cont.aestronglyMeasurable hU.measurableSet).rankOneDivNormSq
        (hb.continuousOn.aestronglyMeasurable hU.measurableSet))
  have hKbd (ζ : ℂ) (hζ : ζ ∈ U) : ‖K ζ‖ ≤ L := by
    refine ContinuousLinearMap.opNorm_le_bound _ hL fun w ↦ ?_
    have h1 : ‖K ζ w‖ ≤ ‖TauCeti.rankOneDivNormSq ℂ (y ζ) (b ζ)‖ * ‖w‖ :=
      ContinuousLinearMap.le_opNorm (TauCeti.rankOneDivNormSq ℂ (y ζ) (b ζ)) w
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg w))
    rw [TauCeti.norm_rankOneDivNormSq]
    by_cases hbz : b ζ = 0
    · simp [hbz, hL]
    · have hpos : 0 < ‖b ζ‖ := norm_pos_iff.2 hbz
      rw [div_le_iff₀ hpos]
      dsimp only [y]
      rw [norm_neg]
      exact hineq ζ hζ
  have hKb : ∀ ζ ∈ U, ∃ M', ∀ᶠ w in 𝓝 ζ, ‖K w‖ ≤ M' := fun ζ hζ ↦
    ⟨L, Filter.eventually_of_mem (hU.mem_nhds hζ) hKbd⟩
  have hKeq (ζ : ℂ) (hζ : ζ ∈ U) :
      fderiv ℝ b ζ 1 + I • fderiv ℝ b ζ I + K ζ (b ζ) = 0 := by
    by_cases hbz : b ζ = 0
    · have h0 : ‖fderiv ℝ b ζ 1 + I • fderiv ℝ b ζ I‖ ≤ 0 := by
        simpa [hbz] using hineq ζ hζ
      have h0' : fderiv ℝ b ζ 1 + I • fderiv ℝ b ζ I = 0 := norm_le_zero_iff.1 h0
      simp [K, hbz, h0']
    · change fderiv ℝ b ζ 1 + I • fderiv ℝ b ζ I +
        TauCeti.rankOneDivNormSq ℂ (y ζ) (b ζ) (b ζ) = 0
      rw [TauCeti.rankOneDivNormSq_apply_self _ hbz]
      simp [y]
  exact TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn hU hUc hb hKm hKb hKeq hne

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Set V} {Ω₀ Ω₁ : Set ℂ} {J : V → V →L[ℝ] V} {u₀ u₁ : ℂ → V}

/-- **Local factorization of `J`-holomorphic curves** (McDuff–Salamon, Lemma 2.4.3, closure form).
Let `J` be a `C²` field of complex structures on an open set `W ⊆ V`, `u₀ : ℂ → V` a `C²`
`J`-holomorphic curve on an open set `Ω₀ ⊆ ℂ` mapping into `W` with `fderiv ℝ u₀ z₀ ≠ 0` at
`z₀ ∈ Ω₀`, and `u₁ : ℂ → V` a `C¹` `J`-holomorphic curve on an open set `Ω₁ ⊆ ℂ` (possibly
critical at `ζ₀`) with `u₀ z₀ = u₁ ζ₀`. If `(z₀, ζ₀)` lies in the closure of
`{p : ℂ × ℂ | p.2 ≠ ζ₀ ∧ u₀ p.1 = u₁ p.2}`, then on an open neighbourhood `U ⊆ Ω₁` of `ζ₀` there
exists a holomorphic map `φ : ℂ → ℂ` with `φ ζ₀ = z₀`, `MapsTo φ U Ω₀`, and
`∀ ζ ∈ U, u₁ ζ = u₀ (φ ζ)`. -/
theorem exists_holomorphic_factorization_of_mem_closure
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W)
    (hJJ : ∀ x ∈ W, J x ∘L J x = -ContinuousLinearMap.id ℝ V)
    (hΩ₀ : IsOpen Ω₀) (hu₀ : ContDiffOn ℝ 2 u₀ Ω₀) (hm₀ : MapsTo u₀ Ω₀ W)
    (hCR₀ : ∀ z ∈ Ω₀, fderiv ℝ u₀ z 1 + J (u₀ z) (fderiv ℝ u₀ z I) = 0)
    (hΩ₁ : IsOpen Ω₁) (hu₁ : ContDiffOn ℝ 1 u₁ Ω₁)
    (hCR₁ : ∀ ζ ∈ Ω₁, fderiv ℝ u₁ ζ 1 + J (u₁ ζ) (fderiv ℝ u₁ ζ I) = 0)
    {z₀ ζ₀ : ℂ} (hz₀ : z₀ ∈ Ω₀) (hζ₀ : ζ₀ ∈ Ω₁) (hnd : fderiv ℝ u₀ z₀ ≠ 0)
    (heq₀ : u₀ z₀ = u₁ ζ₀)
    (hacc : (z₀, ζ₀) ∈ closure {p : ℂ × ℂ | p.2 ≠ ζ₀ ∧ u₀ p.1 = u₁ p.2}) :
    ∃ U : Set ℂ, IsOpen U ∧ ζ₀ ∈ U ∧ U ⊆ Ω₁ ∧
      ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ U ∧ φ ζ₀ = z₀ ∧
        MapsTo φ U Ω₀ ∧ ∀ ζ ∈ U, u₁ ζ = u₀ (φ ζ) := by
  -- Step 1: Adapted `C²` coordinates around `(z₀, 0)` and transverse Lipschitz bound for `Jtilde`.
  obtain ⟨m, e, hz₀_e, he_src_Ω₀, -, he_cd, hes_cd, he_axis, hJtilde_axis, -, hJtilde_cd⟩ :=
    exists_adaptedCoordinates (ℓ := 2) (by norm_num) hW hJ hJJ hΩ₀ hu₀ hm₀ hCR₀ hz₀ hnd
  let Jtilde := e.pullbackEnd J
  have hJtilde_c1 : ContDiffOn ℝ 1 Jtilde e.source := hJtilde_cd (by norm_num)
  obtain ⟨r, hr, hball_r, C, hC0, hLip⟩ :=
    exists_closedBall_norm_pullbackEnd_sub_I_le hz₀_e hJtilde_c1 hJtilde_axis
  -- Step 2: Pull back `u₁` to `v = e.symm ∘ u₁ = (a, b)` on a small disc around `ζ₀`.
  let v : ℂ → ℂ × EuclideanSpace ℂ (Fin m) := e.symm ∘ u₁
  let a : ℂ → ℂ := fun ζ ↦ (v ζ).1
  let b : ℂ → EuclideanSpace ℂ (Fin m) := fun ζ ↦ (v ζ).2
  have hu₁_ζ₀_tgt : u₁ ζ₀ ∈ e.target := by
    rw [← heq₀, ← he_axis z₀]
    exact e.map_source hz₀_e
  have hv_ζ₀ : v ζ₀ = (z₀, 0) := by
    change e.symm (u₁ ζ₀) = (z₀, 0)
    rw [← heq₀, ← he_axis z₀, e.left_inv hz₀_e]
  have hu₁_cont : ContinuousAt u₁ ζ₀ := hu₁.continuousOn.continuousAt (hΩ₁.mem_nhds hζ₀)
  have hv_cont : ContinuousAt v ζ₀ :=
    (hes_cd.continuousOn.continuousAt (e.open_target.mem_nhds hu₁_ζ₀_tgt)).comp hu₁_cont
  have hnhds :
      Ω₁ ∩ (u₁ ⁻¹' e.target ∩ v ⁻¹' ball (z₀, (0 : EuclideanSpace ℂ (Fin m))) r) ∈ 𝓝 ζ₀ :=
    Filter.inter_mem (hΩ₁.mem_nhds hζ₀)
      (Filter.inter_mem (hu₁_cont.preimage_mem_nhds (e.open_target.mem_nhds hu₁_ζ₀_tgt))
        (hv_cont.preimage_mem_nhds (hv_ζ₀ ▸ Metric.ball_mem_nhds _ hr)))
  obtain ⟨δ₀, hδ₀, hδ₀_sub⟩ := Metric.mem_nhds_iff.1 hnhds
  set δ : ℝ := δ₀ / 2
  have hδ : 0 < δ := half_pos hδ₀
  set U : Set ℂ := ball ζ₀ δ
  have hK_sub : closedBall ζ₀ δ ⊆ ball ζ₀ δ₀ := closedBall_subset_ball (half_lt_self hδ₀)
  have hU_sub : U ⊆ ball ζ₀ δ₀ := ball_subset_closedBall.trans hK_sub
  have hδ₀_Ω₁ : ball ζ₀ δ₀ ⊆ Ω₁ := fun ζ hζ ↦ (hδ₀_sub hζ).1
  have hδ₀_tgt : MapsTo u₁ (ball ζ₀ δ₀) e.target := fun ζ hζ ↦ (hδ₀_sub hζ).2.1
  have hδ₀_ball : MapsTo v (ball ζ₀ δ₀) (ball (z₀, (0 : EuclideanSpace ℂ (Fin m))) r) :=
    fun ζ hζ ↦ (hδ₀_sub hζ).2.2
  have hv_cd : ContDiffOn ℝ 1 v (ball ζ₀ δ₀) :=
    (hes_cd.of_le (by norm_num)).comp (hu₁.mono hδ₀_Ω₁) hδ₀_tgt
  have hb_cd : ContDiffOn ℝ 1 b U :=
    (contDiff_snd.comp_contDiffOn hv_cd).mono hU_sub
  have ha_cd : ContDiffOn ℝ 1 a U :=
    (contDiff_fst.comp_contDiffOn hv_cd).mono hU_sub
  -- Derivative bound `‖fderiv ℝ v ζ I‖ ≤ M` on `U` via compactness of `closedBall ζ₀ δ`.
  have hDv_cont : ContinuousOn (fun ζ ↦ fderiv ℝ v ζ I) (closedBall ζ₀ δ) :=
    ((hv_cd.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).mono hK_sub).clm_apply
      continuousOn_const
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall ζ₀ δ).exists_bound_of_continuousOn hDv_cont
  set M : ℝ := max M₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hDv_bd (ζ : ℂ) (hζ : ζ ∈ U) : ‖fderiv ℝ v ζ I‖ ≤ M :=
    (hM₀ ζ (ball_subset_closedBall hζ)).trans (le_max_left _ _)
  -- Step 3: Pulled-back Cauchy–Riemann equation for `v` on `U`.
  have hv_CR (ζ : ℂ) (hζ : ζ ∈ U) :
      fderiv ℝ v ζ 1 + Jtilde (v ζ) (fderiv ℝ v ζ I) = 0 := by
    have hζ₀' : ζ ∈ ball ζ₀ δ₀ := hU_sub hζ
    have hu₁_tgt : u₁ ζ ∈ e.target := hδ₀_tgt hζ₀'
    have hv_src : v ζ ∈ e.source := e.map_target hu₁_tgt
    have hev : e (v ζ) = u₁ ζ := e.right_inv hu₁_tgt
    have hd_u₁ : DifferentiableAt ℝ u₁ ζ :=
      (hu₁.differentiableOn one_ne_zero).differentiableAt (hΩ₁.mem_nhds (hδ₀_Ω₁ hζ₀'))
    have hd_es : DifferentiableAt ℝ e.symm (u₁ ζ) :=
      (hes_cd.differentiableOn two_ne_zero).differentiableAt (e.open_target.mem_nhds hu₁_tgt)
    have hd_e : DifferentiableAt ℝ e (v ζ) :=
      (he_cd.differentiableOn two_ne_zero).differentiableAt (e.open_source.mem_nhds hv_src)
    have hfv : fderiv ℝ v ζ = (fderiv ℝ e.symm (u₁ ζ)).comp (fderiv ℝ u₁ ζ) :=
      (hd_es.hasFDerivAt.comp ζ hd_u₁.hasFDerivAt).fderiv
    have hd_es' : DifferentiableAt ℝ e.symm (e (v ζ)) := hev ▸ hd_es
    have hinv : fderiv ℝ e (v ζ) (fderiv ℝ e.symm (e (v ζ)) (fderiv ℝ u₁ ζ I)) =
        fderiv ℝ u₁ ζ I :=
      e.fderiv_apply_fderiv_symm_apply_of_mem_source hv_src hd_e hd_es' _
    rw [hfv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    simp only [Jtilde, OpenPartialHomeomorph.pullbackEnd_apply]
    rw [← hev, hinv, hev, ← map_add, hCR₁ ζ (hδ₀_Ω₁ hζ₀'), map_zero]
  -- Transverse differential inequality `‖∂ₛb + I • ∂ₜb‖ ≤ (C * M) * ‖b‖` on `U`.
  have hb_ineq (ζ : ℂ) (hζ : ζ ∈ U) :
      ‖fderiv ℝ b ζ 1 + I • fderiv ℝ b ζ I‖ ≤ (C * M) * ‖b ζ‖ := by
    have hv_ball : v ζ ∈ closedBall (z₀, (0 : EuclideanSpace ℂ (Fin m))) r :=
      ball_subset_closedBall (hδ₀_ball (hU_sub hζ))
    have hd_v : DifferentiableAt ℝ v ζ :=
      (hv_cd.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds (hU_sub hζ))
    have hfb : fderiv ℝ b ζ =
        (ContinuousLinearMap.snd ℝ ℂ (EuclideanSpace ℂ (Fin m))).comp (fderiv ℝ v ζ) :=
      (hasFDerivAt_snd.comp ζ hd_v.hasFDerivAt).fderiv
    have hvb_eq : fderiv ℝ b ζ 1 + I • fderiv ℝ b ζ I =
        (fderiv ℝ v ζ 1 + I • fderiv ℝ v ζ I).2 := by
      rw [hfb]
      simp
    have hdiff_eq : fderiv ℝ v ζ 1 + I • fderiv ℝ v ζ I =
        -(Jtilde (v ζ) - I • ContinuousLinearMap.id ℝ (ℂ × EuclideanSpace ℂ (Fin m)))
          (fderiv ℝ v ζ I) := by
      have hcr := hv_CR ζ hζ
      simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply, neg_sub]
      calc fderiv ℝ v ζ 1 + I • fderiv ℝ v ζ I
          = (fderiv ℝ v ζ 1 + Jtilde (v ζ) (fderiv ℝ v ζ I)) +
              (I • fderiv ℝ v ζ I - Jtilde (v ζ) (fderiv ℝ v ζ I)) := by abel
        _ = I • fderiv ℝ v ζ I - Jtilde (v ζ) (fderiv ℝ v ζ I) := by rw [hcr, zero_add]
    calc ‖fderiv ℝ b ζ 1 + I • fderiv ℝ b ζ I‖
        = ‖(fderiv ℝ v ζ 1 + I • fderiv ℝ v ζ I).2‖ := by rw [hvb_eq]
      _ ≤ ‖fderiv ℝ v ζ 1 + I • fderiv ℝ v ζ I‖ := by
          rw [Prod.norm_def]; exact le_max_right _ _
      _ = ‖(Jtilde (v ζ) - I • ContinuousLinearMap.id ℝ (ℂ × EuclideanSpace ℂ (Fin m)))
            (fderiv ℝ v ζ I)‖ := by rw [hdiff_eq, norm_neg]
      _ ≤ ‖Jtilde (v ζ) - I • ContinuousLinearMap.id ℝ (ℂ × EuclideanSpace ℂ (Fin m))‖ *
            ‖fderiv ℝ v ζ I‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (C * ‖b ζ‖) * M := by
          gcongr
          · exact hLip (v ζ) hv_ball
          · exact hDv_bd ζ hζ
      _ = (C * M) * ‖b ζ‖ := by ring
  -- Steps 4–5: `b` vanishes identically on `U`; otherwise absorbing the defect via
  -- `rankOneDivNormSq` and applying Carleman's similarity principle isolates the zeros of `b`,
  -- contradicting the accumulation of coincidences.
  have hb_zero : ∀ ζ ∈ U, b ζ = 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨ζ₁, hζ₁, hne⟩ := hall
    have hdisc := setOf_ne_zero_mem_codiscreteWithin_of_norm_add_le
      isOpen_ball (convex_ball ζ₀ δ).isPreconnected hb_cd (mul_nonneg hC0 hM0) hb_ineq
      ⟨ζ₁, hζ₁, hne⟩
    have hmem : ∀ᶠ ζ in 𝓝[≠] ζ₀, ζ ∉ U \ {ζ | b ζ ≠ 0} :=
      disjoint_principal_right.1 (mem_codiscreteWithin.1 hdisc ζ₀ (mem_ball_self hδ))
    have hev : ∀ᶠ ζ in 𝓝[≠] ζ₀, b ζ ≠ 0 := by
      filter_upwards [hmem, nhdsWithin_le_nhds (Metric.ball_mem_nhds ζ₀ hδ)] with ζ hζ hζU
      by_contra h0
      exact hζ ⟨hζU, fun h ↦ h h0⟩
    rw [eventually_nhdsWithin_iff] at hev
    obtain ⟨ε, hε, hε_sub⟩ := Metric.mem_nhds_iff.1
      (Filter.inter_mem hev (Metric.ball_mem_nhds ζ₀ hδ))
    have hnhds_prod : ball z₀ r ×ˢ ball ζ₀ ε ∈ 𝓝 (z₀, ζ₀) :=
      prod_mem_nhds (Metric.ball_mem_nhds z₀ hr) (Metric.ball_mem_nhds ζ₀ hε)
    obtain ⟨⟨z, ζ⟩, ⟨hz_r, hζ_ε⟩, hζ_ne, hu_eq⟩ :=
      mem_closure_iff_nhds.1 hacc _ hnhds_prod
    have hz_src : (z, (0 : EuclideanSpace ℂ (Fin m))) ∈ e.source := by
      refine hball_r ?_
      rw [mem_closedBall, Prod.dist_eq]
      simp only [dist_self, max_eq_left dist_nonneg]
      exact (mem_ball.1 hz_r).le
    have hbz : b ζ = 0 := by
      change (e.symm (u₁ ζ)).2 = 0
      rw [← hu_eq, ← he_axis z, e.left_inv hz_src]
    exact (hε_sub hζ_ε).1 hζ_ne hbz
  -- Step 6: Extract `φ = a`: on `U`, `b ≡ 0`, so `u₁ ζ = u₀ (a ζ)` and `a` is holomorphic.
  refine ⟨U, isOpen_ball, mem_ball_self hδ, hU_sub.trans hδ₀_Ω₁, a, ?_, ?_, ?_, ?_⟩
  · intro ζ hζ
    have hv_eq : v ζ = (a ζ, 0) := Prod.ext rfl (hb_zero ζ hζ)
    have hv_src : v ζ ∈ e.source := e.map_target (hδ₀_tgt (hU_sub hζ))
    have hJaxis : Jtilde (v ζ) =
        I • ContinuousLinearMap.id ℝ (ℂ × EuclideanSpace ℂ (Fin m)) := by
      rw [hv_eq]
      exact hJtilde_axis (a ζ) (hv_eq ▸ hv_src)
    have hcr_v : fderiv ℝ v ζ 1 + I • fderiv ℝ v ζ I = 0 := by
      simpa [hJaxis] using hv_CR ζ hζ
    have hd_v : DifferentiableAt ℝ v ζ :=
      (hv_cd.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds (hU_sub hζ))
    have hfa : fderiv ℝ a ζ =
        (ContinuousLinearMap.fst ℝ ℂ (EuclideanSpace ℂ (Fin m))).comp (fderiv ℝ v ζ) :=
      (hasFDerivAt_fst.comp ζ hd_v.hasFDerivAt).fderiv
    have hcr_a : fderiv ℝ a ζ 1 + I * fderiv ℝ a ζ I = 0 := by
      have := congrArg Prod.fst hcr_v
      simpa [hfa] using this
    have hsqI : (I • ContinuousLinearMap.id ℝ ℂ) ∘L (I • ContinuousLinearMap.id ℝ ℂ) =
        -ContinuousLinearMap.id ℝ ℂ := by
      refine ContinuousLinearMap.ext fun w ↦ ?_
      simp [smul_smul]
    have hinter : ∀ w : ℂ, fderiv ℝ a ζ (I • w) = I • fderiv ℝ a ζ w := by
      have h := (forall_apply_I_mul_eq_iff (L := fderiv ℝ a ζ) hsqI).2 (by simpa using hcr_a)
      simpa [smul_eq_mul] using h
    have hd_a : DifferentiableAt ℝ a ζ :=
      (ha_cd.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hζ)
    have hc_a : HasFDerivAt (𝕜 := ℂ) a ((fderiv ℝ a ζ).complexOfMapISmul hinter) ζ := by
      rw [hasFDerivAt_iff_isLittleO]
      simpa using hd_a.hasFDerivAt.isLittleO
    exact hc_a.differentiableAt.differentiableWithinAt
  · exact congrArg Prod.fst hv_ζ₀
  · intro ζ hζ
    have hv_src : v ζ ∈ e.source := e.map_target (hδ₀_tgt (hU_sub hζ))
    exact (he_src_Ω₀ hv_src).1
  · intro ζ hζ
    have hv_eq : v ζ = (a ζ, 0) := Prod.ext rfl (hb_zero ζ hζ)
    calc u₁ ζ = e (v ζ) := (e.right_inv (hδ₀_tgt (hU_sub hζ))).symm
      _ = e (a ζ, 0) := by rw [hv_eq]
      _ = u₀ (a ζ) := he_axis (a ζ)

/-- **Local factorization of `J`-holomorphic curves** (McDuff–Salamon, Lemma 2.4.3, sequential
form). If `z ν → z₀` and `ζ ν → ζ₀` with `ζ ν ≠ ζ₀` and `u₀ (z ν) = u₁ (ζ ν)` for all `ν`, then
`u₁` factors locally through `u₀` via a holomorphic map `φ` near `ζ₀`. -/
theorem exists_holomorphic_factorization_of_tendsto
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W)
    (hJJ : ∀ x ∈ W, J x ∘L J x = -ContinuousLinearMap.id ℝ V)
    (hΩ₀ : IsOpen Ω₀) (hu₀ : ContDiffOn ℝ 2 u₀ Ω₀) (hm₀ : MapsTo u₀ Ω₀ W)
    (hCR₀ : ∀ z ∈ Ω₀, fderiv ℝ u₀ z 1 + J (u₀ z) (fderiv ℝ u₀ z I) = 0)
    (hΩ₁ : IsOpen Ω₁) (hu₁ : ContDiffOn ℝ 1 u₁ Ω₁)
    (hCR₁ : ∀ ζ ∈ Ω₁, fderiv ℝ u₁ ζ 1 + J (u₁ ζ) (fderiv ℝ u₁ ζ I) = 0)
    {z₀ ζ₀ : ℂ} (hz₀ : z₀ ∈ Ω₀) (hζ₀ : ζ₀ ∈ Ω₁) (hnd : fderiv ℝ u₀ z₀ ≠ 0)
    (heq₀ : u₀ z₀ = u₁ ζ₀)
    {z ζ : ℕ → ℂ} (hz : Tendsto z atTop (𝓝 z₀)) (hζ : Tendsto ζ atTop (𝓝 ζ₀))
    (hne : ∀ ν, ζ ν ≠ ζ₀) (hmatch : ∀ ν, u₀ (z ν) = u₁ (ζ ν)) :
    ∃ U : Set ℂ, IsOpen U ∧ ζ₀ ∈ U ∧ U ⊆ Ω₁ ∧
      ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ U ∧ φ ζ₀ = z₀ ∧
        MapsTo φ U Ω₀ ∧ ∀ ζ ∈ U, u₁ ζ = u₀ (φ ζ) :=
  exists_holomorphic_factorization_of_mem_closure hW hJ hJJ hΩ₀ hu₀ hm₀ hCR₀ hΩ₁ hu₁ hCR₁
    hz₀ hζ₀ hnd heq₀
    (mem_closure_of_tendsto (hz.prodMk_nhds hζ)
      (Filter.Eventually.of_forall fun ν ↦ ⟨hne ν, hmatch ν⟩))

end TauCeti.JHolomorphic
