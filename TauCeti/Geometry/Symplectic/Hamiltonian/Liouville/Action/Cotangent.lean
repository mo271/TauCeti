/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Torus
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Chart

import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
import TauCeti.Geometry.Manifold.RegularValue.Factorization

/-!
# Liouville–Arnold action-angle coordinates on the cotangent bundle of a torus

In `TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Chart`, a compact regular connected
component `L` of a level of `n` pairwise Poisson-commuting functions `F : M → ι → ℝ` on a
`2n`-dimensional boundaryless Hausdorff symplectic manifold `(M, σ)` is parametrized locally by a
universal-cover chart `Ψ : (ι → ℝ) × (ι → ℝ) → M` whose angle variable is `2πℤ^ι`-periodic and
pulls `σ` back to `∑ i, dα_i ∧ dA_i`.

This file descends `Ψ` to the **cotangent bundle of the torus** `Tⁿ = ∀ i, AddCircle (p i)` for any
finite family of positive periods `p : ι → ℝ`, completing the classical Liouville–Arnold theorem:

* rescaling the `i`-th angle and action by `2π / p_i` makes the angle lattice `∏_i p_i ℤ` while
  preserving `∑_i dθ_i ∧ dI_i`;
* descending along the covering `(ι → ℝ) × (ι → ℝ) → T*Tⁿ` defined by
  `TauCeti.CotangentBundle.torusActionAngleDiffeomorph` and inverting on an open action domain
  `D ⊆ (ι → ℝ)` yields a smooth partial diffeomorphism `ψ` from an open neighbourhood `U` of `L` in
  `M` onto `{ξ : T*Tⁿ | torusAction p ξ ∈ D} ≃ Tⁿ × D`, pulling the canonical symplectic form
  `ω = -dλ` of `T*Tⁿ` back to `σ` and expressing `F = h ∘ I` as a smooth local-diffeomorphism
  function of the canonical actions;
* every nonempty level `U ∩ F ⁻¹' {c}` in this neighbourhood is a compact preconnected regular
  torus;
* any smooth Hamiltonian `H : M → ℝ` on `U` that Poisson-commutes with every `F_i` on `U` is a
  smooth function `K` of the actions `I ∘ ψ` alone, and its Hamiltonian trajectories starting in `U`
  are global quasiperiodic linear motions `t ↦ ψ⁻¹(θ₀ + t · ∂K/∂I(I₀), I₀)` on the invariant tori
  (`TauCeti.SmoothTwoForm.IsSymplectic.exists_eqOn_comp_torusAction`,
  `TauCeti.SmoothTwoForm.IsSymplectic.exists_eqOn_comp_torusAction_and_isMIntegralCurve`).

## Main results

All in the namespace `TauCeti.SmoothTwoForm.IsSymplectic`:

* `exists_partialDiffeomorph_cotangentBundle_addCircle_of_isCompact`: local action-angle
  coordinates near a compact regular connected component `L` packaged as a smooth
  `PartialDiffeomorph` onto `{ξ : T*Tⁿ | torusAction p ξ ∈ D}`.
* `exists_eqOn_comp_torusAction`: smooth factorization of any Hamiltonian in involution with `F`
  on `ψ.source` through the canonical actions `torusAction p`.
* `exists_eqOn_comp_torusAction_and_isMIntegralCurve`: factorization and global quasiperiodic
  linear Hamiltonian flow in action-angle coordinates.
* `exists_actionAngle_of_isCompact`: local action-angle coordinates into
  `T*(∀ i, AddCircle (p i))` without completeness or dense-regularity assumptions.
* `exists_actionAngle`: the Liouville–Arnold theorem for a completely integrable system and any
  positive period `p`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, §§49–50.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, §18.4, Theorem 18.12(b).
-/

public section

open Filter Function Module Real Set
open scoped ContDiff Manifold Topology

namespace TauCeti

/-! ### Period scaling and covering of the torus cotangent bundle -/

section Cover

variable {ι : Type*} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)]

/-- Diagonal continuous linear equivalence rescaling `p_i`-periodic coordinates on `ι → ℝ` to
`2π`-periodic coordinates via `u i ↦ (2π / p i) * u i`. -/
private noncomputable def periodScaleEquiv : (ι → ℝ) ≃L[ℝ] (ι → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u i ↦ 2 * π / p i * u i
      map_add' := fun u v ↦ funext fun i ↦ mul_add _ (u i) (v i)
      map_smul' := fun r u ↦ funext fun i ↦ by simp [mul_left_comm]
      invFun := fun v i ↦ p i / (2 * π) * v i
      left_inv := fun u ↦ funext fun i ↦ by
        have hp : p i ≠ 0 := ne_of_gt Fact.out
        dsimp
        field_simp
      right_inv := fun v ↦ funext fun i ↦ by
        have hp : p i ≠ 0 := ne_of_gt Fact.out
        dsimp
        field_simp }

private theorem periodScaleEquiv_apply (u : ι → ℝ) (i : ι) :
    periodScaleEquiv p u i = 2 * π / p i * u i :=
  rfl

private theorem periodScaleEquiv_symm_apply (v : ι → ℝ) (i : ι) :
    (periodScaleEquiv p).symm v i = p i / (2 * π) * v i :=
  rfl

private theorem isLocalDiffeomorph_periodScaleEquiv :
    IsLocalDiffeomorph 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ (periodScaleEquiv p) :=
  isLocalDiffeomorph_of_mfderiv_eq (periodScaleEquiv p).contDiff.contMDiff (by simp) fun _ ↦
    ⟨periodScaleEquiv p, (periodScaleEquiv p).hasFDerivAt.hasMFDerivAt.mfderiv.symm⟩

/-- Shifting `θ` by an integer multiple of the periods `p` shifts `periodScaleEquiv p θ` by the same
integer multiple of `2π`. -/
private theorem periodScaleEquiv_add_mul_int (θ : ι → ℝ) (m : ι → ℤ) :
    periodScaleEquiv p (θ + fun i ↦ p i * (m i : ℝ)) =
      periodScaleEquiv p θ + fun i ↦ 2 * π * (m i : ℝ) := by
  ext i
  have hp : p i ≠ 0 := ne_of_gt Fact.out
  simp only [Pi.add_apply, periodScaleEquiv_apply, mul_add]
  congr 1
  field_simp

/-- Shifting `α` by an integer multiple of `2π` shifts `(periodScaleEquiv p).symm α` by the same
integer multiple of `p`. -/
private theorem periodScaleEquiv_symm_add_two_pi (α : ι → ℝ) (m : ι → ℤ) :
    (periodScaleEquiv p).symm (α + fun i ↦ 2 * π * (m i : ℝ)) =
      (periodScaleEquiv p).symm α + fun i ↦ p i * (m i : ℝ) := by
  ext i
  simp only [Pi.add_apply, periodScaleEquiv_symm_apply, mul_add]
  congr 1
  field_simp

/-- Smooth covering `(ι → ℝ) × (ι → ℝ) → T*(∀ i, AddCircle (p i))` sending `(θ, I)` to the covector
with angle `[θ]` and canonical action `I`. -/
private noncomputable def torusAngleCover (q : (ι → ℝ) × (ι → ℝ)) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) :=
  (CotangentBundle.torusActionAngleDiffeomorph p).symm (fun i ↦ (q.1 i : AddCircle (p i)), q.2)

private theorem contMDiff_torusAngleCover :
    ContMDiff 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (torusAngleCover p) :=
  (CotangentBundle.torusActionAngleDiffeomorph p).symm.contMDiff.comp
    (((AddCircle.contMDiff_pi_coe p ∞).comp
      (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).contMDiff).prodMk
      (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)).contMDiff)

private theorem hasMFDerivAt_angleCoverPair (q : (ι → ℝ) × (ι → ℝ)) :
    HasMFDerivAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
      (fun x : (ι → ℝ) × (ι → ℝ) ↦ (fun i ↦ (x.1 i : AddCircle (p i)), x.2)) q
      (ContinuousLinearMap.id ℝ ((ι → ℝ) × (ι → ℝ))) := by
  have hfst : HasMFDerivAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun x : (ι → ℝ) × (ι → ℝ) ↦ fun i ↦ (x.1 i : AddCircle (p i))) q
      (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)) :=
    ((AddCircle.hasMFDerivAt_pi_coe (p := p) q.1).comp q
      (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).hasMFDerivAt).congr_mfderiv
      (ContinuousLinearMap.id_comp _)
  exact (hfst.prodMk (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)).hasMFDerivAt).congr_mfderiv
    (ContinuousLinearMap.ext fun _ ↦ rfl)

private theorem hasMFDerivAt_torusAngleCover [DecidableEq ι] (q : (ι → ℝ) × (ι → ℝ)) :
    HasMFDerivAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (torusAngleCover p) q
      ((ContinuousLinearMap.id ℝ (ι → ℝ)).prodMap
        ((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).symm :
          (ι → ℝ) →L[ℝ] ((ι → ℝ) →L[ℝ] ℝ))) :=
  ((CotangentBundle.hasMFDerivAt_torusActionAngleDiffeomorph_symm p _).comp q
    (hasMFDerivAt_angleCoverPair p q)).congr_mfderiv (ContinuousLinearMap.comp_id _)

private theorem isLocalDiffeomorph_torusAngleCover :
    IsLocalDiffeomorph 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (torusAngleCover p) := by
  classical
  exact isLocalDiffeomorph_of_mfderiv_eq (contMDiff_torusAngleCover p) (by simp) fun q ↦
    ⟨(ContinuousLinearEquiv.refl ℝ (ι → ℝ)).prodCongr
      (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).symm,
      (hasMFDerivAt_torusAngleCover p q).mfderiv.symm⟩

private theorem torusAngleCover_out_torusAction
    (ξ : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    torusAngleCover p (fun i ↦ Quotient.out (ξ.proj i), CotangentBundle.torusAction p ξ) = ξ := by
  have hθ : (fun i ↦ ((Quotient.out (ξ.proj i) : ℝ) : AddCircle (p i))) = ξ.proj :=
    funext fun i ↦ Quotient.out_eq (ξ.proj i)
  unfold torusAngleCover
  dsimp only
  rw [hθ, ← CotangentBundle.torusActionAngleDiffeomorph_apply]
  exact (CotangentBundle.torusActionAngleDiffeomorph p).symm_apply_apply ξ

private theorem eval₂_torusAngleCover_symplecticForm (q : (ι → ℝ) × (ι → ℝ))
    (u w : (ι → ℝ) × (ι → ℝ)) :
    SmoothBundleForm.eval₂
      (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (∀ i, AddCircle (p i)))
      (torusAngleCover p q)
      (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (torusAngleCover p) q u)
      (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (torusAngleCover p) q w) =
      ∑ i, (u.1 i * w.2 i - w.1 i * u.2 i) := by
  classical
  let g : (ι → ℝ) × (ι → ℝ) → (∀ i, AddCircle (p i)) × (ι → ℝ) :=
    fun x ↦ (fun i ↦ (x.1 i : AddCircle (p i)), x.2)
  have hsymm_d :=
    (CotangentBundle.hasMFDerivAt_torusActionAngleDiffeomorph_symm p (g q)).mdifferentiableAt
  have hg_has := hasMFDerivAt_angleCoverPair p q
  have hderiv : ∀ v : (ι → ℝ) × (ι → ℝ),
      mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) _ (torusAngleCover p) q v =
        mfderiv _ _ (CotangentBundle.torusActionAngleDiffeomorph p).symm (g q) v := fun v ↦ by
    unfold torusAngleCover
    exact (mfderiv_comp_apply q hsymm_d hg_has.mdifferentiableAt v).trans
      (congrArg _ (DFunLike.congr_fun hg_has.mfderiv v))
  rw [hderiv u, hderiv w]
  exact CotangentBundle.eval₂_torusActionAngleDiffeomorph_symm_symplecticForm p (g q) u w

/-- Restrict a local inverse of `periodScaleEquiv p ∘ A` at `c₀ ∈ U₀` to `U₀`. -/
private theorem exists_partialDiffeomorph_action (A : (ι → ℝ) → ι → ℝ)
    {U₀ : Set (ι → ℝ)} {c₀ : ι → ℝ} (hU₀ : IsOpen U₀) (hc₀ : c₀ ∈ U₀)
    (hA : IsLocalDiffeomorphAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ A c₀) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (ι → ℝ) (ι → ℝ) ∞,
      c₀ ∈ e.source ∧ e.source ⊆ U₀ ∧ ∀ c ∈ e.source, A c = (periodScaleEquiv p).symm (e c) := by
  let Ap : (ι → ℝ) → ι → ℝ := periodScaleEquiv p ∘ A
  have hAp : IsLocalDiffeomorphAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ Ap c₀ :=
    hA.comp (hg := isLocalDiffeomorph_periodScaleEquiv p (A c₀))
  let e := hAp.localInverse.symm.restrOpen U₀ hU₀
  have he_src : e.source = hAp.localInverse.symm.source ∩ U₀ :=
    hAp.localInverse.symm.restrOpen_source hU₀
  refine ⟨e, he_src ▸ ⟨hAp.localInverse_mem_target, hc₀⟩,
    he_src.symm ▸ inter_subset_right, fun c hc ↦ ?_⟩
  have hc' : c ∈ hAp.localInverse.symm.source ∩ U₀ := he_src ▸ hc
  have he_c : e c = hAp.localInverse.symm c :=
    congrFun (hAp.localInverse.symm.coe_restrOpen hU₀) c
  have hinv : hAp.localInverse (e c) = c := by
    rw [he_c, PartialDiffeomorph.symm_toPartialEquiv]
    exact hAp.localInverse.right_inv hc'.1
  have hApc : periodScaleEquiv p (A c) = e c := by
    have hmem_src : e c ∈ hAp.localInverse.source := he_c ▸ hAp.localInverse.symm.map_source hc'.1
    simpa only [Ap, Function.comp_apply, hinv] using hAp.localInverse_right_inv hmem_src
  exact (periodScaleEquiv p).symm_apply_apply (A c) ▸ congrArg (periodScaleEquiv p).symm hApc

/-- Invert `periodScaleEquiv p ∘ A` on an open action domain `D`, extending outside `D` by `c₀` so
that `h : (ι → ℝ) → ι → ℝ` takes values in `U₀` everywhere and satisfies the chain-rule identity
`fderiv (A_i) (h J) (fderiv h J b) = (p i / 2π) * b i` on `D`. -/
private theorem exists_actionInverse_of_isLocalDiffeomorphAt {A : (ι → ℝ) → ι → ℝ}
    {U₀ : Set (ι → ℝ)} {c₀ : ι → ℝ} (hU₀ : IsOpen U₀) (hc₀ : c₀ ∈ U₀)
    (hA : IsLocalDiffeomorphAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ A c₀) :
    ∃ (D : Set (ι → ℝ)) (I₀ : ι → ℝ) (h : (ι → ℝ) → ι → ℝ),
      IsOpen D ∧ I₀ ∈ D ∧ h I₀ = c₀ ∧ (∀ J, h J ∈ U₀) ∧
      ContDiffOn ℝ ∞ h D ∧ InjOn h D ∧ IsLocalDiffeomorphOn 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ h D ∧
      ∀ J ∈ D, ∀ i : ι, ∀ b : ι → ℝ,
        fderiv ℝ (fun c ↦ A c i) (h J) (fderiv ℝ h J b) = p i / (2 * π) * b i := by
  obtain ⟨e, hc₀e, heU₀, hAe⟩ := exists_partialDiffeomorph_action p A hU₀ hc₀ hA
  classical
  let D : Set (ι → ℝ) := e.target
  let h : (ι → ℝ) → ι → ℝ := fun J ↦ if J ∈ D then e.symm J else c₀
  have hh_eq : EqOn h e.symm D := fun J hJ ↦ by simp [h, hJ]
  have hhDiff : ContDiffOn ℝ ∞ h D := contMDiffOn_iff_contDiffOn.1 (e.symm.contMDiffOn.congr hh_eq)
  refine ⟨D, e c₀, h, e.open_target, e.map_source hc₀e,
    (hh_eq (e.map_source hc₀e)).trans (e.left_inv hc₀e), fun J ↦ ?_, hhDiff,
    e.symm.injOn.congr hh_eq.symm, fun ⟨J, hJ⟩ ↦ isLocalDiffeomorphAt_of_eqOn hJ hh_eq,
    fun J hJ i b ↦ ?_⟩
  · by_cases hJ : J ∈ D
    · exact hh_eq hJ ▸ heU₀ (e.map_target hJ)
    · simpa [h, hJ] using hc₀
  · have hmem : h J ∈ e.source := hh_eq hJ ▸ e.map_target hJ
    have heDiff : DifferentiableAt ℝ e (h J) :=
      ((contMDiffOn_iff_contDiffOn.1 e.contMDiffOn).contDiffAt
        (e.open_source.mem_nhds hmem)).differentiableAt (by simp)
    have hAi_ev : (fun c ↦ A c i) =ᶠ[𝓝 (h J)] fun c ↦ p i / (2 * π) * e c i := by
      filter_upwards [e.open_source.mem_nhds hmem] with c hc
      exact congrFun (hAe c hc) i
    let pr : (ι → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
    have hAiDiff : DifferentiableAt ℝ (fun c ↦ A c i) (h J) :=
      ((pr.differentiableAt.comp (h J) heDiff).const_mul (p i / (2 * π))).congr_of_eventuallyEq
        hAi_ev
    have hhAt : DifferentiableAt ℝ h J :=
      (hhDiff.contDiffAt (e.open_target.mem_nhds hJ)).differentiableAt (by simp)
    have hcomp_ev : ((fun c ↦ A c i) ∘ h) =ᶠ[𝓝 J] fun K : ι → ℝ ↦ p i / (2 * π) * K i := by
      filter_upwards [e.open_target.mem_nhds hJ] with K hK
      have hKsrc : e.symm K ∈ e.source := e.map_target hK
      simp only [Function.comp_apply]
      rw [hh_eq hK, hAe _ hKsrc, periodScaleEquiv_symm_apply,
        PartialDiffeomorph.symm_toPartialEquiv, e.right_inv hK]
    have hfderiv_comp := DFunLike.congr_fun
      ((fderiv_comp J hAiDiff hhAt).symm.trans hcomp_ev.fderiv_eq) b
    have hlin : HasFDerivAt (fun K : ι → ℝ ↦ p i / (2 * π) * K i)
        ((p i / (2 * π)) • pr) J :=
      pr.hasFDerivAt.const_mul (p i / (2 * π))
    exact hfderiv_comp.trans (by simp [hlin.fderiv, pr])

end Cover

/-! ### Descent to the cotangent bundle and level-set regularity -/

section Helpers

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type*} [Fintype ι] {F : M → ι → ℝ}

/-- Every point of `ψ.source` is regular for `F` when `F = h ∘ torusAction p ∘ ψ` on `ψ.source`
with `h` a local diffeomorphism on `D`. -/
private theorem isRegularPoint_of_eq_comp_torusAction
    (p : ι → ℝ) [∀ i, Fact (0 < p i)]
    (ψ : PartialDiffeomorph I
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      M (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) ∞)
    {D : Set (ι → ℝ)} {h : (ι → ℝ) → ι → ℝ}
    (htarget : ψ.target = {ξ | CotangentBundle.torusAction p ξ ∈ D})
    (hhLoc : IsLocalDiffeomorphOn 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ h D)
    (hFψ : ∀ x ∈ ψ.source, F x = h (CotangentBundle.torusAction p (ψ x))) :
    ∀ x ∈ ψ.source, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x := fun x hx ↦ by
  have hξD : CotangentBundle.torusAction p (ψ x) ∈ D := by
    simpa [htarget] using ψ.map_source hx
  have hF_ev : F =ᶠ[𝓝 x] (h ∘ CotangentBundle.torusAction p) ∘ ψ :=
    eventually_of_mem (ψ.open_source.mem_nhds hx) hFψ
  have hψ_loc := ψ.isLocalDiffeomorphAt _ _ _ hx
  have hh_loc := hhLoc ⟨_, hξD⟩
  have hI_diff := ((CotangentBundle.contMDiff_torusAction p) (ψ x)).mdifferentiableAt (by simp)
  have hsurj_ψ := (hψ_loc.mfderivToContinuousLinearEquiv (by simp)).surjective
  have hsurj_I := isRegularPoint_iff.1 (CotangentBundle.isRegularPoint_torusAction p (ψ x))
  have hsurj_h := (hh_loc.mfderivToContinuousLinearEquiv (by simp)).surjective
  rw [isRegularPoint_iff, hF_ev.mfderiv_eq,
    mfderiv_comp x ((hh_loc.mdifferentiableAt (by simp)).comp (ψ x) hI_diff)
      (hψ_loc.mdifferentiableAt (by simp)),
    mfderiv_comp (ψ x) (hh_loc.mdifferentiableAt (by simp)) hI_diff]
  exact hsurj_h.comp (hsurj_I.comp hsurj_ψ)

/-- Every fibre `ψ.source ∩ F ⁻¹' {c}` is compact and preconnected when `F = h ∘ torusAction p ∘ ψ`
on `ψ.source` with `h` injective on `D`. -/
private theorem isCompact_and_isPreconnected_inter_preimage_of_eq_comp_torusAction
    (p : ι → ℝ) [∀ i, Fact (0 < p i)]
    (ψ : PartialDiffeomorph I
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      M (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) ∞)
    {D : Set (ι → ℝ)} {h : (ι → ℝ) → ι → ℝ}
    (htarget : ψ.target = {ξ | CotangentBundle.torusAction p ξ ∈ D})
    (hhInj : InjOn h D)
    (hFψ : ∀ x ∈ ψ.source, F x = h (CotangentBundle.torusAction p (ψ x))) (c : ι → ℝ) :
    IsCompact (ψ.source ∩ F ⁻¹' {c}) ∧ IsPreconnected (ψ.source ∩ F ⁻¹' {c}) := by
  by_cases hc : ∃ J ∈ D, h J = c
  · obtain ⟨J, hJD, rfl⟩ := hc
    let slice : (∀ i, AddCircle (p i)) → M := fun θ ↦
      ψ.symm ((CotangentBundle.torusActionAngleDiffeomorph p).symm (θ, J))
    have hmem_tgt : ∀ θ, (CotangentBundle.torusActionAngleDiffeomorph p).symm (θ, J) ∈
        ψ.target := fun θ ↦ by
      rw [htarget, mem_ofPred_eq, CotangentBundle.torusAction_torusActionAngleDiffeomorph_symm]
      exact hJD
    have hcont : Continuous slice :=
      ψ.symm.contMDiffOn.continuousOn.comp_continuous
        ((CotangentBundle.torusActionAngleDiffeomorph p).symm.continuous.comp
          (Continuous.prodMk_left J)) hmem_tgt
    have heq : ψ.source ∩ F ⁻¹' {h J} = range slice := by
      ext x
      constructor
      · rintro ⟨hx, hFx⟩
        have hxD : CotangentBundle.torusAction p (ψ x) ∈ D := by
          simpa [htarget] using ψ.map_source hx
        have hJeq : CotangentBundle.torusAction p (ψ x) = J :=
          hhInj hxD hJD ((hFψ x hx).symm.trans hFx)
        refine ⟨(ψ x).proj, ?_⟩
        dsimp only [slice]
        rw [← hJeq, ← CotangentBundle.torusActionAngleDiffeomorph_apply]
        exact (congrArg ψ.symm
          ((CotangentBundle.torusActionAngleDiffeomorph p).symm_apply_apply (ψ x))).trans
          (ψ.left_inv hx)
      · rintro ⟨θ, rfl⟩
        have hsrc : slice θ ∈ ψ.source := ψ.map_target (hmem_tgt θ)
        refine ⟨hsrc, ?_⟩
        rw [mem_preimage, mem_singleton_iff, hFψ _ hsrc]
        dsimp only [slice]
        rw [PartialDiffeomorph.symm_toPartialEquiv, ψ.right_inv (hmem_tgt θ),
          CotangentBundle.torusAction_torusActionAngleDiffeomorph_symm]
    rw [heq]
    exact ⟨isCompact_range hcont, isPreconnected_range hcont⟩
  · have hemp : ψ.source ∩ F ⁻¹' {c} = ∅ := eq_empty_iff_forall_notMem.2 fun x ⟨hx, hFx⟩ ↦ by
      have hxD : CotangentBundle.torusAction p (ψ x) ∈ D := by
        simpa [htarget] using ψ.map_source hx
      exact hc ⟨_, hxD, (hFψ x hx).symm.trans hFx⟩
    rw [hemp]
    exact ⟨isCompact_empty, isPreconnected_empty⟩

/-- Descend a `2πℤ^ι`-periodic chart `Ψ` on `U₀` along `torusAngleCover p` and `h : (ι → ℝ) → U₀` to
an injective local diffeomorphism on `{ξ | torusAction p ξ ∈ D}`. -/
private theorem exists_cotangentDescent (p : ι → ℝ) [∀ i, Fact (0 < p i)]
    {Ψ : (ι → ℝ) × (ι → ℝ) → M} {U₀ D : Set (ι → ℝ)} {h : (ι → ℝ) → ι → ℝ}
    {Φ : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) → M}
    (hΦ : ∀ ξ, Φ ξ = Ψ (periodScaleEquiv p (fun i ↦ Quotient.out (ξ.proj i)),
      h (CotangentBundle.torusAction p ξ)))
    (hhU₀ : ∀ J, h J ∈ U₀) (hhInj : InjOn h D)
    (hhLoc : IsLocalDiffeomorphOn 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ h D)
    (hΨloc : ∀ c ∈ U₀, ∀ θ, IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ (θ, c))
    (hΨper : ∀ c ∈ U₀, ∀ c' ∈ U₀, ∀ θ θ', Ψ (θ, c) = Ψ (θ', c') ↔
      c' = c ∧ ∃ m : ι → ℤ, θ' = θ + fun i ↦ 2 * π * (m i : ℝ)) :
    (∀ q : (ι → ℝ) × (ι → ℝ), Φ (torusAngleCover p q) = Ψ (Prod.map (periodScaleEquiv p) h q)) ∧
      IsLocalDiffeomorphOn
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) I ∞ Φ
        {ξ | CotangentBundle.torusAction p ξ ∈ D} ∧
      InjOn Φ {ξ | CotangentBundle.torusAction p ξ ∈ D} := by
  have hΦ_cover : ∀ q : (ι → ℝ) × (ι → ℝ),
      Φ (torusAngleCover p q) = Ψ (Prod.map (periodScaleEquiv p) h q) := fun ⟨θ, J⟩ ↦ by
    obtain ⟨m, hm⟩ := AddCircle.pi_coe_eq_iff.1
      (funext fun i ↦ (Quotient.out_eq ((θ i : AddCircle (p i)))).symm)
    rw [hΦ]
    dsimp only [torusAngleCover]
    rw [CotangentBundle.proj_torusActionAngleDiffeomorph_symm,
      CotangentBundle.torusAction_torusActionAngleDiffeomorph_symm, hm,
      Prod.map_apply, periodScaleEquiv_add_mul_int]
    exact ((hΨper (h J) (hhU₀ J) (h J) (hhU₀ J) _ _).2 ⟨rfl, m, rfl⟩).symm
  have hcomp_eq : Φ ∘ torusAngleCover p = Ψ ∘ Prod.map (periodScaleEquiv p) h := funext hΦ_cover
  refine ⟨hΦ_cover, fun ⟨ξ, hξ⟩ ↦ ?_, fun ξ₁ hξ₁ ξ₂ hξ₂ h12 ↦ ?_⟩
  · let q : (ι → ℝ) × (ι → ℝ) := (fun i ↦ Quotient.out (ξ.proj i), CotangentBundle.torusAction p ξ)
    have hProd : IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) ∞
        (Prod.map (periodScaleEquiv p) h) q := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact (isLocalDiffeomorph_periodScaleEquiv p q.1).prodMap (hhLoc ⟨q.2, hξ⟩)
    have hcomp : IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ (Φ ∘ torusAngleCover p) q := by
      rw [hcomp_eq]
      exact hProd.comp (hg := hΨloc (h q.2) (hhU₀ q.2) _)
    have hloc := hcomp.of_comp_right (isLocalDiffeomorph_torusAngleCover p q)
    rwa [torusAngleCover_out_torusAction p ξ] at hloc
  · rw [hΦ, hΦ] at h12
    obtain ⟨hh12, m, hm⟩ := (hΨper _ (hhU₀ _) _ (hhU₀ _) _ _).1 h12
    have hact : CotangentBundle.torusAction p ξ₁ = CotangentBundle.torusAction p ξ₂ :=
      hhInj hξ₁ hξ₂ hh12.symm
    have hθ2 := congrArg (periodScaleEquiv p).symm hm
    rw [(periodScaleEquiv p).symm_apply_apply, periodScaleEquiv_symm_add_two_pi,
      (periodScaleEquiv p).symm_apply_apply] at hθ2
    have hproj : (fun i ↦ ((Quotient.out (ξ₁.proj i) : ℝ) : AddCircle (p i))) =
        fun i ↦ ((Quotient.out (ξ₂.proj i) : ℝ) : AddCircle (p i)) :=
      AddCircle.pi_coe_eq_iff.2 ⟨m, hθ2⟩
    rw [← torusAngleCover_out_torusAction p ξ₁, ← torusAngleCover_out_torusAction p ξ₂]
    simp only [torusAngleCover, hproj, hact]

/-- Evaluate `σ` along the cotangent descent `Φ` on `{ξ | torusAction p ξ ∈ D}` by lifting tangent
vectors through `torusAngleCover p` and cancelling the `2π / p i` and `p i / 2π` factors. -/
private theorem eval₂_cotangentDescent [IsManifold I ∞ M] {σ : SmoothTwoForm I M}
    (p : ι → ℝ) [∀ i, Fact (0 < p i)]
    {Ψ : (ι → ℝ) × (ι → ℝ) → M} {A : (ι → ℝ) → ι → ℝ} {U₀ D : Set (ι → ℝ)}
    {h : (ι → ℝ) → ι → ℝ} {Φ : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (∀ i, AddCircle (p i)) → M}
    (hD : IsOpen D) (hhU₀ : ∀ J, h J ∈ U₀) (hhDiff : ContDiffOn ℝ ∞ h D)
    (hΨloc : ∀ c ∈ U₀, ∀ θ, IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ (θ, c))
    (hΨsymp : ∀ c ∈ U₀, ∀ θ a a' b b', SmoothBundleForm.eval₂ σ (Ψ (θ, c))
      (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ (θ, c) (a, b))
      (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ (θ, c) (a', b')) =
      ∑ i, (a i * fderiv ℝ (fun c ↦ A c i) c b' - a' i * fderiv ℝ (fun c ↦ A c i) c b))
    (hAh_fderiv : ∀ J ∈ D, ∀ i : ι, ∀ b : ι → ℝ,
      fderiv ℝ (fun c ↦ A c i) (h J) (fderiv ℝ h J b) = p i / (2 * π) * b i)
    (hΦ_cover : ∀ q : (ι → ℝ) × (ι → ℝ),
      Φ (torusAngleCover p q) = Ψ (Prod.map (periodScaleEquiv p) h q))
    (hΦ_loc : IsLocalDiffeomorphOn
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) I ∞ Φ
      {ξ | CotangentBundle.torusAction p ξ ∈ D})
    {ξ : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))}
    (hξ : CotangentBundle.torusAction p ξ ∈ D)
    (u w : TangentSpace ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ξ) :
    SmoothBundleForm.eval₂ σ (Φ ξ)
      (mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) I Φ ξ u)
      (mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) I Φ ξ w) =
      SmoothBundleForm.eval₂
        (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (∀ i, AddCircle (p i))) ξ u w := by
  have hcomp_eq : Φ ∘ torusAngleCover p = Ψ ∘ Prod.map (periodScaleEquiv p) h := funext hΦ_cover
  let q : (ι → ℝ) × (ι → ℝ) := (fun i ↦ Quotient.out (ξ.proj i), CotangentBundle.torusAction p ξ)
  suffices ∀ ξ', torusAngleCover p q = ξ' → CotangentBundle.torusAction p ξ' ∈ D →
      ∀ u' w' : TangentSpace
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ξ',
        SmoothBundleForm.eval₂ σ (Φ ξ')
          (mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) I Φ ξ' u')
          (mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) I Φ ξ' w') =
          SmoothBundleForm.eval₂
            (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
              (∀ i, AddCircle (p i))) ξ' u' w' by
    exact this ξ (torusAngleCover_out_torusAction p ξ) hξ u w
  rintro _ rfl hq_mem u w
  let L := (isLocalDiffeomorph_torusAngleCover p q).mfderivToContinuousLinearEquiv (by simp)
  let ab := L.symm u
  let ab' := L.symm w
  have hab : mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) _ (torusAngleCover p) q ab = u := by
    rw [← IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe
      (isLocalDiffeomorph_torusAngleCover p q) (by simp)]
    exact L.apply_symm_apply u
  have hab' : mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) _ (torusAngleCover p) q ab' = w := by
    rw [← IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe
      (isLocalDiffeomorph_torusAngleCover p q) (by simp)]
    exact L.apply_symm_apply w
  rw [← hab, ← hab', eval₂_torusAngleCover_symplecticForm p q ab ab']
  have hΦd := (hΦ_loc ⟨_, hq_mem⟩).mdifferentiableAt (by simp)
  have hcovd := ((contMDiff_torusAngleCover p) q).mdifferentiableAt (by simp)
  rw [← mfderiv_comp_apply q hΦd hcovd, ← mfderiv_comp_apply q hΦd hcovd, hcomp_eq, hΦ_cover q]
  have hhAt : DifferentiableAt ℝ h q.2 :=
    (hhDiff.contDiffAt (hD.mem_nhds hξ)).differentiableAt (by simp)
  have hPhas : HasFDerivAt (Prod.map (periodScaleEquiv p) h)
      ((periodScaleEquiv p : (ι → ℝ) →L[ℝ] (ι → ℝ)).prodMap (fderiv ℝ h q.2)) q :=
    HasFDerivAt.prodMap q (periodScaleEquiv p).hasFDerivAt hhAt.hasFDerivAt
  have hΨd := (hΨloc (h q.2) (hhU₀ q.2) (periodScaleEquiv p q.1)).mdifferentiableAt (by simp)
  rw [mfderiv_comp_apply q hΨd hPhas.differentiableAt.mdifferentiableAt,
    mfderiv_comp_apply q hΨd hPhas.differentiableAt.mdifferentiableAt,
    hPhas.hasMFDerivAt.mfderiv, Prod.map_apply]
  refine ((hΨsymp (h q.2) (hhU₀ q.2) (periodScaleEquiv p q.1) (periodScaleEquiv p ab.1)
    (periodScaleEquiv p ab'.1) (fderiv ℝ h q.2 ab.2) (fderiv ℝ h q.2 ab'.2))).trans ?_
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hp : p i ≠ 0 := ne_of_gt Fact.out
  rw [hAh_fderiv q.2 hξ i ab'.2, hAh_fderiv q.2 hξ i ab.2, periodScaleEquiv_apply,
    periodScaleEquiv_apply]
  field_simp

omit [TopologicalSpace M] in
/-- Identify the image of the constant-action slice `{ξ | torusAction p ξ = I₀}` under `Φ` with
`range fun α ↦ Ψ (α, c₀)` when `h I₀ = c₀`. -/
private theorem image_cotangentDescent_setOf_torusAction_eq (p : ι → ℝ) [∀ i, Fact (0 < p i)]
    {Ψ : (ι → ℝ) × (ι → ℝ) → M} {h : (ι → ℝ) → ι → ℝ} {I₀ c₀ : ι → ℝ}
    {Φ : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) → M}
    (hΦ : ∀ ξ, Φ ξ = Ψ (periodScaleEquiv p (fun i ↦ Quotient.out (ξ.proj i)),
      h (CotangentBundle.torusAction p ξ)))
    (hΦ_cover : ∀ q : (ι → ℝ) × (ι → ℝ),
      Φ (torusAngleCover p q) = Ψ (Prod.map (periodScaleEquiv p) h q))
    (hhI₀ : h I₀ = c₀) :
    Φ '' {ξ | CotangentBundle.torusAction p ξ = I₀} = range fun α ↦ Ψ (α, c₀) := by
  ext y
  constructor
  · rintro ⟨ξ, hξI₀ : CotangentBundle.torusAction p ξ = I₀, rfl⟩
    refine ⟨periodScaleEquiv p (fun i ↦ Quotient.out (ξ.proj i)), ?_⟩
    rw [hΦ, hξI₀, hhI₀]
  · rintro ⟨α, rfl⟩
    refine ⟨torusAngleCover p ((periodScaleEquiv p).symm α, I₀), ?_, ?_⟩
    · simp [torusAngleCover]
    · rw [hΦ_cover]
      simp [hhI₀]

end Helpers

/-! ### Main Liouville–Arnold theorems -/

namespace SmoothTwoForm

namespace IsSymplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {ι : Type*} [Fintype ι] {F : M → ι → ℝ}

/-- **Liouville–Arnold action-angle partial diffeomorphism.** Let `F : M → ι → ℝ` be a smooth
family of `n` pairwise Poisson-commuting functions on a `2n`-dimensional Hausdorff boundaryless
symplectic manifold `(M, σ)`, and let the connected component `L` of `x₀` in its level
`F ⁻¹' {F x₀}` be compact and consist of regular points of `F`. No completeness of the Hamiltonian
vector fields or density of regular points is assumed.

Then for every finite family of positive periods `p : ι → ℝ` there are a smooth
`ψ : PartialDiffeomorph` from `M` into the cotangent bundle of `∀ i, AddCircle (p i)`, an open
action domain `D ⊆ (ι → ℝ)`, and a map `h : (ι → ℝ) → ι → ℝ` such that:

* `L ⊆ ψ.source` and `ψ.target = {ξ | torusAction p ξ ∈ D}`;
* `ψ` carries `L` onto the invariant torus `{ξ | torusAction p ξ = torusAction p (ψ x₀)}`;
* `h` is smooth, injective, and a local diffeomorphism on `D`, with
  `F x = h (torusAction p (ψ x))` for all `x ∈ ψ.source`;
* every point of `ψ.source` is regular for `F`, and every level `ψ.source ∩ F ⁻¹' {c}` is compact
  and preconnected;
* `ψ` pulls the canonical symplectic form of `T*(∀ i, AddCircle (p i))` back to `σ` on
  `ψ.source`. -/
theorem exists_partialDiffeomorph_cotangentBundle_addCircle_of_isCompact [T2Space M]
    (hσ : σ.IsSymplectic)
    (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F) (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x₀ : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x₀}) x₀, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hLc : IsCompact (connectedComponentIn (F ⁻¹' {F x₀}) x₀))
    (p : ι → ℝ) [∀ i, Fact (0 < p i)] :
    ∃ (ψ : PartialDiffeomorph I
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        M (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) ∞)
      (D : Set (ι → ℝ)) (h : (ι → ℝ) → ι → ℝ),
      IsOpen D ∧ connectedComponentIn (F ⁻¹' {F x₀}) x₀ ⊆ ψ.source ∧
      ψ.target = {ξ | CotangentBundle.torusAction p ξ ∈ D} ∧
      ψ '' connectedComponentIn (F ⁻¹' {F x₀}) x₀ =
        {ξ | CotangentBundle.torusAction p ξ = CotangentBundle.torusAction p (ψ x₀)} ∧
      ContDiffOn ℝ ∞ h D ∧ InjOn h D ∧ IsLocalDiffeomorphOn 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ h D ∧
      (∀ x ∈ ψ.source, F x = h (CotangentBundle.torusAction p (ψ x))) ∧
      (∀ x ∈ ψ.source, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) ∧
      (∀ c, IsCompact (ψ.source ∩ F ⁻¹' {c}) ∧ IsPreconnected (ψ.source ∩ F ⁻¹' {c})) ∧
      ∀ x ∈ ψ.source, ∀ v w : TangentSpace I x,
        SmoothBundleForm.eval₂
          (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
            (∀ i, AddCircle (p i))) (ψ x)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ψ x v)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ψ x w) =
          SmoothBundleForm.eval₂ σ x v w := by
  -- 1. Extract the `2πℤ^ι`-periodic universal-cover chart `Ψ` and invert the rescaled action map.
  obtain ⟨Ψ, A, U₀, hU₀, hx₀U₀, hA, hrange, hΨU₀⟩ :=
    hσ.exists_isLocalDiffeomorphAt_eval₂_mfderiv_eq_of_isCompact hF hcomm hdim hreg hLc
  obtain ⟨D, I₀, h, hD, hI₀D, hhI₀, hhU₀, hhDiff, hhInj, hhLoc, hAh_fderiv⟩ :=
    exists_actionInverse_of_isLocalDiffeomorphAt p hU₀ hx₀U₀ hA
  -- 2. Descend `Ψ` to `{ξ : T*Tⁿ | torusAction p ξ ∈ D}` and invert it as a `PartialDiffeomorph`.
  let Φ : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) → M :=
    fun ξ ↦ Ψ (periodScaleEquiv p (fun i ↦ Quotient.out (ξ.proj i)),
      h (CotangentBundle.torusAction p ξ))
  obtain ⟨hΦ_cover, hΦ_loc, hΦ_inj⟩ := exists_cotangentDescent (Φ := Φ) p (fun _ ↦ rfl) hhU₀ hhInj
    hhLoc (fun c hc ↦ (hΨU₀ c hc).2.1) (fun c hc ↦ (hΨU₀ c hc).2.2.2)
  let VD : Set (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :=
    {ξ | CotangentBundle.torusAction p ξ ∈ D}
  have hVD : IsOpen VD := hD.preimage (CotangentBundle.contMDiff_torusAction p).continuous
  have : Nonempty (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (∀ i, AddCircle (p i))) := ⟨Bundle.TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) 0 0⟩
  let φ₀ := hΦ_loc.partialDiffeomorphOfInjOn hVD hΦ_inj
  have hφ₀_coe : ⇑φ₀ = Φ := hΦ_loc.coe_partialDiffeomorphOfInjOn hVD hΦ_inj
  set ψ := φ₀.symm
  have hψ_tgt : ψ.target = VD := hΦ_loc.partialDiffeomorphOfInjOn_source hVD hΦ_inj
  have hψ_src : ψ.source = Φ '' VD := hΦ_loc.partialDiffeomorphOfInjOn_target hVD hΦ_inj
  have hΦψ : ∀ x ∈ ψ.source, Φ (ψ x) = x := fun x hx ↦
    (congrFun hφ₀_coe (ψ x)).symm.trans (ψ.left_inv hx)
  have hψΦ : ∀ ξ ∈ VD, ψ (Φ ξ) = ξ := fun ξ hξ ↦ by
    have hmem : ξ ∈ φ₀.source :=
      (hΦ_loc.partialDiffeomorphOfInjOn_source hVD hΦ_inj).symm ▸ hξ
    exact (congrArg ψ (congrFun hφ₀_coe ξ)).symm.trans (φ₀.left_inv hmem)
  clear_value ψ
  -- 3. Identify `L` with the `I₀`-slice, deduce fibre regularity/compactness, and pull back `ω`.
  have hL_eq : connectedComponentIn (F ⁻¹' {F x₀}) x₀ =
      Φ '' {ξ | CotangentBundle.torusAction p ξ = I₀} :=
    hrange.symm.trans
      (image_cotangentDescent_setOf_torusAction_eq p (fun _ ↦ rfl) hΦ_cover hhI₀).symm
  have hL_sub : connectedComponentIn (F ⁻¹' {F x₀}) x₀ ⊆ ψ.source := by
    rw [hL_eq, hψ_src]
    exact image_mono fun ξ (hξ : CotangentBundle.torusAction p ξ = I₀) ↦ mem_ofPred.2 (hξ ▸ hI₀D)
  have hFψ : ∀ x ∈ ψ.source, F x = h (CotangentBundle.torusAction p (ψ x)) := fun x hx ↦
    (congrArg F (hΦψ x hx).symm).trans ((hΨU₀ _ (hhU₀ _)).1 _)
  refine ⟨ψ, D, h, hD, hL_sub, hψ_tgt, ?_, hhDiff, hhInj, hhLoc, hFψ,
    isRegularPoint_of_eq_comp_torusAction p ψ hψ_tgt hhLoc hFψ,
    isCompact_and_isPreconnected_inter_preimage_of_eq_comp_torusAction p ψ hψ_tgt hhInj hFψ,
    fun x hx v w ↦ ?_⟩
  · have hx₀_src : x₀ ∈ ψ.source := hL_sub (mem_connectedComponentIn rfl)
    have hψx₀ : CotangentBundle.torusAction p (ψ x₀) = I₀ :=
      hhInj (by simpa [hψ_tgt, VD] using ψ.map_source hx₀_src) hI₀D
        ((hFψ x₀ hx₀_src).symm.trans hhI₀.symm)
    rw [hψx₀, hL_eq]
    ext ξ
    constructor
    · rintro ⟨y, ⟨ξ', hξ'I₀ : CotangentBundle.torusAction p ξ' = I₀, rfl⟩, rfl⟩
      rwa [hψΦ ξ' (mem_ofPred.2 (hξ'I₀ ▸ hI₀D))]
    · intro (hξI₀ : CotangentBundle.torusAction p ξ = I₀)
      exact ⟨Φ ξ, ⟨ξ, hξI₀, rfl⟩, hψΦ ξ (mem_ofPred.2 (hξI₀ ▸ hI₀D))⟩
  · have hξVD : ψ x ∈ VD := hψ_tgt ▸ ψ.map_source hx
    have hleft_ev : Φ ∘ ψ =ᶠ[𝓝 x] id :=
      eventually_of_mem (ψ.open_source.mem_nhds hx) fun y hy ↦ hΦψ y hy
    have hΦd := (hΦ_loc ⟨_, hξVD⟩).mdifferentiableAt (by simp)
    have hψd := ψ.mdifferentiableAt (by simp) hx
    have hinv_deriv : ∀ u : TangentSpace I x,
        mfderiv _ I Φ (ψ x) (mfderiv I _ ψ x u) = u := fun u ↦ by
      refine (mfderiv_comp_apply x hΦd hψd u).symm.trans ?_
      -- `tangentSpaceCast` between tangent spaces at equal points is the identity on vectors.
      rw [hleft_ev.mfderiv_eq, mfderiv_id]
      rfl
    have hsymp := eval₂_cotangentDescent p hD hhU₀ hhDiff
      (fun c hc ↦ (hΨU₀ c hc).2.1) (fun c hc ↦ (hΨU₀ c hc).2.2.1) hAh_fderiv hΦ_cover hΦ_loc hξVD
      (mfderiv I _ ψ x v) (mfderiv I _ ψ x w)
    rw [hinv_deriv v, hinv_deriv w, hΦψ x hx] at hsymp
    exact hsymp.symm

/-- **Hamiltonians in involution with `F` depend only on the canonical actions.** Given an
action-angle partial diffeomorphism `ψ` into `T*(∀ i, AddCircle (p i))`, any smooth function
`H : M → ℝ` on `ψ.source` that Poisson-commutes there with every `F_i` factors on `ψ.source` as
`K ∘ torusAction p ∘ ψ` for a smooth function `K` on `D`. -/
theorem exists_eqOn_comp_torusAction (hσ : σ.IsSymplectic)
    (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F) (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) (p : ι → ℝ) [∀ i, Fact (0 < p i)]
    (ψ : PartialDiffeomorph I
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      M (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) ∞)
    {D : Set (ι → ℝ)} (hD : IsOpen D) {h : (ι → ℝ) → ι → ℝ}
    (htarget : ψ.target = {ξ | CotangentBundle.torusAction p ξ ∈ D})
    (hhDiff : ContDiffOn ℝ ∞ h D) (hhInj : InjOn h D)
    (hhLoc : IsLocalDiffeomorphOn 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ h D)
    (hFψ : ∀ x ∈ ψ.source, F x = h (CotangentBundle.torusAction p (ψ x)))
    {H : M → ℝ} (hH : ContMDiffOn I 𝓘(ℝ) ∞ H ψ.source)
    (hHF : ∀ x ∈ ψ.source, ∀ i, σ.poissonBracket (F · i) H x = 0) :
    ∃ K : (ι → ℝ) → ℝ, ContDiffOn ℝ ∞ K D ∧
      EqOn H (K ∘ CotangentBundle.torusAction p ∘ ψ) ψ.source := by
  have hregU := isRegularPoint_of_eq_comp_torusAction p ψ htarget hhLoc hFψ
  have hfibU :=
    isCompact_and_isPreconnected_inter_preimage_of_eq_comp_torusAction p ψ htarget hhInj hFψ
  have hker : ∀ y ∈ ψ.source, (mfderiv I 𝓘(ℝ, ι → ℝ) F y).ker ≤ (mfderiv I 𝓘(ℝ) H y).ker := by
    intro y hy v hv
    rw [hσ.isNondegenerate.ker_mfderiv_eq_span_hamiltonianVectorField (hregU y hy)
      (hcomm · · y) hdim] at hv
    refine Submodule.span_induction ?_ (Submodule.zero_mem _)
      (fun _ _ _ _ ha hb ↦ Submodule.add_mem _ ha hb)
      (fun r _ _ ha ↦ Submodule.smul_mem _ r ha) hv
    rintro _ ⟨i, rfl⟩
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    have hpb : mvfderiv I H y (σ.hamiltonianVectorField (F · i) y) = 0 := by
      have h1 := hσ.isNondegenerate.poissonBracket_eq_neg_mvfderiv (F · i) H y
      rw [hHF y hy i, eq_comm, neg_eq_zero] at h1
      exact h1
    exact (mvfderiv_apply_eq_mfderiv_apply H y _).symm.trans hpb
  obtain ⟨g, hgH, hgDiff⟩ := exists_eqOn_comp_of_ker_mfderiv_le ψ.open_source hregU
    hF.contMDiffOn hH (by simp) hker fun c ↦ (hfibU c).2
  refine ⟨g ∘ h, fun J hJ ↦ ?_, fun y hy ↦ (hgH hy).trans (congrArg g (hFψ y hy))⟩
  let ξ₀ := (CotangentBundle.torusActionAngleDiffeomorph p).symm (0, J)
  have hξ₀ : ξ₀ ∈ ψ.target := by simp [ξ₀, htarget, hJ]
  have hx₀ : ψ.symm ξ₀ ∈ ψ.source := ψ.map_target hξ₀
  have hFx₀ : F (ψ.symm ξ₀) = h J :=
    (hFψ _ hx₀).trans (by
      dsimp only [ξ₀]
      rw [PartialDiffeomorph.symm_toPartialEquiv, ψ.right_inv hξ₀,
        CotangentBundle.torusAction_torusActionAngleDiffeomorph_symm])
  exact ((hFx₀ ▸ hgDiff _ hx₀).comp J (hhDiff.contDiffAt (hD.mem_nhds hJ))).contDiffWithinAt

omit [I.Boundaryless] in
/-- Push the Hamiltonian vector field of `K ∘ torusAction p` forward along `ψ.symm` to
`σ.hamiltonianVectorField H` when `H = K ∘ torusAction p ∘ ψ` on `ψ.source`. -/
private theorem mfderiv_symm_hamiltonianVectorField_comp_torusAction (hσ : σ.IsSymplectic)
    (p : ι → ℝ) [∀ i, Fact (0 < p i)]
    (ψ : PartialDiffeomorph I
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      M (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) ∞)
    {D : Set (ι → ℝ)} (hD : IsOpen D)
    (htarget : ψ.target = {ξ | CotangentBundle.torusAction p ξ ∈ D})
    (hψsymp : ∀ x ∈ ψ.source, ∀ v w : TangentSpace I x,
      SmoothBundleForm.eval₂
        (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (∀ i, AddCircle (p i))) (ψ x)
        (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ψ x v)
        (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ψ x w) =
        SmoothBundleForm.eval₂ σ x v w)
    {H : M → ℝ} {K : (ι → ℝ) → ℝ} (hKDiff : ContDiffOn ℝ ∞ K D)
    (hHK : EqOn H (K ∘ CotangentBundle.torusAction p ∘ ψ) ψ.source)
    {y : M} (hy : y ∈ ψ.source)
    {ξ : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))}
    (hξ : ψ y = ξ) :
    mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) I ψ.symm ξ
      ((CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (∀ i, AddCircle (p i))).hamiltonianVectorField
        (K ∘ CotangentBundle.torusAction p) ξ) =
      σ.hamiltonianVectorField H y := by
  subst hξ
  have hyD : CotangentBundle.torusAction p (ψ y) ∈ D := by
    simpa [htarget] using ψ.map_source hy
  have hKT_diff : MDifferentiableAt _ 𝓘(ℝ) (K ∘ CotangentBundle.torusAction p) (ψ y) :=
    (((hKDiff.contDiffAt (hD.mem_nhds hyD)).differentiableAt (by simp)).mdifferentiableAt).comp
      (ψ y) (((CotangentBundle.contMDiff_torusAction p) (ψ y)).mdifferentiableAt (by simp))
  have hHK_ev : H =ᶠ[𝓝 y] (K ∘ CotangentBundle.torusAction p) ∘ ψ :=
    eventually_of_mem (ψ.open_source.mem_nhds hy) hHK
  have hfwd : mfderiv I _ ψ y (σ.hamiltonianVectorField H y) =
      (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (∀ i, AddCircle (p i))).hamiltonianVectorField
        (K ∘ CotangentBundle.torusAction p) (ψ y) :=
    hσ.isNondegenerate.map_hamiltonianVectorField_of_eval₂
      (CotangentBundle.isSymplectic_symplecticForm
        (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (M := ∀ i, AddCircle (p i))).isNondegenerate
      (((ψ.isLocalDiffeomorphAt _ _ _ hy).mfderivToContinuousLinearEquiv (by simp)).surjective _)
      (hψsymp y hy) fun u ↦ by
        rw [← mvfderiv_comp_apply y hKT_diff (ψ.mdifferentiableAt (by simp) hy) u,
          ← hHK_ev.mvfderiv_eq]
  rw [← hfwd]
  have hleft_ev : ψ.symm ∘ ψ =ᶠ[𝓝 y] id :=
    eventually_of_mem (ψ.open_source.mem_nhds hy) fun z hz ↦ ψ.left_inv hz
  refine (mfderiv_comp_apply y (ψ.symm.mdifferentiableAt (by simp) (ψ.map_source hy))
    (ψ.mdifferentiableAt (by simp) hy) _).symm.trans ?_
  -- `tangentSpaceCast` between tangent spaces at equal points is the identity on vectors.
  rw [hleft_ev.mfderiv_eq, mfderiv_id]
  rfl

/-- **Quasiperiodic linear Hamiltonian flow in action-angle coordinates.** Given an action-angle
partial diffeomorphism `ψ` into `T*(∀ i, AddCircle (p i))` as produced by
`exists_partialDiffeomorph_cotangentBundle_addCircle_of_isCompact`, any smooth Hamiltonian
`H : M → ℝ` on `ψ.source` that Poisson-commutes there with every `F_i` is a smooth function `K` of
the canonical actions `torusAction p ∘ ψ` alone, and for every initial point `x ∈ ψ.source` the
uniform linear motion on its invariant torus with frequencies `ν_i = ∂K/∂I_i(I(ψ x))` pushes
forward under `ψ.symm` to a global integral curve of `σ.hamiltonianVectorField H` inside
`ψ.source`. -/
theorem exists_eqOn_comp_torusAction_and_isMIntegralCurve [DecidableEq ι] (hσ : σ.IsSymplectic)
    (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F) (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) (p : ι → ℝ) [∀ i, Fact (0 < p i)]
    (ψ : PartialDiffeomorph I
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      M (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) ∞)
    {D : Set (ι → ℝ)} (hD : IsOpen D) {h : (ι → ℝ) → ι → ℝ}
    (htarget : ψ.target = {ξ | CotangentBundle.torusAction p ξ ∈ D})
    (hhDiff : ContDiffOn ℝ ∞ h D) (hhInj : InjOn h D)
    (hhLoc : IsLocalDiffeomorphOn 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ h D)
    (hFψ : ∀ x ∈ ψ.source, F x = h (CotangentBundle.torusAction p (ψ x)))
    (hψsymp : ∀ x ∈ ψ.source, ∀ v w : TangentSpace I x,
      SmoothBundleForm.eval₂
        (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (∀ i, AddCircle (p i))) (ψ x)
        (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ψ x v)
        (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ψ x w) =
        SmoothBundleForm.eval₂ σ x v w)
    {H : M → ℝ} (hH : ContMDiffOn I 𝓘(ℝ) ∞ H ψ.source)
    (hHF : ∀ x ∈ ψ.source, ∀ i, σ.poissonBracket (F · i) H x = 0) :
    ∃ K : (ι → ℝ) → ℝ, ContDiffOn ℝ ∞ K D ∧
      EqOn H (K ∘ CotangentBundle.torusAction p ∘ ψ) ψ.source ∧
      ∀ x ∈ ψ.source,
        let I₀ := CotangentBundle.torusAction p (ψ x)
        let γ : ℝ → M := fun t ↦ ψ.symm
          ((CotangentBundle.torusActionAngleDiffeomorph p).symm
            ((ψ x).proj + fun i ↦
              ((t * fderiv ℝ K I₀ (Pi.single i 1) : ℝ) : AddCircle (p i)), I₀))
        (∀ t, γ t ∈ ψ.source) ∧ γ 0 = x ∧
          IsMIntegralCurve γ (σ.hamiltonianVectorField H) := by
  obtain ⟨K, hKDiff, hHK⟩ :=
    hσ.exists_eqOn_comp_torusAction hF hcomm hdim p ψ hD htarget hhDiff hhInj hhLoc hFψ hH hHF
  refine ⟨K, hKDiff, hHK, fun x hx ↦ ?_⟩
  set I₀ := CotangentBundle.torusAction p (ψ x)
  have hI₀D : I₀ ∈ D := by simpa [I₀, htarget] using ψ.map_source hx
  let γT : ℝ → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) :=
    fun t ↦ (CotangentBundle.torusActionAngleDiffeomorph p).symm
      ((ψ x).proj + fun i ↦ ((t * fderiv ℝ K I₀ (Pi.single i 1) : ℝ) : AddCircle (p i)), I₀)
  have hγT_tgt : ∀ t, γT t ∈ ψ.target := fun t ↦ by simp [γT, htarget, hI₀D]
  have hγ0 : ψ.symm (γT 0) = x := by
    have h0 :
        (fun i : ι ↦ (((0 : ℝ) * fderiv ℝ K I₀ (Pi.single i 1) : ℝ) : AddCircle (p i))) = 0 :=
      funext fun _ ↦ by simp
    simp only [γT, h0, add_zero]
    dsimp only [I₀]
    rw [← CotangentBundle.torusActionAngleDiffeomorph_apply p (ψ x)]
    exact (congrArg ψ.symm
      ((CotangentBundle.torusActionAngleDiffeomorph p).symm_apply_apply (ψ x))).trans
      (ψ.left_inv hx)
  refine ⟨fun t ↦ ψ.map_target (hγT_tgt t), hγ0, ?_⟩
  have hKAt : DifferentiableAt ℝ K I₀ :=
    (hKDiff.contDiffAt (hD.mem_nhds hI₀D)).differentiableAt (by simp)
  have hγT_int := CotangentBundle.isMIntegralCurve_torusActionAngleDiffeomorph_symm_add p
    (ψ x).proj hKAt
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at hγT_int ⊢
  exact hγT_int.map_of_mfderiv_eq
    (fun t _ ↦ ψ.symm.mdifferentiableAt (by simp) (hγT_tgt t))
    fun t _ ↦ hσ.mfderiv_symm_hamiltonianVectorField_comp_torusAction p ψ hD htarget hψsymp hKDiff
      hHK (ψ.map_target (hγT_tgt t)) (ψ.symm.left_inv (hγT_tgt t))

/-- **Local action-angle coordinates near a compact regular connected component.** Without assuming
completeness or dense regular points, any compact connected component `L` of a level of `n`
pairwise Poisson-commuting smooth functions `F : M → ι → ℝ` consisting of regular points has an
open neighbourhood `U` carrying an injective smooth local diffeomorphism `φ` onto
`{ξ : T*(∀ i, AddCircle (p i)) | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D}` that pulls the canonical
symplectic form back to `σ` and expresses `F = h ∘ I` via a smooth local diffeomorphism `h` on
`D`. -/
theorem exists_actionAngle_of_isCompact [T2Space M] [DecidableEq ι] (hσ : σ.IsSymplectic)
    (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F) (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {L : Set M} {x₀ : M}
    (hL : L = connectedComponentIn (F ⁻¹' {F x₀}) x₀) (hLc : IsCompact L)
    (hreg : ∀ x ∈ L, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x)
    (p : ι → ℝ) [∀ i, Fact (0 < p i)] :
    ∃ U : Set M, IsOpen U ∧ L ⊆ U ∧ ∃ D : Set (ι → ℝ), IsOpen D ∧
      ∃ φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)),
        InjOn φ U ∧
        IsLocalDiffeomorphOn I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ φ U ∧
        φ '' U = {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D} ∧
        (∀ x ∈ U, ∀ v w : TangentSpace I x,
          SmoothBundleForm.eval₂
              (CotangentBundle.symplecticForm
                (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) (φ x)
              (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
                𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ x v)
              (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
                𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ x w) =
            SmoothBundleForm.eval₂ σ x v w) ∧
        ∃ h : (ι → ℝ) → ι → ℝ, ContDiffOn ℝ ∞ h D ∧ InjOn h D ∧
          IsLocalDiffeomorphOn 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ h D ∧
          ∀ x ∈ U, F x = h (fun i ↦ (φ x).2 (Pi.single i 1)) := by
  subst hL
  obtain ⟨ψ, D, h, hD, hL_sub, hψ_tgt, -, hhDiff, hhInj, hhLoc, hFψ, -, -, hψsymp⟩ :=
    hσ.exists_partialDiffeomorph_cotangentBundle_addCircle_of_isCompact hF hcomm hdim hreg hLc p
  refine ⟨ψ.source, ψ.open_source, hL_sub, D, hD, ψ, ψ.injOn,
    fun ⟨x, hx⟩ ↦ ψ.isLocalDiffeomorphAt _ _ _ hx, ?_, hψsymp, h, hhDiff, hhInj, hhLoc,
    fun x hx ↦ ?_⟩
  · rw [ψ.image_source_eq_target, hψ_tgt]
    simp only [CotangentBundle.torusAction_def]
  · simpa only [CotangentBundle.torusAction_def] using hFψ x hx

/-- **The Liouville–Arnold theorem: action-angle coordinates.** Let `F : M → ι → ℝ` be a
completely integrable system on a Hausdorff boundaryless symplectic manifold `(M, σ)` of dimension
`2 · |ι|`, and let `L` be the connected component through `x₀` of the level `F ⁻¹' {F x₀}`; assume
`L` compact and every point of `L` a regular point of `F`. Other components of the level need not
be regular, and no completeness is assumed.

Then for every positive period `p` there are an open neighbourhood `U` of `L`, an open set
`D ⊆ (ι → ℝ)`, and a map `φ` from `M` to the cotangent bundle of the angle torus
`Tⁿ = ι → AddCircle p` which, on `U`, is an injective smooth local diffeomorphism onto the
covectors `ξ` whose actions `I_i(ξ) = ξ(e_i)` lie in `D`, pulls the canonical symplectic form
`ω = -dλ = ∑_i dθ_i ∧ dI_i` back to `σ`, and expresses `F = h ∘ I` via a smooth injective local
diffeomorphism `h` on `D`. For `p = 2π` these are the classical action-angle coordinates. -/
theorem exists_actionAngle [T2Space M] [DecidableEq ι] (hσ : σ.IsSymplectic)
    (hF : σ.IsIntegrableSystem F)
    {L : Set M} {x₀ : M} (hL : L = connectedComponentIn (F ⁻¹' {F x₀}) x₀) (hLc : IsCompact L)
    (hreg : ∀ x ∈ L, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) (p : ℝ) [Fact (0 < p)] :
    ∃ U : Set M, IsOpen U ∧ L ⊆ U ∧ ∃ D : Set (ι → ℝ), IsOpen D ∧
      ∃ φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p),
        InjOn φ U ∧
        IsLocalDiffeomorphOn I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ φ U ∧
        φ '' U = {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D} ∧
        (∀ x ∈ U, ∀ v w : TangentSpace I x,
          SmoothBundleForm.eval₂
              (CotangentBundle.symplecticForm
                (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) (φ x)
              (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
                𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ x v)
              (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
                𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ x w) =
            SmoothBundleForm.eval₂ σ x v w) ∧
        ∃ h : (ι → ℝ) → ι → ℝ, ContDiffOn ℝ ∞ h D ∧ InjOn h D ∧
          IsLocalDiffeomorphOn 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ h D ∧
          ∀ x ∈ U, F x = h (fun i ↦ (φ x).2 (Pi.single i 1)) :=
  hσ.exists_actionAngle_of_isCompact hF.contMDiff hF.poissonBracket_eq_zero
    hF.two_mul_card_eq_finrank hL hLc hreg fun _ ↦ p

end IsSymplectic

end SmoothTwoForm

end TauCeti
