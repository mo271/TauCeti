/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Torus
public import TauCeti.Geometry.Symplectic.Hamiltonian.Integrable

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Chart

/-!
# The Liouville–Arnold action–angle theorem in torus cotangent coordinates

Let `σ` be a symplectic form on a Hausdorff boundaryless `2n`-dimensional manifold `M`, and let
`F : M → ι → ℝ` (`|ι| = n`) be a smooth family of pairwise Poisson-commuting functions. When the
connected component `L` of `x₀` in its level `F⁻¹(F x₀)` is compact and consists of regular points
of `F`, the local chart theorem
`TauCeti.SmoothTwoForm.IsSymplectic.exists_isLocalDiffeomorphAt_eval₂_mfderiv_eq_of_isCompact`
produces an angle-action covering chart `Ψ : (ι → ℝ) × (ι → ℝ) → M` with `2π`-periodic angles and
action coordinates `A` near `F x₀` pulling `σ` back to `∑ i, dθ_i ∧ dA_i`.

This file descends that covering chart to a genuine symplectic coordinate chart into the cotangent
bundle `T*Tⁿ` of the torus `Tⁿ = ∀ i, AddCircle (p i)` of any prescribed positive periods
`p : ι → ℝ`:

* Rescaling the `i`-th angle by `2π / p i` and the `i`-th action by `p i / (2π)` matches the
  `p`-lattice periodicity of `TauCeti.CotangentBundle.torusCover` while keeping the pulled-back
  two-form equal to the standard pairing `a ⬝ᵥ b' - a' ⬝ᵥ b`.
* Descending along the surjective local diffeomorphism `TauCeti.CotangentBundle.torusCover` and
  inverting via `IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn` gives an open neighbourhood `U` of
  `L`, an open action domain `D ⊆ ι → ℝ`, and a map `φ : M → T*Tⁿ` which on `U` is an injective
  smooth local diffeomorphism onto `{ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D}`, pulls the canonical
  cotangent symplectic form `ω = -dλ` back to `σ`, and expresses `F` on `U` as `h(I)` for an
  injective local diffeomorphism `h` on `D` (`TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle`
  and `TauCeti.SmoothTwoForm.IsIntegrableSystem.exists_actionAngle`).

For `p = fun _ ↦ 2 * π` these are the classical action–angle coordinates. Neither global
completeness of the Hamiltonian vector fields nor regularity of other components of the level is
assumed.

## Main results

* `TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle`: local action–angle coordinates in
  `T*(∀ i, AddCircle (p i))` near a compact regular connected component of a level of `n`
  Poisson-commuting functions on a `2n`-dimensional symplectic manifold.
* `TauCeti.SmoothTwoForm.IsIntegrableSystem.exists_actionAngle`: specialization to a completely
  integrable system `σ.IsIntegrableSystem F`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 49–50.
* J. J. Duistermaat, *On global action-angle coordinates*, Communications on Pure and Applied
  Mathematics 33 (1980), 687–706, Theorem 1.1.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.4, Theorem 18.12(b).
-/

public section

noncomputable section

open Set Function Filter Module Real
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothTwoForm

section Helpers

variable {ι : Type*} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)]

/-- Diagonal linear equivalence rescaling coordinates of period `p i` to period `2π`:
`t ↦ fun i ↦ (2 * π / p i) * t i`, with inverse `θ ↦ fun i ↦ (p i / (2 * π)) * θ i`. -/
private def angleScale : (ι → ℝ) ≃L[ℝ] (ι → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun t i := (2 * π / p i) * t i
      map_add' t t' := funext fun i ↦ mul_add _ _ _
      map_smul' r t := funext fun i ↦ by simp [mul_left_comm]
      invFun θ i := (p i / (2 * π)) * θ i
      left_inv t := funext fun i ↦ by
        have hp : p i ≠ 0 := (Fact.out : 0 < p i).ne'
        field_simp
      right_inv θ := funext fun i ↦ by
        have hp : p i ≠ 0 := (Fact.out : 0 < p i).ne'
        field_simp }

@[simp]
private theorem angleScale_apply (t : ι → ℝ) (i : ι) :
    angleScale p t i = (2 * π / p i) * t i :=
  rfl

@[simp]
private theorem angleScale_symm_apply (θ : ι → ℝ) (i : ι) :
    (angleScale p).symm θ i = (p i / (2 * π)) * θ i :=
  rfl

/-- Pairing `angleScale p` with its inverse cancels the period factors coordinatewise. -/
private theorem angleScale_mul_symm (a b : ι → ℝ) (i : ι) :
    angleScale p a i * (angleScale p).symm b i = a i * b i := by
  have hp : p i ≠ 0 := (Fact.out : 0 < p i).ne'
  simp only [angleScale_apply, angleScale_symm_apply]
  field_simp

/-- Under `angleScale p`, `2π`-shifts correspond to integer multiples of the periods `p i`. -/
private theorem exists_angleScale_eq_add_two_pi_iff {t t' : ι → ℝ} :
    (∃ m : ι → ℤ, angleScale p t' = angleScale p t + fun i ↦ 2 * π * m i) ↔
      ∃ m : ι → ℤ, ∀ i, t' i = t i + m i • p i := by
  refine exists_congr fun m ↦ ?_
  rw [funext_iff]
  refine forall_congr' fun i ↦ ?_
  have hp : p i ≠ 0 := (Fact.out : 0 < p i).ne'
  have hπ : (2 * π : ℝ) ≠ 0 := Real.two_pi_pos.ne'
  have hscale : 2 * π / p i ≠ 0 := div_ne_zero hπ hp
  simp only [Pi.add_apply, angleScale_apply, zsmul_eq_mul]
  constructor <;> intro h
  · apply mul_left_cancel₀ hscale
    calc (2 * π / p i) * t' i = (2 * π / p i) * t i + 2 * π * m i := h
      _ = (2 * π / p i) * (t i + m i * p i) := by field_simp
  · rw [h]
    field_simp

/-- Being a `C^n` local diffeomorphism at `x` is invariant under eventual equality at `x`. -/
private theorem isLocalDiffeomorphAt_congr_of_eventuallyEq
    {𝕜 E F H G M N : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace H] [TopologicalSpace G]
    {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
    {n : WithTop ℕ∞} {f g : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J n f x) (hfg : g =ᶠ[𝓝 x] f) :
    IsLocalDiffeomorphAt I J n g x := by
  obtain ⟨O, hO, hOo, hxO⟩ := mem_nhds_iff.1 <| hfg.and <|
    hf.contMDiffAt.continuousAt.preimage_mem_nhds
      (hf.localInverse_open_source.mem_nhds hf.localInverse_mem_source)
  refine isLocalDiffeomorphAt_of_eqOn (Φ := hf.localInverse.symm.restrOpen O hOo)
    (by simp [hf.localInverse_mem_target, hxO]) fun y hy ↦ ?_
  rw [PartialDiffeomorph.restrOpen_source] at hy
  rw [PartialDiffeomorph.coe_restrOpen]
  calc g y = f y := (hO hy.2).1
    _ = hf.localInverse.symm (hf.localInverse (f y)) :=
      (hf.localInverse.left_inv (hO hy.2).2).symm
    _ = hf.localInverse.symm y := congrArg _ (hf.localInverse_left_inv hy.1)

/-- When `A (h J) = (angleScale p).symm J` for all `J` in an open set `D`, differentiating at
`J ∈ D` gives `(dA_i)_{h J} (dh_J b) = (angleScale p).symm b i`. -/
private theorem fderiv_comp_symm_angleScale
    {A h : (ι → ℝ) → ι → ℝ} {D : Set (ι → ℝ)} (hD : IsOpen D)
    (hAh : ∀ J ∈ D, A (h J) = (angleScale p).symm J)
    {J : ι → ℝ} (hJ : J ∈ D)
    (hdA : DifferentiableAt ℝ A (h J)) (hdh : DifferentiableAt ℝ h J)
    (i : ι) (b : ι → ℝ) :
    fderiv ℝ (fun c ↦ A c i) (h J) (fderiv ℝ h J b) = (angleScale p).symm b i := by
  let L : (ι → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).comp
      (angleScale p).symm.toContinuousLinearMap
  have heq : ((fun c ↦ A c i) ∘ h) =ᶠ[𝓝 J] ⇑L := by
    filter_upwards [hD.mem_nhds hJ] with J' hJ'
    exact congrFun (hAh J' hJ') i
  have hdAi : DifferentiableAt ℝ (fun c ↦ A c i) (h J) := (differentiableAt_pi.1 hdA) i
  have hcomp := DFunLike.congr_fun ((fderiv_comp J hdAi hdh).symm.trans heq.fderiv_eq) b
  simpa [L, ContinuousLinearMap.fderiv] using hcomp

/-- Rescaling angles by `angleScale p` and actions by `h` (where `A (h J) = (angleScale p).symm J`
on `D`) converts the action–angle pullback `∑ i, (dθ_i ∧ dA_i)` of `Ψ` into `a ⬝ᵥ b' - a' ⬝ᵥ b`. -/
private theorem eval₂_mfderiv_comp_prodMap_angleScale
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M]
    {σ : SmoothTwoForm I M} {Ψ : (ι → ℝ) × (ι → ℝ) → M} {A h : (ι → ℝ) → ι → ℝ}
    {D : Set (ι → ℝ)} (hD : IsOpen D) (hAh : ∀ J ∈ D, A (h J) = (angleScale p).symm J)
    {t J : ι → ℝ} (hJ : J ∈ D)
    (hdA : DifferentiableAt ℝ A (h J)) (hdh : DifferentiableAt ℝ h J)
    (hdΨ : MDifferentiableAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ (angleScale p t, h J))
    (hpullΨ : ∀ a a' b b', SmoothBundleForm.eval₂ σ (Ψ (angleScale p t, h J))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ (angleScale p t, h J) (a, b))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ (angleScale p t, h J) (a', b')) =
      ∑ i, (a i * fderiv ℝ (fun c ↦ A c i) (h J) b' -
        a' i * fderiv ℝ (fun c ↦ A c i) (h J) b))
    (a b a' b' : ι → ℝ) :
    SmoothBundleForm.eval₂ σ ((Ψ ∘ Prod.map (angleScale p) h) (t, J))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (Ψ ∘ Prod.map (angleScale p) h) (t, J) (a, b))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (Ψ ∘ Prod.map (angleScale p) h) (t, J) (a', b')) =
      a ⬝ᵥ b' - a' ⬝ᵥ b := by
  let S := angleScale p
  let fstL := S.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))
  have hdsnd : HasFDerivAt (h ∘ ⇑(ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)))
      ((fderiv ℝ h J).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))) (t, J) :=
    hdh.hasFDerivAt.comp (t, J) (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)).hasFDerivAt
  have hdP : HasFDerivAt (Prod.map (⇑S) h)
      (fstL.prod ((fderiv ℝ h J).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)))) (t, J) :=
    fstL.hasFDerivAt.prodMk hdsnd
  have hmP (u v : ι → ℝ) :
      mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (Ψ ∘ Prod.map S h) (t, J) (u, v) =
        mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ (S t, h J) (S u, fderiv ℝ h J v) :=
    DFunLike.congr_fun (hdΨ.hasMFDerivAt.comp (t, J) hdP.hasMFDerivAt).mfderiv (u, v)
  refine (congrArg₂ (SmoothBundleForm.eval₂ σ (Ψ (S t, h J))) (hmP a b) (hmP a' b')).trans ?_
  refine (hpullΨ (S a) (S a') (fderiv ℝ h J b) (fderiv ℝ h J b')).trans ?_
  simp only [fderiv_comp_symm_angleScale p hD hAh hJ hdA hdh, S, angleScale_mul_symm,
    dotProduct, Finset.sum_sub_distrib]

/-- **Rescaling the covering chart to arbitrary positive periods.** Inverting the local action map
`A` near `F x₀` and rescaling angles by `2π / p i` and actions by `p i / (2π)` yields an open action
domain `D`, an injective smooth local diffeomorphism `h` on `D`, and a covering parametrization
`Ψ_p : (ι → ℝ) × (ι → ℝ) → M` with `p`-lattice periodicity and standard symplectic pullback. -/
private theorem IsSymplectic.exists_rescaled_covering
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
    {F : M → ι → ℝ} (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
    (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x₀ : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x₀}) x₀, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x₀}) x₀)) :
    ∃ (D : Set (ι → ℝ)) (h : (ι → ℝ) → ι → ℝ) (Ψ_p : (ι → ℝ) × (ι → ℝ) → M),
      IsOpen D ∧
      IsLocalDiffeomorphOn 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ h D ∧
      InjOn h D ∧
      (∀ y ∈ connectedComponentIn (F ⁻¹' {F x₀}) x₀, ∃ t, ∃ J ∈ D, Ψ_p (t, J) = y) ∧
      (∀ J ∈ D, ∀ t, F (Ψ_p (t, J)) = h J) ∧
      (∀ J ∈ D, ∀ t, IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ_p (t, J)) ∧
      (∀ J ∈ D, ∀ t a b a' b', SmoothBundleForm.eval₂ σ (Ψ_p (t, J))
          (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ_p (t, J) (a, b))
          (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ_p (t, J) (a', b')) =
        a ⬝ᵥ b' - a' ⬝ᵥ b) ∧
      (∀ J ∈ D, ∀ J' ∈ D, ∀ t t',
        Ψ_p (t, J) = Ψ_p (t', J') ↔
          CotangentBundle.torusCover p (t, J) = CotangentBundle.torusCover p (t', J')) := by
  obtain ⟨Ψ, A, U₀, hU₀, hx₀U, hA, hrange, hW⟩ :=
    hσ.exists_isLocalDiffeomorphAt_eval₂_mfderiv_eq_of_isCompact hF hcomm hdim hreg hK
  obtain ⟨U₁, hU₁A, hU₁o, hx₀U₁⟩ := mem_nhds_iff.1 hA.eventually
  let q := hA.localInverse
  let V_A : Set (ι → ℝ) := q.source ∩ q ⁻¹' (U₀ ∩ U₁)
  have hV_A : IsOpen V_A :=
    q.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage q.open_source (hU₀.inter hU₁o)
  let S := angleScale p
  let D : Set (ι → ℝ) := S.symm ⁻¹' V_A
  have hD : IsOpen D := hV_A.preimage S.symm.continuous
  let h : (ι → ℝ) → ι → ℝ := fun J ↦ q (S.symm J)
  have hh_loc : IsLocalDiffeomorphOn 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ h D := fun ⟨J, hJ⟩ ↦
    (S.symm.toDiffeomorph.isLocalDiffeomorph J).comp
      (hg := q.isLocalDiffeomorphAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ hJ.1)
  have hh_inj : InjOn h D :=
    (q.toPartialEquiv.injOn.mono inter_subset_left).comp S.symm.injective.injOn fun _ hJ ↦ hJ
  have hAh (J : ι → ℝ) (hJ : J ∈ D) : A (h J) = S.symm J := hA.localInverse_right_inv hJ.1
  refine ⟨D, h, Ψ ∘ Prod.map S h, hD, hh_loc, hh_inj, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [← hrange] at hy
    obtain ⟨θ, rfl⟩ := hy
    have hq_inv : q (A (F x₀)) = F x₀ := hA.localInverse_left_inv hA.localInverse_mem_target
    refine ⟨S.symm θ, S (A (F x₀)), ?_, by simp [h, hq_inv]⟩
    -- Unfold `D = S.symm ⁻¹' (q.source ∩ q ⁻¹' (U₀ ∩ U₁))` to verify membership of `S (A (F x₀))`.
    change S.symm (S (A (F x₀))) ∈ q.source ∧ q (S.symm (S (A (F x₀)))) ∈ U₀ ∩ U₁
    rw [S.symm_apply_apply, hq_inv]
    exact ⟨hA.localInverse_mem_source, hx₀U, hx₀U₁⟩
  · exact fun J hJ t ↦ (hW (h J) hJ.2.1).1 (S t)
  · intro J hJ t
    have hprod : IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) ∞
        (Prod.map S h) (t, J) := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact (S.toDiffeomorph.isLocalDiffeomorph t).prodMap (hh_loc ⟨J, hJ⟩)
    exact hprod.comp (hg := (hW (h J) hJ.2.1).2.1 (S t))
  · exact fun J hJ t a b a' b' ↦ eval₂_mfderiv_comp_prodMap_angleScale p hD hAh hJ
      (mdifferentiableAt_iff_differentiableAt.1 ((hU₁A hJ.2.2).mdifferentiableAt (by simp)))
      (mdifferentiableAt_iff_differentiableAt.1 ((hh_loc ⟨J, hJ⟩).mdifferentiableAt (by simp)))
      (((hW (h J) hJ.2.1).2.1 (S t)).mdifferentiableAt (by simp))
      ((hW (h J) hJ.2.1).2.2.1 (S t)) a b a' b'
  · intro J hJ J' hJ' t t'
    rw [CotangentBundle.torusCover_eq_iff, ← exists_angleScale_eq_add_two_pi_iff p]
    refine ((hW (h J) hJ.2.1).2.2.2 (h J') hJ'.2.1 (S t) (S t')).trans ?_
    exact and_congr_left' (hh_inj.eq_iff hJ' hJ)

/-- When `Φ ∘ torusCover p` agrees with `Ψ_p` on `univ ×ˢ D` and `torusCover p (t, J) = Φ.symm x`,
a tangent vector `(u₁, u₂)` mapped by `d(torusCover p)_{(t, J)}` to `d(Φ.symm)_x u` is mapped by
`d(Ψ_p)_{(t, J)}` to `u`. -/
private theorem mfderiv_eq_of_eventuallyEq_comp_torusCover
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {D : Set (ι → ℝ)} (hD : IsOpen D) {Ψ_p : (ι → ℝ) × (ι → ℝ) → M}
    (Φ : PartialDiffeomorph
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) I
      (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) M ∞)
    (hΦ_cover : ∀ {t J : ι → ℝ}, J ∈ D → Φ (CotangentBundle.torusCover p (t, J)) = Ψ_p (t, J))
    {t J : ι → ℝ} (hJ : J ∈ D) {x : M} (hx : x ∈ Φ.target)
    (hcover : CotangentBundle.torusCover p (t, J) = Φ.symm x)
    {u₁ u₂ : ι → ℝ} {u : TangentSpace I x}
    (hu : mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (CotangentBundle.torusCover p) (t, J) (u₁, u₂) =
        mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) Φ.symm x u) :
    mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ_p (t, J) (u₁, u₂) = u := by
  let J_cot := (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)
  let T_cot := CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))
  let V_cot := (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)
  have hφs : Φ.symm x ∈ Φ.source := Φ.map_target hx
  have hc := CotangentBundle.isLocalDiffeomorph_torusCover p (t, J)
  have heq : Ψ_p =ᶠ[𝓝 (t, J)] (Φ ∘ CotangentBundle.torusCover p) := by
    filter_upwards [(isOpen_univ.prod hD).mem_nhds ⟨mem_univ t, hJ⟩] with q hq
    exact (hΦ_cover hq.2).symm
  have hmd := ((Φ.mdifferentiableAt (by simp) (hcover.symm ▸ hφs)).hasMFDerivAt).comp (t, J)
    (hc.mdifferentiableAt (by simp)).hasMFDerivAt
  have hcomp : mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ_p (t, J) (u₁, u₂) =
      mfderiv J_cot I Φ (CotangentBundle.torusCover p (t, J))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) J_cot (CotangentBundle.torusCover p) (t, J) (u₁, u₂)) :=
    DFunLike.congr_fun (hmd.congr_of_eventuallyEq_abuse heq).mfderiv (u₁, u₂)
  let w₀ : V_cot := mfderiv I J_cot Φ.symm x u
  have hstep1 : mfderiv J_cot I Φ (CotangentBundle.torusCover p (t, J))
      (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) J_cot (CotangentBundle.torusCover p) (t, J) (u₁, u₂)) =
      (mfderiv J_cot I Φ (CotangentBundle.torusCover p (t, J)) w₀ : E) :=
    congrArg (fun q : V_cot ↦ (mfderiv J_cot I Φ (CotangentBundle.torusCover p (t, J)) q : E)) hu
  have hstep2 : (mfderiv J_cot I Φ (CotangentBundle.torusCover p (t, J)) w₀ : E) =
      (mfderiv J_cot I Φ (Φ.symm x) w₀ : E) :=
    congrArg (fun ξ : T_cot ↦ (mfderiv J_cot I Φ ξ w₀ : E)) hcover
  exact hcomp.trans (hstep1.trans (hstep2.trans
    (Φ.mfderiv_apply_mfderiv_symm_apply (by simp) hx u)))

/-- When a partial diffeomorphism `Φ : T*Tⁿ → M` satisfies `Φ ∘ torusCover p = Ψ_p` on `univ ×ˢ D`
and `Ψ_p` pulls `σ` back to `a ⬝ᵥ b' - a' ⬝ᵥ b`, the inverse `Φ.symm` pulls the canonical torus
symplectic form back to `σ` at every `x ∈ Φ.target`. -/
private theorem eval₂_symplecticForm_symm_of_torusCover
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] {σ : SmoothTwoForm I M}
    {D : Set (ι → ℝ)} (hD : IsOpen D) {Ψ_p : (ι → ℝ) × (ι → ℝ) → M}
    (hpull : ∀ J ∈ D, ∀ t a b a' b', SmoothBundleForm.eval₂ σ (Ψ_p (t, J))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ_p (t, J) (a, b))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ_p (t, J) (a', b')) =
      a ⬝ᵥ b' - a' ⬝ᵥ b)
    (Φ : PartialDiffeomorph
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) I
      (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) M ∞)
    (hΦ_src : Φ.source = {ξ | (CotangentBundle.torusDiffeomorph p ξ).2 ∈ D})
    (hΦ_cover : ∀ {t J : ι → ℝ}, J ∈ D → Φ (CotangentBundle.torusCover p (t, J)) = Ψ_p (t, J))
    {x : M} (hx : x ∈ Φ.target) (v w : TangentSpace I x) :
    SmoothBundleForm.eval₂
        (CotangentBundle.symplecticForm
          (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) (Φ.symm x)
        (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) Φ.symm x v)
        (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) Φ.symm x w) =
      SmoothBundleForm.eval₂ σ x v w := by
  let J_cot := (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)
  let T_cot := CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))
  let V_cot := (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)
  obtain ⟨⟨t, J⟩, hcover⟩ := CotangentBundle.torusCover_surjective p (Φ.symm x)
  have hφs : Φ.symm x ∈ Φ.source := Φ.map_target hx
  have hJ : J ∈ D := by
    rw [hΦ_src, mem_ofPred_eq, ← hcover, CotangentBundle.torusDiffeomorph_torusCover] at hφs
    exact hφs
  have hxΨ : Ψ_p (t, J) = x := (hΦ_cover hJ).symm.trans (hcover ▸ Φ.right_inv hx)
  have hc := CotangentBundle.isLocalDiffeomorph_torusCover p (t, J)
  obtain ⟨⟨a, b⟩, hab⟩ := (hc.isInvertible_mfderiv (by simp)).surjective
    (mfderiv I J_cot Φ.symm x v)
  obtain ⟨⟨a', b'⟩, hab'⟩ := (hc.isInvertible_mfderiv (by simp)).surjective
    (mfderiv I J_cot Φ.symm x w)
  let evalCot (ξ : T_cot) (u₁ u₂ : V_cot) : ℝ :=
    SmoothBundleForm.eval₂
      (CotangentBundle.symplecticForm
        (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) ξ u₁ u₂
  have hlhs : evalCot (Φ.symm x) (mfderiv I J_cot Φ.symm x v) (mfderiv I J_cot Φ.symm x w) =
      a ⬝ᵥ b' - a' ⬝ᵥ b := by
    have h1 : evalCot (Φ.symm x) (mfderiv I J_cot Φ.symm x v) (mfderiv I J_cot Φ.symm x w) =
        evalCot (CotangentBundle.torusCover p (t, J)) (mfderiv I J_cot Φ.symm x v)
          (mfderiv I J_cot Φ.symm x w) :=
      congrArg (fun ξ ↦ evalCot ξ (mfderiv I J_cot Φ.symm x v) (mfderiv I J_cot Φ.symm x w))
        hcover.symm
    exact h1.trans ((congrArg₂ (evalCot (CotangentBundle.torusCover p (t, J)))
      hab.symm hab'.symm).trans (CotangentBundle.eval₂_symplecticForm_torusCover p t J a b a' b'))
  have hrhs : SmoothBundleForm.eval₂ σ x v w = a ⬝ᵥ b' - a' ⬝ᵥ b := by
    have hv := mfderiv_eq_of_eventuallyEq_comp_torusCover p hD Φ hΦ_cover hJ hx hcover hab
    have hw := mfderiv_eq_of_eventuallyEq_comp_torusCover p hD Φ hΦ_cover hJ hx hcover hab'
    cases hxΨ
    exact (congrArg₂ (SmoothBundleForm.eval₂ σ (Ψ_p (t, J))) hv.symm hw.symm).trans
      (hpull J hJ t a b a' b')
  exact hlhs.trans hrhs.symm

/-- A local diffeomorphism `Ψ_p` on `univ ×ˢ D` whose point-identifications match those of
`CotangentBundle.torusCover p` descends to a partial diffeomorphism `Φ : T*Tⁿ → M` with source
`{ξ | (torusDiffeomorph p ξ).2 ∈ D}` and target containing `L`. -/
private theorem exists_partialDiffeomorph_torusCover
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {L : Set M} {D : Set (ι → ℝ)} (hD : IsOpen D) {Ψ_p : (ι → ℝ) × (ι → ℝ) → M}
    (hcov : ∀ y ∈ L, ∃ t, ∃ J ∈ D, Ψ_p (t, J) = y)
    (hloc : ∀ J ∈ D, ∀ t, IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ_p (t, J))
    (hper : ∀ J ∈ D, ∀ J' ∈ D, ∀ t t',
      Ψ_p (t, J) = Ψ_p (t', J') ↔
        CotangentBundle.torusCover p (t, J) = CotangentBundle.torusCover p (t', J')) :
    ∃ Φ : PartialDiffeomorph
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) I
        (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) M ∞,
      Φ.source = {ξ | (CotangentBundle.torusDiffeomorph p ξ).2 ∈ D} ∧
      L ⊆ Φ.target ∧
      ∀ {t J : ι → ℝ}, J ∈ D → Φ (CotangentBundle.torusCover p (t, J)) = Ψ_p (t, J) := by
  let J_cot := (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)
  let T_cot := CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))
  have : Nonempty T_cot := ⟨CotangentBundle.torusCover p 0⟩
  let V : Set T_cot := {ξ | (CotangentBundle.torusDiffeomorph p ξ).2 ∈ D}
  have hV : IsOpen V :=
    hD.preimage (continuous_snd.comp (CotangentBundle.torusDiffeomorph p).continuous)
  let g : T_cot → M := fun ξ ↦ Ψ_p (surjInv (CotangentBundle.torusCover_surjective p) ξ)
  -- On `univ ×ˢ D`, `g ∘ torusCover p` agrees with `Ψ_p`.
  have hg_cover {t J : ι → ℝ} (hJ : J ∈ D) :
      g (CotangentBundle.torusCover p (t, J)) = Ψ_p (t, J) := by
    set z := surjInv (CotangentBundle.torusCover_surjective p) (CotangentBundle.torusCover p (t, J))
    have hz : CotangentBundle.torusCover p z = CotangentBundle.torusCover p (t, J) :=
      surjInv_eq (CotangentBundle.torusCover_surjective p) _
    have hzJ : z.2 = J := ((CotangentBundle.torusCover_eq_iff p).1 hz.symm).1
    exact (hper z.2 (hzJ.symm ▸ hJ) J hJ z.1 t).2 hz
  have hg_loc : IsLocalDiffeomorphOn J_cot I ∞ g V := fun ⟨ξ, hξ⟩ ↦ by
    obtain ⟨⟨t, J⟩, rfl⟩ := CotangentBundle.torusCover_surjective p ξ
    have hJ : J ∈ D := by rwa [mem_ofPred_eq, CotangentBundle.torusDiffeomorph_torusCover] at hξ
    have heq : (g ∘ CotangentBundle.torusCover p) =ᶠ[𝓝 (t, J)] Ψ_p := by
      filter_upwards [(isOpen_univ.prod hD).mem_nhds ⟨mem_univ t, hJ⟩] with q hq
      exact hg_cover hq.2
    exact (isLocalDiffeomorphAt_congr_of_eventuallyEq (hloc J hJ t) heq).of_comp_right
      (CotangentBundle.isLocalDiffeomorph_torusCover p (t, J))
  have hg_inj : InjOn g V := by
    intro ξ hξ ξ' hξ' hgg
    obtain ⟨⟨t, J⟩, rfl⟩ := CotangentBundle.torusCover_surjective p ξ
    obtain ⟨⟨t', J'⟩, rfl⟩ := CotangentBundle.torusCover_surjective p ξ'
    have hJ : J ∈ D := by rwa [mem_ofPred_eq, CotangentBundle.torusDiffeomorph_torusCover] at hξ
    have hJ' : J' ∈ D := by rwa [mem_ofPred_eq, CotangentBundle.torusDiffeomorph_torusCover] at hξ'
    rw [hg_cover hJ, hg_cover hJ'] at hgg
    exact (hper J hJ J' hJ' t t').1 hgg
  let Φ : PartialDiffeomorph J_cot I T_cot M ∞ := hg_loc.partialDiffeomorphOfInjOn hV hg_inj
  refine ⟨Φ, hg_loc.partialDiffeomorphOfInjOn_source hV hg_inj, ?_,
    fun hJ ↦ (congrFun (hg_loc.coe_partialDiffeomorphOfInjOn hV hg_inj) _).trans (hg_cover hJ)⟩
  rw [hg_loc.partialDiffeomorphOfInjOn_target hV hg_inj]
  intro y hy
  obtain ⟨t, J, hJ, rfl⟩ := hcov y hy
  exact ⟨CotangentBundle.torusCover p (t, J), by simp [V, hJ], hg_cover hJ⟩

/-- **Descending a `p`-periodic symplectic covering chart along `torusCover p`.** Inverting the
partial diffeomorphism from `exists_partialDiffeomorph_torusCover` furnishes torus action–angle
coordinates on an open neighbourhood `U` of `L`. -/
private theorem descend_torusCover
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] {σ : SmoothTwoForm I M}
    {L : Set M} {D : Set (ι → ℝ)} (hD : IsOpen D)
    {F : M → ι → ℝ} {h : (ι → ℝ) → ι → ℝ} {Ψ_p : (ι → ℝ) × (ι → ℝ) → M}
    (hcov : ∀ y ∈ L, ∃ t, ∃ J ∈ D, Ψ_p (t, J) = y)
    (hFΨ : ∀ J ∈ D, ∀ t, F (Ψ_p (t, J)) = h J)
    (hloc : ∀ J ∈ D, ∀ t, IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ_p (t, J))
    (hpull : ∀ J ∈ D, ∀ t a b a' b', SmoothBundleForm.eval₂ σ (Ψ_p (t, J))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ_p (t, J) (a, b))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ_p (t, J) (a', b')) =
      a ⬝ᵥ b' - a' ⬝ᵥ b)
    (hper : ∀ J ∈ D, ∀ J' ∈ D, ∀ t t',
      Ψ_p (t, J) = Ψ_p (t', J') ↔
        CotangentBundle.torusCover p (t, J) = CotangentBundle.torusCover p (t', J')) :
    ∃ U : Set M, IsOpen U ∧ L ⊆ U ∧
      ∃ φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)),
        InjOn φ U ∧
        IsLocalDiffeomorphOn I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ φ U ∧
        φ '' U = {ξ | (CotangentBundle.torusDiffeomorph p ξ).2 ∈ D} ∧
        (∀ x ∈ U, ∀ v w : TangentSpace I x,
          SmoothBundleForm.eval₂
              (CotangentBundle.symplecticForm
                (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) (φ x)
              (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
                𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ x v)
              (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
                𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ x w) =
            SmoothBundleForm.eval₂ σ x v w) ∧
        ∀ x ∈ U, F x = h (CotangentBundle.torusDiffeomorph p (φ x)).2 := by
  let J_cot := (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)
  obtain ⟨Φ, hΦ_src, hLΦ, hΦ_cover⟩ := exists_partialDiffeomorph_torusCover p hD hcov hloc hper
  refine ⟨Φ.target, Φ.open_target, hLΦ, Φ.symm, Φ.toPartialEquiv.symm.injOn,
    fun x ↦ Φ.symm.isLocalDiffeomorphAt I J_cot ∞ x.2,
    Φ.symm.toPartialEquiv.image_source_eq_target.trans hΦ_src,
    fun x hx v w ↦ eval₂_symplecticForm_symm_of_torusCover p hD hpull Φ hΦ_src hΦ_cover hx v w,
    ?_⟩
  intro x hx
  obtain ⟨⟨t, J⟩, hcover⟩ := CotangentBundle.torusCover_surjective p (Φ.symm x)
  have hφs : Φ.symm x ∈ Φ.source := Φ.map_target hx
  have hJ : J ∈ D := by
    rwa [hΦ_src, mem_ofPred_eq, ← hcover, CotangentBundle.torusDiffeomorph_torusCover] at hφs
  have hxΨ : x = Ψ_p (t, J) := (Φ.right_inv hx).symm.trans (hcover ▸ hΦ_cover hJ)
  calc F x = F (Ψ_p (t, J)) := congrArg F hxΨ
    _ = h J := hFΨ J hJ t
    _ = h (CotangentBundle.torusDiffeomorph p (Φ.symm x)).2 := by
      rw [← hcover, CotangentBundle.torusDiffeomorph_torusCover]

end Helpers

namespace IsSymplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {σ : SmoothTwoForm I M} {ι : Type*} [Fintype ι] [DecidableEq ι] {F : M → ι → ℝ}

/-- **The Liouville–Arnold theorem: action–angle coordinates.** Let `F : M → ι → ℝ` be a smooth
family of `n = |ι|` pairwise Poisson-commuting functions on a Hausdorff boundaryless symplectic
manifold `(M, σ)` of dimension `2n`, and let `L` be the connected component through `x₀` of the
level `F⁻¹(F x₀)`. Assume `L` is compact and every point of `L` is a regular point of `F`; other
components of the level need not be regular, and no global completeness is assumed. Then for every
family of positive periods `p : ι → ℝ` there are an open neighbourhood `U` of `L`, an open action
domain `D ⊆ ι → ℝ`, and a map `φ` from `M` to the cotangent bundle of the torus
`Tⁿ = ∀ i, AddCircle (p i)` which, on `U`, is an injective smooth local diffeomorphism onto the
covectors `ξ` whose actions `I_i(ξ) = ξ(e_i)` lie in `D`, pulls the canonical form `ω = -dλ` back
to `σ`, and expresses `F` on `U` as `h(I)` for an injective smooth local diffeomorphism `h` on `D`.
For `p = fun _ ↦ 2 * π` these are the classical action–angle coordinates. -/
theorem exists_actionAngle (hσ : σ.IsSymplectic)
    (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
    (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
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
        ∃ h : (ι → ℝ) → ι → ℝ,
          IsLocalDiffeomorphOn 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ h D ∧
          InjOn h D ∧
          ∀ x ∈ U, F x = h (fun i ↦ (φ x).2 (Pi.single i 1)) := by
  subst hL
  obtain ⟨D, h, Ψ_p, hD, hh_loc, hh_inj, hcov, hFΨ, hloc, hpull, hper⟩ :=
    hσ.exists_rescaled_covering p hF hcomm hdim hreg hLc
  obtain ⟨U, hU, hLU, φ, hφ_inj, hφ_loc, hφ_img, hφ_pull, hφ_F⟩ :=
    descend_torusCover p hD hcov hFΨ hloc hpull hper
  simp only [CotangentBundle.torusDiffeomorph_snd] at hφ_img hφ_F
  exact ⟨U, hU, hLU, D, hD, φ, hφ_inj, hφ_loc, hφ_img, hφ_pull, h, hh_loc, hh_inj, hφ_F⟩

end IsSymplectic

namespace IsIntegrableSystem

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {σ : SmoothTwoForm I M} {ι : Type*} [Fintype ι] [DecidableEq ι] {F : M → ι → ℝ}

/-- **The Liouville–Arnold theorem for a completely integrable system.** For a completely integrable
system `F : M → ι → ℝ` on `(M, σ)` and a compact connected component `L` of `F⁻¹(F x₀)` consisting
of regular points of `F`, any family of positive periods `p : ι → ℝ` gives action–angle coordinates
`φ : M → T*(∀ i, AddCircle (p i))` on an open neighbourhood `U` of `L`. -/
theorem exists_actionAngle (hF : σ.IsIntegrableSystem F) (hσ : σ.IsSymplectic)
    {L : Set M} {x₀ : M}
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
        ∃ h : (ι → ℝ) → ι → ℝ,
          IsLocalDiffeomorphOn 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ h D ∧
          InjOn h D ∧
          ∀ x ∈ U, F x = h (fun i ↦ (φ x).2 (Pi.single i 1)) :=
  hσ.exists_actionAngle hF.contMDiff hF.poissonBracket_eq_zero hF.two_mul_card_eq_finrank
    hL hLc hreg p

end IsIntegrableSystem

end SmoothTwoForm

end TauCeti
