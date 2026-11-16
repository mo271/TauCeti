/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.RingTheory.Spectrum.Maximal.Topology
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.ReducedAlgebra
public import TauCeti.RingTheory.Affinoid.QuotientNorm
public import TauCeti.RingTheory.Affinoid.SupSeminorm
public import TauCeti.RingTheory.Huber.Uniform

import TauCeti.Analysis.Normed.Algebra.BanachFunctionAlgebra
import TauCeti.Analysis.Normed.Group.Quotient
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.AlgHom
import TauCeti.RingTheory.Affinoid.NoetherNormalization
import TauCeti.RingTheory.Affinoid.PowerBounded
import TauCeti.RingTheory.Affinoid.SpectralRadius
import TauCeti.RingTheory.Huber.ClosedSubmodule
import TauCeti.RingTheory.Huber.Normed
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.WeaklyStable

/-!
# Reduced affinoid algebras are Banach function algebras

Let `K` be a complete ultrametric nontrivially normed field and let `A` be a `K`-affinoid algebra.
When `A` is reduced, its supremum seminorm `supSeminorm K` is equivalent to every complete
ultrametric `K`-algebra norm on `A`: there exists `C > 0` such that

`supSeminorm K f ≤ ‖f‖ ≤ C * supSeminorm K f`

for every `f : A` ([bosch-guntzer-remmert], §6.2.4, Theorem 1). Consequently:

* `A` is uniform in Huber's sense (`TauCeti.Huber.IsUniform A`) if and only if `A` is reduced;
* every `K`-algebra homomorphism `φ : B →ₐ[K] A` from an arbitrary complete normed `K`-algebra `B`
  contracts `supSeminorm K`, and when `A` is reduced `φ` is automatically continuous;
* the wrapper `TauCeti.IsAffinoidAlgebra.SupNormed` endows any reduced affinoid algebra with its
  canonical complete supremum norm, continuously `K`-algebra isomorphic to any complete ultrametric
  `K`-algebra norm on `A`.

We also connect `supSeminorm K` to the generic spectral norm of [bosch-guntzer-remmert], §3.8.3,
Theorem 7 (`TauCeti.IsAffinoidAlgebra.supSeminorm_eq_spectralValue_minpoly_tensorProduct`). Concrete
sharpness examples (dual numbers, the closed annulus `K⟨X, Y⟩ ⧸ (X Y - c)`, and the maximum locus
on `K × K`) are proved in `TauCeti.RingTheory.Affinoid.Annulus`.

## Main definitions and results

* `TauCeti.IsAffinoidAlgebra.supSeminorm_eq_spectralValue_minpoly_tensorProduct`: for a finite
  torsion-free map `B → A` from a Noetherian complete ultrametric normed `K`-algebra with weakly
  stable fraction field `F` into a reduced affinoid `A`, `supSeminorm K a` equals
  `spectralValue (minpoly F (1 ⊗ₜ[B] a))`.
* `TauCeti.IsAffinoidAlgebra.exists_norm_le_mul_supSeminorm`: **Banach function algebra theorem for
  reduced affinoids** — `supSeminorm K f ≤ ‖f‖` and `‖f‖ ≤ C * supSeminorm K f`.
* `TauCeti.IsAffinoidAlgebra.isUniform` and `TauCeti.IsAffinoidAlgebra.isUniform_iff_isReduced`:
  a completely normed affinoid algebra is uniform if and only if it is reduced.
* `TauCeti.IsAffinoidAlgebra.supSeminorm_apply_le_norm` and
  `TauCeti.IsAffinoidAlgebra.continuous_algHom_of_isReduced`: contraction and automatic continuity
  from an arbitrary complete normed `K`-algebra into an affinoid algebra.
* `TauCeti.IsAffinoidAlgebra.SupNormed` and
  `TauCeti.IsAffinoidAlgebra.toSupNormedContinuousAlgEquiv`: the complete supremum-norm model of a
  reduced affinoid algebra and its continuous `K`-algebra equivalence with the original model.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §3.8.3, Theorem 7 and §§6.2.1–6.2.4.
-/

public section

open Filter Topology _root_.MvPowerSeries
open scoped TensorProduct

namespace TauCeti

namespace IsAffinoidAlgebra

section GenericSpectralNorm

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]
  [IsNoetherianRing B]
  (F : Type*) [NormedField F] [IsUltrametricDist F] [Algebra B F] [IsFractionRing B F]
  {A : Type*} [CommRing A] [Algebra K A] [IsReduced A]
  [Algebra B A] [IsScalarTower K B A] [Module.Finite B A] [Module.IsTorsionFree B A]

/-- If `A` is a reduced `K`-affinoid algebra that is finite and torsion-free over a Noetherian
complete ultrametric normed `K`-algebra `B` whose normed fraction field `F` is weakly stable, then
`supSeminorm K a` coincides with the generic spectral norm `spectralValue (minpoly F (1 ⊗ₜ[B] a))`
on the finite reduced `F`-algebra `F ⊗[B] A`. -/
theorem supSeminorm_eq_spectralValue_minpoly_tensorProduct (hA : IsAffinoidAlgebra K A)
    (hBF : ∀ b : B, ‖algebraMap B F b‖ = ‖b‖) (hF : IsWeaklyStable F) (a : A) :
    supSeminorm K a = spectralValue (minpoly F ((1 : F) ⊗ₜ[B] a)) := by
  let : NormedCommRing A := hA.residueNormedCommRing
  let : NormedAlgebra K A := hA.residueNormedAlgebra
  have : IsUltrametricDist A := hA.isUltrametricDist_residueNormedCommRing
  have : CompleteSpace A := hA.completeSpace_residueNormedCommRing
  have hBA : Continuous (algebraMap B A) :=
    hA.continuous_algHom ((Algebra.ofId B A).restrictScalars K)
  rw [hA.supSeminorm_eq_smoothingFun,
    smoothingFun_eq_spectralValue_minpoly_tensorProduct K F hBF hF hBA]

/-- When `B` in `supSeminorm_eq_spectralValue_minpoly_tensorProduct` is also integrally closed,
`supSeminorm K a` equals `spectralValue (minpoly B a)` directly over `B`. -/
theorem supSeminorm_eq_spectralValue_minpoly [IsIntegrallyClosed B] (hA : IsAffinoidAlgebra K A)
    (hBF : ∀ b : B, ‖algebraMap B F b‖ = ‖b‖) (hF : IsWeaklyStable F) (a : A) :
    supSeminorm K a = spectralValue (minpoly B a) := by
  let : NormedCommRing A := hA.residueNormedCommRing
  let : NormedAlgebra K A := hA.residueNormedAlgebra
  have : IsUltrametricDist A := hA.isUltrametricDist_residueNormedCommRing
  have : CompleteSpace A := hA.completeSpace_residueNormedCommRing
  have hBA : Continuous (algebraMap B A) :=
    hA.continuous_algHom ((Algebra.ofId B A).restrictScalars K)
  rw [hA.supSeminorm_eq_smoothingFun,
    smoothingFun_eq_spectralValue_minpoly_base K F hBF hF hBA]

end GenericSpectralNorm

section NormEquivalence

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

private theorem exists_norm_le_mul_supSeminorm_of_isDomain {A : Type*} [NormedCommRing A]
    [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A] [IsDomain A]
    (hA : IsAffinoidAlgebra K A) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : A, supSeminorm K f ≤ ‖f‖ ∧ ‖f‖ ≤ C * supSeminorm K f := by
  obtain ⟨n, g, hg_inj, hg_fin⟩ := hA.exists_finite_injective
  let B := IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)
  let F := MvPowerSeries.GaussFractionField (Fin n) K (fun _ ↦ 1)
  have : IsNoetherianRing B := (isAffinoidAlgebra_tate (K := K) (σ := Fin n)).isNoetherianRing
  let : Algebra B A := g.toRingHom.toAlgebra
  have : IsScalarTower K B A := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  have : Module.Finite B A := hg_fin
  have : Module.IsTorsionFree B A :=
    Module.IsTorsionFree.of_smul_eq_zero fun b a hba ↦ by
      rcases mul_eq_zero.mp (Algebra.smul_def b a ▸ hba) with hgb | ha
      · exact Or.inl (hg_inj (hgb.trans (map_zero g).symm))
      · exact Or.inr ha
  have hBF (b : B) : ‖algebraMap B F b‖ = ‖b‖ :=
    MvPowerSeries.norm_algebraMap_gaussFractionField (Fin n) K (fun _ ↦ 1) b
  have hF : IsWeaklyStable F := MvPowerSeries.isWeaklyStable_gaussFractionField (Fin n) K _
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_le_mul_smoothingFun K F hBF hF (hA.continuous_algHom g)
  refine ⟨C, hC, fun f ↦ ?_⟩
  simpa only [← hA.supSeminorm_eq_smoothingFun] using hbound f

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem continuousSMul_pi_quotient {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    {ι : Type*} [Finite ι] (I : ι → Ideal A) :
    ContinuousSMul A (∀ i : ι, A ⧸ I i) := by
  let : Fintype ι := Fintype.ofFinite ι
  let ΦL : A →L[K] ∀ i : ι, A ⧸ I i :=
    (AlgHom.pi fun i ↦ Ideal.Quotient.mkₐ K (I i)).toLinearMap.mkContinuous 1 fun a ↦ by
      rw [one_mul]
      exact (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr fun i ↦
        Submodule.Quotient.norm_mk_le (I i) a
  refine ⟨?_⟩
  have hsmul : (fun p : A × (∀ i : ι, A ⧸ I i) ↦ p.1 • p.2) = fun p ↦ ΦL p.1 * p.2 := by
    ext p i
    exact Algebra.smul_def p.1 (p.2 i)
  rw [hsmul]
  exact (ΦL.continuous.comp continuous_fst).mul continuous_snd

/-- **Banach function algebra theorem for reduced affinoid algebras**
([bosch-guntzer-remmert], §6.2.4, Theorem 1). For every reduced `K`-affinoid algebra `A` and every
complete ultrametric `K`-algebra norm on `A`, there is a constant `C > 0` such that
`supSeminorm K f ≤ ‖f‖ ≤ C * supSeminorm K f` for all `f : A`. -/
theorem exists_norm_le_mul_supSeminorm {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    [IsUltrametricDist A] [CompleteSpace A] [IsReduced A] (hA : IsAffinoidAlgebra K A) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : A, supSeminorm K f ≤ ‖f‖ ∧ ‖f‖ ≤ C * supSeminorm K f := by
  have : IsNoetherianRing A := hA.isNoetherianRing
  let : Huber.IsTateRing A := Huber.IsTateRing.of_normedAlgebra K A
  have : Finite (minimalPrimes A) := minimalPrimes.finite_of_isNoetherianRing A
  let : Fintype (minimalPrimes A) := Fintype.ofFinite (minimalPrimes A)
  have (𝔭 : minimalPrimes A) : IsClosed (𝔭.1 : Set A) := Huber.isClosed_of_isNoetherian 𝔭.1
  have hDom (𝔭 : minimalPrimes A) :
      ∃ C : ℝ, 0 < C ∧ ∀ x : A ⧸ 𝔭.1, supSeminorm K x ≤ ‖x‖ ∧ ‖x‖ ≤ C * supSeminorm K x := by
    have : 𝔭.1.IsPrime := 𝔭.2.1.1
    exact exists_norm_le_mul_supSeminorm_of_isDomain (hA.quotient 𝔭.1)
  choose C_dom hC_dom hD_bound using hDom
  let Φ : A →ₐ[K] ∀ 𝔭 : minimalPrimes A, A ⧸ 𝔭.1 :=
    AlgHom.pi fun 𝔭 ↦ Ideal.Quotient.mkₐ K 𝔭.1
  have hΦ_inj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h0 (𝔭 : minimalPrimes A) : Ideal.Quotient.mk 𝔭.1 a = 0 := congrFun ha 𝔭
    have hsup : supSeminorm K a = 0 := by
      simp [hA.supSeminorm_eq_iSup_minimalPrimes, h0, supSeminorm_zero]
    exact (hA.supSeminorm_eq_zero_iff.mp hsup).eq_zero
  have : ContinuousSMul A (∀ 𝔭 : minimalPrimes A, A ⧸ 𝔭.1) :=
    continuousSMul_pi_quotient (K := K) Subtype.val
  have (𝔭 : minimalPrimes A) : Module.Finite A (A ⧸ 𝔭.1) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A 𝔭.1).toLinearMap Ideal.Quotient.mk_surjective
  have : IsNoetherian A (∀ 𝔭 : minimalPrimes A, A ⧸ 𝔭.1) :=
    isNoetherian_of_isNoetherianRing_of_finite A _
  obtain ⟨C₀, hC₀, hC₀_bound⟩ :=
    (Algebra.linearMap A (∀ 𝔭 : minimalPrimes A, A ⧸ 𝔭.1)).exists_norm_le_mul_apply_of_injective
      (K := K) hΦ_inj
  let M : ℝ := 1 + ∑ 𝔭 : minimalPrimes A, C_dom 𝔭
  have hM : 0 < M := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun 𝔭 _ ↦ (hC_dom 𝔭).le)
  refine ⟨C₀ * M, mul_pos hC₀ hM, fun f ↦ ⟨hA.supSeminorm_le_norm f, ?_⟩⟩
  have hΦ_le : ‖Φ f‖ ≤ M * supSeminorm K f := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hM.le (supSeminorm_nonneg f))).mpr fun 𝔭 ↦ ?_
    have h𝔭_le : C_dom 𝔭 ≤ M := by
      have hsum : C_dom 𝔭 ≤ ∑ q : minimalPrimes A, C_dom q :=
        Finset.single_le_sum (fun q _ ↦ (hC_dom q).le) (Finset.mem_univ 𝔭)
      linarith
    calc
      ‖Φ f 𝔭‖ ≤ C_dom 𝔭 * supSeminorm K (Φ f 𝔭) := (hD_bound 𝔭 (Φ f 𝔭)).2
      _ ≤ C_dom 𝔭 * supSeminorm K f := mul_le_mul_of_nonneg_left
          (hA.supSeminorm_map_le (hA.quotient 𝔭.1) (Ideal.Quotient.mkₐ K 𝔭.1) f) (hC_dom 𝔭).le
      _ ≤ M * supSeminorm K f := mul_le_mul_of_nonneg_right h𝔭_le (supSeminorm_nonneg f)
  calc
    ‖f‖ ≤ C₀ * ‖Φ f‖ := hC₀_bound f
    _ ≤ C₀ * (M * supSeminorm K f) := mul_le_mul_of_nonneg_left hΦ_le hC₀.le
    _ = (C₀ * M) * supSeminorm K f := by ring

end NormEquivalence

section UniformityAndContinuity

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Every reduced completely normed `K`-affinoid algebra is uniform in Huber's sense: its
power-bounded elements form a bounded subset. -/
theorem isUniform {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A]
    [CompleteSpace A] [IsReduced A] (hA : IsAffinoidAlgebra K A) : Huber.IsUniform A := by
  obtain ⟨C, hC, hbound⟩ := hA.exists_norm_le_mul_supSeminorm
  refine Huber.isUniform_iff.mpr ((Huber.isBounded_closedBall_zero C).subset fun f hf ↦ ?_)
  rw [mem_closedBall_zero_iff]
  exact (hbound f).2.trans
    (mul_le_of_le_one_right hC.le (hA.isPowerBounded_iff_supSeminorm_le_one.mp hf))

/-- A completely normed `K`-affinoid algebra is uniform if and only if it is reduced. -/
theorem isUniform_iff_isReduced {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    [IsUltrametricDist A] [CompleteSpace A] (hA : IsAffinoidAlgebra K A) :
    Huber.IsUniform A ↔ IsReduced A := by
  let : Huber.IsTateRing A := Huber.IsTateRing.of_normedAlgebra K A
  exact ⟨fun _ ↦ Huber.IsUniform.isReduced, fun _ ↦ hA.isUniform⟩

/-- Any `K`-algebra homomorphism from a complete normed `K`-algebra `B` (not assumed commutative,
Noetherian, or ultrametric) into a `K`-affinoid algebra `A` satisfies `pointNorm K x (φ b) ≤ ‖b‖`
at every classical point `x`. -/
theorem pointNorm_apply_le_norm {B A : Type*} [NormedRing B] [NormedAlgebra K B]
    [CompleteSpace B] [CommRing A] [Algebra K A] (hA : IsAffinoidAlgebra K A)
    (φ : B →ₐ[K] A) (x : MaximalSpectrum A) (b : B) :
    pointNorm K x (φ b) ≤ ‖b‖ := by
  let : Field (A ⧸ x.asIdeal) := Ideal.Quotient.field x.asIdeal
  have : Module.Finite K (A ⧸ x.asIdeal) := hA.finite_quotient_of_isMaximal x.asIdeal
  rw [pointNorm_eq_spectralNorm (ψ := Ideal.Quotient.mkₐ K x.asIdeal)
    (Ideal.Quotient.mkₐ_ker K x.asIdeal).ge]
  exact ((Ideal.Quotient.mkₐ K x.asIdeal).comp φ).spectralNorm_apply_le_norm b

/-- Any `K`-algebra homomorphism from a complete normed commutative `K`-algebra `B` into a
`K`-affinoid algebra `A` satisfies `pointNorm K x (φ b) ≤ smoothingFun (normRingSeminorm B) b` at
every classical point `x`. -/
theorem pointNorm_apply_le_smoothingFun {B A : Type*} [NormedCommRing B] [NormedAlgebra K B]
    [CompleteSpace B] [CommRing A] [Algebra K A] (hA : IsAffinoidAlgebra K A)
    (φ : B →ₐ[K] A) (x : MaximalSpectrum A) (b : B) :
    pointNorm K x (φ b) ≤ smoothingFun (normRingSeminorm B) b := by
  let : Field (A ⧸ x.asIdeal) := Ideal.Quotient.field x.asIdeal
  have : Module.Finite K (A ⧸ x.asIdeal) := hA.finite_quotient_of_isMaximal x.asIdeal
  rw [pointNorm_eq_spectralNorm (ψ := Ideal.Quotient.mkₐ K x.asIdeal)
    (Ideal.Quotient.mkₐ_ker K x.asIdeal).ge]
  exact ((Ideal.Quotient.mkₐ K x.asIdeal).comp φ).spectralNorm_apply_le_smoothingFun b

/-- Any `K`-algebra homomorphism from a complete normed `K`-algebra `B` into a `K`-affinoid algebra
`A` satisfies `supSeminorm K (φ b) ≤ ‖b‖`. -/
theorem supSeminorm_apply_le_norm {B A : Type*} [NormedRing B] [NormedAlgebra K B]
    [CompleteSpace B] [CommRing A] [Algebra K A] (hA : IsAffinoidAlgebra K A)
    (φ : B →ₐ[K] A) (b : B) :
    supSeminorm K (φ b) ≤ ‖b‖ :=
  supSeminorm_le (norm_nonneg b) fun x ↦ hA.pointNorm_apply_le_norm φ x b

/-- Any `K`-algebra homomorphism from a complete normed commutative `K`-algebra `B` into a
`K`-affinoid algebra `A` satisfies `supSeminorm K (φ b) ≤ smoothingFun (normRingSeminorm B) b`. -/
theorem supSeminorm_apply_le_smoothingFun {B A : Type*} [NormedCommRing B] [NormedAlgebra K B]
    [CompleteSpace B] [CommRing A] [Algebra K A] (hA : IsAffinoidAlgebra K A)
    (φ : B →ₐ[K] A) (b : B) :
    supSeminorm K (φ b) ≤ smoothingFun (normRingSeminorm B) b := by
  have hnn : 0 ≤ smoothingFun (normRingSeminorm B) b :=
    le_ciInf fun n ↦ Real.rpow_nonneg (apply_nonneg (normRingSeminorm B) _) _
  exact supSeminorm_le hnn fun x ↦ hA.pointNorm_apply_le_smoothingFun φ x b

/-- **Automatic continuity into a reduced affinoid algebra**
([bosch-guntzer-remmert], §6.2.4, Corollary 2). Every `K`-algebra homomorphism `φ : B →ₐ[K] A` from
an arbitrary complete normed `K`-algebra `B` (not assumed commutative, Noetherian, or ultrametric)
into a reduced completely normed `K`-affinoid algebra `A` is continuous. -/
theorem continuous_algHom_of_isReduced {B A : Type*} [NormedRing B] [NormedAlgebra K B]
    [CompleteSpace B] [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A]
    [CompleteSpace A] [IsReduced A] (hA : IsAffinoidAlgebra K A) (φ : B →ₐ[K] A) :
    Continuous φ := by
  obtain ⟨C, hC, hbound⟩ := hA.exists_norm_le_mul_supSeminorm
  exact (φ.toLinearMap.mkContinuous C fun b ↦ (hbound (φ b)).2.trans
    (mul_le_mul_of_nonneg_left (hA.supSeminorm_apply_le_norm φ b) hC.le)).continuous

end UniformityAndContinuity

section SupNormedModel

/-- **The supremum-normed model of an affinoid algebra.** A one-field wrapper around an affinoid
`K`-algebra `A` carrying `supSeminorm K` as its canonical ultrametric `K`-algebra seminorm. When
`A` is reduced, `hA.SupNormed` is a complete ultrametric normed `K`-algebra (`NormedCommRing`,
`CompleteSpace`). -/
@[ext]
structure SupNormed {K A : Type*} [NormedField K] [IsUltrametricDist K]
    [CommRing A] [Algebra K A] (hA : IsAffinoidAlgebra K A) where
  /-- Wrap an element of `A` in `hA.SupNormed`. -/
  of ::
  /-- The underlying element of `A`. -/
  val : A

/-- The projection `SupNormed.val` to the underlying ring is injective. -/
theorem SupNormed.val_injective {K A : Type*} [NormedField K] [IsUltrametricDist K]
    [CommRing A] [Algebra K A] (hA : IsAffinoidAlgebra K A) :
    Function.Injective (SupNormed.val (hA := hA)) :=
  fun _ _ ↦ SupNormed.ext

section AlgebraicInstances

variable {K A : Type*} [NormedField K] [IsUltrametricDist K]
  [CommRing A] [Algebra K A] {hA : IsAffinoidAlgebra K A}

instance instCommRingSupNormed : CommRing hA.SupNormed where
  zero := ⟨0⟩
  one := ⟨1⟩
  add x y := ⟨x.val + y.val⟩
  sub x y := ⟨x.val - y.val⟩
  neg x := ⟨-x.val⟩
  mul x y := ⟨x.val * y.val⟩
  npow n x := ⟨x.val ^ n⟩
  nsmul n x := ⟨n • x.val⟩
  zsmul n x := ⟨n • x.val⟩
  natCast n := ⟨n⟩
  intCast n := ⟨n⟩
  add_assoc x y z := SupNormed.ext (add_assoc x.val y.val z.val)
  zero_add x := SupNormed.ext (zero_add x.val)
  add_zero x := SupNormed.ext (add_zero x.val)
  nsmul_zero x := SupNormed.ext (zero_nsmul x.val)
  nsmul_succ n x := SupNormed.ext (succ_nsmul x.val n)
  sub_eq_add_neg x y := SupNormed.ext (sub_eq_add_neg x.val y.val)
  zsmul_zero' x := SupNormed.ext (zero_zsmul x.val)
  zsmul_succ' n x := SupNormed.ext (SubNegMonoid.zsmul_succ' n x.val)
  zsmul_neg' n x := SupNormed.ext (SubNegMonoid.zsmul_neg' n x.val)
  neg_add_cancel x := SupNormed.ext (neg_add_cancel x.val)
  add_comm x y := SupNormed.ext (add_comm x.val y.val)
  left_distrib x y z := SupNormed.ext (left_distrib x.val y.val z.val)
  right_distrib x y z := SupNormed.ext (right_distrib x.val y.val z.val)
  zero_mul x := SupNormed.ext (zero_mul x.val)
  mul_zero x := SupNormed.ext (mul_zero x.val)
  mul_assoc x y z := SupNormed.ext (mul_assoc x.val y.val z.val)
  one_mul x := SupNormed.ext (one_mul x.val)
  mul_one x := SupNormed.ext (mul_one x.val)
  natCast_zero := SupNormed.ext Nat.cast_zero
  natCast_succ n := SupNormed.ext (Nat.cast_succ n)
  intCast_ofNat n := SupNormed.ext (Int.cast_natCast n)
  intCast_negSucc n := SupNormed.ext (Int.cast_negSucc n)
  npow_zero x := SupNormed.ext (pow_zero x.val)
  npow_succ n x := SupNormed.ext (pow_succ x.val n)
  mul_comm x y := SupNormed.ext (mul_comm x.val y.val)

@[simp] theorem SupNormed.val_zero : (0 : hA.SupNormed).val = 0 := (rfl)
@[simp] theorem SupNormed.val_one : (1 : hA.SupNormed).val = 1 := (rfl)
@[simp] theorem SupNormed.val_add (x y : hA.SupNormed) : (x + y).val = x.val + y.val := (rfl)
@[simp] theorem SupNormed.val_sub (x y : hA.SupNormed) : (x - y).val = x.val - y.val := (rfl)
@[simp] theorem SupNormed.val_neg (x : hA.SupNormed) : (-x).val = -x.val := (rfl)
@[simp] theorem SupNormed.val_mul (x y : hA.SupNormed) : (x * y).val = x.val * y.val := (rfl)
@[simp] theorem SupNormed.val_pow (x : hA.SupNormed) (n : ℕ) : (x ^ n).val = x.val ^ n := (rfl)

instance instAlgebraSupNormed : Algebra K hA.SupNormed where
  smul c x := ⟨c • x.val⟩
  algebraMap :=
    { toFun c := ⟨algebraMap K A c⟩
      map_one' := SupNormed.ext (map_one (algebraMap K A))
      map_mul' c d := SupNormed.ext (map_mul (algebraMap K A) c d)
      map_zero' := SupNormed.ext (map_zero (algebraMap K A))
      map_add' c d := SupNormed.ext (map_add (algebraMap K A) c d) }
  commutes' c x := SupNormed.ext (Algebra.commutes c x.val)
  smul_def' c x := SupNormed.ext (Algebra.smul_def c x.val)

@[simp]
theorem SupNormed.val_smul (c : K) (x : hA.SupNormed) : (c • x).val = c • x.val := (rfl)

/-- The canonical `K`-algebra isomorphism from `A` to `hA.SupNormed`. -/
def toSupNormed (hA : IsAffinoidAlgebra K A) : A ≃ₐ[K] hA.SupNormed where
  toFun a := ⟨a⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem val_toSupNormed (a : A) : (hA.toSupNormed a).val = a := (rfl)

@[simp]
theorem toSupNormed_symm_apply (x : hA.SupNormed) : hA.toSupNormed.symm x = x.val := (rfl)

instance [Subsingleton A] : Subsingleton hA.SupNormed :=
  (SupNormed.val_injective hA).subsingleton

instance [Nontrivial A] : Nontrivial hA.SupNormed :=
  hA.toSupNormed.symm.toEquiv.nontrivial

instance [IsReduced A] : IsReduced hA.SupNormed :=
  isReduced_of_injective hA.toSupNormed.symm.toRingHom hA.toSupNormed.symm.injective

instance [IsDomain A] : IsDomain hA.SupNormed :=
  hA.toSupNormed.toMulEquiv.isDomain_iff.mp ‹_›

/-- The supremum-seminormed wrapper `hA.SupNormed` of an affinoid algebra is itself affinoid. -/
theorem isAffinoidAlgebra_supNormed (hA : IsAffinoidAlgebra K A) :
    IsAffinoidAlgebra K hA.SupNormed :=
  hA.of_surjective hA.toSupNormed.toAlgHom hA.toSupNormed.surjective

end AlgebraicInstances

section Seminormed

variable {K A : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CommRing A] [Algebra K A] {hA : IsAffinoidAlgebra K A}

noncomputable instance instSeminormedCommRingSupNormed : SeminormedCommRing hA.SupNormed :=
  { instCommRingSupNormed,
    (hA.supRingSeminorm.toAddGroupSeminorm.comp
      { toFun := SupNormed.val, map_zero' := rfl, map_add' _ _ := rfl }).toSeminormedAddCommGroup
    with
    norm_mul_le x y := map_mul_le_mul hA.supRingSeminorm x.val y.val }

/-- The norm on `hA.SupNormed` is `supSeminorm K` of the underlying element. -/
@[simp]
theorem norm_supNormed (x : hA.SupNormed) : ‖x‖ = supSeminorm K x.val :=
  congrFun hA.coe_supRingSeminorm x.val

/-- The distance on `hA.SupNormed` is `supSeminorm K` of the difference. -/
theorem dist_supNormed (x y : hA.SupNormed) : dist x y = supSeminorm K (x.val - y.val) :=
  dist_eq_norm x y ▸ norm_supNormed (x - y)

theorem norm_toSupNormed (a : A) : ‖hA.toSupNormed a‖ = supSeminorm K a :=
  norm_supNormed (hA.toSupNormed a)

noncomputable instance instNormedAlgebraSupNormed : NormedAlgebra K hA.SupNormed :=
  { instAlgebraSupNormed with
    norm_smul_le c x := by
      rw [norm_supNormed, norm_supNormed, SupNormed.val_smul, supSeminorm_smul] }

instance : IsUltrametricDist hA.SupNormed :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ by
    simpa only [norm_supNormed, SupNormed.val_add] using hA.supSeminorm_add_le x.val y.val

instance [Nontrivial A] : NormOneClass hA.SupNormed where
  norm_one := by rw [norm_supNormed, SupNormed.val_one, supSeminorm_one]

/-- When `A` is reduced, `supSeminorm K` is separated, making `hA.SupNormed` a `NormedCommRing`. -/
noncomputable instance instNormedCommRingSupNormed [IsReduced A] : NormedCommRing hA.SupNormed :=
  { instCommRingSupNormed, instSeminormedCommRingSupNormed with
    eq_of_dist_eq_zero {x y} h := by
      rw [dist_supNormed] at h
      exact SupNormed.ext <| sub_eq_zero.mp ((hA.supSeminorm_eq_zero_iff.mp h).eq_zero) }

/-- When `A` is a reduced `K`-affinoid algebra, `hA.SupNormed` is complete for the supremum norm. -/
instance instCompleteSpaceSupNormed [IsReduced A] : CompleteSpace hA.SupNormed := by
  let : NormedCommRing A := hA.residueNormedCommRing
  let : NormedAlgebra K A := hA.residueNormedAlgebra
  have : IsUltrametricDist A := hA.isUltrametricDist_residueNormedCommRing
  have : CompleteSpace A := hA.completeSpace_residueNormedCommRing
  obtain ⟨C, -, hbound⟩ := hA.exists_norm_le_mul_supSeminorm
  let f : A →L[K] hA.SupNormed :=
    hA.toSupNormed.toLinearMap.mkContinuous 1 fun a ↦ by simpa using (hbound a).1
  let g : hA.SupNormed →L[K] A :=
    hA.toSupNormed.symm.toLinearMap.mkContinuous C fun x ↦ by
      simpa only [AlgEquiv.toLinearMap_apply, toSupNormed_symm_apply, norm_supNormed] using
        (hbound x.val).2
  let e : A ≃ᵤ hA.SupNormed :=
    { toEquiv := hA.toSupNormed.toEquiv
      uniformContinuous_toFun := f.uniformContinuous
      uniformContinuous_invFun := g.uniformContinuous }
  exact e.completeSpace_iff.mp inferInstance

end Seminormed

section ContinuousAlgEquiv

variable {K A : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A] [IsReduced A]

/-- **Continuous algebra equivalence with the supremum-normed model**
([bosch-guntzer-remmert], §6.2.4, Theorem 1). Any reduced completely normed `K`-affinoid algebra `A`
is continuously `K`-algebra isomorphic to its complete supremum-normed model `hA.SupNormed`. -/
noncomputable def toSupNormedContinuousAlgEquiv (hA : IsAffinoidAlgebra K A) :
    A ≃A[K] hA.SupNormed :=
  hA.isAffinoidAlgebra_supNormed.toContinuousAlgEquiv hA.toSupNormed

@[simp]
theorem coe_toSupNormedContinuousAlgEquiv (hA : IsAffinoidAlgebra K A) :
    ⇑hA.toSupNormedContinuousAlgEquiv = hA.toSupNormed :=
  coe_toContinuousAlgEquiv hA.isAffinoidAlgebra_supNormed hA.toSupNormed

@[simp]
theorem toAlgEquiv_toSupNormedContinuousAlgEquiv (hA : IsAffinoidAlgebra K A) :
    hA.toSupNormedContinuousAlgEquiv.toAlgEquiv = hA.toSupNormed :=
  toAlgEquiv_toContinuousAlgEquiv hA.isAffinoidAlgebra_supNormed hA.toSupNormed

theorem norm_toSupNormedContinuousAlgEquiv (hA : IsAffinoidAlgebra K A) (a : A) :
    ‖hA.toSupNormedContinuousAlgEquiv a‖ = supSeminorm K a := by
  simp

end ContinuousAlgEquiv

end SupNormedModel

end IsAffinoidAlgebra

end TauCeti
