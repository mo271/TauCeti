/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.MeasureTheory.Group.Circle
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import TauCeti.MeasureTheory.Integral.ContinuousMap
public import TauCeti.Probability.FreeProbability.HaarUnitary.Basic
public import TauCeti.RepresentationTheory.Compact.Haar
import TauCeti.Analysis.Bochner.Herglotz
import TauCeti.Analysis.Fourier.Pontryagin.Uniqueness

/-!
# The circle law of a unitary element and Haar unitaries

Let `A` be a unital C⋆-algebra, `φ : A →ₚ[ℂ] ℂ` a positive linear functional and `u ∈ unitary A`.
Because `u` is normal and its complex spectrum lies in the unit circle `Circle`, restricting a
continuous function `f` on `Circle` to `spectrum ℂ u` and applying the continuous functional
calculus gives a positive functional `f ↦ φ (f(u))` on `C(Circle, ℂ)`. By the
Riesz–Markov–Kakutani theorem it is integration against a unique finite Borel measure
`PositiveLinearMap.circleLaw φ u` on `Circle`, paralleling `PositiveLinearMap.law φ a` on `ℝ` for
selfadjoint elements. For `u ∉ unitary A` the circle law is defined to be `0`.

Since evaluation characters separate points of the Pontryagin dual of `ℤ` — identified with
`Circle` by `TauCeti.circleEquivPontryaginDualInt` — a finite Borel measure on `Circle` is
determined by its integer-power moments `∫ z ^ k dμ`. In particular, `φ.circleLaw u` equals the
normalized Haar measure `haarProb Circle` if and only if `u` is a Haar unitary for `φ` (without
needing a separate `u ∈ unitary A` hypothesis, as `haarProb Circle ≠ 0`). In the commutative
C⋆-algebra `C(Circle, ℂ)` with integration against `haarProb Circle`, the inclusion coordinate
`z ↦ z` is therefore a canonical realization of a Haar unitary.

## Main definitions

* `PositiveLinearMap.circleLaw φ u`: the law of a unitary `u` on `Circle` (`0` if `u ∉ unitary A`).

## Main results

* `PositiveLinearMap.integral_circleLaw_cfc`: `∫ f(z) d(φ.circleLaw u) = φ (cfc f u)` for `u`
  unitary and `f` continuous on the unit sphere.
* `PositiveLinearMap.eq_circleLaw_iff`, `PositiveLinearMap.eq_circleLaw_iff_forall_integral_zpow`:
  characterization of `φ.circleLaw u` by continuous test functions and by integer-power moments.
* `PositiveLinearMap.circleLaw_eq_haarProb_iff`: `φ.circleLaw u = haarProb Circle` iff
  `IsHaarUnitary φ.toLinearMap u`.
* `TauCeti.integral_zpow_haarProb_circle`: `∫ z ^ k d(haarProb Circle) = δ_{k, 0}`.
* `TauCeti.isHaarUnitary_integralPositiveLinearMap_haarProb_circle`: the coordinate function in
  `C(Circle, ℂ)` is Haar unitary for integration against `haarProb Circle`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Examples 1.14 and
  11.24.
-/

public section

noncomputable section

open MeasureTheory TauCeti
open scoped ComplexOrder CompactlySupported

namespace TauCeti

/-- Two finite Borel measures on `Circle` with the same integer-power moments are equal, via
injectivity of the Fourier–Stieltjes transform on `PontryaginDual (Multiplicative ℤ)`. -/
theorem ext_circle_of_forall_integral_zpow_eq {μ ν : Measure Circle} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h : ∀ k : ℤ, ∫ z : Circle, (z : ℂ) ^ k ∂μ = ∫ z : Circle, (z : ℂ) ^ k ∂ν) : μ = ν := by
  borelize (PontryaginDual (Multiplicative ℤ))
  have : PolishSpace (PontryaginDual (Multiplicative ℤ)) :=
    circleEquivPontryaginDualInt.symm.toHomeomorph.isClosedEmbedding.polishSpace
  let μf : FiniteMeasure Circle := ⟨μ, inferInstance⟩
  let νf : FiniteMeasure Circle := ⟨ν, inferInstance⟩
  have hmap : μf.map circleEquivPontryaginDualInt = νf.map circleEquivPontryaginDualInt :=
    FiniteMeasure.ext_of_forall_pontryaginMeasureTransform_eq fun k => by
      rw [FiniteMeasure.pontryaginMeasureTransform_map_circleEquivPontryaginDualInt,
        FiniteMeasure.pontryaginMeasureTransform_map_circleEquivPontryaginDualInt]
      exact h k
  have hmeas : μ.map circleEquivPontryaginDualInt = ν.map circleEquivPontryaginDualInt :=
    congrArg FiniteMeasure.toMeasure hmap
  simpa [Measure.map_map (map_continuous circleEquivPontryaginDualInt.symm).measurable
    (map_continuous circleEquivPontryaginDualInt).measurable, Function.comp_def] using
    congrArg (Measure.map circleEquivPontryaginDualInt.symm) hmeas

/-- The integer-power moments of normalized Haar measure on `Circle` are `1` at `0` and `0`
elsewhere, proved by left-translation invariance along `Circle.exp (π / k)`. -/
@[simp]
theorem integral_zpow_haarProb_circle (k : ℤ) :
    ∫ z : Circle, (z : ℂ) ^ k ∂haarProb Circle = if k = 0 then 1 else 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  rw [ite_eq_right hk]
  let w : Circle := Circle.exp (Real.pi / (k : ℝ))
  have hw : (w : ℂ) ^ k = -1 := by
    rw [Circle.coe_exp, ← Complex.exp_int_mul]
    have harg : (k : ℂ) * ((Real.pi / (k : ℝ) : ℝ) * Complex.I) = Real.pi * Complex.I := by
      push_cast
      rw [← mul_assoc, mul_div_cancel₀ _ (Int.cast_ne_zero.2 hk)]
    rw [harg, Complex.exp_pi_mul_I]
  have hinv := integral_mul_left_eq_self (μ := haarProb Circle)
    (fun z : Circle => (z : ℂ) ^ k) w
  simp only [Circle.coe_mul, mul_zpow, hw, neg_one_mul, integral_neg] at hinv
  linear_combination -hinv / 2

end TauCeti

namespace PositiveLinearMap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (φ : A →ₚ[ℂ] ℂ)
  {u : A}

private def restrictSpectrumCircle (hu : u ∈ unitary A) : C(spectrum ℂ u, Circle) :=
  ⟨fun x => ⟨x.1, spectrum.subset_circle_of_unitary hu x.2⟩, continuous_subtype_val.subtype_mk _⟩

private def circleCfcHom (hu : u ∈ unitary A) : C(Circle, ℂ) →⋆ₐ[ℂ] A :=
  (cfcHom (isStarNormal_of_mem_unitary hu)).comp
    (ContinuousMap.compStarAlgHom' ℂ ℂ (restrictSpectrumCircle hu))

private def circleLawFunctional (hu : u ∈ unitary A) : C_c(Circle, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun g := (φ (circleCfcHom hu (g.toContinuousMap.realToRCLike ℂ))).re
      map_add' g h := by
        rw [show (g + h).toContinuousMap = g.toContinuousMap + h.toContinuousMap from rfl,
          ← ContinuousMap.realToRCLikeStarAlgHom_apply, map_add, map_add, map_add, Complex.add_re]
        rfl
      map_smul' c g := by
        rw [show (c • g).toContinuousMap = c • g.toContinuousMap from rfl,
          ← ContinuousMap.realToRCLikeStarAlgHom_apply, map_smul, ← algebraMap_smul ℂ c,
          map_smul, map_smul]
        simp }
    fun g hg => by
      have : IsStarNormal u := isStarNormal_of_mem_unitary hu
      have hT : 0 ≤ circleCfcHom hu (g.toContinuousMap.realToRCLike ℂ) := by
        dsimp [circleCfcHom]
        rw [cfcHom_nonneg_iff]
        intro x
        simpa using hg (restrictSpectrumCircle hu x)
      exact (Complex.nonneg_iff.mp (φ.map_nonneg hT)).1

open scoped Classical in
/-- The **circle law** of an element `u` of a C⋆-algebra with respect to a positive linear
functional `φ`: for `u ∈ unitary A`, the unique finite Borel measure on `Circle` satisfying
`∫ f(z) dμ = φ (cfc f u)` for `f` continuous on the unit sphere (`integral_circleLaw_cfc`); for
`u ∉ unitary A`, the zero measure. -/
def circleLaw (φ : A →ₚ[ℂ] ℂ) (u : A) : Measure Circle :=
  if hu : u ∈ unitary A then RealRMK.rieszMeasure (circleLawFunctional φ hu) else 0

private lemma circleLaw_of_mem_unitary (hu : u ∈ unitary A) :
    φ.circleLaw u = RealRMK.rieszMeasure (circleLawFunctional φ hu) := by
  simp [circleLaw, hu]

/-- For `u ∉ unitary A`, the circle law is `0` by convention. -/
@[simp]
theorem circleLaw_of_not_mem_unitary (hu : u ∉ unitary A) : φ.circleLaw u = 0 := by
  simp [circleLaw, hu]

instance (u : A) : IsFiniteMeasure (φ.circleLaw u) := by
  by_cases hu : u ∈ unitary A
  · rw [circleLaw_of_mem_unitary φ hu]
    infer_instance
  · rw [circleLaw_of_not_mem_unitary φ hu]
    infer_instance

private lemma ofReal_integral_circleLaw_real (hu : u ∈ unitary A) (g : C(Circle, ℝ)) :
    ((∫ z, g z ∂(φ.circleLaw u) : ℝ) : ℂ) = φ (circleCfcHom hu (g.realToRCLike ℂ)) := by
  have h := RealRMK.integral_rieszMeasure (circleLawFunctional φ hu) ⟨g, .of_compactSpace _⟩
  rw [CompactlySupportedContinuousMap.coe_mk] at h
  rw [circleLaw_of_mem_unitary φ hu, h]
  have hsa : IsSelfAdjoint (φ (circleCfcHom hu (g.realToRCLike ℂ))) :=
    ((ContinuousMap.isSelfAdjoint_realToRCLike ℂ).map (circleCfcHom hu)).map' φ
  exact Complex.conj_eq_iff_re.mp hsa.star_eq

private lemma integral_circleLaw_continuousMap (hu : u ∈ unitary A) (f : C(Circle, ℂ)) :
    ∫ z, f z ∂(φ.circleLaw u) = φ (circleCfcHom hu f) := by
  let L : C(Circle, ℂ) →ₗ[ℂ] ℂ := φ.toLinearMap.comp (circleCfcHom hu).toAlgHom.toLinearMap
  exact (L.apply_eq_integral_of_forall_realToRCLike
    (fun g => (ofReal_integral_circleLaw_real φ hu g).symm) f).symm

/-- Integration against `φ.circleLaw u` for a unitary `u` computes `φ` on the continuous functional
calculus: `∫ f(z) d(φ.circleLaw u) = φ (cfc f u)` for `f` continuous on the unit sphere. -/
theorem integral_circleLaw_cfc (hu : u ∈ unitary A) (f : ℂ → ℂ)
    (hf : ContinuousOn f (Metric.sphere (0 : ℂ) 1) := by cfc_cont_tac) :
    ∫ z : Circle, f z ∂(φ.circleLaw u) = φ (cfc f u) := by
  have hnorm : IsStarNormal u := isStarNormal_of_mem_unitary hu
  let fC : C(Circle, ℂ) := ⟨fun z => f z, hf.comp_continuous continuous_subtype_val fun z => z.2⟩
  have hcfc : cfc f u = circleCfcHom hu fC := by
    rw [cfc_apply f u hnorm (hf.mono (spectrum.subset_circle_of_unitary hu))]
    rfl
  rw [hcfc, ← integral_circleLaw_continuousMap φ hu fC]
  rfl

/-- The total mass of `φ.circleLaw u` for `u ∈ unitary A` is `φ 1`. -/
theorem ofReal_circleLaw_real_univ (hu : u ∈ unitary A) :
    (((φ.circleLaw u).real Set.univ : ℝ) : ℂ) = φ 1 := by
  have : IsStarNormal u := isStarNormal_of_mem_unitary hu
  simpa [cfc_const_one ℂ u, Complex.real_smul] using
    integral_circleLaw_cfc φ hu (fun _ => (1 : ℂ))

/-- The circle law of a unitary element with respect to a state is a probability measure. -/
theorem isProbabilityMeasure_circleLaw (hφ : φ 1 = 1) (hu : u ∈ unitary A) :
    IsProbabilityMeasure (φ.circleLaw u) := by
  refine ⟨?_⟩
  have h := ofReal_circleLaw_real_univ φ hu
  rw [hφ, Complex.ofReal_eq_one] at h
  rw [← ofReal_measureReal, h, ENNReal.ofReal_one]

/-- The integer-power moments of `φ.circleLaw u` for `u ∈ unitary A` are `φ (u ^ k)`. -/
theorem integral_zpow_circleLaw (hu : u ∈ unitary A) (k : ℤ) :
    ∫ z : Circle, (z : ℂ) ^ k ∂(φ.circleLaw u) =
      φ (((⟨u, hu⟩ : unitary A) ^ k : unitary A) : A) := by
  have : IsStarNormal u := isStarNormal_of_mem_unitary hu
  cases k with
  | ofNat n =>
    simpa [SubmonoidClass.coe_pow, cfc_pow_id u n] using
      integral_circleLaw_cfc φ hu (fun w : ℂ => w ^ n)
  | negSucc n =>
    have hcongr : ∀ z : Circle, (z : ℂ) ^ Int.negSucc n = star (z : ℂ) ^ (n + 1) := fun z => by
      rw [zpow_negSucc, ← inv_pow, ← Circle.coe_inv, Circle.coe_inv_eq_conj, RCLike.star_def]
    have hcfc : cfc (fun w : ℂ => star w ^ (n + 1)) u = star u ^ (n + 1) := by
      have hfun : (fun w : ℂ => star w ^ (n + 1)) = fun w : ℂ => star (w ^ (n + 1)) :=
        funext fun w => (star_pow w (n + 1)).symm
      rw [hfun, cfc_star, cfc_pow_id u (n + 1), star_pow]
    have hpow : (((⟨u, hu⟩ : unitary A) ^ Int.negSucc n : unitary A) : A) = star u ^ (n + 1) := by
      rw [zpow_negSucc, ← inv_pow, SubmonoidClass.coe_pow, ← Unitary.star_eq_inv, Unitary.coe_star]
    simp_rw [hcongr]
    rw [integral_circleLaw_cfc φ hu (fun w : ℂ => star w ^ (n + 1)), hcfc, hpow]

variable {φ} in
/-- **Moment determinacy on the circle.** For `u ∈ unitary A`, a finite Borel measure on `Circle`
equals `φ.circleLaw u` if and only if its integer-power moments are `φ (u ^ k)`. -/
theorem eq_circleLaw_iff_forall_integral_zpow (hu : u ∈ unitary A) {μ : Measure Circle}
    [IsFiniteMeasure μ] :
    μ = φ.circleLaw u ↔
      ∀ k : ℤ, ∫ z : Circle, (z : ℂ) ^ k ∂μ = φ (((⟨u, hu⟩ : unitary A) ^ k : unitary A) : A) := by
  refine ⟨fun h k => h ▸ integral_zpow_circleLaw φ hu k, fun h => ?_⟩
  exact ext_circle_of_forall_integral_zpow_eq fun k =>
    (h k).trans (integral_zpow_circleLaw φ hu k).symm

variable {φ} in
/-- For `u ∈ unitary A`, `φ.circleLaw u` is the unique finite Borel measure on `Circle` representing
`f ↦ φ (cfc f u)` for all continuous functions `f : ℂ → ℂ`. -/
theorem eq_circleLaw_iff (hu : u ∈ unitary A) {μ : Measure Circle} [IsFiniteMeasure μ] :
    μ = φ.circleLaw u ↔ ∀ f : ℂ → ℂ, Continuous f → ∫ z : Circle, f z ∂μ = φ (cfc f u) := by
  refine ⟨fun h f hf => h ▸ integral_circleLaw_cfc φ hu f hf.continuousOn, fun h => ?_⟩
  refine ext_circle_of_forall_integral_zpow_eq fun k => ?_
  cases k with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact (h (· ^ n) (continuous_pow n)).trans
      (integral_circleLaw_cfc φ hu (· ^ n) (continuous_pow n).continuousOn).symm
  | negSucc n =>
    have hcongr : (fun z : Circle => (z : ℂ) ^ Int.negSucc n) =
        fun z : Circle => star (z : ℂ) ^ (n + 1) := funext fun z => by
      rw [zpow_negSucc, ← inv_pow, ← Circle.coe_inv, Circle.coe_inv_eq_conj, RCLike.star_def]
    have hcont : Continuous (fun w : ℂ => star w ^ (n + 1)) := continuous_star.pow (n + 1)
    simp_rw [hcongr]
    exact (h _ hcont).trans (integral_circleLaw_cfc φ hu _ hcont.continuousOn).symm

/-- Two unitary elements, possibly in different C⋆-algebras, have the same circle law iff their
integer powers have the same expectations. -/
theorem circleLaw_eq_circleLaw_iff_forall_apply_zpow {B : Type*} [CStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] (ψ : B →ₚ[ℂ] ℂ) {v : B}
    (hu : u ∈ unitary A) (hv : v ∈ unitary B) :
    φ.circleLaw u = ψ.circleLaw v ↔
      ∀ k : ℤ, φ (((⟨u, hu⟩ : unitary A) ^ k : unitary A) : A) =
        ψ (((⟨v, hv⟩ : unitary B) ^ k : unitary B) : B) := by
  rw [eq_circleLaw_iff_forall_integral_zpow hv]
  simp_rw [integral_zpow_circleLaw φ hu]

/-- **Analytic characterization of Haar unitaries.** The circle law `φ.circleLaw u` equals the
normalized Haar measure `haarProb Circle` if and only if `u` is a Haar unitary for `φ`. No
prior unitarity assumption on `u` is needed. -/
theorem circleLaw_eq_haarProb_iff :
    φ.circleLaw u = haarProb Circle ↔ IsHaarUnitary φ.toLinearMap u := by
  by_cases hu : u ∈ unitary A
  · rw [eq_comm, eq_circleLaw_iff_forall_integral_zpow hu,
      isHaarUnitary_iff_apply_zpow (u := ⟨u, hu⟩)]
    refine forall_congr' fun k => ?_
    rw [integral_zpow_haarProb_circle, eq_comm]
    rfl
  · refine iff_of_false (fun h => ?_) (fun h => hu h.mem_unitary)
    have huniv := congrArg (fun μ : Measure Circle => μ Set.univ) h
    simp [circleLaw_of_not_mem_unitary φ hu] at huniv

end PositiveLinearMap

namespace TauCeti

/-- The coordinate inclusion `z ↦ (z : ℂ)` in `C(Circle, ℂ)` is unitary. -/
theorem subtypeVal_mem_unitary_continuousMap_circle :
    (⟨Subtype.val, continuous_subtype_val⟩ : C(Circle, ℂ)) ∈ unitary C(Circle, ℂ) := by
  rw [Unitary.mem_iff]
  refine ⟨ContinuousMap.ext fun z => ?_, ContinuousMap.ext fun z => ?_⟩
  · change star (z : ℂ) * (z : ℂ) = 1
    rw [RCLike.star_def, ← Circle.coe_inv_eq_conj, Circle.coe_inv,
      inv_mul_cancel₀ (Circle.coe_ne_zero z)]
  · change (z : ℂ) * star (z : ℂ) = 1
    rw [RCLike.star_def, ← Circle.coe_inv_eq_conj, Circle.coe_inv,
      mul_inv_cancel₀ (Circle.coe_ne_zero z)]

/-- In `C(Circle, ℂ)`, the circle law of the coordinate `z ↦ z` with respect to integration
against a finite measure `ν` on `Circle` is `ν` itself. -/
@[simp]
theorem circleLaw_integralPositiveLinearMap_subtypeVal (ν : Measure Circle) [IsFiniteMeasure ν] :
    (ContinuousMap.integralPositiveLinearMap ν).circleLaw
      (⟨Subtype.val, continuous_subtype_val⟩ : C(Circle, ℂ)) = ν := by
  symm
  rw [PositiveLinearMap.eq_circleLaw_iff_forall_integral_zpow
    subtypeVal_mem_unitary_continuousMap_circle]
  intro k
  rw [ContinuousMap.integralPositiveLinearMap_apply]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  cases k with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, SubmonoidClass.coe_pow]
    rfl
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow, SubmonoidClass.coe_pow, ← Unitary.star_eq_inv, Unitary.coe_star]
    change ((z : ℂ) ^ (n + 1))⁻¹ = star (z : ℂ) ^ (n + 1)
    rw [← inv_pow, RCLike.star_def, ← Circle.coe_inv_eq_conj, Circle.coe_inv]

/-- **Canonical realization of a Haar unitary.** In the commutative C⋆-algebra `C(Circle, ℂ)` with
the state given by integration against normalized Haar measure `haarProb Circle`, the coordinate
function `z ↦ z` is a Haar unitary. -/
theorem isHaarUnitary_integralPositiveLinearMap_haarProb_circle :
    IsHaarUnitary (ContinuousMap.integralPositiveLinearMap (haarProb Circle)).toLinearMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C(Circle, ℂ)) :=
  (PositiveLinearMap.circleLaw_eq_haarProb_iff _).1
    (circleLaw_integralPositiveLinearMap_subtypeVal (haarProb Circle))

end TauCeti
