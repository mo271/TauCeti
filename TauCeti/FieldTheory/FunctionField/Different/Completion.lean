/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Complementary
public import TauCeti.FieldTheory.FunctionField.Different.Localization
public import TauCeti.FieldTheory.FunctionField.Place.Completion.ResidueExtension
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Semilocal
public import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.Basic
public import TauCeti.RingTheory.DedekindDomain.Different.Discriminant

import TauCeti.RingTheory.DedekindDomain.Different.DualFamily

/-!
# Invariance of the trace-dual different under completion

Let `F' / F` be a finite separable extension of fields, let `P` be a place of `F / k`, and let
`P'` be a place of `F' / k'` lying over `P`. Writing `𝒪_P` for the valuation ring of `P`, `𝒪'_P`
for its integral closure in `F'`, and `𝒪̂_P ⊆ 𝒪̂_{P'}` for the completed valuation rings inside
`F̂_P ⊆ F̂'_{P'}`, this file proves that **the trace-dual complementary module and the different
ideal commute with completion**:

* `Submodule.span 𝒪̂_{P'} (P'.completionEmbedding '' C_P) = Ĉ_{P'}`, where
  `C_P = Submodule.traceDual 𝒪_P F 1` and `Ĉ_{P'} = Submodule.traceDual 𝒪̂_P F̂_P 1`;
* `(differentIdeal 𝒪_P 𝒪'_P).map (integralClosureToCompletionIntegers P P' hP) =
    differentIdeal 𝒪̂_P 𝒪̂_{P'}`;
* `differentIdeal 𝒪̂_P 𝒪̂_{P'} = maximalIdeal 𝒪̂_{P'} ^ d(P' ∣ P)`, so the multiplicity of
  `maximalIdeal 𝒪̂_{P'}` in `differentIdeal 𝒪̂_P 𝒪̂_{P'}` is `d(P' ∣ P)`, and when `k' = k` the
  completed place `P'.completionPlace` has the same different exponent over `P.Completion` as `P'`
  has over `F`.

The same comparison holds when reading the global complementary module and different ideal on any
affine Dedekind model `B ⊆ C` on which `P'` is finite, via localization to the local model
`𝒪_P ⊆ 𝒪'_P` (`TauCeti/FieldTheory/FunctionField/Different/Localization.lean`).

No hypothesis on the residue-field extension, on `IsFunctionField`, or on integrality of `k' / k`
is needed for the single-place completion invariance. In particular, at a **fierce** place — one
whose residue extension `F'_{P'} / F_P` is inseparable — completion preserves the full residue
degree and its inseparability (`TauCeti.Place.finrank_residueField_completion`,
`TauCeti.Place.isSeparable_residueField_completion_iff`), and the trace-dual different is still
computed faithfully on the completed extension `𝒪̂_P ⊆ 𝒪̂_{P'}`. Internally, restricting the
constant field of `P'` from `k'` to `k` without changing its valuation puts the place into the
equal-constants setting, where `Algebra.IsIntegral k k` holds automatically and the semilocal
spanning and trace theorems of `TauCeti/FieldTheory/FunctionField/Place/Completion/Semilocal.lean`
apply directly on `∏_{Q' ∣ P} F̂'_{Q'}` without forming a tensor product over `F`.

Combining completion invariance with the discrete-valuation-ring length and discriminant formulas
`TauCeti.length_traceDual_quotient_eq_multiplicity_mul_finrank` and
`TauCeti.ord_discr_eq_multiplicity_mul_finrank` yields:

* `length_{𝒪̂_P}(Ĉ_{P'} ⧸ 𝒪̂_{P'}) = d(P' ∣ P) · f(P' ∣ P)` and
  `ord_{P̂}(discr_{𝒪̂_P} b̂) = d(P' ∣ P) · f(P' ∣ P)` for every `𝒪̂_P`-basis `b̂`
  of `𝒪̂_{P'}`, where `f(P' ∣ P)` is the full relative residue degree, including its inseparable
  factor;
* when `k' / k` is integral, the diagonal image of an `𝒪_P`-basis of `𝒪'_P` is an `𝒪̂_P`-basis of
  `∏_{P' ∣ P} 𝒪̂_{P'}`, giving the local-to-global discriminant and complementary-module length
  formulas at `P`:
  `ord_P(discr_F b) = ∑_{P' ∣ P} d(P' ∣ P) · f(P' ∣ P)` for any integral basis `b` at `P`, and
  `length_{𝒪_P}(C_P ⧸ 𝒪'_P) = ∑_{P' ∣ P} length_{𝒪̂_P}(Ĉ_{P'} ⧸ 𝒪̂_{P'})`.

The trace-dual comparison parallels the number-field completion theorem in
`TauCeti/NumberTheory/NumberField/LocalGlobal/Different/Basic.lean`, replacing the tensor-product
semilocal algebra `K_v ⊗_K L` and finite residue fields with the coordinatewise weak-approximation
and Nakayama spanning of `TauCeti/FieldTheory/FunctionField/Place/Completion/Semilocal.lean`.

## Main definitions

* `TauCeti.Place.modelToCompletionIntegers`: the canonical ring homomorphism `C →+* 𝒪̂_{P'}` from a
  model `C` of `F'` on which `P'` is finite into the completed valuation ring.
* `TauCeti.Place.integralClosureToCompletionIntegers`: the specialization `𝒪'_P →+* 𝒪̂_{P'}` on the
  local integral closure above `P`.

## Main results

* `TauCeti.Place.isIntegral_iff_forall_restrict_eq_mem_integers_of_isSeparable` and
  `TauCeti.Place.mem_traceDual_iff_forall_valuation_le_of_isSeparable`: the Dedekind valuation
  criteria for `𝒪'_P` and `C_P` without assuming `IsFunctionField`.
* `TauCeti.Place.sum_trace_mul_smul_completionEmbedding_eq`: trace-dual expansions pass from
  `F' / F` to `F̂'_{P'} / F̂_P`.
* `TauCeti.Place.completionEmbedding_mem_traceDual` and
  `TauCeti.Place.span_completionEmbedding_traceDual_eq_traceDual`: `Ĉ_{P'}` is the `𝒪̂_{P'}`-span
  of the image of `C_P` (and `span_completionEmbedding_traceDual_model_eq_traceDual` for an affine
  model `B ⊆ C`).
* `TauCeti.Place.extended_dual_one_eq_dual_one_completionIntegers` and
  `TauCeti.Place.map_differentIdeal_eq_differentIdeal_completionIntegers`: the fractional-ideal
  dual and the different ideal commute with completion (plus affine-model forms).
* `TauCeti.Place.differentIdeal_completionIntegers`,
  `TauCeti.Place.multiplicity_differentIdeal_completionIntegers`,
  `TauCeti.Place.mem_traceDual_completion_iff_valuation_le`, and
  `TauCeti.Place.differentExponent_completionPlace`: explicit description of the completed
  different ideal, its valuation criterion, and invariance of `differentExponent`.
* `TauCeti.Place.length_traceDual_quotient_completionIntegers`,
  `TauCeti.Place.ord_discr_completionIntegers`, and
  `TauCeti.Place.ord_completionPlace_discr_completionIntegers`: completed complementary-module
  length and discriminant valuation `d(P' ∣ P) · f(P' ∣ P)` with full residue degree.
* `TauCeti.Place.ord_discr_of_isIntegralBasis`,
  `TauCeti.Place.length_traceDual_quotient_integralClosure`, and
  `TauCeti.Place.length_traceDual_quotient_eq_finsum_completion`: pre-completion discriminant order
  and complementary-module quotient length at `P` as the sum over `P' ∣ P` of
  `d(P' ∣ P) · f(P' ∣ P)`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections III.4–III.5 and IV.2.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §3 and Chapter III, §§3–4,
  Proposition 10.
* J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter III,
  Proposition (2.2).
-/

public section

open IsDedekindDomain IsLocalRing Module
open scoped WithZero nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti.Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-! ### Valuation criteria on the local model without function-field hypotheses -/

section ValuationCriterion

variable (k') [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [Algebra.IsIntegral k k']

/-- **The integral closure of `𝒪_P` is the intersection of the valuation rings above `P`**, for any
finite separable extension `F' / F` with `k' / k` integral. Unlike
`TauCeti.Place.isIntegral_iff_forall_restrict_eq_mem_integers`, this needs no `IsFunctionField`
hypothesis: `𝒪'_P` is a Dedekind domain finite over the discrete valuation ring `𝒪_P`, so every
height one prime of `𝒪'_P` lies over the maximal ideal of `𝒪_P` and defines a place above `P`. -/
theorem isIntegral_iff_forall_restrict_eq_mem_integers_of_isSeparable (P : Place k F) {x : F'} :
    IsIntegral P.integers x ↔ ∀ P' : Place k' F', P'.restrict k F = P → x ∈ P'.integers := by
  refine ⟨fun hx P' hP' ↦ P'.mem_integers_of_isIntegral (fun a ↦ ?_) hx, fun h ↦ ?_⟩
  · subst hP'
    exact (mem_integers_restrict_iff k F P' (a : F)).mp a.2
  have hR : ∀ r : P.integers, algebraMap P.integers F r ∈ P.integers := fun r ↦ r.2
  have hk' : ∀ c : k', algebraMap k' F' c ∈ integralClosure P.integers F' :=
    fun c ↦ isIntegral_integers_algebraMap P c
  let _ : Algebra k' (integralClosure P.integers F') :=
    ((algebraMap k' F').codRestrict (integralClosure P.integers F') hk').toAlgebra
  have : IsScalarTower k' (integralClosure P.integers F') F' := .of_algebraMap_eq fun _ ↦ rfl
  have hcenter : (P.center hR).asIdeal = maximalIdeal P.integers := by
    ext r
    rw [mem_center_asIdeal, mem_maximalIdeal_iff_valuation_lt_one]
    exact Iff.rfl
  have hval : ∀ 𝔓 : HeightOneSpectrum (integralClosure P.integers F'), 𝔓.valuation F' x ≤ 1 := by
    intro 𝔓
    have : Algebra.IsIntegral P.integers (integralClosure P.integers F') :=
      Algebra.IsIntegral.of_finite _ _
    have hmax : (𝔓.asIdeal.under P.integers).IsMaximal :=
      (𝔓.isPrime.under P.integers).isMaximal (𝔓.asIdeal.under_ne_bot P.integers 𝔓.ne_bot)
    have hlies : 𝔓.asIdeal.LiesOver (P.center hR).asIdeal :=
      ⟨by rw [Ideal.under_def, ← Ideal.under_def, IsLocalRing.eq_maximalIdeal hmax, hcenter]⟩
    have hres : (ofPrime k' F' 𝔓).restrict k F = P :=
      (restrict_ofPrime k F (P.center hR) 𝔓).trans (ofPrime_center k F P hR)
    simpa only [valuation_ofPrime, mem_integers_iff] using h (ofPrime k' F' 𝔓) hres
  obtain ⟨y, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F' x hval
  exact y.2

/-- **The valuation criterion for the complementary module**, without `IsFunctionField`: for
`F' / F` finite separable and `k' / k` integral, `z ∈ C_P` if and only if
`v_{P'}(z) ≤ exp d(P' ∣ P)` at every place `P'` above `P`. -/
theorem mem_traceDual_iff_forall_valuation_le_of_isSeparable (P : Place k F) {z : F'} :
    z ∈ Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F') ↔
      ∀ P' : Place k' F', P'.restrict k F = P →
        P'.valuation z ≤ WithZero.exp (differentExponent k F P' : ℤ) := by
  refine ⟨fun hz P' hP' ↦ ?_, fun h ↦ ?_⟩
  · subst hP'
    exact valuation_le_exp_differentExponent_of_mem_traceDual k F P' hz
  refine mem_traceDual_one_iff_forall_mem_differentIdeal.mpr fun y hy ↦
    Submodule.mem_one.mpr ⟨⟨z * algebraMap (integralClosure P.integers F') F' y, ?_⟩, rfl⟩
  refine (isIntegral_iff_forall_restrict_eq_mem_integers_of_isSeparable k' P).mpr fun P' hP' ↦ ?_
  subst hP'
  rw [mem_integers_iff, map_mul]
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  have hy0' : algebraMap (integralClosure (P'.restrict k F).integers F') F' y ≠ 0 := by
    simpa using hy0
  have hord := differentExponent_le_ord_of_mem_differentIdeal k F P' hy hy0
  rw [P'.valuation_eq_exp_neg_ord hy0']
  calc P'.valuation z * WithZero.exp (-P'.ord (algebraMap _ F' y))
      ≤ WithZero.exp (differentExponent k F P' : ℤ) *
          WithZero.exp (-(differentExponent k F P' : ℤ)) := by
        gcongr
        · exact h P' rfl
        · exact WithZero.exp_le_exp.mpr (neg_le_neg hord)
    _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]

end ValuationCriterion

/-! ### Embeddings of affine and local models into the completed valuation ring -/

section Embeddings

/-- The canonical ring homomorphism from a model `C` of `F'` on which `P'` is finite into the
completed valuation ring `𝒪̂_{P'}`. -/
noncomputable def modelToCompletionIntegers {C : Type*} [CommRing C] [Algebra C F']
    (P' : Place k' F') (hC : ∀ c : C, algebraMap C F' c ∈ P'.integers) :
    C →+* P'.completionPlace.integers :=
  P'.completionIntegersEmbedding.toRingHom.comp ((algebraMap C F').codRestrict P'.integers hC)

@[simp]
theorem coe_modelToCompletionIntegers {C : Type*} [CommRing C] [Algebra C F']
    (P' : Place k' F') (hC : ∀ c : C, algebraMap C F' c ∈ P'.integers) (c : C) :
    (P'.modelToCompletionIntegers hC c : P'.Completion) =
      P'.completionEmbedding (algebraMap C F' c) := by
  simp [modelToCompletionIntegers]

theorem modelToCompletionIntegers_injective {C : Type*} [CommRing C] [Algebra C F']
    [FaithfulSMul C F'] (P' : Place k' F') (hC : ∀ c : C, algebraMap C F' c ∈ P'.integers) :
    Function.Injective (P'.modelToCompletionIntegers hC) := fun _ _ h ↦ by
  refine FaithfulSMul.algebraMap_injective C F'
    ((P'.completionEmbedding : F' →+* P'.Completion).injective ?_)
  rw [RingHom.coe_coe, ← coe_modelToCompletionIntegers P' hC,
    ← coe_modelToCompletionIntegers P' hC, h]

section LocalModel

variable [Algebra.IsIntegral F F'] (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)

/-- The canonical ring homomorphism `𝒪'_P →+* 𝒪̂_{P'}` from the local integral closure above `P`
into the completed valuation ring at `P'`. -/
noncomputable def integralClosureToCompletionIntegers :
    integralClosure P.integers F' →+* P'.completionPlace.integers :=
  P'.modelToCompletionIntegers fun b ↦ by
    subst hP
    exact algebraMap_mem_integers_of_mem_integralClosure k F P' b

@[simp]
theorem coe_integralClosureToCompletionIntegers (b : integralClosure P.integers F') :
    (P.integralClosureToCompletionIntegers P' hP b : P'.Completion) =
      P'.completionEmbedding (algebraMap (integralClosure P.integers F') F' b) :=
  P'.coe_modelToCompletionIntegers _ b

theorem integralClosureToCompletionIntegers_injective :
    Function.Injective (P.integralClosureToCompletionIntegers P' hP) :=
  modelToCompletionIntegers_injective P' _

/-- `integralClosureToCompletionIntegers` extends the completed valuation-ring map on `𝒪_P`. -/
theorem integralClosureToCompletionIntegers_algebraMap (r : P.integers) :
    P.integralClosureToCompletionIntegers P' hP
        (algebraMap P.integers (integralClosure P.integers F') r) =
      P.completionIntegersExtension P' hP (P.completionIntegersEmbedding r) := by
  apply Subtype.ext
  rw [coe_integralClosureToCompletionIntegers, coe_completionIntegersExtension,
    completionIntegersEmbedding_apply, P.completionExtension_completionEmbedding P' hP,
    ← IsScalarTower.algebraMap_apply P.integers (integralClosure P.integers F') F',
    IsScalarTower.algebraMap_apply P.integers F F', ValuationSubring.algebraMap_apply]

end LocalModel

end Embeddings

/-! ### Trace-dual expansions, trace duals, and different ideals under completion -/

section TraceDual

/-- Restrict the constant field of `P' : Place k' F'` to `k`, keeping the same valuation on `F'`.
No integrality assumption on `k' / k` is required. -/
private def restrictConstants (P' : Place k' F') : Place k F' where
  valuation := P'.valuation
  valuation_surjective := P'.valuation_surjective
  isTrivialOn := ⟨fun c hc ↦ by
    rw [IsScalarTower.algebraMap_apply k k' F']
    exact P'.isTrivialOn.eq_one _ ((map_ne_zero (algebraMap k k')).mpr hc)⟩

private theorem restrictConstants_valuation (P' : Place k' F') :
    (restrictConstants (k := k) P').valuation = P'.valuation :=
  rfl

private theorem restrictConstants_integers (P' : Place k' F') :
    (restrictConstants (k := k) P').integers = P'.integers :=
  SetLike.ext fun x ↦ by rw [mem_integers_iff, mem_integers_iff, restrictConstants_valuation]

private theorem restrictConstants_completionEmbedding (P' : Place k' F') (x : F') :
    ((restrictConstants (k := k) P').completionEmbedding x : P'.Completion) =
      P'.completionEmbedding x := by
  rw [completionEmbedding_apply, completionEmbedding_apply]
  rfl

private theorem mem_restrictConstants_completionIntegers (P' : Place k' F')
    (z : P'.valuation.Completion) :
    (z : (restrictConstants (k := k) P').Completion) ∈
        (restrictConstants (k := k) P').completionPlace.integers ↔
      (z : P'.Completion) ∈ P'.completionPlace.integers := by
  have hval : (restrictConstants (k := k) P').completionPlace.valuation z =
      P'.completionPlace.valuation z :=
    ((restrictConstants (k := k) P').completionPlace_valuation z).trans
      (P'.completionPlace_valuation z).symm
  exact ((restrictConstants (k := k) P').completionPlace.mem_integers_iff).trans
    ((Eq.to_iff (congrArg (· ≤ 1) hval)).trans P'.completionPlace.mem_integers_iff.symm)

private theorem restrict_restrictConstants [Algebra.IsIntegral F F'] (P' : Place k' F') :
    (restrictConstants (k := k) P').restrict k F = P'.restrict k F := by
  refine (restrict_eq_iff_integers_le k F _ _).mpr fun f hf ↦ ?_
  rw [restrictConstants_integers]
  exact (mem_integers_restrict_iff k F P' f).mp hf

private theorem completionExtension_restrictConstants [Algebra.IsIntegral F F']
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P) :
    P.completionExtension (restrictConstants (k := k) P')
      ((restrict_restrictConstants (k := k) P').trans hP) = P.completionExtension P' hP := by
  let hQ' : (restrictConstants (k := k) P').restrict k F = P :=
    (restrict_restrictConstants (k := k) P').trans hP
  refine P.eq_completionExtension_of_continuous P' hP
    (P.continuous_completionExtension (restrictConstants (k := k) P') hQ') fun x ↦ ?_
  exact (P.completionExtension_completionEmbedding (restrictConstants (k := k) P') hQ' x).trans
    (restrictConstants_completionEmbedding P' (algebraMap F F' x))

private theorem completionExtensionAlgebra_restrictConstants [Algebra.IsIntegral F F']
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P) :
    P.completionExtensionAlgebra (restrictConstants (k := k) P')
      ((restrict_restrictConstants (k := k) P').trans hP) =
      P.completionExtensionAlgebra P' hP := by
  let hQ' : (restrictConstants (k := k) P').restrict k F = P :=
    (restrict_restrictConstants (k := k) P').trans hP
  refine Algebra.algebra_ext _ _ fun r ↦ ?_
  have h₁ : @algebraMap P.Completion P'.valuation.Completion _ _
      (P.completionExtensionAlgebra (restrictConstants (k := k) P') hQ') r =
      P.completionExtension (restrictConstants (k := k) P') hQ' r :=
    congrArg (fun f : P.Completion →+* P'.valuation.Completion ↦ f r)
      (P.algebraMap_completionExtensionAlgebra (restrictConstants (k := k) P') hQ')
  have h₂ : @algebraMap P.Completion P'.valuation.Completion _ _
      (P.completionExtensionAlgebra P' hP) r = P.completionExtension P' hP r :=
    congrArg (fun f : P.Completion →+* P'.valuation.Completion ↦ f r)
      (P.algebraMap_completionExtensionAlgebra P' hP)
  exact h₁.trans ((congrArg (fun f : P.Completion →+* P'.valuation.Completion ↦ f r)
    (completionExtension_restrictConstants P P' hP)).trans h₂.symm)

private theorem trace_restrictConstants [Algebra.IsIntegral F F']
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)
    (w : P'.valuation.Completion) :
    @Algebra.trace P.Completion P'.valuation.Completion _ _
      (P.completionExtensionAlgebra P' hP) w =
    @Algebra.trace P.Completion P'.valuation.Completion _ _
      (P.completionExtensionAlgebra (restrictConstants (k := k) P')
        ((restrict_restrictConstants (k := k) P').trans hP)) w := by
  rw [completionExtensionAlgebra_restrictConstants P P' hP]

/-- In a finite product of finite free algebras, the trace of a single-coordinate vector is the
trace in that factor. -/
private theorem trace_pi_single {R ι : Type*} [CommRing R] [Finite ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)] (i₀ : ι) (x : A i₀) :
    Algebra.trace R (∀ i, A i) (Pi.single i₀ x) = Algebra.trace R (A i₀) x := by
  have := Fintype.ofFinite ι
  rw [TauCeti.Algebra.trace_pi, Finset.sum_eq_single i₀]
  · simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']
variable (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)

/-- Equal-constants case of `TauCeti.Place.sum_trace_mul_smul_completionEmbedding_eq`. -/
private theorem sum_trace_mul_smul_completionEmbedding_eq_sameConstants
    {Q' : Place k F'} (hQ' : Q'.restrict k F = P) {ι₀ : Type*} [Fintype ι₀] (b y : ι₀ → F')
    (h : ∀ x : F', ∑ i, Algebra.trace F F' (x * b i) • y i = x) (z : Q'.Completion) :
    letI := P.completionExtensionAlgebra Q' hQ'
    ∑ i, Algebra.trace P.Completion Q'.Completion
        (z * Q'.completionEmbedding (b i)) • Q'.completionEmbedding (y i) = z := by
  classical
  let ι := {Q : Place k F' // Q.restrict k F = P}
  let _ := fun q : ι ↦ P.completionExtensionAlgebra q.1 q.2
  have _ := fun q : ι ↦ finiteDimensional_completion P q.1 q.2
  have := Fintype.ofFinite ι
  let Δ (w : F') : ∀ q : ι, q.1.Completion := fun q ↦ q.1.completionEmbedding w
  -- Define the `F̂_P`-linear endomorphism of `∏_{Q ∣ P} F̂'_Q` attached to the family `(b, y)`.
  let Φ : (∀ q : ι, q.1.Completion) →ₗ[P.Completion] ∀ q : ι, q.1.Completion :=
    ∑ i, (LinearMap.toSpanSingleton P.Completion _ (Δ (y i))).comp
      ((Algebra.trace P.Completion (∀ q : ι, q.1.Completion)).comp
        (LinearMap.mulRight P.Completion (Δ (b i))))
  have hΦ_diag (x : F') : Φ (Δ x) = Δ x := by
    funext q
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
      LinearMap.toSpanSingleton_apply, Finset.sum_apply, Pi.smul_apply]
    have hmul (i : ι₀) : Δ x * Δ (b i) = Δ (x * b i) := funext fun _ ↦ (map_mul _ _ _).symm
    have htr (i : ι₀) : Algebra.trace P.Completion (∀ r : ι, r.1.Completion) (Δ (x * b i)) =
        P.completionEmbedding (Algebra.trace F F' (x * b i)) := by
      rw [TauCeti.Algebra.trace_pi, completionEmbedding_trace_of_isSeparable k P,
        finsum_eq_sum_of_fintype]
    simp_rw [hmul, htr]
    calc ∑ i, P.completionEmbedding (Algebra.trace F F' (x * b i)) • q.1.completionEmbedding (y i)
        = ∑ i, q.1.completionEmbedding (Algebra.trace F F' (x * b i) • y i) :=
          Finset.sum_congr rfl fun i _ ↦ (completionEmbedding_smul P q.1 q.2 _ _).symm
      _ = q.1.completionEmbedding (∑ i, Algebra.trace F F' (x * b i) • y i) :=
          (map_sum q.1.completionEmbedding _ _).symm
      _ = q.1.completionEmbedding x := congrArg q.1.completionEmbedding (h x)
  have hΦ_id : Φ = LinearMap.id := by
    refine LinearMap.ext_on (span_completion_pi_eq_top k F' P) fun _ hξ ↦ ?_
    obtain ⟨x, rfl⟩ := hξ
    exact hΦ_diag x
  let q₀ : ι := ⟨Q', hQ'⟩
  have hsingle := congrFun (LinearMap.congr_fun hΦ_id (Pi.single q₀ z)) q₀
  simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
    LinearMap.toSpanSingleton_apply, LinearMap.id_apply, Finset.sum_apply, Pi.smul_apply,
    Pi.single_eq_same] at hsingle
  refine (Finset.sum_congr rfl fun i _ ↦ ?_).symm.trans hsingle
  have hmul : Pi.single q₀ z * Δ (b i) = Pi.single q₀ (z * Q'.completionEmbedding (b i)) := by
    funext q
    rcases eq_or_ne q q₀ with rfl | hq
    · simp [Δ, q₀]
    · simp [Pi.single_eq_of_ne hq]
  rw [hmul, trace_pi_single]

/-- **Trace-dual expansions pass to completions.** If `x = ∑ᵢ Tr_{F'/F}(x bᵢ) • yᵢ` holds for
every `x ∈ F'`, then `z = ∑ᵢ Tr_{F̂'_{P'}/F̂_P}(z bᵢ) • yᵢ` holds for every `z ∈ F̂'_{P'}`. Neither
`IsFunctionField`, nor integrality of `k' / k`, nor residue-field separability is needed. -/
theorem sum_trace_mul_smul_completionEmbedding_eq {ι₀ : Type*} [Fintype ι₀] (b y : ι₀ → F')
    (h : ∀ x : F', ∑ i, Algebra.trace F F' (x * b i) • y i = x) (z : P'.Completion) :
    letI := P.completionExtensionAlgebra P' hP
    ∑ i, Algebra.trace P.Completion P'.Completion
        (z * P'.completionEmbedding (b i)) • P'.completionEmbedding (y i) = z := by
  let Q' : Place k F' := restrictConstants (k := k) P'
  have hQ' : Q'.restrict k F = P := (restrict_restrictConstants (k := k) P').trans hP
  let zQ : Q'.Completion := z
  have key : (letI := P.completionExtensionAlgebra Q' hQ';
      ∑ i, Algebra.trace P.Completion Q'.Completion
        (zQ * Q'.completionEmbedding (b i)) • Q'.completionEmbedding (y i)) = zQ :=
    sum_trace_mul_smul_completionEmbedding_eq_sameConstants P hQ' b y h zQ
  refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans key
  have hmul : (z * P'.completionEmbedding (b i) : P'.valuation.Completion) =
      (zQ * Q'.completionEmbedding (b i) : P'.valuation.Completion) :=
    congrArg (z * ·) (restrictConstants_completionEmbedding (k := k) P' (b i)).symm
  have htr : @Algebra.trace P.Completion P'.valuation.Completion _ _
      (P.completionExtensionAlgebra P' hP) (z * P'.completionEmbedding (b i)) =
      @Algebra.trace P.Completion P'.valuation.Completion _ _
        (P.completionExtensionAlgebra Q' hQ') (zQ * Q'.completionEmbedding (b i)) :=
    (congrArg (@Algebra.trace P.Completion P'.valuation.Completion _ _
      (P.completionExtensionAlgebra P' hP)) hmul).trans (trace_restrictConstants P P' hP _)
  let r : P.Completion := @Algebra.trace P.Completion P'.valuation.Completion _ _
    (P.completionExtensionAlgebra Q' hQ') (zQ * Q'.completionEmbedding (b i))
  have hsmul₁ : (letI := P.completionExtensionAlgebra P' hP;
      Algebra.trace P.Completion P'.Completion (z * P'.completionEmbedding (b i)) •
        P'.completionEmbedding (y i)) =
      P.completionExtension P' hP r * P'.completionEmbedding (y i) := by
    let _ := P.completionExtensionAlgebra P' hP
    rw [Algebra.smul_def, P.algebraMap_completionExtensionAlgebra P' hP]
    exact congrArg (fun t ↦ P.completionExtension P' hP t * P'.completionEmbedding (y i)) htr
  have hsmul₂ : (letI := P.completionExtensionAlgebra Q' hQ';
      Algebra.trace P.Completion Q'.Completion (zQ * Q'.completionEmbedding (b i)) •
        Q'.completionEmbedding (y i)) =
      P.completionExtension P' hP r * P'.completionEmbedding (y i) := by
    let _ := P.completionExtensionAlgebra Q' hQ'
    rw [Algebra.smul_def, P.algebraMap_completionExtensionAlgebra Q' hQ',
      completionExtension_restrictConstants P P' hP]
    exact congrArg (P.completionExtension P' hP r * ·)
      (restrictConstants_completionEmbedding (k := k) P' (y i))
  exact hsmul₁.trans hsmul₂.symm

/-- The `𝒪̂_P`-linear trace pairing `m ↦ ∑_{Q ∣ P} Tr_{F̂'_Q / F̂_P}(d · m_Q)` on `∏_{Q ∣ P} 𝒪̂_Q`
in the equal-constants setting. -/
private noncomputable def semilocalTraceLinearMap
    [Fintype {Q : Place k F' // Q.restrict k F = P}] (d : F') :
    letI := fun q : {Q : Place k F' // Q.restrict k F = P} ↦
      P.completionIntegersExtensionAlgebra q.1 q.2
    (∀ q : {Q : Place k F' // Q.restrict k F = P}, q.1.completionPlace.integers) →ₗ[
      P.completionPlace.integers] P.Completion := by
  let ι := {Q : Place k F' // Q.restrict k F = P}
  let _ := fun q : ι ↦ P.completionExtensionAlgebra q.1 q.2
  let _ := fun q : ι ↦ P.completionIntegersExtensionAlgebra q.1 q.2
  exact
    { toFun m := ∑ q : ι, Algebra.trace P.Completion q.1.Completion
        (q.1.completionEmbedding d * (m q : q.1.Completion))
      map_add' m₁ m₂ := by
        simp only [Pi.add_apply, AddMemClass.coe_add, mul_add, map_add, Finset.sum_add_distrib]
      map_smul' a m := by
        simp only [RingHom.id_apply]
        conv_rhs => rw [Algebra.smul_def, ValuationSubring.algebraMap_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        have hsmul : q.1.completionEmbedding d * (((a • m) q : q.1.completionPlace.integers) :
            q.1.Completion) = (a : P.Completion) •
              (q.1.completionEmbedding d * (m q : q.1.Completion)) := by
          rw [Pi.smul_apply, Algebra.smul_def, MulMemClass.coe_mul,
            coe_algebraMap_completionIntegersExtensionAlgebra, Algebra.smul_def,
            P.algebraMap_completionExtensionAlgebra q.1 q.2]
          ring
        rw [hsmul, LinearMap.map_smul, smul_eq_mul] }

/-- Equal-constants case of `TauCeti.Place.completionEmbedding_mem_traceDual`. -/
private theorem completionEmbedding_mem_traceDual_sameConstants
    {Q' : Place k F'} (hQ' : Q'.restrict k F = P) {d : F'}
    (hd : d ∈ Submodule.traceDual P.integers F
      (1 : Submodule (integralClosure P.integers F') F')) :
    letI := P.completionExtensionAlgebra Q' hQ'
    letI := P.completionIntegersExtensionAlgebra Q' hQ'
    Q'.completionEmbedding d ∈ Submodule.traceDual P.completionPlace.integers P.Completion
      (1 : Submodule Q'.completionPlace.integers Q'.Completion) := by
  classical
  let ι := {Q : Place k F' // Q.restrict k F = P}
  let _ := fun q : ι ↦ P.completionExtensionAlgebra q.1 q.2
  let _ := fun q : ι ↦ P.completionIntegersExtensionAlgebra q.1 q.2
  have := Fintype.ofFinite ι
  let Λ := semilocalTraceLinearMap P d
  -- `Λ` maps every diagonal generator into `𝒪̂_P`, hence maps all of `∏_{Q ∣ P} 𝒪̂_Q` into `𝒪̂_P`.
  have hΛ_mem (m : ∀ q : ι, q.1.completionPlace.integers) :
      Λ m ∈ (1 : Submodule P.completionPlace.integers P.Completion) := by
    have htop : Submodule.comap Λ (1 : Submodule P.completionPlace.integers P.Completion) = ⊤ := by
      refine top_unique ((span_completionIntegers_pi_eq_top k F' P).ge.trans
        (Submodule.span_le.mpr ?_))
      rintro _ ⟨y, rfl⟩
      have hy : IsIntegral P.integers y.1 :=
        (isIntegral_iff_forall_restrict_eq_mem_integers_of_isSeparable k P).mpr
          fun Q hQ ↦ y.2 ⟨Q, hQ⟩
      obtain ⟨r, hr⟩ := Submodule.mem_traceDual.mp hd y.1 (Submodule.mem_one.mpr ⟨⟨y.1, hy⟩, rfl⟩)
      rw [Algebra.traceForm_apply] at hr
      have hΛy : Λ (fun q : ι ↦ q.1.completionIntegersEmbedding ⟨y.1, y.2 q⟩) =
          P.completionEmbedding (algebraMap P.integers F r) := by
        simp only [Λ, semilocalTraceLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
          completionIntegersEmbedding_apply, ← map_mul]
        rw [← finsum_eq_sum_of_fintype, ← completionEmbedding_trace_of_isSeparable k P, ← hr]
      rw [SetLike.mem_coe, Submodule.mem_comap, hΛy]
      exact Submodule.mem_one.mpr ⟨P.completionIntegersEmbedding r,
        by simp [ValuationSubring.algebraMap_apply]⟩
    exact Submodule.mem_comap.mp (htop.symm ▸ Submodule.mem_top)
  let _ := P.completionExtensionAlgebra Q' hQ'
  let _ := P.completionIntegersExtensionAlgebra Q' hQ'
  rw [Submodule.mem_traceDual]
  intro _ hz
  obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hz
  let q₀ : ι := ⟨Q', hQ'⟩
  have hsingle : Λ (Pi.single q₀ z) =
      Algebra.trace P.Completion Q'.Completion
        (Q'.completionEmbedding d * (z : Q'.Completion)) := by
    simp only [Λ, semilocalTraceLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single q₀]
    · simp [q₀]
    · intro q _ hq
      simp [Pi.single_eq_of_ne hq]
    · intro h
      exact absurd (Finset.mem_univ q₀) h
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hΛ_mem (Pi.single q₀ z))
  exact ⟨r, hr.trans (by rw [hsingle, Algebra.traceForm_apply, ValuationSubring.algebraMap_apply])⟩

/-- **Elements of the complementary module remain trace-dual after completion.** For `d ∈ C_P`,
its image `P'.completionEmbedding d` lies in the completed complementary module `Ĉ_{P'}`. -/
theorem completionEmbedding_mem_traceDual {d : F'}
    (hd : d ∈ Submodule.traceDual P.integers F
      (1 : Submodule (integralClosure P.integers F') F')) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    P'.completionEmbedding d ∈ Submodule.traceDual P.completionPlace.integers P.Completion
      (1 : Submodule P'.completionPlace.integers P'.Completion) := by
  let Q' : Place k F' := restrictConstants (k := k) P'
  have hQ' : Q'.restrict k F = P := (restrict_restrictConstants (k := k) P').trans hP
  have key := completionEmbedding_mem_traceDual_sameConstants P hQ' hd
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  rw [Submodule.mem_traceDual]
  intro _ hw
  obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hw
  let zQ : Q'.Completion := (z : P'.valuation.Completion)
  have hzQ : zQ ∈ Q'.completionPlace.integers :=
    (mem_restrictConstants_completionIntegers (k := k) P' zQ).mpr z.2
  have hwQ : zQ ∈ (1 : Submodule Q'.completionPlace.integers Q'.Completion) :=
    Submodule.mem_one.mpr ⟨⟨zQ, hzQ⟩, rfl⟩
  have hmem : (letI := P.completionExtensionAlgebra Q' hQ';
      Algebra.trace P.Completion Q'.Completion (Q'.completionEmbedding d * zQ)) ∈
      (algebraMap P.completionPlace.integers P.Completion).range := by
    let _ := P.completionExtensionAlgebra Q' hQ'
    let _ := P.completionIntegersExtensionAlgebra Q' hQ'
    simpa only [Algebra.traceForm_apply] using Submodule.mem_traceDual.mp key zQ hwQ
  have hmul : (P'.completionEmbedding d * (z : P'.Completion) : P'.valuation.Completion) =
      (Q'.completionEmbedding d * zQ : P'.valuation.Completion) :=
    congrArg (· * (z : P'.valuation.Completion))
      (restrictConstants_completionEmbedding (k := k) P' d).symm
  have htr : Algebra.trace P.Completion P'.Completion
      (P'.completionEmbedding d * (z : P'.Completion)) =
      (letI := P.completionExtensionAlgebra Q' hQ';
        Algebra.trace P.Completion Q'.Completion (Q'.completionEmbedding d * zQ)) :=
    (congrArg (@Algebra.trace P.Completion P'.valuation.Completion _ _
      (P.completionExtensionAlgebra P' hP)) hmul).trans (trace_restrictConstants P P' hP _)
  rw [Algebra.traceForm_apply, ValuationSubring.algebraMap_apply, htr]
  exact hmem

/-- **The completed complementary module is spanned by the local complementary module**:
`Submodule.span 𝒪̂_{P'} (P'.completionEmbedding '' C_P) = Ĉ_{P'}`. -/
theorem span_completionEmbedding_traceDual_eq_traceDual :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    Submodule.span P'.completionPlace.integers
        (P'.completionEmbedding ''
          (Submodule.traceDual P.integers F
            (1 : Submodule (integralClosure P.integers F') F') : Set F')) =
      Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  refine le_antisymm (Submodule.span_le.mpr ?_) fun z hz ↦ ?_
  · rintro _ ⟨d, hd, rfl⟩
    exact P.completionEmbedding_mem_traceDual P' hP hd
  have : Module.Free P.integers (integralClosure P.integers F') :=
    .of_basis (integralClosureFinBasis F' P)
  obtain ⟨n, b, y, hy, hb⟩ :=
    exists_sum_trace_mul_smul_eq P.integers F (L := F') (B := integralClosure P.integers F')
  rw [← P.sum_trace_mul_smul_completionEmbedding_eq P' hP
    (fun i ↦ algebraMap (integralClosure P.integers F') F' (b i)) y hb z]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  obtain ⟨c, hc⟩ := Submodule.mem_traceDual.mp hz _ (Submodule.mem_one.mpr
    ⟨P.integralClosureToCompletionIntegers P' hP (b i), rfl⟩)
  rw [Algebra.traceForm_apply] at hc
  have hsmul : Algebra.trace P.Completion P'.Completion
      (z * P'.completionEmbedding (algebraMap (integralClosure P.integers F') F' (b i))) •
        P'.completionEmbedding (y i) =
      (algebraMap P.completionPlace.integers P'.completionPlace.integers c) •
        P'.completionEmbedding (y i) := by
    rw [← coe_integralClosureToCompletionIntegers P P' hP, ← ValuationSubring.algebraMap_apply,
      ← hc, ValuationSubring.algebraMap_apply, Algebra.smul_def, Algebra.smul_def,
      P.algebraMap_completionExtensionAlgebra P' hP, ValuationSubring.algebraMap_apply,
      P.coe_algebraMap_completionIntegersExtensionAlgebra P' hP]
  rw [hsmul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y i, hy i, rfl⟩)

/-- **Trace duals commute with completion**, as fractional ideals: extending the fractional-ideal
dual of `𝒪'_P` over `𝒪_P` along `integralClosureToCompletionIntegers` gives the fractional-ideal
dual of `𝒪̂_{P'}` over `𝒪̂_P`. -/
theorem extended_dual_one_eq_dual_one_completionIntegers :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    letI := isIntegralClosure_completionIntegers P P' hP
    letI := finiteDimensional_completion P P' hP
    letI := isSeparable_completion P P' hP
    (FractionalIdeal.dual P.integers F
        (1 : FractionalIdeal (integralClosure P.integers F')⁰ F')).extended P'.Completion
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (P.integralClosureToCompletionIntegers_injective P' hP)) =
      FractionalIdeal.dual P.completionPlace.integers P.Completion
        (1 : FractionalIdeal P'.completionPlace.integers⁰ P'.Completion) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := isIntegralClosure_completionIntegers P P' hP
  have := finiteDimensional_completion P P' hP
  have := isSeparable_completion P P' hP
  set hf := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (P.integralClosureToCompletionIntegers_injective P' hP)
  have hmap : IsLocalization.map (S := F') P'.Completion
      (P.integralClosureToCompletionIntegers P' hP) hf =
      (P'.completionEmbedding : F' →+* P'.Completion) := by
    refine IsFractionRing.ringHom_ext (A := integralClosure P.integers F') fun b ↦ ?_
    rw [IsLocalization.map_eq]
    exact coe_integralClosureToCompletionIntegers P P' hP b
  have hdual : ((FractionalIdeal.dual P.integers F
      (1 : FractionalIdeal (integralClosure P.integers F')⁰ F')) : Set F') =
      Submodule.traceDual P.integers F
        (1 : Submodule (integralClosure P.integers F') F') := by
    ext x
    rw [SetLike.mem_coe, SetLike.mem_coe, ← FractionalIdeal.mem_coeToSubmodule,
      FractionalIdeal.coeToSubmodule_dual_one]
  rw [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coeToSubmodule_extended_eq_span,
    hmap, RingHom.coe_coe, hdual, FractionalIdeal.coeToSubmodule_dual_one]
  exact P.span_completionEmbedding_traceDual_eq_traceDual P' hP

/-- **The different ideal commutes with completion.** Extending the different ideal of the local
model `𝒪_P ⊆ 𝒪'_P` along `integralClosureToCompletionIntegers` produces the different ideal of the
completed valuation rings `𝒪̂_P ⊆ 𝒪̂_{P'}`. -/
theorem map_differentIdeal_eq_differentIdeal_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    (differentIdeal P.integers (integralClosure P.integers F')).map
        (P.integralClosureToCompletionIntegers P' hP) =
      differentIdeal P.completionPlace.integers P'.completionPlace.integers := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := isIntegralClosure_completionIntegers P P' hP
  have := finiteDimensional_completion P P' hP
  have := isSeparable_completion P P' hP
  set hf := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (P.integralClosureToCompletionIntegers_injective P' hP)
  rw [← FractionalIdeal.coeIdeal_inj (K := P'.Completion),
    ← FractionalIdeal.extended_coeIdeal_eq_map (K := F') P'.Completion hf,
    ← FractionalIdeal.extendedHom'_apply,
    coeIdeal_differentIdeal P.integers F F' (integralClosure P.integers F'),
    coeIdeal_differentIdeal P.completionPlace.integers P.Completion P'.Completion
      P'.completionPlace.integers,
    map_inv₀, FractionalIdeal.extendedHom'_apply,
    P.extended_dual_one_eq_dual_one_completionIntegers P' hP]

section AffineModel

variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B F] [IsFractionRing B F]
  [CommRing C] [IsDedekindDomain C] [Algebra C F'] [IsFractionRing C F']
  [Algebra B C] [Algebra B F'] [IsScalarTower B C F'] [IsScalarTower B F F']
  [IsIntegralClosure C B F'] [Module.IsTorsionFree B C]

/-- **The different ideal of any affine Dedekind model finite at `P'` generates the completed
different ideal at `P'`.** -/
theorem map_differentIdeal_model_eq_differentIdeal_completionIntegers
    (hC : ∀ c : C, algebraMap C F' c ∈ P'.integers) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    (differentIdeal B C).map (P'.modelToCompletionIntegers hC) =
      differentIdeal P.completionPlace.integers P'.completionPlace.integers := by
  subst hP
  let P₀ : Place k F := P'.restrict k F
  have hB : ∀ b : B, algebraMap B F b ∈ P₀.integers :=
    algebraMap_mem_integers_restrict k F P' hC
  let _ : Module.Finite B C := IsIntegralClosure.finite B F F' C
  let p : HeightOneSpectrum B := P₀.center hB
  let _ : Algebra B P₀.integers := ((algebraMap B F).codRestrict P₀.integers hB).toAlgebra
  let _ : IsScalarTower B P₀.integers F := .of_algebraMap_eq fun _ ↦ rfl
  let eB : HeightOneSpectrum.valuationSubringAtPrime F p ≃ₐ[B] P₀.integers :=
    AlgEquiv.ofRingEquiv
      (f := RingEquiv.subringCongr
        (congrArg ValuationSubring.toSubring (P₀.valuationSubringAtPrime_eq_integers hB)))
      fun _ ↦ rfl
  let _ : IsLocalization p.asIdeal.primeCompl P₀.integers :=
    IsLocalization.isLocalization_of_algEquiv p.asIdeal.primeCompl eB
  let _ : IsScalarTower B P₀.integers F' :=
    .of_algebraMap_eq fun x ↦ IsScalarTower.algebraMap_apply B F F' x
  let Cₘ := integralClosure P₀.integers F'
  let _ : Algebra C Cₘ :=
    ((algebraMap C F').codRestrict Cₘ.toSubring fun c ↦
      IsIntegral.tower_top (R := B) (A := P₀.integers)
        ((IsIntegralClosure.isIntegral_iff (A := C) (R := B)).mpr ⟨c, rfl⟩)).toAlgebra
  let _ : IsScalarTower C Cₘ F' := .of_algebraMap_eq fun _ ↦ rfl
  let _ : IsScalarTower B C Cₘ := .of_algebraMap_eq fun x ↦
    Subtype.ext (IsScalarTower.algebraMap_apply B C F' x)
  let _ : IsScalarTower B P₀.integers Cₘ := .of_algebraMap_eq fun x ↦
    Subtype.ext (IsScalarTower.algebraMap_apply B F F' x)
  let _ : IsLocalization (Algebra.algebraMapSubmonoid C p.asIdeal.primeCompl) Cₘ :=
    isLocalization_algebraMapSubmonoid_of_isIntegralClosure (R := B) (Rₘ := P₀.integers) (S := C)
      (Sₘ := Cₘ) (L := F') (M := p.asIdeal.primeCompl)
  have hcomp : P'.modelToCompletionIntegers hC =
      (P₀.integralClosureToCompletionIntegers P' rfl).comp (algebraMap C Cₘ) := by
    ext c
    rw [RingHom.comp_apply, coe_modelToCompletionIntegers, coe_integralClosureToCompletionIntegers]
    exact congrArg P'.completionEmbedding (IsScalarTower.algebraMap_apply C Cₘ F' c)
  rw [hcomp, ← Ideal.map_map,
    map_differentIdeal_eq_differentIdeal (R := B) (Rₘ := P₀.integers) (S := C) (Sₘ := Cₘ)
      (K := F) (L := F') (M := p.asIdeal.primeCompl),
    P₀.map_differentIdeal_eq_differentIdeal_completionIntegers P' rfl]

/-- **The fractional-ideal dual of any affine Dedekind model finite at `P'` extends to the
completed fractional-ideal dual at `P'`.** -/
theorem extended_dual_one_model_eq_dual_one_completionIntegers
    (hC : ∀ c : C, algebraMap C F' c ∈ P'.integers) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    letI := isIntegralClosure_completionIntegers P P' hP
    letI := finiteDimensional_completion P P' hP
    letI := isSeparable_completion P P' hP
    (FractionalIdeal.dual B F (1 : FractionalIdeal C⁰ F')).extended P'.Completion
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (P'.modelToCompletionIntegers_injective hC)) =
      FractionalIdeal.dual P.completionPlace.integers P.Completion
        (1 : FractionalIdeal P'.completionPlace.integers⁰ P'.Completion) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := isIntegralClosure_completionIntegers P P' hP
  have := finiteDimensional_completion P P' hP
  have := isSeparable_completion P P' hP
  set hf := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (P'.modelToCompletionIntegers_injective hC)
  apply inv_injective
  rw [← FractionalIdeal.extendedHom'_apply, ← map_inv₀,
    ← coeIdeal_differentIdeal B F F' C, FractionalIdeal.extendedHom'_apply,
    FractionalIdeal.extended_coeIdeal_eq_map (K := F') P'.Completion hf,
    ← coeIdeal_differentIdeal P.completionPlace.integers P.Completion P'.Completion
      P'.completionPlace.integers]
  exact (FractionalIdeal.coeIdeal_inj (K := P'.Completion)).mpr
    (P.map_differentIdeal_model_eq_differentIdeal_completionIntegers P' hP hC)

/-- **The trace dual of any affine Dedekind model finite at `P'` spans the completed trace dual at
`P'`.** -/
theorem span_completionEmbedding_traceDual_model_eq_traceDual
    (hC : ∀ c : C, algebraMap C F' c ∈ P'.integers) :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    Submodule.span P'.completionPlace.integers
        (P'.completionEmbedding '' (Submodule.traceDual B F (1 : Submodule C F') : Set F')) =
      Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := isIntegralClosure_completionIntegers P P' hP
  have := finiteDimensional_completion P P' hP
  have := isSeparable_completion P P' hP
  set hf := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (P'.modelToCompletionIntegers_injective hC)
  have hmap : IsLocalization.map (S := F') P'.Completion
      (P'.modelToCompletionIntegers hC) hf =
      (P'.completionEmbedding : F' →+* P'.Completion) := by
    refine IsFractionRing.ringHom_ext (A := C) fun c ↦ ?_
    rw [IsLocalization.map_eq]
    exact coe_modelToCompletionIntegers P' hC c
  have hdual : ((FractionalIdeal.dual B F (1 : FractionalIdeal C⁰ F')) : Set F') =
      Submodule.traceDual B F (1 : Submodule C F') := by
    ext x
    rw [SetLike.mem_coe, SetLike.mem_coe, ← FractionalIdeal.mem_coeToSubmodule,
      FractionalIdeal.coeToSubmodule_dual_one]
  have hext := congrArg FractionalIdeal.coeToSubmodule
    (P.extended_dual_one_model_eq_dual_one_completionIntegers (B := B) P' hP hC)
  rwa [FractionalIdeal.coeToSubmodule_extended_eq_span, hmap, RingHom.coe_coe, hdual,
    FractionalIdeal.coeToSubmodule_dual_one] at hext

end AffineModel

end TraceDual

/-! ### The completed different ideal, its multiplicity, length, and discriminant -/

section CompletedDifferent

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']
variable (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P)

/-- **The completed different ideal is the `d(P' ∣ P)`-th power of the maximal ideal of
`𝒪̂_{P'}`**, with no hypothesis on the residue extension. -/
theorem differentIdeal_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    differentIdeal P.completionPlace.integers P'.completionPlace.integers =
      maximalIdeal P'.completionPlace.integers ^ differentExponent k F P' := by
  subst hP
  let P₀ : Place k F := P'.restrict k F
  let _ := P₀.completionIntegersExtensionAlgebra P' rfl
  rw [← P₀.map_differentIdeal_eq_differentIdeal_completionIntegers P' rfl]
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun y hy ↦ ?_) ?_
  · rw [Ideal.mem_comap, P'.completionPlace.mem_maximalIdeal_pow_iff_coe_mem_filtration]
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    have hyc0 : (P₀.integralClosureToCompletionIntegers P' rfl y : P'.Completion) ≠ 0 := by
      simpa [coe_integralClosureToCompletionIntegers] using hy0
    rw [P'.completionPlace.mem_filtration_iff_le_ord hyc0, coe_integralClosureToCompletionIntegers,
      ord_completionEmbedding]
    exact differentExponent_le_ord_of_mem_differentIdeal k F P' hy hy0
  · obtain ⟨y, hy, hy0, hord⟩ := exists_mem_differentIdeal_ord_eq k F P'
    set w := P₀.integralClosureToCompletionIntegers P' rfl y
    have hw_mem : w ∈ (differentIdeal P₀.integers (integralClosure P₀.integers F')).map
        (P₀.integralClosureToCompletionIntegers P' rfl) := Ideal.mem_map_of_mem _ hy
    have hw0 : (w : P'.Completion) ≠ 0 := by
      simpa [w, coe_integralClosureToCompletionIntegers] using hy0
    have hword : P'.completionPlace.ord (w : P'.Completion) = differentExponent k F P' := by
      simpa [w, coe_integralClosureToCompletionIntegers] using hord
    intro z hz
    rw [P'.completionPlace.mem_maximalIdeal_pow_iff_coe_mem_filtration] at hz
    have hdiv : (z : P'.Completion) / (w : P'.Completion) ∈ P'.completionPlace.integers := by
      rcases eq_or_ne (z : P'.Completion) 0 with hz0 | hz0
      · simp [hz0]
      rw [mem_integers_iff_ord_nonneg, P'.completionPlace.ord_div hz0 hw0, hword]
      have := (P'.completionPlace.mem_filtration_iff_le_ord hz0).mp hz
      omega
    have hzw : z = (⟨_, hdiv⟩ : P'.completionPlace.integers) * w :=
      Subtype.ext (div_mul_cancel₀ (z : P'.Completion) hw0).symm
    rw [hzw]
    exact Ideal.mul_mem_left _ _ hw_mem

/-- **The multiplicity of the maximal ideal in the completed different is `d(P' ∣ P)`.** -/
theorem multiplicity_differentIdeal_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    multiplicity (maximalIdeal P'.completionPlace.integers)
        (differentIdeal P.completionPlace.integers P'.completionPlace.integers) =
      differentExponent k F P' := by
  let _ := P.completionIntegersExtensionAlgebra P' hP
  rw [P.differentIdeal_completionIntegers P' hP]
  exact multiplicity_pow_self_of_prime
    (Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field _) inferInstance) _

@[simp]
theorem multiplicity_differentIdeal_completionIntegers_restrict :
    letI := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
    multiplicity (maximalIdeal P'.completionPlace.integers)
        (differentIdeal (P'.restrict k F).completionPlace.integers
          P'.completionPlace.integers) =
      differentExponent k F P' :=
  multiplicity_differentIdeal_completionIntegers (P'.restrict k F) P' rfl

/-- **Valuation criterion for the completed complementary module**: `z ∈ Ĉ_{P'}` if and only if
`v_{P'}(z) ≤ exp d(P' ∣ P)` in `F̂'_{P'}`. -/
theorem mem_traceDual_completion_iff_valuation_le {z : P'.Completion} :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    z ∈ Submodule.traceDual P.completionPlace.integers P.Completion
        (1 : Submodule P'.completionPlace.integers P'.Completion) ↔
      P'.completionPlace.valuation z ≤ WithZero.exp (differentExponent k F P' : ℤ) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := isIntegralClosure_completionIntegers P P' hP
  have := finiteDimensional_completion P P' hP
  have := isSeparable_completion P P' hP
  obtain ⟨π, hπ0, hπ⟩ := P'.completionPlace.exists_ne_zero_ord_eq 1
  have hπ_int : π ∈ P'.completionPlace.integers := by
    rw [mem_integers_iff_ord_nonneg, hπ]; norm_num
  set π₀ : P'.completionPlace.integers := ⟨π, hπ_int⟩
  have hmax : maximalIdeal P'.completionPlace.integers = Ideal.span {π₀} :=
    (P'.completionPlace.irreducible_of_isUniformizer
      (P'.completionPlace.isUniformizer_iff_ord_eq_one.mpr hπ)).maximalIdeal_eq
  rw [mem_traceDual_one_iff_forall_mem_differentIdeal (S := P'.completionPlace.integers),
    P.differentIdeal_completionIntegers P' hP, hmax, Ideal.span_singleton_pow]
  have hπpow0 : π ^ differentExponent k F P' ≠ 0 := pow_ne_zero _ hπ0
  have hπpow_ord : P'.completionPlace.ord (π ^ differentExponent k F P') =
      differentExponent k F P' := by rw [P'.completionPlace.ord_pow, hπ, mul_one]
  refine ⟨fun h ↦ ?_, fun h y hy ↦ ?_⟩
  · obtain ⟨b, hb⟩ := Submodule.mem_one.mp
      (h (π₀ ^ differentExponent k F P') (Ideal.mem_span_singleton_self _))
    have hle : P'.completionPlace.valuation (z * π ^ differentExponent k F P') ≤ 1 := by
      have hzb : z * π ^ differentExponent k F P' = b := by
        simpa [π₀] using hb.symm
      rw [hzb]
      exact P'.completionPlace.mem_integers_iff.mp b.2
    rw [map_mul, P'.completionPlace.valuation_eq_exp_neg_ord hπpow0, hπpow_ord] at hle
    calc P'.completionPlace.valuation z
        = P'.completionPlace.valuation z * WithZero.exp (-(differentExponent k F P' : ℤ)) *
            WithZero.exp (differentExponent k F P' : ℤ) := by
          rw [mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one]
      _ ≤ 1 * WithZero.exp (differentExponent k F P' : ℤ) := by gcongr
      _ = WithZero.exp (differentExponent k F P' : ℤ) := one_mul _
  · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hy
    refine Submodule.mem_one.mpr
      ⟨⟨z * (π ^ differentExponent k F P' * c), ?_⟩, by simp [π₀]⟩
    rw [mem_integers_iff, map_mul, map_mul,
      P'.completionPlace.valuation_eq_exp_neg_ord hπpow0, hπpow_ord]
    calc P'.completionPlace.valuation z *
          (WithZero.exp (-(differentExponent k F P' : ℤ)) *
            P'.completionPlace.valuation (c : P'.Completion))
        = (P'.completionPlace.valuation z * WithZero.exp (-(differentExponent k F P' : ℤ))) *
            P'.completionPlace.valuation (c : P'.Completion) := (mul_assoc _ _ _).symm
      _ ≤ (WithZero.exp (differentExponent k F P' : ℤ) *
            WithZero.exp (-(differentExponent k F P' : ℤ))) * 1 := by
          gcongr
          exact P'.completionPlace.mem_integers_iff.mp c.2
      _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, mul_one]

/-- **Length of the completed complementary-module quotient**: over `𝒪̂_P`, the quotient
`Ĉ_{P'} ⧸ 𝒪̂_{P'}` has length `d(P' ∣ P) · f(P' ∣ P)`, where `f(P' ∣ P)` is the full relative
residue degree, including its inseparable factor. -/
theorem length_traceDual_quotient_completionIntegers :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    Module.length P.completionPlace.integers
        ((Submodule.traceDual P.completionPlace.integers P.Completion
            (1 : Submodule P'.completionPlace.integers P'.Completion)) ⧸
          (1 : Submodule P'.completionPlace.integers P'.Completion).comap
            (Submodule.traceDual P.completionPlace.integers P.Completion
              (1 : Submodule P'.completionPlace.integers P'.Completion)).subtype) =
      (differentExponent k F P' : ℕ∞) * relativeDegree k F P' := by
  subst hP
  let _ := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := isIntegralClosure_completionIntegers (P'.restrict k F) P' rfl
  have := finiteDimensional_completion (P'.restrict k F) P' rfl
  have := isSeparable_completion (P'.restrict k F) P' rfl
  have hpos : 0 < Module.finrank (P'.restrict k F).completionPlace.ResidueField
      P'.completionPlace.ResidueField := by
    rw [P'.finrank_residueField_completion, relativeDegree_def]
    exact Module.finrank_pos
  have : Module.Finite (IsLocalRing.ResidueField (P'.restrict k F).completionPlace.integers)
      (IsLocalRing.ResidueField P'.completionPlace.integers) :=
    Module.finite_of_finrank_pos hpos
  rw [length_traceDual_quotient_eq_multiplicity_mul_finrank,
    multiplicity_differentIdeal_completionIntegers_restrict]
  exact congrArg ((differentExponent k F P' : ℕ∞) * Nat.cast ·)
    P'.finrank_residueField_completion

/-- On the valuation ring of any place `Q`, `Ring.ord Q.integers` of a nonzero element agrees with
its place order `Q.ord`. -/
private theorem ringOrd_integers_eq_toNat_ord {K₀ L₀ : Type*} [Field K₀] [Field L₀]
    [Algebra K₀ L₀] (Q : Place K₀ L₀) {x : Q.integers} (hx : x ≠ 0) :
    Ring.ord Q.integers x = ((Q.ord (x : L₀)).toNat : ℕ∞) := by
  rw [Ring.ord_eq_addVal]
  refine ENat.eq_of_forall_natCast_le_iff fun n ↦ ?_
  rw [← TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal,
    Q.mem_maximalIdeal_pow_iff_coe_mem_filtration,
    Q.mem_filtration_iff_le_ord (by simpa using hx), Nat.cast_le]
  have := Q.mem_integers_iff_ord_nonneg.mp x.2
  omega

/-- **Valuation of the completed discriminant (in `Ring.ord` form)**: for any `𝒪̂_P`-basis `b` of
`𝒪̂_{P'}`, `ord_{𝒪̂_P}(discr b) = d(P' ∣ P) · f(P' ∣ P)`, counting the full inseparable residue
degree. -/
theorem ord_discr_completionIntegers {ι : Type*} [Fintype ι] [DecidableEq ι] :
    letI := P.completionIntegersExtensionAlgebra P' hP
    ∀ b : Basis ι P.completionPlace.integers P'.completionPlace.integers,
      Ring.ord P.completionPlace.integers (Algebra.discr P.completionPlace.integers b) =
        (differentExponent k F P' : ℕ∞) * relativeDegree k F P' := by
  subst hP
  let _ := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let _ := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := isIntegralClosure_completionIntegers (P'.restrict k F) P' rfl
  have := isSeparable_completion (P'.restrict k F) P' rfl
  intro b
  rw [ord_discr_eq_multiplicity_mul_finrank (P'.restrict k F).Completion P'.Completion b,
    multiplicity_differentIdeal_completionIntegers_restrict]
  exact congrArg ((differentExponent k F P' : ℕ∞) * Nat.cast ·)
    P'.finrank_residueField_completion

/-- **Valuation of the completed discriminant (in `Place.ord` form)**: for any `𝒪̂_P`-basis `b` of
`𝒪̂_{P'}`, `ord_{P̂}(discr b) = d(P' ∣ P) · f(P' ∣ P)`. -/
theorem ord_completionPlace_discr_completionIntegers {ι : Type*} [Fintype ι] [DecidableEq ι] :
    letI := P.completionIntegersExtensionAlgebra P' hP
    ∀ b : Basis ι P.completionPlace.integers P'.completionPlace.integers,
      P.completionPlace.ord (Algebra.discr P.completionPlace.integers b : P.Completion) =
        (differentExponent k F P' : ℤ) * relativeDegree k F P' := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := isIntegralClosure_completionIntegers P P' hP
  have := finiteDimensional_completion P P' hP
  have := isSeparable_completion P P' hP
  have := IsIntegralClosure.isLocalization P.completionPlace.integers P.Completion P'.Completion
    P'.completionPlace.integers
  intro b
  have hdiscr0 : Algebra.discr P.completionPlace.integers b ≠ 0 := by
    intro h
    have hz := Algebra.discr_localizationLocalization P.completionPlace.integers
      P.completionPlace.integers⁰ P'.Completion (Rₘ := P.Completion) b
    rw [h, map_zero] at hz
    exact Algebra.discr_not_zero_of_basis P.Completion
      (b.localizationLocalization P.Completion P.completionPlace.integers⁰ P'.Completion) hz
  have hord := P.ord_discr_completionIntegers P' hP b
  rw [ringOrd_integers_eq_toNat_ord P.completionPlace hdiscr0,
    ← ENat.natCast_mul, ENat.natCast_inj] at hord
  have hnn := P.completionPlace.mem_integers_iff_ord_nonneg.mp
    (Algebra.discr P.completionPlace.integers b).2
  omega

section SameConstants

variable {Q : Place k F} {Q' : Place k F'} (hQ : Q'.restrict k F = Q)

/-- **Completion preserves `differentExponent`** when the constant fields agree: viewing
`Q'.completionPlace` as a place of `Q'.Completion / k` above `Q.completionPlace`, its different
exponent over `Q.Completion` equals `d(Q' ∣ Q)`. -/
theorem differentExponent_completionPlace :
    letI := Q.completionExtensionAlgebra Q' hQ
    letI := Q.isScalarTower_completionExtensionAlgebra Q' hQ
    letI := finiteDimensional_completion Q Q' hQ
    letI := isSeparable_completion Q Q' hQ
    differentExponent k Q.Completion Q'.completionPlace = differentExponent k F Q' := by
  let _ := Q.completionExtensionAlgebra Q' hQ
  let _ := Q.completionIntegersExtensionAlgebra Q' hQ
  let _ := Q.isScalarTower_completionExtensionAlgebra Q' hQ
  have := isIntegralClosure_completionIntegers Q Q' hQ
  have := finiteDimensional_completion Q Q' hQ
  have := isSeparable_completion Q Q' hQ
  have hC : ∀ c : Q'.completionPlace.integers,
      algebraMap Q'.completionPlace.integers Q'.Completion c ∈ Q'.completionPlace.integers :=
    fun c ↦ c.2
  have hcenter : (Q'.completionPlace.center hC).asIdeal =
      maximalIdeal Q'.completionPlace.integers := by
    ext c
    rw [mem_center_asIdeal, mem_maximalIdeal_iff_valuation_lt_one]
    exact Iff.rfl
  rw [differentExponent_eq_multiplicity_center (B := Q.completionPlace.integers)
      (C := Q'.completionPlace.integers) Q'.completionPlace hC,
    hcenter, Q.multiplicity_differentIdeal_completionIntegers Q' hQ]

end SameConstants

end CompletedDifferent

/-! ### Global discriminant order and complementary-module length at a place -/

section GlobalLengthAndDiscriminant

/-- Two finite bases of the same module over a discrete valuation ring have associated
discriminants, hence the same valuation. -/
private theorem ord_discr_eq_of_basis {K₀ L₀ M : Type*} [Field K₀] [Field L₀] [Algebra K₀ L₀]
    (Q : Place K₀ L₀) [CommRing M] [Algebra Q.integers M]
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (b₁ : Basis ι₁ Q.integers M) (b₂ : Basis ι₂ Q.integers M)
    (hb₂ : (Algebra.discr Q.integers b₂ : L₀) ≠ 0) :
    Q.ord (Algebra.discr Q.integers b₁ : L₀) = Q.ord (Algebra.discr Q.integers b₂ : L₀) := by
  let e : ι₁ ≃ ι₂ := b₁.indexEquiv b₂
  let b₁' : Basis ι₂ Q.integers M := b₁.reindex e
  have hre : Algebra.discr Q.integers b₁' = Algebra.discr Q.integers b₁ := by
    simp [b₁']
  have hmul : (b₁' : ι₂ → M) = Matrix.vecMul (b₂ : ι₂ → M)
      ((b₂.toMatrix b₁').map (algebraMap Q.integers M)) := by
    ext j
    rw [Matrix.vecMul, dotProduct]
    conv_lhs => rw [← b₂.sum_repr (b₁' j)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Matrix.map_apply, Algebra.smul_def, mul_comm, Basis.toMatrix_apply]
  have hunit : IsUnit ((b₂.toMatrix b₁').det ^ 2) := (b₂.isUnit_det b₁').pow 2
  have hu0 : (((b₂.toMatrix b₁').det ^ 2 : Q.integers) : L₀) ≠ 0 := by
    simpa using hunit.ne_zero
  have hu_ord : Q.ord (((b₂.toMatrix b₁').det ^ 2 : Q.integers) : L₀) = 0 :=
    (Q.isUnit_iff_ord_eq_zero hu0).mp hunit
  have hdiscr := congrArg (Algebra.discr Q.integers) hmul
  rw [Algebra.discr_of_matrix_vecMul, hre] at hdiscr
  rw [hdiscr, MulMemClass.coe_mul, Q.ord_mul hu0 hb₂, hu_ord, zero_add]

/-- The discriminant of a product basis `Pi.basis b` of a finite product of algebras is the
product of the discriminants of the factor bases. -/
private theorem discr_pi_basis {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (b : ∀ i, Basis (κ i) R (A i)) :
    Algebra.discr R (Pi.basis b) = ∏ i, Algebra.discr R (b i) := by
  have _ (i : ι) : Module.Free R (A i) := .of_basis (b i)
  have _ (i : ι) : Module.Finite R (A i) := .of_basis (b i)
  have hmat : Algebra.traceMatrix R (Pi.basis b) =
      Matrix.blockDiagonal' fun i ↦ Algebra.traceMatrix R (b i) := by
    ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
    rcases eq_or_ne i₁ i₂ with rfl | h
    · simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Pi.basis_apply,
        Matrix.blockDiagonal'_apply_eq, ← Pi.single_mul, trace_pi_single]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h, Algebra.traceMatrix_apply,
        Algebra.traceForm_apply, Pi.basis_apply, Pi.basis_apply]
      have hzero : (Pi.single i₁ (b i₁ j₁) * Pi.single i₂ (b i₂ j₂) : ∀ i, A i) = 0 := by
        funext i
        rcases eq_or_ne i i₁ with rfl | hi₁
        · simp [Pi.single_eq_of_ne h]
        · simp [Pi.single_eq_of_ne hi₁]
      rw [hzero, map_zero]
  rw [Algebra.discr_def, hmat, Matrix.det_blockDiagonal']
  exact Finset.prod_congr rfl fun i _ ↦ (Algebra.discr_def _ _).symm

variable (k') [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [Algebra.IsIntegral k k']

/-- An `𝒪_P`-basis of `𝒪'_P` maps diagonally to an `𝒪̂_P`-basis of `∏_{P' ∣ P} 𝒪̂_{P'}`. -/
private noncomputable def semilocalIntegersBasis (P : Place k F)
    {ι : Type*} [Fintype ι]
    (c : Basis ι P.integers (integralClosure P.integers F')) :
    letI := fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
      P.completionIntegersExtensionAlgebra P'.1 P'.2
    Basis ι P.completionPlace.integers
      (∀ P' : {P' : Place k' F' // P'.restrict k F = P}, P'.1.completionPlace.integers) := by
  classical
  let ιₚ := {P' : Place k' F' // P'.restrict k F = P}
  let _ := fun P' : ιₚ ↦ P.completionExtensionAlgebra P'.1 P'.2
  let _ := fun P' : ιₚ ↦ P.completionIntegersExtensionAlgebra P'.1 P'.2
  have := isLocalization_integralClosure F' P
  let cF : Basis ι F F' := c.localizationLocalization F P.integers⁰ F'
  let v : ι → ∀ P' : ιₚ, P'.1.completionPlace.integers :=
    fun i P' ↦ P.integralClosureToCompletionIntegers P'.1 P'.2 (c i)
  have hli : LinearIndependent P.completionPlace.integers v := by
    have hliF : LinearIndependent P.Completion
        (fun (i : ι) (P' : ιₚ) ↦ P'.1.completionEmbedding (cF i)) :=
      (linearIndependent_completionEmbedding_pi_iff_of_isSeparable k' P).mpr cF.linearIndependent
    rw [linearIndependent_iff'] at hliF ⊢
    intro s g hg i hi
    refine Subtype.ext (hliF s (fun j ↦ (g j : P.Completion)) ?_ i hi)
    funext P'
    have hP' :=
      congrArg (fun f : ∀ Q : ιₚ, Q.1.completionPlace.integers ↦ (f P' : P'.1.Completion)) hg
    simpa [v, cF, Algebra.smul_def, coe_algebraMap_completionIntegersExtensionAlgebra,
      algebraMap_completionExtensionAlgebra] using hP'
  have hsp : ⊤ ≤ Submodule.span P.completionPlace.integers (Set.range v) := by
    refine (span_completionIntegers_pi_eq_top k' F' P).ge.trans (Submodule.span_le.mpr ?_)
    rintro _ ⟨y, rfl⟩
    have hy : IsIntegral P.integers y.1 :=
      (isIntegral_iff_forall_restrict_eq_mem_integers_of_isSeparable k' P).mpr
        fun P' hP' ↦ y.2 ⟨P', hP'⟩
    set y₀ : integralClosure P.integers F' := ⟨y.1, hy⟩
    have hy_eq : (fun P' : ιₚ ↦ P'.1.completionIntegersEmbedding ⟨y.1, y.2 P'⟩) =
        ∑ i, P.completionIntegersEmbedding (c.repr y₀ i) • v i := by
      funext P'
      apply Subtype.ext
      have hc_sum := congrArg P'.1.completionEmbedding
        (congrArg (algebraMap (integralClosure P.integers F') F') (c.sum_repr y₀).symm)
      rw [map_sum, map_sum] at hc_sum
      refine (completionIntegersEmbedding_apply P'.1 ⟨y.1, y.2 P'⟩).trans (hc_sum.trans ?_)
      conv_rhs => rw [Finset.sum_apply, ← ValuationSubring.algebraMap_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul, ValuationSubring.algebraMap_apply,
        coe_algebraMap_completionIntegersExtensionAlgebra, completionIntegersEmbedding_apply,
        P.completionExtension_completionEmbedding P'.1 P'.2,
        ← IsScalarTower.algebraMap_apply P.integers (integralClosure P.integers F') F',
        IsScalarTower.algebraMap_apply P.integers F F', v, coe_integralClosureToCompletionIntegers]
    dsimp only
    rw [hy_eq]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact Basis.mk hli hsp

@[simp]
private theorem semilocalIntegersBasis_apply (P : Place k F)
    {ι : Type*} [Fintype ι]
    (c : Basis ι P.integers (integralClosure P.integers F')) (i : ι)
    (P' : {P' : Place k' F' // P'.restrict k F = P}) :
    semilocalIntegersBasis k' P c i P' =
      P.integralClosureToCompletionIntegers P'.1 P'.2 (c i) := by
  simp [semilocalIntegersBasis]

/-- The discriminant of `semilocalIntegersBasis k' P c` is the image of `discr c` in `𝒪̂_P`. -/
private theorem discr_semilocalIntegersBasis (P : Place k F)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Basis ι P.integers (integralClosure P.integers F')) :
    letI := fun P' : {P' : Place k' F' // P'.restrict k F = P} ↦
      P.completionIntegersExtensionAlgebra P'.1 P'.2
    Algebra.discr P.completionPlace.integers (semilocalIntegersBasis k' P c) =
      P.completionIntegersEmbedding (Algebra.discr P.integers c) := by
  classical
  let ιₚ := {P' : Place k' F' // P'.restrict k F = P}
  let _ := fun P' : ιₚ ↦ P.completionExtensionAlgebra P'.1 P'.2
  let _ := fun P' : ιₚ ↦ P.completionIntegersExtensionAlgebra P'.1 P'.2
  have _ := fun P' : ιₚ ↦ moduleFinite_completionIntegers P P'.1 P'.2
  have _ := fun P' : ιₚ ↦ moduleFree_completionIntegers P P'.1 P'.2
  have := Fintype.ofFinite ιₚ
  have := isLocalization_integralClosure F' P
  set B := semilocalIntegersBasis k' P c
  have hmat : Algebra.traceMatrix P.completionPlace.integers B =
      (P.completionIntegersEmbedding : P.integers →+* P.completionPlace.integers).mapMatrix
        (Algebra.traceMatrix P.integers c) := by
    ext i j
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply,
      AlgHom.coe_toRingHom, completionIntegersEmbedding_apply]
    have htrF : (Algebra.trace P.integers (integralClosure P.integers F') (c i * c j) : F) =
        Algebra.trace F F' (algebraMap (integralClosure P.integers F') F' (c i * c j)) :=
      (Algebra.trace_localization P.integers P.integers⁰ (Rₘ := F) (Sₘ := F')
        (c i * c j)).symm
    have htrC : (Algebra.trace P.completionPlace.integers
          (∀ P' : ιₚ, P'.1.completionPlace.integers) (B i * B j) : P.Completion) =
        ∑ P' : ιₚ, Algebra.trace P.Completion P'.1.Completion
          (P'.1.completionEmbedding (algebraMap _ F' (c i * c j))) := by
      rw [TauCeti.Algebra.trace_pi, ← ValuationSubring.algebraMap_apply, map_sum]
      refine Finset.sum_congr rfl fun P' _ ↦ ?_
      have := isIntegralClosure_completionIntegers P P'.1 P'.2
      have := finiteDimensional_completion P P'.1 P'.2
      have := IsIntegralClosure.isLocalization P.completionPlace.integers P.Completion
        P'.1.Completion P'.1.completionPlace.integers
      simpa [B, map_mul] using (Algebra.trace_localization P.completionPlace.integers
        P.completionPlace.integers⁰ (Rₘ := P.Completion) (Sₘ := P'.1.Completion)
        ((B i * B j) P')).symm
    rw [htrC, htrF, completionEmbedding_trace_of_isSeparable k' P, finsum_eq_sum_of_fintype]
  rw [Algebra.discr_def, hmat, ← RingHom.map_det, ← Algebra.discr_def, AlgHom.coe_toRingHom]

/-- **The order at `P` of the discriminant of an `𝒪_P`-basis of `𝒪'_P`** is
`∑_{P' ∣ P} d(P' ∣ P) · f(P' ∣ P)`, counting each place above `P` with its full residue degree
(including any inseparable factor). -/
theorem ord_discr_integralClosure_basis (P : Place k F) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Basis ι P.integers (integralClosure P.integers F')) :
    P.ord (Algebra.discr P.integers c : F) =
      ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (differentExponent k F P'.1 : ℤ) * relativeDegree k F P'.1 := by
  classical
  let ιₚ := {P' : Place k' F' // P'.restrict k F = P}
  let _ := fun P' : ιₚ ↦ P.completionExtensionAlgebra P'.1 P'.2
  let _ := fun P' : ιₚ ↦ P.completionIntegersExtensionAlgebra P'.1 P'.2
  have _ := fun P' : ιₚ ↦ moduleFinite_completionIntegers P P'.1 P'.2
  have _ := fun P' : ιₚ ↦ moduleFree_completionIntegers P P'.1 P'.2
  have := Fintype.ofFinite ιₚ
  let B := semilocalIntegersBasis k' P c
  have hB := discr_semilocalIntegersBasis k' P c
  let b (P' : ιₚ) := Module.finBasis P.completionPlace.integers P'.1.completionPlace.integers
  have hb_ne (P' : ιₚ) : (Algebra.discr P.completionPlace.integers (b P') : P.Completion) ≠ 0 := by
    have := isIntegralClosure_completionIntegers P P'.1 P'.2
    have := finiteDimensional_completion P P'.1 P'.2
    have := isSeparable_completion P P'.1 P'.2
    have := IsIntegralClosure.isLocalization P.completionPlace.integers P.Completion
      P'.1.Completion P'.1.completionPlace.integers
    intro h
    have hz := Algebra.discr_localizationLocalization P.completionPlace.integers
      P.completionPlace.integers⁰ P'.1.Completion (Rₘ := P.Completion) (b P')
    rw [ValuationSubring.algebraMap_apply, h] at hz
    exact Algebra.discr_not_zero_of_basis P.Completion
      ((b P').localizationLocalization P.Completion P.completionPlace.integers⁰ P'.1.Completion) hz
  have hprod_coe : ((∏ P' : ιₚ, Algebra.discr P.completionPlace.integers (b P') :
      P.completionPlace.integers) : P.Completion) =
      ∏ P' : ιₚ, (Algebra.discr P.completionPlace.integers (b P') : P.Completion) :=
    map_prod (algebraMap P.completionPlace.integers P.Completion) _ _
  have hprod_ne : (Algebra.discr P.completionPlace.integers (Pi.basis b) : P.Completion) ≠ 0 := by
    rw [discr_pi_basis, hprod_coe]
    exact Finset.prod_ne_zero_iff.mpr fun P' _ ↦ hb_ne P'
  have hordB := ord_discr_eq_of_basis P.completionPlace B (Pi.basis b) hprod_ne
  rw [hB, completionIntegersEmbedding_apply, ord_completionEmbedding, discr_pi_basis,
    hprod_coe, P.completionPlace.ord_prod Finset.univ fun P' _ ↦ hb_ne P'] at hordB
  rw [hordB, finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun P' _ ↦
    P.ord_completionPlace_discr_completionIntegers P'.1 P'.2 (b P')

/-- **The order at `P` of the discriminant of any integral basis at `P`** equals
`∑_{P' ∣ P} d(P' ∣ P) · f(P' ∣ P)`, with no separability hypothesis on the residue extensions. -/
theorem ord_discr_of_isIntegralBasis (P : Place k F) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {b : Basis ι F F'} (hb : P.IsIntegralBasis F' b) :
    P.ord (Algebra.discr F b) =
      ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (differentExponent k F P'.1 : ℤ) * relativeDegree k F P'.1 := by
  have hli : LinearIndependent P.integers
      (fun i ↦ (⟨b i, IsIntegralBasis.isIntegral F' P hb i⟩ : integralClosure P.integers F')) := by
    have h := b.linearIndependent
    rw [linearIndependent_iff'] at h ⊢
    intro s g hg i hi
    refine Subtype.ext (h s (fun j ↦ (g j : F)) ?_ i hi)
    have hF := congrArg (algebraMap (integralClosure P.integers F') F') hg
    simpa [Algebra.smul_def, IsScalarTower.algebraMap_apply P.integers F F'] using hF
  have hsp : ⊤ ≤ Submodule.span P.integers
      (Set.range fun i ↦
        (⟨b i, IsIntegralBasis.isIntegral F' P hb i⟩ : integralClosure P.integers F')) := by
    intro y _
    have hy : (y : F') ∈ Submodule.span P.integers (Set.range b) :=
      (IsIntegralBasis.mem_span_iff_isIntegral F' P hb).mpr y.2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy
    have hy' : y = ∑ i, c i •
        (⟨b i, IsIntegralBasis.isIntegral F' P hb i⟩ : integralClosure P.integers F') := by
      apply Subtype.ext
      calc (y : F') = ∑ i, c i • b i := hc.symm
        _ = (integralClosure P.integers F').val
              (∑ i, c i • ⟨b i, IsIntegralBasis.isIntegral F' P hb i⟩) := by
            simp only [map_sum, map_smul]; rfl
    rw [hy']
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let c : Basis ι P.integers (integralClosure P.integers F') := Basis.mk hli hsp
  have := isLocalization_integralClosure F' P
  have hcF : c.localizationLocalization F P.integers⁰ F' = b := by
    ext i
    simp [c]
  have hdiscr : (Algebra.discr P.integers c : F) = Algebra.discr F b := by
    simpa only [ValuationSubring.algebraMap_apply, hcF] using
      (Algebra.discr_localizationLocalization P.integers P.integers⁰ F' (Rₘ := F) c).symm
  rw [← hdiscr, ord_discr_integralClosure_basis k' P c]

/-- **Length of the pre-completion complementary-module quotient**: over `𝒪_P`, the quotient
`C_P ⧸ 𝒪'_P` has length `∑_{P' ∣ P} d(P' ∣ P) · f(P' ∣ P)`, counting each place above `P` with its
full residue degree. -/
theorem length_traceDual_quotient_integralClosure (P : Place k F) :
    Module.length P.integers
        ((Submodule.traceDual P.integers F
            (1 : Submodule (integralClosure P.integers F') F')) ⧸
          (1 : Submodule (integralClosure P.integers F') F').comap
            (Submodule.traceDual P.integers F
              (1 : Submodule (integralClosure P.integers F') F')).subtype) =
      ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        ((differentExponent k F P'.1 : ℕ∞) * relativeDegree k F P'.1) := by
  classical
  have := isLocalization_integralClosure F' P
  let c := integralClosureFinBasis F' P
  have hdiscr0 : Algebra.discr P.integers c ≠ 0 := by
    intro h
    have hz := Algebra.discr_localizationLocalization P.integers P.integers⁰ F' (Rₘ := F) c
    rw [h, map_zero] at hz
    exact Algebra.discr_not_zero_of_basis F (c.localizationLocalization F P.integers⁰ F') hz
  rw [c.length_traceDual_quotient_eq_length_quotient_range_algebraToTraceDual,
    c.length_traceDual_quotient_eq_ord_discr, ringOrd_integers_eq_toNat_ord P hdiscr0,
    ord_discr_integralClosure_basis k' P c]
  have := Fintype.ofFinite {P' : Place k' F' // P'.restrict k F = P}
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have hsum : ∑ x : {P' : Place k' F' // P'.restrict k F = P},
      (differentExponent k F x.1 : ℤ) * relativeDegree k F x.1 =
      ((∑ x : {P' : Place k' F' // P'.restrict k F = P},
        differentExponent k F x.1 * relativeDegree k F x.1 : ℕ) : ℤ) := by
    push_cast
    rfl
  rw [hsum, Int.toNat_natCast]
  push_cast
  rfl

/-- **The pre-completion complementary-module quotient length is the sum of the completed
complementary-module quotient lengths above `P`.** -/
theorem length_traceDual_quotient_eq_finsum_completion (P : Place k F) :
    Module.length P.integers
        ((Submodule.traceDual P.integers F
            (1 : Submodule (integralClosure P.integers F') F')) ⧸
          (1 : Submodule (integralClosure P.integers F') F').comap
            (Submodule.traceDual P.integers F
              (1 : Submodule (integralClosure P.integers F') F')).subtype) =
      ∑ᶠ P' : {P' : Place k' F' // P'.restrict k F = P},
        (letI := P.completionExtensionAlgebra P'.1 P'.2
        letI := P.completionIntegersExtensionAlgebra P'.1 P'.2
        Module.length P.completionPlace.integers
          ((Submodule.traceDual P.completionPlace.integers P.Completion
              (1 : Submodule P'.1.completionPlace.integers P'.1.Completion)) ⧸
            (1 : Submodule P'.1.completionPlace.integers P'.1.Completion).comap
              (Submodule.traceDual P.completionPlace.integers P.Completion
                (1 : Submodule P'.1.completionPlace.integers P'.1.Completion)).subtype)) := by
  rw [length_traceDual_quotient_integralClosure k' P]
  exact finsum_congr fun P' ↦
    (P.length_traceDual_quotient_completionIntegers P'.1 P'.2).symm

end GlobalLengthAndDiscriminant

end TauCeti.Place

end
