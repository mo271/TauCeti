/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MatlisDuality.Finite
import Mathlib.RingTheory.Filtration
import TauCeti.Algebra.Module.Injective.Hom
import TauCeti.Algebra.Module.Torsion.Artinian

/-!
# Matlis duality for Artinian modules and over the adic completion

Let `R` be a Noetherian local ring with maximal ideal `𝔪`, completion
`R̂ = AdicCompletion 𝔪 R`, and an injective envelope `ι : κ → E` of its residue field. This
file completes module-level Matlis duality in both settings:

1. **Over a complete Noetherian local ring** (Stacks Proposition 47.7.8, Tag 08Z9): the Matlis
   dual `Hom_R(M, E)` of an Artinian module `M` is finitely generated, evaluation
   `M → Hom_R(Hom_R(M, E), E)` is a linear equivalence (`evalEquivOfIsArtinian`), and `M` is
   Artinian (resp. finitely generated) if and only if its Matlis dual is finitely generated
   (resp. Artinian).
2. **Injective hull over the completion** (Stacks Lemma 47.7.6, Tag 08Z7): without assuming `R`
   complete, `E` equipped with its canonical `R̂`-action is an injective envelope of the residue
   field of `R̂` (`isInjectiveEnvelope_adicCompletion`). Injectivity over `R̂` is proved by Baer's
   criterion and the Artin–Rees lemma, factoring maps out of ideals `J ⊆ R̂` through
   finite-length quotients `R̂ ⧸ 𝔪̂ᵐ` where `R`-injectivity of `E` and uniqueness of the torsion
   `R̂`-action apply.
3. **Matlis duality over a general Noetherian local ring** (Stacks Remark 47.7.9, Tag 0EGL):
   applying the complete-ring theorems to `E` over `R̂` and transporting along restriction of
   scalars on `𝔪`-power-torsion modules shows that `Hom_R(-, E)` and `Hom_{R̂}(-, E)` exchange
   Artinian `R`-modules and finitely generated `R̂`-modules, with evaluation isomorphisms on both
   sides (`evalAdicCompletionEquivOfIsArtinian`, `evalLinearMapAdicCompletionEquivOfFinite`).
   For a finitely generated `R`-module `N`, combining with the completion adjunction
   `Hom_{R̂}(N̂, E) ≅ Hom_R(N, E)` yields the double-dual completion isomorphism
   `N̂ ≃ₗ[R̂] Hom_R(Hom_R(N, E), E)` (`adicCompletionEquivDoubleDual`).

## Main definitions and results

* `TauCeti.IsInjectiveEnvelope.evalEquivOfIsArtinian`: `M ≃ₗ[R] Hom_R(Hom_R(M, E), E)` for
  Artinian modules over a complete Noetherian local ring, with `isArtinian_iff_finite_linearMap`
  and `finite_iff_isArtinian_linearMap`.
* `TauCeti.IsInjectiveEnvelope.moduleInjective_adicCompletion` and
  `TauCeti.IsInjectiveEnvelope.isInjectiveEnvelope_adicCompletion`: `E` is an injective envelope
  of the residue field of `R̂` over `R̂`.
* `TauCeti.IsInjectiveEnvelope.evalAdicCompletionEquivOfIsArtinian` and
  `TauCeti.IsInjectiveEnvelope.evalLinearMapAdicCompletionEquivOfFinite`: biduality between
  Artinian `R`-modules and finitely generated `R̂`-modules over a general Noetherian local ring,
  with `isArtinian_iff_finite_adicCompletion_linearMap` and
  `finite_iff_isArtinian_adicCompletionLinearMap`.
* `TauCeti.IsInjectiveEnvelope.adicCompletionEquivDoubleDual`: the `R̂`-linear isomorphism
  `AdicCompletion (maximalIdeal R) N ≃ₗ[R̂] ((N →ₗ[R] E) →ₗ[R] E)` for finite `N`.

## References

* The Stacks Project, Section 47.7, Matlis duality (Tag 08Z1): Lemma 47.7.6 (08Z7),
  Proposition 47.7.8 (08Z9), and Remark 47.7.9 (0EGL).
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

noncomputable section

universe u v w

namespace TauCeti.IsInjectiveEnvelope

open IsLocalRing LinearMap

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {E : Type v} [AddCommGroup E] [Module R E] [Small.{v} R]
  {ι : ResidueField R →ₗ[R] E} (hι : IsInjectiveEnvelope ι)

section Complete

variable [IsAdicComplete (maximalIdeal R) R]

include hι

/-- Over a complete Noetherian local ring, the Matlis dual of an Artinian module is finitely
generated. -/
@[stacks 08Z9 "dual of an Artinian module is finite"]
theorem finite_linearMap_of_isArtinian (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R M] : Module.Finite R (M →ₗ[R] E) := by
  have := hι.moduleInjective
  have hEnd : Module.Finite R (E →ₗ[R] E) := by
    refine Module.Finite.of_surjective
      (LinearMap.toSpanSingleton R (Module.End R E) LinearMap.id) fun φ ↦ ?_
    obtain ⟨r, rfl⟩ := hι.exists_eq_smul_id φ
    exact ⟨r, rfl⟩
  refine TauCeti.finite_linearMap_of_isArtinian fun m hm ↦ ?_
  by_contra! h
  exact hm ((injective_iff_map_eq_zero _).mp (injective_applyₗ_of_injective hι.injective) m
    (LinearMap.ext h))

/-- Over a complete Noetherian local ring, a module is Artinian if and only if its Matlis dual is
finitely generated. -/
@[stacks 08Z9 "Artinian iff finite dual"]
theorem isArtinian_iff_finite_linearMap (M : Type w) [AddCommGroup M] [Module R M] :
    IsArtinian R M ↔ Module.Finite R (M →ₗ[R] E) := by
  have := hι.moduleInjective
  exact ⟨fun _ ↦ hι.finite_linearMap_of_isArtinian M,
    fun _ ↦ isArtinian_of_isNoetherian_linearMap R hι.injective⟩

/-- Over a complete Noetherian local ring, a module whose Matlis dual is Artinian is finitely
generated. -/
theorem finite_of_isArtinian_linearMap (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R (M →ₗ[R] E)] : Module.Finite R M := by
  have := hι.moduleInjective
  have := hι.finite_linearMap_of_isArtinian (M →ₗ[R] E)
  exact Module.Finite.of_injective applyₗ (injective_applyₗ_of_injective hι.injective)

/-- Over a complete Noetherian local ring, a module is finitely generated if and only if its
Matlis dual is Artinian. -/
@[stacks 08Z9 "finite iff Artinian dual"]
theorem finite_iff_isArtinian_linearMap (M : Type w) [AddCommGroup M] [Module R M] :
    Module.Finite R M ↔ IsArtinian R (M →ₗ[R] E) :=
  ⟨fun _ ↦ hι.isArtinian_linearMap_of_finite M,
    fun _ ↦ hι.finite_of_isArtinian_linearMap M⟩

/-- **Matlis biduality for Artinian modules** over a complete Noetherian local ring: the canonical
evaluation map into the double Matlis dual is bijective. -/
@[stacks 08Z9 "biduality for Artinian modules"]
theorem bijective_applyₗ_of_isArtinian (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R M] :
    Function.Bijective (applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E) := by
  have := hι.moduleInjective
  have := hι.isArtinian
  exact ⟨injective_applyₗ_of_injective hι.injective,
    surjective_applyₗ_of_isArtinian_of_end_eq_smul
      (fun {_ _ _} ↦ injective_applyₗ_of_injective hι.injective) hι.exists_eq_smul_id
      (injective_applyₗ_of_injective hι.injective)⟩

/-- Evaluation identifies an Artinian module over a complete Noetherian local ring with its
double Matlis dual. -/
@[stacks 08Z9 "biduality for Artinian modules"]
def evalEquivOfIsArtinian (M : Type w) [AddCommGroup M] [Module R M] [IsArtinian R M] :
    M ≃ₗ[R] ((M →ₗ[R] E) →ₗ[R] E) :=
  LinearEquiv.ofBijective applyₗ (hι.bijective_applyₗ_of_isArtinian M)

@[simp]
theorem evalEquivOfIsArtinian_apply_apply (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R M] (m : M) (f : M →ₗ[R] E) :
    hι.evalEquivOfIsArtinian M m f = f m := (rfl)

@[simp]
theorem evalEquivOfIsArtinian_symm_apply_apply (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R M] (φ : (M →ₗ[R] E) →ₗ[R] E) (f : M →ₗ[R] E) :
    f ((hι.evalEquivOfIsArtinian M).symm φ) = φ f := by
  simpa only [evalEquivOfIsArtinian_apply_apply] using
    congrArg (fun ψ : (M →ₗ[R] E) →ₗ[R] E ↦ ψ f)
      ((hι.evalEquivOfIsArtinian M).apply_symm_apply φ)

end Complete

section HullOverCompletion

omit [AddCommGroup E] [Module R E] [Small.{v} R] in
/-- The canonical isomorphism between the residue field of `R` and that of its completion, as an
`R`-algebra equivalence. -/
def residueFieldAdicCompletionAlgEquiv :
    ResidueField R ≃ₐ[R] ResidueField (_root_.AdicCompletion (maximalIdeal R) R) :=
  AlgEquiv.ofBijective
    { IsLocalRing.ResidueField.map (algebraMap R (_root_.AdicCompletion (maximalIdeal R) R)) with
      commutes' := fun r ↦ IsLocalRing.ResidueField.map_residue
        (algebraMap R (_root_.AdicCompletion (maximalIdeal R) R)) r }
    (_root_.AdicCompletion.residueField_map_bijective R)

omit [AddCommGroup E] [Module R E] [Small.{v} R] in
@[simp]
theorem residueFieldAdicCompletionAlgEquiv_residue (r : R) :
    residueFieldAdicCompletionAlgEquiv (residue R r) =
      residue (_root_.AdicCompletion (maximalIdeal R) R)
        (algebraMap R (_root_.AdicCompletion (maximalIdeal R) R) r) :=
  IsLocalRing.ResidueField.map_residue _ r

omit [AddCommGroup E] [Module R E] [Small.{v} R] in
@[simp]
theorem residueFieldAdicCompletionAlgEquiv_symm_residue (r : R) :
    (residueFieldAdicCompletionAlgEquiv (R := R)).symm
      (residue (_root_.AdicCompletion (maximalIdeal R) R)
        (algebraMap R (_root_.AdicCompletion (maximalIdeal R) R) r)) =
      residue R r := by
  rw [← residueFieldAdicCompletionAlgEquiv_residue, AlgEquiv.symm_apply_apply]

include hι

omit [Small.{v} R] in
/-- Every element of `E` is killed by a power of the maximal ideal of the completion `R̂`. -/
theorem mem_primaryComponent_maximalIdeal_adicCompletion (x : E) :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    x ∈ (maximalIdeal (_root_.AdicCompletion (maximalIdeal R) R)).primaryComponent E := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  rw [_root_.AdicCompletion.maximalIdeal_eq_map]
  exact AdicCompletion.mem_primaryComponent_map_of_torsionModule hι.mem_primaryComponent x

/-- **An injective hull of the residue field is injective over the completion.** By Baer's
criterion and the Artin–Rees lemma, any `R̂`-linear map `J → E` from an ideal `J ⊆ R̂` vanishes
on `J ⊓ 𝔪̂ᵐ` for large `m`, hence factors over `R` through `R̂ ⧸ 𝔪̂ᵐ` by `R`-injectivity of
`E`, and that factorisation is automatically `R̂`-linear by uniqueness of the torsion
`R̂`-action. -/
@[stacks 08Z7 "injectivity over the completion"]
theorem moduleInjective_adicCompletion :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    Module.Injective (_root_.AdicCompletion (maximalIdeal R) R) E := by
  let S := _root_.AdicCompletion (maximalIdeal R) R
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  have := hι.moduleInjective
  refine Module.Baer.injective fun J g ↦ ?_
  obtain ⟨k, hk⟩ := Ideal.exists_forall_mem_torsionBySet_pow_of_mem_primaryComponent
    (maximalIdeal S) g (fun x ↦ hι.mem_primaryComponent_maximalIdeal_adicCompletion (g x))
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal S) J
  let m := k + c
  let K : Ideal S := maximalIdeal S ^ k • (maximalIdeal S ^ c ⊓ J)
  have hKJ : K ≤ J := Submodule.smul_le.mpr fun r _ y hy ↦ J.mul_mem_left r hy.2
  have hgK : ∀ z (hz : z ∈ K), g ⟨z, hKJ hz⟩ = 0 := fun z hz ↦ by
    induction hz using Submodule.smul_induction_on' with
    | smul r hr y hy =>
      have hsub : (⟨r • y, hKJ (Submodule.smul_mem_smul hr hy)⟩ : J) =
          r • ⟨y, hy.2⟩ := rfl
      rw [hsub, g.map_smul]
      exact (Submodule.mem_torsionBySet_iff _ _).mp (hk ⟨y, hy.2⟩) ⟨r, hr⟩
    | add u hu v hv ihu ihv =>
      have hadd : (⟨u + v, hKJ (add_mem hu hv)⟩ : J) = ⟨u, hKJ hu⟩ + ⟨v, hKJ hv⟩ := rfl
      rw [hadd, map_add, ihu, ihv, add_zero]
  have hm : maximalIdeal S ^ m ⊓ J = K := by
    have hcm := hc m (Nat.le_add_left c k)
    simpa only [m, K, Nat.add_sub_cancel_right, smul_eq_mul, Ideal.mul_top] using hcm
  let π : S →ₗ[S] S ⧸ maximalIdeal S ^ m := (maximalIdeal S ^ m).mkQ
  have hker : LinearMap.ker ((π.comp J.subtype).restrictScalars R) ≤
      LinearMap.ker (g.restrictScalars R) := by
    intro x hx
    have hx' : (x : S) ∈ maximalIdeal S ^ m ⊓ J := by
      refine ⟨?_, x.2⟩
      simpa [π, Submodule.mkQ_apply, Ideal.Quotient.eq_zero_iff_mem] using hx
    have hxK : (x : S) ∈ K := hm ▸ hx'
    exact hgK x.1 hxK
  obtain ⟨h₀, hh₀⟩ := (LinearMap.exists_comp_eq_iff_ker_le _ _).mpr hker
  have hQ' : ∀ q : S ⧸ maximalIdeal S ^ m,
      q ∈ ((maximalIdeal R).map (algebraMap R S)).primaryComponent
        (S ⧸ maximalIdeal S ^ m) := by
    intro q
    rw [← _root_.AdicCompletion.maximalIdeal_eq_map,
      (maximalIdeal S).primaryComponent_quotient_pow_eq_top m]
    exact Submodule.mem_top
  let h₁ : (S ⧸ maximalIdeal S ^ m) →ₗ[S] E :=
    (AdicCompletion.torsionRestrictScalarsLinearEquivOfMap
      (maximalIdeal R).fg_of_isNoetherianRing hQ' hι.mem_primaryComponent).symm h₀
  refine ⟨h₁.comp π, fun r hr ↦ ?_⟩
  have hval := LinearMap.congr_fun hh₀ ⟨r, hr⟩
  simpa [S, h₁, π] using hval

omit [Small.{v} R] in
/-- The embedding of the residue field of `R̂` into `E`, obtained by transporting `ι` along
`residueFieldAdicCompletionAlgEquiv` and promoting the resulting `R`-linear map to an `R̂`-linear
map. -/
def adicCompletionResidueFieldMap :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    ResidueField (_root_.AdicCompletion (maximalIdeal R) R) →ₗ[
      _root_.AdicCompletion (maximalIdeal R) R] E :=
  let S := _root_.AdicCompletion (maximalIdeal R) R
  have hκ : ∀ x : ResidueField S,
      x ∈ ((maximalIdeal R).map (algebraMap R S)).primaryComponent
        (ResidueField S) := fun x ↦ by
    rw [← _root_.AdicCompletion.maximalIdeal_eq_map]
    refine ((maximalIdeal S).primaryComponent_mem (ResidueField S) x).mpr ⟨1, ?_⟩
    rw [pow_one, Submodule.mem_torsionBySet_iff]
    rintro ⟨a, ha⟩
    simpa [Algebra.smul_def] using Or.inl ((mem_maximalIdeal _).mp ha)
  (AdicCompletion.torsionRestrictScalarsLinearEquivOfMap
    (maximalIdeal R).fg_of_isNoetherianRing hκ hι.mem_primaryComponent).symm
    (ι.comp (residueFieldAdicCompletionAlgEquiv (R := R)).symm.toLinearMap)

omit [Small.{v} R] in
@[simp]
theorem adicCompletionResidueFieldMap_apply
    (x : ResidueField (_root_.AdicCompletion (maximalIdeal R) R)) :
    hι.adicCompletionResidueFieldMap x =
      ι ((residueFieldAdicCompletionAlgEquiv (R := R)).symm x) :=
  AdicCompletion.torsionRestrictScalarsLinearEquivOfMap_symm_apply _ _ _ _ x

omit [Small.{v} R] in
theorem adicCompletionResidueFieldMap_residue (r : R) :
    hι.adicCompletionResidueFieldMap
      (residue (_root_.AdicCompletion (maximalIdeal R) R)
        (algebraMap R (_root_.AdicCompletion (maximalIdeal R) R) r)) =
      ι (residue R r) := by
  simp

/-- **An injective hull of the residue field over `R` is an injective hull of the residue field
over `R̂`.** -/
@[stacks 08Z7]
theorem isInjectiveEnvelope_adicCompletion :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    IsInjectiveEnvelope hι.adicCompletionResidueFieldMap := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  refine ⟨hι.moduleInjective_adicCompletion, fun x y hxy ↦
    (residueFieldAdicCompletionAlgEquiv (R := R)).symm.injective
      (hι.injective (by simpa only [adicCompletionResidueFieldMap_apply] using hxy)), ?_⟩
  rw [isEssential_iff]
  intro K hK
  have hrange : (LinearMap.range hι.adicCompletionResidueFieldMap).restrictScalars R =
      LinearMap.range ι := by
    ext x
    simp only [Submodule.restrictScalars_mem, LinearMap.mem_range,
      adicCompletionResidueFieldMap_apply]
    exact ⟨fun ⟨y, hy⟩ ↦ ⟨_, hy⟩,
      fun ⟨y, hy⟩ ↦ ⟨residueFieldAdicCompletionAlgEquiv y, by simpa using hy⟩⟩
  have hK' : LinearMap.range ι ⊓ K.restrictScalars R = ⊥ := by
    rw [← hrange, ← Submodule.restrictScalars_inf, hK, Submodule.restrictScalars_bot]
  apply (AdicCompletion.torsionSubmoduleOrderIso hι.mem_primaryComponent).injective
  simpa only [AdicCompletion.torsionSubmoduleOrderIso_apply, Submodule.restrictScalars_bot] using
    isEssential_iff.mp hι.isEssential_range (K.restrictScalars R) hK'

end HullOverCompletion

section General

include hι

/-- Over any Noetherian local ring, the Matlis dual of an Artinian `R`-module is finitely
generated over the completion `R̂`. -/
@[stacks 0EGL "dual of an Artinian module is finite over the completion"]
theorem finite_adicCompletion_linearMap_of_isArtinian (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R M] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) (M →ₗ[R] E) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  let hM := mem_primaryComponent_maximalIdeal_of_isArtinian (R := R) (M := M)
  let := AdicCompletion.torsionModule hM
  have : IsArtinian (_root_.AdicCompletion (maximalIdeal R) R) M :=
    (AdicCompletion.torsionModule_isArtinian_iff hM).mpr inferInstance
  have := hι.isInjectiveEnvelope_adicCompletion.finite_linearMap_of_isArtinian M
  exact Module.Finite.equiv (AdicCompletion.torsionRestrictScalarsLinearEquiv hM
    hι.mem_primaryComponent)

/-- Over a Noetherian local ring, an `R`-module is Artinian if and only if its Matlis dual is
finitely generated over the completion `R̂`. -/
@[stacks 0EGL "Artinian iff dual is finite over the completion"]
theorem isArtinian_iff_finite_adicCompletion_linearMap (M : Type w) [AddCommGroup M] [Module R M] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    IsArtinian R M ↔ Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) (M →ₗ[R] E) :=
  ⟨fun _ ↦ hι.finite_adicCompletion_linearMap_of_isArtinian M,
    hι.isArtinian_of_finite_adicCompletion_linearMap⟩

omit [Small.{v} R] in
/-- The canonical evaluation map `M → Hom_{R̂}(Hom_R(M, E), E)` into the completion-linear Matlis
double dual. -/
def evalAdicCompletionₗ (M : Type w) [AddCommGroup M] [Module R M] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    haveI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
    M →ₗ[R] ((M →ₗ[R] E) →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  exact
    { LinearMap.applyₗ' (_root_.AdicCompletion (maximalIdeal R) R) with
      map_smul' := fun r m ↦ LinearMap.ext fun f ↦ f.map_smul r m }

omit [Small.{v} R] in
@[simp]
theorem evalAdicCompletionₗ_apply_apply (M : Type w) [AddCommGroup M] [Module R M] (m : M)
    (f : M →ₗ[R] E) :
    hι.evalAdicCompletionₗ M m f = f m := (rfl)

/-- **Matlis biduality for Artinian modules** over a general Noetherian local ring: evaluation
`M → Hom_{R̂}(Hom_R(M, E), E)` is bijective. -/
@[stacks 0EGL "biduality for Artinian modules over a local ring"]
theorem bijective_evalAdicCompletionₗ_of_isArtinian (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R M] :
    Function.Bijective (hι.evalAdicCompletionₗ M) := by
  let S := _root_.AdicCompletion (maximalIdeal R) R
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  let hM := mem_primaryComponent_maximalIdeal_of_isArtinian (R := R) (M := M)
  let := AdicCompletion.torsionModule hM
  have : IsArtinian S M := (AdicCompletion.torsionModule_isArtinian_iff hM).mpr inferInstance
  let eDual : (M →ₗ[S] E) ≃ₗ[S] (M →ₗ[R] E) :=
    AdicCompletion.torsionRestrictScalarsLinearEquiv hM hι.mem_primaryComponent
  let eHom : ((M →ₗ[S] E) →ₗ[S] E) ≃ₗ[S] ((M →ₗ[R] E) →ₗ[S] E) :=
    LinearEquiv.ofLinearMap (eDual.symm.toLinearMap.lcomp S E) (eDual.toLinearMap.lcomp S E)
      (by ext; simp [S, eDual]) (by ext; simp [S, eDual])
  let e : M ≃ₗ[S] ((M →ₗ[R] E) →ₗ[S] E) :=
    (hι.isInjectiveEnvelope_adicCompletion.evalEquivOfIsArtinian M).trans eHom
  have heq : (hι.evalAdicCompletionₗ M : M → ((M →ₗ[R] E) →ₗ[S] E)) = e := by
    ext m f
    simp [S, e, eHom, eDual]
  rw [heq]
  exact e.bijective

/-- Evaluation identifies an Artinian `R`-module over a Noetherian local ring with the `R̂`-linear
Matlis dual of its `R`-linear Matlis dual. -/
@[stacks 0EGL "biduality for Artinian modules over a local ring"]
def evalAdicCompletionEquivOfIsArtinian (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R M] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    haveI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
    M ≃ₗ[R] ((M →ₗ[R] E) →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  haveI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  LinearEquiv.ofBijective (hι.evalAdicCompletionₗ M)
    (hι.bijective_evalAdicCompletionₗ_of_isArtinian M)

@[simp]
theorem evalAdicCompletionEquivOfIsArtinian_apply_apply (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R M] (m : M) (f : M →ₗ[R] E) :
    hι.evalAdicCompletionEquivOfIsArtinian M m f = f m := (rfl)

@[simp]
theorem evalAdicCompletionEquivOfIsArtinian_symm_apply_apply (M : Type w) [AddCommGroup M]
    [Module R M] [IsArtinian R M]
    (φ : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
         (M →ₗ[R] E) →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E)
    (f : M →ₗ[R] E) :
    f ((hι.evalAdicCompletionEquivOfIsArtinian M).symm φ) = φ f := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  simpa only [evalAdicCompletionEquivOfIsArtinian_apply_apply] using
    congrArg (fun ψ : (M →ₗ[R] E) →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E ↦ ψ f)
      ((hι.evalAdicCompletionEquivOfIsArtinian M).apply_symm_apply φ)

omit [Small.{v} R] in
/-- For a finitely generated `R̂`-module `N`, every `R̂`-linear map `N → E` is killed by a power
of `(maximalIdeal R).map (algebraMap R R̂)`. -/
private theorem mem_primaryComponent_map_adicCompletionLinearMap (N : Type w) [AddCommGroup N]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) N]
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    ∀ f : N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E,
      f ∈ ((maximalIdeal R).map
        (algebraMap R (_root_.AdicCompletion (maximalIdeal R) R))).primaryComponent
        (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) := by
  let S := _root_.AdicCompletion (maximalIdeal R) R
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  intro f
  rw [← _root_.AdicCompletion.maximalIdeal_eq_map]
  obtain ⟨k, hk⟩ := Ideal.exists_forall_mem_torsionBySet_pow_of_mem_primaryComponent
    (maximalIdeal S) f (fun x ↦ hι.mem_primaryComponent_maximalIdeal_adicCompletion (f x))
  refine ((maximalIdeal S).primaryComponent_mem _ f).mpr ⟨k, ?_⟩
  rw [Submodule.mem_torsionBySet_iff]
  rintro ⟨a, ha⟩
  ext x
  exact (Submodule.mem_torsionBySet_iff _ _).mp (hk x) ⟨a, ha⟩

/-- For a finitely generated module `N` over the completion `R̂`, the `R̂`-linear Matlis dual
`Hom_{R̂}(N, E)` is an Artinian `R`-module. -/
@[stacks 0EGL "completion dual of a finite module is Artinian"]
theorem isArtinian_adicCompletionLinearMap_of_finite (N : Type w) [AddCommGroup N]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) N]
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    haveI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
    IsArtinian R (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) := by
  let S := _root_.AdicCompletion (maximalIdeal R) R
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  have : IsArtinian S (N →ₗ[S] E) :=
    hι.isInjectiveEnvelope_adicCompletion.isArtinian_linearMap_of_finite N
  exact (AdicCompletion.isArtinian_iff_of_mem_primaryComponent_map
    (maximalIdeal R).fg_of_isNoetherianRing
    (hι.mem_primaryComponent_map_adicCompletionLinearMap N)).mp inferInstance

/-- An `R̂`-module whose `R̂`-linear Matlis dual is Artinian over `R` is finitely generated over
`R̂`. -/
theorem finite_of_isArtinian_adicCompletionLinearMap (N : Type w) [AddCommGroup N]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) N]
    (hN : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
          haveI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
          IsArtinian R (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E)) :
    Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N := by
  let S := _root_.AdicCompletion (maximalIdeal R) R
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  have : IsArtinian R (N →ₗ[S] E) := hN
  have hmap : ∀ f : N →ₗ[S] E,
      f ∈ ((maximalIdeal R).map (algebraMap R S)).primaryComponent (N →ₗ[S] E) := fun f ↦
    AdicCompletion.mem_primaryComponent_map (mem_primaryComponent_maximalIdeal_of_isArtinian f)
  have : IsArtinian S (N →ₗ[S] E) :=
    (AdicCompletion.isArtinian_iff_of_mem_primaryComponent_map
      (maximalIdeal R).fg_of_isNoetherianRing hmap).mpr hN
  exact hι.isInjectiveEnvelope_adicCompletion.finite_of_isArtinian_linearMap N

/-- Over a Noetherian local ring, an `R̂`-module is finitely generated if and only if its
`R̂`-linear Matlis dual into `E` is Artinian over `R`. -/
@[stacks 0EGL "finite over completion iff Artinian dual"]
theorem finite_iff_isArtinian_adicCompletionLinearMap (N : Type w) [AddCommGroup N]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) N] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    haveI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
    Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N ↔
      IsArtinian R (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) :=
  ⟨fun _ ↦ hι.isArtinian_adicCompletionLinearMap_of_finite N,
    hι.finite_of_isArtinian_adicCompletionLinearMap N⟩

omit [Small.{v} R] in
/-- The canonical evaluation map `N → Hom_R(Hom_{R̂}(N, E), E)` for an `R̂`-module `N`. -/
def evalLinearMapAdicCompletionₗ (N : Type w) [AddCommGroup N]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) N] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    haveI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
    N →ₗ[_root_.AdicCompletion (maximalIdeal R) R]
      ((N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) →ₗ[R] E) := by
  let S := _root_.AdicCompletion (maximalIdeal R) R
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  exact (LinearMap.restrictScalarsₗ R S (N →ₗ[S] E) E S).comp LinearMap.applyₗ

omit [Small.{v} R] in
@[simp]
theorem evalLinearMapAdicCompletionₗ_apply_apply (N : Type w) [AddCommGroup N]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) N] (x : N)
    (f : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
         N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) :
    hι.evalLinearMapAdicCompletionₗ N x f = f x := (rfl)

/-- **Matlis biduality for finite modules over the completion**: for a finitely generated
`R̂`-module `N`, evaluation `N → Hom_R(Hom_{R̂}(N, E), E)` is bijective. -/
@[stacks 0EGL "biduality for finite modules over the completion"]
theorem bijective_evalLinearMapAdicCompletionₗ_of_finite (N : Type w) [AddCommGroup N]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) N]
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N] :
    Function.Bijective (hι.evalLinearMapAdicCompletionₗ N) := by
  let S := _root_.AdicCompletion (maximalIdeal R) R
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  let e : N ≃ₗ[S] ((N →ₗ[S] E) →ₗ[R] E) :=
    (hι.isInjectiveEnvelope_adicCompletion.evalEquivOfFinite N).trans
      (AdicCompletion.torsionRestrictScalarsLinearEquivOfMap
        (maximalIdeal R).fg_of_isNoetherianRing
        (hι.mem_primaryComponent_map_adicCompletionLinearMap N) hι.mem_primaryComponent)
  have heq : (hι.evalLinearMapAdicCompletionₗ N : N → ((N →ₗ[S] E) →ₗ[R] E)) = e := by
    ext x f
    simp [S, e]
  rw [heq]
  exact e.bijective

/-- Evaluation identifies a finitely generated `R̂`-module `N` with the `R`-linear Matlis dual of
its `R̂`-linear Matlis dual. -/
@[stacks 0EGL "biduality for finite modules over the completion"]
def evalLinearMapAdicCompletionEquivOfFinite (N : Type w) [AddCommGroup N]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) N]
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    haveI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
    N ≃ₗ[_root_.AdicCompletion (maximalIdeal R) R]
      ((N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) →ₗ[R] E) :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  haveI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  LinearEquiv.ofBijective (hι.evalLinearMapAdicCompletionₗ N)
    (hι.bijective_evalLinearMapAdicCompletionₗ_of_finite N)

@[simp]
theorem evalLinearMapAdicCompletionEquivOfFinite_apply_apply (N : Type w) [AddCommGroup N]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) N]
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N] (x : N)
    (f : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
         N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) :
    hι.evalLinearMapAdicCompletionEquivOfFinite N x f = f x := (rfl)

@[simp]
theorem evalLinearMapAdicCompletionEquivOfFinite_symm_apply_apply (N : Type w) [AddCommGroup N]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) N]
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N]
    (φ : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
         haveI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
         (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) →ₗ[R] E)
    (f : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
         N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) :
    f ((hι.evalLinearMapAdicCompletionEquivOfFinite N).symm φ) = φ f := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  simpa only [evalLinearMapAdicCompletionEquivOfFinite_apply_apply] using
    congrArg (fun ψ : (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) →ₗ[R] E ↦ ψ f)
      ((hι.evalLinearMapAdicCompletionEquivOfFinite N).apply_symm_apply φ)

/-- **Double Matlis dual of a finite module is its adic completion.** Over a Noetherian local ring
`R`, combining biduality for the finite `R̂`-module `N̂` with the torsion-target completion
adjunction `Hom_R(N, E) ≃ₗ[R̂] Hom_{R̂}(N̂, E)` identifies `AdicCompletion (maximalIdeal R) N`
with the double Matlis dual `Hom_R(Hom_R(N, E), E)` as `R̂`-modules. -/
@[stacks 0EGL "double dual of a finite module is its completion"]
def adicCompletionEquivDoubleDual (N : Type w) [AddCommGroup N] [Module R N]
    [Module.Finite R N] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    _root_.AdicCompletion (maximalIdeal R) N ≃ₗ[_root_.AdicCompletion (maximalIdeal R) R]
      ((N →ₗ[R] E) →ₗ[R] E) :=
  let S := _root_.AdicCompletion (maximalIdeal R) R
  let NS := _root_.AdicCompletion (maximalIdeal R) N
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  haveI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  let eLift : (N →ₗ[R] E) ≃ₗ[R] (NS →ₗ[S] E) :=
    (AdicCompletion.torsionLiftEquiv hι.mem_primaryComponent (N := N)).restrictScalars R
  let eHom : ((NS →ₗ[S] E) →ₗ[R] E) ≃ₗ[S] ((N →ₗ[R] E) →ₗ[R] E) :=
    LinearEquiv.ofLinearMap (eLift.toLinearMap.lcomp S E) (eLift.symm.toLinearMap.lcomp S E)
      (by ext; simp [S, NS, eLift]) (by ext; simp [S, NS, eLift])
  (hι.evalLinearMapAdicCompletionEquivOfFinite NS).trans eHom

@[simp]
theorem adicCompletionEquivDoubleDual_of_apply (N : Type w) [AddCommGroup N] [Module R N]
    [Module.Finite R N] (x : N) (f : N →ₗ[R] E) :
    hι.adicCompletionEquivDoubleDual N (_root_.AdicCompletion.of (maximalIdeal R) N x) f =
      f x := by
  simp [adicCompletionEquivDoubleDual]

end General

end TauCeti.IsInjectiveEnvelope
