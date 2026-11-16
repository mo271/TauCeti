/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import TauCeti.RingTheory.ClassGroup.RelNorm
import Mathlib.RingTheory.Norm.Basic

/-!
# Equivariance and Galois orbit-product formulas for ideal norms and class groups

For an extension of domains `S / R`, ring equivalences induce maps on ideal class groups
(`ClassGroup.mulEquiv`), and when `S / R` is a finite torsion-free extension of Dedekind domains
they interact with extension (`ClassGroup.extendedHom`) and relative norm (`ClassGroup.relNorm`) in
two complementary ways:

1. **Equivariance under compatible ring equivalences.** If `e₁ : R₁ ≃+* R₂` and `e₂ : S₁ ≃+* S₂`
   intertwine `algebraMap`, they intertwine `Algebra.intNorm`, `Ideal.relNorm`,
   `ClassGroup.extendedHom`, and `ClassGroup.relNorm`. In particular, for any `R`-algebra
   automorphism `σ : S ≃ₐ[R] S`, `ClassGroup.relNorm R` is invariant under `σ` and the image of
   `ClassGroup.extendedHom R S` is fixed by `σ`.
2. **Norm then extend is the Galois orbit product.** When `FractionRing S / FractionRing R` is
   Galois, extending the relative norm of an ideal `I : Ideal S` back up to `S` gives the product
   of its Galois conjugates (`Ideal.map_algebraMap_relNorm`), and on ideal class groups

   `ClassGroup.extendedHom R S (ClassGroup.relNorm R c) = ∏ σ : S ≃ₐ[R] S, ClassGroup.mulEquiv σ c`

   (`ClassGroup.extendedHom_relNorm`). Together with `ClassGroup.relNorm_extendedHom`
   (`relNorm ∘ extendedHom = (· ^ finrank R S)`), this completes the pair of composite formulas on
   class groups.

## Main results

* `Algebra.intNorm_eq_of_ringEquiv`: compatible ring equivalences intertwine `Algebra.intNorm`.
* `Ideal.map_relNorm_of_ringEquiv`: compatible ring equivalences intertwine `Ideal.relNorm`.
* `ClassGroup.mulEquiv_extendedHom`: compatible ring equivalences intertwine
  `ClassGroup.extendedHom` (over arbitrary domains).
* `ClassGroup.mulEquiv_relNorm`: compatible ring equivalences intertwine `ClassGroup.relNorm`.
* `ClassGroup.relNorm_mulEquiv_algEquiv`, `ClassGroup.mulEquiv_algEquiv_extendedHom`: invariance of
  `ClassGroup.relNorm` and of the image of `ClassGroup.extendedHom` under `S ≃ₐ[R] S`.
* `Ideal.map_algebraMap_relNorm`: for `FractionRing S / FractionRing R` Galois,
  `Ideal.map (algebraMap R S) (Ideal.relNorm R I) = ∏ σ : S ≃ₐ[R] S, Ideal.map σ I`.
* `ClassGroup.extendedHom_relNorm`: for `FractionRing S / FractionRing R` Galois,
  `ClassGroup.extendedHom R S (ClassGroup.relNorm R c) = ∏ σ : S ≃ₐ[R] S, ClassGroup.mulEquiv σ c`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, Proposition 8.2.
* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §1.5 and §4.3.
-/

public section

open scoped nonZeroDivisors

/-! ### Equivariance under compatible ring equivalences -/

section Equivariance

attribute [local instance] FractionRing.liftAlgebra

/-- **Integral norm under compatible ring equivalences.** If `e₁ : R₁ ≃+* R₂` and `e₂ : S₁ ≃+* S₂`
intertwine `algebraMap`, then `e₁ (Algebra.intNorm R₁ S₁ x) = Algebra.intNorm R₂ S₂ (e₂ x)`. -/
theorem Algebra.intNorm_eq_of_ringEquiv {R₁ R₂ S₁ S₂ : Type*}
    [CommRing R₁] [CommRing R₂] [CommRing S₁] [CommRing S₂]
    [IsDomain R₁] [IsDomain R₂] [IsDomain S₁] [IsDomain S₂]
    [IsIntegrallyClosed R₁] [IsIntegrallyClosed R₂]
    [IsIntegrallyClosed S₁] [IsIntegrallyClosed S₂]
    [Algebra R₁ S₁] [Algebra R₂ S₂] [Algebra.IsIntegral R₁ S₁] [Algebra.IsIntegral R₂ S₂]
    [Module.IsTorsionFree R₁ S₁] [Module.IsTorsionFree R₂ S₂]
    (e₁ : R₁ ≃+* R₂) (e₂ : S₁ ≃+* S₂)
    (he : (algebraMap R₂ S₂).comp e₁.toRingHom = e₂.toRingHom.comp (algebraMap R₁ S₁))
    (x : S₁) :
    e₁ (Algebra.intNorm R₁ S₁ x) = Algebra.intNorm R₂ S₂ (e₂ x) := by
  let f₁ : FractionRing R₁ ≃+* FractionRing R₂ := IsFractionRing.ringEquivOfRingEquiv e₁
  let f₂ : FractionRing S₁ ≃+* FractionRing S₂ := IsFractionRing.ringEquivOfRingEquiv e₂
  have hf : (algebraMap (FractionRing R₂) (FractionRing S₂)).comp f₁.toRingHom =
      f₂.toRingHom.comp (algebraMap (FractionRing R₁) (FractionRing S₁)) := by
    apply IsLocalization.ringHom_ext R₁⁰
    ext r
    have hr := RingHom.congr_fun he r
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at hr ⊢
    dsimp only [f₁, f₂]
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap,
      ← IsScalarTower.algebraMap_apply R₂ (FractionRing R₂) (FractionRing S₂),
      IsScalarTower.algebraMap_apply R₂ S₂ (FractionRing S₂), hr,
      ← IsScalarTower.algebraMap_apply R₁ (FractionRing R₁) (FractionRing S₁),
      IsScalarTower.algebraMap_apply R₁ S₁ (FractionRing S₁),
      IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  apply IsFractionRing.injective R₂ (FractionRing R₂)
  rw [← IsFractionRing.ringEquivOfRingEquiv_algebraMap (K := FractionRing R₁)
      (L := FractionRing R₂) e₁,
    Algebra.algebraMap_intNorm_fractionRing, Algebra.algebraMap_intNorm_fractionRing,
    ← IsFractionRing.ringEquivOfRingEquiv_algebraMap (K := FractionRing S₁)
      (L := FractionRing S₂) e₂,
    Algebra.norm_eq_of_equiv_equiv f₁ f₂ hf]
  exact f₁.apply_symm_apply _

/-- **Relative ideal norm under compatible ring equivalences.** -/
theorem Ideal.map_relNorm_of_ringEquiv {R₁ R₂ S₁ S₂ : Type*}
    [CommRing R₁] [CommRing R₂] [CommRing S₁] [CommRing S₂]
    [IsDedekindDomain R₁] [IsDedekindDomain R₂] [IsDedekindDomain S₁] [IsDedekindDomain S₂]
    [Algebra R₁ S₁] [Algebra R₂ S₂] [Module.Finite R₁ S₁] [Module.Finite R₂ S₂]
    [Module.IsTorsionFree R₁ S₁] [Module.IsTorsionFree R₂ S₂]
    (e₁ : R₁ ≃+* R₂) (e₂ : S₁ ≃+* S₂)
    (he : (algebraMap R₂ S₂).comp e₁.toRingHom = e₂.toRingHom.comp (algebraMap R₁ S₁))
    (I : Ideal S₁) :
    Ideal.map e₁.toRingHom (Ideal.relNorm R₁ I) = Ideal.relNorm R₂ (Ideal.map e₂.toRingHom I) := by
  have himg : (Ideal.map e₂.toRingHom I : Set S₂) = e₂ '' (I : Set S₁) := by
    ext y
    simp only [SetLike.mem_coe, Set.mem_image]
    constructor
    · intro hy
      refine ⟨e₂.symm y, ?_, e₂.apply_symm_apply y⟩
      simpa [Ideal.map_coe] using Ideal.symm_apply_mem_of_equiv_iff.mpr hy
    · rintro ⟨x, hx, rfl⟩
      exact Ideal.mem_map_of_mem e₂.toRingHom hx
  rw [Ideal.map_relNorm, Ideal.relNorm_apply, himg, ← Set.image_comp]
  congr 2
  ext x
  exact Algebra.intNorm_eq_of_ringEquiv e₁ e₂ he x

private theorem ClassGroup.map_congr_ringHom {A B : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] {f g : A →+* B} (hfg : f = g)
    (hf : Function.Injective f) (hg : Function.Injective g) (c : ClassGroup A) :
    ClassGroup.map f hf c = ClassGroup.map g hg c := by
  subst hfg
  rfl

private theorem ClassGroup.extendedHom_eq_map {A B : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Algebra A B] [Module.IsTorsionFree A B] (c : ClassGroup A) :
    ClassGroup.extendedHom A B c =
      ClassGroup.map (algebraMap A B) (FaithfulSMul.algebraMap_injective A B) c := by
  induction c using QuotientGroup.induction_on with
  | H α => rw [ClassGroup.extendedHom_quotientMk, ClassGroup.map_quotientMk]

/-- **Class-group extension commutes with compatible ring equivalences** (for arbitrary torsion-free
extensions of domains). -/
theorem ClassGroup.mulEquiv_extendedHom {R₁ R₂ S₁ S₂ : Type*}
    [CommRing R₁] [IsDomain R₁] [CommRing R₂] [IsDomain R₂]
    [CommRing S₁] [IsDomain S₁] [CommRing S₂] [IsDomain S₂]
    [Algebra R₁ S₁] [Algebra R₂ S₂] [Module.IsTorsionFree R₁ S₁] [Module.IsTorsionFree R₂ S₂]
    (e₁ : R₁ ≃+* R₂) (e₂ : S₁ ≃+* S₂)
    (he : (algebraMap R₂ S₂).comp e₁.toRingHom = e₂.toRingHom.comp (algebraMap R₁ S₁))
    (c : ClassGroup R₁) :
    ClassGroup.mulEquiv e₂ (ClassGroup.extendedHom R₁ S₁ c) =
      ClassGroup.extendedHom R₂ S₂ (ClassGroup.mulEquiv e₁ c) := by
  rw [ClassGroup.extendedHom_eq_map, ClassGroup.extendedHom_eq_map, ClassGroup.mulEquiv_apply,
    ClassGroup.mulEquiv_apply, ClassGroup.map_map, ClassGroup.map_map]
  exact ClassGroup.map_congr_ringHom he.symm _ _ c

/-- **Class-group relative norm commutes with compatible ring equivalences.** -/
theorem ClassGroup.mulEquiv_relNorm {R₁ R₂ S₁ S₂ : Type*}
    [CommRing R₁] [CommRing R₂] [CommRing S₁] [CommRing S₂]
    [IsDedekindDomain R₁] [IsDedekindDomain R₂] [IsDedekindDomain S₁] [IsDedekindDomain S₂]
    [Algebra R₁ S₁] [Algebra R₂ S₂] [Module.Finite R₁ S₁] [Module.Finite R₂ S₂]
    [Module.IsTorsionFree R₁ S₁] [Module.IsTorsionFree R₂ S₂]
    (e₁ : R₁ ≃+* R₂) (e₂ : S₁ ≃+* S₂)
    (he : (algebraMap R₂ S₂).comp e₁.toRingHom = e₂.toRingHom.comp (algebraMap R₁ S₁))
    (c : ClassGroup S₁) :
    ClassGroup.mulEquiv e₁ (ClassGroup.relNorm R₁ c) =
      ClassGroup.relNorm R₂ (ClassGroup.mulEquiv e₂ c) := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [ClassGroup.relNorm_mk0, ClassGroup.mulEquiv_mk0, ClassGroup.mulEquiv_mk0,
    ClassGroup.relNorm_mk0]
  congr 1
  apply Subtype.ext
  simpa [Ideal.map_coe] using Ideal.map_relNorm_of_ringEquiv e₁ e₂ he (I : Ideal S₁)

/-- Every `R`-algebra automorphism of `S` fixes the image of `ClassGroup.extendedHom R S`. -/
theorem ClassGroup.mulEquiv_algEquiv_extendedHom {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S] [Module.IsTorsionFree R S]
    (σ : S ≃ₐ[R] S) (c : ClassGroup R) :
    ClassGroup.mulEquiv σ.toRingEquiv (ClassGroup.extendedHom R S c) =
      ClassGroup.extendedHom R S c := by
  have h := ClassGroup.mulEquiv_extendedHom (S₁ := S) (S₂ := S) (RingEquiv.refl R) σ.toRingEquiv
    (RingHom.ext fun r ↦ (σ.commutes r).symm) c
  simpa using h

/-- `ClassGroup.relNorm R` is invariant under every `R`-algebra automorphism of `S`. -/
theorem ClassGroup.relNorm_mulEquiv_algEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
    [Module.IsTorsionFree R S] (σ : S ≃ₐ[R] S) (c : ClassGroup S) :
    ClassGroup.relNorm R (ClassGroup.mulEquiv σ.toRingEquiv c) = ClassGroup.relNorm R c := by
  have h := ClassGroup.mulEquiv_relNorm (S₁ := S) (S₂ := S) (RingEquiv.refl R) σ.toRingEquiv
    (RingHom.ext fun r ↦ (σ.commutes r).symm) c
  simpa using h.symm

end Equivariance

/-! ### Galois orbit-product formulas -/

section GaloisOrbit

attribute [local instance] FractionRing.liftAlgebra

/-- **Extending a relative norm ideal equals the Galois orbit product.** For a finite torsion-free
extension `S / R` of Dedekind domains whose fraction-field extension is Galois,

`Ideal.map (algebraMap R S) (Ideal.relNorm R I) = ∏ σ : S ≃ₐ[R] S, Ideal.map (σ : S →+* S) I`. -/
theorem Ideal.map_algebraMap_relNorm {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
    [Module.IsTorsionFree R S] [IsGalois (FractionRing R) (FractionRing S)] (I : Ideal S) :
    Ideal.map (algebraMap R S) (Ideal.relNorm R I) =
      ∏ σ : S ≃ₐ[R] S, Ideal.map (σ : S →+* S) I := by
  have : FiniteDimensional (FractionRing R) (FractionRing S) := .of_isLocalization R S R⁰
  have : IsIntegralClosure S R (FractionRing S) := IsIntegralClosure.of_isIntegrallyClosed _ _ _
  let eGal := (galRestrict R (FractionRing R) (FractionRing S) S).toEquiv
  by_cases hI : I = ⊥
  · subst hI
    rw [Ideal.relNorm_bot, Ideal.map_bot]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ (1 : S ≃ₐ[R] S)) Ideal.map_bot
  set K := Ideal.map (algebraMap R S) (Ideal.relNorm R I)
  set J := ∏ σ : S ≃ₐ[R] S, Ideal.map (σ : S →+* S) I
  -- Every norm generator `algebraMap (intNorm x) = ∏ σ, σ x` belongs to `J`, so `K ≤ J`.
  have hKJ : K ≤ J := by
    rw [show K = Ideal.span ((algebraMap R S ∘ Algebra.intNorm R S) '' (I : Set S)) from
      Ideal.map_relNorm R I (algebraMap R S), Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [Function.comp_apply, Algebra.algebraMap_intNorm_of_isGalois]
    exact Ideal.prod_mem_prod fun σ _ ↦ Ideal.mem_map_of_mem (σ : S →+* S) hx
  -- Compare `Ideal.relNorm R` of both sides: both equal `(Ideal.relNorm R I) ^ finrank R S`.
  have hcard : Fintype.card (S ≃ₐ[R] S) = Module.finrank R S := by
    rw [← Fintype.card_congr eGal, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      IsFractionRing.finrank_eq R (FractionRing R) S (FractionRing S)]
  have hnormJ : Ideal.relNorm R J = Ideal.relNorm R I ^ Module.finrank R S := by
    rw [show J = ∏ σ : S ≃ₐ[R] S, Ideal.map (σ : S →+* S) I from rfl, map_prod]
    have hterm (σ : S ≃ₐ[R] S) : Ideal.relNorm R (Ideal.map (σ : S →+* S) I) = Ideal.relNorm R I :=
      Ideal.relNorm_map_algEquiv σ I
    simp only [hterm, Finset.prod_const, Finset.card_univ, hcard]
  have hnormK : Ideal.relNorm R K = Ideal.relNorm R J := by
    rw [Ideal.relNorm_algebraMap S (Ideal.relNorm R I), hnormJ]
  -- Use Dedekind divisibility `J ∣ K` (`K = J * M`) and cancel the nonzero norm in `Ideal R`.
  obtain ⟨M, hKM⟩ := Ideal.dvd_iff_le.mpr hKJ
  have hJ0 : Ideal.relNorm R J ≠ 0 := by
    rw [hnormJ]
    exact pow_ne_zero _ (mt Ideal.relNorm_eq_bot_iff.mp hI)
  have hnormM : Ideal.relNorm R M = 1 := by
    apply mul_left_cancel₀ hJ0
    rw [← map_mul, ← hKM, hnormK, mul_one]
  have hM : M = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have htop : (⊤ : Ideal R) ≤ Ideal.comap (algebraMap R S) M := by
      rw [← Ideal.one_eq_top, ← hnormM]
      exact Ideal.relNorm_le_comap R M
    have h1 : (1 : S) ∈ M := by
      simpa [Ideal.mem_comap] using htop (Submodule.mem_top : (1 : R) ∈ ⊤)
    simpa using M.mul_mem_left x h1
  rw [hKM, hM, ← Ideal.one_eq_top, mul_one]

/-- **Norm then extend on class groups is the Galois orbit product.** When
`FractionRing S / FractionRing R` is Galois, extending `ClassGroup.relNorm R c` back to `S` gives
the product of all `S ≃ₐ[R] S`-conjugates of `c`. -/
theorem ClassGroup.extendedHom_relNorm {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
    [Module.IsTorsionFree R S] [IsGalois (FractionRing R) (FractionRing S)] (c : ClassGroup S) :
    ClassGroup.extendedHom R S (ClassGroup.relNorm R c) =
      ∏ σ : S ≃ₐ[R] S, ClassGroup.mulEquiv σ.toRingEquiv c := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  have hmap (σ : S ≃ₐ[R] S) : Ideal.map (σ : S →+* S) (I : Ideal S) ∈ (Ideal S)⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr <|
      (Ideal.map_eq_bot_iff_of_injective σ.injective).not.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mp I.2)
  let J : (S ≃ₐ[R] S) → (Ideal S)⁰ := fun σ ↦ ⟨Ideal.map (σ : S →+* S) (I : Ideal S), hmap σ⟩
  have hmul (σ : S ≃ₐ[R] S) :
      ClassGroup.mulEquiv σ.toRingEquiv (ClassGroup.mk0 I) = ClassGroup.mk0 (J σ) := by
    rw [ClassGroup.mulEquiv_mk0]
    congr 1
  simp_rw [hmul, ← map_prod]
  rw [ClassGroup.relNorm_mk0, ClassGroup.extendedHom_mk0]
  congr 1
  apply Subtype.ext
  simpa [J] using Ideal.map_algebraMap_relNorm (R := R) (I : Ideal S)

end GaloisOrbit
