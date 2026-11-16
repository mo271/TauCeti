/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.TFAE
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Localization.Finiteness
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.FieldTheory.IntermediateField.ScalarTower
import TauCeti.RingTheory.DedekindDomain.IntegralClosure
import TauCeti.RingTheory.DiscreteValuationRing.AbhyankarModel.Localization
import TauCeti.RingTheory.DiscreteValuationRing.Kummer
import TauCeti.RingTheory.Ideal.LiesOver
import TauCeti.RingTheory.Localization.AtPrime
import TauCeti.RingTheory.Localization.Integral

/-!
# Kummer characterization of tamely ramified extensions

Let `A` be a discrete valuation ring with fraction field `K` and uniformizer `π`, and let `L / K`
be a finite extension. If `L` is tamely ramified with respect to `A` and `E = L(β)` is generated
over `L` by an `n`-th root `β` of `π` whose exponent `n` is divisible by the ramification index
over `A` of every maximal ideal of the integral closure of `A` in `L`, then the integral closure
`A[β]` of `A` in `K(β)` is a discrete valuation ring and `E` is unramified with respect to `A[β]`
(`TauCeti.Algebra.IsTamelyRamifiedWRT.isUnramifiedWRT_of_pow_eq_of_irreducible`). Neither
separability of `L / K` nor invertibility of `n` in the residue field of `A` is required for this
elimination of ramification.

Combined with the converse
`TauCeti.IsDiscreteValuationRing.isTamelyRamifiedWRT_of_isUnramifiedWRT_of_pow_eq_of_irreducible`,
this proves the three-way Kummer characterization of tame ramification for a finite separable
extension `L / K` (Stacks, Lemma 15.116.7):

1. `L` is tamely ramified with respect to `A`;
2. there exist `e` invertible in the residue field `κ_A` and an extension `E` of `L` containing an
   `e`-th root `β` of `π` such that `E / K(β)` is finite separable and unramified with respect to
   `A[β]`;
3. there exists `e₀` invertible in `κ_A` such that for every `d` invertible in `κ_A`, such an
   extension exists with exponent `d * e₀`.

The proof of `isUnramifiedWRT_of_pow_eq_of_irreducible` localizes the integral closures `B` and `C`
of `A` in `L` and `E` at a maximal ideal `Q` of `C` and `P = Q ∩ B`. The local rings `B_P → C_Q`
are discrete valuation rings satisfying the hypotheses of
`TauCeti.RingTheory.DiscreteValuationRing.AbhyankarModel.Localization`, so `β` is a uniformizer of
`C_Q`—forcing `Q` to have ramification index one over `A[β]`—and `κ(Q) / κ(P)` is separable.

## Main results

* `TauCeti.Algebra.IsTamelyRamifiedWRT.isUnramifiedWRT_of_pow_eq_of_irreducible`: adjoining an
  `n`-th root `β` of `π` to a tamely ramified extension `L / K`, with `n` divisible by every
  ramification index of `L` over `A`, makes `L(β)` unramified over `A[β]`.
* `TauCeti.Algebra.isTamelyRamifiedWRT_tfae`: equivalence of the three conditions of Stacks,
  Lemma 15.116.7.
* `TauCeti.Algebra.isTamelyRamifiedWRT_iff_exists_kummer`: equivalence `(1) ↔ (2)`.
* `TauCeti.Algebra.isTamelyRamifiedWRT_iff_exists_forall_kummer`: equivalence `(1) ↔ (3)`.

## References

* [Stacks Project, Lemma 15.116.7](https://stacks.math.columbia.edu/tag/0EXW).
-/

public section

open _root_.IntermediateField IsLocalRing

namespace TauCeti.Algebra

section Helpers

/-- At a prime `P` of an `A`-domain `B` lying over the maximal ideal of a discrete valuation ring
`A`, if `B_P` is a discrete valuation ring with uniformizer `ϖ`, then any uniformizer `π` of `A`
maps in `B_P` to a unit times `ϖ ^ P.ramificationIdx A`. -/
private theorem exists_unit_mul_pow_ramificationIdx_localization {A B : Type*} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [Algebra A B]
    [FaithfulSMul A B] {π : A} (hπ : Irreducible π) (P : Ideal B) [P.IsPrime]
    [P.LiesOver (maximalIdeal A)] [IsDiscreteValuationRing (Localization.AtPrime P)]
    {ϖ : Localization.AtPrime P} (hϖ : Irreducible ϖ) :
    ∃ u : (Localization.AtPrime P)ˣ,
      algebraMap A (Localization.AtPrime P) π = u * ϖ ^ P.ramificationIdx A := by
  let Bp := Localization.AtPrime P
  have hπB : algebraMap A B π ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A B)).mpr hπ.ne_zero
  have hπBp : algebraMap A Bp π ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A B Bp]
    exact (map_ne_zero_iff _ (IsLocalization.injective Bp P.primeCompl_le_nonZeroDivisors)).mpr hπB
  obtain ⟨e', u, hπeq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπBp hϖ
  have hmap : (maximalIdeal A).map (algebraMap A Bp) = maximalIdeal Bp ^ e' := by
    rw [hπ.maximalIdeal_eq, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hπeq,
      Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit u.isUnit]
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_of_map_eq_pow (maximalIdeal A) P e' hmap]
  exact ⟨u, hπeq⟩

/-- Clearing denominators from `E = L(β)` to `B_P[β]` inside a subring `S ⊆ E` over `B_P`. -/
private theorem exists_mul_mem_adjoin_localization {B L S E : Type*} [CommRing B] [IsDomain B]
    [Field L] [Algebra B L] [IsFractionRing B L] (P : Ideal B) [P.IsPrime]
    [Field E] [Algebra L E] [Algebra B E] [IsScalarTower B L E]
    [CommRing S] [Algebra B S] [Algebra S E] [IsScalarTower B S E]
    [Algebra (Localization.AtPrime P) S] [IsScalarTower B (Localization.AtPrime P) S]
    (hSE : Function.Injective (algebraMap S E)) {βS : S}
    (halg : IsAlgebraic L (algebraMap S E βS)) (hgen : L⟮algebraMap S E βS⟯ = ⊤) (c : S) :
    ∃ s : Localization.AtPrime P, s ≠ 0 ∧
      algebraMap (Localization.AtPrime P) S s * c ∈
        Algebra.adjoin (Localization.AtPrime P) {βS} := by
  let Bp := Localization.AtPrime P
  let : Algebra Bp E := ((algebraMap L E).comp (algebraMap Bp L)).toAlgebra
  have : IsScalarTower Bp L E := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower B Bp E := .of_algebraMap_eq fun b ↦ by
    simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply]
  have : IsScalarTower Bp S E := .of_algebraMap_eq fun x ↦ by
    have hEq : (algebraMap S E).comp (algebraMap Bp S) = algebraMap Bp E :=
      IsLocalization.ringHom_ext P.primeCompl <| RingHom.ext fun b ↦ by
        simp [← IsScalarTower.algebraMap_apply]
    exact DFunLike.congr_fun hEq.symm x
  have hmem : algebraMap S E c ∈ Algebra.adjoin L {algebraMap S E βS} := by
    rw [← adjoin_simple_toSubalgebra_of_isAlgebraic halg, hgen]
    exact Algebra.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_adjoin_of_mem_localization_adjoin (nonZeroDivisors Bp) L
    {algebraMap S E βS} (algebraMap S E c) hmem
  refine ⟨t, mem_nonZeroDivisors_iff_ne_zero.mp t.2, ?_⟩
  have himg : (t : Bp) • algebraMap S E c ∈
      (Algebra.adjoin Bp {βS}).map (IsScalarTower.toAlgHom Bp S E) := by
    rwa [AlgHom.map_adjoin_singleton, IsScalarTower.coe_toAlgHom']
  obtain ⟨y, hy, hyeq⟩ := himg
  have hyc : y = algebraMap Bp S t * c := hSE <| by
    simpa [map_mul, ← IsScalarTower.algebraMap_apply Bp S E, Algebra.smul_def] using hyeq
  exact hyc ▸ hy

attribute [local instance] integralClosureMapAlgebra isScalarTower_integralClosureMapAlgebra_left
  isScalarTower_integralClosureMapAlgebra_right

/-- Applying the local Abhyankar model at `B_P → C_Q` shows that `β` is a uniformizer of `C_Q` and
`B ⧸ P → C ⧸ Q` is separable. -/
private theorem irreducible_and_isSeparable_localization {A B L C E : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B] [FaithfulSMul A B]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [CommRing C] [IsDedekindDomain C] [Algebra A C] [Algebra B C]
    [IsScalarTower A B C] [FaithfulSMul A C]
    [Field E] [Algebra A E] [Algebra L E] [Algebra B E] [Algebra C E]
    [IsScalarTower B L E] [IsScalarTower B C E] [IsScalarTower A C E] [IsFractionRing C E]
    {π : A} {n : ℕ} {βC : C} (hπ : Irreducible π) (hn : n ≠ 0)
    (hβ : (algebraMap C E βC) ^ n = algebraMap A E π)
    (halg : IsAlgebraic L (algebraMap C E βC)) (hgen : L⟮algebraMap C E βC⟯ = ⊤)
    (P : Ideal B) [P.IsMaximal] [P.LiesOver (maximalIdeal A)]
    (Q : Ideal C) [Q.IsMaximal] [Q.LiesOver P] [Q.LiesOver (maximalIdeal A)]
    (hdvd : P.ramificationIdx A ∣ n)
    (heP : IsUnit ((P.ramificationIdx A : ℕ) : A ⧸ maximalIdeal A)) :
    Irreducible (algebraMap C (Localization.AtPrime Q) βC) ∧
      Algebra.IsSeparable (B ⧸ P) (C ⧸ Q) := by
  have hP0 : P ≠ ⊥ := fun h0 ↦ hπ.ne_zero <| (FaithfulSMul.algebraMap_injective A B).eq_iff.mp <| by
    simpa [h0] using (P.mem_of_liesOver (maximalIdeal A) π).mp
      ((mem_maximalIdeal π).mpr hπ.not_isUnit)
  have hQ0 : Q ≠ ⊥ := fun h0 ↦ hπ.ne_zero <| (FaithfulSMul.algebraMap_injective A C).eq_iff.mp <| by
    simpa [h0] using (Q.mem_of_liesOver (maximalIdeal A) π).mp
      ((mem_maximalIdeal π).mpr hπ.not_isUnit)
  let Bp := Localization.AtPrime P
  let Cq := Localization.AtPrime Q
  have : IsDiscreteValuationRing Bp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP0 Bp
  have : IsDiscreteValuationRing Cq :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hQ0 Cq
  let := Localization.AtPrime.algebraOfLiesOver P Q
  have : IsScalarTower A Cq E := .to₁₃₄ A C Cq E
  have : IsScalarTower B Cq E := .to₁₃₄ B C Cq E
  have hBpE : (algebraMap Cq E).comp (algebraMap Bp Cq) =
      (algebraMap L E).comp (algebraMap Bp L) :=
    IsLocalization.ringHom_ext P.primeCompl <| RingHom.ext fun b ↦ by
      simp [← IsScalarTower.algebraMap_apply]
  have : FaithfulSMul Bp Cq := (faithfulSMul_iff_algebraMap_injective Bp Cq).mpr <|
    .of_comp (f := algebraMap Cq E) <| by
      rw [← RingHom.coe_comp, hBpE]
      exact (RingHom.injective (algebraMap L E)).comp (IsFractionRing.injective Bp L)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Bp
  obtain ⟨u, hπeq⟩ := exists_unit_mul_pow_ramificationIdx_localization hπ P hϖ
  obtain ⟨d, hd_eq⟩ := hdvd
  have hd : d ≠ 0 := fun hd0 ↦ hn (by simp [hd_eq, hd0])
  have heA : IsUnit ((P.ramificationIdx A : ℕ) : A) :=
    (isUnit_map_iff (IsLocalRing.residue A) (P.ramificationIdx A : A)).mp
      (by rw [map_natCast]; exact heP)
  have he : IsUnit ((P.ramificationIdx A : ℕ) : Bp) :=
    map_natCast (algebraMap A Bp) (P.ramificationIdx A) ▸ heA.map (algebraMap A Bp)
  let βq : Cq := algebraMap C Cq βC
  have hβq : βq ^ (P.ramificationIdx A * d) = algebraMap Bp Cq (↑u * ϖ ^ P.ramificationIdx A) := by
    rw [← hd_eq, ← hπeq, ← IsScalarTower.algebraMap_apply A Bp Cq]
    apply IsFractionRing.injective Cq E
    rw [map_pow, ← IsScalarTower.algebraMap_apply C Cq E, hβ,
      IsScalarTower.algebraMap_apply A Cq E]
  have halgq : IsAlgebraic L (algebraMap Cq E βq) := by
    rwa [← IsScalarTower.algebraMap_apply C Cq E]
  have hgenq := exists_mul_mem_adjoin_localization (L := L) P (IsFractionRing.injective Cq E) halgq
    (by simpa [βq, ← IsScalarTower.algebraMap_apply C Cq E] using hgen)
  have : Algebra.IsSeparable P.ResidueField Q.ResidueField :=
    isSeparable_residueField_of_pow_eq_unit_mul_pow hϖ u.isUnit he hd hβq hgenq
  exact ⟨irreducible_of_pow_eq_unit_mul_pow hϖ u.isUnit he hd hβq hgenq,
    (Algebra.isSeparable_residueField_iff (A := B) (B := C) (p := P) (q := Q)).mp inferInstance⟩

/-- If `L / K` is separable and `E = L(β)`, then `E / K(β)` is separable. -/
private theorem isSeparable_adjoin_of_adjoin_eq_top {K L E : Type*} [Field K] [Field L]
    [Algebra K L] [Algebra.IsSeparable K L] [Field E] [Algebra K E] [Algebra L E]
    [IsScalarTower K L E] {β : E} (hgen : L⟮β⟯ = ⊤) :
    Algebra.IsSeparable K⟮β⟯ E := by
  let S : IntermediateField L E :=
    { (separableClosure K⟮β⟯ E).toSubfield with
      algebraMap_mem' l := mem_separableClosure_iff.mpr <|
        ((Algebra.IsSeparable.isSeparable K l).map (IsScalarTower.toAlgHom K L E)
          (RingHom.injective _)).tower_top K⟮β⟯ }
  have hβS : β ∈ S :=
    mem_separableClosure_iff.mpr (isSeparable_algebraMap (AdjoinSimple.gen K β))
  have htop : S = ⊤ := top_unique (hgen ▸ adjoin_simple_le_iff.mpr hβS)
  exact ⟨fun x ↦ mem_separableClosure_iff.mp (htop ▸ mem_top : x ∈ S)⟩

end Helpers

section Characterization

attribute [local instance] integralClosureMapAlgebra isScalarTower_integralClosureMapAlgebra_left
  isScalarTower_integralClosureMapAlgebra_right

/-- Once `A₁ = integralClosure A K⟮β⟯` is known to be a discrete valuation ring with uniformizer
`⟨β, _⟩`, every maximal ideal `Q` of `integralClosure A E` has ramification index `1` and separable
residue field over `A₁`. -/
private theorem isUnramifiedWRT_integralClosure_adjoin {A K L E : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [FiniteDimensional K L]
    [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [Algebra L E] [IsScalarTower A L E] [FiniteDimensional K E]
    {π : A} {n : ℕ} {β : E} [IsDiscreteValuationRing (integralClosure A K⟮β⟯)]
    (h : IsTamelyRamifiedWRT A L) (hπ : Irreducible π) (hn : n ≠ 0)
    (hβ : β ^ n = algebraMap A E π) (halg : IsAlgebraic L β) (hgen : L⟮β⟯ = ⊤)
    (hmemK : AdjoinSimple.gen K β ∈ integralClosure A K⟮β⟯)
    (hβ₁ : Irreducible (⟨AdjoinSimple.gen K β, hmemK⟩ : integralClosure A K⟮β⟯))
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal], P.ramificationIdx A ∣ n) :
    IsUnramifiedWRT (integralClosure A K⟮β⟯) E := by
  let A₁ := integralClosure A K⟮β⟯
  let B := integralClosure A L
  let C := integralClosure A E
  have := FaithfulSMul.trans A K E
  have := FaithfulSMul.trans A K L
  have : Algebra.IsIntegral A₁ C := .tower_top A
  have : FaithfulSMul A₁ C := .tower_bot _ _ E
  have : Module.IsTorsionFree A₁ C := FaithfulSMul.to_isTorsionFree ..
  have : IsIntegralClosure C A₁ E := IsIntegralClosure.tower_top (R := A)
  have : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  have : IsDedekindDomain C := integralClosure.isDedekindDomain A K E
  have : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have : IsFractionRing C E := IsIntegralClosure.isFractionRing_of_finite_extension A K E C
  have : FaithfulSMul A B := .tower_bot A B L
  have : FaithfulSMul A C := .tower_bot A C E
  have : Algebra.IsIntegral B C := .tower_top A
  rw [isUnramifiedWRT_iff_of_isIntegralClosure C]
  intro Q _ _
  let P : Ideal B := Q.under B
  have : P.IsMaximal := Ideal.IsMaximal.under B Q
  have : Q.LiesOver P := ⟨rfl⟩
  have : P.LiesOver (maximalIdeal A) := ⟨(eq_maximalIdeal (Ideal.IsMaximal.under A P)).symm⟩
  have : (maximalIdeal A₁).LiesOver (maximalIdeal A) :=
    ⟨(eq_maximalIdeal (Ideal.IsMaximal.under A (maximalIdeal A₁))).symm⟩
  have : Q.LiesOver (maximalIdeal A) := .trans Q (maximalIdeal A₁) (maximalIdeal A)
  obtain ⟨hirr, hsepBC⟩ := irreducible_and_isSeparable_localization (L := L)
    (βC := algebraMap A₁ C ⟨AdjoinSimple.gen K β, hmemK⟩) hπ hn hβ halg hgen P Q (hdvd P)
    (isTamelyRamifiedWRT_def.mp h P).2
  have hQ0 : Q ≠ ⊥ := fun h0 ↦ hπ.ne_zero <| (FaithfulSMul.algebraMap_injective A C).eq_iff.mp <| by
    simpa [h0] using (Q.mem_of_liesOver (maximalIdeal A) π).mp
      ((mem_maximalIdeal π).mpr hπ.not_isUnit)
  have : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hQ0 _
  have hmap₁ : (maximalIdeal A₁).map (algebraMap A₁ (Localization.AtPrime Q)) =
      maximalIdeal (Localization.AtPrime Q) ^ 1 := by
    rw [pow_one, hβ₁.maximalIdeal_eq, hirr.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      IsScalarTower.algebraMap_apply A₁ C (Localization.AtPrime Q)]
  let := Ideal.Quotient.field (maximalIdeal A)
  let := Ideal.Quotient.field (maximalIdeal A₁)
  let := Ideal.Quotient.field P
  let := Ideal.Quotient.field Q
  have := (isTamelyRamifiedWRT_def.mp h P).1
  have := Ideal.Quotient.isScalarTower_quotient_of_liesOver (maximalIdeal A) P Q
  have : Algebra.IsSeparable (A ⧸ maximalIdeal A) (C ⧸ Q) := .trans _ (B ⧸ P) _
  have := Ideal.Quotient.isScalarTower_quotient_of_liesOver (maximalIdeal A) (maximalIdeal A₁) Q
  exact ⟨Ideal.IsDedekindDomain.ramificationIdx_eq_of_map_eq_pow (maximalIdeal A₁) Q 1 hmap₁,
    Algebra.isSeparable_tower_top_of_isSeparable (A ⧸ maximalIdeal A) (A₁ ⧸ maximalIdeal A₁)
      (C ⧸ Q)⟩

/-- **Elimination of tame ramification over a Kummer extension (Abhyankar's lemma for DVRs).**
Let `A` be a discrete valuation ring with fraction field `K` and uniformizer `π`, and let `L / K`
be a finite extension tamely ramified with respect to `A`. If `E = L(β)` is generated over `L` by
an `n`-th root `β` of `π`, and `n` is divisible by the ramification index over `A` of every
maximal ideal of the integral closure of `A` in `L`, then the integral closure `A[β]` of `A` in
`K(β)` is a discrete valuation ring and `E` is unramified with respect to `A[β]`. -/
theorem IsTamelyRamifiedWRT.isUnramifiedWRT_of_pow_eq_of_irreducible {A K L E : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [FiniteDimensional K L]
    [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [Algebra L E] [IsScalarTower K L E] {π : A} {n : ℕ} {β : E}
    (h : IsTamelyRamifiedWRT A L) (hπ : Irreducible π)
    (hβ : β ^ n = algebraMap A E π) (hgen : L⟮β⟯ = ⊤)
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal], P.ramificationIdx A ∣ n) :
    ∃ _ : IsDiscreteValuationRing (integralClosure A K⟮β⟯),
      IsUnramifiedWRT (integralClosure A K⟮β⟯) E := by
  have := FaithfulSMul.trans A K E
  have hn : n ≠ 0 := by
    rintro rfl
    exact hπ.ne_one ((FaithfulSMul.algebraMap_injective A E) (by simpa using hβ.symm))
  have : IsScalarTower A L E := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply K L E,
      ← IsScalarTower.algebraMap_apply A K E]
  have hint : IsIntegral A β :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hβ ▸ isIntegral_algebraMap)
  have : FiniteDimensional L E :=
    have : FiniteDimensional L L⟮β⟯ := adjoin.finiteDimensional hint.tower_top
    Module.Finite.equiv (hgen ▸ IntermediateField.topEquiv).toLinearEquiv
  have : FiniteDimensional K E := .trans K L E
  have hβK : AdjoinSimple.gen K β ^ n = algebraMap A K⟮β⟯ π :=
    (algebraMap K⟮β⟯ E).injective (by
      rw [map_pow, AdjoinSimple.algebraMap_gen, hβ, ← IsScalarTower.algebraMap_apply])
  have hgenK : K⟮AdjoinSimple.gen K β⟯ = ⊤ := adjoin_adjoinSimple_gen_eq_top β
  have hDVR : IsDiscreteValuationRing (integralClosure A K⟮β⟯) :=
    IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible
      hπ hβK hgenK
  have hmemK : AdjoinSimple.gen K β ∈ integralClosure A K⟮β⟯ :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hβK ▸ isIntegral_algebraMap)
  have hβ₁ : Irreducible (⟨AdjoinSimple.gen K β, hmemK⟩ : integralClosure A K⟮β⟯) :=
    IsDiscreteValuationRing.irreducible_mk_of_pow_eq_of_irreducible hπ hβK hgenK hmemK
  exact ⟨hDVR, isUnramifiedWRT_integralClosure_adjoin (K := K) h hπ hn hβ
    hint.tower_top.isAlgebraic hgen hmemK hβ₁ hdvd⟩

universe u

variable {A : Type*} (K : Type*) {L : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L]
  [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- Implication `(1) ⇒ (3)` of Stacks, Lemma 15.116.7: taking `e₀` to be the product of all
ramification indices of primes of `integralClosure A L` over `maximalIdeal A`, adjoining a
`(d * e₀)`-th root of `π` eliminates ramification for every `d` invertible in `κ_A`. -/
private theorem exists_forall_kummer_of_isTamelyRamifiedWRT {π : A} (hπ : Irreducible π)
    (h : IsTamelyRamifiedWRT A L) :
    ∃ e₀ : ℕ, IsUnit (e₀ : A ⧸ maximalIdeal A) ∧
      ∀ d : ℕ, IsUnit (d : A ⧸ maximalIdeal A) →
        ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Algebra A E)
          (_ : IsScalarTower A K E) (_ : Algebra L E) (_ : IsScalarTower K L E) (β : E)
          (_ : IsDiscreteValuationRing (integralClosure A K⟮β⟯)),
          β ^ (d * e₀) = algebraMap A E π ∧ FiniteDimensional K⟮β⟯ E ∧
            Algebra.IsSeparable K⟮β⟯ E ∧ IsUnramifiedWRT (integralClosure A K⟮β⟯) E := by
  classical
  have : IsDedekindDomain (integralClosure A L) := integralClosure.isDedekindDomain A K L
  have : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A K L _
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  have : Module.Free A (integralClosure A L) := IsIntegralClosure.module_free A K L _
  let S := (maximalIdeal A).primesOver (integralClosure A L)
  let e₀ : ℕ := ∏ Q : S, Q.1.ramificationIdx A
  have he₀ : IsUnit (e₀ : A ⧸ maximalIdeal A) := by
    rw [Nat.cast_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ ha hb ↦ ha.mul hb) isUnit_one
      fun Q _ ↦ (isTamelyRamifiedWRT_def.mp h Q.1).2
  refine ⟨e₀, he₀, fun d hd ↦ ?_⟩
  have hde : d * e₀ ≠ 0 := by
    rintro h0
    have hu : IsUnit (((d * e₀ : ℕ) : A ⧸ maximalIdeal A)) := by
      rw [Nat.cast_mul]; exact hd.mul he₀
    simp [h0] at hu
  let Ω := AlgebraicClosure L
  have : IsScalarTower A K Ω := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A L Ω, IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply K L Ω]
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A Ω π) (Nat.pos_of_ne_zero hde)
  let E := (L⟮α⟯ : Type u)
  let β : E := AdjoinSimple.gen L α
  have : IsScalarTower A K E := .of_algebraMap_eq fun a ↦
    Subtype.ext (IsScalarTower.algebraMap_apply A K Ω a)
  have : IsScalarTower A E Ω := .of_algebraMap_eq fun _ ↦ rfl
  have hβ : β ^ (d * e₀) = algebraMap A E π :=
    (algebraMap E Ω).injective (by
      rw [map_pow, AdjoinSimple.algebraMap_gen, hα, ← IsScalarTower.algebraMap_apply A E Ω])
  have hgen : L⟮β⟯ = ⊤ := adjoin_adjoinSimple_gen_eq_top α
  have hdvd (P : Ideal (integralClosure A L)) [P.IsMaximal] : P.ramificationIdx A ∣ d * e₀ := by
    have hP : P ∈ S := ⟨inferInstance, ⟨(eq_maximalIdeal (Ideal.IsMaximal.under A P)).symm⟩⟩
    exact (Finset.dvd_prod_of_mem (fun Q : S ↦ Q.1.ramificationIdx A)
      (Finset.mem_univ ⟨P, hP⟩)).trans (dvd_mul_left e₀ d)
  obtain ⟨hDVR, hunr⟩ := h.isUnramifiedWRT_of_pow_eq_of_irreducible (K := K) hπ hβ hgen hdvd
  have hint : IsIntegral L α :=
    (IsIntegral.of_pow (Nat.pos_of_ne_zero hde) (hα ▸ isIntegral_algebraMap (R := A))).tower_top
  have : FiniteDimensional L E := adjoin.finiteDimensional hint
  have : FiniteDimensional K E := .trans K L E
  exact ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, β, hDVR, hβ, .right K K⟮β⟯ E, isSeparable_adjoin_of_adjoin_eq_top hgen, hunr⟩

/-- **Kummer characterization of tame ramification** (Stacks, Lemma 15.116.7, `(1) ⇔ (2)`): `L` is
tamely ramified with respect to `A` iff `L` embeds over `K` into a finite separable extension of
`K(π ^ (1 / e))` unramified with respect to `A[π ^ (1 / e)]`, for some `e` invertible in the
residue field of `A`. -/
@[stacks 0EXW "(1) ⇔ (2)"]
theorem isTamelyRamifiedWRT_iff_exists_kummer {π : A} (hπ : Irreducible π) :
    IsTamelyRamifiedWRT A L ↔
      ∃ (e : ℕ) (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Algebra A E)
        (_ : IsScalarTower A K E) (_ : Algebra L E) (_ : IsScalarTower K L E) (β : E)
        (_ : IsDiscreteValuationRing (integralClosure A K⟮β⟯)),
        IsUnit (e : A ⧸ maximalIdeal A) ∧ β ^ e = algebraMap A E π ∧
          FiniteDimensional K⟮β⟯ E ∧ Algebra.IsSeparable K⟮β⟯ E ∧
          IsUnramifiedWRT (integralClosure A K⟮β⟯) E := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨e₀, he₀, H⟩ := exists_forall_kummer_of_isTamelyRamifiedWRT K hπ h
    have h1 : IsUnit ((1 : ℕ) : A ⧸ maximalIdeal A) := by rw [Nat.cast_one]; exact isUnit_one
    obtain ⟨E, i₁, i₂, i₃, i₄, i₅, i₆, β, hDVR, hβ, hfin, hsep, hunr⟩ := H 1 h1
    rw [one_mul] at hβ
    exact ⟨e₀, E, i₁, i₂, i₃, i₄, i₅, i₆, β, hDVR, he₀, hβ, hfin, hsep, hunr⟩
  · rintro ⟨e, E, _, _, _, _, _, _, β, _, he, hβ, -, -, hunr⟩
    exact IsDiscreteValuationRing.isTamelyRamifiedWRT_of_isUnramifiedWRT_of_pow_eq_of_irreducible
      hπ he hβ hunr

/-- **Kummer characterization of tame ramification for arbitrary multiples** (Stacks,
Lemma 15.116.7, `(1) ⇔ (3)`): `L` is tamely ramified with respect to `A` iff there exists `e₀`
invertible in `κ_A` such that for every `d` invertible in `κ_A`, `L` embeds over `K` into a finite
separable extension of `K(π ^ (1 / (d * e₀)))` unramified with respect to
`A[π ^ (1 / (d * e₀))]`. -/
@[stacks 0EXW "(1) ⇔ (3)"]
theorem isTamelyRamifiedWRT_iff_exists_forall_kummer {π : A} (hπ : Irreducible π) :
    IsTamelyRamifiedWRT A L ↔
      ∃ e₀ : ℕ, IsUnit (e₀ : A ⧸ maximalIdeal A) ∧
        ∀ d : ℕ, IsUnit (d : A ⧸ maximalIdeal A) →
          ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Algebra A E)
            (_ : IsScalarTower A K E) (_ : Algebra L E) (_ : IsScalarTower K L E) (β : E)
            (_ : IsDiscreteValuationRing (integralClosure A K⟮β⟯)),
            β ^ (d * e₀) = algebraMap A E π ∧ FiniteDimensional K⟮β⟯ E ∧
              Algebra.IsSeparable K⟮β⟯ E ∧ IsUnramifiedWRT (integralClosure A K⟮β⟯) E := by
  refine ⟨exists_forall_kummer_of_isTamelyRamifiedWRT K hπ, ?_⟩
  rintro ⟨e₀, he₀, H⟩
  have h1 : IsUnit ((1 : ℕ) : A ⧸ maximalIdeal A) := by rw [Nat.cast_one]; exact isUnit_one
  obtain ⟨E, _, _, _, _, _, _, β, _, hβ, -, -, hunr⟩ := H 1 h1
  rw [one_mul] at hβ
  exact IsDiscreteValuationRing.isTamelyRamifiedWRT_of_isUnramifiedWRT_of_pow_eq_of_irreducible
    hπ he₀ hβ hunr

/-- **Kummer characterization of tamely ramified extensions** (Stacks, Lemma 15.116.7). Let `A`
be a discrete valuation ring with fraction field `K` and uniformizer `π`, and let `L / K` be a
finite separable extension. The following are equivalent:
1. `L` is tamely ramified with respect to `A`;
2. there exist `e` invertible in the residue field `κ_A` and an extension `E` of `L` containing an
   `e`-th root `β` of `π` such that `E / K(β)` is finite separable and unramified with respect to
   the integral closure `A[β]` of `A` in `K(β)`;
3. there exists `e₀` invertible in `κ_A` such that for every `d` invertible in `κ_A`, there exists
   such an extension `E` with exponent `d * e₀`. -/
@[stacks 0EXW]
theorem isTamelyRamifiedWRT_tfae {π : A} (hπ : Irreducible π) :
    List.TFAE
      [IsTamelyRamifiedWRT A L,
       ∃ (e : ℕ) (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Algebra A E)
         (_ : IsScalarTower A K E) (_ : Algebra L E) (_ : IsScalarTower K L E) (β : E)
         (_ : IsDiscreteValuationRing (integralClosure A K⟮β⟯)),
         IsUnit (e : A ⧸ maximalIdeal A) ∧ β ^ e = algebraMap A E π ∧
           FiniteDimensional K⟮β⟯ E ∧ Algebra.IsSeparable K⟮β⟯ E ∧
           IsUnramifiedWRT (integralClosure A K⟮β⟯) E,
       ∃ e₀ : ℕ, IsUnit (e₀ : A ⧸ maximalIdeal A) ∧
         ∀ d : ℕ, IsUnit (d : A ⧸ maximalIdeal A) →
           ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Algebra A E)
             (_ : IsScalarTower A K E) (_ : Algebra L E) (_ : IsScalarTower K L E) (β : E)
             (_ : IsDiscreteValuationRing (integralClosure A K⟮β⟯)),
             β ^ (d * e₀) = algebraMap A E π ∧ FiniteDimensional K⟮β⟯ E ∧
               Algebra.IsSeparable K⟮β⟯ E ∧ IsUnramifiedWRT (integralClosure A K⟮β⟯) E] :=
  have tfae_three {P₁ P₂ P₃ : Prop} (h₁₂ : P₁ ↔ P₂) (h₁₃ : P₁ ↔ P₃) : List.TFAE [P₁, P₂, P₃] := by
    tfae_have 1 ↔ 2 := h₁₂
    tfae_have 1 ↔ 3 := h₁₃
    tfae_finish
  tfae_three (isTamelyRamifiedWRT_iff_exists_kummer K hπ)
    (isTamelyRamifiedWRT_iff_exists_forall_kummer K hπ)

end Characterization

end TauCeti.Algebra
