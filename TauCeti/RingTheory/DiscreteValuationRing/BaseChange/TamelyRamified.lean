/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Unramified.Field
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.FieldTheory.IntermediateField.ScalarTower
import TauCeti.RingTheory.AdjoinRoot.Basic
import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Basic
import TauCeti.RingTheory.DiscreteValuationRing.BaseChange.Characterization
import TauCeti.RingTheory.DiscreteValuationRing.BaseChange.Unramified
import TauCeti.RingTheory.DiscreteValuationRing.Kummer
import TauCeti.RingTheory.IntegralClosure.TensorProduct

/-!
# Base change of tamely ramified extensions of a discrete valuation ring

Let `A → A'` be an extension of discrete valuation rings with fraction fields `K ⊆ K'`, and let
`L / K` be a finite separable extension. If `L` is tamely ramified with respect to `A`, then every
field quotient `L'` of `K' ⊗[K] L` is tamely ramified with respect to `A'` (Stacks, Lemma 15.116.9,
the tamely ramified half; the unramified half is `TauCeti.Algebra.IsUnramifiedWRT.baseChange`).

As in `TauCeti.RingTheory.DiscreteValuationRing.BaseChange.Unramified`, the homomorphism `A → A'`
need not be local: only the injectivity of `A → K → K'` is used, so the case where a uniformizer
`π` of `A` becomes a unit in `A'` is included without a separate branch.

The proof follows Stacks using the Kummer characterization `isTamelyRamifiedWRT_iff_exists_kummer`:
1. Embed `L` over `K` into a finite separable extension `E` of `K(γ)` unramified over
   `A₁ = A[γ]`, where `γ ^ e = π` and `e` is invertible in the residue field of `A` (hence in `A`
   and `A'`).
2. Write `π = u π' ^ m` in `A'` for a uniformizer `π'` of `A'` and a unit `u ∈ A'ˣ` (`m = 0` when
   `π` is a unit in `A'`). Extending `L → L' → Ω' := AlgebraicClosure L'` to `σ : E → Ω'`, pick an
   `e`-th root `β` of `π'` in `Ω'` and set `v := σ γ / β ^ m`, so `v ^ e = u` and
   `σ γ = v β ^ m`.
3. Over `A'₁ := integralClosure A' K'(β)`, the standard cover `D₀ := A'₁[y] / (y ^ e - u)` is
   finite étale, and `A₁ ≅ A[X] / (X ^ e - π)` maps to `D₀` by `γ ↦ y β ^ m`. Tensoring with the
   finite étale `A₁`-algebra `B_E := integralClosure A₁ E` produces a finite étale `A'₁`-algebra
   `D := D₀ ⊗[A₁] B_E` whose generic fibre maps into `Ω'` with image a field `M'` containing `L'`.
4. By `AlgHom.isUnramifiedWRT_of_surjective`, `M'` is unramified over `A'₁`, hence tamely ramified
   over `A'` by `IsTamelyRamifiedWRT.trans`, and `IsTamelyRamifiedWRT.tower_bot` descends tameness
   to `L'`.

## Main results

* `TauCeti.Algebra.IsTamelyRamifiedWRT.baseChange`: every field quotient `L'` of `K' ⊗[K] L` is
  tamely ramified with respect to `A'` when `L` is tamely ramified with respect to `A`.

## References

* [Stacks Project, Lemma 15.116.9](https://stacks.math.columbia.edu/tag/0EXY).
-/

public section

open scoped TensorProduct
open _root_.IntermediateField IsLocalRing Polynomial

namespace TauCeti.Algebra

section Helpers

universe u

/-- Given `γ ^ e = π` over a discrete valuation ring `A` with fraction field `K` and a factorization
`π = u' * (b' ^ e) ^ m` in an `A`-algebra `R'` with `e ≠ 0`, `A₁ = integralClosure A K⟮γ⟯` maps to
`standardTameCover R' u' e` compatibly with `σ : E →ₐ[A] Ω'` and evaluation of the root at `v`. -/
private theorem exists_algHom_integralClosure_standardTameCover {A K E R' Ω' : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    {π : A} {e m : ℕ} {γ : E} (hπ : Irreducible π) (he0 : e ≠ 0) (hγ : γ ^ e = algebraMap A E π)
    [CommRing R'] [Algebra A R'] [CommRing Ω'] [Algebra R' Ω'] [Algebra A Ω']
    [IsScalarTower A R' Ω'] (σ : E →ₐ[A] Ω') {u' b' : R'} {v : Ω'}
    (hπR' : algebraMap A R' π = u' * (b' ^ e) ^ m)
    (hv : v ^ e = algebraMap R' Ω' u') (hvγ : v * algebraMap R' Ω' b' ^ m = σ γ) :
    ∃ (f₁ : integralClosure A K⟮γ⟯ →ₐ[A] standardTameCover R' u' e)
      (ψ₀ : standardTameCover R' u' e →ₐ[R'] Ω'),
      ∀ a₁ : integralClosure A K⟮γ⟯,
        ψ₀ (f₁ a₁) = σ (algebraMap (integralClosure A K⟮γ⟯) E a₁) := by
  let γK : K⟮γ⟯ := AdjoinSimple.gen K γ
  have hγK : γK ^ e = algebraMap A K⟮γ⟯ π := (algebraMap K⟮γ⟯ E).injective <| by
    rw [map_pow, AdjoinSimple.algebraMap_gen, hγ, ← IsScalarTower.algebraMap_apply]
  have hgenγ : K⟮γK⟯ = ⊤ := adjoin_adjoinSimple_gen_eq_top γ
  let A₁ := integralClosure A K⟮γ⟯
  let D₀ := standardTameCover R' u' e
  have := FaithfulSMul.trans A K K⟮γ⟯
  have : Module.IsTorsionFree A K⟮γ⟯ := FaithfulSMul.to_isTorsionFree ..
  have : Module.IsTorsionFree A A₁ := (FaithfulSMul.tower_bot A A₁ K⟮γ⟯).to_isTorsionFree
  have hintγ : IsIntegral A γK :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero he0) (hγK ▸ isIntegral_algebraMap)
  have hadj := IsDiscreteValuationRing.integralClosure_eq_adjoin_of_pow_eq_of_irreducible
    hπ hγK hgenγ
  let pb : PowerBasis A A₁ :=
    (Algebra.adjoin.powerBasis' hintγ).map (Subalgebra.equivOfEq _ _ hadj.symm)
  have hpb_coe : ((pb.gen : A₁) : K⟮γ⟯) = γK := by simp [pb]
  have hpb_pow : pb.gen ^ e = algebraMap A A₁ π := Subtype.ext (by simpa [hpb_coe] using hγK)
  have hmin : minpoly A pb.gen = X ^ e - C π :=
    IsDiscreteValuationRing.minpoly_eq_of_pow_eq_of_irreducible hπ hpb_pow
  let y : D₀ := AdjoinRoot.root (X ^ e - C u') * algebraMap R' D₀ b' ^ m
  have hy : aeval y (minpoly A pb.gen) = 0 := by
    rw [hmin, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero,
      IsScalarTower.algebraMap_apply A R' D₀, hπR', map_mul, mul_pow,
      AdjoinRoot.root_X_pow_sub_C_pow, ← AdjoinRoot.algebraMap_eq, ← map_pow, ← map_pow,
      ← pow_mul, ← pow_mul, mul_comm m e]
  let f₁ : A₁ →ₐ[A] D₀ := pb.lift y hy
  let ψ₀ : D₀ →ₐ[R'] Ω' :=
    AdjoinRoot.liftAlgHom (X ^ e - C u') (Algebra.ofId R' Ω') v (by simp [hv])
  have hψ₀_root : ψ₀ (AdjoinRoot.root (X ^ e - C u')) = v :=
    AdjoinRoot.liftAlgHom_root (X ^ e - C u') (Algebra.ofId R' Ω') v _
  have : IsScalarTower A A₁ E := .to₁₂₄ A A₁ K⟮γ⟯ E
  have hcomp : (ψ₀.restrictScalars A).comp f₁ = σ.comp (IsScalarTower.toAlgHom A A₁ E) :=
    pb.algHom_ext <| by
      rw [AlgHom.comp_apply, AlgHom.coe_restrictScalars', PowerBasis.lift_gen, map_mul, map_pow,
        hψ₀_root, AlgHom.commutes, hvγ, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
        Subalgebra.algebraMap_eq, RingHom.comp_apply, RingHom.coe_coe, Subalgebra.coe_val,
        hpb_coe, AdjoinSimple.algebraMap_gen]
  exact ⟨f₁, ψ₀, fun a₁ ↦ DFunLike.congr_fun hcomp a₁⟩

/-- The image in an ambient field `Ω'` of the generic fibre of a finite étale algebra `D` over a
discrete valuation ring `R'` is an intermediate field unramified with respect to `R'`. -/
private theorem exists_intermediateField_isUnramifiedWRT_of_etale {R' K'₁ D Ω' : Type*}
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Field K'₁] [Algebra R' K'₁] [IsFractionRing R' K'₁]
    [CommRing D] [Algebra R' D] [Algebra.Etale R' D] [Module.Finite R' D]
    [Field Ω'] [Algebra R' Ω'] [Algebra K'₁ Ω'] [IsScalarTower R' K'₁ Ω'] (ψ : D →ₐ[R'] Ω') :
    ∃ M' : IntermediateField K'₁ Ω', IsUnramifiedWRT R' M' ∧ Set.range ψ ⊆ (M' : Set Ω') := by
  let χ₀ : K'₁ ⊗[R'] D →ₐ[K'₁] Ω' :=
    Algebra.TensorProduct.lift (Algebra.ofId K'₁ Ω') ψ fun _ _ ↦ .all _ _
  have : Module.Finite K'₁ χ₀.range :=
    .of_surjective χ₀.rangeRestrict.toLinearMap χ₀.rangeRestrict_surjective
  have hField : IsField χ₀.range := isField_of_isIntegral_of_isField' (Field.toIsField K'₁)
  let M' : IntermediateField K'₁ Ω' :=
    { χ₀.range with
      inv_mem' := fun {x} hx ↦ by
        rcases eq_or_ne x 0 with rfl | hx0
        · rw [inv_zero]
          exact χ₀.range.zero_mem
        · have hx' : (⟨x, hx⟩ : χ₀.range) ≠ 0 := fun h ↦ hx0 (congrArg Subtype.val h)
          obtain ⟨y, hy⟩ := hField.mul_inv_cancel hx'
          have hy' : x * (y : Ω') = 1 := congrArg Subtype.val hy
          exact (mul_eq_one_iff_inv_eq₀ hx0).mp hy' ▸ y.2 }
  let χ : K'₁ ⊗[R'] D →ₐ[K'₁] M' := χ₀.codRestrict M'.toSubalgebra fun z ↦ ⟨z, rfl⟩
  have hχ : Function.Surjective χ := fun ⟨_, z, rfl⟩ ↦ ⟨z, rfl⟩
  refine ⟨M', χ.isUnramifiedWRT_of_surjective hχ, ?_⟩
  rintro _ ⟨d, rfl⟩
  exact ⟨1 ⊗ₜ d, by simp [χ₀]⟩

/-- Given a finite étale `R'`-algebra `D₀` receiving a ring map `f₁ : A₁ →+* D₀` from a discrete
valuation ring `A₁`, and a finite separable extension `E` of the fraction field `K₁` of `A₁`
unramified over `A₁`, the image in `Ω'` of the generic fibre of `D₀ ⊗[A₁] integralClosure A₁ E`
under `(ψ₀, σ)` is an intermediate field `M' / K'₁` unramified over `R'`. -/
private theorem exists_intermediateField_isUnramifiedWRT_of_etale_tensor
    {A₁ K₁ E R' D₀ K'₁ Ω' : Type*}
    [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁]
    [Field K₁] [Algebra A₁ K₁] [IsFractionRing A₁ K₁]
    [Field E] [Algebra K₁ E] [Algebra A₁ E] [IsScalarTower A₁ K₁ E]
    [FiniteDimensional K₁ E] [Algebra.IsSeparable K₁ E] (hunr : IsUnramifiedWRT A₁ E)
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [CommRing D₀] [Algebra R' D₀] [Algebra.Etale R' D₀] [Module.Finite R' D₀]
    [Field K'₁] [Algebra R' K'₁] [IsFractionRing R' K'₁]
    [Field Ω'] [Algebra R' Ω'] [Algebra K'₁ Ω'] [IsScalarTower R' K'₁ Ω']
    (f₁ : A₁ →+* D₀) (ψ₀ : D₀ →ₐ[R'] Ω') (σ : E →+* Ω')
    (hcomp : ∀ a₁ : A₁, ψ₀ (f₁ a₁) = σ (algebraMap A₁ E a₁)) :
    ∃ M' : IntermediateField K'₁ Ω', IsUnramifiedWRT R' M' ∧
      ∀ x : integralClosure A₁ E, σ (x : E) ∈ M' := by
  have : Algebra.Etale A₁ (integralClosure A₁ E) := (isUnramifiedWRT_iff_etale A₁ K₁ E).mp hunr
  have : Module.Finite A₁ (integralClosure A₁ E) := IsIntegralClosure.finite A₁ K₁ E _
  let : Algebra A₁ D₀ := f₁.toAlgebra
  have : SMulCommClass R' A₁ D₀ := ⟨fun _ _ _ ↦ by simp [Algebra.smul_def, mul_left_comm]⟩
  have : Algebra.Etale D₀ (D₀ ⊗[A₁] integralClosure A₁ E) := Algebra.Etale.baseChange ..
  have : Algebra.Etale R' (D₀ ⊗[A₁] integralClosure A₁ E) :=
    .comp R' D₀ (D₀ ⊗[A₁] integralClosure A₁ E)
  have : Module.Finite R' (D₀ ⊗[A₁] integralClosure A₁ E) :=
    .trans D₀ (D₀ ⊗[A₁] integralClosure A₁ E)
  let : Algebra A₁ Ω' := (ψ₀.toRingHom.comp f₁).toAlgebra
  let ψ₀' : D₀ →ₐ[A₁] Ω' := { ψ₀.toRingHom with commutes' := fun _ ↦ rfl }
  let g_E : integralClosure A₁ E →ₐ[A₁] Ω' :=
    { σ.comp (integralClosure A₁ E).val.toRingHom with
      commutes' := fun a₁ ↦ (hcomp a₁).symm }
  let ψD₁ : D₀ ⊗[A₁] integralClosure A₁ E →ₐ[A₁] Ω' :=
    Algebra.TensorProduct.lift ψ₀' g_E fun _ _ ↦ .all _ _
  have hψD₁ : ∀ r' : R',
      ψD₁ (algebraMap R' (D₀ ⊗[A₁] integralClosure A₁ E) r') = algebraMap R' Ω' r' := fun r' ↦ by
    rw [IsScalarTower.algebraMap_apply R' D₀ (D₀ ⊗[A₁] integralClosure A₁ E),
      Algebra.TensorProduct.algebraMap_apply]
    simp [ψD₁, ψ₀']
  let ψD : D₀ ⊗[A₁] integralClosure A₁ E →ₐ[R'] Ω' :=
    { ψD₁.toRingHom with commutes' := hψD₁ }
  obtain ⟨M', hM'unr, hM'sub⟩ := exists_intermediateField_isUnramifiedWRT_of_etale (K'₁ := K'₁) ψD
  exact ⟨M', hM'unr, fun x ↦ hM'sub ⟨1 ⊗ₜ x, by simp [ψD, ψD₁, g_E]⟩⟩

/-- Factoring `π = u * π' ^ m` in `A'` and choosing an `e`-th root `β` of `π'` in an algebraically
closed extension `Ω'` yields `v := σ γ / β ^ m` satisfying `v ^ e = u` and `v * β ^ m = σ γ`. -/
private theorem exists_root_and_div_pow_eq {A K E A' K' Ω' : Type*}
    [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing E] [Algebra A E] {π : A} {e : ℕ} {γ : E}
    (hπ : Irreducible π) (he0 : e ≠ 0) (hγ : γ ^ e = algebraMap A E π)
    [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A']
    [Field K'] [Algebra A' K'] [IsFractionRing A' K']
    [Algebra A A'] [Algebra A K'] [Algebra K K'] [IsScalarTower A A' K'] [IsScalarTower A K K']
    [Field Ω'] [IsAlgClosed Ω'] [Algebra K' Ω'] [Algebra A' Ω'] [IsScalarTower A' K' Ω']
    [Algebra A Ω'] [IsScalarTower A A' Ω'] (σ : E →ₐ[A] Ω') {π' : A'} (hπ' : Irreducible π') :
    ∃ (m : ℕ) (u : A'ˣ) (β v : Ω'),
      algebraMap A A' π = u * π' ^ m ∧ β ^ e = algebraMap A' Ω' π' ∧
        v ^ e = algebraMap A' Ω' u ∧ v * β ^ m = σ γ := by
  have hπA'0 : algebraMap A A' π ≠ 0 := fun h0 ↦ hπ.ne_zero <|
    (IsFractionRing.to_map_eq_zero_iff (K := K)).mp <|
      (map_eq_zero_iff _ (RingHom.injective (algebraMap K K'))).mp <| by
        rw [← IsScalarTower.algebraMap_apply A K K', IsScalarTower.algebraMap_apply A A' K', h0,
          map_zero]
  obtain ⟨m, u, hπA'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπA'0 hπ'
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A' Ω' π') (Nat.pos_of_ne_zero he0)
  have hβ0 : β ≠ 0 := fun h0 ↦ hπ'.ne_zero <| (IsFractionRing.to_map_eq_zero_iff (K := K')).mp <|
    (RingHom.injective (algebraMap K' Ω')).eq_iff.mp <| by
      rw [map_zero, ← IsScalarTower.algebraMap_apply A' K' Ω', ← hβ, h0, zero_pow he0]
  let v : Ω' := σ γ / β ^ m
  refine ⟨m, u, β, v, hπA', hβ, ?_, div_mul_cancel₀ _ (pow_ne_zero m hβ0)⟩
  have hγΩ' : (σ γ) ^ e = algebraMap A' Ω' u * algebraMap A' Ω' π' ^ m := by
    rw [← map_pow, hγ, σ.commutes, IsScalarTower.algebraMap_apply A A' Ω', hπA', map_mul, map_pow]
  rw [div_pow, hγΩ', ← pow_mul, mul_comm m e, pow_mul, hβ,
    mul_div_cancel_right₀ _ (pow_ne_zero m (hβ ▸ pow_ne_zero e hβ0))]

/-- Adjoining an `e`-th root `β` of a uniformizer of `A'` in an algebraically closed extension `Ω'`
and tensoring over `A'[β]` produces a `K'`-subfield `M'` of `Ω'`, tamely ramified over `A'`, whose
image contains `σ (integralClosure A₁ E)`. -/
private theorem exists_isTamelyRamifiedWRT_of_kummer_witness {A K E A' K' : Type*} {Ω' : Type u}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    {π : A} {e : ℕ} {γ : E} [IsDiscreteValuationRing (integralClosure A K⟮γ⟯)]
    [FiniteDimensional K K⟮γ⟯] [FiniteDimensional K⟮γ⟯ E] [Algebra.IsSeparable K⟮γ⟯ E]
    (hπ : Irreducible π) (heA : IsUnit (e : A)) (hγ : γ ^ e = algebraMap A E π)
    (hunr : IsUnramifiedWRT (integralClosure A K⟮γ⟯) E)
    [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A']
    [Field K'] [Algebra A' K'] [IsFractionRing A' K']
    [Algebra A A'] [Algebra A K'] [Algebra K K'] [IsScalarTower A A' K'] [IsScalarTower A K K']
    [Field Ω'] [IsAlgClosed Ω'] [Algebra K' Ω'] [Algebra A' Ω'] [IsScalarTower A' K' Ω']
    [Algebra A Ω'] [IsScalarTower A A' Ω'] (σ : E →ₐ[A] Ω') :
    ∃ (M' : Type u) (_ : Field M') (_ : Algebra K' M') (_ : Algebra A' M')
      (_ : IsScalarTower A' K' M') (ι : M' →ₐ[K'] Ω'),
      IsTamelyRamifiedWRT A' M' ∧
        ∀ x : integralClosure (integralClosure A K⟮γ⟯) E, σ (x : E) ∈ Set.range ι := by
  have he0 : e ≠ 0 := by rintro rfl; simp at heA
  have : NeZero e := ⟨he0⟩
  have heA' : IsUnit (e : A') := map_natCast (algebraMap A A') e ▸ heA.map (algebraMap A A')
  obtain ⟨π', hπ'⟩ := IsDiscreteValuationRing.exists_irreducible A'
  obtain ⟨m, u, β, v, hπA', hβ, hv, hvγ⟩ :=
    exists_root_and_div_pow_eq (K := K) (K' := K') hπ he0 hγ σ hπ'
  let K'₁ := K'⟮β⟯
  let βK : K'₁ := AdjoinSimple.gen K' β
  have hβK : βK ^ e = algebraMap A' K'₁ π' := (algebraMap K'₁ Ω').injective <| by
    rw [map_pow, AdjoinSimple.algebraMap_gen, hβ, ← IsScalarTower.algebraMap_apply A' K'₁ Ω']
  have hgenβ : K'⟮βK⟯ = ⊤ := adjoin_adjoinSimple_gen_eq_top β
  let A'₁ := integralClosure A' K'₁
  have : IsDiscreteValuationRing A'₁ :=
    IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible
      hπ' hβK hgenβ
  have hK'₁ : IsTamelyRamifiedWRT A' K'₁ :=
    (IsDiscreteValuationRing.isTamelyRamifiedWRT_iff_of_pow_eq_of_irreducible hπ' hβK hgenβ).mpr
      (map_natCast (IsLocalRing.residue A') e ▸ heA'.map (IsLocalRing.residue A'))
  have hdegβ := IsDiscreteValuationRing.finrank_eq_of_pow_eq_of_irreducible hπ' hβK hgenβ
  have : FiniteDimensional K' K'₁ := Module.finite_of_finrank_pos (hdegβ ▸ Nat.pos_of_ne_zero he0)
  have : IsFractionRing A'₁ K'₁ :=
    IsIntegralClosure.isFractionRing_of_finite_extension A' K' K'₁ A'₁
  have : IsScalarTower A' A'₁ Ω' := .to₁₂₄ A' A'₁ K'₁ Ω'
  let : Algebra A A'₁ := ((algebraMap A' A'₁).comp (algebraMap A A')).toAlgebra
  have : IsScalarTower A A' A'₁ := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A A'₁ Ω' := .to₁₃₄ A A' A'₁ Ω'
  let b' : A'₁ := ⟨βK, IsIntegral.of_pow (Nat.pos_of_ne_zero he0) (hβK ▸ isIntegral_algebraMap)⟩
  have hb'e : b' ^ e = algebraMap A' A'₁ π' := Subtype.ext hβK
  obtain ⟨f₁, ψ₀, hcomp⟩ := exists_algHom_integralClosure_standardTameCover (K := K) (R' := A'₁)
    hπ he0 hγ σ (by rw [IsScalarTower.algebraMap_apply A A' A'₁, hπA', map_mul, map_pow, hb'e])
    (by rwa [← IsScalarTower.algebraMap_apply A' A'₁ Ω']) hvγ
  have : IsFractionRing (integralClosure A K⟮γ⟯) K⟮γ⟯ :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K K⟮γ⟯ _
  have : Algebra.Etale A'₁ (standardTameCover A'₁ (algebraMap A' A'₁ u) e) :=
    standardTameCover_etale (u.isUnit.map (algebraMap A' A'₁))
      (map_natCast (algebraMap A' A'₁) e ▸ heA'.map (algebraMap A' A'₁))
  obtain ⟨M', hM'unr, hM'sub⟩ := exists_intermediateField_isUnramifiedWRT_of_etale_tensor
    (K₁ := K⟮γ⟯) (K'₁ := K'₁) hunr f₁.toRingHom ψ₀ σ.toRingHom hcomp
  have : IsScalarTower A' K' M' := .of_algebraMap_eq fun a' ↦
    Subtype.ext (IsScalarTower.algebraMap_apply A' K' Ω' a')
  let ι : M' →ₐ[K'] Ω' :=
    (M'.restrictScalars K').val.comp (IntermediateField.restrictScalarsAlgEquiv K' M').symm.toAlgHom
  exact ⟨M', inferInstance, inferInstance, inferInstance, inferInstance, ι,
    hK'₁.trans hM'unr.isTamelyRamifiedWRT, fun x ↦ ⟨⟨σ x, hM'sub x⟩, by simp [ι]⟩⟩

/-- If `φ : K' ⊗[K] L →ₐ[K'] L'` is surjective and the image in `Ω'` of `φ(1 ⊗ integralClosure A L)`
lies inside the image of a field `M'` tamely ramified with respect to `A'`, then `L'` embeds into
`M'` over `K'` and `A'` and hence is tamely ramified with respect to `A'`. -/
private theorem isTamelyRamifiedWRT_of_forall_integralClosure_mem {A K L A' K' L' M' Ω' : Type*}
    [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A']
    [Field K'] [Algebra A' K'] [IsFractionRing A' K'] [Algebra K K']
    [Field L'] [Algebra K' L'] [Algebra A' L'] [IsScalarTower A' K' L']
    (φ : K' ⊗[K] L →ₐ[K'] L') (hφ : Function.Surjective φ)
    [Field Ω'] [Algebra K' Ω'] [Algebra L' Ω'] [IsScalarTower K' L' Ω']
    [Field M'] [Algebra K' M'] [Algebra A' M'] [IsScalarTower A' K' M']
    (ι : M' →ₐ[K'] Ω') (hM' : IsTamelyRamifiedWRT A' M')
    (hmem : ∀ b : integralClosure A L,
      algebraMap L' Ω' (φ ((1 : K') ⊗ₜ[K] (b : L))) ∈ Set.range ι) :
    IsTamelyRamifiedWRT A' L' := by
  have : FiniteDimensional K' L' := Module.Finite.of_surjective φ.toLinearMap hφ
  have : Algebra.FormallyUnramified K L := .of_isSeparable K L
  have hfu : Algebra.FormallyUnramified K' L' := .of_surjective φ hφ
  have : Algebra.IsSeparable K' L' := (Algebra.FormallyUnramified.iff_isSeparable K' L').mp hfu
  have hspan : Submodule.span K' (Set.range fun b : integralClosure A L ↦
      φ ((1 : K') ⊗ₜ[K] (b : L))) = ⊤ := by
    have hs := congrArg (Submodule.map φ.toLinearMap)
      (span_one_tmul_integralClosure_eq_top (A := A) (K := K) (L := L) (K' := K'))
    rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr hφ, ← Set.range_comp]
      at hs
    exact hs
  let W : Submodule K' L' :=
    ι.range.toSubmodule.comap (IsScalarTower.toAlgHom K' L' Ω').toLinearMap
  have hW : W = ⊤ := eq_top_iff.mpr <| hspan ▸ Submodule.span_le.mpr <| by
    rintro _ ⟨b, rfl⟩
    exact hmem b
  have hL'sub (x : L') : algebraMap L' Ω' x ∈ ι.range := by
    have hxW : x ∈ W := hW ▸ Submodule.mem_top
    exact hxW
  let j : L' →ₐ[K'] M' := (AlgEquiv.ofInjective ι ι.injective).symm.toAlgHom.comp
    ((IsScalarTower.toAlgHom K' L' Ω').codRestrict ι.range hL'sub)
  let : Algebra L' M' := j.toRingHom.toAlgebra
  have : IsScalarTower K' L' M' := .of_algebraMap_eq fun k' ↦ (j.commutes k').symm
  have : IsScalarTower A' L' M' := .of_algebraMap_eq fun a' ↦ by
    rw [IsScalarTower.algebraMap_apply A' K' L', ← IsScalarTower.algebraMap_apply K' L' M',
      ← IsScalarTower.algebraMap_apply A' K' M']
  exact hM'.tower_bot K'

end Helpers

section BaseChange

variable {A K L A' K' L' : Type*}
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A'] [Field K'] [Algebra A' K']
  [IsFractionRing A' K'] [Algebra A A'] [Algebra A K'] [Algebra K K'] [IsScalarTower A A' K']
  [IsScalarTower A K K'] [Field L'] [Algebra K' L'] [Algebra A' L'] [IsScalarTower A' K' L']

/-- Tamely ramified extensions of a discrete valuation ring are stable under base change: if `L`
is tamely ramified with respect to `A`, then every factor `L'` of `K' ⊗[K] L`, given by a
surjective `K'`-algebra map `φ : K' ⊗[K] L → L'`, is tamely ramified with respect to `A'`. -/
@[stacks 0EXY "tamely ramified case"]
theorem IsTamelyRamifiedWRT.baseChange (h : IsTamelyRamifiedWRT A L) (φ : K' ⊗[K] L →ₐ[K'] L')
    (hφ : Function.Surjective φ) : IsTamelyRamifiedWRT A' L' := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨e, E, _, _, _, _, _, _, γ, _, heκ, hγ, _, _, hunr⟩ :=
    (isTamelyRamifiedWRT_iff_exists_kummer K hπ).mp h
  have heA : IsUnit (e : A) :=
    (isUnit_map_iff (IsLocalRing.residue A) (e : A)).mp (by rw [map_natCast]; exact heκ)
  have he0 : e ≠ 0 := by rintro rfl; simp at heA
  let : Algebra K L' := ((algebraMap K' L').comp (algebraMap K K')).toAlgebra
  have : IsScalarTower K K' L' := .of_algebraMap_eq fun _ ↦ rfl
  let : Algebra A L' := ((algebraMap A' L').comp (algebraMap A A')).toAlgebra
  have : IsScalarTower A A' L' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A K L' := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply A A' K',
      ← IsScalarTower.algebraMap_apply A K K', ← IsScalarTower.algebraMap_apply A' K' L']
  let Ω' := AlgebraicClosure L'
  have : IsScalarTower K K' Ω' := .to₁₂₄ K K' L' Ω'
  have : IsScalarTower A' K' Ω' := .to₁₂₄ A' K' L' Ω'
  have : IsScalarTower A A' Ω' := .to₁₂₄ A A' L' Ω'
  have : IsScalarTower A K Ω' := .to₁₂₄ A K L' Ω'
  let ιL : L →ₐ[K] Ω' := (IsScalarTower.toAlgHom K L' Ω').comp
    ((φ.restrictScalars K).comp Algebra.TensorProduct.includeRight)
  let : Algebra L Ω' := ιL.toRingHom.toAlgebra
  have hdegγ := IsDiscreteValuationRing.finrank_adjoin_of_pow_eq_of_irreducible (K := K) hπ hγ
  have : FiniteDimensional K K⟮γ⟯ := Module.finite_of_finrank_pos (hdegγ ▸ Nat.pos_of_ne_zero he0)
  have : FiniteDimensional K E := .trans K K⟮γ⟯ E
  have : FiniteDimensional L E := .right K L E
  have : IsScalarTower A L E := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply K L E,
      ← IsScalarTower.algebraMap_apply A K E]
  have : IsScalarTower A L Ω' := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K L, RingHom.algebraMap_toAlgebra,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ιL.commutes,
      ← IsScalarTower.algebraMap_apply A K Ω']
  let σL : E →ₐ[L] Ω' := IsAlgClosed.lift
  let σ : E →ₐ[A] Ω' := σL.restrictScalars A
  obtain ⟨M', _, _, _, _, ι, hM'tame, hψ⟩ :=
    exists_isTamelyRamifiedWRT_of_kummer_witness (K := K) (A' := A') (K' := K') hπ heA hγ hunr σ
  refine isTamelyRamifiedWRT_of_forall_integralClosure_mem (A := A) φ hφ ι hM'tame fun b ↦ ?_
  have : IsScalarTower A (integralClosure A K⟮γ⟯) E := .to₁₂₄ A (integralClosure A K⟮γ⟯) K⟮γ⟯ E
  have hbE : IsIntegral (integralClosure A K⟮γ⟯) (algebraMap L E (b : L)) :=
    (b.2.map (IsScalarTower.toAlgHom A L E)).tower_top
  have hσb : σ (algebraMap L E (b : L)) = algebraMap L' Ω' (φ ((1 : K') ⊗ₜ[K] (b : L))) :=
    σL.commutes b
  exact hσb ▸ hψ ⟨algebraMap L E b, hbE⟩

end BaseChange

end TauCeti.Algebra
