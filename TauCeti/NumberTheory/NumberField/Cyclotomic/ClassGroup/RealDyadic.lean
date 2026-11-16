/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.Tactic.NormNum.Prime
public import TauCeti.LinearAlgebra.Eigenspace.Separation
public import TauCeti.NumberTheory.NumberField.Cyclotomic.ClassGroup.TameDecomposition
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import TauCeti.NumberTheory.NumberField.Cyclotomic.MaximalRealSubfield
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Maximal real class modules, plus/minus eigenspaces, and the dyadic boundary

For any CM number field `K` (`NumberField.IsCMField K`) with maximal real subfield
`K⁺ = maximalRealSubfield K` and complex conjugation `c = IsCMField.complexConj K`, the
scalar-extended class modules over any commutative ring `R` satisfy

`relNorm ∘ extended = 2 • id` and `extended ∘ relNorm = id + c`.

Specializing `K` to `CyclotomicField m ℚ` (`2 < m`) identifies `c` on ideal classes with
`cyclotomicClassAction R m (-1)`.

When `R = ℤ_[p]` for an odd prime `p` (`p ≠ 2`), `2` is a unit in `ℤ_[p]`:
* the `p`-primary CM class module decomposes into complementary `+1` and `-1` eigenspaces of `c`;
* class extension from `K⁺` to `K` is a `ℤ_[p]`-linear isomorphism onto the `+1`-eigenspace
  (`cmRealClassEquivPlus`, `cyclotomicRealClassEquivPlus`);
* the `-1`-eigenspace coincides with the relative-norm kernel `ker relNorm`
  (`cmMinusEigenspace_eq_ker_relNorm`, `cyclotomicMinusEigenspace_eq_ker_relNorm`);
* at conductor `p ^ r` (`r ≥ 1`), the `+1`-eigenspace (hence the real `p`-primary class module)
  is the internal direct sum of the even tame eigenspaces (`Even k.val`), and the `-1`-eigenspace
  (`= ker relNorm`) is the internal direct sum of the odd tame eigenspaces (`Odd k.val`).

At the dyadic boundary `p = 2`, `2` is not invertible in `ℤ_[2]`, so the three minus-type
`ℤ_[2]`-modules — the relative-norm kernel `dyadicCMClassNormKer`, the anti-invariant submodule
`dyadicCMClassAntiInvariants` (`ker (1 + c)`), and the minus coinvariant quotient
`dyadicCMClassMinusQuotient` (`A ⧸ (1 + c) A`) — are kept distinct. We construct the canonical
comparison maps `ker N ↪ ker (1 + c) → A ⧸ (1 + c) A`, prove that all kernels and cokernels are
annihilated by `2`, and establish compatibility of the minus coinvariant quotients under relative
norm in the `2`-power cyclotomic tower (`2 ≤ r ≤ s`).

## Main definitions

* `TauCeti.cmComplexConjClassAction R K`: the `R`-linear action of `IsCMField.complexConj K` on
  `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))`.
* `TauCeti.cmRealClassEquivPlus`, `TauCeti.cyclotomicRealClassEquivPlus`: for `p ≠ 2`, the
  `ℤ_[p]`-linear equivalence from the `K⁺` class module to the `+1`-eigenspace of conjugation.
* `TauCeti.cyclotomicPlusEvenEquiv`, `TauCeti.cyclotomicMinusOddEquiv`: for `p ≠ 2`, the
  `ℤ_[p]`-linear equivalences identifying the `+1` and `-1` eigenspaces with the direct sums of
  even and odd tame eigenspaces.
* `TauCeti.dyadicCMClassNormKer`, `TauCeti.dyadicCMClassAntiInvariants`,
  `TauCeti.dyadicCMClassMinusQuotient` (and their `CyclotomicField (2 ^ r) ℚ` specializations):
  the three distinct dyadic minus-type class modules over `ℤ_[2]`.
* `TauCeti.dyadicNormKerToAntiInvariants`, `TauCeti.dyadicAntiInvariantsToMinusQuotient`,
  `TauCeti.dyadicCyclotomicMinusQuotientRelNorm`: dyadic comparison and tower-norm linear maps.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §§4.3, 10.1–10.3.
* R. Sharifi, *Iwasawa Theory*, §§1.3, 2.8, 4.2.
* The prime-level (`r = 1`) odd-prime decomposition into even and odd tame components parallels
  `BernoulliRegular.Idempotents` (`plusIdempotent_eq_sum_even`, `minusIdempotent_eq_sum_odd`) in
  AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, project `FltRegularBernoulli`).
-/

public section

open NumberField Algebra TensorProduct IsCyclotomicExtension.Rat
open scoped DirectSum

namespace TauCeti

attribute [local instance] instIsCyclotomicExtensionSingletonCyclotomicField instNeZeroPredPrime

local instance instFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-! ### CM-field conjugation and relative-norm identities -/

section CMGeneral

variable (R K : Type*) [CommRing R] [Field K] [NumberField K] [IsCMField K]

/-- The `R`-linear endomorphism of `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))` induced by complex
conjugation `IsCMField.complexConj K`. -/
noncomputable def cmComplexConjClassAction :
    Module.End R (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :=
  fieldAutClassAction R (IsCMField.complexConj K).toRingEquiv

@[simp]
theorem cmComplexConjClassAction_mul_self :
    cmComplexConjClassAction R K * cmComplexConjClassAction R K = 1 := by
  have hsq : (IsCMField.complexConj K).toRingEquiv * (IsCMField.complexConj K).toRingEquiv = 1 := by
    ext x
    exact IsCMField.complexConj_apply_apply K x
  rw [cmComplexConjClassAction, ← fieldAutClassAction_mul, hsq, fieldAutClassAction_one]

theorem involutive_cmComplexConjClassAction :
    Function.Involutive (cmComplexConjClassAction R K) := fun x ↦
  DFunLike.congr_fun (cmComplexConjClassAction_mul_self R K) x

@[simp]
theorem cmComplexConjClassAction_apply_apply (x : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :
    cmComplexConjClassAction R K (cmComplexConjClassAction R K x) = x :=
  involutive_cmComplexConjClassAction R K x

@[simp]
theorem cmComplexConjClassAction_extended
    (x : R ⊗[ℤ] Additive (ClassGroup (𝓞 (maximalRealSubfield K)))) :
    cmComplexConjClassAction R K
        (classGroupExtendedLinearMap R (maximalRealSubfield K) K x) =
      classGroupExtendedLinearMap R (maximalRealSubfield K) K x :=
  fieldAutClassAction_extendedLinearMap R (maximalRealSubfield K) K (IsCMField.complexConj K) x

@[simp]
theorem cmRelNorm_cmComplexConjClassAction (x : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :
    classGroupRelNormLinearMap R (maximalRealSubfield K) K
        (cmComplexConjClassAction R K x) =
      classGroupRelNormLinearMap R (maximalRealSubfield K) K x :=
  classGroupRelNormLinearMap_fieldAutClassAction R (maximalRealSubfield K) K
    (IsCMField.complexConj K) x

/-- In a CM field `K`, extending from `K⁺` and taking the relative norm multiplies by `2`. -/
theorem cmRelNorm_comp_extended :
    (classGroupRelNormLinearMap R (maximalRealSubfield K) K).comp
        (classGroupExtendedLinearMap R (maximalRealSubfield K) K) =
      (2 : ℕ) • LinearMap.id := by
  rw [classGroupRelNormLinearMap_comp_extendedLinearMap,
    IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K]

theorem cmRelNorm_extended (x : R ⊗[ℤ] Additive (ClassGroup (𝓞 (maximalRealSubfield K)))) :
    classGroupRelNormLinearMap R (maximalRealSubfield K) K
        (classGroupExtendedLinearMap R (maximalRealSubfield K) K x) =
      (2 : ℕ) • x :=
  DFunLike.congr_fun (cmRelNorm_comp_extended R K) x

/-- In a CM field `K`, taking the relative norm to `K⁺` and extending back equals `1 + c`. -/
theorem cmExtended_comp_relNorm :
    (classGroupExtendedLinearMap R (maximalRealSubfield K) K).comp
        (classGroupRelNormLinearMap R (maximalRealSubfield K) K) =
      LinearMap.id + cmComplexConjClassAction R K := by
  let j : Bool → Gal(K / maximalRealSubfield K) :=
    fun b ↦ if b then 1 else IsCMField.complexConj K
  have hj_inj : Function.Injective j := by
    rintro (_ | _) (_ | _) h
    · rfl
    · exact absurd h (IsCMField.complexConj_ne_one K)
    · exact absurd h.symm (IsCMField.complexConj_ne_one K)
    · rfl
  have hj_bij : Function.Bijective j :=
    (Fintype.bijective_iff_injective_and_card j).mpr ⟨hj_inj, by
      rw [Fintype.card_bool, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
        IsQuadraticExtension.finrank_eq_two]⟩
  rw [classGroupExtendedLinearMap_comp_relNormLinearMap,
    ← (Equiv.ofBijective j hj_bij).sum_comp, Fintype.sum_bool]
  have hone : (1 : Gal(K / maximalRealSubfield K)).toRingEquiv = 1 := rfl
  simp only [Equiv.ofBijective_apply, j, ↓reduceIte, Bool.false_eq_true, hone,
    fieldAutClassAction_one]
  rfl

theorem cmExtended_relNorm (x : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :
    classGroupExtendedLinearMap R (maximalRealSubfield K) K
        (classGroupRelNormLinearMap R (maximalRealSubfield K) K x) =
      x + cmComplexConjClassAction R K x :=
  DFunLike.congr_fun (cmExtended_comp_relNorm R K) x

end CMGeneral

/-! ### Cyclotomic fields of conductor `m > 2` as CM fields -/

section CyclotomicCM

/-- Every nontrivial rational cyclotomic field (`2 < m`) is a CM field. -/
theorem isCMField_cyclotomicField {m : ℕ} (hm : 2 < m) :
    have : NeZero m := ⟨by omega⟩
    IsCMField (CyclotomicField m ℚ) := by
  let _ : NeZero m := ⟨by omega⟩
  exact IsCyclotomicExtension.Rat.isCMField (CyclotomicField m ℚ) (S := {m})
    ⟨m, Set.mem_singleton m, hm⟩

/-- On `CyclotomicField m ℚ` (`2 < m`), complex conjugation agrees as a ring automorphism with the
Galois element attached to `-1 : (ZMod m)ˣ`. -/
theorem complexConj_toRingEquiv_cyclotomicField {m : ℕ} [NeZero m] (hm : 2 < m) :
    let _ : IsCMField (CyclotomicField m ℚ) := isCMField_cyclotomicField hm
    (IsCMField.complexConj (CyclotomicField m ℚ)).toRingEquiv =
      ((galEquivZMod m (CyclotomicField m ℚ)).symm (-1)).toRingEquiv := by
  let _ : IsCMField (CyclotomicField m ℚ) := isCMField_cyclotomicField hm
  let φ : CyclotomicField m ℚ →+* ℂ := Classical.choice inferInstance
  ext x
  apply φ.injective
  have h1 := IsCMField.complexEmbedding_complexConj (CyclotomicField m ℚ) φ x
  have h2 :=
    TauCeti.IsCyclotomicExtension.Rat.complexEmbedding_galEquivZMod_symm_neg_one_apply m φ x
  exact h1.trans h2.symm

/-- On scalar-extended ideal classes of `CyclotomicField m ℚ` (`2 < m`), `cmComplexConjClassAction`
equals `cyclotomicClassAction R m (-1)`. -/
theorem cmComplexConjClassAction_cyclotomicField (R : Type*) [CommRing R]
    {m : ℕ} [NeZero m] (hm : 2 < m) :
    let _ : IsCMField (CyclotomicField m ℚ) := isCMField_cyclotomicField hm
    cmComplexConjClassAction R (CyclotomicField m ℚ) = cyclotomicClassAction R m (-1) := by
  dsimp only
  let _ : IsCMField (CyclotomicField m ℚ) := isCMField_cyclotomicField hm
  rw [cmComplexConjClassAction, complexConj_toRingEquiv_cyclotomicField hm,
    cyclotomicClassAction_eq_cyclotomicFieldClassAction,
    cyclotomicFieldClassAction_eq_fieldAutClassAction]

end CyclotomicCM

/-! ### Odd-prime plus/minus comparison and even/odd tame eigenspaces (`p ≠ 2`) -/

section OddPrime

variable (p : ℕ) [Fact p.Prime]

/-- For an odd prime `p` and any CM field `K`, the `+1` and `-1` eigenspaces of complex conjugation
are complementary in `ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))`. -/
theorem isCompl_cmPlus_cmMinus (hp : p ≠ 2) (K : Type*) [Field K] [NumberField K] [IsCMField K] :
    IsCompl (Module.End.eigenspace (cmComplexConjClassAction ℤ_[p] K) 1)
      (Module.End.eigenspace (cmComplexConjClassAction ℤ_[p] K) (-1)) :=
  isCompl_eigenspace_one_neg_one (PadicInt.isUnit_two hp)
    (involutive_cmComplexConjClassAction ℤ_[p] K)

/-- **Odd-prime real-to-plus isomorphism for CM fields**: for `p ≠ 2`, class extension from `K⁺` to
`K` is a `ℤ_[p]`-linear equivalence onto the `+1`-eigenspace of complex conjugation, with inverse
`2⁻¹ • relNorm`. -/
noncomputable def cmRealClassEquivPlus (hp : p ≠ 2) (K : Type*) [Field K] [NumberField K]
    [IsCMField K] :
    (ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (maximalRealSubfield K)))) ≃ₗ[ℤ_[p]]
      Module.End.eigenspace (cmComplexConjClassAction ℤ_[p] K) 1 := by
  have h2 : IsUnit (2 : ℤ_[p]) := PadicInt.isUnit_two hp
  let fwd : (ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (maximalRealSubfield K)))) →ₗ[ℤ_[p]]
      Module.End.eigenspace (cmComplexConjClassAction ℤ_[p] K) 1 :=
    LinearMap.codRestrict _ (classGroupExtendedLinearMap ℤ_[p] (maximalRealSubfield K) K) fun x ↦ by
      rw [Module.End.mem_eigenspace_iff, one_smul]
      exact cmComplexConjClassAction_extended ℤ_[p] K x
  let bwd : Module.End.eigenspace (cmComplexConjClassAction ℤ_[p] K) 1 →ₗ[ℤ_[p]]
      (ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (maximalRealSubfield K)))) :=
    (((h2.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) •
      classGroupRelNormLinearMap ℤ_[p] (maximalRealSubfield K) K).comp (Submodule.subtype _)
  refine LinearEquiv.ofLinearMap fwd bwd ?_ ?_
  · refine LinearMap.ext fun y ↦ Subtype.ext ?_
    have hy : cmComplexConjClassAction ℤ_[p] K y.1 = y.1 := by
      simpa using Module.End.mem_eigenspace_iff.mp y.2
    change classGroupExtendedLinearMap ℤ_[p] (maximalRealSubfield K) K
      (((h2.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) •
        classGroupRelNormLinearMap ℤ_[p] (maximalRealSubfield K) K y.1) = y.1
    rw [map_smul, cmExtended_relNorm, hy, ← two_smul ℤ_[p] y.1, smul_smul, h2.val_inv_mul, one_smul]
  · refine LinearMap.ext fun x ↦ ?_
    change ((h2.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) •
      classGroupRelNormLinearMap ℤ_[p] (maximalRealSubfield K) K
        (classGroupExtendedLinearMap ℤ_[p] (maximalRealSubfield K) K x) = x
    rw [cmRelNorm_extended, ← Nat.cast_smul_eq_nsmul ℤ_[p], Nat.cast_ofNat, smul_smul,
      h2.val_inv_mul, one_smul]

@[simp]
theorem coe_cmRealClassEquivPlus_apply (hp : p ≠ 2) (K : Type*) [Field K] [NumberField K]
    [IsCMField K] (x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (maximalRealSubfield K)))) :
    (cmRealClassEquivPlus p hp K x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))) =
      classGroupExtendedLinearMap ℤ_[p] (maximalRealSubfield K) K x :=
  (rfl)

/-- For `p ≠ 2`, `classGroupExtendedLinearMap` from `K⁺` to `K` is injective on `p`-primary class
modules (no odd-prime capitulation between `K⁺` and `K`). -/
theorem cmExtended_injective (hp : p ≠ 2) (K : Type*) [Field K] [NumberField K] [IsCMField K] :
    Function.Injective (classGroupExtendedLinearMap ℤ_[p] (maximalRealSubfield K) K) := fun _ _ h ↦
  (cmRealClassEquivPlus p hp K).injective (Subtype.ext h)

/-- **Odd-prime minus-eigenspace / norm-kernel identification**: for `p ≠ 2`, the `-1`-eigenspace
of complex conjugation equals `LinearMap.ker (classGroupRelNormLinearMap ℤ_[p] K⁺ K)`. -/
theorem cmMinusEigenspace_eq_ker_relNorm (hp : p ≠ 2) (K : Type*) [Field K] [NumberField K]
    [IsCMField K] :
    Module.End.eigenspace (cmComplexConjClassAction ℤ_[p] K) (-1) =
      LinearMap.ker (classGroupRelNormLinearMap ℤ_[p] (maximalRealSubfield K) K) := by
  have h2 : IsUnit (2 : ℤ_[p]) := PadicInt.isUnit_two hp
  ext x
  rw [Module.End.mem_eigenspace_iff, neg_one_smul, LinearMap.mem_ker]
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · have hN : classGroupRelNormLinearMap ℤ_[p] (maximalRealSubfield K) K x =
        -classGroupRelNormLinearMap ℤ_[p] (maximalRealSubfield K) K x := by
      conv_lhs => rw [← cmRelNorm_cmComplexConjClassAction ℤ_[p] K x, hx, map_neg]
    have h2N : (2 : ℤ_[p]) • classGroupRelNormLinearMap ℤ_[p] (maximalRealSubfield K) K x = 0 := by
      rw [two_smul]
      conv_lhs => arg 2; rw [hN]
      exact add_neg_cancel _
    exact h2.smul_eq_zero.mp h2N
  · have h := cmExtended_relNorm ℤ_[p] K x
    rw [hx, map_zero] at h
    exact eq_neg_of_add_eq_zero_right h.symm

private theorem two_lt_prime_pow {r : ℕ} (hp : p ≠ 2) (hr : 1 ≤ r) : 2 < p ^ r := by
  have hp3 : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp)
  exact lt_of_lt_of_le hp3 (Nat.le_self_pow (by omega : r ≠ 0) p)

/-- **Cyclotomic real-to-plus isomorphism (`p ≠ 2`, `r ≥ 1`)**: class extension from the maximal
real subfield of `CyclotomicField (p ^ r) ℚ` identifies its `p`-primary class module with the
`+1`-eigenspace of `cyclotomicClassAction ℤ_[p] (p ^ r) (-1)`. -/
noncomputable def cyclotomicRealClassEquivPlus (hp : p ≠ 2) {r : ℕ} (hr : 1 ≤ r) :
    (ℤ_[p] ⊗[ℤ]
        Additive (ClassGroup (𝓞 (maximalRealSubfield (CyclotomicField (p ^ r) ℚ))))) ≃ₗ[ℤ_[p]]
      Module.End.eigenspace (cyclotomicClassAction ℤ_[p] (p ^ r) (-1)) 1 := by
  let _ : IsCMField (CyclotomicField (p ^ r) ℚ) :=
    isCMField_cyclotomicField (two_lt_prime_pow p hp hr)
  exact (cmRealClassEquivPlus p hp (CyclotomicField (p ^ r) ℚ)).trans
    (LinearEquiv.ofEq _ _ <| by
      rw [cmComplexConjClassAction_cyclotomicField ℤ_[p] (two_lt_prime_pow p hp hr)])

/-- **Cyclotomic minus-eigenspace / norm-kernel equality (`p ≠ 2`, `r ≥ 1`)**. -/
theorem cyclotomicMinusEigenspace_eq_ker_relNorm (hp : p ≠ 2) {r : ℕ} (hr : 1 ≤ r) :
    Module.End.eigenspace (cyclotomicClassAction ℤ_[p] (p ^ r) (-1)) (-1) =
      LinearMap.ker
        (classGroupRelNormLinearMap ℤ_[p]
          (maximalRealSubfield (CyclotomicField (p ^ r) ℚ)) (CyclotomicField (p ^ r) ℚ)) := by
  let _ : IsCMField (CyclotomicField (p ^ r) ℚ) :=
    isCMField_cyclotomicField (two_lt_prime_pow p hp hr)
  rw [← cmComplexConjClassAction_cyclotomicField ℤ_[p] (two_lt_prime_pow p hp hr),
    cmMinusEigenspace_eq_ker_relNorm p hp]

private theorem cyclotomicClassAction_comm_projector {r : ℕ} (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (i : ℤ) (b : (ZMod (p ^ r))ˣ)
    (x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (p ^ r) ℚ)))) :
    cyclotomicClassAction ℤ_[p] (p ^ r) b (cyclotomicClassProjector p r hr ω i x) =
      cyclotomicClassProjector p r hr ω i (cyclotomicClassAction ℤ_[p] (p ^ r) b x) := by
  simp only [cyclotomicClassProjector_eq_sum, LinearMap.smul_apply, LinearMap.coe_sum,
    Finset.sum_apply, map_smul, map_sum, ← cyclotomicClassAction_apply_mul, mul_comm b]

/-- **Plus eigenspace as the supremum of even tame eigenspaces** (`p ≠ 2`, `r ≥ 1`). -/
theorem cyclotomicPlusEigenspace_eq_iSup_even (hp : p ≠ 2) {r : ℕ} (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (hω : ∀ a : (ZMod p)ˣ, PadicInt.toZMod ((ω a : ℤ_[p]ˣ) : ℤ_[p]) = (a : ZMod p)) :
    Module.End.eigenspace (cyclotomicClassAction ℤ_[p] (p ^ r) (-1)) 1 =
      ⨆ (k : ZMod (p - 1)) (_ : Even k.val), cyclotomicClassEigenspace p r hr ω k.val := by
  let _ : IsCMField (CyclotomicField (p ^ r) ℚ) :=
    isCMField_cyclotomicField (two_lt_prime_pow p hp hr)
  have hdisj : Disjoint
      (Module.End.eigenspace (cyclotomicClassAction ℤ_[p] (p ^ r) (-1)) 1)
      (Module.End.eigenspace (cyclotomicClassAction ℤ_[p] (p ^ r) (-1)) (-1)) := by
    rw [← cmComplexConjClassAction_cyclotomicField ℤ_[p] (two_lt_prime_pow p hp hr)]
    exact (isCompl_cmPlus_cmMinus p hp (CyclotomicField (p ^ r) ℚ)).disjoint
  refine le_antisymm (fun x hx ↦ ?_) (iSup₂_le fun k hk y hy ↦ ?_)
  · have hsum : ∑ k : ZMod (p - 1), cyclotomicClassProjector p r hr ω k.val x = x := by
      simpa [LinearMap.coe_sum, Finset.sum_apply] using
        DFunLike.congr_fun (sum_cyclotomicClassProjector p r hr ω hω) x
    rw [← hsum]
    refine Submodule.sum_mem _ fun k _ ↦ ?_
    by_cases hev : Even k.val
    · exact Submodule.mem_iSup_of_mem k
        (Submodule.mem_iSup_of_mem hev (cyclotomicClassProjector_apply_mem p r hr ω k.val x))
    · have hodd : Odd k.val := Nat.not_even_iff_odd.mp hev
      have hmem1 : cyclotomicClassProjector p r hr ω k.val x ∈
          Module.End.eigenspace (cyclotomicClassAction ℤ_[p] (p ^ r) (-1)) 1 := by
        rw [Module.End.mem_eigenspace_iff, one_smul, cyclotomicClassAction_comm_projector,
          Module.End.mem_eigenspace_iff.mp hx, one_smul]
      have hmem2 : cyclotomicClassProjector p r hr ω k.val x ∈
          Module.End.eigenspace (cyclotomicClassAction ℤ_[p] (p ^ r) (-1)) (-1) := by
        rw [Module.End.mem_eigenspace_iff,
          cyclotomicClassAction_neg_one_of_mem_eigenspace_natCast hp hr hω
            (cyclotomicClassProjector_apply_mem p r hr ω k.val x),
          hodd.neg_one_pow]
      rw [Submodule.disjoint_def.mp hdisj _ hmem1 hmem2]
      exact Submodule.zero_mem _
  · rw [Module.End.mem_eigenspace_iff,
      cyclotomicClassAction_neg_one_of_mem_eigenspace_natCast hp hr hω hy, hk.neg_one_pow]

/-- **Minus eigenspace as the supremum of odd tame eigenspaces** (`p ≠ 2`, `r ≥ 1`). -/
theorem cyclotomicMinusEigenspace_eq_iSup_odd (hp : p ≠ 2) {r : ℕ} (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (hω : ∀ a : (ZMod p)ˣ, PadicInt.toZMod ((ω a : ℤ_[p]ˣ) : ℤ_[p]) = (a : ZMod p)) :
    Module.End.eigenspace (cyclotomicClassAction ℤ_[p] (p ^ r) (-1)) (-1) =
      ⨆ (k : ZMod (p - 1)) (_ : Odd k.val), cyclotomicClassEigenspace p r hr ω k.val := by
  let _ : IsCMField (CyclotomicField (p ^ r) ℚ) :=
    isCMField_cyclotomicField (two_lt_prime_pow p hp hr)
  have hdisj : Disjoint
      (Module.End.eigenspace (cyclotomicClassAction ℤ_[p] (p ^ r) (-1)) 1)
      (Module.End.eigenspace (cyclotomicClassAction ℤ_[p] (p ^ r) (-1)) (-1)) := by
    rw [← cmComplexConjClassAction_cyclotomicField ℤ_[p] (two_lt_prime_pow p hp hr)]
    exact (isCompl_cmPlus_cmMinus p hp (CyclotomicField (p ^ r) ℚ)).disjoint
  refine le_antisymm (fun x hx ↦ ?_) (iSup₂_le fun k hk y hy ↦ ?_)
  · have hsum : ∑ k : ZMod (p - 1), cyclotomicClassProjector p r hr ω k.val x = x := by
      simpa [LinearMap.coe_sum, Finset.sum_apply] using
        DFunLike.congr_fun (sum_cyclotomicClassProjector p r hr ω hω) x
    rw [← hsum]
    refine Submodule.sum_mem _ fun k _ ↦ ?_
    by_cases hodd : Odd k.val
    · exact Submodule.mem_iSup_of_mem k
        (Submodule.mem_iSup_of_mem hodd (cyclotomicClassProjector_apply_mem p r hr ω k.val x))
    · have hev : Even k.val := Nat.not_odd_iff_even.mp hodd
      have hmem1 : cyclotomicClassProjector p r hr ω k.val x ∈
          Module.End.eigenspace (cyclotomicClassAction ℤ_[p] (p ^ r) (-1)) 1 := by
        rw [Module.End.mem_eigenspace_iff,
          cyclotomicClassAction_neg_one_of_mem_eigenspace_natCast hp hr hω
            (cyclotomicClassProjector_apply_mem p r hr ω k.val x),
          hev.neg_one_pow]
      have hmem2 : cyclotomicClassProjector p r hr ω k.val x ∈
          Module.End.eigenspace (cyclotomicClassAction ℤ_[p] (p ^ r) (-1)) (-1) := by
        rw [Module.End.mem_eigenspace_iff, cyclotomicClassAction_comm_projector,
          Module.End.mem_eigenspace_iff.mp hx, map_smul]
      rw [Submodule.disjoint_def.mp hdisj _ hmem1 hmem2]
      exact Submodule.zero_mem _
  · rw [Module.End.mem_eigenspace_iff,
      cyclotomicClassAction_neg_one_of_mem_eigenspace_natCast hp hr hω hy, hk.neg_one_pow]

/-- **Bundled direct-sum decomposition of the `+1`-eigenspace into even tame eigenspaces**
(`p ≠ 2`, `r ≥ 1`). -/
noncomputable def cyclotomicPlusEvenEquiv (hp : p ≠ 2) {r : ℕ} (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (hω : ∀ a : (ZMod p)ˣ, PadicInt.toZMod ((ω a : ℤ_[p]ˣ) : ℤ_[p]) = (a : ZMod p)) :
    (⨁ k : {k : ZMod (p - 1) // Even k.val}, cyclotomicClassEigenspace p r hr ω k.1.val) ≃ₗ[ℤ_[p]]
      Module.End.eigenspace (cyclotomicClassAction ℤ_[p] (p ^ r) (-1)) 1 := by
  let f := DirectSum.coeLinearMap
    (fun k : {k : ZMod (p - 1) // Even k.val} ↦ cyclotomicClassEigenspace p r hr ω k.1.val)
  have hind : iSupIndep
      (fun k : {k : ZMod (p - 1) // Even k.val} ↦ cyclotomicClassEigenspace p r hr ω k.1.val) :=
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp
      (isInternal_cyclotomicClassEigenspace p r hr ω hω)).1.comp Subtype.val_injective
  have hinj : Function.Injective f := hind.dfinsupp_lsum_injective
  have hran : LinearMap.range f =
      Module.End.eigenspace (cyclotomicClassAction ℤ_[p] (p ^ r) (-1)) 1 := by
    rw [DirectSum.range_coeLinearMap, iSup_subtype,
      cyclotomicPlusEigenspace_eq_iSup_even p hp hr ω hω]
  exact (LinearEquiv.ofInjective f hinj).trans (LinearEquiv.ofEq _ _ hran)

/-- **Bundled direct-sum decomposition of the `-1`-eigenspace (`= ker relNorm`) into odd tame
eigenspaces** (`p ≠ 2`, `r ≥ 1`). -/
noncomputable def cyclotomicMinusOddEquiv (hp : p ≠ 2) {r : ℕ} (hr : 1 ≤ r)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (hω : ∀ a : (ZMod p)ˣ, PadicInt.toZMod ((ω a : ℤ_[p]ˣ) : ℤ_[p]) = (a : ZMod p)) :
    (⨁ k : {k : ZMod (p - 1) // Odd k.val}, cyclotomicClassEigenspace p r hr ω k.1.val) ≃ₗ[ℤ_[p]]
      LinearMap.ker
        (classGroupRelNormLinearMap ℤ_[p]
          (maximalRealSubfield (CyclotomicField (p ^ r) ℚ)) (CyclotomicField (p ^ r) ℚ)) := by
  let f := DirectSum.coeLinearMap
    (fun k : {k : ZMod (p - 1) // Odd k.val} ↦ cyclotomicClassEigenspace p r hr ω k.1.val)
  have hind : iSupIndep
      (fun k : {k : ZMod (p - 1) // Odd k.val} ↦ cyclotomicClassEigenspace p r hr ω k.1.val) :=
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp
      (isInternal_cyclotomicClassEigenspace p r hr ω hω)).1.comp Subtype.val_injective
  have hinj : Function.Injective f := hind.dfinsupp_lsum_injective
  have hran : LinearMap.range f =
      LinearMap.ker
        (classGroupRelNormLinearMap ℤ_[p]
          (maximalRealSubfield (CyclotomicField (p ^ r) ℚ)) (CyclotomicField (p ^ r) ℚ)) := by
    rw [DirectSum.range_coeLinearMap, iSup_subtype,
      ← cyclotomicMinusEigenspace_eq_iSup_odd p hp hr ω hω,
      cyclotomicMinusEigenspace_eq_ker_relNorm p hp hr]
  exact (LinearEquiv.ofInjective f hinj).trans (LinearEquiv.ofEq _ _ hran)

end OddPrime

/-! ### The dyadic boundary (`p = 2`): norm kernel, anti-invariants, and minus quotient -/

section DyadicBoundary

section CMDyadic

variable (K : Type*) [Field K] [NumberField K]

/-- **Dyadic relative-norm kernel** `ker (N_{K / K⁺})` inside the `2`-primary class module of a
number field `K` over its maximal real subfield. -/
noncomputable def dyadicCMClassNormKer :
    Submodule ℤ_[2] (ℤ_[2] ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :=
  LinearMap.ker (classGroupRelNormLinearMap ℤ_[2] (maximalRealSubfield K) K)

@[simp]
theorem mem_dyadicCMClassNormKer_iff
    {x : ℤ_[2] ⊗[ℤ] Additive (ClassGroup (𝓞 K))} :
    x ∈ dyadicCMClassNormKer K ↔
      classGroupRelNormLinearMap ℤ_[2] (maximalRealSubfield K) K x = 0 :=
  Iff.rfl

variable [IsCMField K]

/-- **Dyadic anti-invariant submodule** `ker (1 + c)` inside the `2`-primary class module of a
CM field `K`. -/
noncomputable def dyadicCMClassAntiInvariants :
    Submodule ℤ_[2] (ℤ_[2] ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :=
  LinearMap.ker (LinearMap.id + cmComplexConjClassAction ℤ_[2] K)

/-- **Dyadic minus coinvariant quotient** `A ⧸ (1 + c) A` of the `2`-primary class module of a
CM field `K`. -/
noncomputable abbrev dyadicCMClassMinusQuotient : Type _ :=
  (ℤ_[2] ⊗[ℤ] Additive (ClassGroup (𝓞 K))) ⧸
    LinearMap.range (LinearMap.id + cmComplexConjClassAction ℤ_[2] K)

theorem mem_dyadicCMClassAntiInvariants_iff
    {x : ℤ_[2] ⊗[ℤ] Additive (ClassGroup (𝓞 K))} :
    x ∈ dyadicCMClassAntiInvariants K ↔ cmComplexConjClassAction ℤ_[2] K x = -x := by
  rw [dyadicCMClassAntiInvariants, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply,
    add_comm, add_eq_zero_iff_eq_neg]

theorem dyadicCMClassAntiInvariants_eq_eigenspace_neg_one :
    dyadicCMClassAntiInvariants K =
      Module.End.eigenspace (cmComplexConjClassAction ℤ_[2] K) (-1) := by
  ext x
  rw [mem_dyadicCMClassAntiInvariants_iff, Module.End.mem_eigenspace_iff, neg_one_smul]

/-- In any CM field `K`, `ker N_{K / K⁺} ≤ ker (1 + c)` on `2`-primary class modules. -/
theorem dyadicCMClassNormKer_le_antiInvariants :
    dyadicCMClassNormKer K ≤ dyadicCMClassAntiInvariants K := by
  intro x hx
  rw [dyadicCMClassNormKer, LinearMap.mem_ker] at hx
  rw [dyadicCMClassAntiInvariants, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply,
    ← cmExtended_relNorm ℤ_[2] K x, hx, map_zero]

/-- The canonical injective `ℤ_[2]`-linear inclusion `ker N_{K / K⁺} ↪ ker (1 + c)`. -/
noncomputable def dyadicNormKerToAntiInvariants :
    dyadicCMClassNormKer K →ₗ[ℤ_[2]] dyadicCMClassAntiInvariants K :=
  Submodule.inclusion (dyadicCMClassNormKer_le_antiInvariants K)

theorem injective_dyadicNormKerToAntiInvariants :
    Function.Injective (dyadicNormKerToAntiInvariants K) :=
  Submodule.inclusion_injective (dyadicCMClassNormKer_le_antiInvariants K)

/-- On `dyadicCMClassAntiInvariants K`, the relative norm to `K⁺` lands in `2`-torsion. -/
theorem two_smul_relNorm_of_mem_dyadicAntiInvariants
    {x : ℤ_[2] ⊗[ℤ] Additive (ClassGroup (𝓞 K))} (hx : x ∈ dyadicCMClassAntiInvariants K) :
    (2 : ℤ_[2]) • classGroupRelNormLinearMap ℤ_[2] (maximalRealSubfield K) K x = 0 := by
  have hx' : x + cmComplexConjClassAction ℤ_[2] K x = 0 := hx
  have h := congrArg (classGroupRelNormLinearMap ℤ_[2] (maximalRealSubfield K) K)
    (cmExtended_relNorm ℤ_[2] K x)
  rw [cmRelNorm_extended, hx', map_zero, ← Nat.cast_smul_eq_nsmul ℤ_[2], Nat.cast_ofNat] at h
  exact h

/-- **`2`-torsion defect between `ker N` and `ker (1 + c)`**: doubling any anti-invariant class
lands in `dyadicCMClassNormKer K`. -/
theorem two_smul_mem_dyadicCMClassNormKer
    {x : ℤ_[2] ⊗[ℤ] Additive (ClassGroup (𝓞 K))} (hx : x ∈ dyadicCMClassAntiInvariants K) :
    (2 : ℤ_[2]) • x ∈ dyadicCMClassNormKer K := by
  rw [dyadicCMClassNormKer, LinearMap.mem_ker, map_smul]
  exact two_smul_relNorm_of_mem_dyadicAntiInvariants K hx

/-- The canonical `ℤ_[2]`-linear comparison map `ker (1 + c) → A ⧸ (1 + c) A`. -/
noncomputable def dyadicAntiInvariantsToMinusQuotient :
    dyadicCMClassAntiInvariants K →ₗ[ℤ_[2]] dyadicCMClassMinusQuotient K :=
  (Submodule.mkQ (LinearMap.range (LinearMap.id + cmComplexConjClassAction ℤ_[2] K))).comp
    (Submodule.subtype _)

/-- **`2`-torsion kernel defect of `ker (1 + c) → A ⧸ (1 + c) A`**: every element in the kernel is
annihilated by `2`. -/
theorem two_smul_eq_zero_of_mem_ker_dyadicAntiInvariantsToMinusQuotient
    {z : dyadicCMClassAntiInvariants K}
    (hz : z ∈ LinearMap.ker (dyadicAntiInvariantsToMinusQuotient K)) :
    (2 : ℤ_[2]) • z = 0 := by
  rw [LinearMap.mem_ker, dyadicAntiInvariantsToMinusQuotient, LinearMap.comp_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
  obtain ⟨w, hw⟩ := hz
  simp only [LinearMap.add_apply, LinearMap.id_apply, Submodule.coe_subtype] at hw
  have hcz : cmComplexConjClassAction ℤ_[2] K z.1 = z.1 := by
    rw [← hw, map_add, cmComplexConjClassAction_apply_apply, add_comm]
  have hanti : z.1 + cmComplexConjClassAction ℤ_[2] K z.1 = 0 := z.2
  rw [hcz, ← two_smul ℤ_[2] z.1] at hanti
  exact Subtype.ext hanti

/-- **`2`-torsion cokernel defect of `ker (1 + c) → A ⧸ (1 + c) A`**: twice every class in
`dyadicCMClassMinusQuotient K` lies in the image of `dyadicAntiInvariantsToMinusQuotient K`. -/
theorem two_smul_mem_range_dyadicAntiInvariantsToMinusQuotient
    (q : dyadicCMClassMinusQuotient K) :
    (2 : ℤ_[2]) • q ∈ LinearMap.range (dyadicAntiInvariantsToMinusQuotient K) := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  let y : ℤ_[2] ⊗[ℤ] Additive (ClassGroup (𝓞 K)) := w - cmComplexConjClassAction ℤ_[2] K w
  have hy : y ∈ dyadicCMClassAntiInvariants K := by
    rw [dyadicCMClassAntiInvariants, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply]
    simp only [y, map_sub, cmComplexConjClassAction_apply_apply]
    abel
  refine ⟨⟨y, hy⟩, ?_⟩
  change Submodule.Quotient.mk y = (2 : ℤ_[2]) • Submodule.Quotient.mk w
  rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq]
  refine ⟨w, ?_⟩
  simp only [y, LinearMap.add_apply, LinearMap.id_apply, two_smul]
  abel

end CMDyadic

section CyclotomicDyadic

private theorem two_lt_two_pow {r : ℕ} (hr : 2 ≤ r) : 2 < 2 ^ r :=
  calc 2 < 2 ^ 2 := by decide
    _ ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) hr

/-- For `r ≥ 2`, the `2`-power cyclotomic field `CyclotomicField (2 ^ r) ℚ` is a CM field. -/
theorem isCMField_cyclotomicField_two_pow {r : ℕ} (hr : 2 ≤ r) :
    IsCMField (CyclotomicField (2 ^ r) ℚ) :=
  isCMField_cyclotomicField (two_lt_two_pow hr)

/-- **Dyadic cyclotomic relative-norm kernel** at conductor `2 ^ r`. -/
noncomputable def dyadicCyclotomicClassNormKer (r : ℕ) :
    Submodule ℤ_[2] (ℤ_[2] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (2 ^ r) ℚ)))) :=
  LinearMap.ker
    (classGroupRelNormLinearMap ℤ_[2]
      (maximalRealSubfield (CyclotomicField (2 ^ r) ℚ)) (CyclotomicField (2 ^ r) ℚ))

/-- **Dyadic cyclotomic anti-invariant submodule** `ker (1 + c)` at conductor `2 ^ r`. -/
noncomputable def dyadicCyclotomicClassAntiInvariants (r : ℕ) :
    Submodule ℤ_[2] (ℤ_[2] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (2 ^ r) ℚ)))) :=
  LinearMap.ker (LinearMap.id + cyclotomicClassAction ℤ_[2] (2 ^ r) (-1))

/-- **Dyadic cyclotomic minus coinvariant quotient** `A ⧸ (1 + c) A` at conductor `2 ^ r`. -/
noncomputable abbrev dyadicCyclotomicClassMinusQuotient (r : ℕ) : Type _ :=
  (ℤ_[2] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (2 ^ r) ℚ)))) ⧸
    LinearMap.range (LinearMap.id + cyclotomicClassAction ℤ_[2] (2 ^ r) (-1))

@[simp]
theorem mem_dyadicCyclotomicClassNormKer_iff {r : ℕ}
    {x : ℤ_[2] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (2 ^ r) ℚ)))} :
    x ∈ dyadicCyclotomicClassNormKer r ↔
      classGroupRelNormLinearMap ℤ_[2]
        (maximalRealSubfield (CyclotomicField (2 ^ r) ℚ)) (CyclotomicField (2 ^ r) ℚ) x = 0 :=
  Iff.rfl

theorem mem_dyadicCyclotomicClassAntiInvariants_iff {r : ℕ}
    {x : ℤ_[2] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (2 ^ r) ℚ)))} :
    x ∈ dyadicCyclotomicClassAntiInvariants r ↔
      cyclotomicClassAction ℤ_[2] (2 ^ r) (-1) x = -x := by
  rw [dyadicCyclotomicClassAntiInvariants, LinearMap.mem_ker, LinearMap.add_apply,
    LinearMap.id_apply, add_comm, add_eq_zero_iff_eq_neg]

theorem dyadicCyclotomicClassAntiInvariants_eq_cm {r : ℕ} (hr : 2 ≤ r) :
    let _ : IsCMField (CyclotomicField (2 ^ r) ℚ) := isCMField_cyclotomicField_two_pow hr
    dyadicCyclotomicClassAntiInvariants r =
      dyadicCMClassAntiInvariants (CyclotomicField (2 ^ r) ℚ) := by
  dsimp only
  let _ : IsCMField (CyclotomicField (2 ^ r) ℚ) := isCMField_cyclotomicField_two_pow hr
  rw [dyadicCyclotomicClassAntiInvariants, dyadicCMClassAntiInvariants,
    cmComplexConjClassAction_cyclotomicField ℤ_[2] (two_lt_two_pow hr)]

theorem dyadicCyclotomicClassNormKer_le_antiInvariants {r : ℕ} (hr : 2 ≤ r) :
    dyadicCyclotomicClassNormKer r ≤ dyadicCyclotomicClassAntiInvariants r := by
  let _ : IsCMField (CyclotomicField (2 ^ r) ℚ) := isCMField_cyclotomicField_two_pow hr
  rw [dyadicCyclotomicClassAntiInvariants_eq_cm hr]
  exact dyadicCMClassNormKer_le_antiInvariants (CyclotomicField (2 ^ r) ℚ)

/-- At conductor `2 ^ 1 = 2` (`CyclotomicField 2 ℚ ≃ ℚ`), all three dyadic class objects are
trivial. -/
theorem subsingleton_dyadicCyclotomicClassMinusQuotient_one :
    Subsingleton (dyadicCyclotomicClassMinusQuotient 1) := by
  have : Subsingleton (ℤ_[2] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (2 ^ 1) ℚ)))) := by
    simpa [pow_one] using subsingleton_cyclotomicClassTensor_two ℤ_[2]
  infer_instance

theorem dyadicCyclotomicClassNormKer_one : dyadicCyclotomicClassNormKer 1 = ⊥ := by
  have : Subsingleton (ℤ_[2] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (2 ^ 1) ℚ)))) := by
    simpa [pow_one] using subsingleton_cyclotomicClassTensor_two ℤ_[2]
  exact Subsingleton.elim _ _

theorem dyadicCyclotomicClassAntiInvariants_one : dyadicCyclotomicClassAntiInvariants 1 = ⊥ := by
  have : Subsingleton (ℤ_[2] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (2 ^ 1) ℚ)))) := by
    simpa [pow_one] using subsingleton_cyclotomicClassTensor_two ℤ_[2]
  exact Subsingleton.elim _ _

/-- **Dyadic tower relative-norm map on minus coinvariant quotients** for `r ≤ s`: relative norm
from `CyclotomicField (2 ^ s) ℚ` to `CyclotomicField (2 ^ r) ℚ` commutes with `-1`, hence descends
from `A_s ⧸ (1 + c) A_s` to `A_r ⧸ (1 + c) A_r`. -/
noncomputable def dyadicCyclotomicMinusQuotientRelNorm (r s : ℕ) (hrs : r ≤ s)
    [Algebra (CyclotomicField (2 ^ r) ℚ) (CyclotomicField (2 ^ s) ℚ)] :
    dyadicCyclotomicClassMinusQuotient s →ₗ[ℤ_[2]] dyadicCyclotomicClassMinusQuotient r := by
  refine Submodule.mapQ _ _
    (classGroupRelNormLinearMap ℤ_[2] (CyclotomicField (2 ^ r) ℚ) (CyclotomicField (2 ^ s) ℚ)) ?_
  rintro _ ⟨x, rfl⟩
  rw [Submodule.mem_comap, LinearMap.add_apply, LinearMap.id_apply, map_add]
  refine ⟨classGroupRelNormLinearMap ℤ_[2]
    (CyclotomicField (2 ^ r) ℚ) (CyclotomicField (2 ^ s) ℚ) x, ?_⟩
  have hmap : ZMod.unitsMap (Nat.pow_dvd_pow 2 hrs) (-1 : (ZMod (2 ^ s))ˣ) = -1 := by
    ext
    simp [ZMod.unitsMap_def]
  rw [LinearMap.add_apply, LinearMap.id_apply, add_right_inj,
    cyclotomicClassAction_eq_cyclotomicFieldClassAction, ← hmap,
    cyclotomicFieldClassAction_relNormLinearMap ℤ_[2] (Nat.pow_dvd_pow 2 hrs),
    ← cyclotomicClassAction_eq_cyclotomicFieldClassAction]

@[simp]
theorem dyadicCyclotomicMinusQuotientRelNorm_mk (r s : ℕ) (hrs : r ≤ s)
    [Algebra (CyclotomicField (2 ^ r) ℚ) (CyclotomicField (2 ^ s) ℚ)]
    (x : ℤ_[2] ⊗[ℤ] Additive (ClassGroup (𝓞 (CyclotomicField (2 ^ s) ℚ)))) :
    dyadicCyclotomicMinusQuotientRelNorm r s hrs (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (classGroupRelNormLinearMap ℤ_[2]
          (CyclotomicField (2 ^ r) ℚ) (CyclotomicField (2 ^ s) ℚ) x) := by
  rw [dyadicCyclotomicMinusQuotientRelNorm, Submodule.mapQ_apply]

end CyclotomicDyadic

end DyadicBoundary

end TauCeti
