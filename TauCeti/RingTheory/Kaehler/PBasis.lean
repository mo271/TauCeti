/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsPerfectClosure
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.FieldTheory.Frobenius.PBasis
public import TauCeti.FieldTheory.FunctionField.Differential.Kaehler
public import TauCeti.RingTheory.Derivation.Basic
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Finsupp.Single
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# `p`-bases and the dimension of Kähler differentials

Let `k` be a field of prime characteristic `p` over a perfect ring `R` (for instance `R = ZMod p`
or any perfect subfield `k₀` of `k`), and let `k ^ p = (frobenius k p).fieldRange` be the subfield
of `p`-th powers. Because every `R`-derivation vanishes on `k ^ p` and every element of `R` is a
`p`-th power, `Ω[k⁄R]` is canonically isomorphic to `Ω[k⁄k ^ p]`
(`KaehlerDifferential.frobeniusFieldRangeEquiv`).

Without any finiteness assumption on `[k : k ^ p]`, this file establishes the bijection between
`p`-bases of `k` and `k`-bases of differentials `Ω[k⁄R]` (Matsumura, §26; Stacks Tag 07P2):
* Every `p`-basis `b : ι → k` admits coordinate derivations
  `hb.coordDerivation R i : Derivation R k k` sending `b i` to `1` and `b j` (`j ≠ i`) to `0`, so
  the differentials `D R k (b i)` form a `k`-basis `hb.kaehlerBasis R : Module.Basis ι k Ω[k⁄R]`.
* Conversely, if `D R k (b i)` is `k`-linearly independent then `b` is `p`-independent
  (`TauCeti.isPIndependent_of_linearIndependent_D`), and a family `b : ι → k` is a `p`-basis if and
  only if its differentials `D R k (b i)` are linearly independent and span `Ω[k⁄R]`
  (`TauCeti.isPBasis_iff_linearIndependent_and_span_D`).
* Consequently, `Ω[k⁄R]` is finite-dimensional over `k` if and only if `k` is finite-dimensional
  over `k ^ p` (`TauCeti.finiteDimensional_kaehlerDifferential_iff`), in which case
  `[k : k ^ p] = p ^ dim_k Ω[k⁄R]`
  (`TauCeti.finrank_fieldRange_frobenius_eq_pow_finrank_kaehlerDifferential`); and `Ω[k⁄R]` is
  trivial if and only if `k` is perfect
  (`TauCeti.subsingleton_kaehlerDifferential_iff_perfectField`).

We also record the concrete consequences for rational and multivariate function fields:
* For `RatFunc k₀` over a perfect field `k₀` of characteristic `p`, `X` is a singleton `p`-basis
  and `[k₀(X) : k₀(X) ^ p] = p` (`TauCeti.isPBasis_ratFunc_X`,
  `TauCeti.finrank_fieldRange_frobenius_ratFunc`), whereas `X ^ p` has vanishing differential and
  is not a `p`-basis (`TauCeti.not_isPBasis_ratFunc_X_pow_char`) despite forming a transcendence
  basis (`TauCeti.RatFunc.isTranscendenceBasis_X_pow`).
* For `FractionRing (MvPolynomial σ k₀)` in any (possibly infinite) variable set `σ`, the variables
  `X i` give a basis of `Ω[FractionRing (MvPolynomial σ k₀)⁄k₀]`
  (`TauCeti.kaehlerBasisFractionRingMvPolynomial`) and hence a `p`-basis
  (`TauCeti.isPBasis_fractionRing_mvPolynomial_X`); when `σ` is infinite, both `Ω¹` and
  `[k : k ^ p]` are infinite-dimensional, while passing to `PerfectClosure` preserves infinite
  transcendence degree yet kills `Ω¹` and reduces `[L : L ^ p]` to `1`.

## References

* H. Matsumura, *Commutative Ring Theory*, 2nd ed., Cambridge Univ. Press, 1989, §26.
* The Stacks Project, Lemma 15.47.2 (Tag 07P2).
* D. Clausen, A. Mathew, and M. Morrow, *K-theory and topological cyclic homology of henselian
  pairs*, J. Amer. Math. Soc. 34 (2021), §5.1, Footnote 10.
-/

public section

open Finset KaehlerDifferential

open scoped nonZeroDivisors

namespace Derivation

section ToFieldRange

variable {R k M : Type*} [CommSemiring R] [Field k] [Algebra R k]
  [AddCommMonoid M] [Module R M] [Module k M]

/-- In characteristic `p`, every `R`-derivation on a field `k` is linear over the subfield
`k ^ p = (frobenius k p).fieldRange` of `p`-th powers. -/
@[simp]
theorem map_smul_fieldRange_frobenius (p : ℕ) [CharP k p] [ExpChar k p]
    (D' : Derivation R k M) (c : (frobenius k p).fieldRange) (x : k) :
    D' (c • x) = (c : k) • D' x := by
  rcases c with ⟨_, y, rfl⟩
  rw [Subfield.smul_def, smul_eq_mul, D'.leibniz, D'.map_frobenius, smul_zero, add_zero]

/-- Promote an `R`-derivation on a field `k` of characteristic `p` to a derivation over the
subfield `k ^ p` of `p`-th powers. -/
def toFieldRangeFrobenius (p : ℕ) [CharP k p] [ExpChar k p]
    [IsScalarTower (frobenius k p).fieldRange k M] (D' : Derivation R k M) :
    Derivation (frobenius k p).fieldRange k M where
  toFun := D'
  map_add' := D'.map_add
  map_smul' c x := by
    rw [D'.map_smul_fieldRange_frobenius p c x]
    exact (IsScalarTower.algebraMap_smul k c (D' x)).symm
  map_one_eq_zero' := D'.map_one_eq_zero
  leibniz' := D'.leibniz

@[simp]
theorem toFieldRangeFrobenius_apply (p : ℕ) [CharP k p] [ExpChar k p]
    [IsScalarTower (frobenius k p).fieldRange k M] (D' : Derivation R k M) (x : k) :
    D'.toFieldRangeFrobenius p x = D' x :=
  (rfl)

end ToFieldRange

/-- Restrict a `(frobenius k p).fieldRange`-derivation on `k` to any perfect base ring `R`. -/
def ofFieldRangeFrobenius (p : ℕ) (R : Type*) [CommRing R] [PerfectRing R p]
    {k M : Type*} [Field k] [Algebra R k] [CharP k p] [ExpChar k p] [AddCommMonoid M]
    [Module R M] [Module k M] [Module (frobenius k p).fieldRange M] [IsScalarTower R k M]
    (D' : Derivation (frobenius k p).fieldRange k M) :
    Derivation R k M where
  toFun := D'
  map_add' := D'.map_add
  map_smul' r x := by
    let r₀ : R := (powMulEquiv R p).symm r
    have hr : r = r₀ ^ p := (powMulEquiv_symm_pow_p R p r).symm
    rw [RingHom.id_apply, hr, Algebra.smul_def, map_pow, D'.leibniz, D'.map_pow_char p,
      smul_zero, add_zero, ← map_pow, IsScalarTower.algebraMap_smul]
  map_one_eq_zero' := D'.map_one_eq_zero
  leibniz' := D'.leibniz

@[simp]
theorem ofFieldRangeFrobenius_apply (p : ℕ) (R : Type*) [CommRing R] [PerfectRing R p]
    {k M : Type*} [Field k] [Algebra R k] [CharP k p] [ExpChar k p] [AddCommMonoid M]
    [Module R M] [Module k M] [Module (frobenius k p).fieldRange M] [IsScalarTower R k M]
    (D' : Derivation (frobenius k p).fieldRange k M) (x : k) :
    D'.ofFieldRangeFrobenius p R x = D' x :=
  (rfl)

end Derivation

namespace KaehlerDifferential

/-- Over any perfect ring `R` (such as `ZMod p` or a perfect subfield), the module of Kähler
differentials `Ω[k⁄R]` of a characteristic-`p` field `k` is canonically `k`-linearly isomorphic to
`Ω[k⁄(frobenius k p).fieldRange]`. -/
noncomputable def frobeniusFieldRangeEquiv (p : ℕ) (R k : Type*) [CommRing R]
    [PerfectRing R p] [Field k] [CharP k p] [ExpChar k p] [Algebra R k] :
    Ω[k⁄R] ≃ₗ[k] Ω[k⁄(frobenius k p).fieldRange] :=
  LinearEquiv.ofLinearMap
    ((D (frobenius k p).fieldRange k).ofFieldRangeFrobenius p R).liftKaehlerDifferential
    ((D R k).toFieldRangeFrobenius p).liftKaehlerDifferential
    (Derivation.liftKaehlerDifferential_unique _ _ <| Derivation.ext fun x ↦ by
      simp only [Derivation.coe_comp, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
        Derivation.coeFn_coe, LinearMap.id_apply, Derivation.liftKaehlerDifferential_comp_D,
        Derivation.toFieldRangeFrobenius_apply, Derivation.ofFieldRangeFrobenius_apply])
    (Derivation.liftKaehlerDifferential_unique _ _ <| Derivation.ext fun x ↦ by
      simp only [Derivation.coe_comp, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
        Derivation.coeFn_coe, LinearMap.id_apply, Derivation.liftKaehlerDifferential_comp_D,
        Derivation.ofFieldRangeFrobenius_apply, Derivation.toFieldRangeFrobenius_apply])

@[simp]
theorem frobeniusFieldRangeEquiv_D (p : ℕ) (R k : Type*) [CommRing R] [PerfectRing R p]
    [Field k] [CharP k p] [ExpChar k p] [Algebra R k] (x : k) :
    frobeniusFieldRangeEquiv p R k (D R k x) = D (frobenius k p).fieldRange k x :=
  (((D (frobenius k p).fieldRange k).ofFieldRangeFrobenius p R).liftKaehlerDifferential_comp_D x)

@[simp]
theorem frobeniusFieldRangeEquiv_symm_D (p : ℕ) (R k : Type*) [CommRing R]
    [PerfectRing R p] [Field k] [CharP k p] [ExpChar k p] [Algebra R k] (x : k) :
    (frobeniusFieldRangeEquiv p R k).symm (D (frobenius k p).fieldRange k x) = D R k x :=
  (((D R k).toFieldRangeFrobenius p).liftKaehlerDifferential_comp_D x)

end KaehlerDifferential

namespace TauCeti

section CoordDerivation

variable {p : ℕ} [hp : Fact p.Prime] {k : Type*} [Field k] [CharP k p] {ι : Type*}

omit hp in
private theorem mod_mul_pow_div_pow_sub_one (x : k) (n : ℕ) :
    ((n % p : ℕ) : k) * (x ^ (n / p)) ^ p * x ^ (n % p - 1) = (n : k) * x ^ (n - 1) := by
  by_cases hmod : n % p = 0
  · have hdvd : p ∣ n := Nat.dvd_of_mod_eq_zero hmod
    have hn0 : (n : k) = 0 := (CharP.cast_eq_zero_iff k p n).mpr hdvd
    simp [hmod, hn0]
  · have hcast : ((n % p : ℕ) : k) = (n : k) := by
      conv_rhs => rw [← Nat.div_add_mod n p]
      simp [CharP.cast_eq_zero]
    have hexp : p * (n / p) + (n % p - 1) = n - 1 := by
      have := Nat.div_add_mod n p
      omega
    rw [hcast, mul_assoc, ← pow_mul, mul_comm (n / p) p, ← pow_add, hexp]

private theorem deriv_pow_mul_eq (x : k) (a c : ℕ) :
    ((a + c : ℕ) : k) * x ^ (a + c - 1) =
      x ^ a * ((c : k) * x ^ (c - 1)) + ((a : k) * x ^ (a - 1)) * x ^ c := by
  rcases a with _ | a <;> rcases c with _ | c
  · simp
  · simp
  · simp [mul_comm]
  · have hexp : a + 1 + (c + 1) - 1 = a + c + 1 := by omega
    rw [hexp]
    simp only [Nat.add_sub_cancel]
    push_cast
    ring

/-- Formal `i`-th partial derivative of a `p`-monomial `pMonomial p b e`. -/
private def pMonomialDeriv [DecidableEq ι] (b : ι → k) (i : ι) (e : ι →₀ Fin p) : k :=
  ((e i : ℕ) : k) * b i ^ ((e i : ℕ) - 1) * ∏ j ∈ e.support.erase i, b j ^ (e j : ℕ)

omit [CharP k p] in
private theorem pMonomialDeriv_of_support_subset [DecidableEq ι] (b : ι → k) (i : ι)
    {e : ι →₀ Fin p} {S : Finset ι} (heS : e.support ⊆ S) :
    pMonomialDeriv b i e =
      ((e i : ℕ) : k) * b i ^ ((e i : ℕ) - 1) * ∏ j ∈ S.erase i, b j ^ (e j : ℕ) := by
  rw [pMonomialDeriv]
  congr 1
  refine prod_subset (erase_subset_erase i heS) fun j hjS hje ↦ ?_
  have hjne : j ≠ i := ne_of_mem_erase hjS
  have hjnot : j ∉ e.support := fun hmem ↦ hje (mem_erase.mpr ⟨hjne, hmem⟩)
  rw [Finsupp.notMem_support_iff.mp hjnot, Fin.val_zero, pow_zero]

private theorem pMonomial_mul_eq_smul_add (b : ι → k) {e₁ e₂ : ι →₀ Fin p} {S : Finset ι}
    (h₁ : e₁.support ⊆ S) (h₂ : e₂.support ⊆ S) :
    pMonomial p b e₁ * pMonomial p b e₂ =
      (⟨frobenius k p (∏ j ∈ S, b j ^ (((e₁ j : ℕ) + (e₂ j : ℕ)) / p)),
        (frobenius k p).mem_fieldRange_self _⟩ : (frobenius k p).fieldRange) •
        pMonomial p b (e₁ + e₂) := by
  classical
  have hadd : (e₁ + e₂).support ⊆ S :=
    Finsupp.support_add.trans (union_subset h₁ h₂)
  rw [Subfield.smul_def, smul_eq_mul]
  dsimp only
  rw [frobenius_def, pMonomial_of_support_subset p b h₁,
    pMonomial_of_support_subset p b h₂, pMonomial_of_support_subset p b hadd,
    ← prod_mul_distrib, ← prod_pow, ← prod_mul_distrib]
  refine prod_congr rfl fun j _ ↦ ?_
  rw [← pow_add, ← pow_mul, mul_comm _ p, ← pow_add, Finsupp.add_apply, Fin.val_add,
    Nat.div_add_mod]

private theorem coordLinearMap_leibniz_basis [DecidableEq ι] {b : ι → k} (hb : IsPBasis p b)
    (i : ι) (e₁ e₂ : ι →₀ Fin p) :
    let δ : k →ₗ[(frobenius k p).fieldRange] k :=
      hb.basis.constr (frobenius k p).fieldRange (pMonomialDeriv b i)
    δ (hb.basis e₁ * hb.basis e₂) =
      hb.basis e₁ * δ (hb.basis e₂) + δ (hb.basis e₁) * hb.basis e₂ := by
  intro δ
  let S : Finset ι := insert i (e₁.support ∪ e₂.support)
  have hiS : i ∈ S := mem_insert_self i _
  have h₁ : e₁.support ⊆ S := subset_union_left.trans (subset_insert i _)
  have h₂ : e₂.support ⊆ S := subset_union_right.trans (subset_insert i _)
  have hadd : (e₁ + e₂).support ⊆ S := Finsupp.support_add.trans (union_subset h₁ h₂)
  let n : ι → ℕ := fun j ↦ (e₁ j : ℕ) + (e₂ j : ℕ)
  let q : (frobenius k p).fieldRange :=
    ⟨frobenius k p (∏ j ∈ S, b j ^ (n j / p)), (frobenius k p).mem_fieldRange_self _⟩
  have hmul : hb.basis e₁ * hb.basis e₂ = q • hb.basis (e₁ + e₂) := by
    simpa only [q, n, IsPBasis.basis_apply] using pMonomial_mul_eq_smul_add b h₁ h₂
  rw [hmul, map_smul, hb.basis.constr_basis, hb.basis.constr_basis, hb.basis.constr_basis,
    hb.basis_apply, hb.basis_apply, Subfield.smul_def, smul_eq_mul,
    pMonomialDeriv_of_support_subset b i hadd, pMonomialDeriv_of_support_subset b i h₁,
    pMonomialDeriv_of_support_subset b i h₂, pMonomial_of_support_subset p b h₁,
    pMonomial_of_support_subset p b h₂]
  have hq : (q : k) = (b i ^ (n i / p)) ^ p * ∏ j ∈ S.erase i, (b j ^ (n j / p)) ^ p := by
    dsimp only [q]
    rw [frobenius_def, ← prod_pow, ← mul_prod_erase S _ hiS]
  have hrest :
      (∏ j ∈ S.erase i, (b j ^ (n j / p)) ^ p) * (∏ j ∈ S.erase i, b j ^ (((e₁ + e₂) j : ℕ))) =
        (∏ j ∈ S.erase i, b j ^ (e₁ j : ℕ)) * (∏ j ∈ S.erase i, b j ^ (e₂ j : ℕ)) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun j _ ↦ ?_
    rw [← pow_mul, mul_comm _ p, ← pow_add, Finsupp.add_apply, Fin.val_add, Nat.div_add_mod,
      pow_add]
  have hmod_i : ((e₁ + e₂) i : ℕ) = n i % p := by rw [Finsupp.add_apply, Fin.val_add]
  have hmain_i :
      (b i ^ (n i / p)) ^ p * ((((e₁ + e₂) i : ℕ) : k) * b i ^ (((e₁ + e₂) i : ℕ) - 1)) =
        (n i : k) * b i ^ (n i - 1) := by
    rw [hmod_i, ← mul_assoc, mul_comm ((b i ^ (n i / p)) ^ p), mod_mul_pow_div_pow_sub_one]
  calc (q : k) * ((((e₁ + e₂) i : ℕ) : k) * b i ^ (((e₁ + e₂) i : ℕ) - 1) *
          ∏ j ∈ S.erase i, b j ^ (((e₁ + e₂) j : ℕ)))
      = ((b i ^ (n i / p)) ^ p * ((((e₁ + e₂) i : ℕ) : k) * b i ^ (((e₁ + e₂) i : ℕ) - 1))) *
          ((∏ j ∈ S.erase i, (b j ^ (n j / p)) ^ p) *
            ∏ j ∈ S.erase i, b j ^ (((e₁ + e₂) j : ℕ))) := by
        rw [hq]
        ring
    _ = ((n i : k) * b i ^ (n i - 1)) *
          ((∏ j ∈ S.erase i, b j ^ (e₁ j : ℕ)) * (∏ j ∈ S.erase i, b j ^ (e₂ j : ℕ))) := by
        rw [hmain_i, hrest]
    _ = (b i ^ (e₁ i : ℕ) * ∏ j ∈ S.erase i, b j ^ (e₁ j : ℕ)) *
          (((e₂ i : ℕ) : k) * b i ^ ((e₂ i : ℕ) - 1) * ∏ j ∈ S.erase i, b j ^ (e₂ j : ℕ)) +
        (((e₁ i : ℕ) : k) * b i ^ ((e₁ i : ℕ) - 1) * ∏ j ∈ S.erase i, b j ^ (e₁ j : ℕ)) *
          (b i ^ (e₂ i : ℕ) * ∏ j ∈ S.erase i, b j ^ (e₂ j : ℕ)) := by
        rw [deriv_pow_mul_eq (b i) (e₁ i) (e₂ i)]
        ring
    _ = (∏ j ∈ S, b j ^ (e₁ j : ℕ)) *
          (((e₂ i : ℕ) : k) * b i ^ ((e₂ i : ℕ) - 1) * ∏ j ∈ S.erase i, b j ^ (e₂ j : ℕ)) +
        (((e₁ i : ℕ) : k) * b i ^ ((e₁ i : ℕ) - 1) * ∏ j ∈ S.erase i, b j ^ (e₁ j : ℕ)) *
          (∏ j ∈ S, b j ^ (e₂ j : ℕ)) := by
        rw [← mul_prod_erase S _ hiS, ← mul_prod_erase S _ hiS]

/-- The `i`-th coordinate derivation over `k ^ p` attached to a `p`-basis `b : ι → k`, sending
`b i` to `1` and `b j` (`j ≠ i`) to `0`. -/
noncomputable def IsPBasis.coordDerivationFieldRange {b : ι → k} (hb : IsPBasis p b) (i : ι) :
    Derivation (frobenius k p).fieldRange k k := by
  classical
  let K₀ := (frobenius k p).fieldRange
  let δ : k →ₗ[K₀] k := hb.basis.constr K₀ (pMonomialDeriv b i)
  have hleib₁ (u : k) (e₂ : ι →₀ Fin p) :
      δ (u * hb.basis e₂) = u * δ (hb.basis e₂) + δ u * hb.basis e₂ := by
    let L₁ : k →ₗ[K₀] k := δ.comp (LinearMap.mulRight K₀ (hb.basis e₂))
    let L₂ : k →ₗ[K₀] k :=
      LinearMap.mulRight K₀ (δ (hb.basis e₂)) + (LinearMap.mulRight K₀ (hb.basis e₂)).comp δ
    have hu := DFunLike.congr_fun (hb.basis.ext (f₁ := L₁) (f₂ := L₂) fun e₁ ↦ by
      simpa only [L₁, L₂, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulRight_apply]
        using coordLinearMap_leibniz_basis hb i e₁ e₂) u
    simpa only [L₁, L₂, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulRight_apply]
      using hu
  have hleib (u v : k) : δ (u * v) = u • δ v + v • δ u := by
    let R₁ : k →ₗ[K₀] k := δ.comp (LinearMap.mulLeft K₀ u)
    let R₂ : k →ₗ[K₀] k := (LinearMap.mulLeft K₀ u).comp δ + LinearMap.mulLeft K₀ (δ u)
    have hv := DFunLike.congr_fun (hb.basis.ext (f₁ := R₁) (f₂ := R₂) fun e₂ ↦ by
      simpa only [R₁, R₂, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
        using hleib₁ u e₂) v
    simpa only [R₁, R₂, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      smul_eq_mul, mul_comm v (δ u)] using hv
  exact Derivation.mk' δ hleib

@[simp]
theorem IsPBasis.coordDerivationFieldRange_apply_self {b : ι → k} (hb : IsPBasis p b) (i : ι) :
    hb.coordDerivationFieldRange i (b i) = 1 := by
  classical
  let e : ι →₀ Fin p := Finsupp.single i ⟨1, hp.out.one_lt⟩
  have hb_eq : b i = hb.basis e := by simp [e]
  have hei : e i = ⟨1, hp.out.one_lt⟩ := Finsupp.single_eq_same
  rw [hb_eq, IsPBasis.coordDerivationFieldRange]
  simp only [Derivation.coe_mk', Module.Basis.constr_basis]
  rw [pMonomialDeriv_of_support_subset b i Finsupp.support_single_subset, hei]
  simp

theorem IsPBasis.coordDerivationFieldRange_apply_of_ne {b : ι → k} (hb : IsPBasis p b) {i j : ι}
    (h : j ≠ i) :
    hb.coordDerivationFieldRange i (b j) = 0 := by
  classical
  let e : ι →₀ Fin p := Finsupp.single j ⟨1, hp.out.one_lt⟩
  have hb_eq : b j = hb.basis e := by simp [e]
  have hei : e i = 0 := Finsupp.single_eq_of_ne' h
  rw [hb_eq, IsPBasis.coordDerivationFieldRange]
  simp only [Derivation.coe_mk', Module.Basis.constr_basis, pMonomialDeriv, hei]
  simp

/-- The `i`-th coordinate `R`-derivation attached to a `p`-basis `b : ι → k` over any perfect base
ring `R`. -/
noncomputable def IsPBasis.coordDerivation (R : Type*) [CommRing R] [PerfectRing R p] [Algebra R k]
    {b : ι → k} (hb : IsPBasis p b) (i : ι) : Derivation R k k :=
  (hb.coordDerivationFieldRange i).ofFieldRangeFrobenius p R

@[simp]
theorem IsPBasis.coordDerivation_apply_self (R : Type*) [CommRing R] [PerfectRing R p]
    [Algebra R k] {b : ι → k} (hb : IsPBasis p b) (i : ι) :
    hb.coordDerivation R i (b i) = 1 :=
  hb.coordDerivationFieldRange_apply_self i

theorem IsPBasis.coordDerivation_apply_of_ne (R : Type*) [CommRing R] [PerfectRing R p]
    [Algebra R k] {b : ι → k} (hb : IsPBasis p b) {i j : ι} (h : j ≠ i) :
    hb.coordDerivation R i (b j) = 0 :=
  hb.coordDerivationFieldRange_apply_of_ne h

theorem IsPBasis.coordDerivation_apply (R : Type*) [CommRing R] [PerfectRing R p] [Algebra R k]
    [DecidableEq ι] {b : ι → k} (hb : IsPBasis p b) (i j : ι) :
    hb.coordDerivation R i (b j) = if j = i then 1 else 0 := by
  split_ifs with h
  · exact h ▸ hb.coordDerivation_apply_self R i
  · exact hb.coordDerivation_apply_of_ne R h

end CoordDerivation

section KaehlerBasis

variable {p : ℕ} [hp : Fact p.Prime] {k : Type*} [Field k] [CharP k p] {ι : Type*}

omit [CharP k p] in
/-- Formula for the image of a `p`-monomial under any derivation `D'`, expanded on a finite
superset `I ⊇ e.support`. -/
private theorem apply_pMonomial_of_support_subset [DecidableEq ι] {R M : Type*} [CommSemiring R]
    [Algebra R k] [AddCommMonoid M] [Module R M] [Module k M] (D' : Derivation R k M)
    (b : ι → k) {e : ι →₀ Fin p} {I : Finset ι} (heI : e.support ⊆ I) :
    D' (pMonomial p b e) =
      ∑ i ∈ I,
        (((e i : ℕ) : k) * b i ^ ((e i : ℕ) - 1) * ∏ j ∈ I.erase i, b j ^ (e j : ℕ)) •
          D' (b i) := by
  rw [pMonomial_of_support_subset p b heI, D'.leibniz_prod]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [D'.leibniz_pow, ← Nat.cast_smul_eq_nsmul k, smul_smul, smul_smul]
  congr 1
  ring

/-- Whenever the `p`-monomials of `b` span `k` over `k ^ p`, the differentials `D R k (b i)` span
`Ω[k⁄R]` over `k`. -/
theorem span_D_eq_top_of_span_pMonomial_eq_top (R : Type*) [CommRing R] [Algebra R k]
    {b : ι → k}
    (hspan : Submodule.span (frobenius k p).fieldRange (Set.range (pMonomial p b)) = ⊤) :
    Submodule.span k (Set.range fun i ↦ D R k (b i)) = ⊤ := by
  classical
  set N : Submodule k Ω[k⁄R] := Submodule.span k (Set.range fun i ↦ D R k (b i))
  suffices hD : ∀ x : k, D R k x ∈ N by
    rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation R k, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hD x
  intro x
  have hx : x ∈ Submodule.span (frobenius k p).fieldRange (Set.range (pMonomial p b)) :=
    hspan.symm ▸ trivial
  refine Submodule.span_induction ?_ (by simp)
    (fun u v _ _ hu hv ↦ by rw [map_add]; exact N.add_mem hu hv)
    (fun c u _ hu ↦ by
      rw [(D R k).map_smul_fieldRange_frobenius p c u]
      exact N.smul_mem (c : k) hu) hx
  rintro _ ⟨e, rfl⟩
  rw [apply_pMonomial_of_support_subset (D R k) b Subset.rfl]
  exact N.sum_mem fun i _ ↦ N.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)

/-- For a `p`-basis `b : ι → k` over a perfect ring `R`, the differentials `D R k (b i)` are
`k`-linearly independent in `Ω[k⁄R]`. -/
theorem IsPBasis.linearIndependent_D (R : Type*) [CommRing R] [PerfectRing R p] [Algebra R k]
    {b : ι → k} (hb : IsPBasis p b) :
    LinearIndependent k (fun i ↦ D R k (b i)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hc i hi
  have h := congrArg (hb.coordDerivation R i).liftKaehlerDifferential hc
  simp only [map_sum, map_smul, Derivation.liftKaehlerDifferential_comp_D,
    hb.coordDerivation_apply R i, smul_eq_mul, mul_ite, mul_one, mul_zero, sum_ite_eq', hi,
    ite_true, map_zero] at h
  exact h

/-- For a `p`-basis `b : ι → k`, the differentials `D R k (b i)` span `Ω[k⁄R]` over `k`. -/
theorem IsPBasis.span_D (R : Type*) [CommRing R] [Algebra R k] {b : ι → k} (hb : IsPBasis p b) :
    Submodule.span k (Set.range fun i ↦ D R k (b i)) = ⊤ :=
  span_D_eq_top_of_span_pMonomial_eq_top R hb.span_eq

/-- A `p`-basis `b : ι → k` induces a `k`-basis `D R k (b i)` of `Ω[k⁄R]` over any perfect base
ring `R` (such as `ZMod p` or a perfect subfield). -/
noncomputable def IsPBasis.kaehlerBasis (R : Type*) [CommRing R] [PerfectRing R p] [Algebra R k]
    {b : ι → k} (hb : IsPBasis p b) : Module.Basis ι k Ω[k⁄R] :=
  Module.Basis.mk (hb.linearIndependent_D R) (hb.span_D R).ge

@[simp]
theorem IsPBasis.kaehlerBasis_apply (R : Type*) [CommRing R] [PerfectRing R p] [Algebra R k]
    {b : ι → k} (hb : IsPBasis p b) (i : ι) :
    hb.kaehlerBasis R i = D R k (b i) :=
  Module.Basis.mk_apply (hb.linearIndependent_D R) (hb.span_D R).ge i

/-- Coordinates in `hb.kaehlerBasis R` of `D R k x` are given by `hb.coordDerivation R i x`. -/
@[simp]
theorem IsPBasis.kaehlerBasis_repr_D (R : Type*) [CommRing R] [PerfectRing R p] [Algebra R k]
    {b : ι → k} (hb : IsPBasis p b) (x : k) (i : ι) :
    (hb.kaehlerBasis R).repr (D R k x) i = hb.coordDerivation R i x := by
  classical
  let φ : Ω[k⁄R] →ₗ[k] k :=
    (Finsupp.lapply i).comp (hb.kaehlerBasis R).repr.toLinearMap
  have hcomp : φ = (hb.coordDerivation R i).liftKaehlerDifferential := by
    refine (hb.kaehlerBasis R).ext fun j ↦ ?_
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply, Module.Basis.repr_self,
      hb.kaehlerBasis_apply R, Derivation.liftKaehlerDifferential_comp_D,
      hb.coordDerivation_apply R i j, Finsupp.single_apply, eq_comm]
  simpa only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply,
    Derivation.liftKaehlerDifferential_comp_D] using DFunLike.congr_fun hcomp (D R k x)

/-- For a finite `p`-basis `b : ι → k`, `dim_k Ω[k⁄R] = Fintype.card ι`. -/
theorem IsPBasis.finrank_kaehlerDifferential (R : Type*) [CommRing R] [PerfectRing R p]
    [Algebra R k] [Fintype ι] {b : ι → k} (hb : IsPBasis p b) :
    Module.finrank k Ω[k⁄R] = Fintype.card ι :=
  Module.finrank_eq_card_basis (hb.kaehlerBasis R)

end KaehlerBasis

section Converse

variable {p : ℕ} [hp : Fact p.Prime] {k : Type*} [Field k] [CharP k p] {ι : Type*}

private def pMonomialDeg (e : ι →₀ Fin p) : ℕ :=
  e.sum fun _ m ↦ (m : ℕ)

private theorem pMonomialDeg_eq_zero_iff {e : ι →₀ Fin p} :
    pMonomialDeg e = 0 ↔ e = 0 := by
  rw [pMonomialDeg, Finsupp.sum, sum_eq_zero_iff]
  refine ⟨fun h ↦ Finsupp.ext fun i ↦ ?_, fun h ↦ by simp [h]⟩
  by_cases hi : i ∈ e.support
  · exact Fin.ext (h i hi)
  · exact Finsupp.notMem_support_iff.mp hi

private noncomputable def decrExp (e : ι →₀ Fin p) (i : ι) : ι →₀ Fin p :=
  e.update i ⟨(e i : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) (e i).isLt⟩

private theorem incr_decrExp {e : ι →₀ Fin p} {i : ι} (hei : e i ≠ 0) :
    let m1 : Fin p := ⟨1, hp.out.one_lt⟩
    (decrExp e i).update i ((decrExp e i) i + m1) = e := by
  classical
  intro m1
  have hpos : 0 < (e i : ℕ) := Fin.pos_iff_ne_zero.mpr hei
  have hval : (decrExp e i) i + m1 = e i := by
    apply Fin.ext
    rw [decrExp, Finsupp.coe_update, Function.update_self, Fin.val_add]
    have hlt : (e i : ℕ) - 1 + 1 < p := by
      rw [Nat.sub_add_cancel hpos]
      exact (e i).isLt
    rw [Nat.mod_eq_of_lt hlt, Nat.sub_add_cancel hpos]
  rw [hval, decrExp, Finsupp.update_idem, Finsupp.update_self]

private theorem pMonomialDeg_decrExp_add_one {e : ι →₀ Fin p} {i : ι} (hei : e i ≠ 0) :
    pMonomialDeg (decrExp e i) + 1 = pMonomialDeg e := by
  classical
  have hi : i ∈ e.support := Finsupp.mem_support_iff.mpr hei
  have hpos : 1 ≤ (e i : ℕ) := Fin.pos_iff_ne_zero.mpr hei
  have hsub : (decrExp e i).support ⊆ e.support := by
    refine (Finsupp.support_update_subset e i).trans ?_
    exact insert_subset hi Subset.rfl
  rw [pMonomialDeg, (decrExp e i).sum_of_support_subset hsub _ (by simp), pMonomialDeg, Finsupp.sum,
    ← add_sum_erase _ _ hi, ← add_sum_erase _ _ hi]
  have hself : ((decrExp e i) i : ℕ) = (e i : ℕ) - 1 := by
    simp [decrExp]
  have herase : ∑ j ∈ e.support.erase i, ((decrExp e i) j : ℕ) =
      ∑ j ∈ e.support.erase i, (e j : ℕ) :=
    sum_congr rfl fun j hj ↦ by simp [decrExp, Function.update_of_ne (ne_of_mem_erase hj)]
  rw [hself, herase]
  omega

omit [CharP k p] in
private theorem pMonomial_decrExp [DecidableEq ι] (b : ι → k) {e : ι →₀ Fin p} {I : Finset ι}
    (heI : e.support ⊆ I) {i : ι} (hiI : i ∈ I) :
    pMonomial p b (decrExp e i) =
      b i ^ ((e i : ℕ) - 1) * ∏ j ∈ I.erase i, b j ^ (e j : ℕ) := by
  have hsub : (decrExp e i).support ⊆ I :=
    (Finsupp.support_update_subset e i).trans (insert_subset hiI heI)
  rw [pMonomial_of_support_subset p b hsub, ← mul_prod_erase I _ hiI]
  simp only [decrExp, Finsupp.coe_update, Function.update_self]
  congr 1
  exact prod_congr rfl fun j hj ↦ by rw [Function.update_of_ne (ne_of_mem_erase hj)]

private theorem map_sum_smul_pMonomial [DecidableEq ι] {R : Type*} [CommRing R] [Algebra R k]
    (b : ι → k) (s : Finset (ι →₀ Fin p))
    (c : (ι →₀ Fin p) → (frobenius k p).fieldRange) :
    D R k (∑ e ∈ s, c e • pMonomial p b e) =
      ∑ i ∈ s.biUnion Finsupp.support,
        (∑ e ∈ s.filter (fun e ↦ e i ≠ 0),
          (c e : k) * ((e i : ℕ) : k) * pMonomial p b (decrExp e i)) • D R k (b i) := by
  let I : Finset ι := s.biUnion Finsupp.support
  rw [map_sum]
  have hterm (e : ι →₀ Fin p) (he : e ∈ s) :
      D R k (c e • pMonomial p b e) =
        ∑ i ∈ I,
          (if e i ≠ 0 then (c e : k) * ((e i : ℕ) : k) * pMonomial p b (decrExp e i)
            else 0) • D R k (b i) := by
    have heI : e.support ⊆ I := subset_biUnion_of_mem Finsupp.support he
    rw [(D R k).map_smul_fieldRange_frobenius p (c e),
      apply_pMonomial_of_support_subset (D R k) b heI, smul_sum]
    refine sum_congr rfl fun i hiI ↦ ?_
    by_cases hei : e i = 0
    · simp [hei]
    · simp only [Ne, hei, not_false_eq_true, ↓reduceIte]
      rw [pMonomial_decrExp b heI hiI, smul_smul]
      congr 1
      ring
  rw [sum_congr rfl hterm, sum_comm]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← sum_smul, sum_filter]

private theorem eq_zero_of_ne_zero_of_linearIndependent_D {R : Type*}
    [CommRing R] [Algebra R k] {b : ι → k} (hli : LinearIndependent k (fun i ↦ D R k (b i)))
    {N : ℕ}
    (ih : ∀ (s : Finset (ι →₀ Fin p)) (c : (ι →₀ Fin p) → (frobenius k p).fieldRange),
      (∀ e ∈ s, pMonomialDeg e ≤ N) → ∑ e ∈ s, c e • pMonomial p b e = 0 → ∀ e ∈ s, c e = 0)
    {s : Finset (ι →₀ Fin p)} {c : (ι →₀ Fin p) → (frobenius k p).fieldRange}
    (hdeg : ∀ e ∈ s, pMonomialDeg e ≤ N + 1) (hc : ∑ e ∈ s, c e • pMonomial p b e = 0)
    {e : ι →₀ Fin p} (he : e ∈ s) {i : ι} (hei : e i ≠ 0) :
    c e = 0 := by
  classical
  let I : Finset ι := s.biUnion Finsupp.support
  have hD0 : ∑ j ∈ I,
      (∑ e' ∈ s.filter (fun e' ↦ e' j ≠ 0),
        (c e' : k) * ((e' j : ℕ) : k) * pMonomial p b (decrExp e' j)) • D R k (b j) = 0 := by
    rw [← map_sum_smul_pMonomial b s c, hc, map_zero]
  have hiI : i ∈ I := mem_biUnion.mpr ⟨e, he, Finsupp.mem_support_iff.mpr hei⟩
  have hcoeff : ∑ e' ∈ s.filter (fun e' ↦ e' i ≠ 0),
      (c e' : k) * ((e' i : ℕ) : k) * pMonomial p b (decrExp e' i) = 0 :=
    linearIndependent_iff'.mp hli I _ hD0 i hiI
  let m1 : Fin p := ⟨1, hp.out.one_lt⟩
  let incr : (ι →₀ Fin p) → (ι →₀ Fin p) := fun f ↦ f.update i (f i + m1)
  let natK₀ : ℕ → (frobenius k p).fieldRange := fun m ↦
    ⟨(m : k), (m : k), map_natCast (frobenius k p) m⟩
  let t : Finset (ι →₀ Fin p) := s.filter (fun e' ↦ e' i ≠ 0)
  let s' : Finset (ι →₀ Fin p) := t.image (fun e' ↦ decrExp e' i)
  let c' : (ι →₀ Fin p) → (frobenius k p).fieldRange := fun f ↦
    c (incr f) * natK₀ ((incr f) i)
  have hinj : Set.InjOn (fun e' : ι →₀ Fin p ↦ decrExp e' i) t := fun e₁ he₁ e₂ he₂ h ↦ by
    have ⟨_, he₁_ne⟩ : e₁ ∈ s ∧ e₁ i ≠ 0 := by simpa [t] using he₁
    have ⟨_, he₂_ne⟩ : e₂ ∈ s ∧ e₂ i ≠ 0 := by simpa [t] using he₂
    have h₁ : incr (decrExp e₁ i) = e₁ := incr_decrExp he₁_ne
    have h₂ : incr (decrExp e₂ i) = e₂ := incr_decrExp he₂_ne
    exact h₁.symm.trans ((congrArg incr h).trans h₂)
  have hs'deg : ∀ f ∈ s', pMonomialDeg f ≤ N := by
    intro f hf
    rcases mem_image.mp hf with ⟨e', he', rfl⟩
    have h1 := pMonomialDeg_decrExp_add_one (mem_filter.mp he').2
    have h2 := hdeg e' (mem_filter.mp he').1
    omega
  have hs'sum : ∑ f ∈ s', c' f • pMonomial p b f = 0 := by
    rw [sum_image hinj]
    convert hcoeff using 2 with e' he'
    have hinv : incr (decrExp e' i) = e' := incr_decrExp (mem_filter.mp he').2
    simp [c', natK₀, hinv, Subfield.smul_def]
  have hc'0 : c' (decrExp e i) = 0 :=
    ih s' c' hs'deg hs'sum (decrExp e i) (mem_image_of_mem _ (mem_filter.mpr ⟨he, hei⟩))
  have hc'_eq : c' (decrExp e i) = c e * natK₀ (e i) := by
    dsimp only [c', incr]
    rw [incr_decrExp hei]
  rw [hc'_eq] at hc'0
  have hnat_ne : natK₀ (e i) ≠ 0 := by
    intro h0
    have hk0 : ((e i : ℕ) : k) = 0 := congrArg Subtype.val h0
    have hdvd : p ∣ (e i : ℕ) := (CharP.cast_eq_zero_iff k p _).mp hk0
    exact Nat.not_dvd_of_pos_of_lt (Fin.pos_iff_ne_zero.mpr hei) (e i).isLt hdvd
  exact (mul_eq_zero.mp hc'0).resolve_right hnat_ne

/-- If the differentials `D R k (b i)` are `k`-linearly independent in `Ω[k⁄R]`, then `b` is
`p`-independent over `k ^ p`. This holds over any commutative base ring `R`. -/
theorem isPIndependent_of_linearIndependent_D {R : Type*} [CommRing R] [Algebra R k]
    {b : ι → k} (hli : LinearIndependent k (fun i ↦ D R k (b i))) :
    IsPIndependent p b := by
  classical
  rw [isPIndependent_def, linearIndependent_iff']
  suffices hind : ∀ (N : ℕ) (s : Finset (ι →₀ Fin p))
      (c : (ι →₀ Fin p) → (frobenius k p).fieldRange),
      (∀ e ∈ s, pMonomialDeg e ≤ N) → ∑ e ∈ s, c e • pMonomial p b e = 0 →
      ∀ e ∈ s, c e = 0 by
    intro s c hc e he
    exact hind (s.sup pMonomialDeg) s c (fun e' he' ↦ le_sup he') hc e he
  intro N
  induction N with
  | zero =>
    intro s c hdeg hc e₀ he₀
    have hs0 : ∀ e ∈ s, e = 0 := fun e he ↦
      pMonomialDeg_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (hdeg e he))
    have he₀0 : e₀ = 0 := hs0 e₀ he₀
    subst he₀0
    have hsum : ∑ e ∈ s, c e • pMonomial p b e = c 0 • pMonomial p b 0 :=
      sum_eq_single 0 (fun e he hne ↦ (hne (hs0 e he)).elim) (fun hnot ↦ (hnot he₀).elim)
    rw [hsum, pMonomial_zero, Subfield.smul_def, smul_eq_mul, mul_one] at hc
    exact Subtype.ext hc
  | succ N ih =>
    intro s c hdeg hc e₀ he₀
    have hce_ne0 : ∀ e ∈ s, e ≠ 0 → c e = 0 := by
      intro e he hne
      obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hne
      exact eq_zero_of_ne_zero_of_linearIndependent_D hli ih hdeg hc he
        (Finsupp.mem_support_iff.mp hi)
    by_cases he₀0 : e₀ = 0
    · subst he₀0
      have hsum : ∑ e ∈ s, c e • pMonomial p b e = c 0 • pMonomial p b 0 :=
        sum_eq_single 0 (fun e he hne ↦ by rw [hce_ne0 e he hne, zero_smul])
          (fun hnot ↦ (hnot he₀).elim)
      rw [hsum, pMonomial_zero, Subfield.smul_def, smul_eq_mul, mul_one] at hc
      exact Subtype.ext hc
    · exact hce_ne0 e₀ he₀ he₀0

/-- Over a perfect base ring `R`, if the differentials `D R k (b i)` are linearly independent and
span `Ω[k⁄R]`, then `b` is a `p`-basis of `k`. -/
theorem isPBasis_of_linearIndependent_of_span_D (R : Type*) [CommRing R] [PerfectRing R p]
    [Algebra R k] {b : ι → k} (hli : LinearIndependent k (fun i ↦ D R k (b i)))
    (hspan : Submodule.span k (Set.range fun i ↦ D R k (b i)) = ⊤) :
    IsPBasis p b := by
  have hb_ind : IsPIndependent p b := isPIndependent_of_linearIndependent_D hli
  refine (isPBasis_def p).mpr ⟨hb_ind, ?_⟩
  rw [eq_top_iff]
  intro x _
  by_contra hx
  let b' : ι ⊕ Unit → k := Sum.elim b (fun _ : Unit ↦ x)
  have hb' : IsPIndependent p b' := (isPIndependent_sumElim_unique_iff).mpr ⟨hb_ind, hx⟩
  obtain ⟨t, ht_sub, ht⟩ := hb'.exists_isPBasis_range_superset
  let f : ι ⊕ Unit → t := fun z ↦ ⟨b' z, ht_sub (Set.mem_range_self z)⟩
  have hf_inj : Function.Injective f := fun z₁ z₂ h ↦
    hb'.injective hp.out.one_lt (congrArg Subtype.val h)
  have hli_t : LinearIndependent k (fun y : t ↦ D R k y) := ht.linearIndependent_D R
  have hli_sum : LinearIndependent k (Sum.elim (fun i ↦ D R k (b i)) (fun _ : Unit ↦ D R k x)) := by
    convert hli_t.comp f hf_inj using 1
    ext (i | ⟨⟩) <;> rfl
  obtain ⟨_, hli_unit, hdisj⟩ := linearIndependent_sum.mp hli_sum
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at hli_unit hdisj
  rw [hspan] at hdisj
  have hDx0 : D R k x = 0 :=
    Submodule.disjoint_def.mp hdisj (D R k x) trivial (Submodule.subset_span ⟨(), rfl⟩)
  exact (linearIndependent_unique_iff.mp hli_unit) hDx0

/-- **Stacks Tag 07P2**: over a perfect base ring `R` (in particular `R = ZMod p`), a family
`b : ι → k` is a `p`-basis of `k` if and only if its differentials `D R k (b i)` are `k`-linearly
independent and span `Ω[k⁄R]`. -/
theorem isPBasis_iff_linearIndependent_and_span_D (R : Type*) [CommRing R] [PerfectRing R p]
    [Algebra R k] {b : ι → k} :
    IsPBasis p b ↔
      LinearIndependent k (fun i ↦ D R k (b i)) ∧
        Submodule.span k (Set.range fun i ↦ D R k (b i)) = ⊤ :=
  ⟨fun hb ↦ ⟨hb.linearIndependent_D R, hb.span_D R⟩,
    fun ⟨hli, hspan⟩ ↦ isPBasis_of_linearIndependent_of_span_D R hli hspan⟩

end Converse

end TauCeti

/-- Any `k`-basis of `Ω[k⁄R]` consisting of differentials `D R k (b i)` comes from a `p`-basis `b`
of `k`. -/
theorem Module.Basis.isPBasis_of_eq_D (p : ℕ) [Fact p.Prime] {R k ι : Type*} [CommRing R]
    [PerfectRing R p] [Field k] [CharP k p] [Algebra R k] (B : Module.Basis ι k Ω[k⁄R])
    {b : ι → k} (hB : ∀ i, B i = D R k (b i)) :
    TauCeti.IsPBasis p b := by
  have hfun : (fun i ↦ D R k (b i)) = ⇑B := funext fun i ↦ (hB i).symm
  rw [TauCeti.isPBasis_iff_linearIndependent_and_span_D R, hfun]
  exact ⟨B.linearIndependent, B.span_eq⟩

namespace TauCeti

section Finiteness

variable (p : ℕ) [hp : Fact p.Prime] (R k : Type*) [CommRing R] [PerfectRing R p]
  [Field k] [CharP k p] [Algebra R k]

/-- **Finiteness criterion for Kähler differentials**: without assuming `[k : k ^ p]` finite,
`Ω[k⁄R]` is finite-dimensional over `k` if and only if `k` is finite-dimensional over its subfield
`k ^ p = (frobenius k p).fieldRange` of `p`-th powers. -/
theorem finiteDimensional_kaehlerDifferential_iff :
    FiniteDimensional k Ω[k⁄R] ↔ FiniteDimensional (frobenius k p).fieldRange k := by
  obtain ⟨s, hs⟩ := exists_isPBasis p k
  rw [← hs.finite_iff_finiteDimensional]
  constructor
  · intro _
    let _ : Fintype s := FiniteDimensional.fintypeBasisIndex (hs.kaehlerBasis R)
    infer_instance
  · intro _
    cases nonempty_fintype s
    exact (hs.kaehlerBasis R).finiteDimensional_of_finite

/-- When `k` is finite-dimensional over `k ^ p` (equivalently `Ω[k⁄R]` is finite-dimensional over
`k`), `[k : k ^ p] = p ^ dim_k Ω[k⁄R]`. -/
theorem finrank_fieldRange_frobenius_eq_pow_finrank_kaehlerDifferential
    [FiniteDimensional (frobenius k p).fieldRange k] :
    Module.finrank (frobenius k p).fieldRange k = p ^ Module.finrank k Ω[k⁄R] := by
  obtain ⟨s, hs⟩ := exists_isPBasis p k
  have : Finite s := hs.finite_iff_finiteDimensional.mpr ‹_›
  cases nonempty_fintype s
  rw [hs.finrank_fieldRange_frobenius, hs.finrank_kaehlerDifferential R]

include p in
/-- Over a perfect base ring `R`, `Ω[k⁄R]` is trivial if and only if `k` is a perfect field. -/
theorem subsingleton_kaehlerDifferential_iff_perfectField :
    Subsingleton Ω[k⁄R] ↔ PerfectField k := by
  obtain ⟨s, hs⟩ := exists_isPBasis p k
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have : IsEmpty s := ⟨fun x ↦ (hs.kaehlerBasis R).ne_zero x (Subsingleton.elim _ _)⟩
    exact (isPBasis_of_isEmpty_iff_perfectField ((↑) : s → k)).mp hs
  · have : IsEmpty s := ⟨fun x ↦ by
      have hmem : (x : k) ∈ (frobenius k p).fieldRange := by
        rw [fieldRange_frobenius_eq_top_iff_perfectField.mpr ‹_›]
        trivial
      exact not_isPBasis_of_mem_fieldRange_frobenius hp.out.one_lt (i := x) hmem hs⟩
    exact (hs.kaehlerBasis R).repr.subsingleton

include p in
/-- Over a perfect base ring `R`, any perfect field `k` of characteristic `p` has trivial Kähler
differentials `Ω[k⁄R]`. -/
instance subsingleton_kaehlerDifferential_of_perfectField [PerfectField k] :
    Subsingleton Ω[k⁄R] :=
  (subsingleton_kaehlerDifferential_iff_perfectField p R k).mpr ‹_›

end Finiteness

section FunctionFields

/-- For a univariate rational function field `RatFunc k₀` over a perfect field `k₀` of
characteristic `p`, the indeterminate `RatFunc.X` (indexed by `[Unique ι]`) is a `p`-basis. -/
theorem isPBasis_ratFunc_X (p : ℕ) [Fact p.Prime] (k₀ ι : Type*) [Field k₀] [CharP k₀ p]
    [PerfectField k₀] [Unique ι] :
    IsPBasis p (fun _ : ι ↦ (RatFunc.X : RatFunc k₀)) := by
  have : CharP (RatFunc k₀) p :=
    charP_of_injective_algebraMap (algebraMap k₀ (RatFunc k₀)).injective p
  exact ((kaehlerBasisRatFunc k₀).reindex (Equiv.ofUnique Unit ι)).isPBasis_of_eq_D p
    fun i ↦ by simp

/-- Over a perfect field `k₀` of characteristic `p`, `[k₀(X) : k₀(X) ^ p] = p`. -/
@[simp]
theorem finrank_fieldRange_frobenius_ratFunc (p : ℕ) [Fact p.Prime] (k₀ : Type*) [Field k₀]
    [CharP k₀ p] [PerfectField k₀] :
    Module.finrank (frobenius (RatFunc k₀) p).fieldRange (RatFunc k₀) = p := by
  have : CharP (RatFunc k₀) p :=
    charP_of_injective_algebraMap (algebraMap k₀ (RatFunc k₀)).injective p
  simpa using (isPBasis_ratFunc_X p k₀ Unit).finrank_fieldRange_frobenius

/-- In `RatFunc k₀` of characteristic `p`, `D k₀ (RatFunc k₀) (RatFunc.X ^ p) = 0`. -/
theorem D_ratFunc_X_pow_char (p : ℕ) (k₀ : Type*) [Field k₀] [CharP k₀ p] :
    D k₀ (RatFunc k₀) ((RatFunc.X : RatFunc k₀) ^ p) = 0 := by
  have : CharP (RatFunc k₀) p :=
    charP_of_injective_algebraMap (algebraMap k₀ (RatFunc k₀)).injective p
  exact (D k₀ (RatFunc k₀)).map_pow_char p RatFunc.X

/-- Although `{X ^ p}` is a transcendence basis of `RatFunc k₀` over `k₀`
(`TauCeti.RatFunc.isTranscendenceBasis_X_pow`), it is never a `p`-basis in prime characteristic `p`:
`X ^ p` lies in `(RatFunc k₀) ^ p` and its differential vanishes. -/
theorem not_isPBasis_ratFunc_X_pow_char (p : ℕ) [hp : Fact p.Prime] (k₀ ι : Type*) [Field k₀]
    [CharP k₀ p] [Nonempty ι] :
    ¬ IsPBasis p (fun _ : ι ↦ (RatFunc.X : RatFunc k₀) ^ p) := by
  have : CharP (RatFunc k₀) p :=
    charP_of_injective_algebraMap (algebraMap k₀ (RatFunc k₀)).injective p
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact not_isPBasis_of_mem_fieldRange_frobenius hp.out.one_lt (i := i) ⟨RatFunc.X, rfl⟩

/-- The differentials of the variables `X i` (`i : σ`) form a basis of the Kähler differentials of
`FractionRing (MvPolynomial σ R)` over any commutative ring `R`. -/
noncomputable def kaehlerBasisFractionRingMvPolynomial (R σ : Type*) [CommRing R] :
    Module.Basis σ (FractionRing (MvPolynomial σ R))
      Ω[FractionRing (MvPolynomial σ R)⁄R] :=
  haveI : Algebra.FormallyEtale (MvPolynomial σ R) (FractionRing (MvPolynomial σ R)) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := FractionRing (MvPolynomial σ R))
      (MvPolynomial σ R)⁰
  kaehlerBasisOfFormallyEtale R (MvPolynomial σ R) (FractionRing (MvPolynomial σ R))
    (KaehlerDifferential.mvPolynomialBasis R σ)

@[simp]
theorem kaehlerBasisFractionRingMvPolynomial_apply (R σ : Type*) [CommRing R] (i : σ) :
    kaehlerBasisFractionRingMvPolynomial R σ i =
      D R (FractionRing (MvPolynomial σ R))
        (algebraMap (MvPolynomial σ R) (FractionRing (MvPolynomial σ R)) (.X i)) := by
  have : Algebra.FormallyEtale (MvPolynomial σ R) (FractionRing (MvPolynomial σ R)) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := FractionRing (MvPolynomial σ R))
      (MvPolynomial σ R)⁰
  rw [kaehlerBasisFractionRingMvPolynomial, kaehlerBasisOfFormallyEtale_apply]
  simp [KaehlerDifferential.map_D]

/-- Over a perfect field `k₀` of characteristic `p`, the variables `X i` (`i : σ`) form a `p`-basis
of `FractionRing (MvPolynomial σ k₀)` for any (finite or infinite) index type `σ`. -/
theorem isPBasis_fractionRing_mvPolynomial_X (p : ℕ) [Fact p.Prime] (k₀ σ : Type*) [Field k₀]
    [CharP k₀ p] [PerfectField k₀] :
    IsPBasis p (fun i : σ ↦
      algebraMap (MvPolynomial σ k₀) (FractionRing (MvPolynomial σ k₀)) (.X i)) :=
  (kaehlerBasisFractionRingMvPolynomial k₀ σ).isPBasis_of_eq_D p
    (kaehlerBasisFractionRingMvPolynomial_apply k₀ σ)

/-- In infinitely many variables `σ`, `Ω[FractionRing (MvPolynomial σ k₀)⁄k₀]` is not
finite-dimensional over `FractionRing (MvPolynomial σ k₀)`. -/
theorem not_finiteDimensional_kaehlerDifferential_fractionRing_mvPolynomial (k₀ σ : Type*)
    [Field k₀] [Infinite σ] :
    ¬ FiniteDimensional (FractionRing (MvPolynomial σ k₀))
        Ω[FractionRing (MvPolynomial σ k₀)⁄k₀] := by
  intro _
  let _ : Fintype σ :=
    FiniteDimensional.fintypeBasisIndex (kaehlerBasisFractionRingMvPolynomial k₀ σ)
  exact not_finite σ

/-- In infinitely many variables `σ` over a perfect field `k₀` of characteristic `p`, `k₀(X_i)` is
not finite-dimensional over its subfield of `p`-th powers. -/
theorem not_finiteDimensional_fieldRange_frobenius_fractionRing_mvPolynomial (p : ℕ)
    [Fact p.Prime] (k₀ σ : Type*) [Field k₀] [CharP k₀ p] [PerfectField k₀] [Infinite σ] :
    ¬ FiniteDimensional
        (frobenius (FractionRing (MvPolynomial σ k₀)) p).fieldRange
        (FractionRing (MvPolynomial σ k₀)) := by
  rw [← finiteDimensional_kaehlerDifferential_iff p k₀]
  exact not_finiteDimensional_kaehlerDifferential_fractionRing_mvPolynomial k₀ σ

/-- Over any domain `R`, the fraction field of `MvPolynomial σ R` has transcendence degree `#σ`
(up to universe lift). -/
@[simp]
theorem trdeg_fractionRing_mvPolynomial.{u, v} (R : Type u) (σ : Type v)
    [CommRing R] [IsDomain R] :
    Algebra.trdeg R (FractionRing (MvPolynomial σ R)) =
      Cardinal.lift.{u} (Cardinal.mk σ) := by
  let S := MvPolynomial σ R
  let K := FractionRing S
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr <| by
    rw [MvPolynomial.algebraMap_eq]
    exact MvPolynomial.C_injective σ R
  have : FaithfulSMul S K :=
    (faithfulSMul_iff_algebraMap_injective S K).mpr (IsFractionRing.injective S K)
  have : Algebra.IsAlgebraic S K := (IsFractionRing.isAlgebraic_iff' S S K).mp inferInstance
  exact (trdeg_eq_of_isAlgebraic (R := R) (S' := S) (A' := K)).trans MvPolynomial.trdeg_of_isDomain

/-- Passing from a field `K` of characteristic `p` to `PerfectClosure K p` preserves transcendence
degree over `ZMod p`. -/
@[simp]
theorem trdeg_zmod_perfectClosure (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] [Algebra (ZMod p) (PerfectClosure K p)] :
    Algebra.trdeg (ZMod p) (PerfectClosure K p) = Algebra.trdeg (ZMod p) K := by
  let _ : Algebra K (PerfectClosure K p) := (PerfectClosure.of K p).toAlgebra
  have : IsScalarTower (ZMod p) K (PerfectClosure K p) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : IsPRadical (algebraMap K (PerfectClosure K p)) p := PerfectClosure.isPRadical K p
  have : IsPurelyInseparable K (PerfectClosure K p) :=
    IsPRadical.isPurelyInseparable K (PerfectClosure K p) p
  exact trdeg_eq_of_isAlgebraic (R := ZMod p) (S' := K) (A' := PerfectClosure K p)

/-- The perfect closure of `FractionRing (MvPolynomial σ (ZMod p))` in infinitely many variables `σ`
has infinite transcendence degree over `ZMod p`, even though its Kähler differentials vanish
(`subsingleton_kaehlerDifferential_of_perfectField`) and `[L : L ^ p] = 1`
(`finrank_fieldRange_frobenius_of_perfectField`). -/
theorem aleph0_le_trdeg_zmod_perfectClosure_fractionRing_mvPolynomial (p : ℕ) [Fact p.Prime]
    (σ : Type*) [Infinite σ]
    [Algebra (ZMod p) (PerfectClosure (FractionRing (MvPolynomial σ (ZMod p))) p)] :
    Cardinal.aleph0 ≤
      Algebra.trdeg (ZMod p) (PerfectClosure (FractionRing (MvPolynomial σ (ZMod p))) p) := by
  rw [trdeg_zmod_perfectClosure, trdeg_fractionRing_mvPolynomial, Cardinal.lift_uzero]
  exact Cardinal.aleph0_le_mk σ

end FunctionFields

end TauCeti
