/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.Polynomial.Pochhammer
import TauCeti.RingTheory.PreLambdaRing.Ideal
import TauCeti.RingTheory.PreLambdaRing.MonoidAlgebra

/-!
# Tests: pre-`λ`-rings, morphisms, `λ`-ideals, and line-monomial structures

This file exercises the pre-`λ`-ring API on concrete integer, quotient, Laurent/polynomial, and
locally constant examples:

* in binomial `ℤ`, `λ²(2) = 1` and `λ²(1) = 0`, so `λ²` is not additive and `(2)` is not a
  `λ`-ideal;
* the sum-law structure `λ_t(m) = (1 + X + X²)^m` on `ℤ` is a valid `PreLambdaRing` structure with
  `λ²(1) = 1`, and `RingHom.id ℤ` from binomial `ℤ` to this structure is not a pre-`λ` morphism;
* the zero and whole ideals of any pre-`λ`-ring `R` are `λ`-ideals with quotients `R ⧸ ⊥ ≃λ+* R`
  and subsingleton `R ⧸ ⊤`, whereas quotienting binomial `ℤ` by `(2)` cannot preserve `λ²` and
  admits no quotient `PreLambdaRing` structure;
* `0` is a line element in every pre-`λ`-ring and is not a unit in a nontrivial ring; in the
  line-monomial structure on `ℤ[u, u⁻¹] = MonoidAlgebra ℤ (Multiplicative ℤ)`,
  `λ²(u + u⁻¹) = 1`; and `ℤ[u] = MonoidAlgebra ℤ (Multiplicative ℕ)` carries the line-monomial
  `PreLambdaRing` structure even though it admits no `BinomialRing` structure;
* locally constant operations on two discrete points (`Bool`) act componentwise via
  `LocallyConstant Bool R ≃λ+* R × R`, the empty space gives a subsingleton ring, and the trivial
  monoid `PUnit` gives binomial `ℤ` via `MonoidAlgebra ℤ PUnit ≃λ+* ℤ`.
-/

open PowerSeries

namespace TauCeti

/-! ### Binomial `ℤ` and failure of `(2)` to be a `λ`-ideal -/

/-- *binomialInt_lambdaOp_two*: in binomial `ℤ`, `λ²(2) = 1` and `λ²(1) = 0`. -/
example : lambdaOp 2 (2 : ℤ) = 1 ∧ lambdaOp 2 (1 : ℤ) = 0 :=
  ⟨lambdaOp_int_natCast 2 2, lambdaOp_int_natCast 2 1⟩

/-- *binomialInt_lambdaOp_two_not_additive*: `λ²` on binomial `ℤ` is not additive. -/
example : lambdaOp 2 ((1 : ℤ) + 1) ≠ lambdaOp 2 (1 : ℤ) + lambdaOp 2 (1 : ℤ) := by
  have h2 : lambdaOp 2 ((1 : ℤ) + 1) = 1 := lambdaOp_int_natCast 2 2
  have h1 : lambdaOp 2 (1 : ℤ) = 0 := lambdaOp_int_natCast 2 1
  omega

/-- *not_isLambdaIdeal_span_two*: the ideal `(2) ⊆ ℤ` is not a `λ`-ideal for binomial `ℤ`. -/
example : ¬ (Ideal.span {(2 : ℤ)}).IsLambdaIdeal := by
  intro hI
  have hmem : lambdaOp 2 (2 : ℤ) ∈ Ideal.span {(2 : ℤ)} :=
    (Ideal.span {(2 : ℤ)}).lambdaOp_mem (by omega) (Ideal.subset_span rfl)
  have hval : lambdaOp 2 (2 : ℤ) = 1 := lambdaOp_int_natCast 2 2
  rw [hval, Ideal.mem_span_singleton] at hmem
  rcases hmem with ⟨k, hk⟩
  omega

/-! ### Sum-law structure `λ_t(m) = (1 + X + X²)^m` on `ℤ` -/

/-- *sumLawInt_check*: under the sum-law `PreLambdaRing` structure `λ_t(m) = (1 + X + X²)^m` on
`ℤ`, `λ_t(n) = (1 + X + X²)^n` for `n : ℕ`, `λ²(1) = 1`, and `RingHom.id ℤ` from binomial `ℤ` to
this structure is not a pre-`λ` morphism. -/
example (n : ℕ) :
    let sumLawInt : PreLambdaRing ℤ :=
      PreLambdaRing.intOfPowerSeries (1 + X + X ^ 2) (by simp)
        (by simp [coeff_one, coeff_X, coeff_X_pow])
    @PreLambdaRing.totalSeries ℤ _ sumLawInt (n : ℤ) = (1 + X + X ^ 2) ^ n ∧
      @lambdaOp ℤ _ sumLawInt 2 1 = 1 ∧
      ¬ @RingHom.IsPreLambdaHom ℤ ℤ _ Int.instPreLambdaRing _ sumLawInt (RingHom.id ℤ) := by
  intro sumLawInt
  have h1 : @lambdaOp ℤ _ sumLawInt 2 1 = 1 := by
    rw [PreLambdaRing.lambdaOp_intOfPowerSeries_one]
    simp [coeff_one, coeff_X, coeff_X_pow]
  refine ⟨PreLambdaRing.totalSeries_intOfPowerSeries_natCast _ _ _ n, h1, ?_⟩
  intro hf
  have h := @RingHom.IsPreLambdaHom.apply ℤ ℤ _ Int.instPreLambdaRing _ sumLawInt
    (RingHom.id ℤ) hf 2 1
  have hleft : @lambdaOp ℤ _ Int.instPreLambdaRing 2 (1 : ℤ) = 0 := lambdaOp_int_natCast 2 1
  rw [RingHom.id_apply, RingHom.id_apply, hleft, h1] at h
  omega

/-! ### Zero, whole, and non-`λ` quotients -/

section Quotients

variable (R : Type*) [CommRing R] [PreLambdaRing R]

/-- *quotient_bot_and_top*: `R ⧸ ⊥` is pre-`λ`-isomorphic to `R`, and `R ⧸ ⊤` is a subsingleton
pre-`λ`-ring. -/
example : Nonempty (PreLambdaRingEquiv (R ⧸ (⊥ : Ideal R)) R) ∧
    Subsingleton (R ⧸ (⊤ : Ideal R)) :=
  ⟨⟨Ideal.quotientBotPreLambdaRingEquiv R⟩, Ideal.Quotient.subsingleton_iff.mpr rfl⟩

/-- *quotient_span_two_no_lambdaOp_two*: no unary operation on `ℤ ⧸ (2)` commutes with `λ²` on
binomial `ℤ`, since `2 ≡ 0 (mod 2)` whereas `λ²(2) = 1 ≢ 0 = λ²(0) (mod 2)`. -/
example : ¬ ∃ op₂ : (ℤ ⧸ Ideal.span {(2 : ℤ)}) → (ℤ ⧸ Ideal.span {(2 : ℤ)}),
    ∀ z : ℤ, Ideal.Quotient.mk (Ideal.span {(2 : ℤ)}) (lambdaOp 2 z) =
      op₂ (Ideal.Quotient.mk (Ideal.span {(2 : ℤ)}) z) := by
  rintro ⟨op₂, hop⟩
  have hmk : Ideal.Quotient.mk (Ideal.span {(2 : ℤ)}) 2 =
      Ideal.Quotient.mk (Ideal.span {(2 : ℤ)}) 0 :=
    Ideal.Quotient.eq.mpr (by rw [sub_zero]; exact Ideal.subset_span (Set.mem_singleton (2 : ℤ)))
  have h20 : Ideal.Quotient.mk (Ideal.span {(2 : ℤ)}) (lambdaOp 2 (2 : ℤ)) =
      Ideal.Quotient.mk (Ideal.span {(2 : ℤ)}) (lambdaOp 2 (0 : ℤ)) := by
    rw [hop 2, hmk, ← hop 0]
  have hval2 : lambdaOp 2 (2 : ℤ) = 1 := lambdaOp_int_natCast 2 2
  rw [hval2, PreLambdaRing.lambdaOp_succ_zero, Ideal.Quotient.eq, sub_zero,
    Ideal.mem_span_singleton] at h20
  rcases h20 with ⟨k, hk⟩
  omega

/-- *quotient_span_two_no_preLambdaRing*: `ℤ ⧸ (2)` admits no `PreLambdaRing` structure making the
quotient map from binomial `ℤ` a pre-`λ` morphism. -/
example : ¬ ∃ l : PreLambdaRing (ℤ ⧸ Ideal.span {(2 : ℤ)}),
    @RingHom.IsPreLambdaHom ℤ (ℤ ⧸ Ideal.span {(2 : ℤ)}) _ _ _ l
      (Ideal.Quotient.mk (Ideal.span {(2 : ℤ)})) := by
  rw [← Ideal.isLambdaIdeal_iff_exists_preLambdaRing_quotient]
  intro hI
  have hmem : lambdaOp 2 (2 : ℤ) ∈ Ideal.span {(2 : ℤ)} :=
    (Ideal.span {(2 : ℤ)}).lambdaOp_mem (by omega) (Ideal.subset_span rfl)
  have hval : lambdaOp 2 (2 : ℤ) = 1 := lambdaOp_int_natCast 2 2
  rw [hval, Ideal.mem_span_singleton] at hmem
  rcases hmem with ⟨k, hk⟩
  omega

end Quotients

/-! ### Line elements, Laurent polynomials `ℤ[u, u⁻¹]`, and `ℤ[u]` as a non-binomial ring -/

section LineMonomial

/-- *zero_isLineElement_and_not_isUnit*: in any nontrivial pre-`λ`-ring `R`, `0` is a line element
and is not a unit. -/
example (R : Type*) [CommRing R] [PreLambdaRing R] [Nontrivial R] :
    IsLineElement (0 : R) ∧ ¬ IsUnit (0 : R) :=
  ⟨PreLambdaRing.IsLineElement.zero, not_isUnit_zero⟩

/-- *laurent_lambdaOp_two_u_add_uInv*: in the line-monomial `PreLambdaRing` structure on
`ℤ[u, u⁻¹] = MonoidAlgebra ℤ (Multiplicative ℤ)`, `λ²(u + u⁻¹) = 1`. -/
example :
    let u : MonoidAlgebra ℤ (Multiplicative ℤ) :=
      MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) 1
    let uInv : MonoidAlgebra ℤ (Multiplicative ℤ) :=
      MonoidAlgebra.single (Multiplicative.ofAdd (-1 : ℤ)) 1
    lambdaOp 2 (u + uInv) = 1 := by
  intro u uInv
  have hu : IsLineElement u := MonoidAlgebra.isLineElement_single_one _
  have huInv : IsLineElement uInv := MonoidAlgebra.isLineElement_single_one _
  rw [hu.lambdaOp_two_add huInv]
  dsimp only [u, uInv]
  rw [MonoidAlgebra.single_mul_single, ← ofAdd_add, add_neg_cancel, ofAdd_zero, mul_one,
    MonoidAlgebra.one_def]

/-- *monoidAlgebra_nat_not_binomialRing*: `ℤ[u] = MonoidAlgebra ℤ (Multiplicative ℕ)` carries the
line-monomial `PreLambdaRing` structure, yet admits no `BinomialRing` structure (because
`u (u - 1) = u² - u` is not divisible by `2` in `ℤ[u]`). -/
example : Nonempty (PreLambdaRing (MonoidAlgebra ℤ (Multiplicative ℕ))) ∧
    ¬ Nonempty (BinomialRing (MonoidAlgebra ℤ (Multiplicative ℕ))) := by
  refine ⟨⟨inferInstance⟩, ?_⟩
  rintro ⟨b⟩
  let _ : BinomialRing (MonoidAlgebra ℤ (Multiplicative ℕ)) := b
  let u : MonoidAlgebra ℤ (Multiplicative ℕ) :=
    MonoidAlgebra.single (Multiplicative.ofAdd 1) 1
  have hpoch := Ring.descPochhammer_eq_factorial_smul_choose u 2
  have heval : (descPochhammer ℤ 2).smeval u = u * (u - 1) := by
    rw [descPochhammer_succ_right ℤ 1, descPochhammer_one, Polynomial.smeval_mul,
      Polynomial.smeval_sub, Polynomial.smeval_X, pow_one, Nat.cast_one, Polynomial.smeval_one,
      pow_zero, one_smul]
  rw [heval, Nat.factorial_two] at hpoch
  have hcoeff := congrArg (fun x : MonoidAlgebra ℤ (Multiplicative ℕ) ↦
    x.coeff (Multiplicative.ofAdd 1)) hpoch
  have hlhs : (u * (u - 1)).coeff (Multiplicative.ofAdd 1) = -1 := by
    dsimp only [u]
    rw [mul_sub, mul_one, MonoidAlgebra.single_mul_single, ← ofAdd_add, mul_one]
    simp
  have hrhs : (2 • Ring.choose u 2).coeff (Multiplicative.ofAdd 1) =
      2 * (Ring.choose u 2).coeff (Multiplicative.ofAdd 1) := by
    rw [two_smul, MonoidAlgebra.coeff_add, Finsupp.add_apply, two_mul]
  omega

end LineMonomial

/-! ### Locally constant functions on `Bool` and `Empty`, and the trivial monoid `PUnit` -/

section LocallyConstantAndTrivialMonoid

variable (R : Type*) [CommRing R] [PreLambdaRing R]

/-- *locallyConstant_bool_and_empty*: `λ`-operations on `LocallyConstant Bool R` act componentwise
via `boolPreLambdaRingEquiv R`, and `LocallyConstant Empty R` is a subsingleton. -/
example (n : ℕ) (f : LocallyConstant Bool R) :
    LocallyConstant.boolPreLambdaRingEquiv R (lambdaOp n f) =
      (lambdaOp n (f false), lambdaOp n (f true)) ∧
    Subsingleton (LocallyConstant Empty R) :=
  ⟨by simp [lambdaOp_prodMk], ⟨fun g₁ g₂ ↦ LocallyConstant.ext fun x ↦ Empty.elim x⟩⟩

/-- *monoidAlgebra_punit_equiv_int*: for the trivial monoid `PUnit`, the line-monomial
`PreLambdaRing` structure on `MonoidAlgebra ℤ PUnit` is pre-`λ`-isomorphic to binomial `ℤ`. -/
example (n : ℕ) (z : ℤ) :
    MonoidAlgebra.uniquePreLambdaRingEquiv PUnit
        (lambdaOp n (MonoidAlgebra.single PUnit.unit z)) =
      Ring.choose z n := by
  rw [map_lambdaOp, MonoidAlgebra.uniquePreLambdaRingEquiv_single_one, lambdaOp_int_eq_choose]

end LocallyConstantAndTrivialMonoid

end TauCeti
