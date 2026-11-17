/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.Algebra.Cluster.CoefficientSemifield.Positive.Basic
public import TauCeti.Algebra.Cluster.CoefficientSemifield.Universal
public import TauCeti.Algebra.MvPolynomial.Laurent.Polynomial
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Comparisons and specializations for `PosZero` and `Pos`

This file establishes the canonical comparisons connecting `TauCeti.PosZero P K` and
`TauCeti.Pos P K` to Laurent total quotients, the universal coefficient semifield, the nonnegative
rationals, and the fraction ring of the integer Laurent ring `LaurentRing (MonoidAlgebra ℤ P) K`.

## Main definitions

* `TauCeti.PosZero.laurentEquiv`: the `MonoidAlgebra ℕ P`-algebra isomorphism
  `PosZero P K ≃ₐ[MonoidAlgebra ℕ P] TotalQuotient (LaurentRing (MonoidAlgebra ℕ P) K)`.
* `TauCeti.PosZero.equivQsfZero`, `TauCeti.Pos.equivQsf`: identifications with `QsfZero K` and
  `Qsf K` when `Subsingleton P`.
* `TauCeti.PosZero.isEmptyAlgEquiv`, `TauCeti.Pos.isEmptyRingEquiv`: identifications when
  `IsEmpty K`.
* `TauCeti.PosZero.equivNNRat`, `TauCeti.Pos.equivNNRatUnits`: identifications with `ℚ≥0` and
  `ℚ≥0ˣ` when `Subsingleton P` and `IsEmpty K`.
* `TauCeti.PosZero.toFractionRing`: the embedding of `PosZero P K` into
  `FractionRing (LaurentRing (MonoidAlgebra ℤ P) K)`.

## Main results

* `TauCeti.PosZero.toFractionRing_injective`: `PosZero P K` embeds injectively into
  `FractionRing (LaurentRing (MonoidAlgebra ℤ P) K)` for every commutative monoid `P`.
* `TauCeti.PosZero.toFractionRing_laurentEquiv_symm_algebraMap`: compatibility of `toFractionRing`
  with `laurentEquiv` and casting coefficients of Laurent polynomials from `ℕ[P]` to `ℤ[P]`.
* `TauCeti.PosZero.mem_range_toFractionRing_iff` and `TauCeti.Pos.exists_toFractionRing_eq_iff`:
  when `UniqueProds P` holds, the images of `PosZero P K` and `Pos P K` are the ratios of
  (nonzero) polynomials over `ℕ[P]`.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Compos. Math. 143 (2007), §2.
-/

public section

noncomputable section

open scoped nonZeroDivisors

namespace TauCeti

open CoefficientSemifield

namespace PosZero

variable {P K : Type*} [CommMonoid P]

/-! ### Comparison with the Laurent total quotient -/

section Laurent

/-- The canonical `MonoidAlgebra ℕ P`-algebra isomorphism identifying `PosZero P K` with the total
quotient of the Laurent semiring `LaurentRing (MonoidAlgebra ℕ P) K`. -/
def laurentEquiv :
    PosZero P K ≃ₐ[MonoidAlgebra ℕ P] TotalQuotient (LaurentRing (MonoidAlgebra ℕ P) K) :=
  (LaurentRing.totalQuotientEquiv (R := MonoidAlgebra ℕ P) (K := K)).symm.restrictScalars
    (MonoidAlgebra ℕ P)

@[simp]
theorem laurentEquiv_algebraMap (p : MvPolynomial K (MonoidAlgebra ℕ P)) :
    laurentEquiv (algebraMap (MvPolynomial K (MonoidAlgebra ℕ P)) (PosZero P K) p) =
      @algebraMap (LaurentRing (MonoidAlgebra ℕ P) K)
        (TotalQuotient (LaurentRing (MonoidAlgebra ℕ P) K)) inferInstance _ _
        (MvPolynomial.toLaurent p) :=
  LaurentRing.totalQuotientEquiv_symm_algebraMap p

@[simp]
theorem laurentEquiv_coeff (p : P) :
    laurentEquiv (coeff p : PosZero P K) =
      @algebraMap (LaurentRing (MonoidAlgebra ℕ P) K)
        (TotalQuotient (LaurentRing (MonoidAlgebra ℕ P) K)) inferInstance _ _
        (algebraMap (MonoidAlgebra ℕ P) (LaurentRing (MonoidAlgebra ℕ P) K)
          (MonoidAlgebra.single p 1)) := by
  rw [← algebraMap_C_single]
  exact LaurentRing.totalQuotientEquiv_symm_algebraMap_C (K := K) (MonoidAlgebra.single p (1 : ℕ))

@[simp]
theorem laurentEquiv_X (i : K) :
    laurentEquiv (X i : PosZero P K) =
      @algebraMap (LaurentRing (MonoidAlgebra ℕ P) K)
        (TotalQuotient (LaurentRing (MonoidAlgebra ℕ P) K)) inferInstance _ _
        (LaurentRing.X i) := by
  rw [← algebraMap_X]
  exact LaurentRing.totalQuotientEquiv_symm_algebraMap_X (R := MonoidAlgebra ℕ P) i

@[simp]
theorem laurentEquiv_symm_algebraMap_toLaurent (p : MvPolynomial K (MonoidAlgebra ℕ P)) :
    laurentEquiv.symm
        (@algebraMap (LaurentRing (MonoidAlgebra ℕ P) K)
          (TotalQuotient (LaurentRing (MonoidAlgebra ℕ P) K)) inferInstance _ _
          (MvPolynomial.toLaurent p)) =
      algebraMap (MvPolynomial K (MonoidAlgebra ℕ P)) (PosZero P K) p :=
  LaurentRing.totalQuotientEquiv_algebraMap_toLaurent p

@[simp]
theorem laurentEquiv_symm_algebraMap_X (i : K) :
    laurentEquiv.symm
        (@algebraMap (LaurentRing (MonoidAlgebra ℕ P) K)
          (TotalQuotient (LaurentRing (MonoidAlgebra ℕ P) K)) inferInstance _ _
          (LaurentRing.X i)) =
      X i := by
  rw [← algebraMap_X]
  exact LaurentRing.totalQuotientEquiv_algebraMap_X (R := MonoidAlgebra ℕ P) i

theorem laurentEquiv_symm_algebraMap_coeff (p : P) :
    laurentEquiv.symm
        (@algebraMap (LaurentRing (MonoidAlgebra ℕ P) K)
          (TotalQuotient (LaurentRing (MonoidAlgebra ℕ P) K)) inferInstance _ _
          (algebraMap (MonoidAlgebra ℕ P) (LaurentRing (MonoidAlgebra ℕ P) K)
            (MonoidAlgebra.single p 1))) =
      coeff p := by
  rw [← algebraMap_C_single]
  exact LaurentRing.totalQuotientEquiv_algebraMap_algebraMap (K := K)
    (MonoidAlgebra.single p (1 : ℕ))

end Laurent

/-! ### Specializations -/

section Specializations

/-- For a one-element coefficient monoid `P`, `PosZero P K` is canonically isomorphic to the
universal semifield `QsfZero K`. -/
def equivQsfZero [Subsingleton P] : PosZero P K ≃+* QsfZero K :=
  TotalQuotient.ringEquivOfRingEquiv
    (MvPolynomial.mapEquiv K (MonoidAlgebra.uniqueRingEquiv (R := ℕ) (M := P)))

@[simp]
theorem equivQsfZero_coeff [Subsingleton P] (p : P) :
    equivQsfZero (coeff p : PosZero P K) = 1 := by
  have hp : p = 1 := Subsingleton.elim p 1
  simp [hp]

@[simp]
theorem equivQsfZero_X [Subsingleton P] (i : K) :
    equivQsfZero (X i : PosZero P K) = QsfZero.X i := by
  simp [equivQsfZero, ← algebraMap_X, ← QsfZero.algebraMap_X]

@[simp]
theorem equivQsfZero_symm_X [Subsingleton P] (i : K) :
    (equivQsfZero (P := P)).symm (QsfZero.X i) = X i := by
  rw [RingEquiv.symm_apply_eq, equivQsfZero_X]

/-- Under `equivQsfZero`, evaluation on `QsfZero K` agrees with evaluation on `PosZero P K`. -/
theorem eval_equivQsfZero [Subsingleton P] {S : Type*} [Semifield S] [Subsingleton (AddUnits S)]
    (φ : P →* Sˣ) (a : K → Sˣ) (x : PosZero P K) :
    QsfZero.eval a (equivQsfZero x) = eval φ a x := by
  rw [← RingEquiv.coe_toRingHom, ← RingHom.comp_apply]
  refine DFunLike.congr_fun (hom_ext (g := eval φ a) (fun p ↦ ?_) fun i ↦ by simp) x
  have hp : p = 1 := Subsingleton.elim p 1
  simp [hp]

/-- For an empty index type `K`, `PosZero P K` is canonically isomorphic, as a
`MonoidAlgebra ℕ P`-algebra, to `TotalQuotient (MonoidAlgebra ℕ P)`. -/
def isEmptyAlgEquiv [IsEmpty K] :
    PosZero P K ≃ₐ[MonoidAlgebra ℕ P] TotalQuotient (MonoidAlgebra ℕ P) :=
  TotalQuotient.algEquivOfAlgEquiv (MvPolynomial.isEmptyAlgEquiv (MonoidAlgebra ℕ P) K)

@[simp]
theorem isEmptyAlgEquiv_coeff [IsEmpty K] (p : P) :
    isEmptyAlgEquiv (coeff p : PosZero P K) =
      algebraMap (MonoidAlgebra ℕ P) (TotalQuotient (MonoidAlgebra ℕ P))
        (MonoidAlgebra.single p 1) := by
  simp [isEmptyAlgEquiv, ← algebraMap_C_single]

theorem isEmptyAlgEquiv_symm_algebraMap [IsEmpty K] (r : MonoidAlgebra ℕ P) :
    (isEmptyAlgEquiv (P := P) (K := K)).symm (algebraMap (MonoidAlgebra ℕ P) _ r) =
      algebraMap (MvPolynomial K (MonoidAlgebra ℕ P)) (PosZero P K) (MvPolynomial.C r) := by
  rw [AlgEquiv.symm_apply_eq]
  simp [isEmptyAlgEquiv]

/-- For a one-element coefficient monoid and an empty index type, `PosZero P K` is canonically
isomorphic to the nonnegative rationals `ℚ≥0`. -/
def equivNNRat [Subsingleton P] [IsEmpty K] : PosZero P K ≃+* ℚ≥0 :=
  ((isEmptyAlgEquiv (P := P) (K := K)).toRingEquiv.trans
    (TotalQuotient.ringEquivOfRingEquiv (MonoidAlgebra.uniqueRingEquiv (R := ℕ) (M := P)))).trans
      (TotalQuotient.algEquivOfIsFractionRing ℚ≥0).toRingEquiv

end Specializations

/-! ### Embedding in `FractionRing (LaurentRing (MonoidAlgebra ℤ P) K)` -/

section FractionRing

/-- Every polynomial over `ℤ[P]` is the difference of the images of two polynomials over `ℕ[P]`. -/
private theorem exists_sub_map_natCast (q : MvPolynomial K (MonoidAlgebra ℤ P)) :
    ∃ a b : MvPolynomial K (MonoidAlgebra ℕ P),
      q = MvPolynomial.map (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ)) a -
        MvPolynomial.map (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ)) b := by
  classical
  induction q using MvPolynomial.induction_on with
  | C r =>
    let a : MonoidAlgebra ℕ P := ∑ p ∈ r.coeff.support, MonoidAlgebra.single p (r.coeff p).toNat
    let b : MonoidAlgebra ℕ P := ∑ p ∈ r.coeff.support, MonoidAlgebra.single p (-r.coeff p).toNat
    refine ⟨MvPolynomial.C a, MvPolynomial.C b, ?_⟩
    rw [MvPolynomial.map_C, MvPolynomial.map_C, ← map_sub]
    congr 1
    ext p
    simp [a, b, Finsupp.single_apply]
    split_ifs <;> omega
  | add q₁ q₂ h₁ h₂ =>
    obtain ⟨a₁, b₁, rfl⟩ := h₁
    obtain ⟨a₂, b₂, rfl⟩ := h₂
    refine ⟨a₁ + a₂, b₁ + b₂, ?_⟩
    simp only [map_add]
    abel
  | mul_X q i hq =>
    obtain ⟨a, b, rfl⟩ := hq
    refine ⟨a * MvPolynomial.X i, b * MvPolynomial.X i, ?_⟩
    simp only [map_mul, MvPolynomial.map_X, sub_mul]

/-- Every regular polynomial over `ℕ[P]` maps to a non-zero-divisor of `LaurentRing ℤ[P] K`. -/
private theorem toLaurent_map_natCast_mem_nonZeroDivisors
    {p : MvPolynomial K (MonoidAlgebra ℕ P)} (hp : IsRegular p) :
    MvPolynomial.toLaurent
        (MvPolynomial.map (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ)) p) ∈
      (LaurentRing (MonoidAlgebra ℤ P) K)⁰ := by
  refine mem_nonZeroDivisors_iff_right.mpr fun f hf ↦ ?_
  obtain ⟨n, q, hfq, -⟩ := LaurentRing.exists_mul_toLaurent_monomial f
  have hmul : MvPolynomial.toLaurent
      (MvPolynomial.map (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ)) p * q) = 0 := by
    rw [map_mul, ← hfq, ← mul_assoc, mul_comm _ f, hf, zero_mul]
  have hpq : MvPolynomial.map (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ)) p * q = 0 :=
    MvPolynomial.toLaurent_injective (by simpa using hmul)
  obtain ⟨a, b, rfl⟩ := exists_sub_map_natCast q
  have hpa : MvPolynomial.map (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ)) (p * a) =
      MvPolynomial.map (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ)) (p * b) := by
    rw [map_mul, map_mul, ← sub_eq_zero, ← mul_sub]
    exact hpq
  have hinj : Function.Injective
      (MvPolynomial.map (σ := K) (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ))) :=
    MvPolynomial.map_injective _
      (MonoidAlgebra.map_injective (Nat.castRingHom ℤ).toAddMonoidHom Nat.cast_injective)
  have hab : a = b := hp.left (hinj hpa)
  have hunit : IsUnit (MvPolynomial.toLaurent (R := MonoidAlgebra ℤ P)
      (MvPolynomial.monomial n 1)) := by
    rw [MvPolynomial.toLaurent_monomial]
    refine ⟨⟨AddMonoidAlgebra.single (n.mapRange Nat.cast Nat.cast_zero) 1,
      AddMonoidAlgebra.single (-(n.mapRange Nat.cast Nat.cast_zero)) 1, ?_, ?_⟩, rfl⟩
    · simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]
    · simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]
  have hf0 : f * MvPolynomial.toLaurent (MvPolynomial.monomial n 1) = 0 := by
    rw [hfq, hab, sub_self, map_zero]
  exact hunit.mul_left_eq_zero.mp hf0

variable (P K) in
/-- The embedding of `PosZero P K` into `FractionRing (LaurentRing (MonoidAlgebra ℤ P) K)`,
induced by the natural-to-integer coefficient inclusion and polynomial-to-Laurent inclusion. -/
def toFractionRing : PosZero P K →+* FractionRing (LaurentRing (MonoidAlgebra ℤ P) K) :=
  IsLocalization.lift (M := regulars (MvPolynomial K (MonoidAlgebra ℕ P)))
    (g := ((algebraMap (LaurentRing (MonoidAlgebra ℤ P) K)
        (FractionRing (LaurentRing (MonoidAlgebra ℤ P) K))).comp
      (MvPolynomial.toLaurent : MvPolynomial K (MonoidAlgebra ℤ P) →ₐ[_] _).toRingHom).comp
      (MvPolynomial.map (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ)))) fun p ↦
    IsLocalization.map_units (FractionRing (LaurentRing (MonoidAlgebra ℤ P) K))
      ⟨_, toLaurent_map_natCast_mem_nonZeroDivisors (mem_regulars.mp p.2)⟩

@[simp]
theorem toFractionRing_algebraMap (p : MvPolynomial K (MonoidAlgebra ℕ P)) :
    toFractionRing P K (algebraMap (MvPolynomial K (MonoidAlgebra ℕ P)) (PosZero P K) p) =
      algebraMap (LaurentRing (MonoidAlgebra ℤ P) K)
        (FractionRing (LaurentRing (MonoidAlgebra ℤ P) K))
        (MvPolynomial.toLaurent
          (MvPolynomial.map (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ)) p)) :=
  IsLocalization.lift_eq _ p

@[simp]
theorem toFractionRing_coeff (p : P) :
    toFractionRing P K (coeff p) =
      algebraMap (LaurentRing (MonoidAlgebra ℤ P) K)
        (FractionRing (LaurentRing (MonoidAlgebra ℤ P) K))
        (algebraMap (MonoidAlgebra ℤ P) (LaurentRing (MonoidAlgebra ℤ P) K)
          (MonoidAlgebra.single p 1)) := by
  simp [← algebraMap_C_single]

@[simp]
theorem toFractionRing_X (i : K) :
    toFractionRing P K (X i) =
      algebraMap (LaurentRing (MonoidAlgebra ℤ P) K)
        (FractionRing (LaurentRing (MonoidAlgebra ℤ P) K)) (LaurentRing.X i) := by
  simp [← algebraMap_X]

/-- `PosZero P K` embeds injectively into `FractionRing (LaurentRing (MonoidAlgebra ℤ P) K)`. -/
theorem toFractionRing_injective : Function.Injective (toFractionRing P K) :=
  IsLocalization.lift_injective_of_injective _ <| by
    rw [RingHom.coe_comp, RingHom.coe_comp]
    exact ((IsFractionRing.injective _ _).comp MvPolynomial.toLaurent_injective).comp
      (MvPolynomial.map_injective _
        (MonoidAlgebra.map_injective (Nat.castRingHom ℤ).toAddMonoidHom Nat.cast_injective))

@[simp]
theorem toFractionRing_inj {x y : PosZero P K} :
    toFractionRing P K x = toFractionRing P K y ↔ x = y :=
  toFractionRing_injective.eq_iff

/-- Along `laurentEquiv.symm`, the embedding into `FractionRing (LaurentRing ℤ[P] K)` agrees with
casting the coefficients of a Laurent polynomial from `ℕ[P]` to `ℤ[P]`. -/
theorem toFractionRing_laurentEquiv_symm_algebraMap (f : LaurentRing (MonoidAlgebra ℕ P) K) :
    toFractionRing P K
        (laurentEquiv.symm
          (@algebraMap (LaurentRing (MonoidAlgebra ℕ P) K)
            (TotalQuotient (LaurentRing (MonoidAlgebra ℕ P) K)) inferInstance _ _ f)) =
      algebraMap (LaurentRing (MonoidAlgebra ℤ P) K)
        (FractionRing (LaurentRing (MonoidAlgebra ℤ P) K))
        (AddMonoidAlgebra.mapRingHom (K →₀ ℤ)
          (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ)) f) := by
  obtain ⟨n, p, hfp, -⟩ := LaurentRing.exists_mul_toLaurent_monomial f
  let ι := algebraMap (LaurentRing (MonoidAlgebra ℤ P) K)
    (FractionRing (LaurentRing (MonoidAlgebra ℤ P) K))
  let j := @algebraMap (LaurentRing (MonoidAlgebra ℕ P) K)
    (TotalQuotient (LaurentRing (MonoidAlgebra ℕ P) K)) inferInstance _ _
  let c := MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ)
  have hunit :
      IsUnit (ι (MvPolynomial.toLaurent (MvPolynomial.map c (MvPolynomial.monomial n 1)))) :=
    IsLocalization.map_units (FractionRing (LaurentRing (MonoidAlgebra ℤ P) K))
      ⟨_, toLaurent_map_natCast_mem_nonZeroDivisors
        (isRegular_one (R := MonoidAlgebra ℕ P)).monomial⟩
  apply hunit.mul_left_inj.mp
  calc
    toFractionRing P K (laurentEquiv.symm (j f)) *
        ι (MvPolynomial.toLaurent (MvPolynomial.map c (MvPolynomial.monomial n 1)))
      = toFractionRing P K
          (laurentEquiv.symm (j (f * MvPolynomial.toLaurent (.monomial n 1)))) := by
          rw [← toFractionRing_algebraMap, ← laurentEquiv_symm_algebraMap_toLaurent, ← map_mul,
            ← map_mul, ← map_mul]
    _ = ι (MvPolynomial.toLaurent (MvPolynomial.map c p)) := by
          rw [hfp, laurentEquiv_symm_algebraMap_toLaurent, toFractionRing_algebraMap]
    _ = ι (AddMonoidAlgebra.mapRingHom (K →₀ ℤ) c f) *
        ι (MvPolynomial.toLaurent (MvPolynomial.map c (MvPolynomial.monomial n 1))) := by
          rw [← map_mul, MvPolynomial.toLaurent_map, MvPolynomial.toLaurent_map, ← map_mul, hfp]

/-- When `UniqueProds P` holds, `toFractionRing` sends a fraction to the ratio of its numerator
and denominator. -/
theorem toFractionRing_mk' [UniqueProds P] (p : MvPolynomial K (MonoidAlgebra ℕ P))
    (q : regulars (MvPolynomial K (MonoidAlgebra ℕ P))) :
    toFractionRing P K (IsLocalization.mk' (PosZero P K) p q) =
      algebraMap (LaurentRing (MonoidAlgebra ℤ P) K)
          (FractionRing (LaurentRing (MonoidAlgebra ℤ P) K))
          (MvPolynomial.toLaurent
            (MvPolynomial.map (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ)) p)) /
        algebraMap (LaurentRing (MonoidAlgebra ℤ P) K)
          (FractionRing (LaurentRing (MonoidAlgebra ℤ P) K))
          (MvPolynomial.toLaurent
            (MvPolynomial.map (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ))
              (q : MvPolynomial K (MonoidAlgebra ℕ P)))) := by
  rw [TotalQuotient.mk'_eq_div, map_div₀, toFractionRing_algebraMap, toFractionRing_algebraMap]

/-- When `UniqueProds P` holds, the image of `PosZero P K` in
`FractionRing (LaurentRing (MonoidAlgebra ℤ P) K)` consists of all ratios of polynomials over
`ℕ[P]` with nonzero denominator. -/
theorem mem_range_toFractionRing_iff [UniqueProds P]
    {z : FractionRing (LaurentRing (MonoidAlgebra ℤ P) K)} :
    z ∈ Set.range (toFractionRing P K) ↔
      ∃ p q : MvPolynomial K (MonoidAlgebra ℕ P), q ≠ 0 ∧
        z = algebraMap (LaurentRing (MonoidAlgebra ℤ P) K)
              (FractionRing (LaurentRing (MonoidAlgebra ℤ P) K))
              (MvPolynomial.toLaurent
                (MvPolynomial.map (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ)) p)) /
            algebraMap (LaurentRing (MonoidAlgebra ℤ P) K)
              (FractionRing (LaurentRing (MonoidAlgebra ℤ P) K))
              (MvPolynomial.toLaurent
                (MvPolynomial.map (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ)) q)) := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨⟨p, q⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (regulars (MvPolynomial K (MonoidAlgebra ℕ P))) x
    exact ⟨p, q, mem_regulars_iff_ne_zero.mp q.2, toFractionRing_mk' p q⟩
  · rintro ⟨p, q, hq, rfl⟩
    exact ⟨IsLocalization.mk' _ p ⟨q, mem_regulars_iff_ne_zero.mpr hq⟩, toFractionRing_mk' _ _⟩

end FractionRing

end PosZero

namespace Pos

variable {P K Q : Type*} [CommMonoid P] [UniqueProds P] [CoefficientSemifield Q]

/-! ### Specializations and rational-function comparison -/

/-- For a one-element coefficient monoid `P`, `Pos P K` is canonically isomorphic to the universal
coefficient semifield `Qsf K`. -/
def equivQsf [Subsingleton P] : Pos P K ≃+* Qsf K :=
  PosZero.equivQsfZero.mapUnits

@[simp]
theorem equivQsf_coeff [Subsingleton P] (p : P) : equivQsf (coeff p : Pos P K) = 1 :=
  Units.ext <| by simp [equivQsf]

@[simp]
theorem equivQsf_X [Subsingleton P] (i : K) : equivQsf (X i : Pos P K) = Qsf.X i :=
  Units.ext <| by simp [equivQsf]

@[simp]
theorem equivQsf_symm_X [Subsingleton P] (i : K) : (equivQsf (P := P)).symm (Qsf.X i) = X i := by
  rw [RingEquiv.symm_apply_eq, equivQsf_X]

/-- Under `equivQsf`, evaluation on `Qsf K` agrees with evaluation on `Pos P K`. -/
theorem eval_equivQsf [Subsingleton P] (φ : P →* Q) (a : K → Q) (x : Pos P K) :
    Qsf.eval a (equivQsf x) = eval φ a x :=
  WithZero.coe_injective <| by
    have h : (fun i ↦ unitsWithZeroRingEquiv.symm (a i)) =
        fun i ↦ WithZero.unitsWithZeroEquiv.symm (a i) :=
      funext fun i ↦ Units.ext (by simp)
    simpa [Qsf.coe_eval_apply, coe_eval_apply, equivQsf, h] using
      PosZero.eval_equivQsfZero (WithZero.unitsWithZeroEquiv.symm.toMonoidHom.comp φ)
        (fun i ↦ WithZero.unitsWithZeroEquiv.symm (a i)) (x : PosZero P K)

/-- For an empty index type `K`, `Pos P K` is canonically isomorphic to the coefficient semifield
of units of `TotalQuotient (MonoidAlgebra ℕ P)`. -/
def isEmptyRingEquiv [IsEmpty K] : Pos P K ≃+* (TotalQuotient (MonoidAlgebra ℕ P))ˣ :=
  (PosZero.isEmptyAlgEquiv (P := P) (K := K)).toRingEquiv.mapUnits

/-- For a one-element coefficient monoid and an empty index type, `Pos P K` is canonically
isomorphic to the positive rationals `ℚ≥0ˣ`. -/
def equivNNRatUnits [Subsingleton P] [IsEmpty K] : Pos P K ≃+* ℚ≥0ˣ :=
  (PosZero.equivNNRat (P := P) (K := K)).mapUnits

/-- The elements of `FractionRing (LaurentRing (MonoidAlgebra ℤ P) K)` coming from `Pos P K` are
exactly the ratios of nonzero polynomials over `ℕ[P]`. -/
theorem exists_toFractionRing_eq_iff {z : FractionRing (LaurentRing (MonoidAlgebra ℤ P) K)} :
    (∃ x : Pos P K, PosZero.toFractionRing P K x = z) ↔
      ∃ p q : MvPolynomial K (MonoidAlgebra ℕ P), p ≠ 0 ∧ q ≠ 0 ∧
        z = algebraMap (LaurentRing (MonoidAlgebra ℤ P) K)
              (FractionRing (LaurentRing (MonoidAlgebra ℤ P) K))
              (MvPolynomial.toLaurent
                (MvPolynomial.map (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ)) p)) /
            algebraMap (LaurentRing (MonoidAlgebra ℤ P) K)
              (FractionRing (LaurentRing (MonoidAlgebra ℤ P) K))
              (MvPolynomial.toLaurent
                (MvPolynomial.map (MonoidAlgebra.mapRingHom P (Nat.castRingHom ℤ)) q)) := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨⟨p, q⟩, h⟩ := IsLocalization.mk'_surjective
      (regulars (MvPolynomial K (MonoidAlgebra ℕ P))) (x : PosZero P K)
    refine ⟨p, q, IsLocalization.ne_zero_of_mk'_ne_zero (h ▸ x.ne_zero),
      mem_regulars_iff_ne_zero.mp q.2, ?_⟩
    rw [← h, PosZero.toFractionRing_mk']
  · rintro ⟨p, q, hp, hq, rfl⟩
    have hq' : q ∈ regulars (MvPolynomial K (MonoidAlgebra ℕ P)) := mem_regulars_iff_ne_zero.mpr hq
    refine ⟨Units.mk0 (IsLocalization.mk' _ p ⟨q, hq'⟩) ?_, PosZero.toFractionRing_mk' _ _⟩
    rw [ne_eq, IsLocalization.mk'_eq_zero_iff]
    rintro ⟨m, hm⟩
    exact hp ((mem_regulars.mp m.2).left (by simpa using hm))

end Pos

/-! ### Interface checks -/

section Checks

/-- For every `CoefficientSemifield P`, `PosZero P K` is automatically a semifield. -/
example (P K : Type*) [CoefficientSemifield P] : Semifield (PosZero P K) := inferInstance

/-- For every `CoefficientSemifield P`, `PosZero P K` is automatically zero-sum-free. -/
example (P K : Type*) [CoefficientSemifield P] : Subsingleton (AddUnits (PosZero P K)) :=
  inferInstance

/-- For every `CoefficientSemifield P`, `Pos P K` is automatically a `CoefficientSemifield`. -/
example (P K : Type*) [CoefficientSemifield P] : CoefficientSemifield (Pos P K) := inferInstance

/-- Evaluation in any coefficient semifield simplifies ratios such as
`(p * X 0 + p * X 1) / (X 0 + X 1)` to `φ p`. -/
example {P Q : Type*} [CoefficientSemifield P] [CoefficientSemifield Q]
    (φ : P →* Q) (a : Fin 2 → Q) (p : P) :
    Pos.eval φ a ((Pos.coeff p * Pos.X 0 + Pos.coeff p * Pos.X 1) / (Pos.X 0 + Pos.X 1)) = φ p := by
  simp [← mul_add]

/-- Addition in `PosZero P K` is formal rather than the auxiliary addition of `P`: even for
`PUnit` (where `1 + 1 = 1`), `coeff (1 + 1) = 1` whereas `coeff 1 + coeff 1 ≠ 1`. -/
example :
    PosZero.coeff (K := Empty) ((1 : PUnit) + 1) ≠
      PosZero.coeff (K := Empty) (1 : PUnit) + PosZero.coeff (K := Empty) (1 : PUnit) := by
  intro h
  have hq := congrArg (PosZero.equivNNRat (P := PUnit) (K := Empty)) h
  rw [Subsingleton.elim ((1 : PUnit) + 1) 1] at hq
  simp only [map_add, map_one] at hq
  norm_num at hq

end Checks

end TauCeti
