/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import TauCeti.RingTheory.PowerSeries.PrincipalUnit

/-!
# Pre-`λ`-rings, total `λ`-series, virtual negatives, and line elements

A **pre-`λ`-ring** (`TauCeti.PreLambdaRing`) is a commutative ring `R` equipped with operations
`λ^n : R → R` for `n : ℕ` satisfying `λ^0(x) = 1`, `λ^1(x) = x`, and the convolution addition law
`λ^n(x + y) = ∑_{i + j = n} λ^i(x) λ^j(y)`. Assembling the coefficients into a formal power series
`λ_t(x) = ∑_{n ≥ 0} λ^n(x) t^n` identifies pre-`λ`-ring structures on `R` bijectively with group
homomorphisms `Multiplicative R →* PowerSeries.principalUnitSubgroup R` into `1 + X R⟦X⟧` whose
linear coefficient is the identity (`TauCeti.PreLambdaRing.equivTotalLambda`).

From the group homomorphism `λ_t` follow immediately:
* the **zero formula**: `λ^0(0) = 1` and `λ^n(0) = 0` for `n ≥ 1`, because `λ_t(0)` is an
  idempotent in the group `1 + X R⟦X⟧`;
* the **virtual-negative formula**: `λ_t(-x) = λ_t(x)⁻¹` in `1 + X R⟦X⟧`, together with the
  convolution recurrence `λ^{n+1}(-x) = -∑_{i=0}^n λ^{n+1-i}(x) λ^i(-x)` and low-degree formulas
  `λ^2(-x) = x^2 - λ^2(x)` and `λ^3(-x) = -x^3 + 2 x λ^2(x) - λ^3(x)`;
* **additive generation uniqueness** (`TauCeti.PreLambdaRing.ext_addSubgroupClosure`): two
  pre-`λ`-structures on `R` agreeing on a subset `s` agree on `AddSubgroup.closure s`;
* **line elements** (`TauCeti.PreLambdaRing.IsLineElement`): elements `l : R` with
  `λ_t(l) = 1 + l X` (equivalently `λ^n(l) = 0` for all `n ≥ 2`), which need not be units, and
  whose integer multiples satisfy `λ^n(z • l) = Ring.choose z n • l^n`.

## Main definitions

* `TauCeti.PreLambdaRing`: pre-`λ`-ring structure on a commutative ring.
* `TauCeti.PreLambdaRing.totalSeries` and `TauCeti.PreLambdaRing.totalLambda`: the total series
  `λ_t(x) ∈ R⟦X⟧` and the group homomorphism
  `Multiplicative R →* PowerSeries.principalUnitSubgroup R`.
* `TauCeti.PreLambdaRing.ofTotalLambda` and `TauCeti.PreLambdaRing.equivTotalLambda`: equivalence
  between the coefficient axioms and the total-series homomorphism law.
* `TauCeti.PreLambdaRing.IsLineElement`: predicate `λ_t(l) = 1 + C l * X`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, §II.4.1–4.1.1 (p. 90) and
  Exercises II.4.1, II.4.4 (pp. 101–102).
-/

public section

noncomputable section

open Finset PowerSeries

namespace TauCeti

/-- A pre-`λ`-ring structure on a commutative ring `R` (Weibel, *The K-book*, Definition II.4.1):
operations `lambdaOp n : R → R` (`λ^n`) with `λ^0(x) = 1`, `λ^1(x) = x`, and
`λ^n(x + y) = ∑_{i + j = n} λ^i(x) λ^j(y)`. -/
@[ext]
class PreLambdaRing (R : Type*) [CommRing R] where
  /-- The `n`-th `λ`-operation `λ^n : R → R`. -/
  lambdaOp : ℕ → R → R
  /-- Degree-zero normalization `λ^0(x) = 1`. -/
  lambdaOp_zero (x : R) : lambdaOp 0 x = 1
  /-- Degree-one normalization `λ^1(x) = x`. -/
  lambdaOp_one (x : R) : lambdaOp 1 x = x
  /-- Addition convolution law `λ^n(x + y) = ∑_{i + j = n} λ^i(x) * λ^j(y)`. -/
  lambdaOp_add (n : ℕ) (x y : R) :
    lambdaOp n (x + y) = ∑ ij ∈ antidiagonal n, lambdaOp ij.1 x * lambdaOp ij.2 y

export PreLambdaRing (lambdaOp lambdaOp_zero lambdaOp_one lambdaOp_add)

attribute [simp] lambdaOp_zero lambdaOp_one

namespace PreLambdaRing

section Basic

variable {R : Type*} [CommRing R]

/-- Two `PreLambdaRing` structures on `R` are equal as soon as their operations `λ^n` agree for all
`n ≥ 2`, since `n = 0` and `n = 1` are fixed by the axioms. -/
theorem ext_of_two_le {l₁ l₂ : PreLambdaRing R}
    (h : ∀ ⦃n : ℕ⦄, 2 ≤ n → ∀ x : R, @lambdaOp R _ l₁ n x = @lambdaOp R _ l₂ n x) :
    l₁ = l₂ := by
  ext n x
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 => exact h (Nat.le_add_left 2 n) x

variable [PreLambdaRing R]

/-- Explicit expansion `λ^2(x + y) = λ^2(x) + x * y + λ^2(y)`. -/
theorem lambdaOp_two_add (x y : R) :
    lambdaOp 2 (x + y) = lambdaOp 2 x + x * y + lambdaOp 2 y := by
  rw [lambdaOp_add 2 x y, Nat.sum_antidiagonal_succ, Nat.sum_antidiagonal_succ,
    Nat.antidiagonal_zero]
  simp
  ring

/-- The total `λ`-series `λ_t(x) = ∑_{n ≥ 0} λ^n(x) X^n` of an element `x` in a pre-`λ`-ring. -/
def totalSeries (x : R) : R⟦X⟧ :=
  PowerSeries.mk fun n ↦ lambdaOp n x

theorem totalSeries_def (x : R) :
    totalSeries x = PowerSeries.mk fun n ↦ lambdaOp n x :=
  (rfl)

@[simp]
theorem coeff_totalSeries (n : ℕ) (x : R) :
    coeff n (totalSeries x) = lambdaOp n x :=
  coeff_mk n _

@[simp]
theorem constantCoeff_totalSeries (x : R) :
    constantCoeff (totalSeries x) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_totalSeries, lambdaOp_zero]

theorem isUnit_totalSeries (x : R) : IsUnit (totalSeries x) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_totalSeries]
  exact isUnit_one

/-- Addition in `R` becomes multiplication of total `λ`-series. -/
@[simp]
theorem totalSeries_add (x y : R) :
    totalSeries (x + y) = totalSeries x * totalSeries y := by
  ext n
  simp [coeff_mul, lambdaOp_add]

/-- The total `λ`-series of `0` is `1`. -/
@[simp]
theorem totalSeries_zero : totalSeries (0 : R) = 1 := by
  have hidem : totalSeries (0 : R) * totalSeries 0 = totalSeries 0 := by
    rw [← totalSeries_add, zero_add]
  have hinv := invOfUnit_mul (totalSeries (0 : R)) 1 (by simp)
  calc
    totalSeries (0 : R) = 1 * totalSeries 0 := (one_mul _).symm
    _ = invOfUnit (totalSeries 0) 1 * totalSeries 0 * totalSeries 0 := by rw [hinv]
    _ = invOfUnit (totalSeries 0) 1 * (totalSeries 0 * totalSeries 0) := mul_assoc _ _ _
    _ = invOfUnit (totalSeries 0) 1 * totalSeries 0 := by rw [hidem]
    _ = 1 := hinv

/-- For `n ≥ 1`, `λ^n(0) = 0` (the zero formula). -/
@[simp]
theorem lambdaOp_succ_zero (n : ℕ) : lambdaOp (n + 1) (0 : R) = 0 := by
  rw [← coeff_totalSeries, totalSeries_zero, coeff_one, ite_eq_right (Nat.succ_ne_zero n)]

theorem lambdaOp_zero_right_of_ne_zero {n : ℕ} (hn : n ≠ 0) : lambdaOp n (0 : R) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact lambdaOp_succ_zero k

theorem lambdaOp_zero_right (n : ℕ) : lambdaOp n (0 : R) = if n = 0 then 1 else 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [hn, lambdaOp_zero_right_of_ne_zero hn]

/-- Total `λ`-series of a finite sum `∑ i ∈ s, f i`. -/
theorem totalSeries_sum {ι : Type*} (s : Finset ι) (f : ι → R) :
    totalSeries (∑ i ∈ s, f i) = ∏ i ∈ s, totalSeries (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, totalSeries_add, prod_insert ha, ih]

variable (R) in
/-- The total `λ`-operation as an additive-to-multiplicative homomorphism
`Multiplicative R →* PowerSeries.principalUnitSubgroup R` into `1 + X R⟦X⟧`. -/
def totalLambda : Multiplicative R →* principalUnitSubgroup R where
  toFun x := principalUnitMk (totalSeries (Multiplicative.toAdd x)) (constantCoeff_totalSeries _)
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [toAdd_mul]

@[simp]
theorem principalUnitSeries_totalLambda (x : R) :
    principalUnitSeries (totalLambda R (Multiplicative.ofAdd x)) = totalSeries x := by
  simp [totalLambda]

theorem coeff_one_totalLambda (x : R) :
    coeff 1 (principalUnitSeries (totalLambda R (Multiplicative.ofAdd x))) = x := by
  simp

end Basic

/-! ### Equivalence of total and coefficient laws -/

section Equivalence

variable {R : Type*} [CommRing R]

/-- Construct a `PreLambdaRing` structure on `R` from an additive-to-multiplicative homomorphism
`L : Multiplicative R →* principalUnitSubgroup R` whose linear coefficient is the identity. -/
@[instance_reducible]
def ofTotalLambda (L : Multiplicative R →* principalUnitSubgroup R)
    (h₁ : ∀ x : R, coeff 1 (principalUnitSeries (L (Multiplicative.ofAdd x))) = x) :
    PreLambdaRing R where
  lambdaOp n x := coeff n (principalUnitSeries (L (Multiplicative.ofAdd x)))
  lambdaOp_zero x := coeff_zero_principalUnitSeries _
  lambdaOp_one := h₁
  lambdaOp_add n x y := by
    rw [ofAdd_add, map_mul, principalUnitSeries_mul, coeff_mul]

theorem lambdaOp_ofTotalLambda (L : Multiplicative R →* principalUnitSubgroup R)
    (h₁ : ∀ x : R, coeff 1 (principalUnitSeries (L (Multiplicative.ofAdd x))) = x)
    (n : ℕ) (x : R) :
    @lambdaOp R _ (ofTotalLambda L h₁) n x =
      coeff n (principalUnitSeries (L (Multiplicative.ofAdd x))) :=
  (rfl)

theorem totalSeries_ofTotalLambda (L : Multiplicative R →* principalUnitSubgroup R)
    (h₁ : ∀ x : R, coeff 1 (principalUnitSeries (L (Multiplicative.ofAdd x))) = x) (x : R) :
    @totalSeries R _ (ofTotalLambda L h₁) x =
      principalUnitSeries (L (Multiplicative.ofAdd x)) := by
  ext n
  rw [@coeff_totalSeries R _ (ofTotalLambda L h₁), lambdaOp_ofTotalLambda]

@[simp]
theorem totalLambda_ofTotalLambda (L : Multiplicative R →* principalUnitSubgroup R)
    (h₁ : ∀ x : R, coeff 1 (principalUnitSeries (L (Multiplicative.ofAdd x))) = x) :
    @totalLambda R _ (ofTotalLambda L h₁) = L := by
  apply MonoidHom.ext
  intro x
  apply principalUnit_ext
  rw [← ofAdd_toAdd x, @principalUnitSeries_totalLambda R _ (ofTotalLambda L h₁),
    totalSeries_ofTotalLambda]

variable (R) in
/-- Equivalence between `PreLambdaRing` structures on `R` and homomorphisms
`Multiplicative R →* principalUnitSubgroup R` into `1 + X R⟦X⟧` with linear coefficient `id`. -/
def equivTotalLambda :
    PreLambdaRing R ≃
      { L : Multiplicative R →* principalUnitSubgroup R //
        ∀ x : R, coeff 1 (principalUnitSeries (L (Multiplicative.ofAdd x))) = x } where
  toFun l := ⟨@totalLambda R _ l, @coeff_one_totalLambda R _ l⟩
  invFun L := ofTotalLambda L.1 L.2
  left_inv l := by
    ext n x
    simp [lambdaOp_ofTotalLambda]
  right_inv L := Subtype.ext (totalLambda_ofTotalLambda L.1 L.2)

end Equivalence

/-! ### Virtual-negative formulas and additive generation -/

section VirtualNegative

variable {R : Type*} [CommRing R] [PreLambdaRing R]

/-- Group-level virtual-negative formula: `λ_t(-x) = λ_t(x)⁻¹` in `1 + X R⟦X⟧`. -/
theorem totalLambda_neg (x : R) :
    totalLambda R (Multiplicative.ofAdd (-x)) = (totalLambda R (Multiplicative.ofAdd x))⁻¹ :=
  map_inv (totalLambda R) (Multiplicative.ofAdd x)

/-- Group-level subtraction formula: `λ_t(x - y) = λ_t(x) * λ_t(y)⁻¹` in `1 + X R⟦X⟧`. -/
theorem totalLambda_sub (x y : R) :
    totalLambda R (Multiplicative.ofAdd (x - y)) =
      totalLambda R (Multiplicative.ofAdd x) * (totalLambda R (Multiplicative.ofAdd y))⁻¹ := by
  rw [sub_eq_add_neg, ofAdd_add, map_mul, totalLambda_neg]

@[simp]
theorem totalSeries_mul_totalSeries_neg (x : R) :
    totalSeries x * totalSeries (-x) = 1 := by
  simp [← totalSeries_add]

@[simp]
theorem totalSeries_neg_mul_totalSeries (x : R) :
    totalSeries (-x) * totalSeries x = 1 := by
  rw [mul_comm, totalSeries_mul_totalSeries_neg]

/-- Formal power-series inverse characterization of `λ_t(-x)`. -/
theorem totalSeries_neg_eq_invOfUnit (x : R) :
    totalSeries (-x) = invOfUnit (totalSeries x) 1 := by
  rw [← principalUnitSeries_totalLambda (-x), totalLambda_neg, principalUnitSeries_inv,
    principalUnitSeries_totalLambda]

/-- Positive-degree convolution relation `∑_{i + j = n} λ^i(x) * λ^j(-x) = 0` for `n ≠ 0`. -/
theorem sum_antidiagonal_lambdaOp_neg {n : ℕ} (hn : n ≠ 0) (x : R) :
    ∑ ij ∈ antidiagonal n, lambdaOp ij.1 x * lambdaOp ij.2 (-x) = 0 := by
  rw [← lambdaOp_add, add_neg_cancel, lambdaOp_zero_right_of_ne_zero hn]

/-- Recursive formula for virtual negatives:
`λ^{n+1}(-x) = -∑_{i=0}^n λ^{n+1-i}(x) * λ^i(-x)`. -/
theorem lambdaOp_succ_neg (n : ℕ) (x : R) :
    lambdaOp (n + 1) (-x) =
      -∑ i ∈ range (n + 1), lambdaOp (n + 1 - i) x * lambdaOp i (-x) := by
  have h := sum_antidiagonal_lambdaOp_neg (Nat.succ_ne_zero n) x
  rw [Nat.sum_antidiagonal_succ, lambdaOp_zero, one_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  have hswap :
      (∑ i ∈ range (n + 1), lambdaOp (i + 1) x * lambdaOp (n - i) (-x)) =
        ∑ j ∈ range (n + 1), lambdaOp (n + 1 - j) x * lambdaOp j (-x) := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun j hj ↦ ?_
    have hjlt : j < n + 1 := mem_range.mp hj
    have h1 : n + 1 - 1 - j + 1 = n + 1 - j := by omega
    have h2 : n - (n + 1 - 1 - j) = j := by omega
    rw [h1, h2]
  rw [hswap] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Explicit degree-two virtual-negative formula `λ^2(-x) = x^2 - λ^2(x)`. -/
theorem lambdaOp_two_neg (x : R) :
    lambdaOp 2 (-x) = x ^ 2 - lambdaOp 2 x := by
  rw [lambdaOp_succ_neg 1 x, sum_range_succ, sum_range_one]
  simp
  ring

/-- Explicit degree-three virtual-negative formula
`λ^3(-x) = -x^3 + 2 * x * lambdaOp 2 x - lambdaOp 3 x`. -/
theorem lambdaOp_three_neg (x : R) :
    lambdaOp 3 (-x) = -x ^ 3 + 2 * x * lambdaOp 2 x - lambdaOp 3 x := by
  rw [lambdaOp_succ_neg 2 x, sum_range_succ, sum_range_succ, sum_range_one]
  simp [lambdaOp_two_neg]
  ring

/-- Coefficient formula for differences `λ^n(x - y) = ∑_{i + j = n} λ^i(x) * λ^j(-y)`. -/
theorem lambdaOp_sub (n : ℕ) (x y : R) :
    lambdaOp n (x - y) = ∑ ij ∈ antidiagonal n, lambdaOp ij.1 x * lambdaOp ij.2 (-y) := by
  rw [sub_eq_add_neg, lambdaOp_add]

end VirtualNegative

section AddSubgroupClosure

variable {R : Type*} [CommRing R]

/-- The additive subgroup where two `PreLambdaRing` structures on `R` agree in all degrees. -/
def eqLocusAddSubgroup (l₁ l₂ : PreLambdaRing R) : AddSubgroup R where
  carrier := {x : R | ∀ n : ℕ, @lambdaOp R _ l₁ n x = @lambdaOp R _ l₂ n x}
  zero_mem' n := by
    rw [@lambdaOp_zero_right R _ l₁, @lambdaOp_zero_right R _ l₂]
  add_mem' {x y} hx hy n := by
    rw [@lambdaOp_add R _ l₁, @lambdaOp_add R _ l₂]
    exact sum_congr rfl fun ij _ ↦ by rw [hx ij.1, hy ij.2]
  neg_mem' {x} hx n := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | n
      · simp
      · rw [@lambdaOp_succ_neg R _ l₁, @lambdaOp_succ_neg R _ l₂]
        congr 1
        refine sum_congr rfl fun i hi ↦ ?_
        rw [hx (n + 1 - i), ih i (mem_range.mp hi)]

/-- Two `PreLambdaRing` structures on `R` that agree on a set `s` in all degrees agree on
`AddSubgroup.closure s`. -/
theorem eqOn_addSubgroupClosure {l₁ l₂ : PreLambdaRing R} {s : Set R}
    (hs : ∀ x ∈ s, ∀ n : ℕ, @lambdaOp R _ l₁ n x = @lambdaOp R _ l₂ n x)
    {x : R} (hx : x ∈ AddSubgroup.closure s) (n : ℕ) :
    @lambdaOp R _ l₁ n x = @lambdaOp R _ l₂ n x :=
  (AddSubgroup.closure_le (eqLocusAddSubgroup l₁ l₂)).mpr hs hx n

/-- Two `PreLambdaRing` structures on `R` that agree on a set `s` with
`AddSubgroup.closure s = ⊤` are equal. -/
theorem ext_addSubgroupClosure {l₁ l₂ : PreLambdaRing R} {s : Set R}
    (hspan : AddSubgroup.closure s = ⊤)
    (hs : ∀ x ∈ s, ∀ n : ℕ, @lambdaOp R _ l₁ n x = @lambdaOp R _ l₂ n x) :
    l₁ = l₂ := by
  ext n x
  exact eqOn_addSubgroupClosure hs (hspan.symm ▸ AddSubgroup.mem_top x) n

end AddSubgroupClosure

/-! ### Line elements -/

section LineElement

variable {R : Type*} [CommRing R] [PreLambdaRing R]

/-- An element `l : R` is a **line element** if its total `λ`-series is `1 + l X`, i.e.,
`totalSeries l = 1 + C l * X`. Line elements need not be units (for instance, `0` is always a line
element). -/
def IsLineElement (l : R) : Prop :=
  totalSeries l = 1 + C l * X

theorem isLineElement_def (l : R) :
    IsLineElement l ↔ totalSeries l = 1 + C l * X :=
  (Iff.rfl)

/-- `l` is a line element if and only if `λ^n(l) = 0` for every `n ≥ 2`. -/
theorem isLineElement_iff_forall_two_le {l : R} :
    IsLineElement l ↔ ∀ ⦃n : ℕ⦄, 2 ≤ n → lambdaOp n l = 0 := by
  rw [isLineElement_def, PowerSeries.ext_iff]
  constructor
  · intro h n hn
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    simpa [coeff_one, hn0, hn1, coeff_C_mul, coeff_X] using h n
  · intro h n
    match n with
    | 0 => simp
    | 1 => simp
    | n + 2 =>
      simpa [coeff_one, coeff_C_mul, coeff_X] using h (Nat.le_add_left 2 n)

/-- Zero is a line element in every pre-`λ`-ring. -/
@[simp]
theorem IsLineElement.zero : IsLineElement (0 : R) := by
  simp [isLineElement_def]

namespace IsLineElement

theorem totalSeries_eq {l : R} (hl : IsLineElement l) :
    totalSeries l = 1 + C l * X :=
  hl

theorem lambdaOp_eq_zero {l : R} (hl : IsLineElement l) {n : ℕ} (hn : 2 ≤ n) :
    lambdaOp n l = 0 :=
  isLineElement_iff_forall_two_le.mp hl hn

/-- Natural multiples of a line element satisfy `totalSeries (m • l) = (1 + C l * X) ^ m`. -/
theorem totalSeries_nsmul {l : R} (hl : IsLineElement l) (m : ℕ) :
    totalSeries (m • l) = (1 + C l * X) ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [succ_nsmul, totalSeries_add, ih, hl.totalSeries_eq, pow_succ]

/-- The total `λ`-series of `-l` for a line element `l` is the geometric series `∑ (-l)^n X^n`. -/
theorem totalSeries_neg {l : R} (hl : IsLineElement l) :
    totalSeries (-l) = PowerSeries.mk fun n ↦ (-l) ^ n := by
  have hmul : totalSeries l * (PowerSeries.mk fun n ↦ (-l) ^ n) = 1 := by
    rw [hl.totalSeries_eq, add_mul, one_mul, mul_assoc]
    ext n
    rcases n with _ | n
    · simp
    · simp [coeff_succ_X_mul, pow_succ]
      ring
  calc
    totalSeries (-l) = totalSeries (-l) * 1 := (mul_one _).symm
    _ = totalSeries (-l) * (totalSeries l * PowerSeries.mk fun n ↦ (-l) ^ n) := by rw [hmul]
    _ = (totalSeries (-l) * totalSeries l) * PowerSeries.mk fun n ↦ (-l) ^ n :=
      (mul_assoc _ _ _).symm
    _ = PowerSeries.mk fun n ↦ (-l) ^ n := by rw [totalSeries_neg_mul_totalSeries, one_mul]

/-- The negative of a line element `l` has `λ^n(-l) = (-l) ^ n`. -/
theorem lambdaOp_neg {l : R} (hl : IsLineElement l) (n : ℕ) :
    lambdaOp n (-l) = (-l) ^ n := by
  rw [← coeff_totalSeries, hl.totalSeries_neg, coeff_mk]

/-- On the integer multiples `z • l` of a line element `l`, the total `λ`-series is obtained by
evaluating the formal binomial series `(1 + X)^z` at `l X`. -/
theorem totalSeries_zsmul {l : R} (hl : IsLineElement l) (z : ℤ) :
    totalSeries (z • l) =
      rescale l ((binomialSeries ℤ z).map (Int.castRingHom R)) := by
  have h1 : rescale l ((binomialSeries ℤ (1 : ℤ)).map (Int.castRingHom R)) = totalSeries l := by
    have hbin1 : binomialSeries ℤ (1 : ℤ) = 1 + X := by
      simpa using binomialSeries_nat (R := ℤ) (A := ℤ) 1
    simp [hbin1, hl.totalSeries_eq, rescale_X]
  induction z using Int.induction_on with
  | zero => simp
  | succ m ih =>
    rw [add_smul, one_smul, totalSeries_add, ih, binomialSeries_add, map_mul, map_mul, h1]
  | pred m ih =>
    have hinv : totalSeries (-l) * totalSeries l = 1 := totalSeries_neg_mul_totalSeries l
    have hbin_neg :
        rescale l ((binomialSeries ℤ (-1 : ℤ)).map (Int.castRingHom R)) * totalSeries l = 1 := by
      rw [← h1, ← map_mul, ← map_mul, ← binomialSeries_add]
      simp
    have hneg1 :
        totalSeries (-l) = rescale l ((binomialSeries ℤ (-1 : ℤ)).map (Int.castRingHom R)) := by
      calc
        totalSeries (-l) = totalSeries (-l) * (totalSeries l * totalSeries (-l)) := by
          rw [totalSeries_mul_totalSeries_neg, mul_one]
        _ = (totalSeries (-l) * totalSeries l) * totalSeries (-l) := (mul_assoc _ _ _).symm
        _ = (rescale l ((binomialSeries ℤ (-1 : ℤ)).map (Int.castRingHom R)) * totalSeries l) *
            totalSeries (-l) := by rw [hinv, hbin_neg]
        _ = rescale l ((binomialSeries ℤ (-1 : ℤ)).map (Int.castRingHom R)) *
            (totalSeries l * totalSeries (-l)) := mul_assoc _ _ _
        _ = rescale l ((binomialSeries ℤ (-1 : ℤ)).map (Int.castRingHom R)) := by
          rw [totalSeries_mul_totalSeries_neg, mul_one]
    rw [sub_eq_add_neg, add_smul, neg_one_smul, totalSeries_add, ih, hneg1,
      binomialSeries_add, map_mul, map_mul]

/-- Integer multiples of a line element satisfy `λ^n(z • l) = Ring.choose z n • l ^ n`. -/
theorem lambdaOp_zsmul {l : R} (hl : IsLineElement l) (z : ℤ) (n : ℕ) :
    lambdaOp n (z • l) = Ring.choose z n • l ^ n := by
  rw [← coeff_totalSeries, hl.totalSeries_zsmul, coeff_rescale, coeff_map, binomialSeries_coeff,
    smul_eq_mul, mul_one, Int.coe_castRingHom, mul_comm, zsmul_eq_mul]

/-- Natural multiples of a line element satisfy `λ^n(m • l) = m.choose n • l ^ n`. -/
theorem lambdaOp_nsmul {l : R} (hl : IsLineElement l) (m n : ℕ) :
    lambdaOp n (m • l) = m.choose n • l ^ n := by
  rw [← natCast_zsmul, hl.lambdaOp_zsmul, Ring.choose_natCast, natCast_zsmul]

/-- For two line elements `l₁` and `l₂`, `λ^2(l₁ + l₂) = l₁ * l₂`. -/
theorem lambdaOp_two_add {l₁ l₂ : R} (hl₁ : IsLineElement l₁) (hl₂ : IsLineElement l₂) :
    lambdaOp 2 (l₁ + l₂) = l₁ * l₂ := by
  rw [PreLambdaRing.lambdaOp_two_add, hl₁.lambdaOp_eq_zero (le_refl 2),
    hl₂.lambdaOp_eq_zero (le_refl 2), zero_add, add_zero]

end IsLineElement

end LineElement

end PreLambdaRing

export PreLambdaRing (IsLineElement)

end TauCeti
