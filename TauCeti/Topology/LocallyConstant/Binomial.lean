/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Binomial
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Pointwise binomial ring structure on locally constant functions

For a topological space `X` and a binomial ring `R`, locally constant functions `X → R` inherit a
pointwise binomial structure (`LocallyConstant.binomialRing`), because any unary map on `R`
preserves local constancy on `X` and Pochhammer evaluations commute with evaluation at a point.

Because `Mathlib.RingTheory.Binomial` registers a global `BinomialRing` instance on every
`ℚ≥0`-module with natural powers, `LocallyConstant.binomialRing` is exposed as a definition for a
general target `R` (avoiding a non-definitional diamond on `LocallyConstant X A` when `A` is a
`ℚ≥0`-module) and registered as a global instance for `ℕ` and `ℤ`
(`LocallyConstant.instBinomialRingNat` and `LocallyConstant.instBinomialRingInt`). Pointwise
evaluation of `Ring.multichoose` and `Ring.choose` holds for any `BinomialRing` instance on
`LocallyConstant X R` (`LocallyConstant.multichoose_apply` and `LocallyConstant.choose_apply`),
since `HasUniqueDiv` forces agreement after multiplying by `n!`.
-/

public section

namespace LocallyConstant

variable {X R : Type*} [TopologicalSpace X]

instance instHasUniqueDiv [AddMonoid R] [HasUniqueDiv R] : HasUniqueDiv (LocallyConstant X R) where
  nsmul_right_injective _ hn _ _ h := ext fun x ↦
    nsmul_right_injective hn (congrArg (fun f : LocallyConstant X R ↦ f x) h)

/-- Evaluating a `ℕ`-polynomial via `Polynomial.smeval` on a locally constant function commutes
with evaluation at any point of `X`. -/
theorem smeval_nat_apply [AddCommMonoid R] [Pow R ℕ] (p : Polynomial ℕ)
    (f : LocallyConstant X R) (x : X) :
    (p.smeval f) x = p.smeval (f x) := by
  rw [Polynomial.smeval_eq_sum, Polynomial.smeval_eq_sum, Polynomial.sum_def, Polynomial.sum_def]
  exact map_sum (evalAddMonoidHom x) _ _

/-- Evaluating a `ℤ`-polynomial via `Polynomial.smeval` on a locally constant function commutes
with evaluation at any point of `X`. -/
theorem smeval_int_apply [AddCommGroup R] [Pow R ℕ] (p : Polynomial ℤ)
    (f : LocallyConstant X R) (x : X) :
    (p.smeval f) x = p.smeval (f x) := by
  rw [Polynomial.smeval_eq_sum, Polynomial.smeval_eq_sum, Polynomial.sum_def, Polynomial.sum_def]
  exact map_sum (evalAddMonoidHom x) _ _

section Binomial

attribute [local instance] BinomialRing.toHasUniqueDiv

/-- Pointwise `BinomialRing` structure on `LocallyConstant X R` from a `BinomialRing` structure on
`R`. Registered globally for `ℕ` and `ℤ` so as not to conflict definitionally with the
`Module ℚ≥0` instance on rational algebras. -/
@[instance_reducible]
def binomialRing [AddCommMonoid R] [Pow R ℕ] [BinomialRing R] :
    BinomialRing (LocallyConstant X R) where
  multichoose f n := f.map fun r ↦ Ring.multichoose r n
  factorial_nsmul_multichoose f n := ext fun x ↦ by
    rw [smul_apply, map_apply, Function.comp_apply,
      Ring.factorial_nsmul_multichoose_eq_ascPochhammer, smeval_nat_apply]

instance instBinomialRingNat : BinomialRing (LocallyConstant X ℕ) := binomialRing

instance instBinomialRingInt : BinomialRing (LocallyConstant X ℤ) := binomialRing

/-- Pointwise formula for `Ring.multichoose` on `LocallyConstant X R`, valid for any
`BinomialRing (LocallyConstant X R)` instance by unique divisibility by `n!`. -/
@[simp]
theorem multichoose_apply [AddCommMonoid R] [Pow R ℕ] [BinomialRing R]
    [BinomialRing (LocallyConstant X R)] (f : LocallyConstant X R) (n : ℕ) (x : X) :
    Ring.multichoose f n x = Ring.multichoose (f x) n := by
  apply nsmul_right_injective (Nat.factorial_ne_zero n)
  dsimp only
  rw [← smul_apply, Ring.factorial_nsmul_multichoose_eq_ascPochhammer, smeval_nat_apply,
    Ring.factorial_nsmul_multichoose_eq_ascPochhammer]

/-- Pointwise formula for `Ring.choose` on `LocallyConstant X R`, valid for any
`BinomialRing (LocallyConstant X R)` instance. -/
@[simp]
theorem choose_apply [Ring R] [BinomialRing R] [BinomialRing (LocallyConstant X R)]
    (f : LocallyConstant X R) (n : ℕ) (x : X) :
    Ring.choose f n x = Ring.choose (f x) n :=
  Ring.map_choose (evalRingHom x) f n

/-- `LocallyConstant.constRingHom` commutes with `Ring.choose`. -/
@[simp]
theorem choose_const [Ring R] [BinomialRing R] [BinomialRing (LocallyConstant X R)]
    (r : R) (n : ℕ) :
    Ring.choose (const X r) n = const X (Ring.choose r n) :=
  (Ring.map_choose constRingHom r n).symm

/-- Precomposition along a continuous map commutes with `Ring.choose`. -/
@[simp]
theorem choose_comap {Y : Type*} [TopologicalSpace Y] [Ring R]
    [BinomialRing (LocallyConstant X R)] [BinomialRing (LocallyConstant Y R)]
    (g : C(X, Y)) (f : LocallyConstant Y R) (n : ℕ) :
    Ring.choose (f.comap g) n = (Ring.choose f n).comap g :=
  (Ring.map_choose (comapRingHom g) f n).symm

end Binomial

end LocallyConstant
