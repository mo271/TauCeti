/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.Topology.Order
public import TauCeti.RingTheory.PreLambdaRing.Hom
public import TauCeti.Topology.LocallyConstant.Binomial

/-!
# Binomial pre-`λ`-rings, integer structures, and locally constant functions

Any commutative `BinomialRing` `R` carries a binomial `PreLambdaRing` structure given by
`λ^n(r) = Ring.choose r n` (`TauCeti.PreLambdaRing.ofBinomialRing`), whose total series is
`(1 + X)^r` (`PowerSeries.binomialSeries R r`). Because `Mathlib.RingTheory.Binomial` registers a
global `BinomialRing` instance on every `ℚ≥0`-module, `ofBinomialRing` is exposed as an
`@[instance_reducible]` definition rather than a global `[BinomialRing R] → PreLambdaRing R`
instance (so rational algebras such as `K₀(X)_ℚ` or `ℚ × ℚ` can carry non-binomial `λ`-structures
without typeclass diamonds), and registered globally on `ℤ` (`Int.instPreLambdaRing`).

We also construct:
* `TauCeti.PreLambdaRing.intOfPowerSeries`: the pre-`λ`-ring structure on `ℤ` determined by any
  power series `φ = 1 + X + a₂ X² + ⋯ ∈ ℤ⟦X⟧` via `λ_t(m) = φ^m` (Weibel, Exercise II.4.1).
* `LocallyConstant.instPreLambdaRing`: the pointwise `PreLambdaRing` structure on
  `LocallyConstant X R` for any topological space `X` and pre-`λ`-ring `R`, together with its
  agreement with `PreLambdaRing.ofBinomialRing (LocallyConstant X ℤ)` when `R = ℤ` and its
  componentwise equivalences on discrete spaces and `Bool`.
-/

public section

open PowerSeries

namespace TauCeti

namespace PreLambdaRing

section Binomial

variable (R : Type*) [CommRing R] [BinomialRing R]

/-- Binomial `PreLambdaRing` structure on a commutative `BinomialRing` `R`, with
`λ^n(r) = Ring.choose r n` (Chu-Vandermonde). Defined as `@[instance_reducible]` rather than a
global instance so rational algebras do not inherit the binomial structure by default. -/
@[instance_reducible]
def ofBinomialRing : PreLambdaRing R where
  lambdaOp n r := Ring.choose r n
  lambdaOp_zero := Ring.choose_zero_right
  lambdaOp_one := Ring.choose_one_right
  lambdaOp_add n x y := Ring.add_choose_eq n (Commute.all x y)

variable {R}

theorem lambdaOp_ofBinomialRing (n : ℕ) (r : R) :
    @lambdaOp R _ (ofBinomialRing R) n r = Ring.choose r n :=
  (rfl)

/-- Under `ofBinomialRing R`, the total `λ`-series of `r` is `(1 + X)^r`, i.e.
`PowerSeries.binomialSeries R r`. -/
theorem totalSeries_ofBinomialRing (r : R) :
    @totalSeries R _ (ofBinomialRing R) r = binomialSeries R r := by
  ext n
  rw [@coeff_totalSeries R _ (ofBinomialRing R), lambdaOp_ofBinomialRing, binomialSeries_coeff,
    smul_eq_mul, mul_one]

/-- In any binomial pre-`λ`-ring, `1` is a line element (`λ_t(1) = 1 + t`). -/
theorem isLineElement_one_ofBinomialRing :
    @IsLineElement R _ (ofBinomialRing R) 1 := by
  rw [@isLineElement_iff_forall_two_le R _ (ofBinomialRing R)]
  intro n hn
  rw [lambdaOp_ofBinomialRing, ← Nat.cast_one, Ring.choose_natCast,
    Nat.choose_eq_zero_of_lt hn, Nat.cast_zero]

/-- Every ring homomorphism between commutative binomial rings is a pre-`λ` morphism for their
binomial `PreLambdaRing` structures. -/
theorem isPreLambdaHom_ofBinomialRing {S : Type*} [CommRing S] [BinomialRing S] (f : R →+* S) :
    @RingHom.IsPreLambdaHom R S _ (ofBinomialRing R) _ (ofBinomialRing S) f :=
  @RingHom.IsPreLambdaHom.mk R S _ (ofBinomialRing R) _ (ofBinomialRing S) f fun n r ↦
    Ring.map_choose f r n

end Binomial

end PreLambdaRing

end TauCeti

/-! ### Integer pre-`λ`-ring structures -/

/-- Canonical binomial `PreLambdaRing` structure on `ℤ`, with `λ^n(m) = Ring.choose m n`. -/
instance Int.instPreLambdaRing : TauCeti.PreLambdaRing ℤ :=
  TauCeti.PreLambdaRing.ofBinomialRing ℤ

namespace TauCeti

@[simp]
theorem lambdaOp_int_eq_choose (n : ℕ) (z : ℤ) :
    lambdaOp n z = Ring.choose z n :=
  (rfl)

theorem lambdaOp_int_natCast (n m : ℕ) :
    lambdaOp n (m : ℤ) = Nat.choose m n := by
  rw [lambdaOp_int_eq_choose, Ring.choose_natCast]

theorem PreLambdaRing.totalSeries_int (z : ℤ) :
    PreLambdaRing.totalSeries z = binomialSeries ℤ z :=
  PreLambdaRing.totalSeries_ofBinomialRing z

theorem PreLambdaRing.IsLineElement.one_int : IsLineElement (1 : ℤ) :=
  PreLambdaRing.isLineElement_one_ofBinomialRing

namespace PreLambdaRing

/-- Construct a `PreLambdaRing` structure on `ℤ` from any formal power series
`φ = 1 + X + a₂ X² + ⋯ ∈ ℤ⟦X⟧` by setting `λ_t(m) = φ^m` in `1 + X ℤ⟦X⟧`
(Weibel, *The K-book*, Exercise II.4.1). -/
@[instance_reducible]
noncomputable def intOfPowerSeries (φ : ℤ⟦X⟧) (h₀ : constantCoeff φ = 1) (h₁ : coeff 1 φ = 1) :
    PreLambdaRing ℤ :=
  ofTotalLambda (zpowersHom (principalUnitSubgroup ℤ) (principalUnitMk φ h₀)) fun z ↦ by
    have hpow := map_zpow (principalUnitCoeffOneHom ℤ) (principalUnitMk φ h₀) z
    have hone : principalUnitCoeffOneHom ℤ (principalUnitMk φ h₀) = Multiplicative.ofAdd 1 := by
      apply Multiplicative.toAdd.injective
      simp [h₁]
    rw [zpowersHom_apply, toAdd_ofAdd, ← toAdd_principalUnitCoeffOneHom, hpow, hone,
      ← ofAdd_zsmul, smul_eq_mul, mul_one, toAdd_ofAdd]

@[simp]
theorem totalSeries_intOfPowerSeries (φ : ℤ⟦X⟧) (h₀ : constantCoeff φ = 1) (h₁ : coeff 1 φ = 1)
    (z : ℤ) :
    @totalSeries ℤ _ (intOfPowerSeries φ h₀ h₁) z =
      principalUnitSeries (principalUnitMk φ h₀ ^ z) := by
  rw [intOfPowerSeries, totalSeries_ofTotalLambda, zpowersHom_apply, toAdd_ofAdd]

theorem totalSeries_intOfPowerSeries_natCast (φ : ℤ⟦X⟧) (h₀ : constantCoeff φ = 1)
    (h₁ : coeff 1 φ = 1) (n : ℕ) :
    @totalSeries ℤ _ (intOfPowerSeries φ h₀ h₁) (n : ℤ) = φ ^ n := by
  rw [totalSeries_intOfPowerSeries, zpow_natCast, principalUnitSeries_pow, principalUnitSeries_mk]

theorem totalSeries_intOfPowerSeries_one (φ : ℤ⟦X⟧) (h₀ : constantCoeff φ = 1)
    (h₁ : coeff 1 φ = 1) :
    @totalSeries ℤ _ (intOfPowerSeries φ h₀ h₁) 1 = φ := by
  simpa only [Nat.cast_one, pow_one] using totalSeries_intOfPowerSeries_natCast φ h₀ h₁ 1

@[simp]
theorem lambdaOp_intOfPowerSeries_one (φ : ℤ⟦X⟧) (h₀ : constantCoeff φ = 1) (h₁ : coeff 1 φ = 1)
    (n : ℕ) :
    @lambdaOp ℤ _ (intOfPowerSeries φ h₀ h₁) n 1 = coeff n φ := by
  rw [← @coeff_totalSeries ℤ _ (intOfPowerSeries φ h₀ h₁), totalSeries_intOfPowerSeries_one]

end PreLambdaRing

end TauCeti

/-! ### Pointwise `PreLambdaRing` structure on locally constant functions -/

namespace LocallyConstant

section PreLambdaRing

variable {X Y R S : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CommRing R] [TauCeti.PreLambdaRing R] [CommRing S] [TauCeti.PreLambdaRing S]

/-- Pointwise `PreLambdaRing` structure on locally constant functions `X → R`. -/
instance instPreLambdaRing : TauCeti.PreLambdaRing (LocallyConstant X R) where
  lambdaOp n f := f.map (TauCeti.lambdaOp n)
  lambdaOp_zero f := ext fun x ↦ TauCeti.lambdaOp_zero (f x)
  lambdaOp_one f := ext fun x ↦ TauCeti.lambdaOp_one (f x)
  lambdaOp_add _ _ _ := ext fun x ↦ by
    rw [← evalAddMonoidHom_apply (Y := R) x (∑ _ ∈ _, _), map_sum]
    simp [TauCeti.lambdaOp_add]

@[simp]
theorem lambdaOp_apply (n : ℕ) (f : LocallyConstant X R) (x : X) :
    TauCeti.lambdaOp n f x = TauCeti.lambdaOp n (f x) :=
  (rfl)

/-- Evaluation at `x : X` as a bundled `PreLambdaRingHom`. -/
def evalPreLambdaRingHom (x : X) : TauCeti.PreLambdaRingHom (LocallyConstant X R) R :=
  TauCeti.PreLambdaRingHom.ofIsPreLambdaHom (evalRingHom x)
    (RingHom.IsPreLambdaHom.mk fun _ _ ↦ rfl)

@[simp]
theorem evalPreLambdaRingHom_apply (x : X) (f : LocallyConstant X R) :
    evalPreLambdaRingHom x f = f x := by
  simp [evalPreLambdaRingHom]

variable (X) in
/-- Constant locally constant functions as a bundled `PreLambdaRingHom`. -/
def constPreLambdaRingHom : TauCeti.PreLambdaRingHom R (LocallyConstant X R) :=
  TauCeti.PreLambdaRingHom.ofIsPreLambdaHom constRingHom
    (RingHom.IsPreLambdaHom.mk fun _ _ ↦ ext fun _ ↦ rfl)

@[simp]
theorem constPreLambdaRingHom_apply (r : R) :
    constPreLambdaRingHom X r = const X r := by
  simp [constPreLambdaRingHom]

@[simp]
theorem lambdaOp_const (n : ℕ) (r : R) :
    TauCeti.lambdaOp n (const X r) = const X (TauCeti.lambdaOp n r) :=
  (rfl)

/-- Pullback of locally constant functions along a continuous map as a `PreLambdaRingHom`. -/
def comapPreLambdaRingHom (g : C(X, Y)) :
    TauCeti.PreLambdaRingHom (LocallyConstant Y R) (LocallyConstant X R) :=
  TauCeti.PreLambdaRingHom.ofIsPreLambdaHom (comapRingHom g)
    (RingHom.IsPreLambdaHom.mk fun _ _ ↦ ext fun _ ↦ rfl)

@[simp]
theorem comapPreLambdaRingHom_apply (g : C(X, Y)) (f : LocallyConstant Y R) :
    comapPreLambdaRingHom g f = f.comap g := by
  rw [comapPreLambdaRingHom, TauCeti.PreLambdaRingHom.ofIsPreLambdaHom_apply]
  rfl

/-- Pushforward of locally constant functions along a `PreLambdaRingHom`. -/
def mapPreLambdaRingHom (φ : TauCeti.PreLambdaRingHom R S) :
    TauCeti.PreLambdaRingHom (LocallyConstant X R) (LocallyConstant X S) :=
  TauCeti.PreLambdaRingHom.ofIsPreLambdaHom (mapRingHom φ.toRingHom)
    (RingHom.IsPreLambdaHom.mk fun _ _ ↦ ext fun _ ↦ by simp)

@[simp]
theorem mapPreLambdaRingHom_apply (φ : TauCeti.PreLambdaRingHom R S) (f : LocallyConstant X R)
    (x : X) : mapPreLambdaRingHom φ f x = φ (f x) := by
  simp [mapPreLambdaRingHom]

/-- On integer-valued locally constant functions, the pointwise `PreLambdaRing` structure coincides
with the binomial structure `PreLambdaRing.ofBinomialRing (LocallyConstant X ℤ)`. -/
theorem instPreLambdaRingInt_eq_ofBinomialRing :
    (instPreLambdaRing : TauCeti.PreLambdaRing (LocallyConstant X ℤ)) =
      TauCeti.PreLambdaRing.ofBinomialRing (LocallyConstant X ℤ) := by
  ext n f x
  rw [lambdaOp_apply, TauCeti.lambdaOp_int_eq_choose,
    @TauCeti.PreLambdaRing.lambdaOp_ofBinomialRing (LocallyConstant X ℤ), choose_apply]

@[simp]
theorem lambdaOp_int_eq_choose (n : ℕ) (f : LocallyConstant X ℤ) :
    TauCeti.lambdaOp n f = Ring.choose f n := by
  ext x
  rw [lambdaOp_apply, TauCeti.lambdaOp_int_eq_choose, choose_apply]

variable (X R) in
/-- On a discrete space `X`, `LocallyConstant X R` is pre-`λ`-isomorphic to `X → R` with its
coordinatewise `PreLambdaRing` structure. -/
def discretePreLambdaRingEquiv [DiscreteTopology X] :
    TauCeti.PreLambdaRingEquiv (LocallyConstant X R) (X → R) where
  toFun f := f
  invFun f := ⟨f, IsLocallyConstant.of_discrete f⟩
  left_inv _ := ext fun _ ↦ rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_lambdaOp' _ _ := rfl

@[simp]
theorem discretePreLambdaRingEquiv_apply [DiscreteTopology X] (f : LocallyConstant X R) (x : X) :
    discretePreLambdaRingEquiv X R f x = f x :=
  (rfl)

variable (R) in
/-- Locally constant functions on the two-point discrete space `Bool` identify with `R × R` as a
pre-`λ`-ring via `f ↦ (f false, f true)`. -/
def boolPreLambdaRingEquiv :
    TauCeti.PreLambdaRingEquiv (LocallyConstant Bool R) (R × R) where
  toFun f := (f false, f true)
  invFun p := ⟨fun b ↦ cond b p.2 p.1, IsLocallyConstant.of_discrete _⟩
  left_inv f := ext fun b ↦ by cases b <;> rfl
  right_inv p := by ext <;> rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_lambdaOp' _ _ := rfl

@[simp]
theorem boolPreLambdaRingEquiv_apply (f : LocallyConstant Bool R) :
    boolPreLambdaRingEquiv R f = (f false, f true) :=
  (rfl)

@[simp]
theorem boolPreLambdaRingEquiv_symm_apply_false (p : R × R) :
    (boolPreLambdaRingEquiv R).symm p false = p.1 :=
  (Prod.mk.inj ((boolPreLambdaRingEquiv_apply _).symm.trans
    ((boolPreLambdaRingEquiv R).apply_symm_apply p))).1

@[simp]
theorem boolPreLambdaRingEquiv_symm_apply_true (p : R × R) :
    (boolPreLambdaRingEquiv R).symm p true = p.2 :=
  (Prod.mk.inj ((boolPreLambdaRingEquiv_apply _).symm.trans
    ((boolPreLambdaRingEquiv R).apply_symm_apply p))).2

end PreLambdaRing

end LocallyConstant
