/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The multiplicative group `1 + X R⟦X⟧` of principal unit power series

Over a commutative ring `R`, a formal power series `φ ∈ R⟦X⟧` with constant coefficient `1` is a
unit (`PowerSeries.invOfUnit φ 1`). Such series form the kernel
`PowerSeries.principalUnitSubgroup R` of the constant-coefficient homomorphism `(R⟦X⟧)ˣ →* Rˣ`.
Realizing `1 + X R⟦X⟧` as a `Subgroup` of `(R⟦X⟧)ˣ` endows it directly with its `CommGroup`
structure, extensionality in `R⟦X⟧`, formal series inversion, and functoriality under ring
homomorphisms (`PowerSeries.principalUnitMap`).

This multiplicative group is the target of total characteristic and `λ`-series homomorphisms
`R → 1 + X R⟦X⟧`.
-/

public section

noncomputable section

namespace PowerSeries

section CommRing

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

variable (R) in
/-- The multiplicative subgroup `1 + X R⟦X⟧` of `(R⟦X⟧)ˣ` consisting of power series with constant
coefficient `1`, realized as the kernel of `Units.map constantCoeff : (R⟦X⟧)ˣ →* Rˣ`. -/
def principalUnitSubgroup : Subgroup (R⟦X⟧)ˣ :=
  (Units.map (constantCoeff (R := R)).toMonoidHom).ker

/-- A unit of `R⟦X⟧` lies in `principalUnitSubgroup R` if and only if its constant coefficient is
`1`. -/
@[simp]
theorem mem_principalUnitSubgroup {u : (R⟦X⟧)ˣ} :
    u ∈ principalUnitSubgroup R ↔ constantCoeff (u : R⟦X⟧) = 1 := by
  rw [principalUnitSubgroup, MonoidHom.mem_ker, Units.ext_iff]
  rfl

/-- Underlying formal power series of an element of `1 + X R⟦X⟧`. -/
def principalUnitSeries (u : principalUnitSubgroup R) : R⟦X⟧ :=
  ((u : (R⟦X⟧)ˣ) : R⟦X⟧)

theorem principalUnitSeries_def (u : principalUnitSubgroup R) :
    principalUnitSeries u = ((u : (R⟦X⟧)ˣ) : R⟦X⟧) :=
  (rfl)

@[simp]
theorem constantCoeff_principalUnitSeries (u : principalUnitSubgroup R) :
    constantCoeff (principalUnitSeries u) = 1 :=
  mem_principalUnitSubgroup.mp u.2

@[simp]
theorem coeff_zero_principalUnitSeries (u : principalUnitSubgroup R) :
    coeff 0 (principalUnitSeries u) = 1 := by
  rw [coeff_zero_eq_constantCoeff, constantCoeff_principalUnitSeries]

/-- Two elements of `principalUnitSubgroup R` are equal if and only if their underlying power series
are equal. -/
@[ext]
theorem principalUnit_ext {u v : principalUnitSubgroup R}
    (h : principalUnitSeries u = principalUnitSeries v) : u = v :=
  Subtype.ext (Units.ext h)

theorem principalUnitSeries_injective :
    Function.Injective (principalUnitSeries (R := R)) :=
  fun _ _ ↦ principalUnit_ext

@[simp]
theorem principalUnitSeries_one :
    principalUnitSeries (1 : principalUnitSubgroup R) = 1 :=
  (rfl)

@[simp]
theorem principalUnitSeries_mul (u v : principalUnitSubgroup R) :
    principalUnitSeries (u * v) = principalUnitSeries u * principalUnitSeries v :=
  (rfl)

@[simp]
theorem principalUnitSeries_pow (u : principalUnitSubgroup R) (n : ℕ) :
    principalUnitSeries (u ^ n) = principalUnitSeries u ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, principalUnitSeries_mul, ih]

@[simp]
theorem principalUnitSeries_mul_inv (u : principalUnitSubgroup R) :
    principalUnitSeries u * principalUnitSeries u⁻¹ = 1 :=
  Units.mul_inv (u : (R⟦X⟧)ˣ)

@[simp]
theorem principalUnitSeries_inv_mul (u : principalUnitSubgroup R) :
    principalUnitSeries u⁻¹ * principalUnitSeries u = 1 :=
  Units.inv_mul (u : (R⟦X⟧)ˣ)

/-- The inverse in `1 + X R⟦X⟧` has underlying series `invOfUnit (principalUnitSeries u) 1`. -/
theorem principalUnitSeries_inv (u : principalUnitSubgroup R) :
    principalUnitSeries u⁻¹ = invOfUnit (principalUnitSeries u) 1 := by
  apply Units.inv_eq_of_mul_eq_one_right (u := (u : (R⟦X⟧)ˣ))
  exact mul_invOfUnit (principalUnitSeries u) 1 (by simp)

/-- Construct an element of `principalUnitSubgroup R` from a power series with constant coefficient
`1`. -/
def principalUnitMk (φ : R⟦X⟧) (hφ : constantCoeff φ = 1) :
    principalUnitSubgroup R :=
  ⟨⟨φ, invOfUnit φ 1, mul_invOfUnit φ 1 (by simp [hφ]), invOfUnit_mul φ 1 (by simp [hφ])⟩,
    mem_principalUnitSubgroup.mpr hφ⟩

@[simp]
theorem principalUnitSeries_mk (φ : R⟦X⟧) (hφ : constantCoeff φ = 1) :
    principalUnitSeries (principalUnitMk φ hφ) = φ :=
  (rfl)

@[simp]
theorem principalUnitMk_principalUnitSeries (u : principalUnitSubgroup R) :
    principalUnitMk (principalUnitSeries u) (constantCoeff_principalUnitSeries u) = u := by
  ext
  rfl

/-- Pushforward of `1 + X R⟦X⟧` along a ring homomorphism `f : R →+* S`. -/
def principalUnitMap (f : R →+* S) :
    principalUnitSubgroup R →* principalUnitSubgroup S where
  toFun u := principalUnitMk ((principalUnitSeries u).map f) (by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_principalUnitSeries, map_one])
  map_one' := by ext; simp
  map_mul' u v := by ext; simp

@[simp]
theorem principalUnitSeries_map (f : R →+* S) (u : principalUnitSubgroup R) :
    principalUnitSeries (principalUnitMap f u) = (principalUnitSeries u).map f :=
  (rfl)

@[simp]
theorem principalUnitMap_id :
    principalUnitMap (RingHom.id R) = MonoidHom.id (principalUnitSubgroup R) := by
  ext u : 2
  simp

theorem principalUnitMap_comp (g : S →+* T) (f : R →+* S) :
    principalUnitMap (g.comp f) = (principalUnitMap g).comp (principalUnitMap f) := by
  ext u : 2
  rw [MonoidHom.comp_apply, principalUnitSeries_map, principalUnitSeries_map,
    principalUnitSeries_map, PowerSeries.map_comp, RingHom.comp_apply]

theorem coeff_one_principalUnitSeries_one :
    coeff 1 (principalUnitSeries (1 : principalUnitSubgroup R)) = 0 := by
  simp

theorem coeff_one_principalUnitSeries_mul (u v : principalUnitSubgroup R) :
    coeff 1 (principalUnitSeries (u * v)) =
      coeff 1 (principalUnitSeries u) + coeff 1 (principalUnitSeries v) := by
  simp [principalUnitSeries_mul, coeff_one_mul]

variable (R) in
/-- Extracting the degree-`1` coefficient is a group homomorphism `(1 + X R⟦X⟧) →* Multiplicative R`
sending `1 + a₁ X + a₂ X² + ⋯` to `Multiplicative.ofAdd a₁`. -/
def principalUnitCoeffOneHom : principalUnitSubgroup R →* Multiplicative R where
  toFun u := Multiplicative.ofAdd (coeff 1 (principalUnitSeries u))
  map_one' := by simp
  map_mul' u v := by rw [coeff_one_principalUnitSeries_mul, ofAdd_add]

@[simp]
theorem toAdd_principalUnitCoeffOneHom (u : principalUnitSubgroup R) :
    Multiplicative.toAdd (principalUnitCoeffOneHom R u) = coeff 1 (principalUnitSeries u) :=
  (rfl)

end CommRing

end PowerSeries
