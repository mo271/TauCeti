/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.WithTop.Untop0
public import Mathlib.Basic.Real.Basic
public import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic
public import TauCeti.NumberTheory.LocalField.InertiaDegree
public import TauCeti.RingTheory.Valuation.ToAdditive

/-!
# Additive normalized valuations on a nonarchimedean local field

`TauCeti.normalizedValuation K` is the normalized valuation of a nonarchimedean local field `K` as
a multiplicative homomorphism `Kˣ →* Multiplicative ℤ`. Two additive interfaces are needed when
forming difference quotients and Newton polygons over `K`:

* `TauCeti.addValInt K : K → ℤ`, decoding `normalizedValuation K` on nonzero elements and sending
  `0` to the junk value `0`, convenient in rational difference formulas on nonzero elements such as
  conjugate ramification breaks `(v_M(σ α - α) - v_M(α)) / e(M/L)`.
* `TauCeti.normalizedIntAddValuation K : AddValuation K (WithTop ℤ)` and
  `TauCeti.normalizedAddValuation K : AddValuation K (WithTop ℝ)`, genuine additive valuations
  sending `0` to `⊤` and a nonzero element `x` to `addValInt K x`, obtained by applying
  `Valuation.addVal` to `ValuativeRel.valuation K` transported along `valueGroupWithZeroIsoInt K`.
  `normalizedAddValuation K` is the valuation argument expected by `Polynomial.newtonPolygon` and
  `Polynomial.newtonSlopes`.

In a scalar tower `K → L → M` of compatible local fields, every `K`-algebra embedding
`σ : L →ₐ[K] M` (not only the canonical inclusion) scales valuations by the ramification index
`ramificationIndex L M`.

## Main definitions

* `TauCeti.addValInt K`: the integer-valued normalized valuation `K → ℤ`, with `0 ↦ 0`.
* `TauCeti.normalizedIntAddValuation K`: the `WithTop ℤ`-valued normalized additive valuation.
* `TauCeti.normalizedAddValuation K`: the `WithTop ℝ`-valued normalized additive valuation.

## Main results

* `TauCeti.addValInt_zero`, `TauCeti.addValInt_of_ne_zero`, `TauCeti.addValInt_coe_unit`,
  `TauCeti.addValInt_mul`, `TauCeti.addValInt_div`, `TauCeti.addValInt_pow`,
  `TauCeti.addValInt_zpow`, `TauCeti.addValInt_irreducible`, `TauCeti.addValInt_natCast`:
  basic arithmetic and normalization of `addValInt`.
* `TauCeti.normalizedIntAddValuation_of_ne_zero`, `TauCeti.normalizedAddValuation_of_ne_zero`,
  `TauCeti.normalizedAddValuation_eq_top_iff`, `TauCeti.exists_int_normalizedAddValuation`:
  agreement of the genuine additive valuations with `addValInt` away from zero and integrality on
  nonzero elements.
* `TauCeti.normalizedAddValuation_coe_integer`,
  `TauCeti.normalizedAddValuation_natCast_of_ne_zero`,
  `TauCeti.normalizedAddValuation_natCast_le_of_factorization_le`: agreement with
  `IsDiscreteValuationRing.addVal 𝒪[K]` on the ring of integers and comparison of natural-number
  casts through the residue-characteristic factorization, uniformly across mixed and equal
  characteristic.
* `TauCeti.addValInt_algebraMap`, `TauCeti.normalizedAddValuation_algebraMap`,
  `TauCeti.ramificationIndex_mul_addValInt_algHom`, `TauCeti.addValInt_algHom`,
  `TauCeti.normalizedAddValuation_algHom`: scaling along the algebra map and along any
  `K`-embedding `L →ₐ[K] M`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter I, §§2 and 4; Chapter II, §2.
-/

public section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField
open scoped WithZero

namespace TauCeti

section SingleField

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The integer-valued normalized additive valuation on a nonarchimedean local field `K`, sending a
nonzero element `x` to `(normalizedValuation K (Units.mk0 x hx)).toAdd` and `0` to `0`. -/
def addValInt (x : K) : ℤ :=
  open Classical in
  if hx : x = 0 then 0 else (normalizedValuation K (Units.mk0 x hx)).toAdd

/-- The `WithTop ℤ`-valued normalized additive valuation of a nonarchimedean local field `K`,
sending `0` to `⊤` and a uniformizer to `1`. -/
def normalizedIntAddValuation : AddValuation K (WithTop ℤ) :=
  ((valuation K).map (valueGroupWithZeroIsoInt K : ValueGroupWithZero K →*₀o ℤᵐ⁰)).addVal

/-- The `WithTop ℝ`-valued normalized additive valuation of a nonarchimedean local field `K`,
sending `0` to `⊤` and a uniformizer to `1`. -/
def normalizedAddValuation : AddValuation K (WithTop ℝ) :=
  (normalizedIntAddValuation K).map
    { (Int.castAddHom ℝ).withTopMap with
      monotone' := WithTop.monotone_map_iff.mpr fun _ _ h ↦ Int.cast_le.mpr h }
    rfl

variable {K}

/-- `addValInt K` takes the junk value `0` at `0`. -/
@[simp]
theorem addValInt_zero : addValInt K 0 = 0 :=
  dite_eq_left rfl

/-- On a nonzero element, `addValInt K` decodes `normalizedValuation K`. -/
theorem addValInt_of_ne_zero {x : K} (hx : x ≠ 0) :
    addValInt K x = (normalizedValuation K (Units.mk0 x hx)).toAdd :=
  dite_eq_right hx

/-- On a unit `u : Kˣ`, `addValInt K` is `(normalizedValuation K u).toAdd`. -/
@[simp]
theorem addValInt_coe_unit (u : Kˣ) :
    addValInt K (u : K) = (normalizedValuation K u).toAdd := by
  have hu : Units.mk0 (u : K) u.ne_zero = u := Units.ext rfl
  rw [addValInt_of_ne_zero u.ne_zero, hu]

/-- `addValInt K 1 = 0`. -/
@[simp]
theorem addValInt_one : addValInt K 1 = 0 := by
  rw [show (1 : K) = ((1 : Kˣ) : K) from rfl, addValInt_coe_unit, map_one, toAdd_one]

/-- Negation preserves `addValInt K`. -/
@[simp]
theorem addValInt_neg (x : K) : addValInt K (-x) = addValInt K x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx' : -x ≠ 0 := neg_ne_zero.mpr hx
  have hu : Units.mk0 (-x) hx' = -Units.mk0 x hx := Units.ext rfl
  rw [addValInt_of_ne_zero hx', addValInt_of_ne_zero hx, hu, normalizedValuation_neg]

/-- On nonzero elements, `addValInt K` turns multiplication into addition. -/
theorem addValInt_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    addValInt K (x * y) = addValInt K x + addValInt K y := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have hu : Units.mk0 (x * y) hxy = Units.mk0 x hx * Units.mk0 y hy := Units.ext rfl
  rw [addValInt_of_ne_zero hxy, addValInt_of_ne_zero hx, addValInt_of_ne_zero hy, hu, map_mul,
    toAdd_mul]

/-- `addValInt K` negates under inversion. -/
theorem addValInt_inv (x : K) : addValInt K x⁻¹ = -addValInt K x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hxi : x⁻¹ ≠ 0 := inv_ne_zero hx
  have hu : Units.mk0 x⁻¹ hxi = (Units.mk0 x hx)⁻¹ := Units.ext rfl
  rw [addValInt_of_ne_zero hxi, addValInt_of_ne_zero hx, hu, map_inv, toAdd_inv]

/-- On nonzero elements, `addValInt K` turns division into subtraction. -/
theorem addValInt_div {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    addValInt K (x / y) = addValInt K x - addValInt K y := by
  rw [div_eq_mul_inv, addValInt_mul hx (inv_ne_zero hy), addValInt_inv, sub_eq_add_neg]

/-- On a nonzero element, `addValInt K (x ^ n) = n * addValInt K x`. -/
theorem addValInt_pow {x : K} (hx : x ≠ 0) (n : ℕ) :
    addValInt K (x ^ n) = n * addValInt K x := by
  have hxn : x ^ n ≠ 0 := pow_ne_zero n hx
  have hu : Units.mk0 (x ^ n) hxn = Units.mk0 x hx ^ n := Units.ext (by simp)
  rw [addValInt_of_ne_zero hxn, addValInt_of_ne_zero hx, hu, map_pow, toAdd_pow, nsmul_eq_mul]

/-- On a nonzero element, `addValInt K (x ^ n) = n * addValInt K x` for `n : ℤ`. -/
theorem addValInt_zpow {x : K} (hx : x ≠ 0) (n : ℤ) :
    addValInt K (x ^ n) = n * addValInt K x := by
  have hxn : x ^ n ≠ 0 := zpow_ne_zero n hx
  have hu : Units.mk0 (x ^ n) hxn = Units.mk0 x hx ^ n := Units.ext (by simp)
  rw [addValInt_of_ne_zero hxn, addValInt_of_ne_zero hx, hu, map_zpow, toAdd_zpow, zsmul_eq_mul,
    Int.cast_id]

/-- A uniformizer of `𝒪[K]` has `addValInt K` equal to `1`. -/
@[simp]
theorem addValInt_irreducible {π : 𝒪[K]} (hπ : Irreducible π) :
    addValInt K (π : K) = 1 := by
  rw [addValInt_of_ne_zero (fun h ↦ hπ.ne_zero (Subtype.ext h)),
    normalizedValuation_irreducible hπ, toAdd_ofAdd]

/-- On a nonzero natural-number cast, `addValInt K` agrees with `natCastValuation K`. -/
theorem addValInt_natCast (n : ℕ) (hn : (n : K) ≠ 0) :
    addValInt K (n : K) = natCastValuation K n hn := by
  rw [addValInt_of_ne_zero hn, toAdd_normalizedValuation_natCast]

/-- A nonzero element of `K` lies in `𝒪[K]` if and only if its `addValInt K` is nonnegative. -/
theorem mem_integer_iff_addValInt_nonneg {x : K} (hx : x ≠ 0) :
    x ∈ 𝒪[K] ↔ 0 ≤ addValInt K x := by
  rw [addValInt_of_ne_zero hx]
  exact mem_integer_iff_toAdd_normalizedValuation_nonneg (Units.mk0 x hx)

/-- On a nonzero element, `normalizedIntAddValuation K` equals `(addValInt K x : WithTop ℤ)`. -/
theorem normalizedIntAddValuation_of_ne_zero {x : K} (hx : x ≠ 0) :
    normalizedIntAddValuation K x = (addValInt K x : WithTop ℤ) := by
  have hv := valueGroupWithZeroIsoInt_valuation (Units.mk0 x hx)
  simpa [normalizedIntAddValuation, addValInt_of_ne_zero hx] using congrArg WithZero.negLog hv

/-- `normalizedIntAddValuation K` is `⊤` if and only if the element is zero. -/
theorem normalizedIntAddValuation_eq_top_iff {x : K} :
    normalizedIntAddValuation K x = ⊤ ↔ x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [normalizedIntAddValuation_of_ne_zero hx, hx]

/-- `normalizedAddValuation K` is obtained from `normalizedIntAddValuation K` by casting integers
to reals. -/
theorem normalizedAddValuation_eq_map (x : K) :
    normalizedAddValuation K x = (normalizedIntAddValuation K x).map ((↑) : ℤ → ℝ) := by
  rw [normalizedAddValuation]
  rfl

/-- On a nonzero element, `normalizedAddValuation K` equals `((addValInt K x : ℝ) : WithTop ℝ)`. -/
theorem normalizedAddValuation_of_ne_zero {x : K} (hx : x ≠ 0) :
    normalizedAddValuation K x = ((addValInt K x : ℝ) : WithTop ℝ) := by
  rw [normalizedAddValuation_eq_map, normalizedIntAddValuation_of_ne_zero hx, WithTop.map_coe]

/-- `normalizedAddValuation K` is `⊤` if and only if the element is zero. -/
theorem normalizedAddValuation_eq_top_iff {x : K} :
    normalizedAddValuation K x = ⊤ ↔ x = 0 := by
  rw [normalizedAddValuation_eq_map, WithTop.map_eq_top_iff, normalizedIntAddValuation_eq_top_iff]

/-- `normalizedAddValuation K` takes integer values on nonzero elements. -/
theorem exists_int_normalizedAddValuation {x : K} (hx : x ≠ 0) :
    ∃ n : ℤ, normalizedAddValuation K x = ((n : ℝ) : WithTop ℝ) :=
  ⟨addValInt K x, normalizedAddValuation_of_ne_zero hx⟩

/-- A uniformizer of `𝒪[K]` has `normalizedAddValuation K` equal to `1`. -/
@[simp]
theorem normalizedAddValuation_irreducible {π : 𝒪[K]} (hπ : Irreducible π) :
    normalizedAddValuation K (π : K) = 1 := by
  rw [normalizedAddValuation_of_ne_zero (fun h ↦ hπ.ne_zero (Subtype.ext h)),
    addValInt_irreducible hπ, Int.cast_one, WithTop.coe_one]

/-- An element of `K` lies in `𝒪[K]` if and only if its `normalizedAddValuation K` is
nonnegative. -/
theorem mem_integer_iff_normalizedAddValuation_nonneg {x : K} :
    x ∈ 𝒪[K] ↔ 0 ≤ normalizedAddValuation K x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [mem_integer_iff_addValInt_nonneg hx, normalizedAddValuation_of_ne_zero hx,
      ← WithTop.coe_zero, WithTop.coe_le_coe]
    exact_mod_cast Iff.rfl

/-- On `𝒪[K]`, `normalizedAddValuation K` agrees with `IsDiscreteValuationRing.addVal 𝒪[K]` cast
from `ℕ∞` to `WithTop ℝ`. -/
theorem normalizedAddValuation_coe_integer (a : 𝒪[K]) :
    normalizedAddValuation K (a : K) =
      (IsDiscreteValuationRing.addVal 𝒪[K] a).map ((↑) : ℕ → ℝ) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  have hu : normalizedAddValuation K ((u : 𝒪[K]) : K) = 0 := by
    have hu0 : ((u : 𝒪[K]) : K) ≠ 0 := fun h ↦ u.ne_zero (Subtype.ext h)
    have hval1 : valuation K ((u : 𝒪[K]) : K) = 1 :=
      (Valuation.integer.integers (valuation K)).valuation_unit u
    rw [normalizedAddValuation_of_ne_zero hu0, addValInt_of_ne_zero hu0,
      toAdd_eq_zero.mpr ((normalizedValuation_eq_one_iff _).mpr hval1), Int.cast_zero,
      WithTop.coe_zero]
  rw [IsDiscreteValuationRing.addVal_def' u hπ n, Subring.coe_mul, Subring.coe_pow,
    AddValuation.map_mul, AddValuation.map_pow, hu, zero_add, normalizedAddValuation_irreducible hπ,
    nsmul_one]
  rfl

/-- An integer `x : 𝒪[K]` lies in `𝓂[K]` if and only if `1 ≤ normalizedAddValuation K (x : K)`. -/
theorem mem_maximalIdeal_iff_one_le_normalizedAddValuation {x : 𝒪[K]} :
    x ∈ 𝓂[K] ↔ 1 ≤ normalizedAddValuation K (x : K) := by
  rw [normalizedAddValuation_coe_integer, show 𝓂[K] = 𝓂[K] ^ 1 from (pow_one _).symm,
    IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal]
  cases IsDiscreteValuationRing.addVal 𝒪[K] x with
  | top => simp
  | coe m =>
    rw [ENat.map_natCast, ← WithTop.coe_one, WithTop.coe_le_coe]
    exact_mod_cast Iff.rfl

/-- For every nonzero natural number `n`, `normalizedAddValuation K (n : K)` is the multiplicity of
the residue characteristic `p = ringChar 𝓀[K]` in `n` times `normalizedAddValuation K (p : K)`,
uniformly in mixed and equal characteristic. -/
theorem normalizedAddValuation_natCast_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    normalizedAddValuation K (n : K) =
      n.factorization (ringChar 𝓀[K]) • normalizedAddValuation K (ringChar 𝓀[K] : K) := by
  have hp : (ringChar 𝓀[K]).Prime := CharP.prime_ringChar 𝓀[K]
  have hu : IsUnit ((ordCompl[ringChar 𝓀[K]] n : ℕ) : 𝒪[K]) :=
    IsLocalRing.isUnit_natCast_iff_not_dvd.mpr (Nat.not_dvd_ordCompl hp hn)
  have hv0 : normalizedAddValuation K ((ordCompl[ringChar 𝓀[K]] n : ℕ) : K) = 0 := by
    rw [show ((ordCompl[ringChar 𝓀[K]] n : ℕ) : K) =
        (((ordCompl[ringChar 𝓀[K]] n : ℕ) : 𝒪[K]) : K) by simp,
      normalizedAddValuation_coe_integer, IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hu]
    simp
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n (ringChar 𝓀[K])]
  rw [Nat.cast_mul, AddValuation.map_mul, Nat.cast_pow, AddValuation.map_pow, hv0, add_zero]

/-- If `a` and `b` are nonzero natural numbers with
`a.factorization (ringChar 𝓀[K]) ≤ b.factorization (ringChar 𝓀[K])`, then
`normalizedAddValuation K (a : K) ≤ normalizedAddValuation K (b : K)`. -/
theorem normalizedAddValuation_natCast_le_of_factorization_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a.factorization (ringChar 𝓀[K]) ≤ b.factorization (ringChar 𝓀[K])) :
    normalizedAddValuation K (a : K) ≤ normalizedAddValuation K (b : K) := by
  rw [normalizedAddValuation_natCast_of_ne_zero ha, normalizedAddValuation_natCast_of_ne_zero hb]
  have hp0 : 0 ≤ normalizedAddValuation K (ringChar 𝓀[K] : K) :=
    mem_integer_iff_normalizedAddValuation_nonneg.mp (natCast_mem 𝒪[K] _)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
  rw [hd, add_nsmul]
  exact le_add_of_nonneg_right (nsmul_nonneg hp0 d)

end SingleField

section Extension

variable {K L M : Type*}
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

/-- Along a compatible local-field extension `L/K`, `addValInt` scales by `ramificationIndex K L`.
-/
@[simp]
theorem addValInt_algebraMap (x : K) :
    addValInt L (algebraMap K L x) = ramificationIndex K L * addValInt K x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hxL : algebraMap K L x ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hx
  have hu : Units.mk0 (algebraMap K L x) hxL =
      Units.map (algebraMap K L : K →* L) (Units.mk0 x hx) := Units.ext rfl
  rw [addValInt_of_ne_zero hxL, addValInt_of_ne_zero hx, hu, toAdd_normalizedValuation_algebraMap]

/-- Along a compatible local-field extension `L/K`, `normalizedAddValuation` scales by
`ramificationIndex K L`. -/
theorem normalizedAddValuation_algebraMap (x : K) :
    normalizedAddValuation L (algebraMap K L x) =
      (normalizedAddValuation K x).map ((ramificationIndex K L : ℝ) * ·) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [normalizedAddValuation_of_ne_zero ((map_ne_zero (algebraMap K L)).mpr hx),
    normalizedAddValuation_of_ne_zero hx, addValInt_algebraMap, WithTop.map_coe, Int.cast_mul,
    Int.cast_natCast]

/-- For two compatible extensions `L/K` and `M/K` and any `K`-algebra embedding `σ : L →ₐ[K] M`,
`e(L/K) * v_M(σ x) = e(M/K) * v_L(x)` without fixing a prior `L`-algebra structure on `M`. -/
theorem ramificationIndex_mul_addValInt_algHom
    [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
    [Algebra K M] [ValuativeExtension K M] (σ : L →ₐ[K] M) (x : L) :
    (ramificationIndex K L : ℤ) * addValInt M (σ x) = ramificationIndex K M * addValInt L x := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  let _ : Algebra L M := σ.toAlgebra
  have : IsScalarTower K L M := .of_algebraMap_eq fun r ↦ (σ.commutes r).symm
  have : ValuativeExtension L M := σ.valuativeExtension
  have hv : addValInt M (σ x) = ramificationIndex L M * addValInt L x :=
    addValInt_algebraMap (K := L) (L := M) x
  rw [hv, ramificationIndex_tower (K := K) (L := L) M, Nat.cast_mul, mul_assoc]

variable [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra L M] [Algebra K M] [IsScalarTower K L M] [ValuativeExtension L M]

/-- In a compatible tower `K → L → M`, every `K`-algebra embedding `σ : L →ₐ[K] M` scales
`addValInt L` by `ramificationIndex L M`. -/
theorem addValInt_algHom (σ : L →ₐ[K] M) (x : L) :
    addValInt M (σ x) = ramificationIndex L M * addValInt L x := by
  have : ValuativeExtension K M := ValuativeExtension.trans K L M
  have h := ramificationIndex_mul_addValInt_algHom σ x
  rw [ramificationIndex_tower (K := K) (L := L) M, Nat.cast_mul, mul_assoc] at h
  exact mul_left_cancel₀
    (Nat.cast_ne_zero.mpr (ramificationIndex_pos (K := K) (L := L)).ne') h

/-- In a compatible tower `K → L → M`, every `K`-algebra embedding `σ : L →ₐ[K] M` scales
`normalizedAddValuation L` by `ramificationIndex L M`. -/
theorem normalizedAddValuation_algHom (σ : L →ₐ[K] M) (x : L) :
    normalizedAddValuation M (σ x) =
      (normalizedAddValuation L x).map ((ramificationIndex L M : ℝ) * ·) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [normalizedAddValuation_of_ne_zero ((map_ne_zero σ).mpr hx),
    normalizedAddValuation_of_ne_zero hx, addValInt_algHom, WithTop.map_coe, Int.cast_mul,
    Int.cast_natCast]

end Extension

end TauCeti

end
