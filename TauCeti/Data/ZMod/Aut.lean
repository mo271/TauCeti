/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Aut

/-!
# `(ℤ/Nℤ)ˣ` is the automorphism group of `Multiplicative (ZMod N)`

Every additive automorphism of `ℤ/Nℤ` is multiplication by a unique unit (`ZMod.AddAutEquivUnits`).
Transporting this equivalence along `AddEquiv.toMultiplicative` identifies the unit group
`(ZMod N)ˣ` with the group of automorphisms of `ℤ/Nℤ` written multiplicatively,
`Multiplicative (ZMod N)`, matching `TauCeti.zmodProdMulAutEquiv` for `(ℤ/Nℤ)²`.

Precomposing a homomorphism `φ : Multiplicative (ZMod N) →* G` with the automorphism attached to
`u : (ZMod N)ˣ` sends the generator `1` to `φ u = (φ 1) ^ ((u : ZMod N).cast : ℤ)`
(`TauCeti.zmodMonoidHom_apply_ofAdd`). This is the diamond action `P ↦ uP` on naive `[Γ₁(N)]`-level
structures.

## Main definitions

* `TauCeti.zmodUnitsMulAutEquiv N`: the group isomorphism
  `(ZMod N)ˣ ≃* MulAut (Multiplicative (ZMod N))`, valid for all `N : ℕ`.

## Main results

* `TauCeti.zmodUnitsMulAutEquiv_apply`: the automorphism of `u : (ZMod N)ˣ` sends `x` to `u * x`.
* `TauCeti.coe_zmodUnitsMulAutEquiv_symm_apply`: the unit attached to an automorphism `σ` is the
  image of `1`.
* `TauCeti.zmodMonoidHom_apply_ofAdd`: any homomorphism `φ : Multiplicative (ZMod N) →* G` sends
  `a` to `(φ 1) ^ (a.cast : ℤ)`, for all `N : ℕ`.
-/

public section

namespace TauCeti

variable (N : ℕ)

/-- **`(ℤ/Nℤ)ˣ` is the automorphism group of `Multiplicative (ZMod N)`.** A unit `u : (ZMod N)ˣ`
acts on `ℤ/Nℤ` by left multiplication (`zmodUnitsMulAutEquiv_apply`), and every group automorphism
of `Multiplicative (ZMod N)` arises from a unique unit, whose value in `ZMod N` is the image of `1`
(`coe_zmodUnitsMulAutEquiv_symm_apply`). -/
def zmodUnitsMulAutEquiv : (ZMod N)ˣ ≃* MulAut (Multiplicative (ZMod N)) where
  toFun u :=
    { toFun x := .ofAdd ((u : ZMod N) * x.toAdd)
      invFun x := .ofAdd ((↑u⁻¹ : ZMod N) * x.toAdd)
      left_inv x := by simp [← mul_assoc]
      right_inv x := by simp [← mul_assoc]
      map_mul' x y := by simp [mul_add] }
  invFun σ := (ZMod.AddAutEquivUnits N (AddEquiv.toMultiplicative.symm σ)).toMul
  left_inv _ := by ext; simp
  right_inv σ := by
    have h := (ZMod.AddAutEquivUnits N).left_inv (AddEquiv.toMultiplicative.symm σ)
    ext x
    simpa [Units.smul_def] using DFunLike.congr_fun h x.toAdd
  map_mul' _ _ := MulEquiv.ext fun _ ↦ by simp [mul_assoc]

variable {N}

/-- The automorphism of `Multiplicative (ZMod N)` attached to `u : (ZMod N)ˣ` sends `x` to
`u * x`. -/
@[simp]
theorem zmodUnitsMulAutEquiv_apply (u : (ZMod N)ˣ) (x : ZMod N) :
    zmodUnitsMulAutEquiv N u (.ofAdd x) = .ofAdd ((u : ZMod N) * x) := by
  rfl

/-- The inverse of the automorphism attached to `u : (ZMod N)ˣ` sends `x` to `u⁻¹ * x`. -/
@[simp]
theorem zmodUnitsMulAutEquiv_symm_apply_ofAdd (u : (ZMod N)ˣ) (x : ZMod N) :
    (zmodUnitsMulAutEquiv N u).symm (.ofAdd x) = .ofAdd ((↑u⁻¹ : ZMod N) * x) := by
  rw [← MulAut.inv_def, ← map_inv]
  exact zmodUnitsMulAutEquiv_apply u⁻¹ x

/-- The unit in `(ZMod N)ˣ` attached to an automorphism `σ` of `Multiplicative (ZMod N)` has
underlying residue `σ 1`. -/
@[simp]
theorem coe_zmodUnitsMulAutEquiv_symm_apply (σ : MulAut (Multiplicative (ZMod N))) :
    (((zmodUnitsMulAutEquiv N).symm σ : (ZMod N)ˣ) : ZMod N) = (σ (.ofAdd 1)).toAdd := by
  obtain ⟨u, rfl⟩ := (zmodUnitsMulAutEquiv N).surjective σ
  simp

/-- In `Multiplicative (ZMod N)`, raising the additive generator `1` to `(a.cast : ℤ)` gives `a`,
for every `N : ℕ` (including `N = 0` and `N = 1`). -/
theorem ofAdd_one_zpow_zmod_cast (a : ZMod N) :
    (.ofAdd 1 : Multiplicative (ZMod N)) ^ (a.cast : ℤ) = .ofAdd a := by
  rw [← ofAdd_zsmul, zsmul_one, ZMod.intCast_zmod_cast]

/-- Every monoid homomorphism `φ : Multiplicative (ZMod N) →* G` into a group `G` sends `a` to
`(φ 1) ^ (a.cast : ℤ)`, for every `N : ℕ`. -/
theorem zmodMonoidHom_apply_ofAdd {G : Type*} [Group G]
    (φ : Multiplicative (ZMod N) →* G) (a : ZMod N) :
    φ (.ofAdd a) = φ (.ofAdd 1) ^ (a.cast : ℤ) := by
  rw [← ofAdd_one_zpow_zmod_cast a, map_zpow]

end TauCeti
