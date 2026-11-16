/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Powers indexed by residues

If `x ^ n = 1` in a monoid, then the power `x ^ a.val` of `x` at the canonical representative of
a residue `a : ZMod n` is multiplicative in `a`. At `n = 2` and `x = -1` this is the sign
`(-1) ^ a.val` of a residue modulo two. A product of residues gives the iterated power. The residue
of a natural number `c` gives the power `x ^ c`, and the residue `-1` gives the inverse of `x`.

In a group, using `ZMod.cast : ZMod n → ℤ` in place of `ZMod.val` gives integer powers
`x ^ (a.cast : ℤ)` satisfying the same identities without any `NeZero n` hypothesis, including at
`n = 0` (where `ZMod 0 = ℤ` and `x ^ 0 = 1` holds automatically) and `n = 1`.

## Main results

* `TauCeti.pow_val_add`: `x ^ (a + b).val = x ^ a.val * x ^ b.val` when `x ^ n = 1` and `n ≠ 0`.
* `TauCeti.pow_val_mul`: `x ^ (a * b).val = (x ^ a.val) ^ b.val` when `x ^ n = 1`.
* `TauCeti.pow_val_natCast`: `x ^ (c : ZMod n).val = x ^ c` when `x ^ n = 1`.
* `TauCeti.pow_val_neg_one`: `x ^ (-1 : ZMod n).val = x⁻¹` when `x ^ n = 1` and `n ≠ 0`.
* `TauCeti.pow_mul_val_inv`: `x ^ (k * (k⁻¹ : ZMod n).val) = x` when `x ^ n = 1` and `k` is prime
  to `n`.
* `TauCeti.zpow_zmod_cast_eq_pow_val`: `x ^ (a.cast : ℤ) = x ^ a.val` in a group when `n ≠ 0`.
* `TauCeti.zpow_zmod_cast_intCast`: `x ^ ((c : ZMod n).cast : ℤ) = x ^ c` when `x ^ n = 1`.
* `TauCeti.zpow_zmod_cast_add`, `TauCeti.zpow_zmod_cast_mul`, `TauCeti.zpow_zmod_cast_neg`,
  `TauCeti.zpow_zmod_cast_one`, `TauCeti.zpow_zmod_cast_neg_one`: additivity, multiplicativity,
  negation, `1`, and `-1` laws for `x ^ (a.cast : ℤ)` when `x ^ n = 1`, for all `n : ℕ`.
-/

public section

namespace TauCeti

/-- **A power indexed by a residue is multiplicative in the residue:** if `x ^ n = 1`, then
`x ^ (a + b).val = x ^ a.val * x ^ b.val` for `a b : ZMod n`. -/
theorem pow_val_add {M : Type*} [Monoid M] {n : ℕ} [NeZero n] {x : M} (hx : x ^ n = 1)
    (a b : ZMod n) : x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]

/-- **A power at a product of residues is an iterated power:** if `x ^ n = 1`, then
`x ^ (a * b).val = (x ^ a.val) ^ b.val` for `a b : ZMod n`. -/
theorem pow_val_mul {M : Type*} [Monoid M] {n : ℕ} {x : M} (hx : x ^ n = 1)
    (a b : ZMod n) : x ^ (a * b).val = (x ^ a.val) ^ b.val := by
  rw [ZMod.val_mul, ← pow_eq_pow_mod _ hx, pow_mul]

/-- If `x ^ n = 1`, then the power of `x` at the residue of a natural number `c` is `x ^ c`. -/
theorem pow_val_natCast {M : Type*} [Monoid M] {n : ℕ} {x : M} (hx : x ^ n = 1) (c : ℕ) :
    x ^ (c : ZMod n).val = x ^ c := by
  rw [ZMod.val_natCast, ← pow_eq_pow_mod _ hx]

/-- If `x ^ n = 1`, then the power of `x` at the residue `1` is `x`. -/
theorem pow_val_one {M : Type*} [Monoid M] {n : ℕ} {x : M} (hx : x ^ n = 1) :
    x ^ (1 : ZMod n).val = x := by
  simpa using pow_val_natCast hx 1

/-- If `x ^ n = 1` with `n ≠ 0`, then the power of `x` at the residue `-1` is the inverse of `x`. -/
theorem pow_val_neg_one {G : Type*} [DivisionMonoid G] {n : ℕ} [NeZero n] {x : G}
    (hx : x ^ n = 1) : x ^ (-1 : ZMod n).val = x⁻¹ := by
  have h := pow_val_add hx (-1) 1
  rw [neg_add_cancel, ZMod.val_zero, pow_zero, pow_val_one hx] at h
  exact eq_inv_of_mul_eq_one_left h.symm

/-- If `x ^ n = 1` and `k` is prime to `n`, then raising `x` to the power `k` and then to the
representative of the inverse of `k` modulo `n` gives back `x`. -/
theorem pow_mul_val_inv {M : Type*} [Monoid M] {n k : ℕ} {x : M} (hx : x ^ n = 1)
    (hk : k.Coprime n) : x ^ (k * (k⁻¹ : ZMod n).val) = x := by
  rw [← pow_val_natCast hx, Nat.cast_mul, ZMod.mul_val_inv hk, ← Nat.cast_one, pow_val_natCast hx,
    pow_one]

section ZPowCast

variable {G : Type*} [Group G] {n : ℕ} {x : G}

/-- For `n ≠ 0`, the integer power of `x` at `a.cast : ℤ` is the natural power `x ^ a.val`. -/
theorem zpow_zmod_cast_eq_pow_val [NeZero n] (x : G) (a : ZMod n) :
    x ^ (a.cast : ℤ) = x ^ a.val := by
  rw [ZMod.cast_eq_val, zpow_natCast]

/-- If `x ^ n = 1` in a group, then the integer power of `x` at the residue of `c : ℤ` modulo `n`
is `x ^ c`, for every `n : ℕ` (including `n = 0`). -/
theorem zpow_zmod_cast_intCast (hx : x ^ n = 1) (c : ℤ) :
    x ^ ((c : ZMod n).cast : ℤ) = x ^ c := by
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub c ((c : ZMod n).cast : ℤ) n).mp
    (ZMod.intCast_zmod_cast _).symm
  rw [sub_eq_iff_eq_add'.mp hk, zpow_add, zpow_mul, zpow_natCast, hx, one_zpow, mul_one]

/-- If `x ^ n = 1` in a group, then the integer power of `x` at the residue of `c : ℕ` modulo `n`
is `x ^ c`, for every `n : ℕ`. -/
theorem zpow_zmod_cast_natCast (hx : x ^ n = 1) (c : ℕ) :
    x ^ ((c : ZMod n).cast : ℤ) = x ^ c := by
  simpa using zpow_zmod_cast_intCast hx c

/-- If `x ^ n = 1` in a group, then the integer power of `x` at the residue `1 : ZMod n` is `x`,
for every `n : ℕ`. -/
theorem zpow_zmod_cast_one (hx : x ^ n = 1) : x ^ ((1 : ZMod n).cast : ℤ) = x := by
  simpa using zpow_zmod_cast_intCast hx 1

/-- If `x ^ n = 1` in a group, then the integer power of `x` at the residue `-1 : ZMod n` is
`x⁻¹`, for every `n : ℕ` (including `n = 0` and `n = 1`). -/
theorem zpow_zmod_cast_neg_one (hx : x ^ n = 1) : x ^ ((-1 : ZMod n).cast : ℤ) = x⁻¹ := by
  simpa using zpow_zmod_cast_intCast hx (-1)

/-- **An integer power indexed by a residue is multiplicative in the residue:** if `x ^ n = 1` in a
group, then `x ^ ((a + b).cast : ℤ) = x ^ (a.cast : ℤ) * x ^ (b.cast : ℤ)` for all `n : ℕ`. -/
theorem zpow_zmod_cast_add (hx : x ^ n = 1) (a b : ZMod n) :
    x ^ ((a + b).cast : ℤ) = x ^ (a.cast : ℤ) * x ^ (b.cast : ℤ) := by
  conv_lhs => rw [← ZMod.intCast_zmod_cast a, ← ZMod.intCast_zmod_cast b, ← Int.cast_add]
  rw [zpow_zmod_cast_intCast hx, zpow_add]

/-- If `x ^ n = 1` in a group, then `x ^ ((-a).cast : ℤ) = (x ^ (a.cast : ℤ))⁻¹` for all `n : ℕ`. -/
theorem zpow_zmod_cast_neg (hx : x ^ n = 1) (a : ZMod n) :
    x ^ ((-a).cast : ℤ) = (x ^ (a.cast : ℤ))⁻¹ := by
  conv_lhs => rw [← ZMod.intCast_zmod_cast a, ← Int.cast_neg]
  rw [zpow_zmod_cast_intCast hx, zpow_neg]

/-- **An integer power at a product of residues is an iterated power:** if `x ^ n = 1` in a group,
then `x ^ ((a * b).cast : ℤ) = (x ^ (a.cast : ℤ)) ^ (b.cast : ℤ)` for all `n : ℕ`. -/
theorem zpow_zmod_cast_mul (hx : x ^ n = 1) (a b : ZMod n) :
    x ^ ((a * b).cast : ℤ) = (x ^ (a.cast : ℤ)) ^ (b.cast : ℤ) := by
  conv_lhs => rw [← ZMod.intCast_zmod_cast a, ← ZMod.intCast_zmod_cast b, ← Int.cast_mul]
  rw [zpow_zmod_cast_intCast hx, zpow_mul]

/-- If `x ^ n = 1` in a group and `u : (ZMod n)ˣ` is a unit modulo `n`, then raising `x` to
`((u : ZMod n).cast : ℤ)` and then to `((↑u⁻¹ : ZMod n).cast : ℤ)` recovers `x`. -/
theorem zpow_zmod_cast_mul_inv (hx : x ^ n = 1) (u : (ZMod n)ˣ) :
    (x ^ ((u : ZMod n).cast : ℤ)) ^ ((↑u⁻¹ : ZMod n).cast : ℤ) = x := by
  rw [← zpow_zmod_cast_mul hx, Units.mul_inv, zpow_zmod_cast_one hx]

end ZPowCast

end TauCeti
