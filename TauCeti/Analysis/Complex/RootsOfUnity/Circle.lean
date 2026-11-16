/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Roots of unity in the circle

Mathlib's `ZMod.toCircle : AddChar (ZMod n) Circle` sends `j` to `e^{2πi j / n}`. This file records
that its values are exactly the `n`-th roots of unity of the circle, in the form used to compare
points of the circle with the same `n`-th power. These are the facts needed to identify the orbits
of the cyclic rotation groups `ℤ/n` acting on the circle, as in the quotient constructions of lens
spaces.

## Main results

* `ZMod.toCircle_pow_eq_one`: every value of `ZMod.toCircle` is an `n`-th root of unity.
* `ZMod.exists_toCircle_eq_of_pow_eq_one`: every `n`-th root of unity in the circle is a value
  of `ZMod.toCircle`.
* `ZMod.toCircle_pow_mul_eq_self_iff`: for `n` coprime to `b`, multiplication by `toCircle k ^ b`
  fixes a nonzero complex number only for `k = 0`, so `ℤ/n` acts freely on `ℂ \ {0}` this way.
* `Subgroup.instIsCyclicSubgroupCircle`: every finite subgroup of `Circle` is cyclic.
* `Subgroup.eq_range_toCircle_of_finite`: every finite subgroup of `Circle` is the image of
  `ZMod.toCircle` at its order.
* `Subgroup.eq_of_subgroup_circle_of_natCard_eq`: two finite subgroups of `Circle` of the same
  order are equal.
-/

public section

namespace ZMod

variable {n : ℕ} [NeZero n]

/-- The values of `ZMod.toCircle` are `n`-th roots of unity. -/
theorem toCircle_pow_eq_one (j : ZMod n) : toCircle j ^ n = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, natCast_self, zero_mul, AddChar.map_zero_eq_one]

/-- **The `n`-th roots of unity in the circle are the values of `ZMod.toCircle`.** -/
theorem exists_toCircle_eq_of_pow_eq_one {ζ : Circle} (hζ : ζ ^ n = 1) :
    ∃ j : ZMod n, toCircle j = ζ := by
  obtain ⟨j, hj⟩ := (bijective_rootsOfUnityAddChar (n := n)).2 ⟨toUnits ζ, by
    rw [mem_rootsOfUnity, ← map_pow, hζ, map_one]⟩
  exact ⟨j, by simpa using congrArg (fun u : rootsOfUnity n Circle ↦ ((u : Circleˣ) : Circle)) hj⟩

/-- **The rotations by `b`-th powers of `n`-th roots of unity act freely.** For `n` coprime to `b`,
multiplication by `toCircle k ^ b` fixes a nonzero complex number `w` only for `k = 0`. -/
theorem toCircle_pow_mul_eq_self_iff {b : ℕ} (hnb : n.Coprime b) {w : ℂ} (hw : w ≠ 0)
    {k : ZMod n} : ((toCircle k ^ b : Circle) : ℂ) * w = w ↔ k = 0 := by
  rw [mul_eq_right₀ hw, Circle.coe_eq_one, ← AddChar.map_nsmul_eq_pow,
    ← (toCircle (N := n)).map_zero_eq_one, injective_toCircle.eq_iff, nsmul_eq_mul,
    ((isUnit_iff_coprime b n).2 hnb.symm).mul_right_eq_zero]

end ZMod

namespace Subgroup

/-- **Every finite subgroup of `Circle` is cyclic**, since it embeds into the multiplicative
monoid of the field `ℂ` along `Circle.coeHom`. -/
instance instIsCyclicSubgroupCircle (H : Subgroup Circle) [Finite H] : IsCyclic H :=
  isCyclic_of_injective_ringHom (Circle.coeHom.comp H.subtype)
    (Circle.coe_injective.comp Subtype.val_injective)

/-- **Every finite subgroup of `Circle` is the subgroup of `(Nat.card H)`-th roots of unity**,
given as the range of `ZMod.toCircle` at `Nat.card H`. -/
theorem eq_range_toCircle_of_finite (H : Subgroup Circle) [Finite H] :
    H = (ZMod.toCircle (N := Nat.card H)).toMonoidHom.range := by
  have : NeZero (Nat.card H) := ⟨Nat.card_pos.ne'⟩
  have : Finite (ZMod.toCircle (N := Nat.card H)).toMonoidHom.range :=
    Set.finite_range (ZMod.toCircle (N := Nat.card H)).toMonoidHom
  have hle : H ≤ (ZMod.toCircle (N := Nat.card H)).toMonoidHom.range := fun ζ hζ ↦ by
    have hpow : ζ ^ Nat.card H = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (x := (⟨ζ, hζ⟩ : H)))
    exact ZMod.exists_toCircle_eq_of_pow_eq_one hpow
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hbij : Function.Bijective (ZMod.toCircle (N := Nat.card H)).toMonoidHom.rangeRestrict :=
    ⟨fun _ _ h ↦ ZMod.injective_toCircle (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩
  have hcard : Nat.card (ZMod.toCircle (N := Nat.card H)).toMonoidHom.range = Nat.card H := by
    rw [← Nat.card_eq_of_bijective _ hbij]
    exact Nat.card_zmod (Nat.card H)
  exact hcard.le

/-- **Two finite subgroups of `Circle` of the same cardinality are equal.** -/
theorem eq_of_subgroup_circle_of_natCard_eq {H₁ H₂ : Subgroup Circle} [Finite H₁] [Finite H₂]
    (h : Nat.card H₁ = Nat.card H₂) : H₁ = H₂ := by
  rw [H₁.eq_range_toCircle_of_finite, H₂.eq_range_toCircle_of_finite]
  congr!

end Subgroup
