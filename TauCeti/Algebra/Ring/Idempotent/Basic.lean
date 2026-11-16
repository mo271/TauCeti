/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# Componentwise arithmetic along an idempotent

An idempotent `e` of a commutative ring `R` splits it as `R ≅ e R × (1 - e) R`. Without reference
to the product decomposition, an element `e x + (1 - e) y` has `e`-component `e x` and
`(1 - e)`-component `(1 - e) y`, and since `e² = e` and `e (1 - e) = 0` such elements multiply
componentwise.

For an idempotent `p` of any ring, `2 p - 1` squares to `1`. For a star projection this is the
self-adjoint unitary `IsStarProjection.two_mul_sub_one_mem_unitary`. Conversely, for any element
`u` with `u * u = 1`, `1 + u` squares to `(1 + u) + (1 + u)`, and when `v` anticommutes with `u`
(`u * v + v * u = 0`), the sandwich `(1 + u) * (1 + v) * (1 + u)` also reduces to
`(1 + u) + (1 + u)`.

## Main results

* `IsIdempotentElem.mul_add_one_sub_mul`: elements of the form `e x + (1 - e) y` multiply
  componentwise.
* `IsIdempotentElem.two_mul_sub_one_mul_self`: `(2 p - 1) * (2 p - 1) = 1`.
* `TauCeti.one_add_mul_self_of_mul_self_eq_one`: if `u * u = 1`, then
  `(1 + u) * (1 + u) = (1 + u) + (1 + u)`.
* `TauCeti.one_add_mul_one_add_mul_one_add_of_mul_self_eq_one`: if `u * u = 1` and
  `u * v + v * u = 0`, then `(1 + u) * (1 + v) * (1 + u) = (1 + u) + (1 + u)`.
* `IsIdempotentElem.conj_one_add_mul_sub_mul`: if `e` and `e + u` are idempotent and `u * u = 0`,
  conjugating `e + u` by the unit `1 + (e * u - u * e)` recovers `e`.
-/

public section

namespace IsIdempotentElem

section CommRing

variable {R : Type*} [CommRing R] {e : R}

/-- **Componentwise multiplication**: for an idempotent `e` of a commutative ring, elements of the
form `e x + (1 - e) y` multiply componentwise, as they would in `e R × (1 - e) R`. -/
theorem mul_add_one_sub_mul (he : IsIdempotentElem e) (x y x' y' : R) :
    (e * x + (1 - e) * y) * (e * x' + (1 - e) * y') = e * (x * x') + (1 - e) * (y * y') := by
  linear_combination (x * x' - x * y' - y * x' + y * y') * he.eq

end CommRing

section Ring

variable {R : Type*} [Ring R] {p : R}

/-- For an idempotent `p`, `2 p - 1` squares to `1`. -/
theorem two_mul_sub_one_mul_self (hp : IsIdempotentElem p) : (2 * p - 1) * (2 * p - 1) = 1 := by
  simp only [two_mul, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, hp.eq]
  abel

section SqZeroPerturbation

variable {e u : R}

private theorem mul_add_mul_and_sandwiches_of_add (he : IsIdempotentElem e) (hu : u * u = 0)
    (heu : IsIdempotentElem (e + u)) :
    e * u + u * e = u ∧ e * u * e = 0 ∧ u * e * u = 0 := by
  have hsum : e * u + u * e = u := by
    apply add_left_cancel (a := e)
    calc
      e + (e * u + u * e) = (e + u) * (e + u) := by
        rw [add_mul, mul_add, mul_add, he.eq, hu, add_zero, add_assoc]
      _ = e + u := heu.eq
  have heue : e * u * e = 0 := by
    apply add_left_cancel (a := e * u)
    calc
      e * u + e * u * e = e * (e * u + u * e) := by
        rw [mul_add, ← mul_assoc, ← mul_assoc, he.eq]
      _ = e * u + 0 := by rw [hsum, add_zero]
  have hueu : u * e * u = 0 := by
    calc
      u * e * u = 0 + u * e * u := (zero_add _).symm
      _ = (e * u + u * e) * u := by rw [add_mul, mul_assoc e u u, hu, mul_zero]
      _ = 0 := by rw [hsum, hu]
  exact ⟨hsum, heue, hueu⟩

/-- If `e` and `e + u` are idempotent and `u * u = 0`, the commutator `e * u - u * e` squares to
zero. -/
theorem mul_sub_mul_mul_self_eq_zero (he : IsIdempotentElem e) (hu : u * u = 0)
    (heu : IsIdempotentElem (e + u)) :
    (e * u - u * e) * (e * u - u * e) = 0 := by
  obtain ⟨_, heue, hueu⟩ := he.mul_add_mul_and_sandwiches_of_add hu heu
  have h1 : e * u * (e * u) = 0 := by rw [← mul_assoc, heue, zero_mul]
  have h2 : u * e * (e * u) = 0 := by rw [mul_assoc, ← mul_assoc e e u, he.eq, ← mul_assoc, hueu]
  have h3 : e * u * (u * e) = 0 := by
    rw [mul_assoc, ← mul_assoc u u e, hu, zero_mul, mul_zero]
  have h4 : u * e * (u * e) = 0 := by rw [mul_assoc, ← mul_assoc e u e, heue, mul_zero]
  rw [sub_mul, mul_sub, mul_sub, h1, h2, h3, h4, sub_zero, sub_zero]

/-- If `e` and `e + u` are idempotent and `u * u = 0`, then `1 + (e * u - u * e)` and
`1 - (e * u - u * e)` multiply to `1`. -/
theorem one_add_mul_sub_mul_mul_one_sub (he : IsIdempotentElem e) (hu : u * u = 0)
    (heu : IsIdempotentElem (e + u)) :
    (1 + (e * u - u * e)) * (1 - (e * u - u * e)) = 1 := by
  rw [add_mul, one_mul, mul_sub, mul_one, he.mul_sub_mul_mul_self_eq_zero hu heu, sub_zero]
  abel

/-- If `e` and `e + u` are idempotent and `u * u = 0`, then `1 - (e * u - u * e)` and
`1 + (e * u - u * e)` multiply to `1`. -/
theorem one_sub_mul_sub_mul_mul_one_add (he : IsIdempotentElem e) (hu : u * u = 0)
    (heu : IsIdempotentElem (e + u)) :
    (1 - (e * u - u * e)) * (1 + (e * u - u * e)) = 1 := by
  rw [sub_mul, one_mul, mul_add, mul_one, he.mul_sub_mul_mul_self_eq_zero hu heu, add_zero]
  abel

/-- **Conjugation of a square-zero perturbation of an idempotent**: in any ring, if `e` and
`e + u` are idempotent and `u * u = 0`, conjugating `e + u` by the unit `1 + (e * u - u * e)`
recovers `e`. -/
theorem conj_one_add_mul_sub_mul (he : IsIdempotentElem e) (hu : u * u = 0)
    (heu : IsIdempotentElem (e + u)) :
    (1 + (e * u - u * e)) * (e + u) * (1 - (e * u - u * e)) = e := by
  obtain ⟨hsum, heue, hueu⟩ := he.mul_add_mul_and_sandwiches_of_add hu heu
  have hpe : (e * u - u * e) * e = -(u * e) := by
    rw [sub_mul, heue, mul_assoc, he.eq, zero_sub]
  have hpu : (e * u - u * e) * u = 0 := by
    rw [sub_mul, mul_assoc, hu, mul_zero, hueu, sub_self]
  have hep : e * (e * u - u * e) = e * u := by
    rw [mul_sub, ← mul_assoc, he.eq, ← mul_assoc, heue, sub_zero]
  have heup : e * u * (e * u - u * e) = 0 := by
    rw [mul_sub, ← mul_assoc, heue, zero_mul, mul_assoc e u (u * e), ← mul_assoc u u e, hu,
      zero_mul, mul_zero, sub_self]
  have hleft : (1 + (e * u - u * e)) * (e + u) = e + e * u := by
    calc
      (1 + (e * u - u * e)) * (e + u) = e + u + (-(u * e) + 0) := by
        rw [add_mul, one_mul, mul_add, hpe, hpu]
      _ = e + (e * u + u * e) + (-(u * e) + 0) := by rw [hsum]
      _ = e + e * u := by abel
  rw [hleft, add_mul, mul_sub e, mul_one, hep, mul_sub (e * u), mul_one, heup, sub_zero]
  abel

end SqZeroPerturbation

end Ring

end IsIdempotentElem

namespace TauCeti

/-- If `u * u = 1`, then `1 + u` squares to `(1 + u) + (1 + u)` (so after dividing by `2`,
`2⁻¹ • (1 + u)` is idempotent). -/
theorem one_add_mul_self_of_mul_self_eq_one {R : Type*} [NonAssocSemiring R] {u : R}
    (hu : u * u = 1) :
    (1 + u) * (1 + u) = (1 + u) + (1 + u) := by
  rw [add_mul, one_mul, mul_add, mul_one, hu, add_comm u 1]

/-- If `u * u = 1` and `u * v + v * u = 0`, then `(1 + u) * (1 + v) * (1 + u)` reduces to
`(1 + u) + (1 + u)`. -/
theorem one_add_mul_one_add_mul_one_add_of_mul_self_eq_one {R : Type*} [Semiring R] {u v : R}
    (hu : u * u = 1) (huv : u * v + v * u = 0) :
    (1 + u) * (1 + v) * (1 + u) = (1 + u) + (1 + u) := by
  have hv : v + u * v * u = 0 :=
    calc
      v + u * v * u = 1 * v + u * (v * u) := by rw [one_mul, mul_assoc]
      _ = u * u * v + u * (v * u) := by rw [hu]
      _ = u * (u * v + v * u) := by rw [mul_assoc, mul_add]
      _ = 0 := by rw [huv, mul_zero]
  calc
    (1 + u) * (1 + v) * (1 + u)
        = ((1 + u) + (u + u * u)) + (u * v + v * u) + (v + u * v * u) := by
          simp only [add_mul, mul_add, one_mul, mul_one]
          ac_rfl
    _ = (1 + u) + (1 + u) := by
          rw [hu, huv, hv, add_zero, add_zero, add_comm u 1]

end TauCeti
