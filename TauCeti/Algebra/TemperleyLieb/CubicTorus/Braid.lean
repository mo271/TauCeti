/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic
public import TauCeti.KnotTheory.TemperleyLieb
-- Private: quotient-group finiteness, linear-map determinants, and roots of unity are used only
-- inside the finiteness proof for the Gaussian braid image.
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The cubic Gaussian braid representation and its finiteness

At Jones's parameter `t = ζ = exp (π i / 3)`, fix the twelfth root of unity
`u = twelfthRootOfUnity = exp (π i / 6)`, so `u ^ 2 = ζ`, `u ^ 3 = i`,
`u ^ 4 = ω = exp (2 π i / 3)`, `u ^ 6 = -1`, `u ^ 12 = 1`, and `u + u⁻¹ = √3`. Inside the
inversion-fixed subalgebra `cubicFixed N` of `CubicTorus N`, the **Gaussian braid generators** are

  `g_j = u • ((1 + u ^ 2) • p_j - 1) = i • p_j - u • (1 - p_j)`
      `= -(√3)⁻¹ • (1 + ω ^ 2 • (U_j + U_j ^ 2))`
      `= -(√3)⁻¹ • ∑_{r ∈ ZMod 3} ω ^ (-r ^ 2) • U_j ^ r`.

* **Algebraic and unitary properties**: each `g_j` lies in `cubicFixed N`, is unitary with respect
  to `cubicAdjoint N` (`g_j† * g_j = g_j * g_j† = 1`), has eigenvalues `i` on `p_j` and `-u` on
  `1 - p_j`, satisfies `g_j ^ 3 = (-i) • 1` and `g_j ^ 12 = 1`, commutes with `g_k` at distance at
  least two, and obeys the braid relation `g_i * g_j * g_i = g_j * g_i * g_j` when `|i - j| = 1`.
  Consequently `σ_j ↦ g_j` defines a group homomorphism
  `gaussianBraidHom N : BraidGroup (N + 1) →* (cubicFixed N)ˣ`.
* **Kauffman-bracket comparison**: for every unit `a : ℂˣ` satisfying `a ^ 2 = -u⁻¹` (for instance
  `a = exp (5 π i / 12)`), the Jones loop value is `jonesDelta a = √3`, and `cubicFixedHom (N + 1)`
  sends the Kauffman-bracket crossing `a • 1 + a⁻¹ • e j` to `(-a / u) • g_j`.
* **Heisenberg subgroup and conjugation action**: the finite Heisenberg group
  `heisenbergSubgroup N = {ω ^ c • W(a) : c ∈ ZMod 3, a ∈ (ZMod 3) ^ N} ≤ (CubicTorus N)ˣ` has
  order `3 ^ (N + 1)`. Conjugation by `g_j` maps `W(a)` according to `B(e_j, a) ∈ ZMod 3`, fixing
  `U_j` and distant `U_k`, sending `U_{j + 1} ↦ ω • (U_{j + 1} * U_j ^ 2)` and
  `U_{j - 1} ↦ ω • (U_{j - 1} * U_j)`. Thus the subgroup `H = Subgroup.closure (Set.range g)` acts
  by conjugation on the finite group `heisenbergSubgroup N`.
* **Finiteness of the Gaussian braid image**: any element `z` in the kernel of the conjugation
  action commutes with every Weyl basis vector `W(a)`, so its Weyl support lies in the radical of
  `chainForm N`. For even `N`, the radical is trivial, so `z = c • 1`; taking the determinant of
  left multiplication on `CubicTorus N` (whose generators satisfy `g_j ^ 12 = 1`) forces
  `c ^ (3 ^ N * 12) = 1`. For odd `N`, the radical is spanned by `cubicRadicalVec N`, so `z` is a
  linear combination of `1`, `W(ρ)`, `W(ρ⁻¹)` and acts as a scalar `λ_r` on each of the three
  nonzero central-idempotent blocks `P_r (CubicTorus N)` (`r ∈ ZMod 3`); blockwise determinants
  force each `λ_r` to be a root of unity of bounded order. Hence both the kernel and the quotient
  `H ⧸ ker` are finite, proving `finite_gaussianBraid_closure` and `finite_range_gaussianBraidHom`.

## Main definitions

* `TauCeti.TemperleyLieb.twelfthRootOfUnity`: `u = exp (π i / 6)`.
* `TauCeti.TemperleyLieb.gaussianBraidGenerator`: `g_j = u • ((1 + u ^ 2) • p_j - 1)`.
* `TauCeti.TemperleyLieb.gaussianBraidUnit` and `TauCeti.TemperleyLieb.gaussianBraidFixedUnit`:
  the units `g_j` in `(CubicTorus N)ˣ` and `(cubicFixed N)ˣ`.
* `TauCeti.TemperleyLieb.gaussianBraidHom`: the braid-group representation
  `BraidGroup (N + 1) →* (cubicFixed N)ˣ`.
* `TauCeti.TemperleyLieb.weylUnit` and `TauCeti.TemperleyLieb.heisenbergSubgroup`: the Weyl
  basis units and the finite Heisenberg subgroup `{ω ^ c • W(a)}` of `(CubicTorus N)ˣ`.

## Main results

* `TauCeti.TemperleyLieb.gaussianBraidGenerator_eq_proj`,
  `TauCeti.TemperleyLieb.gaussianBraidGenerator_eq_site`, and
  `TauCeti.TemperleyLieb.gaussianBraidGenerator_eq_gaussSum`: equivalent projection, site-unitary,
  and Gauss-sum formulas for `g_j`.
* `TauCeti.TemperleyLieb.gaussianBraidGenerator_pow_three` and
  `TauCeti.TemperleyLieb.gaussianBraidGenerator_pow_twelve`: `g_j ^ 3 = (-i) • 1` and
  `g_j ^ 12 = 1`.
* `TauCeti.TemperleyLieb.commute_gaussianBraidGenerator` and
  `TauCeti.TemperleyLieb.gaussianBraidGenerator_braid`: distant commutation and braid relations.
* `TauCeti.TemperleyLieb.jonesDelta_eq_sqrt_three_of_sq_eq` and
  `TauCeti.TemperleyLieb.cubicFixedHom_crossing_eq_gaussianBraidGenerator`: Kauffman-bracket
  comparison at `a ^ 2 = -u⁻¹`.
* `TauCeti.TemperleyLieb.natCard_heisenbergSubgroup`:
  `Nat.card (heisenbergSubgroup N) = 3 ^ (N + 1)`.
* `TauCeti.TemperleyLieb.gaussianBraidGenerator_mul_cubicSite_mul_adjoint_self`,
  `TauCeti.TemperleyLieb.gaussianBraidGenerator_mul_cubicSite_mul_adjoint_of_succ`,
  `TauCeti.TemperleyLieb.gaussianBraidGenerator_mul_cubicSite_mul_adjoint_of_pred`, and
  `TauCeti.TemperleyLieb.gaussianBraidGenerator_mul_cubicSite_mul_adjoint_of_far`: explicit
  conjugation action on site unitaries.
* `TauCeti.TemperleyLieb.finite_subgroup_closure_range_gaussianBraidUnit`,
  `TauCeti.TemperleyLieb.finite_gaussianBraid_closure`, and
  `TauCeti.TemperleyLieb.finite_range_gaussianBraidHom`: finiteness of the Gaussian braid image.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111, p. 107.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*, Ann. of
  Math. 126 (1987), 335–388, §11.
* C. Galindo and E. C. Rowell, *Braid representations from unitary braided vector spaces*,
  J. Math. Phys. 55 (2014), 061702, Proposition 3.6.
* E. C. Rowell and H. Wenzl, *SO(N)_2 braid group representations are Gaussian*, Quantum Topol. 8
  (2017), 1–33, §4.
-/

public section

open scoped ComplexConjugate

namespace TauCeti.TemperleyLieb

private theorem sqrt_three_sq_coe : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
  rw [sq]
  exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)

private theorem sqrt_three_ne_zero_coe : (Real.sqrt 3 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))

/-! ### The twelfth root of unity `u = exp (π i / 6)` -/

/-- `u = exp (π i / 6)`, the twelfth root of unity with `u ^ 2 = exp (π i / 3)`, `u ^ 3 = i`, and
`u ^ 4 = cubeRootOfUnity`. -/
noncomputable def twelfthRootOfUnity : ℂ :=
  Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * Complex.I)

/-- Rectangular form `u = √3 / 2 + (1 / 2) * i`. -/
theorem twelfthRootOfUnity_eq :
    twelfthRootOfUnity = (Real.sqrt 3 / 2 : ℂ) + (1 / 2 : ℂ) * Complex.I := by
  rw [twelfthRootOfUnity, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_six, Real.sin_pi_div_six]
  push_cast
  ring

/-- `twelfthRootOfUnity` is nonzero. -/
@[simp]
theorem twelfthRootOfUnity_ne_zero : twelfthRootOfUnity ≠ 0 :=
  Complex.exp_ne_zero _

/-- `u ^ 2 = 1 / 2 + (√3 / 2) * i`. -/
theorem twelfthRootOfUnity_sq :
    twelfthRootOfUnity ^ 2 = (1 / 2 : ℂ) + (Real.sqrt 3 / 2 : ℂ) * Complex.I := by
  rw [twelfthRootOfUnity_eq]
  linear_combination (1 / 4 : ℂ) * sqrt_three_sq_coe + (1 / 4 : ℂ) * Complex.I_sq

/-- `u ^ 3 = i`. -/
@[simp]
theorem twelfthRootOfUnity_pow_three : twelfthRootOfUnity ^ 3 = Complex.I := by
  rw [show twelfthRootOfUnity ^ 3 = twelfthRootOfUnity ^ 2 * twelfthRootOfUnity by ring,
    twelfthRootOfUnity_sq, twelfthRootOfUnity_eq]
  linear_combination ((Real.sqrt 3 : ℂ) / 4) * Complex.I_sq +
    ((1 / 4 : ℂ) * Complex.I) * sqrt_three_sq_coe

/-- `u ^ 4 = ω = exp (2 π i / 3)`. -/
@[simp]
theorem twelfthRootOfUnity_pow_four :
    twelfthRootOfUnity ^ 4 = (cubeRootOfUnity : ℂ) := by
  rw [show twelfthRootOfUnity ^ 4 = twelfthRootOfUnity ^ 3 * twelfthRootOfUnity by ring,
    twelfthRootOfUnity_pow_three, twelfthRootOfUnity_eq, cubeRootOfUnity_val_eq]
  linear_combination (1 / 2 : ℂ) * Complex.I_sq

/-- `u ^ 6 = -1`. -/
@[simp]
theorem twelfthRootOfUnity_pow_six : twelfthRootOfUnity ^ 6 = -1 := by
  rw [show twelfthRootOfUnity ^ 6 = (twelfthRootOfUnity ^ 3) ^ 2 by ring,
    twelfthRootOfUnity_pow_three, Complex.I_sq]

/-- `u ^ 12 = 1`. -/
@[simp]
theorem twelfthRootOfUnity_pow_twelve : twelfthRootOfUnity ^ 12 = 1 := by
  rw [show twelfthRootOfUnity ^ 12 = (twelfthRootOfUnity ^ 6) ^ 2 by ring,
    twelfthRootOfUnity_pow_six]
  norm_num

/-- Complex conjugation maps `u` to `u⁻¹`. -/
@[simp]
theorem conj_twelfthRootOfUnity : conj twelfthRootOfUnity = twelfthRootOfUnity⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [twelfthRootOfUnity_eq]
  simp only [map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  linear_combination (1 / 4 : ℂ) * sqrt_three_sq_coe - (1 / 4 : ℂ) * Complex.I_sq

/-- Rectangular form of `u⁻¹ = √3 / 2 - (1 / 2) * i`. -/
theorem twelfthRootOfUnity_inv_eq :
    twelfthRootOfUnity⁻¹ = (Real.sqrt 3 / 2 : ℂ) - (1 / 2 : ℂ) * Complex.I := by
  rw [← conj_twelfthRootOfUnity, twelfthRootOfUnity_eq]
  simp only [map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- `u + u⁻¹ = √3`. -/
theorem twelfthRootOfUnity_add_inv :
    twelfthRootOfUnity + twelfthRootOfUnity⁻¹ = (Real.sqrt 3 : ℂ) := by
  rw [twelfthRootOfUnity_inv_eq, twelfthRootOfUnity_eq]
  ring

private theorem cubeRootOfUnity_sq_eq :
    (cubeRootOfUnity : ℂ) ^ 2 = -(1 / 2 : ℂ) - (Real.sqrt 3 / 2 : ℂ) * Complex.I := by
  rw [← cubeRootOfUnity_inv_val, ← conj_cubeRootOfUnity, cubeRootOfUnity_val_eq]
  simp only [map_add, map_mul, map_div₀, map_neg, map_one, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I]
  ring

/-- `u * (1 + u ^ 2) = -√3 * ω ^ 2`. -/
theorem twelfthRootOfUnity_mul_one_add_sq :
    twelfthRootOfUnity * (1 + twelfthRootOfUnity ^ 2) =
      -(Real.sqrt 3 : ℂ) * (cubeRootOfUnity : ℂ) ^ 2 := by
  rw [show twelfthRootOfUnity * (1 + twelfthRootOfUnity ^ 2) =
      twelfthRootOfUnity + twelfthRootOfUnity ^ 3 by ring,
    twelfthRootOfUnity_pow_three, twelfthRootOfUnity_eq, cubeRootOfUnity_sq_eq]
  linear_combination -(1 / 2 * Complex.I) * sqrt_three_sq_coe

/-- Quadratic identity satisfied by `1 + u ^ 2`: `(1 + u ^ 2) ^ 2 - 3 * (1 + u ^ 2) + 3 = 0`. -/
private theorem one_add_twelfthRootOfUnity_sq_poly :
    (1 + twelfthRootOfUnity ^ 2) ^ 2 - 3 * (1 + twelfthRootOfUnity ^ 2) + 3 = 0 := by
  rw [twelfthRootOfUnity_sq]
  linear_combination (1 / 4 * Complex.I ^ 2) * sqrt_three_sq_coe + (3 / 4 : ℂ) * Complex.I_sq

/-! ### Subtraction-rewriting helpers for `CubicTorus N` -/

private theorem cubicTorus_sub_eq_add_neg {N : ℕ} (x y : CubicTorus N) : x - y = x + -y :=
  sub_eq_add_neg x y

private theorem cubicTorus_sub_mul {N : ℕ} (x y z : CubicTorus N) :
    (x - y) * z = x * z - y * z :=
  sub_mul x y z

private theorem cubicTorus_mul_sub {N : ℕ} (x y z : CubicTorus N) :
    x * (y - z) = x * y - x * z :=
  mul_sub x y z

private theorem cubicTorus_smul_sub {N : ℕ} (c : ℂ) (x y : CubicTorus N) :
    c • (x - y) = c • x - c • y :=
  smul_sub c x y

private theorem cubicTorus_sub_self {N : ℕ} (x : CubicTorus N) : x - x = 0 :=
  sub_self x

private theorem cubicTorus_sub_zero {N : ℕ} (x : CubicTorus N) : x - 0 = x :=
  sub_zero x

private theorem cubicTorus_zero_sub {N : ℕ} (x : CubicTorus N) : 0 - x = -x :=
  zero_sub x

private theorem cubicTorus_sub_neg_eq_add {N : ℕ} (x y : CubicTorus N) : x - -y = x + y :=
  sub_neg_eq_add x y

private theorem cubicAdjoint_sub {N : ℕ} (x y : CubicTorus N) :
    cubicAdjoint N (x - y) = cubicAdjoint N x - cubicAdjoint N y :=
  map_sub (cubicAdjoint N) x y

private theorem cubicProjection_mul_one_sub (N : ℕ) (j : Fin N) :
    cubicProjection N j * (1 - cubicProjection N j) = 0 := by
  rw [cubicTorus_mul_sub, mul_one, cubicProjection_mul_self, cubicTorus_sub_self]

private theorem one_sub_cubicProjection_mul (N : ℕ) (j : Fin N) :
    (1 - cubicProjection N j) * cubicProjection N j = 0 := by
  rw [cubicTorus_sub_mul, one_mul, cubicProjection_mul_self, cubicTorus_sub_self]

private theorem one_sub_cubicProjection_mul_self (N : ℕ) (j : Fin N) :
    (1 - cubicProjection N j) * (1 - cubicProjection N j) = 1 - cubicProjection N j := by
  rw [cubicTorus_sub_mul, one_mul, cubicProjection_mul_one_sub, cubicTorus_sub_zero]

/-! ### Gaussian braid generators -/

/-- The `j`-th **Gaussian braid generator**
`g_j = u • ((1 + u ^ 2) • p_j - 1)` in `CubicTorus N`. -/
noncomputable def gaussianBraidGenerator (N : ℕ) (j : Fin N) : CubicTorus N :=
  twelfthRootOfUnity • ((1 + twelfthRootOfUnity ^ 2) • cubicProjection N j - 1)

/-- Unfolding `gaussianBraidGenerator`. -/
theorem gaussianBraidGenerator_def (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j =
      twelfthRootOfUnity • ((1 + twelfthRootOfUnity ^ 2) • cubicProjection N j - 1) :=
  (rfl)

/-- Every Gaussian braid generator lies in the inversion-fixed subalgebra `cubicFixed N`. -/
theorem gaussianBraidGenerator_mem_cubicFixed (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j ∈ cubicFixed N := by
  rw [gaussianBraidGenerator_def, cubicTorus_sub_eq_add_neg, ← neg_one_smul ℂ (1 : CubicTorus N)]
  exact Subalgebra.smul_mem _
    (add_mem (Subalgebra.smul_mem _ (cubicProjection_mem_cubicFixed N j) _)
      (Subalgebra.smul_mem _ (one_mem _) _)) _

/-- Spectral decomposition `g_j = i • p_j - u • (1 - p_j)`. -/
theorem gaussianBraidGenerator_eq_proj (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j =
      Complex.I • cubicProjection N j - twelfthRootOfUnity • (1 - cubicProjection N j) := by
  rw [gaussianBraidGenerator_def, cubicTorus_smul_sub, smul_smul, ← twelfthRootOfUnity_pow_three]
  rw [show twelfthRootOfUnity * (1 + twelfthRootOfUnity ^ 2) =
      twelfthRootOfUnity ^ 3 + twelfthRootOfUnity by ring]
  module

/-- Eigenvalue `i` of `g_j` on the range of `p_j`: `g_j * p_j = i • p_j`. -/
@[simp]
theorem gaussianBraidGenerator_mul_proj (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j * cubicProjection N j = Complex.I • cubicProjection N j := by
  rw [gaussianBraidGenerator_eq_proj, cubicTorus_sub_mul, smul_mul_assoc, smul_mul_assoc,
    one_sub_cubicProjection_mul, cubicProjection_mul_self, smul_zero, cubicTorus_sub_zero]

/-- Eigenvalue `-u` of `g_j` on `1 - p_j`: `g_j * (1 - p_j) = (-u) • (1 - p_j)`. -/
@[simp]
theorem gaussianBraidGenerator_mul_one_sub_proj (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j * (1 - cubicProjection N j) =
      (-twelfthRootOfUnity) • (1 - cubicProjection N j) := by
  rw [gaussianBraidGenerator_eq_proj, cubicTorus_sub_mul, smul_mul_assoc, smul_mul_assoc,
    cubicProjection_mul_one_sub, smul_zero, one_sub_cubicProjection_mul_self,
    cubicTorus_zero_sub]
  exact (neg_smul twelfthRootOfUnity (1 - cubicProjection N j)).symm

/-- Site-unitary form `g_j = -(√3)⁻¹ • (1 + ω ^ 2 • (U_j + U_j ^ 2))`. -/
theorem gaussianBraidGenerator_eq_site (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j =
      -(Real.sqrt 3 : ℂ)⁻¹ •
        (1 + (cubeRootOfUnity : ℂ) ^ 2 • (cubicSite N j + cubicSite N j ^ 2)) := by
  have hc1 : twelfthRootOfUnity * (1 + twelfthRootOfUnity ^ 2) * (3 : ℂ)⁻¹ =
      -(Real.sqrt 3 : ℂ)⁻¹ * (cubeRootOfUnity : ℂ) ^ 2 := by
    rw [twelfthRootOfUnity_mul_one_add_sq, ← sqrt_three_sq_coe, sq]
    field_simp [sqrt_three_ne_zero_coe]
  have hc0 : -(Real.sqrt 3 : ℂ)⁻¹ * (cubeRootOfUnity : ℂ) ^ 2 - twelfthRootOfUnity =
      -(Real.sqrt 3 : ℂ)⁻¹ := by
    field_simp [sqrt_three_ne_zero_coe]
    rw [cubeRootOfUnity_sq_eq, twelfthRootOfUnity_eq]
    linear_combination -(1 / 2 : ℂ) * sqrt_three_sq_coe
  rw [gaussianBraidGenerator_def, cubicProjection_def, cubicTorus_smul_sub, smul_smul, smul_smul,
    show twelfthRootOfUnity * (1 + twelfthRootOfUnity ^ 2) * (3 : ℂ)⁻¹ =
      -(Real.sqrt 3 : ℂ)⁻¹ * (cubeRootOfUnity : ℂ) ^ 2 from hc1]
  have hdecomp : (-(Real.sqrt 3 : ℂ)⁻¹ * (cubeRootOfUnity : ℂ) ^ 2) •
        (1 + cubicSite N j + cubicSite N j ^ 2) - twelfthRootOfUnity • (1 : CubicTorus N) =
      (-(Real.sqrt 3 : ℂ)⁻¹ * (cubeRootOfUnity : ℂ) ^ 2 - twelfthRootOfUnity) •
          (1 : CubicTorus N) +
        (-(Real.sqrt 3 : ℂ)⁻¹ * (cubeRootOfUnity : ℂ) ^ 2) •
          (cubicSite N j + cubicSite N j ^ 2) := by
    module
  rw [hdecomp, hc0]
  module

/-- Gauss-sum form `g_j = -(√3)⁻¹ • ∑ r : ZMod 3, ω ^ (-r ^ 2) • U_j ^ r.val`. -/
theorem gaussianBraidGenerator_eq_gaussSum (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j =
      -(Real.sqrt 3 : ℂ)⁻¹ •
        ∑ r : ZMod 3, (cubeRootPow (-(r ^ 2)) : ℂ) • cubicSite N j ^ r.val := by
  rw [gaussianBraidGenerator_eq_site]
  congr 1
  rw [show (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have h0 : -((0 : ZMod 3) ^ 2) = 0 := by decide
  have h1 : -((1 : ZMod 3) ^ 2) = 2 := by decide
  have h2 : -((2 : ZMod 3) ^ 2) = 2 := by decide
  rw [h0, h1, h2, cubeRootPow_zero, cubeRootPow_two, cubeRootOfUnity_inv_val]
  simp only [Units.val_one, ZMod.val_zero, pow_zero, one_smul, ZMod.val_one, pow_one,
    show (2 : ZMod 3).val = 2 by decide]
  module

/-- Adjoint of `g_j` in spectral form: `g_j† = (-i) • p_j - u⁻¹ • (1 - p_j)`. -/
theorem cubicAdjoint_gaussianBraidGenerator_eq_proj (N : ℕ) (j : Fin N) :
    cubicAdjoint N (gaussianBraidGenerator N j) =
      (-Complex.I) • cubicProjection N j -
        twelfthRootOfUnity⁻¹ • (1 - cubicProjection N j) := by
  rw [gaussianBraidGenerator_eq_proj, cubicAdjoint_sub, map_smulₛₗ, map_smulₛₗ, cubicAdjoint_sub,
    cubicAdjoint_one, cubicAdjoint_cubicProjection, Complex.conj_I, conj_twelfthRootOfUnity]

/-- Adjoint of `g_j` in site-unitary form: `g_j† = -(√3)⁻¹ • (1 + ω • (U_j + U_j ^ 2))`. -/
theorem cubicAdjoint_gaussianBraidGenerator_eq_site (N : ℕ) (j : Fin N) :
    cubicAdjoint N (gaussianBraidGenerator N j) =
      -(Real.sqrt 3 : ℂ)⁻¹ •
        (1 + (cubeRootOfUnity : ℂ) • (cubicSite N j + cubicSite N j ^ 2)) := by
  have hconj : conj ((cubeRootOfUnity : ℂ) ^ 2) = (cubeRootOfUnity : ℂ) := by
    rw [← cubeRootOfUnity_inv_val, ← conj_cubeRootOfUnity]
    simp
  rw [gaussianBraidGenerator_eq_site, map_smulₛₗ, map_add, cubicAdjoint_one, map_smulₛₗ, map_add,
    cubicAdjoint_cubicSite, hconj, sq (cubicSite N j), cubicAdjoint_mul, cubicAdjoint_cubicSite,
    cubicSite_sq_mul_sq]
  simp only [map_neg, map_inv₀, Complex.conj_ofReal]
  congr 2
  rw [add_comm]

/-- Left unitarity of `g_j`: `g_j† * g_j = 1`. -/
@[simp]
theorem cubicAdjoint_gaussianBraidGenerator_mul_self (N : ℕ) (j : Fin N) :
    cubicAdjoint N (gaussianBraidGenerator N j) * gaussianBraidGenerator N j = 1 := by
  rw [cubicAdjoint_gaussianBraidGenerator_eq_proj, gaussianBraidGenerator_eq_proj,
    cubicTorus_sub_mul, cubicTorus_mul_sub, cubicTorus_mul_sub, smul_mul_smul_comm,
    smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm, cubicProjection_mul_self,
    cubicProjection_mul_one_sub, one_sub_cubicProjection_mul, one_sub_cubicProjection_mul_self,
    smul_zero, smul_zero, cubicTorus_sub_zero, cubicTorus_zero_sub, cubicTorus_sub_neg_eq_add,
    show (-Complex.I) * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg],
    inv_mul_cancel₀ twelfthRootOfUnity_ne_zero, one_smul, one_smul]
  abel

/-- Right unitarity of `g_j`: `g_j * g_j† = 1`. -/
@[simp]
theorem mul_cubicAdjoint_gaussianBraidGenerator_self (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j * cubicAdjoint N (gaussianBraidGenerator N j) = 1 := by
  rw [cubicAdjoint_gaussianBraidGenerator_eq_proj, gaussianBraidGenerator_eq_proj,
    cubicTorus_sub_mul, cubicTorus_mul_sub, cubicTorus_mul_sub, smul_mul_smul_comm,
    smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm, cubicProjection_mul_self,
    cubicProjection_mul_one_sub, one_sub_cubicProjection_mul, one_sub_cubicProjection_mul_self,
    smul_zero, smul_zero, cubicTorus_sub_zero, cubicTorus_zero_sub, cubicTorus_sub_neg_eq_add,
    show Complex.I * (-Complex.I) = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg],
    mul_inv_cancel₀ twelfthRootOfUnity_ne_zero, one_smul, one_smul]
  abel

/-- `g_j ^ 3 = (-i) • 1`. -/
@[simp]
theorem gaussianBraidGenerator_pow_three (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j ^ 3 = (-Complex.I) • (1 : CubicTorus N) := by
  have hpow (k : ℕ) :
      gaussianBraidGenerator N j ^ k =
        (Complex.I ^ k) • cubicProjection N j +
          ((-twelfthRootOfUnity) ^ k) • (1 - cubicProjection N j) := by
    induction k with
    | zero =>
      simp only [pow_zero, one_smul]
      abel
    | succ k ih =>
      rw [pow_succ', ih, mul_add, mul_smul_comm, mul_smul_comm, gaussianBraidGenerator_mul_proj,
        gaussianBraidGenerator_mul_one_sub_proj, smul_smul, smul_smul, pow_succ, pow_succ]
  rw [hpow 3]
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]
    ring
  have hu3 : (-twelfthRootOfUnity) ^ 3 = -Complex.I := by
    rw [neg_pow, show (-1 : ℂ) ^ 3 = -1 by norm_num, twelfthRootOfUnity_pow_three]
    ring
  rw [hI3, hu3, ← smul_add]
  congr 1
  abel

/-- `g_j ^ 12 = 1`. -/
@[simp]
theorem gaussianBraidGenerator_pow_twelve (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j ^ 12 = 1 := by
  calc
    gaussianBraidGenerator N j ^ 12
        = (gaussianBraidGenerator N j ^ 3) ^ 4 := by rw [← pow_mul]
    _ = ((-Complex.I) • (1 : CubicTorus N)) ^ 4 := by rw [gaussianBraidGenerator_pow_three]
    _ = ((-Complex.I) ^ 4) • (1 : CubicTorus N) := by rw [smul_pow, one_pow]
    _ = 1 := by
          have h : (-Complex.I) ^ 4 = 1 := by
            rw [show (-Complex.I) ^ 4 = (Complex.I ^ 2) ^ 2 by ring, Complex.I_sq]
            norm_num
          rw [h, one_smul]

/-- Distant Gaussian braid generators commute (`|i - j| ≥ 2`). -/
theorem commute_gaussianBraidGenerator {N : ℕ} {i j : Fin N}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (gaussianBraidGenerator N i) (gaussianBraidGenerator N j) := by
  unfold Commute SemiconjBy
  rw [gaussianBraidGenerator_def, gaussianBraidGenerator_def, smul_mul_smul_comm,
    smul_mul_smul_comm]
  congr 1
  have hc : cubicProjection N i * cubicProjection N j =
      cubicProjection N j * cubicProjection N i := (commute_cubicProjection h).eq
  simp only [cubicTorus_sub_mul, cubicTorus_mul_sub, one_mul, mul_one, smul_mul_smul_comm, hc]
  abel

/-- Adjacent Gaussian braid generators satisfy the braid relation
`g_i * g_j * g_i = g_j * g_i * g_j`. -/
theorem gaussianBraidGenerator_braid {N : ℕ} {i j : Fin N}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    gaussianBraidGenerator N i * gaussianBraidGenerator N j * gaussianBraidGenerator N i =
      gaussianBraidGenerator N j * gaussianBraidGenerator N i * gaussianBraidGenerator N j := by
  set α : ℂ := 1 + twelfthRootOfUnity ^ 2
  have hpoly : α ^ 3 * (3 : ℂ)⁻¹ - α ^ 2 + α = 0 := by
    linear_combination (α * (3 : ℂ)⁻¹) * one_add_twelfthRootOfUnity_sq_poly
  -- Expand `(α • p_a - 1)(α • p_b - 1)(α • p_a - 1)` into an expression symmetric in `p_a`, `p_b`.
  have hexp (a b : Fin N) (hab : (a : ℕ) + 1 = b ∨ (b : ℕ) + 1 = a) :
      (α • cubicProjection N a - 1) * (α • cubicProjection N b - 1) *
          (α • cubicProjection N a - 1) =
        α • (cubicProjection N a + cubicProjection N b) -
          (α ^ 2) • (cubicProjection N a * cubicProjection N b +
            cubicProjection N b * cubicProjection N a) - 1 := by
    have hmul :
        (α • cubicProjection N a - 1) * (α • cubicProjection N b - 1) *
            (α • cubicProjection N a - 1) =
          (α ^ 3) • (cubicProjection N a * cubicProjection N b * cubicProjection N a) -
            (α ^ 2) • (cubicProjection N a * cubicProjection N b) -
            (α ^ 2) • (cubicProjection N b * cubicProjection N a) -
            (α ^ 2) • (cubicProjection N a * cubicProjection N a) +
            α • cubicProjection N a + α • cubicProjection N b + α • cubicProjection N a - 1 := by
      simp only [cubicTorus_sub_mul, cubicTorus_mul_sub, one_mul, mul_one, smul_mul_assoc,
        mul_smul_comm]
      module
    rw [hmul, cubicProjection_mul_cubicProjection_mul_cubicProjection hab,
      cubicProjection_mul_self, smul_smul]
    calc
      (α ^ 3 * (3 : ℂ)⁻¹) • cubicProjection N a -
          (α ^ 2) • (cubicProjection N a * cubicProjection N b) -
          (α ^ 2) • (cubicProjection N b * cubicProjection N a) -
          (α ^ 2) • cubicProjection N a +
          α • cubicProjection N a + α • cubicProjection N b + α • cubicProjection N a - 1
          = (α ^ 3 * (3 : ℂ)⁻¹ - α ^ 2 + α) • cubicProjection N a +
            (α • (cubicProjection N a + cubicProjection N b) -
              (α ^ 2) • (cubicProjection N a * cubicProjection N b +
                cubicProjection N b * cubicProjection N a) - 1) := by module
      _ = α • (cubicProjection N a + cubicProjection N b) -
            (α ^ 2) • (cubicProjection N a * cubicProjection N b +
              cubicProjection N b * cubicProjection N a) - 1 := by
            rw [hpoly, zero_smul, zero_add]
  rw [gaussianBraidGenerator_def, gaussianBraidGenerator_def]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  rw [hexp i j h, hexp j i h.symm, add_comm (cubicProjection N j) (cubicProjection N i),
    add_comm (cubicProjection N j * cubicProjection N i)
      (cubicProjection N i * cubicProjection N j)]

/-! ### Units, the braid group representation, and Kauffman-bracket comparison -/

/-- The `j`-th Gaussian braid generator as a unit of `CubicTorus N`. -/
noncomputable def gaussianBraidUnit (N : ℕ) (j : Fin N) : (CubicTorus N)ˣ where
  val := gaussianBraidGenerator N j
  inv := cubicAdjoint N (gaussianBraidGenerator N j)
  val_inv := mul_cubicAdjoint_gaussianBraidGenerator_self N j
  inv_val := cubicAdjoint_gaussianBraidGenerator_mul_self N j

/-- Coercion of `gaussianBraidUnit N j` to `CubicTorus N`. -/
@[simp]
theorem coe_gaussianBraidUnit (N : ℕ) (j : Fin N) :
    (gaussianBraidUnit N j : CubicTorus N) = gaussianBraidGenerator N j :=
  (rfl)

/-- Coercion of `(gaussianBraidUnit N j)⁻¹` to `CubicTorus N`. -/
@[simp]
theorem coe_gaussianBraidUnit_inv (N : ℕ) (j : Fin N) :
    (((gaussianBraidUnit N j)⁻¹ : (CubicTorus N)ˣ) : CubicTorus N) =
      cubicAdjoint N (gaussianBraidGenerator N j) :=
  (rfl)

/-- `(gaussianBraidUnit N j) ^ 12 = 1`. -/
@[simp]
theorem gaussianBraidUnit_pow_twelve (N : ℕ) (j : Fin N) :
    gaussianBraidUnit N j ^ 12 = 1 :=
  Units.ext (gaussianBraidGenerator_pow_twelve N j)

/-- The `j`-th Gaussian braid generator as a unit of `cubicFixed N`. -/
noncomputable def gaussianBraidFixedUnit (N : ℕ) (j : Fin N) : (cubicFixed N)ˣ where
  val := ⟨gaussianBraidGenerator N j, gaussianBraidGenerator_mem_cubicFixed N j⟩
  inv := ⟨cubicAdjoint N (gaussianBraidGenerator N j),
    cubicAdjoint_mem_cubicFixed N (gaussianBraidGenerator_mem_cubicFixed N j)⟩
  val_inv := Subtype.ext (mul_cubicAdjoint_gaussianBraidGenerator_self N j)
  inv_val := Subtype.ext (cubicAdjoint_gaussianBraidGenerator_mul_self N j)

/-- Coercion of `gaussianBraidFixedUnit N j` to `CubicTorus N`. -/
@[simp]
theorem coe_gaussianBraidFixedUnit (N : ℕ) (j : Fin N) :
    ((gaussianBraidFixedUnit N j : cubicFixed N) : CubicTorus N) =
      gaussianBraidGenerator N j :=
  (rfl)

/-- Coercion of `(gaussianBraidFixedUnit N j)⁻¹` to `CubicTorus N`. -/
@[simp]
theorem coe_gaussianBraidFixedUnit_inv (N : ℕ) (j : Fin N) :
    ((((gaussianBraidFixedUnit N j)⁻¹ : (cubicFixed N)ˣ) : cubicFixed N) : CubicTorus N) =
      cubicAdjoint N (gaussianBraidGenerator N j) :=
  (rfl)

/-- The Gaussian representation `BraidGroup (N + 1) →* (cubicFixed N)ˣ` sending each elementary
braid `σ j` to `gaussianBraidFixedUnit N j`. -/
noncomputable def gaussianBraidHom (N : ℕ) : BraidGroup (N + 1) →* (cubicFixed N)ˣ :=
  BraidGroup.lift (gaussianBraidFixedUnit N)
    (fun h ↦ Units.ext <| Subtype.ext <| (commute_gaussianBraidGenerator h).eq)
    (fun h ↦ Units.ext <| Subtype.ext <| gaussianBraidGenerator_braid h)

/-- `gaussianBraidHom N` sends the elementary braid `σ j` to `gaussianBraidFixedUnit N j`. -/
@[simp]
theorem gaussianBraidHom_sigma (N : ℕ) (j : Fin N) :
    gaussianBraidHom N (BraidGroup.sigma j) = gaussianBraidFixedUnit N j :=
  BraidGroup.lift_sigma (n := N + 1) _ _ _ j

/-- Existence of a Kauffman parameter `a : ℂˣ` with `a ^ 2 = -u⁻¹` (witnessed by
`exp (5 π i / 12)`). -/
theorem exists_unit_sq_eq_neg_twelfthRootOfUnity_inv :
    ∃ a : ℂˣ, (a : ℂ) ^ 2 = -twelfthRootOfUnity⁻¹ := by
  refine ⟨Units.mk0 (Complex.exp (((5 * Real.pi / 12 : ℝ) : ℂ) * Complex.I))
    (Complex.exp_ne_zero _), ?_⟩
  simp only [Units.val_mk0, ← Complex.exp_nat_mul, Nat.cast_ofNat]
  rw [twelfthRootOfUnity, ← Complex.exp_neg]
  have harg : (2 : ℂ) * (((5 * Real.pi / 12 : ℝ) : ℂ) * Complex.I) =
      Real.pi * Complex.I + -(((Real.pi / 6 : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- Any unit `a : ℂˣ` with `a ^ 2 = -u⁻¹` gives Jones loop value `jonesDelta a = √3`. -/
theorem jonesDelta_eq_sqrt_three_of_sq_eq {a : ℂˣ}
    (ha : (a : ℂ) ^ 2 = -twelfthRootOfUnity⁻¹) :
    jonesDelta a = (Real.sqrt 3 : ℂ) := by
  have hinv : ((a⁻¹ : ℂˣ) : ℂ) ^ 2 = -twelfthRootOfUnity := by
    have hmul : (a : ℂ) ^ 2 * ((a⁻¹ : ℂˣ) : ℂ) ^ 2 = 1 := by
      rw [← mul_pow, Units.mul_inv, one_pow]
    rw [ha] at hmul
    have := congrArg (fun z ↦ (-twelfthRootOfUnity) * z) hmul
    rw [mul_one, ← mul_assoc, neg_mul_neg, mul_inv_cancel₀ twelfthRootOfUnity_ne_zero,
      one_mul] at this
    exact this
  rw [jonesDelta_def, ha, hinv, ← twelfthRootOfUnity_add_inv]
  ring

/-- **Kauffman-bracket comparison**: for any unit `a : ℂˣ` with `a ^ 2 = -u⁻¹`, `cubicFixedHom`
sends the Kauffman crossing `a • 1 + a⁻¹ • e j` to `(-a / u) • g_j`. -/
theorem cubicFixedHom_crossing_eq_gaussianBraidGenerator {N : ℕ} {a : ℂˣ}
    (ha : (a : ℂ) ^ 2 = -twelfthRootOfUnity⁻¹) (j : Fin N) :
    ((cubicFixedHom (N + 1)
        (crossing (Real.sqrt 3 : ℂ) (a : ℂ) ((a⁻¹ : ℂˣ) : ℂ) j)).1 : CubicTorus N) =
      (-(a : ℂ) / twelfthRootOfUnity) • gaussianBraidGenerator N j := by
  have ha_inv : ((a⁻¹ : ℂˣ) : ℂ) = -twelfthRootOfUnity * (a : ℂ) := by
    have h1 : (a : ℂ) * (-twelfthRootOfUnity * (a : ℂ)) = 1 := by
      calc
        (a : ℂ) * (-twelfthRootOfUnity * (a : ℂ))
            = -twelfthRootOfUnity * (a : ℂ) ^ 2 := by ring
        _ = -twelfthRootOfUnity * (-twelfthRootOfUnity⁻¹) := by rw [ha]
        _ = twelfthRootOfUnity * twelfthRootOfUnity⁻¹ := by ring
        _ = 1 := mul_inv_cancel₀ twelfthRootOfUnity_ne_zero
    calc
      ((a⁻¹ : ℂˣ) : ℂ) = ((a⁻¹ : ℂˣ) : ℂ) * ((a : ℂ) * (-twelfthRootOfUnity * (a : ℂ))) := by
        rw [h1, mul_one]
      _ = (((a⁻¹ : ℂˣ) : ℂ) * (a : ℂ)) * (-twelfthRootOfUnity * (a : ℂ)) := by ring
      _ = -twelfthRootOfUnity * (a : ℂ) := by rw [Units.inv_mul, one_mul]
  have hcoeff : ((a⁻¹ : ℂˣ) : ℂ) * (Real.sqrt 3 : ℂ) =
      -(a : ℂ) * (1 + twelfthRootOfUnity ^ 2) := by
    rw [ha_inv, ← twelfthRootOfUnity_add_inv]
    field_simp [twelfthRootOfUnity_ne_zero]
    ring
  -- Express the coercion `(cubicFixed N).val ∘ cubicFixedHom (N + 1)` as a single `AlgHom` so
  -- `map_add`/`map_smul`/`map_one` fire without `N + 1 - 1` subtype-coercion mismatches.
  let F : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) (N + 1) →ₐ[ℂ] CubicTorus N :=
    (cubicFixed N).val.comp (cubicFixedHom (N + 1))
  change F (crossing (Real.sqrt 3 : ℂ) (a : ℂ) ((a⁻¹ : ℂˣ) : ℂ) j) = _
  rw [crossing_def, map_add, map_smul, map_smul, map_one]
  have he : F (e (Real.sqrt 3 : ℂ) j) = (Real.sqrt 3 : ℂ) • cubicProjection N j :=
    coe_cubicFixedHom_e (N + 1) j
  rw [he, smul_smul, hcoeff, gaussianBraidGenerator_def, smul_smul,
    div_mul_cancel₀ _ twelfthRootOfUnity_ne_zero]
  module

/-! ### The Heisenberg subgroup and conjugation action -/

/-- The Weyl basis element `W(a)` bundled as a unit of `CubicTorus N`. -/
noncomputable def weylUnit (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) : (CubicTorus N)ˣ where
  val := weyl N a
  inv := weyl N a⁻¹
  val_inv := weyl_mul_weyl_inv N a
  inv_val := weyl_inv_mul_weyl N a

/-- Coercion of `weylUnit N a` to `CubicTorus N`. -/
@[simp]
theorem coe_weylUnit (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    (weylUnit N a : CubicTorus N) = weyl N a :=
  (rfl)

/-- Coercion of `(weylUnit N a)⁻¹` to `CubicTorus N`. -/
@[simp]
theorem coe_weylUnit_inv (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    (((weylUnit N a)⁻¹ : (CubicTorus N)ˣ) : CubicTorus N) = weyl N a⁻¹ :=
  (rfl)

/-- A scalar unit `u : ℂˣ` embedded into `(CubicTorus N)ˣ`. -/
private noncomputable def scalarUnit (N : ℕ) (u : ℂˣ) : (CubicTorus N)ˣ :=
  Units.map (algebraMap ℂ (CubicTorus N)).toMonoidHom u

private theorem coe_scalarUnit (N : ℕ) (u : ℂˣ) :
    (scalarUnit N u : CubicTorus N) = (u : ℂ) • (1 : CubicTorus N) := by
  simp [scalarUnit, Algebra.algebraMap_eq_smul_one]

/-- The **Heisenberg subgroup** `H_N = {ω ^ c • W(a) : c ∈ ZMod 3, a ∈ (ZMod 3) ^ N}` of
`(CubicTorus N)ˣ`, of order `3 ^ (N + 1)`. -/
noncomputable def heisenbergSubgroup (N : ℕ) : Subgroup (CubicTorus N)ˣ where
  carrier := {x | ∃ (c : ZMod 3) (a : Multiplicative (Fin N → ZMod 3)),
    (x : CubicTorus N) = (cubeRootPow c : ℂ) • weyl N a}
  one_mem' := ⟨0, 1, by simp⟩
  mul_mem' := by
    rintro x y ⟨c, a, hx⟩ ⟨d, b, hy⟩
    refine ⟨c + d + 2 * chainForm N a.toAdd b.toAdd, a * b, ?_⟩
    rw [Units.val_mul, hx, hy, smul_mul_smul_comm, weyl_mul_weyl, smul_smul, cubicFactor_def,
      ← Units.val_mul, ← Units.val_mul, ← cubeRootPow_add, ← cubeRootPow_add]
  inv_mem' := by
    rintro x ⟨c, a, hx⟩
    refine ⟨-c, a⁻¹, ?_⟩
    have hmul : (x : CubicTorus N) * ((cubeRootPow (-c) : ℂ) • weyl N a⁻¹) = 1 := by
      rw [hx, smul_mul_smul_comm, weyl_mul_weyl_inv, ← Units.val_mul, ← cubeRootPow_add,
        add_neg_cancel, cubeRootPow_zero, Units.val_one, one_smul]
    calc
      ((x⁻¹ : (CubicTorus N)ˣ) : CubicTorus N)
          = ((x⁻¹ : (CubicTorus N)ˣ) : CubicTorus N) *
              ((x : CubicTorus N) * ((cubeRootPow (-c) : ℂ) • weyl N a⁻¹)) := by
            rw [hmul, mul_one]
      _ = (((x⁻¹ : (CubicTorus N)ˣ) : CubicTorus N) * (x : CubicTorus N)) *
            ((cubeRootPow (-c) : ℂ) • weyl N a⁻¹) := by rw [mul_assoc]
      _ = (cubeRootPow (-c) : ℂ) • weyl N a⁻¹ := by rw [← Units.val_mul, inv_mul_cancel,
            Units.val_one, one_mul]

/-- Every Weyl unit `weylUnit N a` belongs to `heisenbergSubgroup N`. -/
theorem weylUnit_mem_heisenbergSubgroup (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    weylUnit N a ∈ heisenbergSubgroup N :=
  ⟨0, a, by simp⟩

/-- Bijection between `ZMod 3 × Multiplicative (Fin N → ZMod 3)` and `heisenbergSubgroup N`. -/
private noncomputable def heisenbergEquiv (N : ℕ) :
    ZMod 3 × Multiplicative (Fin N → ZMod 3) ≃ heisenbergSubgroup N :=
  Equiv.ofBijective
    (fun p ↦ ⟨scalarUnit N (cubeRootPow p.1) * weylUnit N p.2,
      ⟨p.1, p.2, by rw [Units.val_mul, coe_scalarUnit, coe_weylUnit, smul_mul_assoc, one_mul]⟩⟩)
    ⟨by
      rintro ⟨c₁, a₁⟩ ⟨c₂, a₂⟩ h
      have hval : (cubeRootPow c₁ : ℂ) • weyl N a₁ = (cubeRootPow c₂ : ℂ) • weyl N a₂ := by
        simpa [coe_scalarUnit, smul_mul_assoc, one_mul] using
          congrArg (fun u : heisenbergSubgroup N ↦ (u.1 : CubicTorus N)) h
      have hrepr := congrArg (fun z ↦ (weylBasis N).repr z a₁) hval
      simp only [map_smul, ← weylBasis_apply, Module.Basis.repr_self, Finsupp.smul_apply,
        smul_eq_mul, Finsupp.single_eq_same, mul_one, Finsupp.single_apply] at hrepr
      have ha : a₂ = a₁ := by
        by_contra hne
        rw [ite_eq_right hne, mul_zero] at hrepr
        exact (cubeRootPow c₁).ne_zero hrepr
      subst ha
      simp only [ite_true, mul_one] at hrepr
      have hc : c₁ = c₂ := cubeRootPow_injective (Units.ext hrepr)
      rw [hc],
     by
      rintro ⟨x, c, a, hx⟩
      refine ⟨(c, a), Subtype.ext (Units.ext ?_)⟩
      simp [coe_scalarUnit, one_mul, hx]⟩

/-- The Heisenberg subgroup `heisenbergSubgroup N` is finite. -/
instance finite_heisenbergSubgroup (N : ℕ) : Finite (heisenbergSubgroup N) :=
  Finite.of_equiv _ (heisenbergEquiv N)

/-- The Heisenberg subgroup `heisenbergSubgroup N` has order `3 ^ (N + 1)`. -/
@[simp]
theorem natCard_heisenbergSubgroup (N : ℕ) :
    Nat.card (heisenbergSubgroup N) = 3 ^ (N + 1) := by
  rw [← Nat.card_congr (heisenbergEquiv N), Nat.card_eq_fintype_card, Fintype.card_prod]
  simp [Fintype.card_pi, pow_succ']

/-- Unified conjugation formula for `g_j * x * g_j†` when `U_j * x = ω ^ t • (x * U_j)`. -/
private theorem gaussianBraidGenerator_mul_mul_adjoint {N : ℕ} (j : Fin N) {x : CubicTorus N}
    {t : ZMod 3} (hcomm : cubicSite N j * x = (cubeRootPow t : ℂ) • (x * cubicSite N j)) :
    gaussianBraidGenerator N j * x * cubicAdjoint N (gaussianBraidGenerator N j) =
      if t = 0 then x
      else if t = 1 then (cubeRootOfUnity : ℂ) • (x * cubicSite N j ^ 2)
      else (cubeRootOfUnity : ℂ) • (x * cubicSite N j) := by
  have hcomm2 (ξ : ℂ) (hξ : cubicSite N j * x = ξ • (x * cubicSite N j)) :
      cubicSite N j ^ 2 * x = (ξ ^ 2) • (x * cubicSite N j ^ 2) := by
    calc
      cubicSite N j ^ 2 * x
          = cubicSite N j * (cubicSite N j * x) := by rw [sq, mul_assoc]
      _ = cubicSite N j * (ξ • (x * cubicSite N j)) := by rw [hξ]
      _ = ξ • ((cubicSite N j * x) * cubicSite N j) := by rw [mul_smul_comm, ← mul_assoc]
      _ = (ξ ^ 2) • (x * cubicSite N j ^ 2) := by
            rw [hξ, smul_mul_assoc, smul_smul, ← sq, mul_assoc, ← sq]
  have hω3 : (cubeRootOfUnity : ℂ) ^ 3 = 1 := cubeRootOfUnity_val_pow_three
  have hωp : (1 : ℂ) + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2 = 0 :=
    one_add_cubeRootOfUnity_add_sq
  have hsq3 : (-(Real.sqrt 3 : ℂ)⁻¹) * (-(Real.sqrt 3 : ℂ)⁻¹) = (3 : ℂ)⁻¹ := by
    rw [neg_mul_neg, ← mul_inv, ← sq, sqrt_three_sq_coe]
  have hU2 : cubicSite N j * cubicSite N j = cubicSite N j ^ 2 := (sq _).symm
  have ht : t = 0 ∨ t = 1 ∨ t = 2 := by
    fin_cases t
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  rcases ht with rfl | rfl | rfl
  · rw [ite_eq_left rfl]
    have h0 : cubicSite N j * x = x * cubicSite N j := by simpa using hcomm
    have h02 : cubicSite N j ^ 2 * x = x * cubicSite N j ^ 2 := by
      simpa using hcomm2 1 (by simpa using h0)
    have hgx : gaussianBraidGenerator N j * x = x * gaussianBraidGenerator N j := by
      rw [gaussianBraidGenerator_eq_site, smul_mul_assoc, mul_smul_comm]
      congr 1
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, h0, h02]
    rw [hgx, mul_assoc, mul_cubicAdjoint_gaussianBraidGenerator_self, mul_one]
  · rw [ite_eq_right (by decide), ite_eq_left rfl]
    have h1 : cubicSite N j * x = (cubeRootOfUnity : ℂ) • (x * cubicSite N j) := by
      simpa using hcomm
    have h12 := hcomm2 (cubeRootOfUnity : ℂ) h1
    rw [cubicAdjoint_gaussianBraidGenerator_eq_site, gaussianBraidGenerator_eq_site,
      smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, hsq3]
    have hpass :
        (1 + (cubeRootOfUnity : ℂ) ^ 2 • (cubicSite N j + cubicSite N j ^ 2)) * x =
          x * (1 + cubicSite N j + (cubeRootOfUnity : ℂ) • cubicSite N j ^ 2) := by
      simp only [add_mul, one_mul, smul_add, smul_mul_assoc, h1, h12, smul_smul, mul_add, mul_one,
        mul_smul_comm]
      rw [show (cubeRootOfUnity : ℂ) ^ 2 * (cubeRootOfUnity : ℂ) = 1 by rw [← pow_succ, hω3],
        show (cubeRootOfUnity : ℂ) ^ 2 * (cubeRootOfUnity : ℂ) ^ 2 = (cubeRootOfUnity : ℂ) by
          linear_combination (cubeRootOfUnity : ℂ) * hω3]
      simp only [one_smul, add_assoc]
    have hprod :
        (1 + cubicSite N j + (cubeRootOfUnity : ℂ) • cubicSite N j ^ 2) *
            (1 + (cubeRootOfUnity : ℂ) • (cubicSite N j + cubicSite N j ^ 2)) =
          ((3 : ℂ) * (cubeRootOfUnity : ℂ)) • cubicSite N j ^ 2 := by
      calc
        (1 + cubicSite N j + (cubeRootOfUnity : ℂ) • cubicSite N j ^ 2) *
            (1 + (cubeRootOfUnity : ℂ) • (cubicSite N j + cubicSite N j ^ 2))
            = (1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2) • (1 : CubicTorus N) +
              (1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2) • cubicSite N j +
              ((3 : ℂ) * (cubeRootOfUnity : ℂ)) • cubicSite N j ^ 2 := by
              simp only [add_mul, mul_add, one_mul, mul_one, smul_add, smul_mul_assoc,
                mul_smul_comm, smul_smul, cubicSite_mul_sq, cubicSite_sq_mul,
                cubicSite_sq_mul_sq, hU2]
              module
        _ = ((3 : ℂ) * (cubeRootOfUnity : ℂ)) • cubicSite N j ^ 2 := by
              rw [hωp, zero_smul, zero_smul, zero_add, zero_add]
    rw [hpass, mul_assoc, hprod, mul_smul_comm, smul_smul]
    congr 1
    ring
  · rw [ite_eq_right (by decide), ite_eq_right (by decide)]
    have h2 : cubicSite N j * x = ((cubeRootOfUnity : ℂ) ^ 2) • (x * cubicSite N j) := by
      rw [cubeRootPow_two, cubeRootOfUnity_inv_val] at hcomm
      exact hcomm
    have h22 := hcomm2 ((cubeRootOfUnity : ℂ) ^ 2) h2
    rw [cubicAdjoint_gaussianBraidGenerator_eq_site, gaussianBraidGenerator_eq_site,
      smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, hsq3]
    have hpass :
        (1 + (cubeRootOfUnity : ℂ) ^ 2 • (cubicSite N j + cubicSite N j ^ 2)) * x =
          x * (1 + (cubeRootOfUnity : ℂ) • cubicSite N j + cubicSite N j ^ 2) := by
      simp only [add_mul, one_mul, smul_add, smul_mul_assoc, h2, h22, smul_smul, mul_add, mul_one,
        mul_smul_comm]
      rw [show (cubeRootOfUnity : ℂ) ^ 2 * (cubeRootOfUnity : ℂ) ^ 2 = (cubeRootOfUnity : ℂ) by
            linear_combination (cubeRootOfUnity : ℂ) * hω3,
        show (cubeRootOfUnity : ℂ) ^ 2 * ((cubeRootOfUnity : ℂ) ^ 2) ^ 2 = 1 by
            linear_combination ((cubeRootOfUnity : ℂ) ^ 3 + 1) * hω3]
      simp only [one_smul, add_assoc]
    have hprod :
        (1 + (cubeRootOfUnity : ℂ) • cubicSite N j + cubicSite N j ^ 2) *
            (1 + (cubeRootOfUnity : ℂ) • (cubicSite N j + cubicSite N j ^ 2)) =
          ((3 : ℂ) * (cubeRootOfUnity : ℂ)) • cubicSite N j := by
      calc
        (1 + (cubeRootOfUnity : ℂ) • cubicSite N j + cubicSite N j ^ 2) *
            (1 + (cubeRootOfUnity : ℂ) • (cubicSite N j + cubicSite N j ^ 2))
            = (1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2) • (1 : CubicTorus N) +
              ((3 : ℂ) * (cubeRootOfUnity : ℂ)) • cubicSite N j +
              (1 + (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2) • cubicSite N j ^ 2 := by
              simp only [add_mul, mul_add, one_mul, mul_one, smul_add, smul_mul_assoc,
                mul_smul_comm, smul_smul, cubicSite_mul_sq, cubicSite_sq_mul,
                cubicSite_sq_mul_sq, hU2]
              module
        _ = ((3 : ℂ) * (cubeRootOfUnity : ℂ)) • cubicSite N j := by
              rw [hωp, zero_smul, zero_smul, zero_add, add_zero]
    rw [hpass, mul_assoc, hprod, mul_smul_comm, smul_smul]
    congr 1
    ring

/-- Conjugation by `g_j` fixes `U_j`. -/
@[simp]
theorem gaussianBraidGenerator_mul_cubicSite_mul_adjoint_self (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j * cubicSite N j *
        cubicAdjoint N (gaussianBraidGenerator N j) = cubicSite N j := by
  have hcomm : cubicSite N j * cubicSite N j =
      (cubeRootPow 0 : ℂ) • (cubicSite N j * cubicSite N j) := by simp
  simpa using gaussianBraidGenerator_mul_mul_adjoint j hcomm

/-- Conjugation by `g_j` sends `U_{j + 1}` to `ω • (U_{j + 1} * U_j ^ 2)`. -/
theorem gaussianBraidGenerator_mul_cubicSite_mul_adjoint_of_succ {N : ℕ} {j k : Fin N}
    (h : (j : ℕ) + 1 = k) :
    gaussianBraidGenerator N j * cubicSite N k *
        cubicAdjoint N (gaussianBraidGenerator N j) =
      (cubeRootOfUnity : ℂ) • (cubicSite N k * cubicSite N j ^ 2) := by
  have hcomm : cubicSite N j * cubicSite N k =
      (cubeRootPow 1 : ℂ) • (cubicSite N k * cubicSite N j) := by
    simpa [cubeRootPow_one] using cubicSite_mul_cubicSite_of_succ h
  simpa using gaussianBraidGenerator_mul_mul_adjoint j hcomm

/-- Conjugation by `g_j` sends `U_{j - 1}` to `ω • (U_{j - 1} * U_j)`. -/
theorem gaussianBraidGenerator_mul_cubicSite_mul_adjoint_of_pred {N : ℕ} {j k : Fin N}
    (h : (k : ℕ) + 1 = j) :
    gaussianBraidGenerator N j * cubicSite N k *
        cubicAdjoint N (gaussianBraidGenerator N j) =
      (cubeRootOfUnity : ℂ) • (cubicSite N k * cubicSite N j) := by
  have hcomm : cubicSite N j * cubicSite N k =
      (cubeRootPow 2 : ℂ) • (cubicSite N k * cubicSite N j) := by
    simpa [cubeRootPow_two] using cubicSite_mul_cubicSite_of_pred h
  have hne20 : (2 : ZMod 3) ≠ 0 := by decide
  have hne21 : (2 : ZMod 3) ≠ 1 := by decide
  simpa [hne20, hne21] using gaussianBraidGenerator_mul_mul_adjoint j hcomm

/-- Conjugation by `g_j` fixes `U_k` when `|j - k| ≥ 2`. -/
theorem gaussianBraidGenerator_mul_cubicSite_mul_adjoint_of_far {N : ℕ} {j k : Fin N}
    (h : (j : ℕ) + 2 ≤ k ∨ (k : ℕ) + 2 ≤ j) :
    gaussianBraidGenerator N j * cubicSite N k *
        cubicAdjoint N (gaussianBraidGenerator N j) = cubicSite N k := by
  have hcomm : cubicSite N j * cubicSite N k =
      (cubeRootPow 0 : ℂ) • (cubicSite N k * cubicSite N j) := by
    simpa using (commute_cubicSite h).eq
  simpa using gaussianBraidGenerator_mul_mul_adjoint j hcomm

/-- Conjugation by `gaussianBraidUnit N j` preserves `heisenbergSubgroup N`. -/
theorem gaussianBraidUnit_conj_mem_heisenbergSubgroup {N : ℕ} (j : Fin N)
    {h : (CubicTorus N)ˣ} (hh : h ∈ heisenbergSubgroup N) :
    gaussianBraidUnit N j * h * (gaussianBraidUnit N j)⁻¹ ∈ heisenbergSubgroup N := by
  rcases hh with ⟨c, a, ha⟩
  set ej : Multiplicative (Fin N → ZMod 3) := Multiplicative.ofAdd (Pi.single j 1)
  have hcomm : cubicSite N j * weyl N a =
      (cubeRootPow (chainForm N (Pi.single j 1) a.toAdd) : ℂ) • (weyl N a * cubicSite N j) := by
    rw [cubicSite_def, weyl_mul_weyl_comm, toAdd_ofAdd]
  have hconj :
      ((gaussianBraidUnit N j * h * (gaussianBraidUnit N j)⁻¹ : (CubicTorus N)ˣ) : CubicTorus N) =
        (cubeRootPow c : ℂ) •
          (gaussianBraidGenerator N j * weyl N a *
            cubicAdjoint N (gaussianBraidGenerator N j)) := by
    simp only [Units.val_mul, coe_gaussianBraidUnit, coe_gaussianBraidUnit_inv, ha,
      mul_smul_comm, smul_mul_assoc]
  rw [gaussianBraidGenerator_mul_mul_adjoint j hcomm] at hconj
  split_ifs at hconj with ht0 ht1
  · exact ⟨c, a, hconj⟩
  · refine ⟨c + 1 + 2 * chainForm N a.toAdd (-Pi.single j 1), a * ej⁻¹, ?_⟩
    rw [hconj, cubicSite_sq, weyl_mul_weyl, cubicFactor_def, toAdd_inv, toAdd_ofAdd,
      smul_smul, smul_smul, ← Units.val_mul, ← Units.val_mul, ← cubeRootPow_one,
      ← cubeRootPow_add, ← cubeRootPow_add]
  · refine ⟨c + 1 + 2 * chainForm N a.toAdd (Pi.single j 1), a * ej, ?_⟩
    rw [hconj, cubicSite_def, weyl_mul_weyl, cubicFactor_def, toAdd_ofAdd,
      smul_smul, smul_smul, ← Units.val_mul, ← Units.val_mul, ← cubeRootPow_one,
      ← cubeRootPow_add, ← cubeRootPow_add]

/-- Conjugation by `(gaussianBraidUnit N j)⁻¹` also preserves `heisenbergSubgroup N` (since
`g_j ^ 12 = 1`, hence `g_j⁻¹ = g_j ^ 11`). -/
private theorem gaussianBraidUnit_inv_conj_mem_heisenbergSubgroup {N : ℕ} (j : Fin N)
    {h : (CubicTorus N)ˣ} (hh : h ∈ heisenbergSubgroup N) :
    (gaussianBraidUnit N j)⁻¹ * h * gaussianBraidUnit N j ∈ heisenbergSubgroup N := by
  have hpow (k : ℕ) :
      gaussianBraidUnit N j ^ k * h * (gaussianBraidUnit N j ^ k)⁻¹ ∈ heisenbergSubgroup N := by
    induction k with
    | zero => simpa using hh
    | succ k ih =>
      have heq :
          gaussianBraidUnit N j ^ (k + 1) * h * (gaussianBraidUnit N j ^ (k + 1))⁻¹ =
            gaussianBraidUnit N j * (gaussianBraidUnit N j ^ k * h *
              (gaussianBraidUnit N j ^ k)⁻¹) * (gaussianBraidUnit N j)⁻¹ := by
        rw [pow_succ', mul_inv_rev]
        group
      rw [heq]
      exact gaussianBraidUnit_conj_mem_heisenbergSubgroup j ih
  have h11 : (gaussianBraidUnit N j)⁻¹ = gaussianBraidUnit N j ^ 11 := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, gaussianBraidUnit_pow_twelve]
  have hstep := hpow 11
  rw [← h11, inv_inv] at hstep
  exact hstep

/-- Every element in `Subgroup.closure (Set.range (gaussianBraidUnit N))` normalizes
`heisenbergSubgroup N`. -/
private theorem mem_closure_gaussianBraidUnit_conj_mem {N : ℕ}
    {g : (CubicTorus N)ˣ} (hg : g ∈ Subgroup.closure (Set.range (gaussianBraidUnit N))) :
    (∀ h ∈ heisenbergSubgroup N, g * h * g⁻¹ ∈ heisenbergSubgroup N) ∧
      (∀ h ∈ heisenbergSubgroup N, g⁻¹ * h * g ∈ heisenbergSubgroup N) := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨j, rfl⟩
    exact ⟨fun _ hh ↦ gaussianBraidUnit_conj_mem_heisenbergSubgroup j hh,
      fun _ hh ↦ gaussianBraidUnit_inv_conj_mem_heisenbergSubgroup j hh⟩
  | one =>
    exact ⟨fun h hh ↦ by simpa using hh, fun h hh ↦ by simpa using hh⟩
  | mul x y _ _ ihx ihy =>
    refine ⟨fun h hh ↦ ?_, fun h hh ↦ ?_⟩
    · have : (x * y) * h * (x * y)⁻¹ = x * (y * h * y⁻¹) * x⁻¹ := by group
      rw [this]
      exact ihx.1 _ (ihy.1 h hh)
    · have : (x * y)⁻¹ * h * (x * y) = y⁻¹ * (x⁻¹ * h * x) * y := by group
      rw [this]
      exact ihy.2 _ (ihx.2 h hh)
  | inv x _ ihx =>
    exact ⟨fun h hh ↦ by simpa [inv_inv] using ihx.2 h hh,
      fun h hh ↦ by simpa [inv_inv] using ihx.1 h hh⟩

/-! ### Central elements, left-regular determinants, and finiteness -/

/-- If `x : CubicTorus N` commutes with every Weyl basis element, then every label in its support
lies in the radical of `chainForm N`. -/
private theorem chainForm_eq_zero_of_commute_weyl {N : ℕ} {x : CubicTorus N}
    (hcomm : ∀ b : Multiplicative (Fin N → ZMod 3), x * weyl N b = weyl N b * x)
    {a : Multiplicative (Fin N → ZMod 3)} (ha : (weylBasis N).repr x a ≠ 0)
    (b : Multiplicative (Fin N → ZMod 3)) :
    chainForm N a.toAdd b.toAdd = 0 := by
  let coord : CubicTorus N →ₗ[ℂ] ℂ :=
    (Finsupp.lapply (a * b)).comp (weylBasis N).repr.toLinearMap
  have h1 : coord (x * weyl N b) = (weylBasis N).repr x a * (cubicFactor N a b : ℂ) := by
    conv_lhs => rw [← (weylBasis N).sum_repr x]
    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, weylBasis_apply, weyl_mul_weyl,
      smul_eq_mul]
    rw [Finset.sum_eq_single a]
    · change (weylBasis N).repr x a * ((cubicFactor N a b : ℂ) *
        (weylBasis N).repr (weyl N (a * b)) (a * b)) = _
      rw [← weylBasis_apply, Module.Basis.repr_self, Finsupp.single_eq_same, mul_one]
    · intro c _ hca
      change (weylBasis N).repr x c * ((cubicFactor N c b : ℂ) *
        (weylBasis N).repr (weyl N (c * b)) (a * b)) = 0
      have hne : a * b ≠ c * b := fun h ↦ hca (mul_right_cancel h).symm
      rw [← weylBasis_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne hne, mul_zero,
        mul_zero]
    · intro hmem; exact absurd (Finset.mem_univ a) hmem
  have h2 : coord (weyl N b * x) = (weylBasis N).repr x a * (cubicFactor N b a : ℂ) := by
    conv_lhs => rw [← (weylBasis N).sum_repr x]
    simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, weylBasis_apply, weyl_mul_weyl,
      smul_eq_mul]
    rw [Finset.sum_eq_single a]
    · change (weylBasis N).repr x a * ((cubicFactor N b a : ℂ) *
        (weylBasis N).repr (weyl N (b * a)) (a * b)) = _
      rw [mul_comm b a, ← weylBasis_apply, Module.Basis.repr_self, Finsupp.single_eq_same, mul_one]
    · intro c _ hca
      change (weylBasis N).repr x c * ((cubicFactor N b c : ℂ) *
        (weylBasis N).repr (weyl N (b * c)) (a * b)) = 0
      have hne : a * b ≠ b * c := fun h ↦ hca (mul_right_cancel (h.trans (mul_comm b c))).symm
      rw [← weylBasis_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne hne, mul_zero,
        mul_zero]
    · intro hmem; exact absurd (Finset.mem_univ a) hmem
  have heq : (cubicFactor N a b : ℂ) = (cubicFactor N b a : ℂ) :=
    mul_left_cancel₀ ha (h1.symm.trans ((congrArg coord (hcomm b)).trans h2))
  have hfac : cubicFactor N a b = cubicFactor N b a := Units.ext heq
  have hpow : cubeRootPow (chainForm N a.toAdd b.toAdd) = 1 := by
    rw [← cubicFactor_mul_inv_swap, hfac, mul_inv_cancel]
  exact cubeRootPow_eq_one_iff.mp hpow

/-- Left multiplication by `x : CubicTorus N`, transported along `(weylBasis N).equivFun` to an
endomorphism of `Multiplicative (Fin N → ZMod 3) → ℂ`. -/
private noncomputable def mulLeftFun (N : ℕ) :
    CubicTorus N →* Module.End ℂ (Multiplicative (Fin N → ZMod 3) → ℂ) where
  toFun x :=
    (weylBasis N).equivFun.toLinearMap ∘ₗ LinearMap.mulLeft ℂ x ∘ₗ
      (weylBasis N).equivFun.symm.toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro f
    change (weylBasis N).equivFun (1 * (weylBasis N).equivFun.symm f) = f
    rw [one_mul, LinearEquiv.apply_symm_apply]
  map_mul' x y := by
    apply LinearMap.ext
    intro f
    change (weylBasis N).equivFun ((x * y) * (weylBasis N).equivFun.symm f) =
      (weylBasis N).equivFun (x * (weylBasis N).equivFun.symm
        ((weylBasis N).equivFun (y * (weylBasis N).equivFun.symm f)))
    rw [LinearEquiv.symm_apply_apply, mul_assoc]

private theorem mulLeftFun_apply (N : ℕ) (x : CubicTorus N)
    (f : Multiplicative (Fin N → ZMod 3) → ℂ) :
    mulLeftFun N x f = (weylBasis N).equivFun (x * (weylBasis N).equivFun.symm f) :=
  rfl

private theorem mulLeftFun_smul (N : ℕ) (c : ℂ) (x : CubicTorus N) :
    mulLeftFun N (c • x) = c • mulLeftFun N x := by
  apply LinearMap.ext
  intro f
  rw [mulLeftFun_apply, smul_mul_assoc, LinearEquiv.map_smul]
  rfl

private theorem mulLeftFun_smul_one (N : ℕ) (c : ℂ) :
    mulLeftFun N (c • (1 : CubicTorus N)) = c • LinearMap.id := by
  rw [mulLeftFun_smul, map_one]
  rfl

/-- Any multiplicative homomorphism `d : Subgroup.closure (Set.range (gaussianBraidUnit N)) →* ℂ`
takes values in the `12`-th roots of unity (because every generator has `g_j ^ 12 = 1`). -/
private theorem map_pow_twelve_eq_one {N : ℕ}
    (d : Subgroup.closure (Set.range (gaussianBraidUnit N)) →* ℂ)
    (h : Subgroup.closure (Set.range (gaussianBraidUnit N))) :
    d h ^ 12 = 1 := by
  rcases h with ⟨x, hx⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with ⟨j, rfl⟩
    have h12 : (⟨gaussianBraidUnit N j, Subgroup.subset_closure ⟨j, rfl⟩⟩ :
        Subgroup.closure (Set.range (gaussianBraidUnit N))) ^ 12 = 1 :=
      Subtype.ext (gaussianBraidUnit_pow_twelve N j)
    rw [← map_pow, h12, map_one]
  | one =>
    exact (by simp : d 1 ^ 12 = 1)
  | mul x y hx hy ihx ihy =>
    have hmul : (⟨x * y, mul_mem hx hy⟩ :
        Subgroup.closure (Set.range (gaussianBraidUnit N))) =
        ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [hmul, map_mul, mul_pow, ihx, ihy, mul_one]
  | inv x hx ihx =>
    have hinv : (⟨x⁻¹, inv_mem hx⟩ :
        Subgroup.closure (Set.range (gaussianBraidUnit N))) = (⟨x, hx⟩)⁻¹ := rfl
    have hprod : d (⟨x, hx⟩)⁻¹ ^ 12 * d ⟨x, hx⟩ ^ 12 = 1 := by
      rw [← mul_pow, ← map_mul, inv_mul_cancel, map_one, one_pow]
    rw [hinv]
    rw [ihx, mul_one] at hprod
    exact hprod

/-- The conjugation action of `Subgroup.closure (Set.range (gaussianBraidUnit N))` on the finite
Heisenberg subgroup `heisenbergSubgroup N`. -/
private noncomputable def gaussianConjAction (N : ℕ) :
    Subgroup.closure (Set.range (gaussianBraidUnit N)) →* Equiv.Perm (heisenbergSubgroup N) where
  toFun g :=
    { toFun := fun h ↦
        ⟨g.1 * h.1 * g.1⁻¹, (mem_closure_gaussianBraidUnit_conj_mem g.2).1 h.1 h.2⟩
      invFun := fun h ↦
        ⟨g.1⁻¹ * h.1 * g.1, (mem_closure_gaussianBraidUnit_conj_mem g.2).2 h.1 h.2⟩
      left_inv := fun h ↦ Subtype.ext (by group)
      right_inv := fun h ↦ Subtype.ext (by group) }
  map_one' := by
    refine Equiv.ext fun h ↦ Subtype.ext ?_
    change (1 : (CubicTorus N)ˣ) * h.1 * (1 : (CubicTorus N)ˣ)⁻¹ = h.1
    group
  map_mul' g₁ g₂ := by
    refine Equiv.ext fun h ↦ Subtype.ext ?_
    change (g₁.1 * g₂.1) * h.1 * (g₁.1 * g₂.1)⁻¹ = g₁.1 * (g₂.1 * h.1 * g₂.1⁻¹) * g₁.1⁻¹
    group

private theorem commute_weyl_of_mem_ker_gaussianConjAction {N : ℕ}
    (z : (gaussianConjAction N).ker) (b : Multiplicative (Fin N → ZMod 3)) :
    (z.1.1 : CubicTorus N) * weyl N b = weyl N b * (z.1.1 : CubicTorus N) := by
  have hz : gaussianConjAction N z.1 = 1 := z.2
  have heq := congrArg (fun p : Equiv.Perm (heisenbergSubgroup N) ↦
    (p ⟨weylUnit N b, weylUnit_mem_heisenbergSubgroup N b⟩).1) hz
  change z.1.1 * weylUnit N b * z.1.1⁻¹ = weylUnit N b at heq
  have hunit : z.1.1 * weylUnit N b = weylUnit N b * z.1.1 := by
    have := congrArg (· * z.1.1) heq
    simpa [mul_assoc] using this
  simpa [Units.val_mul] using congrArg Units.val hunit

/-- Finiteness of `(gaussianConjAction N).ker` when `N` is even: every kernel element is a scalar
multiple of `1` whose `(3 ^ N * 12)`-th power is `1`. -/
private theorem finite_ker_gaussianConjAction_even {N : ℕ} (hN : Even N) :
    Finite (gaussianConjAction N).ker := by
  let H := Subgroup.closure (Set.range (gaussianBraidUnit N))
  let G := Multiplicative (Fin N → ZMod 3)
  let detHom : H →* ℂ :=
    LinearMap.det.comp ((mulLeftFun N).comp ((Units.coeHom (CubicTorus N)).comp H.subtype))
  have hscalar (z : (gaussianConjAction N).ker) :
      (z.1.1 : CubicTorus N) = cubicScalarCoefficient N z.1.1 • (1 : CubicTorus N) := by
    conv_lhs => rw [← (weylBasis N).sum_repr z.1.1]
    rw [Finset.sum_eq_single (1 : G)]
    · rw [weylBasis_apply, weyl_one, cubicScalarCoefficient_apply]
    · intro a _ ha
      have h0 : (weylBasis N).repr z.1.1 a = 0 := by
        by_contra hne
        have hrad : ∀ b : Fin N → ZMod 3, chainForm N a.toAdd b = 0 := fun b ↦ by
          simpa [toAdd_ofAdd] using chainForm_eq_zero_of_commute_weyl
            (commute_weyl_of_mem_ker_gaussianConjAction z) hne (Multiplicative.ofAdd b)
        have ha0 : a.toAdd = 0 := eq_zero_of_forall_chainForm_eq_zero_of_even hN hrad
        exact ha (Multiplicative.toAdd.injective (by simpa using ha0))
      rw [h0, zero_smul]
    · intro h1; exact absurd (Finset.mem_univ _) h1
  have hcard : Module.finrank ℂ (G → ℂ) = 3 ^ N := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [G, Fintype.card_pi]
  have hpow (z : (gaussianConjAction N).ker) :
      (cubicScalarCoefficient N z.1.1) ^ (3 ^ N * 12) = 1 := by
    have hdet : detHom z.1 = (cubicScalarCoefficient N z.1.1) ^ (3 ^ N) := by
      change LinearMap.det (mulLeftFun N z.1.1) = _
      conv_lhs => rw [hscalar z]
      rw [mulLeftFun_smul_one, LinearMap.det_smul, LinearMap.det_id, mul_one, hcard]
    rw [pow_mul, ← hdet]
    exact map_pow_twelve_eq_one detHom z.1
  have hne (z : (gaussianConjAction N).ker) : cubicScalarCoefficient N z.1.1 ≠ 0 := by
    intro h0
    have hp := hpow z
    rw [h0, zero_pow (by positivity)] at hp
    exact zero_ne_one hp
  let embed : (gaussianConjAction N).ker → rootsOfUnity (3 ^ N * 12) ℂ := fun z ↦
    ⟨Units.mk0 (cubicScalarCoefficient N z.1.1) (hne z),
      (mem_rootsOfUnity' (3 ^ N * 12) _).mpr (by simpa using hpow z)⟩
  refine Finite.of_injective embed ?_
  intro z₁ z₂ h
  have hc : cubicScalarCoefficient N z₁.1.1 = cubicScalarCoefficient N z₂.1.1 := by
    simpa [embed] using congrArg (fun u : rootsOfUnity (3 ^ N * 12) ℂ ↦ (u.1 : ℂ)) h
  exact Subtype.ext (Subtype.ext (Units.ext (by rw [hscalar z₁, hscalar z₂, hc])))

private def oddRadicalLabel (N : ℕ) : Multiplicative (Fin N → ZMod 3) :=
  Multiplicative.ofAdd (cubicRadicalVec N)

private theorem oddRadicalLabel_ne_one {N : ℕ} (hN : Odd N) : oddRadicalLabel N ≠ 1 := by
  obtain ⟨k, hk⟩ := hN
  have hNpos : 0 < N := by omega
  intro h
  have hadd := congrArg Multiplicative.toAdd h
  rw [oddRadicalLabel, toAdd_ofAdd, toAdd_one] at hadd
  have h0 := congrFun hadd ⟨0, hNpos⟩
  rw [Pi.zero_apply, cubicRadicalVec_apply, ite_eq_left Even.zero] at h0
  exact absurd h0 (by decide)

private theorem oddRadicalLabel_inv_ne_one {N : ℕ} (hN : Odd N) :
    (oddRadicalLabel N)⁻¹ ≠ 1 :=
  fun h ↦ oddRadicalLabel_ne_one hN (inv_eq_one.mp h)

private theorem oddRadicalLabel_inv_ne_self {N : ℕ} (hN : Odd N) :
    (oddRadicalLabel N)⁻¹ ≠ oddRadicalLabel N := by
  obtain ⟨k, hk⟩ := hN
  have hNpos : 0 < N := by omega
  intro h
  have hadd := congrArg Multiplicative.toAdd h
  rw [toAdd_inv, oddRadicalLabel, toAdd_ofAdd] at hadd
  have h0 := congrFun hadd ⟨0, hNpos⟩
  rw [Pi.neg_apply, cubicRadicalVec_apply, ite_eq_left Even.zero] at h0
  exact absurd h0 (by decide)

private theorem weyl_oddRadicalLabel_central {N : ℕ} (hN : Odd N) (y : CubicTorus N) :
    y * weyl N (oddRadicalLabel N) = weyl N (oddRadicalLabel N) * y := by
  conv_lhs => rw [← (weylBasis N).sum_repr y]
  conv_rhs => rw [← (weylBasis N).sum_repr y]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, weylBasis_apply]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  congr 1
  rw [weyl_mul_weyl_comm, chainForm_swap, oddRadicalLabel, toAdd_ofAdd,
    chainForm_cubicRadicalVec_left_of_odd hN b.toAdd, neg_zero, cubeRootPow_zero, Units.val_one,
    one_smul]

private theorem weyl_oddRadicalLabel_inv_central {N : ℕ} (hN : Odd N) (y : CubicTorus N) :
    y * weyl N (oddRadicalLabel N)⁻¹ = weyl N (oddRadicalLabel N)⁻¹ * y := by
  rw [← weyl_sq, sq, ← mul_assoc, weyl_oddRadicalLabel_central hN, mul_assoc,
    weyl_oddRadicalLabel_central hN, ← mul_assoc]

/-- The three central idempotents `P_r = 3⁻¹ • (1 + ω ^ (-r) • W(ρ) + ω ^ r • W(ρ⁻¹))`
(`r ∈ ZMod 3`) splitting `CubicTorus N` for odd `N`. -/
private noncomputable def oddCentralProj (N : ℕ) (r : ZMod 3) : CubicTorus N :=
  (3 : ℂ)⁻¹ • (1 + (cubeRootPow (-r) : ℂ) • weyl N (oddRadicalLabel N) +
    (cubeRootPow r : ℂ) • weyl N (oddRadicalLabel N)⁻¹)

private theorem oddCentralProj_central {N : ℕ} (hN : Odd N) (r : ZMod 3) (y : CubicTorus N) :
    y * oddCentralProj N r = oddCentralProj N r * y := by
  simp only [oddCentralProj, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul,
    weyl_oddRadicalLabel_central hN, weyl_oddRadicalLabel_inv_central hN]

private theorem weyl_oddRadicalLabel_mul_oddCentralProj (N : ℕ) (r : ZMod 3) :
    weyl N (oddRadicalLabel N) * oddCentralProj N r = (cubeRootPow r : ℂ) • oddCentralProj N r := by
  have h1 : (cubeRootPow r : ℂ) * (cubeRootPow (-r) : ℂ) = 1 := by
    rw [← Units.val_mul, ← cubeRootPow_add, add_neg_cancel, cubeRootPow_zero, Units.val_one]
  have h2 : (cubeRootPow r : ℂ) * (cubeRootPow r : ℂ) = (cubeRootPow (-r) : ℂ) := by
    rw [← Units.val_mul, ← cubeRootPow_add]
    congr 2
    fin_cases r <;> decide
  have hstep :
      (cubeRootPow r : ℂ) •
          (1 + (cubeRootPow (-r) : ℂ) • weyl N (oddRadicalLabel N) +
            (cubeRootPow r : ℂ) • weyl N (oddRadicalLabel N)⁻¹) =
        weyl N (oddRadicalLabel N) + (cubeRootPow (-r) : ℂ) • weyl N (oddRadicalLabel N)⁻¹ +
          (cubeRootPow r : ℂ) • (1 : CubicTorus N) := by
    rw [smul_add, smul_add, smul_smul, smul_smul, h1, h2, one_smul]
    abel
  simp only [oddCentralProj, mul_smul_comm, mul_add, mul_one, ← sq, weyl_sq, weyl_mul_weyl_inv]
  rw [smul_comm (cubeRootPow r : ℂ) (3 : ℂ)⁻¹, hstep]

private theorem weyl_oddRadicalLabel_inv_mul_oddCentralProj (N : ℕ) (r : ZMod 3) :
    weyl N (oddRadicalLabel N)⁻¹ * oddCentralProj N r =
      (cubeRootPow (-r) : ℂ) • oddCentralProj N r := by
  calc
    weyl N (oddRadicalLabel N)⁻¹ * oddCentralProj N r
        = weyl N (oddRadicalLabel N) * (weyl N (oddRadicalLabel N) * oddCentralProj N r) := by
          rw [← weyl_sq, sq, mul_assoc]
    _ = weyl N (oddRadicalLabel N) * ((cubeRootPow r : ℂ) • oddCentralProj N r) := by
          rw [weyl_oddRadicalLabel_mul_oddCentralProj]
    _ = (cubeRootPow r : ℂ) • (weyl N (oddRadicalLabel N) * oddCentralProj N r) := by
          rw [mul_smul_comm]
    _ = ((cubeRootPow r : ℂ) * (cubeRootPow r : ℂ)) • oddCentralProj N r := by
          rw [weyl_oddRadicalLabel_mul_oddCentralProj, smul_smul]
    _ = (cubeRootPow (-r) : ℂ) • oddCentralProj N r := by
          congr 1
          rw [← Units.val_mul, ← cubeRootPow_add]
          congr 2
          fin_cases r <;> decide

private theorem oddCentralProj_sum (N : ℕ) :
    oddCentralProj N 0 + oddCentralProj N 1 + oddCentralProj N 2 = 1 := by
  have hsumω : (1 : ℂ) + (cubeRootOfUnity : ℂ) + ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ) = 0 := by
    rw [cubeRootOfUnity_inv_val]
    exact one_add_cubeRootOfUnity_add_sq
  have hneg1 : (-1 : ZMod 3) = 2 := by decide
  have hneg2 : (-2 : ZMod 3) = 1 := by decide
  simp only [oddCentralProj, neg_zero, hneg1, hneg2, cubeRootPow_zero, cubeRootPow_one,
    cubeRootPow_two, Units.val_one, one_smul]
  calc
    (3 : ℂ)⁻¹ • (1 + weyl N (oddRadicalLabel N) + weyl N (oddRadicalLabel N)⁻¹) +
        (3 : ℂ)⁻¹ • (1 + ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ) • weyl N (oddRadicalLabel N) +
          (cubeRootOfUnity : ℂ) • weyl N (oddRadicalLabel N)⁻¹) +
        (3 : ℂ)⁻¹ • (1 + (cubeRootOfUnity : ℂ) • weyl N (oddRadicalLabel N) +
          ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ) • weyl N (oddRadicalLabel N)⁻¹)
        = ((3 : ℂ)⁻¹ * 3) • (1 : CubicTorus N) +
            ((3 : ℂ)⁻¹ * (1 + (cubeRootOfUnity : ℂ) + ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ))) •
              weyl N (oddRadicalLabel N) +
            ((3 : ℂ)⁻¹ * (1 + (cubeRootOfUnity : ℂ) + ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ))) •
              weyl N (oddRadicalLabel N)⁻¹ := by module
    _ = 1 := by
          rw [hsumω, mul_zero, zero_smul, zero_smul, add_zero, add_zero,
            inv_mul_cancel₀ (by norm_num : (3 : ℂ) ≠ 0), one_smul]

private theorem oddCentralProj_ne_zero {N : ℕ} (hN : Odd N) (r : ZMod 3) :
    oddCentralProj N r ≠ 0 := by
  intro h0
  have hs := congrArg (cubicScalarCoefficient N) h0
  simp only [oddCentralProj, map_smul, map_add, cubicScalarCoefficient_one,
    cubicScalarCoefficient_weyl, ite_eq_right (oddRadicalLabel_ne_one hN),
    ite_eq_right (oddRadicalLabel_inv_ne_one hN), smul_eq_mul, mul_zero, add_zero, mul_one,
    map_zero] at hs
  norm_num at hs

private theorem central_eq_linear_comb_of_odd {N : ℕ} (hN : Odd N) {x : CubicTorus N}
    (hcomm : ∀ b : Multiplicative (Fin N → ZMod 3), x * weyl N b = weyl N b * x) :
    x = (weylBasis N).repr x 1 • (1 : CubicTorus N) +
      (weylBasis N).repr x (oddRadicalLabel N) • weyl N (oddRadicalLabel N) +
      (weylBasis N).repr x (oddRadicalLabel N)⁻¹ • weyl N (oddRadicalLabel N)⁻¹ := by
  apply (weylBasis N).repr.injective
  ext a
  have h1 : (1 : CubicTorus N) = weylBasis N 1 := by rw [weylBasis_apply, weyl_one]
  have hρ : weyl N (oddRadicalLabel N) = weylBasis N (oddRadicalLabel N) :=
    (weylBasis_apply N _).symm
  have hρi : weyl N (oddRadicalLabel N)⁻¹ = weylBasis N (oddRadicalLabel N)⁻¹ :=
    (weylBasis_apply N _).symm
  rw [h1, hρ, hρi]
  simp only [map_add, map_smul, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
    smul_eq_mul, Finsupp.single_apply, mul_ite, mul_one, mul_zero]
  by_cases ha1 : a = 1
  · subst ha1
    rw [ite_eq_left rfl, ite_eq_right (oddRadicalLabel_ne_one hN),
      ite_eq_right (oddRadicalLabel_inv_ne_one hN), add_zero, add_zero]
  · by_cases haρ : a = oddRadicalLabel N
    · subst haρ
      rw [ite_eq_right (oddRadicalLabel_ne_one hN).symm, ite_eq_left rfl,
        ite_eq_right (oddRadicalLabel_inv_ne_self hN), zero_add, add_zero]
    · by_cases haρi : a = (oddRadicalLabel N)⁻¹
      · subst haρi
        rw [ite_eq_right (oddRadicalLabel_inv_ne_one hN).symm,
          ite_eq_right (oddRadicalLabel_inv_ne_self hN).symm, ite_eq_left rfl, zero_add, zero_add]
      · rw [ite_eq_right (Ne.symm ha1), ite_eq_right (Ne.symm haρ), ite_eq_right (Ne.symm haρi),
          add_zero, add_zero]
        by_contra hne
        have hrad : ∀ b : Fin N → ZMod 3, chainForm N a.toAdd b = 0 := fun b ↦ by
          simpa [toAdd_ofAdd] using
            chainForm_eq_zero_of_commute_weyl hcomm hne (Multiplicative.ofAdd b)
        obtain ⟨c, hc⟩ := exists_smul_cubicRadicalVec_of_forall_chainForm_eq_zero_of_odd hN hrad
        have hc_cases : c = 0 ∨ c = 1 ∨ c = 2 := by
          fin_cases c
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
        rcases hc_cases with rfl | rfl | rfl
        · exact ha1 (Multiplicative.toAdd.injective (by rw [toAdd_one, hc, zero_smul]))
        · exact haρ (Multiplicative.toAdd.injective (by
            rw [oddRadicalLabel, toAdd_ofAdd, hc, one_smul]))
        · exact haρi (Multiplicative.toAdd.injective (by
            rw [toAdd_inv, oddRadicalLabel, toAdd_ofAdd, hc,
              show (2 : ZMod 3) = -1 by decide, neg_one_smul]))

/-- Finiteness of `(gaussianConjAction N).ker` when `N` is odd: every kernel element lies in the
center `ℂ[W(ρ)]` and acts by a root-of-unity scalar on each of the three nonzero central blocks
`oddCentralProj N r`. -/
private theorem finite_ker_gaussianConjAction_odd {N : ℕ} (hN : Odd N) :
    Finite (gaussianConjAction N).ker := by
  -- 1. Build the three nonzero central-idempotent blocks `E r = range (mulLeftFun N P_r)`.
  let H := Subgroup.closure (Set.range (gaussianBraidUnit N))
  let E (r : ZMod 3) : Submodule ℂ (Multiplicative (Fin N → ZMod 3) → ℂ) :=
    LinearMap.range (mulLeftFun N (oddCentralProj N r))
  have hE_pos (r : ZMod 3) : 0 < Module.finrank ℂ (E r) := by
    have hne : (weylBasis N).equivFun (oddCentralProj N r) ≠ 0 := fun h ↦ by
      have h0 : (weylBasis N).equivFun (oddCentralProj N r) = (weylBasis N).equivFun 0 := by
        rw [h, LinearEquiv.map_zero]
      exact oddCentralProj_ne_zero hN r ((weylBasis N).equivFun.injective h0)
    have hmem : (weylBasis N).equivFun (oddCentralProj N r) ∈ E r := by
      refine ⟨(weylBasis N).equivFun 1, ?_⟩
      rw [mulLeftFun_apply, LinearEquiv.symm_apply_apply, mul_one]
    exact Module.finrank_pos_iff.mpr
      ⟨⟨(weylBasis N).equivFun (oddCentralProj N r), hmem⟩, 0,
        fun h ↦ hne (congrArg Subtype.val h)⟩
  let restrictLeft (r : ZMod 3) : CubicTorus N →* Module.End ℂ (E r) :=
    { toFun := fun x ↦ (mulLeftFun N x).restrict fun v hv ↦ by
        rcases hv with ⟨w, rfl⟩
        refine ⟨mulLeftFun N x w, ?_⟩
        change (mulLeftFun N (oddCentralProj N r) * mulLeftFun N x) w =
          (mulLeftFun N x * mulLeftFun N (oddCentralProj N r)) w
        rw [← map_mul, ← map_mul, oddCentralProj_central hN r x]
      map_one' := by
        apply LinearMap.ext
        rintro ⟨v, hv⟩
        apply Subtype.ext
        change mulLeftFun N 1 v = v
        rw [map_one]
        rfl
      map_mul' := fun x y ↦ by
        apply LinearMap.ext
        rintro ⟨v, hv⟩
        apply Subtype.ext
        change mulLeftFun N (x * y) v = mulLeftFun N x (mulLeftFun N y v)
        rw [map_mul]
        rfl }
  let detBlock (r : ZMod 3) : H →* ℂ :=
    LinearMap.det.comp ((restrictLeft r).comp ((Units.coeHom (CubicTorus N)).comp H.subtype))
  -- 2. Every kernel element acts on `E r` as scalar `eig r z`, forced to be a root of unity via
  --    the block determinant `detBlock r`.
  let eig (r : ZMod 3) (z : (gaussianConjAction N).ker) : ℂ :=
    (weylBasis N).repr z.1.1 1 +
      (weylBasis N).repr z.1.1 (oddRadicalLabel N) * (cubeRootPow r : ℂ) +
      (weylBasis N).repr z.1.1 (oddRadicalLabel N)⁻¹ * (cubeRootPow (-r) : ℂ)
  have hmul_P (r : ZMod 3) (z : (gaussianConjAction N).ker) :
      (z.1.1 : CubicTorus N) * oddCentralProj N r = eig r z • oddCentralProj N r := by
    conv_lhs =>
      rw [central_eq_linear_comb_of_odd hN (commute_weyl_of_mem_ker_gaussianConjAction z)]
    simp only [add_mul, smul_mul_assoc, one_mul, weyl_oddRadicalLabel_mul_oddCentralProj,
      weyl_oddRadicalLabel_inv_mul_oddCentralProj, smul_smul, eig]
    module
  have hrestrict_eq (r : ZMod 3) (z : (gaussianConjAction N).ker) :
      restrictLeft r z.1.1 = eig r z • LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨v, hv⟩
    rcases hv with ⟨w, rfl⟩
    apply Subtype.ext
    change mulLeftFun N z.1.1 (mulLeftFun N (oddCentralProj N r) w) =
      eig r z • mulLeftFun N (oddCentralProj N r) w
    calc
      mulLeftFun N z.1.1 (mulLeftFun N (oddCentralProj N r) w)
          = (mulLeftFun N z.1.1 * mulLeftFun N (oddCentralProj N r)) w := rfl
      _ = mulLeftFun N ((z.1.1 : CubicTorus N) * oddCentralProj N r) w := by rw [← map_mul]
      _ = mulLeftFun N (eig r z • oddCentralProj N r) w := by rw [hmul_P r z]
      _ = eig r z • mulLeftFun N (oddCentralProj N r) w := by rw [mulLeftFun_smul]; rfl
  have heig_pow (r : ZMod 3) (z : (gaussianConjAction N).ker) :
      eig r z ^ (Module.finrank ℂ (E r) * 12) = 1 := by
    have hdet : detBlock r z.1 = eig r z ^ Module.finrank ℂ (E r) := by
      change LinearMap.det (restrictLeft r z.1.1) = _
      rw [hrestrict_eq r z, LinearMap.det_smul, LinearMap.det_id, mul_one]
    rw [pow_mul, ← hdet]
    exact map_pow_twelve_eq_one (detBlock r) z.1
  have heig_ne (r : ZMod 3) (z : (gaussianConjAction N).ker) : eig r z ≠ 0 := by
    intro h0
    have hp := heig_pow r z
    have hpos : 0 < Module.finrank ℂ (E r) * 12 := Nat.mul_pos (hE_pos r) (by norm_num)
    rw [h0, zero_pow hpos.ne'] at hp
    exact zero_ne_one hp
  -- 3. Reconstruct `z` injectively from `(eig 0 z, eig 1 z, eig 2 z)` via `P_0 + P_1 + P_2 = 1`.
  have : ∀ r : ZMod 3, NeZero (Module.finrank ℂ (E r) * 12) :=
    fun r ↦ ⟨(Nat.mul_pos (hE_pos r) (by norm_num)).ne'⟩
  let embed :
      (gaussianConjAction N).ker → ∀ r : ZMod 3, rootsOfUnity (Module.finrank ℂ (E r) * 12) ℂ :=
    fun z r ↦ ⟨Units.mk0 (eig r z) (heig_ne r z),
      (mem_rootsOfUnity' (Module.finrank ℂ (E r) * 12) _).mpr (by simpa using heig_pow r z)⟩
  refine Finite.of_injective embed ?_
  intro z₁ z₂ h
  have heig_eq (r : ZMod 3) : eig r z₁ = eig r z₂ := by
    simpa [embed] using
      congrArg (fun f : ∀ r : ZMod 3, rootsOfUnity (Module.finrank ℂ (E r) * 12) ℂ ↦ (f r).1.1) h
  have hsplit (z : (gaussianConjAction N).ker) :
      (z.1.1 : CubicTorus N) = eig 0 z • oddCentralProj N 0 + eig 1 z • oddCentralProj N 1 +
        eig 2 z • oddCentralProj N 2 := by
    conv_lhs => rw [← mul_one (z.1.1 : CubicTorus N), ← oddCentralProj_sum N]
    simp only [mul_add, hmul_P]
  exact Subtype.ext (Subtype.ext (Units.ext (by
    rw [hsplit z₁, hsplit z₂, heig_eq 0, heig_eq 1, heig_eq 2])))

/-- **Finiteness of the Gaussian braid subgroup**
`Subgroup.closure (Set.range (gaussianBraidUnit N))`. -/
theorem finite_subgroup_closure_range_gaussianBraidUnit (N : ℕ) :
    Finite (Subgroup.closure (Set.range (gaussianBraidUnit N))) := by
  have : Finite (Subgroup.closure (Set.range (gaussianBraidUnit N)) ⧸ (gaussianConjAction N).ker) :=
    Finite.of_injective (QuotientGroup.kerLift (gaussianConjAction N))
      (QuotientGroup.kerLift_injective (gaussianConjAction N))
  have : Finite (gaussianConjAction N).ker :=
    (Nat.even_or_odd N).elim finite_ker_gaussianConjAction_even finite_ker_gaussianConjAction_odd
  exact Finite.of_subgroup_quotient (gaussianConjAction N).ker

/-- **The Gaussian braid image is finite**: the generators `gaussianBraidGenerator N j` are units
of `CubicTorus N`, and the subgroup of `(CubicTorus N)ˣ` they generate is finite. -/
theorem finite_gaussianBraid_closure (N : ℕ) :
    ∃ g : Fin N → (CubicTorus N)ˣ,
      (∀ j, (g j : CubicTorus N) = gaussianBraidGenerator N j) ∧
        Finite (Subgroup.closure (Set.range g)) :=
  ⟨gaussianBraidUnit N, coe_gaussianBraidUnit N,
    finite_subgroup_closure_range_gaussianBraidUnit N⟩

/-- The image of `BraidGroup (N + 1)` under `gaussianBraidHom N` is finite. -/
theorem finite_range_gaussianBraidHom (N : ℕ) :
    Finite (gaussianBraidHom N).range := by
  let incl : (cubicFixed N)ˣ →* (CubicTorus N)ˣ := Units.map (cubicFixed N).val.toMonoidHom
  have hinj : Function.Injective incl := fun u v h ↦
    Units.ext (Subtype.ext (congrArg Units.val h))
  have hmem (b : BraidGroup (N + 1)) :
      incl (gaussianBraidHom N b) ∈ Subgroup.closure (Set.range (gaussianBraidUnit N)) := by
    have htop : b ∈ Subgroup.closure (Set.range (BraidGroup.sigma (n := N + 1))) := by
      rw [BraidGroup.closure_range_sigma]
      trivial
    induction htop using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with ⟨j, rfl⟩
      have heq : incl (gaussianBraidHom N (BraidGroup.sigma j)) = gaussianBraidUnit N j := by
        rw [gaussianBraidHom_sigma]
        exact Units.ext rfl
      rw [heq]
      exact Subgroup.subset_closure ⟨j, rfl⟩
    | one =>
      rw [map_one, map_one]
      exact one_mem _
    | mul x y _ _ ihx ihy =>
      rw [map_mul, map_mul]
      exact mul_mem ihx ihy
    | inv x _ ihx =>
      have hinv : incl (gaussianBraidHom N x⁻¹) = (incl (gaussianBraidHom N x))⁻¹ :=
        eq_inv_of_mul_eq_one_left (by rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one])
      rw [hinv]
      exact inv_mem ihx
  let mapToClosure : (gaussianBraidHom N).range →
      Subgroup.closure (Set.range (gaussianBraidUnit N)) :=
    fun x ↦ ⟨incl x.1, by rcases x.2 with ⟨b, hb⟩; rw [← hb]; exact hmem b⟩
  have := finite_subgroup_closure_range_gaussianBraidUnit N
  refine Finite.of_injective mapToClosure fun x y h ↦ ?_
  exact Subtype.ext (hinj (congrArg Subtype.val h))

end TauCeti.TemperleyLieb
