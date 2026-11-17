/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic
public import TauCeti.KnotTheory.TemperleyLieb
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The cubic Gaussian braid representation and its finiteness

In `CubicTorus N`, with `u = twelfthRootOfUnity = exp (π i / 6)`, the Gaussian braid generators
`g_j = gaussianBraidGenerator N j = u • ((1 + u ^ 2) • p_j - 1)` lie in `cubicFixed N`, are unitary
(`g_j ^ 3 = (-I) • 1`, `g_j ^ 12 = 1`), satisfy the Artin braid relations (`gaussianBraid`), and
agree up to scalar phase with the image of the Jones crossing under `cubicFixedHom (N + 1)`.
Conjugation by `g_j` permutes the Weyl basis by the symplectic transvection
`g_j * W(a) * g_j⁻¹ = W(a + B(a, e_j) • e_j)` (`gaussianBraidUnit_conj_weyl`). Elements in the
kernel of the resulting permutation representation lie in the center ∩ `cubicFixed N` (scalar for
even `N`, spanned by `oddProj N` and `1 - oddProj N` for odd `N`); determinant bounds show the
eigenvalues are roots of unity of bounded order, yielding `finite_gaussianBraid_closure`.
-/

public section

namespace TauCeti.TemperleyLieb

open TwistedMonoidAlgebra (basis scalarTrace)
private theorem zmod3_cases (c : ZMod 3) : c = 0 ∨ c = 1 ∨ c = 2 := by decide +revert
private theorem sqrt_three_sq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
  rw [sq]; exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)

/-! ### The twelfth root of unity `u = exp (π i / 6)` -/

/-- `u = exp (π i / 6)`, a primitive twelfth root of unity with `u + u⁻¹ = √3` and `u ^ 4 = ω`. -/
noncomputable def twelfthRootOfUnity : ℂ :=
  Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * Complex.I)
theorem twelfthRootOfUnity_def :
    twelfthRootOfUnity = Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * Complex.I) := (rfl)
theorem twelfthRootOfUnity_eq :
    twelfthRootOfUnity = ((Real.sqrt 3 : ℂ) + Complex.I) / 2 := by
  rw [twelfthRootOfUnity_def, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_six, Real.sin_pi_div_six]; push_cast; ring
theorem twelfthRootOfUnity_ne_zero : twelfthRootOfUnity ≠ 0 := Complex.exp_ne_zero _
@[simp] theorem star_twelfthRootOfUnity : star twelfthRootOfUnity = twelfthRootOfUnity⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [twelfthRootOfUnity_def, Complex.star_def, ← Complex.exp_conj,
    show (starRingEnd ℂ) (((Real.pi / 6 : ℝ) : ℂ) * Complex.I) =
      -(((Real.pi / 6 : ℝ) : ℂ) * Complex.I) by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg],
    ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
theorem twelfthRootOfUnity_inv_eq :
    twelfthRootOfUnity⁻¹ = ((Real.sqrt 3 : ℂ) - Complex.I) / 2 := by
  rw [← star_twelfthRootOfUnity, twelfthRootOfUnity_eq, Complex.star_def, map_div₀, map_add,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat, sub_eq_add_neg]
theorem twelfthRootOfUnity_add_inv :
    twelfthRootOfUnity + twelfthRootOfUnity⁻¹ = (Real.sqrt 3 : ℂ) := by
  rw [twelfthRootOfUnity_inv_eq, twelfthRootOfUnity_eq]; ring
theorem twelfthRootOfUnity_pow_two :
    twelfthRootOfUnity ^ 2 = (1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2 := by
  rw [twelfthRootOfUnity_eq]
  linear_combination (1 / 4 : ℂ) * sqrt_three_sq + (1 / 4 : ℂ) * Complex.I_sq
theorem one_add_twelfthRootOfUnity_sq :
    1 + twelfthRootOfUnity ^ 2 = (Real.sqrt 3 : ℂ) * twelfthRootOfUnity := by
  rw [twelfthRootOfUnity_pow_two, twelfthRootOfUnity_eq]
  linear_combination (-1 / 2 : ℂ) * sqrt_three_sq
@[simp] theorem twelfthRootOfUnity_pow_three : twelfthRootOfUnity ^ 3 = Complex.I := by
  rw [pow_succ, twelfthRootOfUnity_pow_two, twelfthRootOfUnity_eq]
  linear_combination (Complex.I / 4 : ℂ) * sqrt_three_sq + ((Real.sqrt 3 : ℂ) / 4) * Complex.I_sq
@[simp] theorem twelfthRootOfUnity_pow_four : twelfthRootOfUnity ^ 4 = (cubeRootOfUnity : ℂ) := by
  rw [pow_succ, twelfthRootOfUnity_pow_three, twelfthRootOfUnity_eq, cubeRootOfUnity_val_eq]
  linear_combination (1 / 2 : ℂ) * Complex.I_sq
@[simp] theorem twelfthRootOfUnity_pow_six : twelfthRootOfUnity ^ 6 = -1 := by
  rw [show (6 : ℕ) = 3 * 2 by decide, pow_mul, twelfthRootOfUnity_pow_three, Complex.I_sq]
@[simp] theorem twelfthRootOfUnity_pow_twelve : twelfthRootOfUnity ^ 12 = 1 := by
  rw [show (12 : ℕ) = 6 * 2 by decide, pow_mul, twelfthRootOfUnity_pow_six]; norm_num

/-! ### Gaussian braid generators, unitarity, order, and braid relations -/

/-- The Gaussian braid generator `g_j = u • ((1 + u ^ 2) • p_j - 1)` in `CubicTorus N`. -/
noncomputable def gaussianBraidGenerator (N : ℕ) (j : Fin N) : CubicTorus N :=
  twelfthRootOfUnity • ((1 + twelfthRootOfUnity ^ 2) • cubicProjection N j - 1)
theorem gaussianBraidGenerator_def (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j =
      twelfthRootOfUnity • ((1 + twelfthRootOfUnity ^ 2) • cubicProjection N j - 1) := (rfl)
theorem gaussianBraidGenerator_mem_cubicFixed (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j ∈ cubicFixed N :=
  StarSubalgebra.smul_mem _
    (sub_mem (StarSubalgebra.smul_mem _ (cubicProjection_mem_cubicFixed N j) _) (one_mem _)) _
theorem gaussianBraidGenerator_eq_crossing (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j =
      ((cubicFixedHom (N + 1)
        (crossing (Real.sqrt 3 : ℂ) (-twelfthRootOfUnity) (twelfthRootOfUnity ^ 2) j)).1 :
        CubicTorus N) := by
  rw [crossing_def, map_add, map_smul, map_smul, map_one, AddMemClass.coe_add,
    SetLike.val_smul, SetLike.val_smul, OneMemClass.coe_one, coe_cubicFixedHom_e, smul_smul,
    gaussianBraidGenerator_def, smul_sub, smul_smul, one_add_twelfthRootOfUnity_sq,
    show twelfthRootOfUnity * ((Real.sqrt 3 : ℂ) * twelfthRootOfUnity) =
      twelfthRootOfUnity ^ 2 * (Real.sqrt 3 : ℂ) by ring, neg_smul, sub_eq_neg_add]
  rfl
/-- Weyl-basis expansion `g_j = -(√3)⁻¹ • (1 + ω ^ 2 • (U_j + U_j ^ 2))`. -/
theorem gaussianBraidGenerator_eq_weyl (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j =
      -((Real.sqrt 3 : ℂ)⁻¹) •
        (1 + ((cubeRootOfUnity : ℂ) ^ 2) • (cubicSite N j + cubicSite N j ^ 2)) := by
  have hsqrt_ne : (Real.sqrt 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hω2 : -((cubeRootOfUnity : ℂ) ^ 2) = twelfthRootOfUnity ^ 2 := by
    rw [← twelfthRootOfUnity_pow_four]
    linear_combination -twelfthRootOfUnity ^ 2 * twelfthRootOfUnity_pow_six
  have h3inv : (Real.sqrt 3 : ℂ) * (3 : ℂ)⁻¹ = (Real.sqrt 3 : ℂ)⁻¹ :=
    mul_left_cancel₀ hsqrt_ne (by
      rw [mul_inv_cancel₀ hsqrt_ne, ← mul_assoc, ← sq, sqrt_three_sq]; norm_num)
  have hc1 : twelfthRootOfUnity * (1 + twelfthRootOfUnity ^ 2) * (3 : ℂ)⁻¹ - twelfthRootOfUnity =
      -(Real.sqrt 3 : ℂ)⁻¹ := mul_left_cancel₀ hsqrt_ne <| by
    rw [mul_neg, mul_inv_cancel₀ hsqrt_ne, one_add_twelfthRootOfUnity_sq]
    linear_combination (twelfthRootOfUnity ^ 2 * (3 : ℂ)⁻¹) * sqrt_three_sq +
      one_add_twelfthRootOfUnity_sq
  have hc2 : twelfthRootOfUnity * (1 + twelfthRootOfUnity ^ 2) * (3 : ℂ)⁻¹ =
      -(Real.sqrt 3 : ℂ)⁻¹ * (cubeRootOfUnity : ℂ) ^ 2 := by
    rw [one_add_twelfthRootOfUnity_sq]
    linear_combination twelfthRootOfUnity ^ 2 * h3inv - (Real.sqrt 3 : ℂ)⁻¹ * hω2
  simp only [gaussianBraidGenerator_def, cubicProjection_def, smul_sub, smul_add, smul_smul,
    ← mul_assoc]
  rw [add_assoc ((twelfthRootOfUnity * (1 + twelfthRootOfUnity ^ 2) * (3 : ℂ)⁻¹) • (1 : _)),
    add_sub_right_comm, ← sub_smul, hc1, hc2]
theorem star_gaussianBraidGenerator_eq_weyl (N : ℕ) (j : Fin N) :
    star (gaussianBraidGenerator N j) =
      -((Real.sqrt 3 : ℂ)⁻¹) •
        (1 + (cubeRootOfUnity : ℂ) • (cubicSite N j + cubicSite N j ^ 2)) := by
  have hωstar : star ((cubeRootOfUnity : ℂ) ^ 2) = (cubeRootOfUnity : ℂ) := by
    rw [star_pow, star_cubeRootOfUnity_val]
    have hmul : ((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ) ^ 2 * (cubeRootOfUnity : ℂ) ^ 2 = 1 := by
      rw [← mul_pow, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_pow]
    linear_combination -((cubeRootOfUnity⁻¹ : ℂˣ) : ℂ) ^ 2 * cubeRootOfUnity_val_pow_three +
      (cubeRootOfUnity : ℂ) * hmul
  rw [gaussianBraidGenerator_eq_weyl, star_smul, star_add, star_one, star_smul, star_add,
    hωstar, star_pow, star_cubicSite, ← pow_mul, show cubicSite N j ^ 4 = cubicSite N j by
      rw [pow_succ, cubicSite_pow_three, one_mul], add_comm (cubicSite N j ^ 2),
    show star (-(Real.sqrt 3 : ℂ)⁻¹) = -(Real.sqrt 3 : ℂ)⁻¹ by simp]
theorem gaussianBraidGenerator_eq_spectral (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j =
      Complex.I • cubicProjection N j + (-twelfthRootOfUnity) • (1 - cubicProjection N j) := by
  rw [gaussianBraidGenerator_def, smul_sub, smul_smul, smul_sub,
    show twelfthRootOfUnity * (1 + twelfthRootOfUnity ^ 2) = Complex.I + twelfthRootOfUnity by
      linear_combination twelfthRootOfUnity_pow_three, add_smul, neg_smul, neg_smul]; abel
private theorem cubicProjection_spectral_mul (N : ℕ) (j : Fin N) (a b c d : ℂ) :
    (a • cubicProjection N j + b • (1 - cubicProjection N j)) *
        (c • cubicProjection N j + d • (1 - cubicProjection N j)) =
      (a * c) • cubicProjection N j + (b * d) • (1 - cubicProjection N j) := by
  have h1 : cubicProjection N j * (1 - cubicProjection N j) = 0 := by
    rw [mul_sub, mul_one, cubicProjection_mul_self, sub_self]
  have h2 : (1 - cubicProjection N j) * cubicProjection N j = 0 := by
    rw [sub_mul, one_mul, cubicProjection_mul_self, sub_self]
  simp only [add_mul, mul_add, smul_mul_smul_comm, cubicProjection_mul_self, h1, h2,
    show (1 - cubicProjection N j) * (1 - cubicProjection N j) = 1 - cubicProjection N j by
      rw [mul_sub, mul_one, h2, sub_zero], smul_zero, add_zero, zero_add]
@[simp] theorem star_gaussianBraidGenerator_mul_self (N : ℕ) (j : Fin N) :
    star (gaussianBraidGenerator N j) * gaussianBraidGenerator N j = 1 := by
  rw [gaussianBraidGenerator_eq_spectral, star_add, star_smul, star_smul, star_sub, star_one,
    star_cubicProjection, star_neg, star_twelfthRootOfUnity, Complex.star_def, Complex.conj_I,
    cubicProjection_spectral_mul, show (-Complex.I) * Complex.I = 1 by simp, neg_mul_neg,
    inv_mul_cancel₀ twelfthRootOfUnity_ne_zero, one_smul, one_smul, add_sub_cancel]
@[simp] theorem gaussianBraidGenerator_mul_star_self (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j * star (gaussianBraidGenerator N j) = 1 := by
  rw [gaussianBraidGenerator_eq_spectral, star_add, star_smul, star_smul, star_sub, star_one,
    star_cubicProjection, star_neg, star_twelfthRootOfUnity, Complex.star_def, Complex.conj_I,
    cubicProjection_spectral_mul, show Complex.I * (-Complex.I) = 1 by simp, neg_mul_neg,
    mul_inv_cancel₀ twelfthRootOfUnity_ne_zero, one_smul, one_smul, add_sub_cancel]
/-- The Gaussian braid generator `g_j`, bundled as a unitary unit in `(CubicTorus N)ˣ`. -/
noncomputable def gaussianBraidUnit (N : ℕ) (j : Fin N) : (CubicTorus N)ˣ where
  val := gaussianBraidGenerator N j
  inv := star (gaussianBraidGenerator N j)
  val_inv := gaussianBraidGenerator_mul_star_self N j
  inv_val := star_gaussianBraidGenerator_mul_self N j
@[simp] theorem gaussianBraidUnit_val (N : ℕ) (j : Fin N) :
    (gaussianBraidUnit N j : CubicTorus N) = gaussianBraidGenerator N j := (rfl)
@[simp] theorem gaussianBraidUnit_inv_val (N : ℕ) (j : Fin N) :
    (((gaussianBraidUnit N j)⁻¹ : (CubicTorus N)ˣ) : CubicTorus N) =
      star (gaussianBraidGenerator N j) := (rfl)
/-- Every Gaussian braid generator cubes to `-i`: `g_j ^ 3 = (-I) • 1`. -/
@[simp] theorem gaussianBraidGenerator_pow_three (N : ℕ) (j : Fin N) :
    gaussianBraidGenerator N j ^ 3 = (-Complex.I) • (1 : CubicTorus N) := by
  rw [gaussianBraidGenerator_eq_spectral, pow_succ, sq, cubicProjection_spectral_mul,
    cubicProjection_spectral_mul, show Complex.I * Complex.I * Complex.I = -Complex.I by
      rw [Complex.I_mul_I]; ring,
    show (-twelfthRootOfUnity) * (-twelfthRootOfUnity) * (-twelfthRootOfUnity) = -Complex.I by
      linear_combination -twelfthRootOfUnity_pow_three, ← smul_add, add_sub_cancel]
/-- Every Gaussian braid unit has order dividing `12`: `g_j ^ 12 = 1`. -/
@[simp] theorem gaussianBraidUnit_pow_twelve (N : ℕ) (j : Fin N) :
    gaussianBraidUnit N j ^ 12 = 1 := by
  apply Units.ext
  have hI4 : (-Complex.I) ^ 4 = 1 := by
    rw [show (-Complex.I) ^ 4 = (Complex.I ^ 2) ^ 2 by ring, Complex.I_sq]; norm_num
  rw [Units.val_pow_eq_pow_val, Units.val_one, gaussianBraidUnit_val,
    show (12 : ℕ) = 3 * 4 by decide, pow_mul, gaussianBraidGenerator_pow_three, smul_pow, one_pow,
    hI4, one_smul]
theorem gaussianBraidUnit_mul_comm {N : ℕ} {i j : Fin N}
    (hij : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    gaussianBraidUnit N i * gaussianBraidUnit N j =
      gaussianBraidUnit N j * gaussianBraidUnit N i := by
  apply Units.ext
  simp only [Units.val_mul, gaussianBraidUnit_val, gaussianBraidGenerator_eq_crossing,
    ← MulMemClass.coe_mul, ← map_mul]
  congr 2; exact crossing_mul_crossing_comm _ _ _ _ hij
theorem gaussianBraidUnit_braid {N : ℕ} {i j : Fin N}
    (hij : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    gaussianBraidUnit N i * gaussianBraidUnit N j * gaussianBraidUnit N i =
      gaussianBraidUnit N j * gaussianBraidUnit N i * gaussianBraidUnit N j := by
  have hcoef : twelfthRootOfUnity ^ 2 * ((-twelfthRootOfUnity) ^ 2 +
      (-twelfthRootOfUnity) * twelfthRootOfUnity ^ 2 * (Real.sqrt 3 : ℂ) +
      (twelfthRootOfUnity ^ 2) ^ 2) = 0 := by
    linear_combination twelfthRootOfUnity ^ 4 * one_add_twelfthRootOfUnity_sq
  apply Units.ext
  simp only [Units.val_mul, gaussianBraidUnit_val, gaussianBraidGenerator_eq_crossing,
    ← MulMemClass.coe_mul, ← map_mul]
  congr 2; exact crossing_braid hcoef hij
/-- The **Gaussian braid representation** `BraidGroup (N + 1) →* (CubicTorus N)ˣ` sending each
elementary braid `BraidGroup.sigma j` to `gaussianBraidUnit N j`. -/
noncomputable def gaussianBraid (N : ℕ) : BraidGroup (N + 1) →* (CubicTorus N)ˣ :=
  BraidGroup.lift (gaussianBraidUnit N) (fun h ↦ gaussianBraidUnit_mul_comm h)
    (fun h ↦ gaussianBraidUnit_braid h)
@[simp] theorem gaussianBraid_sigma (N : ℕ) (j : Fin N) :
    gaussianBraid N (BraidGroup.sigma j) = gaussianBraidUnit N j := BraidGroup.lift_sigma ..
theorem jonesDelta_eq_sqrt_three_of_sq_eq {a : ℂˣ}
    (ha : (a : ℂ) ^ 2 = -twelfthRootOfUnity⁻¹) : jonesDelta a = (Real.sqrt 3 : ℂ) := by
  have hinv : ((a⁻¹ : ℂˣ) : ℂ) ^ 2 = -twelfthRootOfUnity :=
    mul_left_cancel₀ (neg_ne_zero.mpr (inv_ne_zero twelfthRootOfUnity_ne_zero)) <| by
      calc -twelfthRootOfUnity⁻¹ * ((a⁻¹ : ℂˣ) : ℂ) ^ 2
          = ((a : ℂ) * ((a⁻¹ : ℂˣ) : ℂ)) ^ 2 := by rw [← ha, mul_pow]
        _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow]
        _ = -twelfthRootOfUnity⁻¹ * (-twelfthRootOfUnity) := by
          rw [neg_mul_neg, inv_mul_cancel₀ twelfthRootOfUnity_ne_zero]
  rw [jonesDelta_def, ha, hinv]; linear_combination twelfthRootOfUnity_add_inv
theorem cubicFixedHom_crossing_eq_gaussianBraidGenerator (N : ℕ) {a : ℂˣ}
    (ha : (a : ℂ) ^ 2 = -twelfthRootOfUnity⁻¹) (j : Fin N) :
    ((cubicFixedHom (N + 1) (crossing (Real.sqrt 3 : ℂ) (a : ℂ) ((a⁻¹ : ℂˣ) : ℂ) j)).1 :
        CubicTorus N) =
      (-(a : ℂ) / twelfthRootOfUnity) • gaussianBraidGenerator N j := by
  have hinv_a : ((a⁻¹ : ℂˣ) : ℂ) = -(a : ℂ) * twelfthRootOfUnity :=
    mul_left_cancel₀ (Units.ne_zero a) <| by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, ← mul_assoc, mul_neg, ← sq, ha, neg_neg,
        inv_mul_cancel₀ twelfthRootOfUnity_ne_zero]
  rw [crossing_def, map_add, map_smul, map_smul, map_one, AddMemClass.coe_add, SetLike.val_smul,
    SetLike.val_smul, OneMemClass.coe_one, coe_cubicFixedHom_e, gaussianBraidGenerator_def,
    smul_smul, smul_smul, smul_sub, smul_smul, one_add_twelfthRootOfUnity_sq, hinv_a]
  have h1 : -(a : ℂ) / twelfthRootOfUnity * twelfthRootOfUnity = -(a : ℂ) := by
    field_simp [twelfthRootOfUnity_ne_zero]
  rw [show -(a : ℂ) / twelfthRootOfUnity * twelfthRootOfUnity *
      ((Real.sqrt 3 : ℂ) * twelfthRootOfUnity) =
      -(a : ℂ) * twelfthRootOfUnity * (Real.sqrt 3 : ℂ) by rw [h1]; ring,
    h1, neg_smul, sub_neg_eq_add]; exact add_comm _ _

/-! ### Symplectic transvection action on the Weyl basis -/

private theorem cubic_poly_mul {R : Type*} [Ring R] [Algebra ℂ R] {U : R} (hU : U ^ 3 = 1)
    (a₀ a₁ a₂ b₀ b₁ b₂ : ℂ) :
    (a₀ • (1 : R) + a₁ • U + a₂ • U ^ 2) * (b₀ • (1 : R) + b₁ • U + b₂ • U ^ 2) =
      (a₀ * b₀ + a₁ * b₂ + a₂ * b₁) • 1 + (a₀ * b₁ + a₁ * b₀ + a₂ * b₂) • U +
        (a₀ * b₂ + a₁ * b₁ + a₂ * b₀) • U ^ 2 := by
  have h0 : U * U = U ^ 2 := (sq U).symm
  have h1 : U * U ^ 2 = 1 := by rw [← pow_succ', hU]
  have h2 : U ^ 2 * U = 1 := by rw [← pow_succ, hU]
  have h3 : U ^ 2 * U ^ 2 = U := by
    rw [← pow_add, show (2 + 2 : ℕ) = 3 + 1 by decide, pow_succ, hU, one_mul]
  simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, h0, h1, h2, h3]; module
/-- **Conjugation by a Gaussian braid unit acts on the Weyl basis as a symplectic transvection**:
`g_j * W(a) * g_j⁻¹ = W(a + B(a, e_j) • e_j)`. -/
theorem gaussianBraidUnit_conj_weyl (N : ℕ) (j : Fin N) (a : Fin N → ZMod 3) :
    (gaussianBraidUnit N j : CubicTorus N) * weyl N (Multiplicative.ofAdd a) *
        (((gaussianBraidUnit N j)⁻¹ : (CubicTorus N)ˣ) : CubicTorus N) =
      weyl N (Multiplicative.ofAdd (a + chainForm N a (Pi.single j 1) • Pi.single j 1)) := by
  set U : CubicTorus N := cubicSite N j
  set W : CubicTorus N := weyl N (Multiplicative.ofAdd a)
  set ω : ℂ := (cubeRootOfUnity : ℂ)
  have hω3 : ω ^ 3 = 1 := cubeRootOfUnity_val_pow_three
  have hωsum : 1 + ω + ω ^ 2 = 0 := one_add_cubeRootOfUnity_add_sq
  set c : ZMod 3 := chainForm N a (Pi.single j 1)
  set ζ : ℂ := (cubeRootPow (-c) : ℂ)
  have hUW : U * W = ζ • (W * U) := by
    dsimp only [U, W, ζ, c]
    rw [cubicSite_def, weyl_mul_comm_factor, toAdd_ofAdd, toAdd_ofAdd, chainForm_swap]
  have hU2W : U ^ 2 * W = (ζ ^ 2) • (W * U ^ 2) := by
    rw [sq, mul_assoc, hUW, mul_smul_comm, ← mul_assoc, hUW, smul_mul_assoc, smul_smul,
      ← sq, mul_assoc, ← sq]
  have hconj_gen : (gaussianBraidUnit N j : CubicTorus N) * W *
      (((gaussianBraidUnit N j)⁻¹ : (CubicTorus N)ˣ) : CubicTorus N) =
      (3 : ℂ)⁻¹ • (W * (((1 : ℂ) • (1 : CubicTorus N) + (ω ^ 2 * ζ) • U +
          (ω ^ 2 * ζ ^ 2) • U ^ 2) *
        ((1 : ℂ) • (1 : CubicTorus N) + ω • U + ω • U ^ 2))) := by
    have hsqrt_inv : (-(Real.sqrt 3 : ℂ)⁻¹) * (-(Real.sqrt 3 : ℂ)⁻¹) = (3 : ℂ)⁻¹ := by
      rw [neg_mul_neg, ← mul_inv, ← sq, sqrt_three_sq]
    have hpush : gaussianBraidGenerator N j * W = (-(Real.sqrt 3 : ℂ)⁻¹) •
        (W * ((1 : ℂ) • (1 : CubicTorus N) + (ω ^ 2 * ζ) • U + (ω ^ 2 * ζ ^ 2) • U ^ 2)) := by
      rw [gaussianBraidGenerator_eq_weyl]
      simp only [U, ω, one_smul, smul_add, add_mul, mul_add, one_mul, mul_one, hUW, hU2W,
        smul_mul_assoc, mul_smul_comm, smul_smul, add_assoc, mul_assoc]
    rw [gaussianBraidUnit_val, gaussianBraidUnit_inv_val, hpush,
      star_gaussianBraidGenerator_eq_weyl, smul_mul_smul_comm, hsqrt_inv, mul_assoc]
    simp only [U, ω, one_smul, smul_add, add_assoc]
  rw [hconj_gen, cubic_poly_mul (U := U) (cubicSite_pow_three N j)]
  have hU2_weyl : U ^ 2 = weyl N (Multiplicative.ofAdd ((2 : ZMod 3) • Pi.single j 1)) := by
    dsimp only [U]; rw [cubicSite_def, weyl_sq]; congr 1
    apply Multiplicative.toAdd.injective; ext k; simp [show (2 : ZMod 3) = -1 by decide]
  have hclose {k : ZMod 3} (hk : c = k) (hkk : k * k = 1) :
      ω • (W * weyl N (Multiplicative.ofAdd (k • Pi.single j 1))) =
        weyl N (Multiplicative.ofAdd (a + c • Pi.single j 1)) := by
    simp only [W, weyl_mul, smul_smul, ← ofAdd_add, hk]
    rw [show ω * (cubicFactor N (Multiplicative.ofAdd a)
        (Multiplicative.ofAdd (k • Pi.single j 1)) : ℂ) = 1 by
      rw [cubicFactor_def, toAdd_ofAdd, toAdd_ofAdd, chainForm_smul_right,
        show chainForm N a (Pi.single j 1) = k from hk, hkk, mul_one, cubeRootPow_two,
        Units.val_pow_eq_pow_val]; linear_combination hω3, one_smul]
  rcases zmod3_cases c with hc | hc | hc
  · rw [show ζ = 1 by simp [ζ, hc],
      show 1 * 1 + (ω ^ 2 * 1) * ω + (ω ^ 2 * 1 ^ 2) * ω = 3 by linear_combination 2 * hω3,
      show 1 * ω + (ω ^ 2 * 1) * 1 + (ω ^ 2 * 1 ^ 2) * ω = 0 by linear_combination hωsum + hω3,
      show 1 * ω + (ω ^ 2 * 1) * ω + (ω ^ 2 * 1 ^ 2) * 1 = 0 by linear_combination hωsum + hω3]
    simp [W, hc]
  · rw [show ζ = ω ^ 2 by simp [ζ, hc, show (-1 : ZMod 3) = 2 by decide, ω],
      show 1 * 1 + (ω ^ 2 * ω ^ 2) * ω + (ω ^ 2 * (ω ^ 2) ^ 2) * ω = 0 by
        linear_combination hωsum + ω ^ 2 * hω3 + (ω ^ 4 + ω) * hω3,
      show 1 * ω + (ω ^ 2 * ω ^ 2) * 1 + (ω ^ 2 * (ω ^ 2) ^ 2) * ω = 3 * ω by
        linear_combination (ω ^ 4 + ω) * hω3 + ω * hω3,
      show 1 * ω + (ω ^ 2 * ω ^ 2) * ω + (ω ^ 2 * (ω ^ 2) ^ 2) * 1 = 0 by
        linear_combination hωsum + (ω ^ 3 + 1) * hω3 + ω ^ 2 * hω3]
    simp only [zero_smul, zero_add, add_zero, mul_smul_comm, smul_smul]
    rw [show (3 : ℂ)⁻¹ * (3 * ω) = ω by ring,
      show U = weyl N (Multiplicative.ofAdd ((1 : ZMod 3) • Pi.single j 1)) by
        simp [U, cubicSite_def]]
    exact hclose hc (by decide)
  · rw [show ζ = ω by simp [ζ, hc, show (-2 : ZMod 3) = 1 by decide, ω],
      show 1 * 1 + (ω ^ 2 * ω) * ω + (ω ^ 2 * ω ^ 2) * ω = 0 by
        linear_combination hωsum + ω * hω3 + ω ^ 2 * hω3,
      show 1 * ω + (ω ^ 2 * ω) * 1 + (ω ^ 2 * ω ^ 2) * ω = 0 by
        linear_combination hωsum + hω3 + ω ^ 2 * hω3,
      show 1 * ω + (ω ^ 2 * ω) * ω + (ω ^ 2 * ω ^ 2) * 1 = 3 * ω by
        linear_combination ω * hω3 + ω * hω3]
    simp only [zero_smul, zero_add, mul_smul_comm, smul_smul]
    rw [show (3 : ℂ)⁻¹ * (3 * ω) = ω by ring, hU2_weyl]
    exact hclose hc (by decide)

/-! ### Radical of `chainForm N`, center of `CubicTorus N`, and finiteness of the braid image -/

private def oddRadicalVec (N : ℕ) : Fin N → ZMod 3 := fun i ↦ if Even i.val then 1 else 0
private theorem chainForm_radical_step {N : ℕ} {a : Fin N → ZMod 3}
    (ha : ∀ b, chainForm N a b = 0) :
    (∀ i : Fin N, Odd i.val → a i = 0) ∧
    (∀ i : Fin N, Even i.val → a i = a ⟨0, Nat.zero_lt_of_lt i.2⟩) := by
  have h1 : ∀ (n : ℕ) (hn : n < N),
      (Odd n → a ⟨n, hn⟩ = 0) ∧ (Even n → a ⟨n, hn⟩ = a ⟨0, by omega⟩) := by
    intro n; induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn; match n with
      | 0 => exact ⟨fun h ↦ absurd h (by decide), fun _ ↦ rfl⟩
      | 1 =>
        refine ⟨fun _ ↦ ?_, fun h ↦ absurd h (by decide)⟩
        have h0 := ha (Pi.single ⟨0, by omega⟩ 1)
        rw [chainForm_single_right] at h0; simpa [hn] using h0
      | m + 2 =>
        have hmid := ha (Pi.single ⟨m + 1, by omega⟩ 1)
        rw [chainForm_single_right] at hmid
        have heq : a ⟨m + 2, hn⟩ = a ⟨m, by omega⟩ :=
          (sub_eq_zero.mp (by simpa [hn] using hmid)).symm
        obtain ⟨hodd, heven⟩ := ih m (by omega) (by omega)
        exact ⟨fun ⟨k, hk⟩ ↦ heq.trans (hodd ⟨k - 1, by omega⟩),
          fun ⟨k, hk⟩ ↦ heq.trans (heven ⟨k - 1, by omega⟩)⟩
  exact ⟨fun i hi ↦ (h1 i.val i.2).1 hi, fun i hi ↦ (h1 i.val i.2).2 hi⟩
private theorem chainForm_radical_eq_zero_of_even {N : ℕ} (hN : Even N) {a : Fin N → ZMod 3}
    (ha : ∀ b, chainForm N a b = 0) : a = 0 := by
  obtain ⟨hodd, heven⟩ := chainForm_radical_step ha
  ext i; rcases Nat.even_or_odd i.val with hi | hi
  · rw [heven i hi]; obtain ⟨k, hk⟩ := hN; have hiN := i.2
    have hlast := ha (Pi.single ⟨N - 1, by omega⟩ 1); rw [chainForm_single_right] at hlast
    have ha_prev : a ⟨N - 1 - 1, by omega⟩ = 0 := by
      simpa [show 0 < N - 1 by omega, show ¬ (N - 1) + 1 < N by omega] using hlast
    rw [← heven ⟨N - 1 - 1, by omega⟩ ⟨k - 1, by dsimp; omega⟩, ha_prev]; rfl
  · exact hodd i hi
private theorem chainForm_radical_of_odd {N : ℕ} (hN : Odd N) {a : Fin N → ZMod 3}
    (ha : ∀ b, chainForm N a b = 0) :
    a = a ⟨0, by obtain ⟨k, hk⟩ := hN; omega⟩ • oddRadicalVec N := by
  obtain ⟨hodd, heven⟩ := chainForm_radical_step ha
  ext i; simp only [Pi.smul_apply, smul_eq_mul, oddRadicalVec]
  rcases Nat.even_or_odd i.val with hi | hi
  · simp [hi, heven i hi]
  · simp [Nat.not_even_iff_odd.mpr hi, hodd i hi]
private theorem chainForm_oddRadicalVec {N : ℕ} (hN : Odd N) (b : Fin N → ZMod 3) :
    chainForm N (oddRadicalVec N) b = 0 := by
  have hsingle (k : Fin N) : chainForm N (oddRadicalVec N) (Pi.single k 1) = 0 := by
    obtain ⟨m, hm⟩ := hN; rw [chainForm_single_right]
    rcases Nat.even_or_odd k.val with ⟨r, hr⟩ | ⟨r, hr⟩
    · have ho2 : ¬ Even (k.val + 1) := Nat.not_even_iff_odd.mpr ⟨r, by omega⟩
      split_ifs with h1 _ _
      · simp [oddRadicalVec, Nat.not_even_iff_odd.mpr (⟨r - 1, by omega⟩ : Odd (k.val - 1)), ho2]
      · simp [oddRadicalVec, Nat.not_even_iff_odd.mpr (⟨r - 1, by omega⟩ : Odd (k.val - 1))]
      · simp [oddRadicalVec, ho2]
      · simp
    · simp only [show 0 < k.val by omega, show k.val + 1 < N by omega, ↓reduceDIte, oddRadicalVec]
      have h1 : Even (k.val - 1) := ⟨r, by omega⟩; have h2 : Even (k.val + 1) := ⟨r + 1, by omega⟩
      simp [h1, h2]
  rw [show b = ∑ k : Fin N, b k • Pi.single k (1 : ZMod 3) by
    ext i; simp [Finset.sum_apply, Pi.single_apply]]
  have hsum (s : Finset (Fin N)) :
      chainForm N (oddRadicalVec N) (∑ k ∈ s, b k • Pi.single k (1 : ZMod 3)) = 0 := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert k s _ ih =>
      rw [Finset.sum_insert ‹_›, chainForm_add_right, chainForm_smul_right, hsingle k,
        mul_zero, zero_add, ih]
  exact hsum Finset.univ
private theorem mem_radical_of_commute_weyl {N : ℕ} {z : CubicTorus N}
    (hz : ∀ b, z * weyl N b = weyl N b * z) {a : Multiplicative (Fin N → ZMod 3)}
    (ha : (basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)).repr z a ≠ 0) :
    ∀ b : Fin N → ZMod 3, chainForm N a.toAdd b = 0 := by
  intro b; let bM := Multiplicative.ofAdd b
  let bas := basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  let conj : CubicTorus N →ₗ[ℂ] CubicTorus N :=
    (LinearMap.mulRight ℂ (weyl N bM⁻¹)).comp (LinearMap.mulLeft ℂ (weyl N bM))
  have hdiag : (bas.coord a).comp conj =
      (cubeRootPow (chainForm N b a.toAdd) : ℂ) • bas.coord a := bas.ext fun g ↦ by
    classical
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
    change (bas.repr (weyl N bM * bas g * weyl N bM⁻¹)) a = _
    conv_lhs =>
      rw [show bas g = weyl N g by rw [weyl_def]; exact TwistedMonoidAlgebra.basis_apply ..,
        weyl_mul_comm_factor N bM g, smul_mul_assoc, mul_assoc, weyl_mul_weyl_inv, mul_one,
        show weyl N g = bas g by rw [weyl_def]; exact (TwistedMonoidAlgebra.basis_apply ..).symm]
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self,
      Finsupp.single_apply]
    split_ifs with h <;> simp [h, bM]
  have hfix : conj z = z := by
    change weyl N bM * z * weyl N bM⁻¹ = z
    rw [← hz bM, mul_assoc, weyl_mul_weyl_inv, mul_one]
  have heq : bas.repr z a = (cubeRootPow (chainForm N b a.toAdd) : ℂ) * bas.repr z a := by
    simpa [hfix] using LinearMap.congr_fun hdiag z
  have h1 : (cubeRootPow (chainForm N b a.toAdd) : ℂ) = 1 :=
    mul_right_cancel₀ ha (by rw [one_mul, ← heq])
  rw [chainForm_swap, cubeRootPow_eq_one_iff.mp (Units.ext h1), neg_zero]
private theorem finite_pow_eq_one {k : ℕ} (hk : k ≠ 0) : Finite {c : ℂ // c ^ k = 1} := by
  have : NeZero k := ⟨hk⟩
  let toRoot : {c : ℂ // c ^ k = 1} → rootsOfUnity k ℂ := fun c ↦
    ⟨Units.mk0 c.1 fun h0 ↦ (zero_ne_one : (0 : ℂ) ≠ 1) (by simpa [h0, zero_pow hk] using c.2), by
      rw [mem_rootsOfUnity]; exact Units.ext (by simpa using c.2)⟩
  exact Finite.of_injective toRoot fun _ _ hab ↦
    Subtype.ext (by simpa [toRoot] using congrArg (fun u : rootsOfUnity k ℂ ↦ ((u : ℂˣ) : ℂ)) hab)
private theorem eig_pow_eq_one_of_central {N : ℕ} {e : CubicTorus N}
    (hcomm : ∀ x, e * x = x * e)
    (x : Subgroup.closure (Set.range (gaussianBraidUnit N))) {lam : ℂ}
    (heig : x.1.val * e = lam • e) :
    lam ^ (12 * Module.finrank ℂ (LinearMap.range (LinearMap.mulLeft ℂ e))) = 1 := by
  let V := LinearMap.range (LinearMap.mulLeft ℂ e)
  let L : CubicTorus N →ₐ[ℂ] Module.End ℂ V :=
    { toFun := fun y ↦
        { toFun := fun v ↦ ⟨y * v.1, let ⟨w, hw⟩ := v.2
            ⟨y * w, by dsimp at hw ⊢; rw [← hw, ← mul_assoc, hcomm, mul_assoc]⟩⟩
          map_add' := fun _ _ ↦ Subtype.ext (mul_add _ _ _)
          map_smul' := fun _ _ ↦ Subtype.ext (mul_smul_comm _ _ _) }
      map_one' := LinearMap.ext fun _ ↦ Subtype.ext (one_mul _)
      map_mul' := fun _ _ ↦ LinearMap.ext fun _ ↦ Subtype.ext (mul_assoc _ _ _)
      map_zero' := LinearMap.ext fun _ ↦ Subtype.ext (zero_mul _)
      map_add' := fun _ _ ↦ LinearMap.ext fun _ ↦ Subtype.ext (add_mul _ _ _)
      commutes' := fun r ↦ LinearMap.ext fun _ ↦ Subtype.ext (Algebra.smul_def r _).symm }
  let det12 : (CubicTorus N)ˣ →* ℂ :=
    { toFun := fun u ↦ (LinearMap.det (L u.val)) ^ 12, map_one' := by simp,
      map_mul' := fun _ _ ↦ by simp only [Units.val_mul, map_mul, mul_pow] }
  have hle : Subgroup.closure (Set.range (gaussianBraidUnit N)) ≤ det12.ker := by
    rw [Subgroup.closure_le]; rintro _ ⟨j, rfl⟩
    change (LinearMap.det (L (gaussianBraidUnit N j).val)) ^ 12 = 1
    rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, gaussianBraidUnit_pow_twelve,
      Units.val_one, map_one, map_one]
  have hdet : (LinearMap.det (L x.1.val)) ^ 12 = 1 := hle x.2
  have hLx : L x.1.val = lam • LinearMap.id := LinearMap.ext fun ⟨_, ⟨w, hw⟩⟩ ↦ Subtype.ext <| by
    dsimp [L] at hw ⊢; rw [← hw, ← mul_assoc, heig, smul_mul_assoc]
  rw [hLx, LinearMap.det_smul, LinearMap.det_id, mul_one, ← pow_mul, mul_comm] at hdet
  exact hdet
private theorem mem_cubicFixed_of_mem_gaussianBraid {N : ℕ}
    (x : Subgroup.closure (Set.range (gaussianBraidUnit N))) :
    cubicInversion N x.1.val = x.1.val :=
  (Subgroup.closure_le (K := {
      carrier := {u | cubicInversion N u.val = u.val}
      one_mem' := map_one _
      mul_mem' := fun {u v} hu hv ↦ by
        change cubicInversion N (u.val * v.val) = u.val * v.val; rw [map_mul, hu, hv]
      inv_mem' := fun {u} hu ↦ by
        change cubicInversion N u⁻¹.val = u⁻¹.val
        have h : u.val * cubicInversion N u⁻¹.val = 1 := by
          have := congrArg (cubicInversion N) u.val_inv
          rwa [map_mul, map_one, show cubicInversion N u.val = u.val from hu] at this
        simpa [← mul_assoc, ← Units.val_mul] using congrArg (u⁻¹.val * ·) h
    })).mpr (by
      rintro _ ⟨j, rfl⟩; exact mem_cubicFixed.mp (gaussianBraidGenerator_mem_cubicFixed N j)) x.2
private theorem exists_weylPerm_of_mem_gaussianBraid (N : ℕ)
    (x : Subgroup.closure (Set.range (gaussianBraidUnit N))) :
    ∃ σ : Equiv.Perm (Fin N → ZMod 3), ∀ a : Fin N → ZMod 3,
      x.1.val * weyl N (Multiplicative.ofAdd a) * x.1⁻¹.val =
        weyl N (Multiplicative.ofAdd (σ a)) := by
  let S : Subgroup (CubicTorus N)ˣ :=
    { carrier := {u | ∃ σ : Equiv.Perm (Fin N → ZMod 3), ∀ a,
        u.val * weyl N (Multiplicative.ofAdd a) * u⁻¹.val = weyl N (Multiplicative.ofAdd (σ a))}
      one_mem' := ⟨Equiv.refl _, fun _ ↦ by simp⟩
      mul_mem' := fun {u v} ⟨σ, hσ⟩ ⟨τ, hτ⟩ ↦ ⟨τ.trans σ, fun a ↦ by
        simp only [Units.val_mul, mul_inv_rev, Equiv.trans_apply, mul_assoc]
        rw [← mul_assoc v.val, ← mul_assoc (v.val * _), hτ, ← mul_assoc, hσ]⟩
      inv_mem' := fun {u} ⟨σ, hσ⟩ ↦ ⟨σ.symm, fun a ↦ by
        have h := hσ (σ.symm a); rw [Equiv.apply_symm_apply] at h
        have := congrArg (fun t ↦ u⁻¹.val * t * u.val) h.symm
        simpa [mul_assoc, ← Units.val_mul] using this⟩ }
  refine (Subgroup.closure_le (K := S)).mpr (by
    rintro _ ⟨j, rfl⟩
    exact ⟨{ toFun := fun a ↦ a + chainForm N a (Pi.single j 1) • Pi.single j 1
             invFun := fun a ↦ a - chainForm N a (Pi.single j 1) • Pi.single j 1
             left_inv := fun a ↦ by
               dsimp only; rw [chainForm_add_left, chainForm_smul_left, chainForm_self,
                 mul_zero, add_zero, add_sub_cancel_right]
             right_inv := fun a ↦ by
               dsimp only; rw [sub_eq_add_neg, chainForm_add_left, chainForm_neg_left,
                 chainForm_smul_left, chainForm_self, mul_zero, neg_zero, add_zero,
                 ← sub_eq_add_neg, sub_add_cancel] },
      gaussianBraidUnit_conj_weyl N j⟩) x.2
private noncomputable def weylPermHom (N : ℕ) :
    Subgroup.closure (Set.range (gaussianBraidUnit N)) →* Equiv.Perm (Fin N → ZMod 3) :=
  have hinj : Function.Injective (fun a : Fin N → ZMod 3 ↦ weyl N (Multiplicative.ofAdd a)) :=
    fun _ _ hab ↦ Multiplicative.ofAdd.injective <|
      (basis ℂ _ (cubicFactor N)).injective <| by
        simpa [weyl_def, ← TwistedMonoidAlgebra.basis_apply] using hab
  { toFun := fun x ↦ (exists_weylPerm_of_mem_gaussianBraid N x).choose
    map_one' := Equiv.ext fun a ↦ hinj (by
      simpa using ((exists_weylPerm_of_mem_gaussianBraid N 1).choose_spec a).symm)
    map_mul' := fun x y ↦ Equiv.ext fun a ↦ hinj <| by
      dsimp only
      rw [Equiv.Perm.mul_apply, ← (exists_weylPerm_of_mem_gaussianBraid N x).choose_spec _,
        ← (exists_weylPerm_of_mem_gaussianBraid N y).choose_spec a,
        ← (exists_weylPerm_of_mem_gaussianBraid N (x * y)).choose_spec a]
      simp only [Subgroup.coe_mul, Units.val_mul, mul_inv_rev, mul_assoc] }
private theorem weylPermHom_ker_comm {N : ℕ} (z : (weylPermHom N).ker)
    (b : Multiplicative (Fin N → ZMod 3)) : z.1.1.val * weyl N b = weyl N b * z.1.1.val := by
  have hfix : (exists_weylPerm_of_mem_gaussianBraid N z.1).choose b.toAdd = b.toAdd := by
    simpa [weylPermHom] using congrArg (fun σ : Equiv.Perm (Fin N → ZMod 3) ↦ σ b.toAdd) z.2
  have hconj := (exists_weylPerm_of_mem_gaussianBraid N z.1).choose_spec b.toAdd
  rw [hfix, ofAdd_toAdd] at hconj
  simpa [mul_assoc, ← Units.val_mul] using congrArg (· * z.1.1.val) hconj
private theorem finrank_mulLeft_pos {N : ℕ} {e : CubicTorus N} (he : e ≠ 0) :
    0 < Module.finrank ℂ (LinearMap.range (LinearMap.mulLeft ℂ e)) :=
  have : Nontrivial (LinearMap.range (LinearMap.mulLeft ℂ e)) :=
    ⟨⟨⟨e, 1, by simp⟩, 0, fun h ↦ he (congrArg Subtype.val h)⟩⟩
  Module.finrank_pos
private theorem finite_ker_weylPermHom_of_even {N : ℕ} (hN : Even N) :
    Finite (weylPermHom N).ker := by
  let b := basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  have hscalar (z : (weylPermHom N).ker) :
      z.1.1.val = scalarTrace (cubicFactor N) z.1.1.val • (1 : CubicTorus N) := by
    conv_lhs => rw [← b.sum_repr z.1.1.val]
    rw [Finset.sum_eq_single (1 : Multiplicative (Fin N → ZMod 3))]
    · simp [b, TwistedMonoidAlgebra.scalarTrace_apply]
    · intro g _ hg
      suffices b.repr z.1.1.val g = 0 by rw [this, zero_smul]
      by_contra hne
      exact hg (Multiplicative.toAdd.injective (by
        simpa using chainForm_radical_eq_zero_of_even hN
          (mem_radical_of_commute_weyl (weylPermHom_ker_comm z) hne)))
    · simp
  have h1 : (1 : CubicTorus N) ≠ 0 := fun h0 ↦ by
    have := congrArg (scalarTrace (cubicFactor N)) h0; simp at this
  let d := 12 * Module.finrank ℂ (LinearMap.range (LinearMap.mulLeft ℂ (1 : CubicTorus N)))
  have : Finite {c : ℂ // c ^ d = 1} :=
    finite_pow_eq_one (mul_ne_zero (by decide) (finrank_mulLeft_pos h1).ne')
  let toScalar : (weylPermHom N).ker → {c : ℂ // c ^ d = 1} := fun z ↦
    ⟨scalarTrace (cubicFactor N) z.1.1.val,
      eig_pow_eq_one_of_central (fun _ ↦ by simp) z.1 (by simpa using hscalar z)⟩
  refine Finite.of_injective toScalar fun z₁ z₂ h ↦ Subtype.ext <| Subtype.ext <| Units.ext <| by
    have hc : scalarTrace (cubicFactor N) z₁.1.1.val = scalarTrace (cubicFactor N) z₂.1.1.val :=
      congrArg Subtype.val h
    rw [hscalar z₁, hscalar z₂, hc]
private noncomputable def oddProj (N : ℕ) : CubicTorus N :=
  let R := weyl N (Multiplicative.ofAdd (oddRadicalVec N))
  (3 : ℂ)⁻¹ • (1 + R + R ^ 2)
private theorem odd_linear_combo {M : Type*} [AddCommGroup M] [Module ℂ M]
    (u p : M) (c₀ c₁ : ℂ) :
    c₀ • u + c₁ • ((3 : ℂ) • p - u) = (c₀ + 2 * c₁) • p + (c₀ - c₁) • (u - p) := by module
private theorem oddRad_comm {N : ℕ} (hN : Odd N) (x : CubicTorus N) :
    weyl N (Multiplicative.ofAdd (oddRadicalVec N)) * x =
      x * weyl N (Multiplicative.ofAdd (oddRadicalVec N)) :=
  let R := weyl N (Multiplicative.ofAdd (oddRadicalVec N))
  LinearMap.congr_fun ((basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)).ext fun g ↦ by
    simp only [LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      TwistedMonoidAlgebra.basis_apply, ← weyl_def, R]
    rw [weyl_mul_comm_factor, toAdd_ofAdd, chainForm_oddRadicalVec hN, cubeRootPow_zero,
      Units.val_one, one_smul] : LinearMap.mulLeft ℂ R = LinearMap.mulRight ℂ R) x
private theorem oddProj_mul_self (N : ℕ) : oddProj N * oddProj N = oddProj N := by
  let R := weyl N (Multiplicative.ofAdd (oddRadicalVec N))
  have hPdef : oddProj N = (3 : ℂ)⁻¹ • (1 + R + R ^ 2) := rfl
  have hR_P : R * oddProj N = oddProj N := by
    rw [hPdef, mul_smul_comm]; congr 1
    rw [mul_add, mul_add, mul_one, ← sq, ← pow_succ', weyl_pow_three,
      add_comm (R + R ^ 2), ← add_assoc]
  conv_lhs => arg 1; rw [hPdef]
  rw [smul_mul_assoc, add_mul, add_mul, one_mul, hR_P, sq, mul_assoc, hR_P, hR_P,
    show oddProj N + oddProj N + oddProj N = (3 : ℂ) • oddProj N by
      rw [show (3 : ℂ) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul], smul_smul]
  norm_num
private theorem oddProj_comm {N : ℕ} (hN : Odd N) (x : CubicTorus N) :
    oddProj N * x = x * oddProj N := by
  let R := weyl N (Multiplicative.ofAdd (oddRadicalVec N))
  have hR : R * x = x * R := oddRad_comm hN x
  have hR2 : R ^ 2 * x = x * R ^ 2 := by rw [sq, mul_assoc, hR, ← mul_assoc, hR, mul_assoc]
  rw [show oddProj N = (3 : ℂ)⁻¹ • (1 + R + R ^ 2) from rfl]
  simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, one_mul, mul_one, hR, hR2]
private theorem odd_ker_decomp {N : ℕ} (hN : Odd N) (z : (weylPermHom N).ker) :
    let b := basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
    let gρ := Multiplicative.ofAdd (oddRadicalVec N)
    z.1.1.val = (b.repr z.1.1.val 1 + 2 * b.repr z.1.1.val gρ) • oddProj N +
      (b.repr z.1.1.val 1 - b.repr z.1.1.val gρ) • (1 - oddProj N) := by
  intro b gρ; let x := z.1.1.val; let R : CubicTorus N := weyl N gρ
  have hgρ_ne : gρ ≠ 1 := fun h ↦ by
    obtain ⟨k, hk⟩ := hN; have := congrFun (congrArg Multiplicative.toAdd h) ⟨0, by omega⟩
    simp [gρ, oddRadicalVec] at this
  have hinv_eq : b.repr x gρ⁻¹ = b.repr x gρ := by
    have h1 : scalarTrace (cubicFactor N) (x * weyl N gρ⁻¹) = b.repr x gρ := by
      simpa [weyl_def, b] using TwistedMonoidAlgebra.scalarTrace_mul_of_inv (cubicFactor N) x gρ
    have h2 : scalarTrace (cubicFactor N) (x * weyl N gρ) = b.repr x gρ⁻¹ := by
      simpa [weyl_def, b, inv_inv] using
        TwistedMonoidAlgebra.scalarTrace_mul_of_inv (cubicFactor N) x gρ⁻¹
    rw [← h2, ← h1, ← scalarTrace_cubicInversion N (x * weyl N gρ), map_mul,
      mem_cubicFixed_of_mem_gaussianBraid z.1, cubicInversion_weyl]
  have h12 : gρ ≠ gρ⁻¹ := fun h ↦ by
    obtain ⟨k, hk⟩ := hN
    exact absurd (by
      simpa [gρ, oddRadicalVec] using congrFun (congrArg Multiplicative.toAdd h) ⟨0, by omega⟩ :
      (1 : ZMod 3) = -1) (by decide)
  have hsum : x = b.repr x 1 • (1 : CubicTorus N) + b.repr x gρ • R + b.repr x gρ • R ^ 2 := by
    conv_lhs => rw [← b.sum_repr x]
    rw [← Finset.sum_subset (Finset.subset_univ ({1, gρ, gρ⁻¹} : Finset _))]
    · rw [Finset.sum_insert (by simp [hgρ_ne.symm, (inv_ne_one.mpr hgρ_ne).symm]),
        Finset.sum_insert (by simp [h12]), Finset.sum_singleton, hinv_eq]
      simp [b, R, ← weyl_def, weyl_sq, add_assoc]
    · intro g _ hg
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hg
      suffices b.repr x g = 0 by rw [this, zero_smul]
      by_contra hne
      have hmul := chainForm_radical_of_odd hN
        (mem_radical_of_commute_weyl (weylPermHom_ker_comm z) hne)
      rcases zmod3_cases (g.toAdd ⟨0, by obtain ⟨k, hk⟩ := hN; omega⟩) with ht | ht | ht
      · exact hg.1 (Multiplicative.toAdd.injective (by simpa [ht] using hmul))
      · exact hg.2.1 (Multiplicative.toAdd.injective (by simpa [gρ, ht] using hmul))
      · exact hg.2.2 (Multiplicative.toAdd.injective (by
          rw [ht, show (2 : ZMod 3) = -1 by decide, neg_one_smul] at hmul; simpa [gρ] using hmul))
  have hRsum : R + R ^ 2 = (3 : ℂ) • oddProj N - 1 := by
    have h3 : (3 : ℂ) • oddProj N = 1 + (R + R ^ 2) := by
      rw [show oddProj N = (3 : ℂ)⁻¹ • (1 + R + R ^ 2) from rfl, smul_smul, add_assoc]; norm_num
    rw [h3, add_sub_cancel_left]
  calc x = b.repr x 1 • (1 : CubicTorus N) + b.repr x gρ • R + b.repr x gρ • R ^ 2 := hsum
    _ = b.repr x 1 • (1 : CubicTorus N) + b.repr x gρ • (R + R ^ 2) := by rw [add_assoc, ← smul_add]
    _ = b.repr x 1 • (1 : CubicTorus N) + b.repr x gρ • ((3 : ℂ) • oddProj N - 1) := by rw [hRsum]
    _ = _ := odd_linear_combo 1 (oddProj N) (b.repr x 1) (b.repr x gρ)
private theorem finite_ker_weylPermHom_of_odd {N : ℕ} (hN : Odd N) :
    Finite (weylPermHom N).ker := by
  let b := basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  let gρ := Multiplicative.ofAdd (oddRadicalVec N)
  have hgρ_ne : gρ ≠ 1 := fun h ↦ by
    obtain ⟨k, hk⟩ := hN; have := congrFun (congrArg Multiplicative.toAdd h) ⟨0, by omega⟩
    simp [gρ, oddRadicalVec] at this
  have htrP : scalarTrace (cubicFactor N) (oddProj N) = (3 : ℂ)⁻¹ := by
    rw [show oddProj N = (3 : ℂ)⁻¹ • (1 + weyl N gρ + weyl N gρ ^ 2) from rfl,
      map_smul, map_add, map_add, TwistedMonoidAlgebra.scalarTrace_one, weyl_sq N gρ,
      weyl_def, weyl_def, TwistedMonoidAlgebra.scalarTrace_of_ne_one _ hgρ_ne,
      TwistedMonoidAlgebra.scalarTrace_of_ne_one _ (inv_ne_one.mpr hgρ_ne), smul_eq_mul]; norm_num
  have hP_ne : oddProj N ≠ 0 := fun h ↦ by
    have := congrArg (scalarTrace (cubicFactor N)) h; rw [htrP, map_zero] at this; norm_num at this
  have hQ_ne : 1 - oddProj N ≠ 0 := fun h ↦ by
    have := congrArg (scalarTrace (cubicFactor N)) h
    rw [map_sub, TwistedMonoidAlgebra.scalarTrace_one, htrP, map_zero] at this; norm_num at this
  have hP_comm := oddProj_comm hN
  have hQ_comm (x : CubicTorus N) : (1 - oddProj N) * x = x * (1 - oddProj N) := by
    rw [sub_mul, mul_sub, one_mul, mul_one, hP_comm]
  have hP_sq := oddProj_mul_self N
  have hPQ : oddProj N * (1 - oddProj N) = 0 := by rw [mul_sub, mul_one, hP_sq, sub_self]
  have hQP : (1 - oddProj N) * oddProj N = 0 := by rw [sub_mul, one_mul, hP_sq, sub_self]
  have hQ_sq : (1 - oddProj N) * (1 - oddProj N) = 1 - oddProj N := by
    rw [mul_sub, mul_one, hQP, sub_zero]
  let d₁ := 12 * Module.finrank ℂ (LinearMap.range (LinearMap.mulLeft ℂ (oddProj N)))
  let d₂ := 12 * Module.finrank ℂ (LinearMap.range (LinearMap.mulLeft ℂ (1 - oddProj N)))
  have : Finite {w : ℂ // w ^ d₁ = 1} :=
    finite_pow_eq_one (mul_ne_zero (by decide) (finrank_mulLeft_pos hP_ne).ne')
  have : Finite {w : ℂ // w ^ d₂ = 1} :=
    finite_pow_eq_one (mul_ne_zero (by decide) (finrank_mulLeft_pos hQ_ne).ne')
  let cP (z : (weylPermHom N).ker) : ℂ := b.repr z.1.1.val 1 + 2 * b.repr z.1.1.val gρ
  let cQ (z : (weylPermHom N).ker) : ℂ := b.repr z.1.1.val 1 - b.repr z.1.1.val gρ
  let f : (weylPermHom N).ker → {w : ℂ // w ^ d₁ = 1} × {w : ℂ // w ^ d₂ = 1} := fun z ↦
    (⟨cP z, eig_pow_eq_one_of_central hP_comm z.1 (by
        have hd : z.1.1.val = cP z • oddProj N + cQ z • (1 - oddProj N) := odd_ker_decomp hN z
        rw [hd, add_mul, smul_mul_assoc, smul_mul_assoc, hP_sq, hQP, smul_zero, add_zero])⟩,
     ⟨cQ z, eig_pow_eq_one_of_central hQ_comm z.1 (by
        have hd : z.1.1.val = cP z • oddProj N + cQ z • (1 - oddProj N) := odd_ker_decomp hN z
        rw [hd, add_mul, smul_mul_assoc, smul_mul_assoc, hPQ, hQ_sq, smul_zero, zero_add])⟩)
  refine Finite.of_injective f fun z₁ z₂ h ↦ Subtype.ext <| Subtype.ext <| Units.ext ?_
  have h1 : cP z₁ = cP z₂ := congrArg (fun p ↦ p.1.1) h
  have h2 : cQ z₁ = cQ z₂ := congrArg (fun p ↦ p.2.1) h
  calc z₁.1.1.val = cP z₁ • oddProj N + cQ z₁ • (1 - oddProj N) := odd_ker_decomp hN z₁
    _ = cP z₂ • oddProj N + cQ z₂ • (1 - oddProj N) := by rw [h1, h2]
    _ = z₂.1.1.val := (odd_ker_decomp hN z₂).symm
/-- **Finiteness of the subgroup generated by the Gaussian braid units** in `(CubicTorus N)ˣ`. -/
theorem finite_subgroup_closure_gaussianBraidUnit (N : ℕ) :
    Finite (Subgroup.closure (Set.range (gaussianBraidUnit N))) :=
  (weylPermHom N).finite_iff_finite_ker_range.mpr
    ⟨(Nat.even_or_odd N).elim finite_ker_weylPermHom_of_even finite_ker_weylPermHom_of_odd,
      inferInstance⟩
/-- **The Gaussian braid image is finite.** For every `N : ℕ`, the Gaussian braid generators
`g_j = gaussianBraidGenerator N j` are units of `CubicTorus N` and generate a finite subgroup of
`(CubicTorus N)ˣ`. -/
theorem finite_gaussianBraid_closure (N : ℕ) :
    ∃ g : Fin N → (CubicTorus N)ˣ,
      (∀ j, (g j : CubicTorus N) = gaussianBraidGenerator N j) ∧
        Finite (Subgroup.closure (Set.range g)) :=
  ⟨gaussianBraidUnit N, gaussianBraidUnit_val N, finite_subgroup_closure_gaussianBraidUnit N⟩

end TauCeti.TemperleyLieb
