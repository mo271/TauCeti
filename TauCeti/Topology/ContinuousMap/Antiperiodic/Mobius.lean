/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Projection
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.ScalarChange
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.Topology.Circle.AddCircle
public import TauCeti.Topology.ContinuousMap.Antiperiodic.Basic
import Mathlib.Topology.Instances.Matrix
import TauCeti.Algebra.Module.Projective.Complement

/-!
# The Möbius section module over `C(AddCircle 1, ℝ)` and its complexification

Let `T = AddCircle (1 : ℝ)` be the real additive unit circle `ℝ / ℤ`, with continuous function
rings `R_ℝ = C(T, ℝ)` and `R_ℂ = C(T, ℂ)`. Continuous `1`-antiperiodic functions
`TauCeti.ContinuousAntiperiodicMap 1 ℝ` form the continuous section module of the real Möbius line
bundle over `T`.

Setting `u(t) = (cos(π t), sin(π t))` (`TauCeti.mobiusUnit`), the outer product
`p([t]) = u(t) u(t)ᵀ` descends to a symmetric rank-one idempotent matrix `TauCeti.mobiusProj` in
`Matrix (Fin 2) (Fin 2) R_ℝ` whose associated reflection `ρ = 2 p - 1` (`TauCeti.mobiusRefl`) has
entries built from the circle coordinates `TauCeti.circleCoord 0` (`[t] ↦ cos(2 π t)`) and
`TauCeti.circleCoord 1` (`[t] ↦ sin(2 π t)`). The reflection's fixed-point submodule
`TauCeti.mobiusSections` in `Fin 2 → R_ℝ` coincides with `LinearMap.ker (1 - p.mulVecLin)` and with
`LinearMap.range p.mulVecLin`, making it a finitely generated projective `R_ℝ`-module. Sending an
antiperiodic function `v` to `[t] ↦ v(t) u(t)` gives an explicit `R_ℝ`-linear isomorphism
`TauCeti.antiperiodicEquivMobiusSections : ContinuousAntiperiodicMap 1 ℝ ≃ₗ[R_ℝ] mobiusSections`
preserving the `R_ℝ`-valued pointwise inner product, while the orthonormal half-turn frame
`(u(t), u_⊥(t))` (`u_⊥(t) = (-sin(π t), cos(π t))`, `TauCeti.mobiusOrth`) yields the doubled
splitting `M ⊕ M ≃ₗ[R_ℝ] R_ℝ²` (`TauCeti.mobiusSectionsProdEquiv`).

Despite `M ⊕ M ≃ R_ℝ²`, `M` is neither free nor stably free: for every `N : ℕ` there is no
`R_ℝ`-linear isomorphism `M ⊕ R_ℝᴺ ≃ R_ℝᴺ⁺¹` (`TauCeti.mobiusSections_order_two`). Pulling back a
putative basis of `M ⊕ R_ℝᴺ` to `ℝ` produces a continuous `(N + 1) × (N + 1)` matrix function `B`
that is invertible at every `t ∈ ℝ` and satisfies `B(t + 1) = diag(-1, 1, …, 1) B(t)`, making
`t ↦ det(B(t))` a continuous nowhere-zero `1`-antiperiodic real function, contradicting the
intermediate-value zero theorem. Consequently, the reduced projective `K₀` class
`η = [M] - [R_ℝ]` (`TauCeti.mobiusK0Class`) has exact additive order `2`.

Over `ℂ`, the unit-modulus `1`-antiperiodic character `χ(t) = exp(π i t)` (`TauCeti.mobiusChar`)
gives an isometric `R_ℂ`-linear isomorphism `R_ℂ ≃ₗ[R_ℂ] ContinuousAntiperiodicMap 1 ℂ`
(`TauCeti.continuousMapEquivAntiperiodicComplex`). Along the pointwise real-to-complex ring
homomorphism `TauCeti.circleRealToComplex : R_ℝ →+* R_ℂ`, the balanced scalar extension
`TauCeti.BalancedExtension` of `ContinuousAntiperiodicMap 1 ℝ` (and of `mobiusSections`) is
canonically isomorphic to `ContinuousAntiperiodicMap 1 ℂ`, so the induced map `K₀(R_ℝ) → K₀(R_ℂ)`
annihilates `η` (`TauCeti.map_mobiusK0Class_complex_eq_zero`).

## Main definitions

* `TauCeti.circleCoord`: the coordinate functions `[t] ↦ cos(2 π t)` and `[t] ↦ sin(2 π t)` in
  `C(AddCircle (1 : ℝ), ℝ)`.
* `TauCeti.mobiusProj`, `TauCeti.mobiusRefl`: the rank-one symmetric idempotent `p([t]) = u(t)u(t)ᵀ`
  and reflection `ρ = 2 p - 1` in `Matrix (Fin 2) (Fin 2) C(AddCircle (1 : ℝ), ℝ)`.
* `TauCeti.mobiusSections`: the Möbius submodule `ker(ρ - 1) ≤ (Fin 2 → C(AddCircle (1 : ℝ), ℝ))`.
* `TauCeti.antiperiodicEquivMobiusSections`: the `C(AddCircle (1 : ℝ), ℝ)`-linear isomorphism
  `ContinuousAntiperiodicMap 1 ℝ ≃ₗ mobiusSections`.
* `TauCeti.antiperiodicProdEquiv`, `TauCeti.mobiusSectionsProdEquiv`: the doubled splittings
  `M ⊕ M ≃ₗ C(AddCircle (1 : ℝ), ℝ)²`.
* `TauCeti.mobiusK0Class`: the reduced class `[mobiusSections] - [R_ℝ]` in projective `K₀`.
* `TauCeti.mobiusChar`, `TauCeti.continuousMapEquivAntiperiodicComplex`,
  `TauCeti.balancedExtensionAntiperiodicComplexEquiv`: the complex antiperiodic character
  `χ(t) = exp(π i t)`, the isometric trivialization `R_ℂ ≃ₗ M_ℂ`, and the balanced complexification
  isomorphism `R_ℂ ⊗_{R_ℝ} M_ℝ ≃ₗ M_ℂ`.

## Main results

* `TauCeti.mobiusSections_order_two`: `mobiusSections × mobiusSections ≃ₗ R_ℝ²`, and
  `IsEmpty ((mobiusSections × (Fin N → R_ℝ)) ≃ₗ (Fin (N + 1) → R_ℝ))` for every `N : ℕ`.
* `TauCeti.not_free_continuousAntiperiodicMap_real`, `TauCeti.not_free_mobiusSections`: neither
  carrier is free over `C(AddCircle (1 : ℝ), ℝ)`.
* `TauCeti.addOrderOf_mobiusK0Class`: the reduced class `[M] - [R_ℝ]` has exact additive order `2`
  in `K₀(R_ℝ)`.
* `TauCeti.map_mobiusK0Class_complex_eq_zero`: complexification sends `mobiusK0Class` to `0`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter I, (4.9.1).
-/

public section

namespace TauCeti

open CategoryTheory Matrix

noncomputable section

section CircleCoordinatesAndFrame

/-- The functions `[t] ↦ cos(2 π t)` and `[t] ↦ sin(2 π t)` on the additive unit circle
`AddCircle (1 : ℝ)`, obtained as the real and imaginary parts of `AddCircle.toCircle`. -/
noncomputable def circleCoord (i : Fin 2) : C(AddCircle (1 : ℝ), ℝ) :=
  ⟨fun x => if i = 0 then (AddCircle.toCircle x : ℂ).re else (AddCircle.toCircle x : ℂ).im,
    continuous_if_const _
      (fun _ => Complex.continuous_re.comp
        (continuous_induced_dom.comp AddCircle.continuous_toCircle))
      (fun _ => Complex.continuous_im.comp
        (continuous_induced_dom.comp AddCircle.continuous_toCircle))⟩

@[simp]
theorem circleCoord_zero_apply (x : AddCircle (1 : ℝ)) :
    circleCoord 0 x = (AddCircle.toCircle x : ℂ).re :=
  (rfl)

@[simp]
theorem circleCoord_one_apply (x : AddCircle (1 : ℝ)) :
    circleCoord 1 x = (AddCircle.toCircle x : ℂ).im :=
  (rfl)

theorem circleCoord_zero_coe (t : ℝ) :
    circleCoord 0 (t : AddCircle (1 : ℝ)) = Real.cos (2 * Real.pi * t) := by
  rw [circleCoord_zero_apply, AddCircle.re_toCircle_coe, div_one]

theorem circleCoord_one_coe (t : ℝ) :
    circleCoord 1 (t : AddCircle (1 : ℝ)) = Real.sin (2 * Real.pi * t) := by
  rw [circleCoord_one_apply, AddCircle.im_toCircle_coe, div_one]

theorem circleCoord_sq_add_sq : circleCoord 0 ^ 2 + circleCoord 1 ^ 2 = 1 := by
  ext x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  simp [Real.cos_sq_add_sin_sq]

/-- The half-turn unit vector `u(t) = (cos(π t), sin(π t))` on `ℝ`, whose sign reverses upon
advancing `t` by `1`. -/
def mobiusUnit (t : ℝ) : Fin 2 → ℝ :=
  ![Real.cos (Real.pi * t), Real.sin (Real.pi * t)]

/-- The complementary half-turn unit vector `u_⊥(t) = (-sin(π t), cos(π t))` orthogonal to
`mobiusUnit t`. -/
def mobiusOrth (t : ℝ) : Fin 2 → ℝ :=
  ![-Real.sin (Real.pi * t), Real.cos (Real.pi * t)]

@[simp] theorem mobiusUnit_zero (t : ℝ) : mobiusUnit t 0 = Real.cos (Real.pi * t) := (rfl)
@[simp] theorem mobiusUnit_one (t : ℝ) : mobiusUnit t 1 = Real.sin (Real.pi * t) := (rfl)
@[simp] theorem mobiusOrth_zero (t : ℝ) : mobiusOrth t 0 = -Real.sin (Real.pi * t) := (rfl)
@[simp] theorem mobiusOrth_one (t : ℝ) : mobiusOrth t 1 = Real.cos (Real.pi * t) := (rfl)

theorem continuous_mobiusUnit_apply (i : Fin 2) : Continuous fun t ↦ mobiusUnit t i := by
  revert i
  rw [Fin.forall_fin_two]
  exact ⟨Real.continuous_cos.comp (continuous_const.mul continuous_id),
    Real.continuous_sin.comp (continuous_const.mul continuous_id)⟩

theorem continuous_mobiusOrth_apply (i : Fin 2) : Continuous fun t ↦ mobiusOrth t i := by
  revert i
  rw [Fin.forall_fin_two]
  exact ⟨(Real.continuous_sin.comp (continuous_const.mul continuous_id)).neg,
    Real.continuous_cos.comp (continuous_const.mul continuous_id)⟩

theorem antiperiodic_mobiusUnit_apply (i : Fin 2) :
    Function.Antiperiodic (fun t ↦ mobiusUnit t i) 1 := by
  revert i
  rw [Fin.forall_fin_two]
  refine ⟨fun t ↦ ?_, fun t ↦ ?_⟩
  · dsimp only
    rw [mobiusUnit_zero, mobiusUnit_zero, mul_add, mul_one, Real.cos_add_pi]
  · dsimp only
    rw [mobiusUnit_one, mobiusUnit_one, mul_add, mul_one, Real.sin_add_pi]

theorem antiperiodic_mobiusOrth_apply (i : Fin 2) :
    Function.Antiperiodic (fun t ↦ mobiusOrth t i) 1 := by
  revert i
  rw [Fin.forall_fin_two]
  refine ⟨fun t ↦ ?_, fun t ↦ ?_⟩
  · dsimp only
    rw [mobiusOrth_zero, mobiusOrth_zero, mul_add, mul_one, Real.sin_add_pi]
  · dsimp only
    rw [mobiusOrth_one, mobiusOrth_one, mul_add, mul_one, Real.cos_add_pi]

theorem mobiusUnit_sq_add_sq (t : ℝ) :
    mobiusUnit t 0 * mobiusUnit t 0 + mobiusUnit t 1 * mobiusUnit t 1 = 1 := by
  simpa only [mobiusUnit_zero, mobiusUnit_one, sq] using Real.cos_sq_add_sin_sq (Real.pi * t)

/-- Shifted cosine `s ↦ cos(π (s - t₀))`, a continuous `1`-antiperiodic real function taking the
value `1` at `t₀`. -/
def mobiusShiftedCos (t₀ : ℝ) : ContinuousAntiperiodicMap 1 ℝ where
  toFun s := Real.cos (Real.pi * (s - t₀))
  continuous_toFun :=
    Real.continuous_cos.comp (continuous_const.mul (continuous_id.sub continuous_const))
  antiperiodic' s := by
    dsimp only
    have harg : Real.pi * (s + 1 - t₀) = Real.pi * (s - t₀) + Real.pi := by ring
    rw [harg, Real.cos_add_pi]

@[simp]
theorem mobiusShiftedCos_apply (t₀ s : ℝ) :
    mobiusShiftedCos t₀ s = Real.cos (Real.pi * (s - t₀)) :=
  (rfl)

theorem mobiusShiftedCos_self (t₀ : ℝ) : mobiusShiftedCos t₀ t₀ = 1 := by
  rw [mobiusShiftedCos_apply, sub_self, mul_zero, Real.cos_zero]

/-- The rank-one symmetric projection matrix `p([t]) = u(t) u(t)ᵀ` in
`Matrix (Fin 2) (Fin 2) C(AddCircle (1 : ℝ), ℝ)`, descended from `mobiusUnit` by `1`-periodicity of
`t ↦ uᵢ(t) uⱼ(t)`. -/
def mobiusProj : Matrix (Fin 2) (Fin 2) C(AddCircle (1 : ℝ), ℝ) :=
  Matrix.of fun i j ↦
    ((antiperiodic_mobiusUnit_apply i).mul (antiperiodic_mobiusUnit_apply j)).liftContinuousMap
      ((continuous_mobiusUnit_apply i).mul (continuous_mobiusUnit_apply j))

@[simp]
theorem mobiusProj_apply_coe (i j : Fin 2) (t : ℝ) :
    mobiusProj i j (t : AddCircle (1 : ℝ)) = mobiusUnit t i * mobiusUnit t j := by
  simp [mobiusProj]

theorem isSymm_mobiusProj : mobiusProj.IsSymm := by
  ext i j x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  simp [mul_comm]

theorem isIdempotentElem_mobiusProj : IsIdempotentElem mobiusProj := by
  ext i j x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  simp only [Matrix.mul_apply, Fin.sum_univ_two, ContinuousMap.add_apply, ContinuousMap.mul_apply,
    mobiusProj_apply_coe]
  calc
    mobiusUnit t i * mobiusUnit t 0 * (mobiusUnit t 0 * mobiusUnit t j) +
        mobiusUnit t i * mobiusUnit t 1 * (mobiusUnit t 1 * mobiusUnit t j)
      = mobiusUnit t i * (mobiusUnit t 0 * mobiusUnit t 0 + mobiusUnit t 1 * mobiusUnit t 1) *
          mobiusUnit t j := by ring
    _ = mobiusUnit t i * mobiusUnit t j := by rw [mobiusUnit_sq_add_sq, mul_one]

@[simp]
theorem trace_mobiusProj : mobiusProj.trace = 1 := by
  ext x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hcs := Real.cos_sq_add_sin_sq (Real.pi * t)
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, ContinuousMap.add_apply,
    mobiusProj_apply_coe, mobiusUnit_zero, mobiusUnit_one, ContinuousMap.one_apply]
  linarith

@[simp]
theorem det_mobiusProj : mobiusProj.det = 0 := by
  ext x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  simp only [Matrix.det_fin_two, ContinuousMap.sub_apply, ContinuousMap.mul_apply,
    mobiusProj_apply_coe, ContinuousMap.zero_apply]
  ring

/-- The reflection matrix `ρ([t]) = [[cos(2 π t), sin(2 π t)], [sin(2 π t), -cos(2 π t)]]` in
`Matrix (Fin 2) (Fin 2) C(AddCircle (1 : ℝ), ℝ)` whose `+1`-eigenspace is `mobiusSections`. -/
def mobiusRefl : Matrix (Fin 2) (Fin 2) C(AddCircle (1 : ℝ), ℝ) :=
  !![circleCoord 0, circleCoord 1; circleCoord 1, -circleCoord 0]

theorem mobiusRefl_def :
    mobiusRefl = !![circleCoord 0, circleCoord 1; circleCoord 1, -circleCoord 0] :=
  (rfl)

@[simp] theorem mobiusRefl_zero_zero : mobiusRefl 0 0 = circleCoord 0 := (rfl)
@[simp] theorem mobiusRefl_zero_one : mobiusRefl 0 1 = circleCoord 1 := (rfl)
@[simp] theorem mobiusRefl_one_zero : mobiusRefl 1 0 = circleCoord 1 := (rfl)
@[simp] theorem mobiusRefl_one_one : mobiusRefl 1 1 = -circleCoord 0 := (rfl)

/-- Double-angle relation `ρ = 2 p - 1` linking the reflection `mobiusRefl` and the rank-one
idempotent `mobiusProj`. -/
theorem two_smul_mobiusProj_sub_one : (2 : ℝ) • mobiusProj - 1 = mobiusRefl := by
  ext i j x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  have h2 : 2 * Real.pi * t = 2 * (Real.pi * t) := by ring
  have hcs := Real.cos_sq_add_sin_sq (Real.pi * t)
  revert i j
  rw [Fin.forall_fin_two, Fin.forall_fin_two, Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simp only [Matrix.sub_apply, Matrix.smul_apply, ContinuousMap.sub_apply,
      ContinuousMap.smul_apply, smul_eq_mul, mobiusProj_apply_coe, mobiusUnit_zero,
      Matrix.one_apply_eq, ContinuousMap.one_apply, mobiusRefl_zero_zero, circleCoord_zero_coe, h2,
      Real.cos_two_mul]
    ring
  · simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne Fin.zero_ne_one, sub_zero,
      ContinuousMap.smul_apply, smul_eq_mul, mobiusProj_apply_coe, mobiusUnit_zero, mobiusUnit_one,
      mobiusRefl_zero_one, circleCoord_one_coe, h2, Real.sin_two_mul]
    ring
  · simp only [Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply_ne (Ne.symm Fin.zero_ne_one), sub_zero, ContinuousMap.smul_apply,
      smul_eq_mul, mobiusProj_apply_coe, mobiusUnit_zero, mobiusUnit_one, mobiusRefl_one_zero,
      circleCoord_one_coe, h2, Real.sin_two_mul]
    ring
  · simp only [Matrix.sub_apply, Matrix.smul_apply, ContinuousMap.sub_apply,
      ContinuousMap.smul_apply, smul_eq_mul, mobiusProj_apply_coe, mobiusUnit_one,
      Matrix.one_apply_eq, ContinuousMap.one_apply, mobiusRefl_one_one, ContinuousMap.neg_apply,
      circleCoord_zero_coe, h2, Real.cos_two_mul']
    linarith

@[simp]
theorem mobiusRefl_mul_self : mobiusRefl * mobiusRefl = 1 := by
  ext i j x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hcs := Real.cos_sq_add_sin_sq (2 * Real.pi * t)
  revert i j
  rw [Fin.forall_fin_two, Fin.forall_fin_two, Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, mobiusRefl_zero_zero, mobiusRefl_zero_one,
      mobiusRefl_one_zero, ContinuousMap.add_apply, ContinuousMap.mul_apply, circleCoord_zero_coe,
      circleCoord_one_coe, Matrix.one_apply_eq, ContinuousMap.one_apply]
    linarith
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, mobiusRefl_zero_zero, mobiusRefl_zero_one,
      mobiusRefl_one_one, ContinuousMap.add_apply, ContinuousMap.mul_apply,
      ContinuousMap.neg_apply, circleCoord_zero_coe, circleCoord_one_coe,
      Matrix.one_apply_ne Fin.zero_ne_one, ContinuousMap.zero_apply]
    ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, mobiusRefl_one_zero, mobiusRefl_zero_zero,
      mobiusRefl_one_one, ContinuousMap.add_apply, ContinuousMap.mul_apply,
      ContinuousMap.neg_apply, circleCoord_zero_coe, circleCoord_one_coe,
      Matrix.one_apply_ne (Ne.symm Fin.zero_ne_one), ContinuousMap.zero_apply]
    ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, mobiusRefl_one_zero, mobiusRefl_zero_one,
      mobiusRefl_one_one, ContinuousMap.add_apply, ContinuousMap.mul_apply,
      ContinuousMap.neg_apply, circleCoord_zero_coe, circleCoord_one_coe, Matrix.one_apply_eq,
      ContinuousMap.one_apply]
    linarith

@[simp]
theorem det_mobiusRefl : mobiusRefl.det = -1 := by
  ext x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hcs := Real.cos_sq_add_sin_sq (2 * Real.pi * t)
  simp only [mobiusRefl, Matrix.det_fin_two_of, ContinuousMap.sub_apply, ContinuousMap.mul_apply,
    ContinuousMap.neg_apply, circleCoord_zero_coe, circleCoord_one_coe, ContinuousMap.one_apply]
  linarith

end CircleCoordinatesAndFrame

section MobiusSections

/-- The Möbius section module over `R_ℝ = C(AddCircle (1 : ℝ), ℝ)`: the submodule of pairs
`w ∈ R_ℝ²` fixed by the reflection `ρ([t]) = [[cos(2 π t), sin(2 π t)], [sin(2 π t), -cos(2 π t)]]`,
that is, the continuous fields whose value at `[t]` lies on the line spanned by
`u(t) = (cos(π t), sin(π t))`. -/
noncomputable def mobiusSections :
    Submodule C(AddCircle (1 : ℝ), ℝ) (Fin 2 → C(AddCircle (1 : ℝ), ℝ)) :=
  LinearMap.ker (Matrix.mulVecLin
    (!![circleCoord 0, circleCoord 1; circleCoord 1, -circleCoord 0] - 1))

theorem mobiusSections_eq_ker_mobiusRefl_sub_one :
    mobiusSections = LinearMap.ker (Matrix.mulVecLin (mobiusRefl - 1)) :=
  (rfl)

/-- Pointwise coordinate characterization of membership in `mobiusSections`: `w ∈ mobiusSections`
iff `cos(2 π t) w₀([t]) + sin(2 π t) w₁([t]) = w₀([t])` and
`sin(2 π t) w₀([t]) - cos(2 π t) w₁([t]) = w₁([t])` at every point of `AddCircle (1 : ℝ)`. -/
theorem mem_mobiusSections_iff {w : Fin 2 → C(AddCircle (1 : ℝ), ℝ)} :
    w ∈ mobiusSections ↔
      ∀ x : AddCircle (1 : ℝ),
        circleCoord 0 x * w 0 x + circleCoord 1 x * w 1 x = w 0 x ∧
          circleCoord 1 x * w 0 x - circleCoord 0 x * w 1 x = w 1 x := by
  rw [mobiusSections_eq_ker_mobiusRefl_sub_one, LinearMap.mem_ker, Matrix.mulVecLin_apply,
    Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero, funext_iff, Fin.forall_fin_two]
  refine ⟨fun ⟨h0, h1⟩ x ↦ ?_, fun h ↦ ⟨ContinuousMap.ext fun x ↦ ?_,
      ContinuousMap.ext fun x ↦ ?_⟩⟩
  · have h0x := congrArg (fun f : C(AddCircle (1 : ℝ), ℝ) ↦ f x) h0
    have h1x := congrArg (fun f : C(AddCircle (1 : ℝ), ℝ) ↦ f x) h1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mobiusRefl_zero_zero,
      mobiusRefl_zero_one, ContinuousMap.add_apply, ContinuousMap.mul_apply] at h0x
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mobiusRefl_one_zero,
      mobiusRefl_one_one, neg_mul, ← sub_eq_add_neg] at h1x
    exact ⟨h0x, h1x⟩
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mobiusRefl_zero_zero,
      mobiusRefl_zero_one, ContinuousMap.add_apply, ContinuousMap.mul_apply]
    exact (h x).1
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mobiusRefl_one_zero,
      mobiusRefl_one_one, neg_mul, ← sub_eq_add_neg]
    exact (h x).2

theorem isIdempotentElem_mulVecLin_mobiusProj : IsIdempotentElem mobiusProj.mulVecLin := by
  rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul,
    isIdempotentElem_mobiusProj.eq]

/-- Since `ρ - 1 = -2 (1 - p)` and `2` is invertible in `ℝ`, the kernel `mobiusSections` of `ρ - 1`
coincides with `ker (1 - p)`. -/
theorem mobiusSections_eq_ker_one_sub_mobiusProj :
    mobiusSections = LinearMap.ker (1 - mobiusProj.mulVecLin) := by
  ext w
  rw [mobiusSections_eq_ker_mobiusRefl_sub_one, ← two_smul_mobiusProj_sub_one, LinearMap.mem_ker,
    LinearMap.mem_ker]
  have hrel : ((2 : ℝ) • mobiusProj - 1 - 1) *ᵥ w = (-2 : ℝ) • ((1 - mobiusProj) *ᵥ w) := by
    ext i x
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.sub_apply,
      Pi.smul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul]
    ring
  have h1 : (1 - mobiusProj.mulVecLin) w = (1 - mobiusProj) *ᵥ w := by
    simp [LinearMap.sub_apply, one_apply_eq_self, Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [Matrix.mulVecLin_apply, hrel, h1]
  refine ⟨fun h ↦ funext fun i ↦ ContinuousMap.ext fun x ↦ ?_, fun h ↦ by simp [h]⟩
  have hx := congrArg (fun v : Fin 2 → C(AddCircle (1 : ℝ), ℝ) ↦ v i x) h
  simp only [Pi.smul_apply, ContinuousMap.smul_apply, smul_eq_mul, Pi.zero_apply,
    ContinuousMap.zero_apply, mul_eq_zero] at hx
  rcases hx with h2 | h0
  · norm_num at h2
  · exact h0

/-- `mobiusSections` is the column range `p R_ℝ²` of the rank-one idempotent `mobiusProj`. -/
theorem mobiusSections_eq_range_mobiusProj :
    mobiusSections = LinearMap.range mobiusProj.mulVecLin := by
  rw [mobiusSections_eq_ker_one_sub_mobiusProj,
    ← LinearMap.IsIdempotentElem.range_eq_ker_one_sub isIdempotentElem_mulVecLin_mobiusProj]

/-- A vector `w : Fin 2 → C(AddCircle (1 : ℝ), ℝ)` lies in `mobiusSections` iff `p w = w`. -/
theorem mem_mobiusSections_iff_mulVec {w : Fin 2 → C(AddCircle (1 : ℝ), ℝ)} :
    w ∈ mobiusSections ↔ mobiusProj *ᵥ w = w := by
  rw [mobiusSections_eq_range_mobiusProj]
  exact LinearMap.IsIdempotentElem.mem_range_iff isIdempotentElem_mulVecLin_mobiusProj

/-- `mobiusSections` and `ker mobiusProj.mulVecLin` are complementary submodules of `R_ℝ²`. -/
theorem isCompl_mobiusSections :
    IsCompl mobiusSections (LinearMap.ker mobiusProj.mulVecLin) := by
  rw [mobiusSections_eq_range_mobiusProj]
  exact LinearMap.IsIdempotentElem.isCompl isIdempotentElem_mulVecLin_mobiusProj

/-- Direct-summand decomposition `mobiusSections × ker p ≃ₗ[R_ℝ] R_ℝ²`. -/
def mobiusSectionsComplementEquiv :
    (mobiusSections × LinearMap.ker mobiusProj.mulVecLin) ≃ₗ[C(AddCircle (1 : ℝ), ℝ)]
      (Fin 2 → C(AddCircle (1 : ℝ), ℝ)) :=
  Submodule.prodEquivOfIsCompl _ _ isCompl_mobiusSections

@[simp]
theorem mobiusSectionsComplementEquiv_apply
    (p : mobiusSections × LinearMap.ker mobiusProj.mulVecLin) :
    mobiusSectionsComplementEquiv p =
      (p.1 : Fin 2 → C(AddCircle (1 : ℝ), ℝ)) + (p.2 : Fin 2 → C(AddCircle (1 : ℝ), ℝ)) :=
  (rfl)

instance instModuleFiniteMobiusSections :
    Module.Finite C(AddCircle (1 : ℝ), ℝ) mobiusSections := by
  have hrange : Module.Finite C(AddCircle (1 : ℝ), ℝ) (LinearMap.range mobiusProj.mulVecLin) :=
    Module.Finite.range mobiusProj.mulVecLin
  exact Module.Finite.equiv (LinearEquiv.ofEq _ _ mobiusSections_eq_range_mobiusProj.symm)

instance instModuleProjectiveMobiusSections :
    Module.Projective C(AddCircle (1 : ℝ), ℝ) mobiusSections :=
  Module.Projective.of_isCompl isCompl_mobiusSections

end MobiusSections

section AntiperiodicEquivalence

/-- Forward underlying map `v ↦ ([t] ↦ v(t) u(t))` sending a `1`-antiperiodic real function to a
pair of continuous functions on `AddCircle (1 : ℝ)`. -/
private def antiperiodicToPair (v : ContinuousAntiperiodicMap 1 ℝ) :
    Fin 2 → C(AddCircle (1 : ℝ), ℝ) :=
  fun i ↦
    (v.antiperiodic.mul (antiperiodic_mobiusUnit_apply i)).liftContinuousMap
      ((map_continuous v).mul (continuous_mobiusUnit_apply i))

private theorem antiperiodicToPair_coe (v : ContinuousAntiperiodicMap 1 ℝ) (i : Fin 2) (t : ℝ) :
    antiperiodicToPair v i (t : AddCircle (1 : ℝ)) = v t * mobiusUnit t i := by
  simp [antiperiodicToPair]

private theorem antiperiodicToPair_mem_mobiusSections (v : ContinuousAntiperiodicMap 1 ℝ) :
    antiperiodicToPair v ∈ mobiusSections := by
  rw [mem_mobiusSections_iff_mulVec]
  ext i x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ContinuousMap.add_apply,
    ContinuousMap.mul_apply, mobiusProj_apply_coe, antiperiodicToPair_coe]
  calc
    mobiusUnit t i * mobiusUnit t 0 * (v t * mobiusUnit t 0) +
        mobiusUnit t i * mobiusUnit t 1 * (v t * mobiusUnit t 1)
      = v t * mobiusUnit t i * (mobiusUnit t 0 * mobiusUnit t 0 +
          mobiusUnit t 1 * mobiusUnit t 1) := by ring
    _ = v t * mobiusUnit t i := by rw [mobiusUnit_sq_add_sq, mul_one]

/-- Inverse map `w ↦ (t ↦ ⟨u(t), w([t])⟩)` projecting a pair in `R_ℝ²` onto `mobiusUnit`. -/
private def pairToAntiperiodic (w : Fin 2 → C(AddCircle (1 : ℝ), ℝ)) :
    ContinuousAntiperiodicMap 1 ℝ where
  toFun t := mobiusUnit t 0 * w 0 (t : AddCircle (1 : ℝ)) +
    mobiusUnit t 1 * w 1 (t : AddCircle (1 : ℝ))
  continuous_toFun :=
    ((continuous_mobiusUnit_apply 0).mul ((w 0).continuous.comp (AddCircle.continuous_mk' 1))).add
      ((continuous_mobiusUnit_apply 1).mul ((w 1).continuous.comp (AddCircle.continuous_mk' 1)))
  antiperiodic' :=
    ((antiperiodic_mobiusUnit_apply 0).mul_periodic
      (fun t ↦ congrArg (w 0) (AddCircle.coe_add_period 1 t))).fun_add
      ((antiperiodic_mobiusUnit_apply 1).mul_periodic
        (fun t ↦ congrArg (w 1) (AddCircle.coe_add_period 1 t)))

@[simp]
private theorem pairToAntiperiodic_apply (w : Fin 2 → C(AddCircle (1 : ℝ), ℝ)) (t : ℝ) :
    pairToAntiperiodic w t =
      mobiusUnit t 0 * w 0 (t : AddCircle (1 : ℝ)) +
        mobiusUnit t 1 * w 1 (t : AddCircle (1 : ℝ)) :=
  (rfl)

/-- Complementary projection `w ↦ (t ↦ ⟨u_⊥(t), w([t])⟩)` onto `mobiusOrth`. -/
private def pairToOrthAntiperiodic (w : Fin 2 → C(AddCircle (1 : ℝ), ℝ)) :
    ContinuousAntiperiodicMap 1 ℝ where
  toFun t := mobiusOrth t 0 * w 0 (t : AddCircle (1 : ℝ)) +
    mobiusOrth t 1 * w 1 (t : AddCircle (1 : ℝ))
  continuous_toFun :=
    ((continuous_mobiusOrth_apply 0).mul ((w 0).continuous.comp (AddCircle.continuous_mk' 1))).add
      ((continuous_mobiusOrth_apply 1).mul ((w 1).continuous.comp (AddCircle.continuous_mk' 1)))
  antiperiodic' :=
    ((antiperiodic_mobiusOrth_apply 0).mul_periodic
      (fun t ↦ congrArg (w 0) (AddCircle.coe_add_period 1 t))).fun_add
      ((antiperiodic_mobiusOrth_apply 1).mul_periodic
        (fun t ↦ congrArg (w 1) (AddCircle.coe_add_period 1 t)))

@[simp]
private theorem pairToOrthAntiperiodic_apply (w : Fin 2 → C(AddCircle (1 : ℝ), ℝ)) (t : ℝ) :
    pairToOrthAntiperiodic w t =
      mobiusOrth t 0 * w 0 (t : AddCircle (1 : ℝ)) +
        mobiusOrth t 1 * w 1 (t : AddCircle (1 : ℝ)) :=
  (rfl)

/-- Explicit `C(AddCircle (1 : ℝ), ℝ)`-linear isomorphism `M_ℝ ≃ₗ[R_ℝ] mobiusSections`, sending
`v` to `[t] ↦ v(t) u(t)` with inverse `w ↦ (t ↦ ⟨u(t), w([t])⟩)`. -/
def antiperiodicEquivMobiusSections :
    ContinuousAntiperiodicMap 1 ℝ ≃ₗ[C(AddCircle (1 : ℝ), ℝ)] mobiusSections where
  toFun v := ⟨antiperiodicToPair v, antiperiodicToPair_mem_mobiusSections v⟩
  map_add' v₁ v₂ := by
    ext i x
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
    simp [antiperiodicToPair_coe, add_mul]
  map_smul' f v := by
    ext i x
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
    simp [antiperiodicToPair_coe, mul_assoc]
  invFun w := pairToAntiperiodic w
  left_inv v := by
    ext t
    simp only [pairToAntiperiodic_apply, antiperiodicToPair_coe]
    calc
      mobiusUnit t 0 * (v t * mobiusUnit t 0) + mobiusUnit t 1 * (v t * mobiusUnit t 1)
        = v t * (mobiusUnit t 0 * mobiusUnit t 0 + mobiusUnit t 1 * mobiusUnit t 1) := by ring
      _ = v t := by rw [mobiusUnit_sq_add_sq, mul_one]
  right_inv w := by
    have hw := mem_mobiusSections_iff_mulVec.1 w.2
    ext i x
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
    have hwt : (mobiusProj *ᵥ (w : Fin 2 → C(AddCircle (1 : ℝ), ℝ))) i (t : AddCircle (1 : ℝ)) =
        (w : Fin 2 → C(AddCircle (1 : ℝ), ℝ)) i (t : AddCircle (1 : ℝ)) := by
      rw [hw]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ContinuousMap.add_apply,
      ContinuousMap.mul_apply, mobiusProj_apply_coe] at hwt
    simp only [antiperiodicToPair_coe, pairToAntiperiodic_apply]
    linarith

@[simp]
theorem coe_antiperiodicEquivMobiusSections_apply (v : ContinuousAntiperiodicMap 1 ℝ)
    (i : Fin 2) (t : ℝ) :
    (antiperiodicEquivMobiusSections v : Fin 2 → C(AddCircle (1 : ℝ), ℝ)) i
        (t : AddCircle (1 : ℝ)) =
      v t * mobiusUnit t i :=
  antiperiodicToPair_coe v i t

@[simp]
theorem antiperiodicEquivMobiusSections_symm_apply (w : mobiusSections) (t : ℝ) :
    antiperiodicEquivMobiusSections.symm w t =
      mobiusUnit t 0 * (w : Fin 2 → C(AddCircle (1 : ℝ), ℝ)) 0 (t : AddCircle (1 : ℝ)) +
        mobiusUnit t 1 * (w : Fin 2 → C(AddCircle (1 : ℝ), ℝ)) 1 (t : AddCircle (1 : ℝ)) :=
  (rfl)

/-- `antiperiodicEquivMobiusSections` preserves the `C(AddCircle (1 : ℝ), ℝ)`-valued pointwise inner
product, carrying `innerContinuousMap` to the ambient Euclidean dot product on `R_ℝ²`. -/
theorem innerContinuousMap_eq_dotProduct_antiperiodicEquivMobiusSections
    (v₁ v₂ : ContinuousAntiperiodicMap 1 ℝ) :
    v₁.innerContinuousMap v₂ =
      dotProduct (antiperiodicEquivMobiusSections v₁ : Fin 2 → C(AddCircle (1 : ℝ), ℝ))
        (antiperiodicEquivMobiusSections v₂ : Fin 2 → C(AddCircle (1 : ℝ), ℝ)) := by
  ext x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  simp only [ContinuousAntiperiodicMap.innerContinuousMap_coe, star_trivial, dotProduct,
    Fin.sum_univ_two, ContinuousMap.add_apply, ContinuousMap.mul_apply,
    coe_antiperiodicEquivMobiusSections_apply]
  calc
    v₁ t * v₂ t = v₁ t * v₂ t *
        (mobiusUnit t 0 * mobiusUnit t 0 + mobiusUnit t 1 * mobiusUnit t 1) := by
      rw [mobiusUnit_sq_add_sq, mul_one]
    _ = v₁ t * mobiusUnit t 0 * (v₂ t * mobiusUnit t 0) +
        v₁ t * mobiusUnit t 1 * (v₂ t * mobiusUnit t 1) := by ring

instance instModuleFiniteAntiperiodicReal :
    Module.Finite C(AddCircle (1 : ℝ), ℝ) (ContinuousAntiperiodicMap 1 ℝ) :=
  Module.Finite.equiv antiperiodicEquivMobiusSections.symm

instance instModuleProjectiveAntiperiodicReal :
    Module.Projective C(AddCircle (1 : ℝ), ℝ) (ContinuousAntiperiodicMap 1 ℝ) :=
  Module.Projective.of_equiv antiperiodicEquivMobiusSections.symm

private def antiperiodicProdToPair
    (p : ContinuousAntiperiodicMap 1 ℝ × ContinuousAntiperiodicMap 1 ℝ) :
    Fin 2 → C(AddCircle (1 : ℝ), ℝ) :=
  fun i ↦
    ((p.1.antiperiodic.mul (antiperiodic_mobiusUnit_apply i)).add
      (p.2.antiperiodic.mul (antiperiodic_mobiusOrth_apply i))).liftContinuousMap
      (((map_continuous p.1).mul (continuous_mobiusUnit_apply i)).add
        ((map_continuous p.2).mul (continuous_mobiusOrth_apply i)))

@[simp]
private theorem antiperiodicProdToPair_coe
    (p : ContinuousAntiperiodicMap 1 ℝ × ContinuousAntiperiodicMap 1 ℝ) (i : Fin 2) (t : ℝ) :
    antiperiodicProdToPair p i (t : AddCircle (1 : ℝ)) =
      p.1 t * mobiusUnit t i + p.2 t * mobiusOrth t i := by
  simp [antiperiodicProdToPair]

/-- Explicit doubled splitting `M_ℝ × M_ℝ ≃ₗ[R_ℝ] R_ℝ²` built from the orthonormal half-turn frame
`(u(t), u_⊥(t))`: `(v₁, v₂)` goes to `[t] ↦ v₁(t) u(t) + v₂(t) u_⊥(t)`. -/
def antiperiodicProdEquiv :
    (ContinuousAntiperiodicMap 1 ℝ × ContinuousAntiperiodicMap 1 ℝ) ≃ₗ[C(AddCircle (1 : ℝ), ℝ)]
      (Fin 2 → C(AddCircle (1 : ℝ), ℝ)) where
  toFun := antiperiodicProdToPair
  map_add' p q := by
    ext i x
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
    simp only [Pi.add_apply, ContinuousMap.add_apply, antiperiodicProdToPair_coe, Prod.fst_add,
      Prod.snd_add, ContinuousAntiperiodicMap.add_apply]
    ring
  map_smul' f p := by
    ext i x
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
    simp only [Pi.smul_apply, smul_eq_mul, ContinuousMap.mul_apply, antiperiodicProdToPair_coe,
      Prod.smul_fst, Prod.smul_snd, ContinuousAntiperiodicMap.smul_circle_apply, RingHom.id_apply]
    ring
  invFun w := (pairToAntiperiodic w, pairToOrthAntiperiodic w)
  left_inv p := by
    obtain ⟨v₁, v₂⟩ := p
    refine Prod.ext (ContinuousAntiperiodicMap.ext fun t ↦ ?_)
      (ContinuousAntiperiodicMap.ext fun t ↦ ?_)
    · have ht := Real.cos_sq_add_sin_sq (Real.pi * t)
      simp only [pairToAntiperiodic_apply, antiperiodicProdToPair_coe, mobiusUnit_zero,
        mobiusUnit_one, mobiusOrth_zero, mobiusOrth_one]
      calc
        Real.cos (Real.pi * t) * (v₁ t * Real.cos (Real.pi * t) + v₂ t * -Real.sin (Real.pi * t)) +
            Real.sin (Real.pi * t) * (v₁ t * Real.sin (Real.pi * t) + v₂ t * Real.cos (Real.pi * t))
          = v₁ t * (Real.cos (Real.pi * t) ^ 2 + Real.sin (Real.pi * t) ^ 2) := by ring
        _ = v₁ t := by rw [ht, mul_one]
    · have ht := Real.cos_sq_add_sin_sq (Real.pi * t)
      simp only [pairToOrthAntiperiodic_apply, antiperiodicProdToPair_coe, mobiusUnit_zero,
        mobiusUnit_one, mobiusOrth_zero, mobiusOrth_one]
      calc
        -Real.sin (Real.pi * t) * (v₁ t * Real.cos (Real.pi * t) + v₂ t * -Real.sin (Real.pi * t)) +
            Real.cos (Real.pi * t) * (v₁ t * Real.sin (Real.pi * t) + v₂ t * Real.cos (Real.pi * t))
          = v₂ t * (Real.cos (Real.pi * t) ^ 2 + Real.sin (Real.pi * t) ^ 2) := by ring
        _ = v₂ t := by rw [ht, mul_one]
  right_inv w := by
    ext i x
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
    have ht := Real.cos_sq_add_sin_sq (Real.pi * t)
    revert i
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · simp only [antiperiodicProdToPair_coe, pairToAntiperiodic_apply,
        pairToOrthAntiperiodic_apply, mobiusUnit_zero, mobiusUnit_one, mobiusOrth_zero,
        mobiusOrth_one]
      calc
        (Real.cos (Real.pi * t) * w 0 (t : AddCircle (1 : ℝ)) +
              Real.sin (Real.pi * t) * w 1 (t : AddCircle (1 : ℝ))) * Real.cos (Real.pi * t) +
            (-Real.sin (Real.pi * t) * w 0 (t : AddCircle (1 : ℝ)) +
              Real.cos (Real.pi * t) * w 1 (t : AddCircle (1 : ℝ))) * -Real.sin (Real.pi * t)
          = w 0 (t : AddCircle (1 : ℝ)) *
              (Real.cos (Real.pi * t) ^ 2 + Real.sin (Real.pi * t) ^ 2) := by ring
        _ = w 0 (t : AddCircle (1 : ℝ)) := by rw [ht, mul_one]
    · simp only [antiperiodicProdToPair_coe, pairToAntiperiodic_apply,
        pairToOrthAntiperiodic_apply, mobiusUnit_zero, mobiusUnit_one, mobiusOrth_zero,
        mobiusOrth_one]
      calc
        (Real.cos (Real.pi * t) * w 0 (t : AddCircle (1 : ℝ)) +
              Real.sin (Real.pi * t) * w 1 (t : AddCircle (1 : ℝ))) * Real.sin (Real.pi * t) +
            (-Real.sin (Real.pi * t) * w 0 (t : AddCircle (1 : ℝ)) +
              Real.cos (Real.pi * t) * w 1 (t : AddCircle (1 : ℝ))) * Real.cos (Real.pi * t)
          = w 1 (t : AddCircle (1 : ℝ)) *
              (Real.cos (Real.pi * t) ^ 2 + Real.sin (Real.pi * t) ^ 2) := by ring
        _ = w 1 (t : AddCircle (1 : ℝ)) := by rw [ht, mul_one]

@[simp]
theorem antiperiodicProdEquiv_apply_coe
    (p : ContinuousAntiperiodicMap 1 ℝ × ContinuousAntiperiodicMap 1 ℝ) (i : Fin 2) (t : ℝ) :
    antiperiodicProdEquiv p i (t : AddCircle (1 : ℝ)) =
      p.1 t * mobiusUnit t i + p.2 t * mobiusOrth t i :=
  antiperiodicProdToPair_coe p i t

@[simp]
theorem antiperiodicProdEquiv_symm_fst_apply (w : Fin 2 → C(AddCircle (1 : ℝ), ℝ)) (t : ℝ) :
    (antiperiodicProdEquiv.symm w).1 t =
      mobiusUnit t 0 * w 0 (t : AddCircle (1 : ℝ)) +
        mobiusUnit t 1 * w 1 (t : AddCircle (1 : ℝ)) :=
  (rfl)

@[simp]
theorem antiperiodicProdEquiv_symm_snd_apply (w : Fin 2 → C(AddCircle (1 : ℝ), ℝ)) (t : ℝ) :
    (antiperiodicProdEquiv.symm w).2 t =
      mobiusOrth t 0 * w 0 (t : AddCircle (1 : ℝ)) +
        mobiusOrth t 1 * w 1 (t : AddCircle (1 : ℝ)) :=
  (rfl)

/-- Doubled splitting `mobiusSections × mobiusSections ≃ₗ[R_ℝ] R_ℝ²`. -/
def mobiusSectionsProdEquiv :
    (mobiusSections × mobiusSections) ≃ₗ[C(AddCircle (1 : ℝ), ℝ)]
      (Fin 2 → C(AddCircle (1 : ℝ), ℝ)) :=
  (antiperiodicEquivMobiusSections.symm.prodCongr antiperiodicEquivMobiusSections.symm).trans
    antiperiodicProdEquiv

@[simp]
theorem mobiusSectionsProdEquiv_apply (p : mobiusSections × mobiusSections) :
    mobiusSectionsProdEquiv p =
      antiperiodicProdEquiv
        (antiperiodicEquivMobiusSections.symm p.1, antiperiodicEquivMobiusSections.symm p.2) :=
  (rfl)

end AntiperiodicEquivalence

section OrderTwoAndK0

/-- **Monodromy obstruction to free stabilization.** For every `N : ℕ`, there is no
`C(AddCircle (1 : ℝ), ℝ)`-linear isomorphism `M_ℝ × R_ℝᴺ ≃ₗ R_ℝᴺ⁺¹`. -/
theorem isEmpty_antiperiodic_prod_linearEquiv_fin (N : ℕ) :
    IsEmpty ((ContinuousAntiperiodicMap 1 ℝ × (Fin N → C(AddCircle (1 : ℝ), ℝ))) ≃ₗ[
      C(AddCircle (1 : ℝ), ℝ)] (Fin (N + 1) → C(AddCircle (1 : ℝ), ℝ))) := by
  refine ⟨fun e ↦ ?_⟩
  -- Pull back the standard basis of `R_ℝᴺ⁺¹` along `e.symm` to an `(N + 1) × (N + 1)` real matrix
  -- `B(t)` whose determinant is continuous and `1`-antiperiodic, hence vanishes at some `t₀`.
  let b : Fin (N + 1) → ContinuousAntiperiodicMap 1 ℝ × (Fin N → C(AddCircle (1 : ℝ), ℝ)) :=
    fun j ↦ e.symm (Pi.single j 1)
  let B : ℝ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := fun t ↦
    Matrix.of (Fin.cases (fun j ↦ (b j).1 t)
      (fun k j ↦ (b j).2 k (t : AddCircle (1 : ℝ))))
  have hcontB : Continuous fun t ↦ (B t).det := by
    refine Continuous.matrix_det (continuous_matrix fun i j ↦ ?_)
    refine Fin.cases ?_ ?_ i
    · exact map_continuous (b j).1
    · intro k
      exact ((b j).2 k).continuous.comp (AddCircle.continuous_mk' 1)
  let Mdiag : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
    Matrix.diagonal (Fin.cons (-1 : ℝ) fun _ ↦ 1)
  have hmon : ∀ t : ℝ, B (t + 1) = Mdiag * B t := fun t ↦ by
    ext i j
    rw [Matrix.diagonal_mul]
    refine Fin.cases ?_ ?_ i
    · simp [B, (b j).1.apply_add_one t]
    · intro k
      simp [B, AddCircle.coe_add_period 1 t]
  have hdetM : Mdiag.det = -1 := by
    simp [Mdiag, Matrix.det_diagonal, Fin.prod_univ_succ]
  have hanti : Function.Antiperiodic (fun t ↦ (B t).det) 1 := fun t ↦ by
    dsimp only
    rw [hmon t, Matrix.det_mul, hdetM, neg_one_mul]
  obtain ⟨t₀, -, ht₀⟩ := hanti.exists_mem_unitInterval_eq_zero hcontB
  -- Build a right inverse `A` to `B t₀` by evaluating `e` on sections that realize the standard
  -- basis of `ℝᴺ⁺¹` at `t₀`, contradicting `det (B t₀) = 0`.
  let sec : Fin (N + 1) → ContinuousAntiperiodicMap 1 ℝ × (Fin N → C(AddCircle (1 : ℝ), ℝ)) :=
    Fin.cases (mobiusShiftedCos t₀, 0) fun m ↦ (0, Pi.single m 1)
  let A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
    Matrix.of fun j p ↦ e (sec p) j (t₀ : AddCircle (1 : ℝ))
  have hBA : B t₀ * A = 1 := by
    ext i p
    have hdecomp : sec p = ∑ j : Fin (N + 1), e (sec p) j • b j := by
      have hpi : e (sec p) = ∑ j : Fin (N + 1), e (sec p) j • Pi.single j 1 := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      calc
        sec p = e.symm (e (sec p)) := (e.symm_apply_apply (sec p)).symm
        _ = e.symm (∑ j : Fin (N + 1), e (sec p) j • Pi.single j 1) := congrArg e.symm hpi
        _ = ∑ j : Fin (N + 1), e (sec p) j • b j := by simp [map_sum, map_smul, b]
    refine Fin.cases ?_ ?_ i
    · have h0 := congrArg (fun z : ContinuousAntiperiodicMap 1 ℝ × _ ↦ z.1 t₀) hdecomp
      simp only [Prod.fst_sum, ContinuousAntiperiodicMap.coe_sum, Finset.sum_apply,
        Prod.smul_fst, ContinuousAntiperiodicMap.smul_circle_apply, smul_eq_mul] at h0
      rw [Matrix.mul_apply]
      refine (Finset.sum_congr rfl fun j _ ↦ ?_).trans h0.symm |>.trans ?_
      · simp [B, A, mul_comm]
      · refine Fin.cases ?_ ?_ p
        · simp [sec]
        · intro m
          simp [sec, Matrix.one_apply_ne (Fin.succ_ne_zero m).symm]
    · intro k
      have hk := congrArg
        (fun z : _ × (Fin N → C(AddCircle (1 : ℝ), ℝ)) ↦ z.2 k (t₀ : AddCircle (1 : ℝ))) hdecomp
      simp only [Prod.snd_sum, Finset.sum_apply, ContinuousMap.coe_sum, Prod.smul_snd,
        Pi.smul_apply, smul_eq_mul] at hk
      rw [Matrix.mul_apply]
      refine (Finset.sum_congr rfl fun j _ ↦ ?_).trans hk.symm |>.trans ?_
      · simp [B, A, mul_comm]
      · refine Fin.cases ?_ ?_ p
        · simp [sec, Matrix.one_apply_ne (Fin.succ_ne_zero k)]
        · intro m
          rcases eq_or_ne k m with rfl | hkm
          · simp [sec]
          · simp [sec, Fin.succ_inj, hkm]
  have hdet1 : (B t₀).det * A.det = 1 := by
    rw [← Matrix.det_mul, hBA, Matrix.det_one]
  rw [ht₀, zero_mul] at hdet1
  exact zero_ne_one hdet1

/-- For every `N : ℕ`, there is no `C(AddCircle (1 : ℝ), ℝ)`-linear isomorphism
`mobiusSections × R_ℝᴺ ≃ₗ R_ℝᴺ⁺¹`. -/
theorem isEmpty_mobiusSections_prod_linearEquiv_fin (N : ℕ) :
    IsEmpty ((mobiusSections × (Fin N → C(AddCircle (1 : ℝ), ℝ))) ≃ₗ[C(AddCircle (1 : ℝ), ℝ)]
      (Fin (N + 1) → C(AddCircle (1 : ℝ), ℝ))) :=
  ⟨fun e ↦ (isEmpty_antiperiodic_prod_linearEquiv_fin N).false
    ((antiperiodicEquivMobiusSections.prodCongr (.refl _ _)).trans e)⟩

/-- **Order-two and non-stabilization theorem for the Möbius module.** Over
`R = C(AddCircle (1 : ℝ), ℝ)`, the Möbius module `M = mobiusSections` satisfies `M ⊕ M ≅ R²`, while
`M ⊕ Rᴺ ≇ Rᴺ⁺¹` for every `N : ℕ` (Weibel, *The K-book*, Chapter I, (4.9.1)). -/
theorem mobiusSections_order_two :
    Nonempty ((mobiusSections × mobiusSections) ≃ₗ[C(AddCircle (1 : ℝ), ℝ)]
      (Fin 2 → C(AddCircle (1 : ℝ), ℝ))) ∧
    ∀ N : ℕ, IsEmpty ((mobiusSections × (Fin N → C(AddCircle (1 : ℝ), ℝ))) ≃ₗ[
      C(AddCircle (1 : ℝ), ℝ)] (Fin (N + 1) → C(AddCircle (1 : ℝ), ℝ))) :=
  ⟨⟨mobiusSectionsProdEquiv⟩, isEmpty_mobiusSections_prod_linearEquiv_fin⟩

/-- `ContinuousAntiperiodicMap 1 ℝ` is not generated by a single element over
`C(AddCircle (1 : ℝ), ℝ)`. -/
theorem exists_forall_smul_ne_antiperiodic (v : ContinuousAntiperiodicMap 1 ℝ) :
    ∃ w : ContinuousAntiperiodicMap 1 ℝ, ∀ f : C(AddCircle (1 : ℝ), ℝ), f • v ≠ w := by
  obtain ⟨t₀, -, ht₀⟩ := v.exists_mem_unitInterval_eq_zero
  refine ⟨mobiusShiftedCos t₀, fun f hf ↦ ?_⟩
  have h := congrArg (fun z : ContinuousAntiperiodicMap 1 ℝ ↦ z t₀) hf
  simp [ht₀] at h

/-- `ContinuousAntiperiodicMap 1 ℝ` is not a free `C(AddCircle (1 : ℝ), ℝ)`-module. -/
theorem not_free_continuousAntiperiodicMap_real :
    ¬ Module.Free C(AddCircle (1 : ℝ), ℝ) (ContinuousAntiperiodicMap 1 ℝ) := by
  intro hfree
  let b := Module.Free.chooseBasis C(AddCircle (1 : ℝ), ℝ) (ContinuousAntiperiodicMap 1 ℝ)
  have h0ne : mobiusShiftedCos 0 ≠ 0 := fun h ↦ by
    have := congrArg (fun z : ContinuousAntiperiodicMap 1 ℝ ↦ z 0) h
    simp at this
  have hrepr_ne : b.repr (mobiusShiftedCos 0) ≠ 0 := fun h ↦
    h0ne (b.repr.injective (h.trans (map_zero b.repr).symm))
  obtain ⟨i, -⟩ := Finsupp.support_nonempty_iff.2 hrepr_ne
  -- Any two basis vectors satisfy `⟨bᵢ, bⱼ⟩ • bᵢ = ⟨bᵢ, bᵢ⟩ • bⱼ`, forcing a single basis index.
  have huniq : ∀ j, j = i := by
    intro j
    by_contra hji
    have hrel : (b i).innerContinuousMap (b j) • b i =
        (b i).innerContinuousMap (b i) • b j := by
      ext t
      simp only [ContinuousAntiperiodicMap.smul_circle_apply,
        ContinuousAntiperiodicMap.innerContinuousMap_coe, star_trivial, smul_eq_mul]
      ring
    have hcoord := congrArg (fun z ↦ b.repr z j) hrel
    have hij : i ≠ j := Ne.symm hji
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, hij,
      ↓reduceIte, smul_eq_mul, mul_zero, mul_one] at hcoord
    exact b.ne_zero i ((b i).innerContinuousMap_self_eq_zero_iff.1 hcoord.symm)
  obtain ⟨w, hw⟩ := exists_forall_smul_ne_antiperiodic (b i)
  refine hw (b.repr w i) (b.repr.injective ?_)
  ext j
  obtain rfl := huniq j
  simp

/-- `mobiusSections` is not a free `C(AddCircle (1 : ℝ), ℝ)`-module. -/
theorem not_free_mobiusSections :
    ¬ Module.Free C(AddCircle (1 : ℝ), ℝ) mobiusSections :=
  fun _ ↦ not_free_continuousAntiperiodicMap_real
    (Module.Free.of_equiv antiperiodicEquivMobiusSections.symm)

/-- The reduced Möbius class `η = [mobiusSections] - [R_ℝ]` in the projective `K₀` of
`R_ℝ = C(AddCircle (1 : ℝ), ℝ)`. -/
def mobiusK0Class :
    SplitK0.{0} (finiteProjectiveModules C(AddCircle (1 : ℝ), ℝ)).FullSubcategory :=
  FiniteProjectiveModules.classOf C(AddCircle (1 : ℝ), ℝ) mobiusSections 1

theorem mobiusK0Class_def :
    mobiusK0Class = FiniteProjectiveModules.classOf C(AddCircle (1 : ℝ), ℝ) mobiusSections 1 :=
  (rfl)

theorem mobiusK0Class_eq_antiperiodic :
    mobiusK0Class =
      FiniteProjectiveModules.classOf C(AddCircle (1 : ℝ), ℝ)
        (ContinuousAntiperiodicMap 1 ℝ) 1 :=
  FiniteProjectiveModules.classOf_congr antiperiodicEquivMobiusSections.symm 1

@[simp]
theorem two_nsmul_mobiusK0Class : 2 • mobiusK0Class = 0 := by
  rw [mobiusK0Class, two_nsmul, ← FiniteProjectiveModules.classOf_prod 1 1,
    FiniteProjectiveModules.classOf_congr mobiusSectionsProdEquiv 2,
    FiniteProjectiveModules.classOf_free]

theorem mobiusK0Class_ne_zero : mobiusK0Class ≠ 0 := by
  rw [mobiusK0Class, ne_eq, FiniteProjectiveModules.classOf_eq_zero_iff]
  rintro ⟨k, ⟨e⟩⟩
  exact (isEmpty_mobiusSections_prod_linearEquiv_fin k).false
    (e.trans (LinearEquiv.funCongrLeft _ _ (finCongr (Nat.add_comm k 1))))

/-- The reduced Möbius class `mobiusK0Class` has exact additive order `2` in `K₀(R_ℝ)`. -/
@[simp]
theorem addOrderOf_mobiusK0Class : addOrderOf mobiusK0Class = 2 :=
  addOrderOf_eq_prime two_nsmul_mobiusK0Class mobiusK0Class_ne_zero

end OrderTwoAndK0

section Complexification

/-- The continuous `1`-antiperiodic unit-modulus character `χ(t) = exp(π i t)` in
`ContinuousAntiperiodicMap 1 ℂ`. -/
def mobiusChar : ContinuousAntiperiodicMap 1 ℂ where
  toFun t := Complex.exp (Real.pi * Complex.I * t)
  continuous_toFun :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  antiperiodic' t := by
    dsimp only
    have harg : (Real.pi : ℂ) * Complex.I * ((t + 1 : ℝ) : ℂ) =
        Real.pi * Complex.I * t + Real.pi * Complex.I := by push_cast; ring
    rw [harg, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

theorem mobiusChar_apply (t : ℝ) : mobiusChar t = Complex.exp (Real.pi * Complex.I * t) :=
  (rfl)

theorem mobiusChar_ne_zero (t : ℝ) : mobiusChar t ≠ 0 :=
  Complex.exp_ne_zero _

@[simp]
theorem norm_mobiusChar_apply (t : ℝ) : ‖mobiusChar t‖ = 1 := by
  have harg : (Real.pi : ℂ) * Complex.I * t = ((Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [mobiusChar_apply, harg, Complex.norm_exp_ofReal_mul_I]

@[simp]
theorem norm_mobiusChar : ‖mobiusChar‖ = 1 := by
  refine le_antisymm
    (mobiusChar.norm_le_of_forall_mem_Icc (a := 0) zero_le_one
      fun t _ ↦ (norm_mobiusChar_apply t).le) ?_
  simpa only [norm_mobiusChar_apply] using mobiusChar.norm_apply_le 0

/-- Isometric `C(AddCircle (1 : ℝ), ℂ)`-linear isomorphism `R_ℂ ≃ₗ[R_ℂ] M_ℂ`, sending
`f ↦ (t ↦ χ(t) f([t]))` with inverse `v ↦ ([t] ↦ χ(t)⁻¹ v(t))`. -/
def continuousMapEquivAntiperiodicComplex :
    C(AddCircle (1 : ℝ), ℂ) ≃ₗ[C(AddCircle (1 : ℝ), ℂ)] ContinuousAntiperiodicMap 1 ℂ where
  toFun f := f • mobiusChar
  map_add' f g := add_smul f g mobiusChar
  map_smul' f g := mul_smul f g mobiusChar
  invFun v :=
    ((mobiusChar.antiperiodic.comp_odd (g := Inv.inv) fun _ ↦ inv_neg).mul
      v.antiperiodic).liftContinuousMap
      (((map_continuous mobiusChar).inv₀ mobiusChar_ne_zero).mul (map_continuous v))
  left_inv f := by
    ext x
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
    simp only [Function.Periodic.liftContinuousMap_coe, Pi.mul_apply, Function.comp_apply,
      ContinuousAntiperiodicMap.smul_circle_apply, smul_eq_mul]
    rw [mul_left_comm, inv_mul_cancel₀ (mobiusChar_ne_zero t), mul_one]
  right_inv v := by
    ext t
    simp only [ContinuousAntiperiodicMap.smul_circle_apply, smul_eq_mul,
      Function.Periodic.liftContinuousMap_coe, Pi.mul_apply, Function.comp_apply]
    rw [mul_right_comm, inv_mul_cancel₀ (mobiusChar_ne_zero t), one_mul]

@[simp]
theorem continuousMapEquivAntiperiodicComplex_apply (f : C(AddCircle (1 : ℝ), ℂ)) (t : ℝ) :
    continuousMapEquivAntiperiodicComplex f t = mobiusChar t * f (t : AddCircle (1 : ℝ)) := by
  simp [continuousMapEquivAntiperiodicComplex, mul_comm]

@[simp]
theorem continuousMapEquivAntiperiodicComplex_symm_coe (v : ContinuousAntiperiodicMap 1 ℂ)
    (t : ℝ) :
    continuousMapEquivAntiperiodicComplex.symm v (t : AddCircle (1 : ℝ)) =
      (mobiusChar t)⁻¹ * v t := by
  simp [continuousMapEquivAntiperiodicComplex]

@[simp]
theorem norm_continuousMapEquivAntiperiodicComplex (f : C(AddCircle (1 : ℝ), ℂ)) :
    ‖continuousMapEquivAntiperiodicComplex f‖ = ‖f‖ := by
  refine le_antisymm
    ((continuousMapEquivAntiperiodicComplex f).norm_le_of_forall_mem_Icc (a := 0) (norm_nonneg f)
      fun t _ ↦ ?_)
    ((ContinuousMap.norm_le f (norm_nonneg _)).2 fun x ↦ ?_)
  · rw [continuousMapEquivAntiperiodicComplex_apply, norm_mul, norm_mobiusChar_apply, one_mul]
    exact f.norm_coe_le_norm (t : AddCircle (1 : ℝ))
  · obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
    simpa only [continuousMapEquivAntiperiodicComplex_apply, norm_mul, norm_mobiusChar_apply,
      one_mul] using (continuousMapEquivAntiperiodicComplex f).norm_apply_le t

theorem isometry_continuousMapEquivAntiperiodicComplex :
    Isometry continuousMapEquivAntiperiodicComplex :=
  AddMonoidHomClass.isometry_of_norm continuousMapEquivAntiperiodicComplex
    norm_continuousMapEquivAntiperiodicComplex

instance instModuleFreeAntiperiodicComplex :
    Module.Free C(AddCircle (1 : ℝ), ℂ) (ContinuousAntiperiodicMap 1 ℂ) :=
  Module.Free.of_equiv continuousMapEquivAntiperiodicComplex

/-- Pointwise real-to-complex ring homomorphism
`C(AddCircle (1 : ℝ), ℝ) →+* C(AddCircle (1 : ℝ), ℂ)`. -/
def circleRealToComplex : C(AddCircle (1 : ℝ), ℝ) →+* C(AddCircle (1 : ℝ), ℂ) :=
  Complex.ofRealHom.compLeftContinuous (AddCircle (1 : ℝ)) Complex.continuous_ofReal

@[simp]
theorem circleRealToComplex_apply (f : C(AddCircle (1 : ℝ), ℝ)) (x : AddCircle (1 : ℝ)) :
    circleRealToComplex f x = (f x : ℂ) :=
  (rfl)

/-- Semilinear inclusion of real `1`-antiperiodic continuous functions into complex ones. -/
def ofRealAntiperiodic :
    ContinuousAntiperiodicMap 1 ℝ →ₛₗ[circleRealToComplex] ContinuousAntiperiodicMap 1 ℂ where
  toFun v :=
    ⟨⟨fun t ↦ (v t : ℂ), Complex.continuous_ofReal.comp (map_continuous v)⟩,
      v.antiperiodic.comp_odd Complex.ofReal_neg⟩
  map_add' v w := by ext t; simp
  map_smul' f v := by ext t; simp

@[simp]
theorem ofRealAntiperiodic_apply (v : ContinuousAntiperiodicMap 1 ℝ) (t : ℝ) :
    ofRealAntiperiodic v t = (v t : ℂ) :=
  (rfl)

/-- Pointwise real-part additive homomorphism on continuous complex `p`-antiperiodic maps. -/
def reAntiperiodic {p : ℝ} : ContinuousAntiperiodicMap p ℂ →+ ContinuousAntiperiodicMap p ℝ where
  toFun w :=
    ⟨⟨fun t ↦ (w t).re, Complex.continuous_re.comp (map_continuous w)⟩,
      w.antiperiodic.comp_odd Complex.neg_re⟩
  map_zero' := by ext t; rfl
  map_add' _ _ := by ext t; rfl

@[simp]
theorem reAntiperiodic_apply {p : ℝ} (w : ContinuousAntiperiodicMap p ℂ) (t : ℝ) :
    reAntiperiodic w t = (w t).re :=
  (rfl)

/-- Pointwise imaginary-part additive homomorphism on continuous complex `p`-antiperiodic maps. -/
def imAntiperiodic {p : ℝ} : ContinuousAntiperiodicMap p ℂ →+ ContinuousAntiperiodicMap p ℝ where
  toFun w :=
    ⟨⟨fun t ↦ (w t).im, Complex.continuous_im.comp (map_continuous w)⟩,
      w.antiperiodic.comp_odd Complex.neg_im⟩
  map_zero' := by ext t; rfl
  map_add' _ _ := by ext t; rfl

@[simp]
theorem imAntiperiodic_apply {p : ℝ} (w : ContinuousAntiperiodicMap p ℂ) (t : ℝ) :
    imAntiperiodic w t = (w t).im :=
  (rfl)

private def complexAntiperiodicToBalanced :
    ContinuousAntiperiodicMap 1 ℂ →+
      BalancedExtension circleRealToComplex (ContinuousAntiperiodicMap 1 ℝ) where
  toFun w :=
    BalancedExtension.tmul circleRealToComplex 1 (reAntiperiodic w) +
      BalancedExtension.tmul circleRealToComplex (ContinuousMap.const _ Complex.I)
        (imAntiperiodic w)
  map_zero' := by simp
  map_add' w₁ w₂ := by
    rw [map_add, map_add, BalancedExtension.tmul_add, BalancedExtension.tmul_add]
    abel

/-- **Balanced complexification of the Möbius section module.** Along `circleRealToComplex`,
`R_ℂ ⊗_{R_ℝ} M_ℝ ≃ₗ[R_ℂ] M_ℂ`, sending `f ⊗ v` to `t ↦ v(t) f([t])`. -/
def balancedExtensionAntiperiodicComplexEquiv :
    BalancedExtension circleRealToComplex (ContinuousAntiperiodicMap 1 ℝ) ≃ₗ[
      C(AddCircle (1 : ℝ), ℂ)] ContinuousAntiperiodicMap 1 ℂ where
  toLinearMap := BalancedExtension.lift ofRealAntiperiodic
  invFun := complexAntiperiodicToBalanced
  left_inv z := by
    rw [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    induction z using BalancedExtension.induction_on with
    | tmul f v =>
      let fre : C(AddCircle (1 : ℝ), ℝ) :=
        ⟨fun x ↦ (f x).re, Complex.continuous_re.comp f.continuous⟩
      let fim : C(AddCircle (1 : ℝ), ℝ) :=
        ⟨fun x ↦ (f x).im, Complex.continuous_im.comp f.continuous⟩
      have hre : reAntiperiodic (f • ofRealAntiperiodic v) = fre • v := by
        ext t
        simp [fre, Complex.mul_re]
      have him : imAntiperiodic (f • ofRealAntiperiodic v) = fim • v := by
        ext t
        simp [fim, Complex.mul_im]
      have hf : circleRealToComplex fre + ContinuousMap.const _ Complex.I *
          circleRealToComplex fim = f := by
        ext x
        simpa [fre, fim, mul_comm] using Complex.re_add_im (f x)
      simp only [BalancedExtension.lift_tmul, complexAntiperiodicToBalanced,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk, hre, him, BalancedExtension.tmul_smul, one_mul,
        ← BalancedExtension.add_tmul, hf]
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
  right_inv w := by
    ext t
    simpa [complexAntiperiodicToBalanced, mul_comm] using Complex.re_add_im (w t)

@[simp]
theorem balancedExtensionAntiperiodicComplexEquiv_tmul
    (f : C(AddCircle (1 : ℝ), ℂ)) (v : ContinuousAntiperiodicMap 1 ℝ) (t : ℝ) :
    balancedExtensionAntiperiodicComplexEquiv
        (BalancedExtension.tmul circleRealToComplex f v) t =
      (v t : ℂ) * f (t : AddCircle (1 : ℝ)) := by
  simp [balancedExtensionAntiperiodicComplexEquiv, mul_comm]

@[simp]
theorem balancedExtensionAntiperiodicComplexEquiv_symm_apply
    (w : ContinuousAntiperiodicMap 1 ℂ) :
    balancedExtensionAntiperiodicComplexEquiv.symm w =
      BalancedExtension.tmul circleRealToComplex 1 (reAntiperiodic w) +
        BalancedExtension.tmul circleRealToComplex (ContinuousMap.const _ Complex.I)
          (imAntiperiodic w) :=
  (rfl)

/-- Balanced complexification of `mobiusSections`:
`R_ℂ ⊗_{R_ℝ} mobiusSections ≃ₗ[R_ℂ] ContinuousAntiperiodicMap 1 ℂ`. -/
def balancedExtensionMobiusSectionsComplexEquiv :
    BalancedExtension circleRealToComplex mobiusSections ≃ₗ[C(AddCircle (1 : ℝ), ℂ)]
      ContinuousAntiperiodicMap 1 ℂ :=
  (BalancedExtension.congr circleRealToComplex antiperiodicEquivMobiusSections.symm).trans
    balancedExtensionAntiperiodicComplexEquiv

@[simp]
theorem balancedExtensionMobiusSectionsComplexEquiv_apply
    (z : BalancedExtension circleRealToComplex mobiusSections) :
    balancedExtensionMobiusSectionsComplexEquiv z =
      balancedExtensionAntiperiodicComplexEquiv
        (BalancedExtension.congr circleRealToComplex antiperiodicEquivMobiusSections.symm z) :=
  (rfl)

/-- Extension of scalars along `circleRealToComplex : R_ℝ →+* R_ℂ` annihilates the reduced Möbius
class `mobiusK0Class` in projective `K₀`. -/
@[simp]
theorem map_mobiusK0Class_complex_eq_zero :
    SplitK0.map.{0, 0} circleRealToComplex.finiteProjectiveModulesExtendScalars mobiusK0Class =
      0 := by
  let Q : (finiteProjectiveModules C(AddCircle (1 : ℝ), ℂ)).FullSubcategory :=
    ⟨ModuleCat.of C(AddCircle (1 : ℝ), ℂ) C(AddCircle (1 : ℝ), ℂ),
      finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩
  rw [mobiusK0Class, FiniteProjectiveModules.classOf_def, map_sub, one_smul,
    SplitK0.map_of, SplitK0.map_of,
    SplitK0.of_extendScalars_obj (Q := Q)
      (balancedExtensionMobiusSectionsComplexEquiv.trans
        continuousMapEquivAntiperiodicComplex.symm),
    SplitK0.of_extendScalars_obj (Q := Q)
      ((BalancedExtension.congr circleRealToComplex (LinearEquiv.funUnique (Fin 1) _ _).symm).trans
        ((BalancedExtension.piScalarRight circleRealToComplex (Fin 1)).trans
          (LinearEquiv.funUnique (Fin 1) _ _))),
    sub_self]

end Complexification

end

end TauCeti
