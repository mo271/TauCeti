/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Manifold.MFDeriv.Pi

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Integral linear automorphisms of a torus

Let `p > 0` and let `Tⁿ = ι → AddCircle p` be the torus with all periods equal to `p`, a smooth
manifold modelled on `ModelWithCorners.pi fun _ ↦ 𝓘(ℝ)` whose tangent space at every point is
`ι → ℝ`. An invertible integer matrix `A ∈ GL(ι, ℤ)` acts on `Tⁿ` by

`(A • x) i = ∑ j, A i j • x j`

(`AddCircle.generalLinearGroup_smul_apply`), each `A i j • x j` being integer multiplication in the
circle. This is an action of the group `GL(ι, ℤ)` by additive maps
(`AddCircle.instDistribMulActionGeneralLinearGroup`), and each `A` acts by smooth maps
(`AddCircle.instContMDiffConstSMulGeneralLinearGroup`). So `x ↦ A • x` is a diffeomorphism of the
torus, with inverse `x ↦ A⁻¹ • x` (`Diffeomorph.constSmul`), and the cotangent bundle `T*Tⁿ`
inherits the cotangent-lifted action (`TauCeti.CotangentBundle.instMulAction`).

The covering map `(ι → ℝ) → ∀ i, AddCircle (p i)`, `t ↦ ([t i])ᵢ`, is surjective with fibres the
cosets of the period lattice `∏ᵢ pᵢ ℤ` (`AddCircle.pi_coe_surjective`, `AddCircle.pi_coe_eq_iff`),
is an analytic local diffeomorphism (`AddCircle.isLocalDiffeomorph_pi_coe`), and has derivative the
identity of `ι → ℝ` at every point (`AddCircle.hasMFDerivAt_pi_coe`). On `Tⁿ`, it intertwines the
action of `A` on the torus with multiplication of real vectors by the matrix `A`
(`AddCircle.generalLinearGroup_smul_coe_pi`). Hence the derivative of `x ↦ A • x` at every point is
the matrix `A`, acting on `ι → ℝ` (`AddCircle.mfderiv_generalLinearGroup_smul_apply`). Choosing a
basis of the period lattice of a torus is choosing such an `A`: these maps are the changes of angle
coordinates of action–angle charts.

For a torus `∀ i, AddCircle (p i)` with arbitrary positive periods, every translation
`x ↦ x + a` likewise has derivative the identity of `ι → ℝ` (`AddCircle.mfderiv_pi_add_right`).

## Main results

* `AddCircle.pi_coe_surjective`, `AddCircle.pi_coe_eq_iff`: the covering map
  `(ι → ℝ) → ∀ i, AddCircle (p i)` is surjective, and two vectors have the same image exactly when
  they differ by an integer multiple of the periods in each coordinate.
* `AddCircle.isLocalDiffeomorph_pi_coe`, `AddCircle.hasMFDerivAt_pi_coe`,
  `AddCircle.mfderiv_pi_coe`: for positive periods, the covering map is an analytic local
  diffeomorphism with derivative the identity of `ι → ℝ`.
* `AddCircle.instDistribMulActionGeneralLinearGroup`: the action of `GL(ι, ℤ)` on
  `ι → AddCircle p` by additive maps.
* `AddCircle.instContMDiffConstSMulGeneralLinearGroup`: it acts by smooth maps.
* `AddCircle.hasMFDerivAt_pi_add_right`, `AddCircle.mfderiv_pi_add_right`: translations of a torus
  `∀ i, AddCircle (p i)` have derivative the identity.
* `AddCircle.hasMFDerivAt_generalLinearGroup_smul`,
  `AddCircle.mfderiv_generalLinearGroup_smul_apply`: the derivative of `x ↦ A • x` is the matrix
  `A`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (changes of the basis of the period lattice).
-/

public section

noncomputable section

open Function Matrix Set
open scoped Manifold ContDiff

namespace AddCircle

/-! ### The covering map -/

section CoverPi

variable {ι : Type*}

/-- Every point of the torus `∀ i, AddCircle (p i)` is the image of a real vector under the
coordinatewise quotient map. -/
theorem pi_coe_surjective (p : ι → ℝ) :
    Surjective fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p i)) := fun x ↦
  ⟨fun i ↦ Quotient.out (x i), funext fun i ↦ Quotient.out_eq (x i)⟩

/-- Two vectors in `ι → ℝ` have the same image in `∀ i, AddCircle (p i)` if and only if each
coordinate differs by an integer multiple of its period. -/
theorem pi_coe_eq_iff {p : ι → ℝ} {t t' : ι → ℝ} :
    (fun i ↦ (t i : AddCircle (p i))) = (fun i ↦ (t' i : AddCircle (p i))) ↔
      ∃ m : ι → ℤ, t' = t + fun i ↦ p i * m i := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · choose m hm using fun i ↦ AddSubgroup.mem_zmultiples_iff.1
      (QuotientAddGroup.eq_iff_sub_mem.1 (congrFun h i).symm)
    refine ⟨m, funext fun i ↦ ?_⟩
    have hi := hm i
    rw [zsmul_eq_mul, mul_comm, eq_sub_iff_add_eq] at hi
    simpa [add_comm] using hi.symm
  · rintro ⟨m, rfl⟩
    ext i
    simp [Pi.add_apply, mul_comm (p i), ← zsmul_eq_mul]

variable [Fintype ι]

section ArbitraryPeriods

variable {p : ι → ℝ} [∀ i, Fact (0 < p i)]

/-- The covering map `(ι → ℝ) → ∀ i, AddCircle (p i)`, `t ↦ ([t i])ᵢ`, has derivative the identity
of `ι → ℝ`, the tangent spaces of the torus being read in its product charts. -/
theorem hasMFDerivAt_pi_coe (t : ι → ℝ) :
    HasMFDerivAt 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p i))) t (ContinuousLinearMap.id ℝ (ι → ℝ)) :=
  (TauCeti.hasMFDerivAt_pi (M := fun i : ι ↦ AddCircle (p i)) (I := fun _ ↦ 𝓘(ℝ))
    (f := fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p i))) fun i ↦
    (hasMFDerivAt_coe (p i) (t i)).comp t
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).hasMFDerivAt).congr_mfderiv <| by
    -- The product of the coordinate projections is the identity of `ι → ℝ`.
    ext v i
    rfl

/-- The derivative of the covering map `(ι → ℝ) → ∀ i, AddCircle (p i)` is the identity of
`ι → ℝ`. -/
@[simp]
theorem mfderiv_pi_coe (t : ι → ℝ) :
    mfderiv 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p i))) t =
      ContinuousLinearMap.id ℝ (ι → ℝ) :=
  (hasMFDerivAt_pi_coe t).mfderiv

variable (p) in
/-- For positive periods `p i`, the covering map `(ι → ℝ) → ∀ i, AddCircle (p i)` is a `C^n`
local diffeomorphism for every `n : ℕ∞ω` (in particular analytic). -/
theorem isLocalDiffeomorph_pi_coe (n : ℕ∞ω) :
    IsLocalDiffeomorph 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) n
      (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p i))) := fun t ↦ by
  -- Assemble a product partial diffeomorphism around `t` from the inverses of local inverses on
  -- each circle factor.
  let h := fun i ↦ isLocalDiffeomorph_coe (p i) n (t i)
  let Φ := fun i ↦ (h i).localInverse.symm
  let e : OpenPartialHomeomorph (ι → ℝ) (∀ i, AddCircle (p i)) :=
    OpenPartialHomeomorph.pi fun i ↦ (Φ i).toOpenPartialHomeomorph
  let Ψ : PartialDiffeomorph 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (ι → ℝ) (∀ i, AddCircle (p i)) n :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiffOn_pi_iff.2 fun i ↦
        (Φ i).contMDiffOn.comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).contMDiff.contMDiffOn
          fun y hy ↦ hy i trivial
      contMDiffOn_invFun := contMDiffOn_pi_module_iff.2 fun i ↦
        (Φ i).symm.contMDiffOn.comp contMDiff_apply.contMDiffOn fun z hz ↦ hz i trivial }
  refine TauCeti.isLocalDiffeomorphAt_of_eqOn (Φ := Ψ) (fun i _ ↦ (h i).localInverse_mem_target)
    fun y hy ↦ funext fun i ↦ ?_
  have hyi : y i ∈ (h i).localInverse.target := hy i trivial
  have h1 := (h i).localInverse_right_inv ((h i).localInverse.map_target hyi)
  rw [(h i).localInverse.right_inv hyi] at h1
  exact h1

variable (p) in
/-- For positive periods `p i`, the covering map `(ι → ℝ) → ∀ i, AddCircle (p i)` is `C^n` for
every `n : ℕ∞ω` (in particular smooth and analytic). -/
theorem contMDiff_pi_coe (n : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) n
      (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p i))) :=
  (isLocalDiffeomorph_pi_coe p n).contMDiff

end ArbitraryPeriods

end CoverPi

variable (p : ℝ) {ι : Type*} [Fintype ι]

section Cover

variable [Fact (0 < p)]

/-- The covering map `(ι → ℝ) → (ι → AddCircle p)`, `t ↦ ([t i])ᵢ`, has derivative the identity of
`ι → ℝ`, the tangent spaces of the torus being read in its product charts. -/
theorem hasMFDerivAt_coe_pi (t : ι → ℝ) :
    HasMFDerivAt 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle p)) t (ContinuousLinearMap.id ℝ (ι → ℝ)) :=
  hasMFDerivAt_pi_coe t

end Cover

/-! ### Translations -/

section Translation

variable {p : ι → ℝ} [∀ i, Fact (0 < p i)]

/-- Every translation `x ↦ x + a` of the torus `∀ i, AddCircle (p i)` has derivative the identity
of `ι → ℝ`, the tangent spaces of the torus being read in its product charts. -/
theorem hasMFDerivAt_pi_add_right (a x : ∀ i, AddCircle (p i)) :
    HasMFDerivAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (· + a) x (ContinuousLinearMap.id ℝ (ι → ℝ)) := by
  -- Each component is the projection followed by a translation of a circle, whose derivative is
  -- the identity of `ℝ`.
  have h (i : ι) : HasMFDerivAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) 𝓘(ℝ)
      (fun z : ∀ i, AddCircle (p i) ↦ (z + a) i) x (ContinuousLinearMap.proj i) := by
    have h₁ := ((contMDiff_add_right (I := 𝓘(ℝ)) (n := 1) (a := a i)).mdifferentiableAt
      one_ne_zero (x := x i)).hasMFDerivAt
    refine (h₁.comp x (TauCeti.hasMFDerivAt_apply i x)).congr_mfderiv ?_
    rw [mfderiv_add_right]
    exact ContinuousLinearMap.id_comp _
  exact (TauCeti.hasMFDerivAt_pi h).congr_mfderiv ContinuousLinearMap.pi_proj

/-- Every translation `x ↦ x + a` of the torus `∀ i, AddCircle (p i)` has derivative the identity
of `ι → ℝ`. -/
@[simp]
theorem mfderiv_pi_add_right (a x : ∀ i, AddCircle (p i)) :
    mfderiv (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (· + a) x = ContinuousLinearMap.id ℝ (ι → ℝ) :=
  (hasMFDerivAt_pi_add_right a x).mfderiv

end Translation

/-! ### The action of `GL(ι, ℤ)` -/

variable [DecidableEq ι]

/-- An integer matrix `A` acts on the torus `ι → AddCircle p` by `(A • x) i = ∑ j, A i j • x j`. -/
instance instSMulGeneralLinearGroup : SMul (GL ι ℤ) (ι → AddCircle p) where
  smul A x i := ∑ j, (A : Matrix ι ι ℤ) i j • x j

/-- The `i`-th coordinate of `A • x` is `∑ j, A i j • x j`. -/
@[simp]
theorem generalLinearGroup_smul_apply (A : GL ι ℤ) (x : ι → AddCircle p) (i : ι) :
    (A • x) i = ∑ j, (A : Matrix ι ι ℤ) i j • x j :=
  (rfl)

/-- The invertible integer matrices act on the torus `ι → AddCircle p` by additive maps, by matrix
multiplication of the coordinates. -/
instance instDistribMulActionGeneralLinearGroup : DistribMulAction (GL ι ℤ) (ι → AddCircle p) where
  one_smul x := funext fun i ↦ by
    simp [generalLinearGroup_smul_apply, Matrix.one_apply, ite_smul]
  mul_smul A B x := funext fun i ↦ by
    simp only [generalLinearGroup_smul_apply, Units.val_mul, Matrix.mul_apply, Finset.sum_smul,
      Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  smul_zero A := funext fun i ↦ by simp [generalLinearGroup_smul_apply]
  smul_add A x y := funext fun i ↦ by
    simp only [generalLinearGroup_smul_apply, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- The covering map `(ι → ℝ) → (ι → AddCircle p)` intertwines the action of an integer matrix `A`
on the torus with the multiplication of real vectors by `A`. -/
theorem generalLinearGroup_smul_coe_pi (A : GL ι ℤ) (t : ι → ℝ) :
    A • (fun i ↦ (t i : AddCircle p)) =
      fun i ↦ (((A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ) *ᵥ t) i : AddCircle p) :=
  funext fun i ↦ by
    simp only [generalLinearGroup_smul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
      ← zsmul_eq_mul, QuotientAddGroup.mk_sum, coe_zsmul]

/-! ### Smoothness and derivative -/

variable [Fact (0 < p)]

/-- Integer matrices act on the torus `ι → AddCircle p` by smooth maps. -/
instance instContMDiffConstSMulGeneralLinearGroup {n : ℕ∞ω} :
    ContMDiffConstSMul (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) n (GL ι ℤ) (ι → AddCircle p) where
  contMDiff_const_smul A := contMDiff_pi_iff.2 fun i ↦ by
    simp only [generalLinearGroup_smul_apply]
    exact ContMDiff.sum fun j _ ↦ (TauCeti.contMDiff_zsmul (I := 𝓘(ℝ)) _).comp contMDiff_apply

/-- The derivative of the action of an integer matrix `A` on the torus `ι → AddCircle p` is, at
every point, multiplication of tangent vectors `v : ι → ℝ` by the matrix `A`. -/
theorem hasMFDerivAt_generalLinearGroup_smul (A : GL ι ℤ) (x : ι → AddCircle p) :
    HasMFDerivAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun y ↦ A • y) x
      (LinearMap.toContinuousLinearMap (Matrix.toLin' ((A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ)))) := by
  set L := LinearMap.toContinuousLinearMap (Matrix.toLin' ((A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ)))
  obtain ⟨t, rfl⟩ : ∃ t : ι → ℝ, (fun i ↦ (t i : AddCircle p)) = x :=
    ⟨fun i ↦ (QuotientAddGroup.mk_surjective (x i)).choose,
      funext fun i ↦ (QuotientAddGroup.mk_surjective (x i)).choose_spec⟩
  -- The action composed with the covering map is the covering map composed with `L`.
  have hcomp : HasMFDerivAt 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      ((fun y ↦ A • y) ∘ fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle p)) t L := by
    have hfun : ((fun y ↦ A • y) ∘ fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle p)) =
        (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle p)) ∘ L :=
      funext (generalLinearGroup_smul_coe_pi p A)
    rw [hfun]
    exact ((hasMFDerivAt_coe_pi p (L t)).comp t L.hasMFDerivAt).congr_mfderiv
      (ContinuousLinearMap.id_comp L)
  have hd : MDifferentiableAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun y ↦ A • y) (fun i ↦ (t i : AddCircle p)) :=
    ((contMDiff_const_smul A).mdifferentiableAt (n := 1) one_ne_zero)
  have h := mfderiv_comp t hd (hasMFDerivAt_coe_pi p t).mdifferentiableAt
  rw [hcomp.mfderiv, (hasMFDerivAt_coe_pi p t).mfderiv] at h
  have h' : mfderiv (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun y ↦ A • y) (fun i ↦ (t i : AddCircle p)) = L := by
    rw [h]
    exact (ContinuousLinearMap.comp_id _).symm
  exact hd.hasMFDerivAt.congr_mfderiv h'

/-- The derivative of the action of an integer matrix `A` on the torus sends a tangent vector
`v : ι → ℝ` to `A *ᵥ v`. -/
@[simp]
theorem mfderiv_generalLinearGroup_smul_apply (A : GL ι ℤ) (x : ι → AddCircle p) (v : ι → ℝ) :
    mfderiv (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun y ↦ A • y) x v = (A : Matrix ι ι ℤ).map ((↑) : ℤ → ℝ) *ᵥ v := by
  rw [(hasMFDerivAt_generalLinearGroup_smul p A x).mfderiv]
  exact Matrix.toLin'_apply _ v

end AddCircle
