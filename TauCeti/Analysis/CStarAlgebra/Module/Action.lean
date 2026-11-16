/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Basic

/-!
# Algebraic and boundedness laws of the coefficient action on C⋆-modules

The inner-product axioms force the given coefficient action to be additive, associative,
and compatible with complex scalars. Over a C⋆-algebra, the norm estimate `‖a • x‖ ≤ ‖a‖ * ‖x‖`
further bundles the action as a contractive complex-bilinear map `CStarModule.smulCLM` (and, for
right Hilbert `A`-modules `CStarModule Aᵐᵒᵖ E`, `CStarModule.opSmulCLM`). For a right Hilbert
`B`-module, take `A = Bᵐᵒᵖ`: then associativity of the left `A`-action gives the usual
right-action law.

The structures here are reducible non-instances, preserving the caller's existing `SMul A E`.
Install them locally, for example with `letI := CStarModule.module A E` when `A` is unital,
to use the ordinary module laws. For nonunital coefficients, use `distribSMul`,
`smulWithZero`, and `semigroupAction`, together with `add_smul`, `neg_smul`, `sub_smul`,
`sum_smul`, and `isBoundedSMul`. Keeping these structures explicit avoids a typeclass-search
cycle through the action required by `CStarModule` itself.
Neither completeness nor the analytic C⋆-algebra axioms are needed for the algebraic laws.

## References

* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2.
* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
-/

public section

open MulOpposite

namespace CStarModule

section NonUnital

variable (A E : Type*) [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A] [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E]
  [CStarModule A E]

/-- The given coefficient action preserves vector addition and zero. -/
abbrev distribSMul : DistribSMul A E where
  smul := (· • ·)
  smul_zero a := by
    apply ext_inner_left (A := A)
    intro y
    simp
  smul_add a x y := by
    apply ext_inner_left (A := A)
    intro z
    simp [mul_add]

/-- Zero coefficients act by zero, also for nonunital coefficient rings. -/
abbrev smulWithZero : SMulWithZero A E where
  toSMulZeroClass := (distribSMul A E).toSMulZeroClass
  zero_smul x := by
    apply ext_inner_left (A := A)
    intro y
    simp

/-- The given coefficient action is associative, also for nonunital coefficient rings. -/
abbrev semigroupAction : SemigroupAction A E where
  smul := (· • ·)
  mul_smul a b x := by
    apply ext_inner_left (A := A)
    intro y
    simp [mul_assoc]

variable {A E}

/-- The action is additive in the coefficient, without requiring a unit. -/
protected theorem add_smul (a b : A) (x : E) : (a + b) • x = a • x + b • x := by
  apply ext_inner_left (A := A)
  intro y
  simp [add_mul]

/-- Negating a coefficient negates its action, without requiring a unit. -/
protected theorem neg_smul (a : A) (x : E) : (-a) • x = -(a • x) := by
  apply eq_neg_of_add_eq_zero_left
  rw [← CStarModule.add_smul, neg_add_cancel]
  exact (smulWithZero A E).zero_smul x

/-- The action preserves coefficient subtraction, without requiring a unit. -/
protected theorem sub_smul (a b : A) (x : E) : (a - b) • x = a • x - b • x := by
  rw [sub_eq_add_neg, CStarModule.add_smul, CStarModule.neg_smul, sub_eq_add_neg]

/-- Finite sums of coefficients act by the sum of their actions, without requiring a unit. -/
protected theorem sum_smul {ι : Type*} (s : Finset ι) (a : ι → A) (x : E) :
    (∑ i ∈ s, a i) • x = ∑ i ∈ s, a i • x := by
  let f : A →+ E :=
    { toFun := (· • x)
      map_zero' := (smulWithZero A E).zero_smul x
      map_add' := fun a b => CStarModule.add_smul a b x }
  exact map_sum f a s

variable (A E)

/-- Complex scaling of a coefficient agrees with successive actions on the module. -/
theorem isScalarTower [IsScalarTower ℂ A A] : IsScalarTower ℂ A E where
  smul_assoc c a x := by
    apply ext_inner_left (A := A)
    intro y
    simp [smul_mul_assoc]

/-- The coefficient action commutes with complex scaling of vectors.
After installing this class locally, `letI := SMulCommClass.symm ℂ A E` supplies the
reverse class for consumers such as linear action maps and pointwise submodule actions. -/
theorem smulCommClass [SMulCommClass ℂ A A] : SMulCommClass ℂ A E where
  smul_comm c a x := by
    apply ext_inner_left (A := A)
    intro y
    simp [mul_smul_comm]

/-- The coefficient action `(· • ·)` bundled as a complex-bilinear map `A →ₗ[ℂ] E →ₗ[ℂ] E`. -/
def smulₗ [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] : A →ₗ[ℂ] E →ₗ[ℂ] E :=
  LinearMap.mk₂ ℂ (· • ·) CStarModule.add_smul (isScalarTower A E).smul_assoc
    (distribSMul A E).smul_add fun c a x ↦ ((smulCommClass A E).smul_comm c a x).symm

/-- Applying `smulₗ A E` evaluates the coefficient action. -/
@[simp]
theorem smulₗ_apply [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (a : A) (x : E) :
    smulₗ A E a x = a • x := (rfl)

end NonUnital

/-- Over a unital coefficient ring, the given action is an ordinary module structure.
This reducible non-instance retains the caller's scalar multiplication. -/
abbrev module (A E : Type*) [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
    [PartialOrder A] [Norm A] [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E]
    [CStarModule A E] : Module A E where
  toSMul := inferInstance
  mul_smul := (semigroupAction A E).mul_smul
  one_smul x := by
    apply ext_inner_left (A := A)
    intro y
    simp
  smul_zero := (distribSMul A E).smul_zero
  smul_add := (distribSMul A E).smul_add
  add_smul := CStarModule.add_smul
  zero_smul := (smulWithZero A E).zero_smul

/-! ### Boundedness and continuity of the action -/

section Bounded

variable (A E : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E]

section Left

/-- The coefficient action of a C⋆-algebra on a Hilbert C⋆-module is a bounded scalar action.
Kept as an explicit theorem rather than an instance to avoid typeclass cycles through `A`. -/
theorem isBoundedSMul [Module ℂ E] [SMul A E] [CStarModule A E] : IsBoundedSMul A E where
  dist_smul_pair' a x y := by
    let _ := distribSMul A E
    rw [dist_zero_right, dist_eq_norm, dist_eq_norm, ← smul_sub]
    exact CStarModule.norm_smul_le a (x - y)
  dist_pair_smul' a b x := by
    rw [dist_zero_right, dist_eq_norm, dist_eq_norm, ← CStarModule.sub_smul]
    exact CStarModule.norm_smul_le (a - b) x

/-- The left coefficient action `(· • ·)` on a Hilbert C⋆-module bundled as a contractive
continuous complex-bilinear map `A →L[ℂ] E →L[ℂ] E`. -/
noncomputable def smulCLM [NormedSpace ℂ E] [SMul A E] [CStarModule A E] :
    A →L[ℂ] E →L[ℂ] E :=
  (smulₗ A E).mkContinuous₂ 1 fun a x ↦ by
    simpa only [one_mul, smulₗ_apply] using CStarModule.norm_smul_le a x

variable {A E}

section CLM

variable [NormedSpace ℂ E] [SMul A E] [CStarModule A E]

/-- Applying `smulCLM A E` evaluates the left coefficient action. -/
@[simp]
theorem smulCLM_apply (a : A) (x : E) : smulCLM A E a x = a • x := (rfl)

/-- Associativity of the bundled left action `smulCLM`. -/
theorem smulCLM_mul (a b : A) (x : E) :
    smulCLM A E (a * b) x = smulCLM A E a (smulCLM A E b x) :=
  (semigroupAction A E).mul_smul a b x

/-- `smulCLM A E` has operator norm at most `1`. -/
theorem norm_smulCLM_le : ‖smulCLM A E‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/-- Acting by `a : A` has operator norm at most `‖a‖`. -/
theorem norm_smulCLM_apply_le (a : A) : ‖smulCLM A E a‖ ≤ ‖a‖ :=
  (smulCLM A E a).opNorm_le_bound (norm_nonneg a) (CStarModule.norm_smul_le a)

end CLM

/-- Joint continuity of the coefficient action `(a, x) ↦ a • x` on a Hilbert C⋆-module. -/
@[continuity, fun_prop]
theorem continuous_smul [Module ℂ E] [SMul A E] [CStarModule A E] :
    Continuous fun p : A × E ↦ p.1 • p.2 := by
  let _ : NormedSpace ℂ E := .ofCore (normedSpaceCore A)
  exact (smulCLM A E).continuous₂

end Left

section Right

/-- The right coefficient action `(x, a) ↦ MulOpposite.op a • x` on a right Hilbert `A`-module
(`CStarModule Aᵐᵒᵖ E`) bundled as a contractive continuous complex-bilinear map
`E →L[ℂ] A →L[ℂ] E`. -/
noncomputable def opSmulCLM [NormedSpace ℂ E] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E] :
    E →L[ℂ] A →L[ℂ] E :=
  ((smulCLM Aᵐᵒᵖ E).comp (MulOpposite.opContinuousLinearEquiv ℂ).toContinuousLinearMap).flip

variable {A E}

section CLM

variable [NormedSpace ℂ E] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]

/-- Applying `opSmulCLM A E` evaluates the right coefficient action `op a • x`. -/
@[simp]
theorem opSmulCLM_apply (x : E) (a : A) : opSmulCLM A E x a = op a • x := (rfl)

/-- Right-module associativity `(x a) b = x (a * b)` of the bundled right action `opSmulCLM`. -/
theorem opSmulCLM_mul (x : E) (a b : A) :
    opSmulCLM A E (opSmulCLM A E x a) b = opSmulCLM A E x (a * b) := by
  simp only [opSmulCLM_apply, op_mul]
  exact ((semigroupAction Aᵐᵒᵖ E).mul_smul (op b) (op a) x).symm

/-- `opSmulCLM A E` has operator norm at most `1`. -/
theorem norm_opSmulCLM_le : ‖opSmulCLM A E‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a ↦ by
      simpa only [one_mul, opSmulCLM_apply] using norm_op_smul_le a x

/-- Acting on `x : E` on the right has operator norm at most `‖x‖`. -/
theorem norm_opSmulCLM_apply_le (x : E) : ‖opSmulCLM A E x‖ ≤ ‖x‖ :=
  (opSmulCLM A E x).opNorm_le_bound (norm_nonneg x) fun a ↦ norm_op_smul_le a x

end CLM

/-- Joint continuity of the right coefficient action `(x, a) ↦ MulOpposite.op a • x` on a right
Hilbert `A`-module. -/
@[continuity, fun_prop]
theorem continuous_op_smul [Module ℂ E] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E] :
    Continuous fun p : E × A ↦ op p.2 • p.1 := by
  let _ : NormedSpace ℂ E := .ofCore (normedSpaceCore Aᵐᵒᵖ)
  exact (opSmulCLM A E).continuous₂

end Right

end Bounded

end CStarModule
