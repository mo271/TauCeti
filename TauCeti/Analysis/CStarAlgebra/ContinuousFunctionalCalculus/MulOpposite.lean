/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import TauCeti.Algebra.Algebra.Quasispectrum

/-!
# Non-unital continuous functional calculus in opposite algebras

Although `MulOpposite.unop : Aᵐᵒᵖ → A` reverses multiplication in general, the algebra
`C(quasispectrum R a, R)₀` of scalar-valued continuous functions on the quasispectrum is
commutative whenever `R` is commutative. Composing `cfcₙHom` in `Aᵐᵒᵖ` with `MulOpposite.unop`
therefore yields a genuine non-unital star algebra homomorphism into `A` sending the identity
function to `MulOpposite.unop a`. When `ContinuousMapZero.UniqueHom R A` holds, uniqueness of the
continuous functional calculus identifies `unop (cfcₙ f a)` with `cfcₙ f (unop a)`.

## Main declarations

* `MulOpposite.unop_cfcₙ_of_iff`, `MulOpposite.op_cfcₙ_of_iff`: `cfcₙ` commutes with `unop` and
  `op` whenever the functional-calculus predicates on `Aᵐᵒᵖ` and `A` correspond under `unop`.
* `MulOpposite.unop_cfcₙ_nonneg`, `MulOpposite.op_cfcₙ_nonneg`: `@[simp]` specializations for the
  nonnegative predicate `(0 ≤ ·)`.
* `MulOpposite.unop_cfcₙ_isSelfAdjoint`, `MulOpposite.op_cfcₙ_isSelfAdjoint`: `@[simp]`
  specializations for `IsSelfAdjoint`.
* `MulOpposite.unop_cfcₙ_isStarNormal`, `MulOpposite.op_cfcₙ_isStarNormal`: `@[simp]`
  specializations for `IsStarNormal`.
-/

public section

open scoped ContinuousMapZero NonUnitalContinuousFunctionalCalculus

namespace MulOpposite

section General

variable {R A : Type*} {p : A → Prop} {q : Aᵐᵒᵖ → Prop}
  [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R]
  [ContinuousStar R] [NonUnitalRing A] [StarRing A] [TopologicalSpace A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalContinuousFunctionalCalculus R A p]
  [NonUnitalContinuousFunctionalCalculus R Aᵐᵒᵖ q]
  [ContinuousMapZero.UniqueHom R A]

/-- The non-unital continuous functional calculus commutes with `MulOpposite.unop` whenever the
domains of the calculi on `Aᵐᵒᵖ` and `A` correspond under `unop`. Both sides take the junk value
`0` simultaneously outside those domains, for discontinuous `f`, or when `f 0 ≠ 0`. -/
theorem unop_cfcₙ_of_iff (f : R → R) (a : Aᵐᵒᵖ) (ha_iff : q a ↔ p (unop a)) :
    unop (cfcₙ f a) = cfcₙ f (unop a) := by
  by_cases ha : q a
  · have ha' : p (unop a) := ha_iff.mp ha
    by_cases hf : ContinuousOn f (quasispectrum R a)
    · have hf' : ContinuousOn f (quasispectrum R (unop a)) := by
        rwa [quasispectrum_unop]
      by_cases hf₀ : f 0 = 0
      · let hsub : quasispectrum R (unop a) ⊆ quasispectrum R a :=
          (quasispectrum_unop R a).subset
        let ι : C(quasispectrum R (unop a), quasispectrum R a)₀ :=
          ⟨⟨Set.inclusion hsub, continuous_id.subtype_map hsub⟩, rfl⟩
        let ψ : C(quasispectrum R a, R)₀ →⋆ₙₐ[R] A :=
          { toFun g := unop (cfcₙHom ha g)
            map_zero' := by simp
            map_add' g₁ g₂ := by simp
            map_mul' g₁ g₂ := by rw [mul_comm g₁ g₂, map_mul, unop_mul]
            map_smul' r g := by simp
            map_star' g := by rw [map_star, unop_star] }
        have hψ_cont : Continuous ψ := continuous_unop.comp (cfcₙHom_continuous ha)
        have hcomp_cont : Continuous
            ((cfcₙHom ha').comp (ContinuousMapZero.nonUnitalStarAlgHom_precomp R ι)) :=
          (cfcₙHom_continuous ha').comp (ContinuousMapZero.continuous_precomp ι)
        have heq : ψ = (cfcₙHom ha').comp (ContinuousMapZero.nonUnitalStarAlgHom_precomp R ι) := by
          refine ContinuousMapZero.UniqueHom.eq_of_continuous_of_map_id _ ψ _ hψ_cont hcomp_cont ?_
          trans cfcₙHom ha' (.id (quasispectrum R (unop a)))
          · simp [ψ, cfcₙHom_id]
          · congr
        rw [cfcₙ_apply f a hf hf₀ ha, cfcₙ_apply f (unop a) hf' hf₀ ha']
        exact DFunLike.congr_fun heq ⟨⟨_, hf.domRestrict⟩, hf₀⟩
      · rw [cfcₙ_apply_of_not_map_zero a hf₀, cfcₙ_apply_of_not_map_zero (unop a) hf₀, unop_zero]
    · have hf' : ¬ ContinuousOn f (quasispectrum R (unop a)) := by
        rwa [quasispectrum_unop]
      rw [cfcₙ_apply_of_not_continuousOn a hf, cfcₙ_apply_of_not_continuousOn (unop a) hf',
        unop_zero]
  · rw [cfcₙ_apply_of_not_predicate a ha,
      cfcₙ_apply_of_not_predicate (unop a) (ha_iff.not.mp ha), unop_zero]

/-- The non-unital continuous functional calculus commutes with `MulOpposite.op` whenever the
domains of the calculi on `Aᵐᵒᵖ` and `A` correspond under `op`. -/
theorem op_cfcₙ_of_iff (f : R → R) (a : A) (ha_iff : q (op a) ↔ p a) :
    op (cfcₙ f a) = cfcₙ f (op a) := by
  rw [← unop_inj, unop_op, unop_cfcₙ_of_iff f (op a) (by simpa using ha_iff), unop_op]

end General

section Predicates

variable {R A : Type*}
  [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R]
  [ContinuousStar R] [NonUnitalRing A] [StarRing A] [TopologicalSpace A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [ContinuousMapZero.UniqueHom R A]

/-- For the nonnegative functional-calculus predicate `(0 ≤ ·)`, `cfcₙ` commutes with `unop`. -/
@[simp]
theorem unop_cfcₙ_nonneg [PartialOrder A]
    [NonUnitalContinuousFunctionalCalculus R A (0 ≤ ·)]
    [NonUnitalContinuousFunctionalCalculus R Aᵐᵒᵖ (0 ≤ ·)]
    (f : R → R) (a : Aᵐᵒᵖ) :
    unop (cfcₙ f a) = cfcₙ f (unop a) :=
  unop_cfcₙ_of_iff f a unop_nonneg.symm

/-- For the nonnegative functional-calculus predicate `(0 ≤ ·)`, `cfcₙ` commutes with `op`. -/
@[simp]
theorem op_cfcₙ_nonneg [PartialOrder A]
    [NonUnitalContinuousFunctionalCalculus R A (0 ≤ ·)]
    [NonUnitalContinuousFunctionalCalculus R Aᵐᵒᵖ (0 ≤ ·)]
    (f : R → R) (a : A) :
    op (cfcₙ f a) = cfcₙ f (op a) :=
  op_cfcₙ_of_iff f a op_nonneg

/-- For the self-adjoint functional-calculus predicate `IsSelfAdjoint`, `cfcₙ` commutes with
`unop`. -/
@[simp]
theorem unop_cfcₙ_isSelfAdjoint
    [NonUnitalContinuousFunctionalCalculus R A IsSelfAdjoint]
    [NonUnitalContinuousFunctionalCalculus R Aᵐᵒᵖ IsSelfAdjoint]
    (f : R → R) (a : Aᵐᵒᵖ) :
    unop (cfcₙ f a) = cfcₙ f (unop a) :=
  unop_cfcₙ_of_iff f a (by simp [IsSelfAdjoint, ← unop_star, unop_inj])

/-- For the self-adjoint functional-calculus predicate `IsSelfAdjoint`, `cfcₙ` commutes with
`op`. -/
@[simp]
theorem op_cfcₙ_isSelfAdjoint
    [NonUnitalContinuousFunctionalCalculus R A IsSelfAdjoint]
    [NonUnitalContinuousFunctionalCalculus R Aᵐᵒᵖ IsSelfAdjoint]
    (f : R → R) (a : A) :
    op (cfcₙ f a) = cfcₙ f (op a) :=
  op_cfcₙ_of_iff f a (by simp [IsSelfAdjoint, ← op_star, op_inj])

/-- For the normal functional-calculus predicate `IsStarNormal`, `cfcₙ` commutes with `unop`. -/
@[simp]
theorem unop_cfcₙ_isStarNormal
    [NonUnitalContinuousFunctionalCalculus R A IsStarNormal]
    [NonUnitalContinuousFunctionalCalculus R Aᵐᵒᵖ IsStarNormal]
    (f : R → R) (a : Aᵐᵒᵖ) :
    unop (cfcₙ f a) = cfcₙ f (unop a) :=
  unop_cfcₙ_of_iff f a (by simp [isStarNormal_iff, commute_iff_eq, ← unop_star, ← unop_mul,
    unop_inj, eq_comm])

/-- For the normal functional-calculus predicate `IsStarNormal`, `cfcₙ` commutes with `op`. -/
@[simp]
theorem op_cfcₙ_isStarNormal
    [NonUnitalContinuousFunctionalCalculus R A IsStarNormal]
    [NonUnitalContinuousFunctionalCalculus R Aᵐᵒᵖ IsStarNormal]
    (f : R → R) (a : A) :
    op (cfcₙ f a) = cfcₙ f (op a) :=
  op_cfcₙ_of_iff f a (by simp [isStarNormal_iff, commute_iff_eq, ← op_star, ← op_mul, op_inj,
    eq_comm])

end Predicates

end MulOpposite
