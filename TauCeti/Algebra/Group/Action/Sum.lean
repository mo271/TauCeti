/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import TauCeti.Algebra.Group.Sum

/-!
# Actions of disjoint-sum families of monoids

For indexed families `M : ι → Type*`, `M' : κ → Type*` acting on `U : ι → Type*`, `U' : κ → Type*`,
this file equips `Sum.elim U U' s` with `SMul`, `VAdd`, `MulAction`, and `AddAction` instances for
`Sum.elim M M' s`, reducing definitionally on `Sum.inl i` and `Sum.inr k` to the given actions.
-/

public section

universe u₁ u₂ v₁ v₂

namespace Sum

variable {ι : Type u₁} {κ : Type u₂} {M : ι → Type v₁} {M' : κ → Type v₁}
  {U : ι → Type v₂} {U' : κ → Type v₂}

/-- Scalar action of `Sum.elim M M' s` on `Sum.elim U U' s`. -/
@[to_additive /-- Additive action of `Sum.elim M M' s` on `Sum.elim U U' s`. -/]
instance instSMulElim [∀ i, SMul (M i) (U i)] [∀ k, SMul (M' k) (U' k)] (s : ι ⊕ κ) :
    SMul (Sum.elim M M' s) (Sum.elim U U' s) where
  smul := match s with
    | .inl i => (HSMul.hSMul : M i → U i → U i)
    | .inr k => (HSMul.hSMul : M' k → U' k → U' k)

/-- Multiplicative action of `Sum.elim M M' s` on `Sum.elim U U' s`. -/
@[to_additive /-- Additive monoid action of `Sum.elim M M' s` on `Sum.elim U U' s`. -/]
instance instMulActionElim [∀ i, Monoid (M i)] [∀ k, Monoid (M' k)]
    [∀ i, MulAction (M i) (U i)] [∀ k, MulAction (M' k) (U' k)] (s : ι ⊕ κ) :
    MulAction (Sum.elim M M' s) (Sum.elim U U' s) where
  toSMul := instSMulElim s
  one_smul := by cases s <;> dsimp <;> exact one_smul _
  mul_smul := by cases s <;> dsimp <;> exact mul_smul

end Sum
