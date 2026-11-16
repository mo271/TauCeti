/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# Disjoint-sum families of monoids and groups

For `M : ι → Type*` and `M' : κ → Type*`, this file equips `Sum.elim M M' s` with `Monoid`,
`AddMonoid`, `Group`, and `AddGroup` instances for every `s : ι ⊕ κ`, with `instGroupElim`
extending `instMonoidElim` directly so forgetting to `Monoid` has no diamond on variable `s`.
-/

public section

universe u₁ u₂ v

namespace Sum

variable {ι : Type u₁} {κ : Type u₂} {M : ι → Type v} {M' : κ → Type v}

/-- Monoid structure on the disjoint-sum family `Sum.elim M M' s`. -/
@[to_additive /-- Additive monoid structure on the disjoint-sum family `Sum.elim M M' s`. -/]
instance instMonoidElim [∀ i, Monoid (M i)] [∀ k, Monoid (M' k)] (s : ι ⊕ κ) :
    Monoid (Sum.elim M M' s) where
  one := match s with | .inl i => (1 : M i) | .inr k => (1 : M' k)
  mul := match s with
    | .inl i => ((· * ·) : M i → M i → M i)
    | .inr k => ((· * ·) : M' k → M' k → M' k)
  npow n := match s with
    | .inl i => (inferInstance : Monoid (M i)).npow n
    | .inr k => (inferInstance : Monoid (M' k)).npow n
  mul_assoc := by cases s <;> dsimp <;> exact mul_assoc
  one_mul := by cases s <;> dsimp <;> exact one_mul
  mul_one := by cases s <;> dsimp <;> exact mul_one
  npow_zero := by cases s <;> dsimp <;> exact Monoid.npow_zero
  npow_succ n := by cases s <;> dsimp <;> exact Monoid.npow_succ n

/-- Group structure on `Sum.elim M M' s`, extending `instMonoidElim` with no `Monoid` diamond. -/
@[to_additive /-- Additive group structure on `Sum.elim M M' s`, extending `instAddMonoidElim`
  with no `AddMonoid` diamond. -/]
instance instGroupElim [∀ i, Group (M i)] [∀ k, Group (M' k)] (s : ι ⊕ κ) :
    Group (Sum.elim M M' s) where
  toMonoid := instMonoidElim s
  inv := match s with | .inl i => (Inv.inv : M i → M i) | .inr k => (Inv.inv : M' k → M' k)
  div := match s with
    | .inl i => ((· / ·) : M i → M i → M i)
    | .inr k => ((· / ·) : M' k → M' k → M' k)
  zpow n := match s with
    | .inl i => (inferInstance : DivInvMonoid (M i)).zpow n
    | .inr k => (inferInstance : DivInvMonoid (M' k)).zpow n
  div_eq_mul_inv := by cases s <;> dsimp <;> exact div_eq_mul_inv
  zpow_zero' := by cases s <;> dsimp <;> exact DivInvMonoid.zpow_zero'
  zpow_succ' n := by cases s <;> dsimp <;> exact DivInvMonoid.zpow_succ' n
  zpow_neg' n := by cases s <;> dsimp <;> exact DivInvMonoid.zpow_neg' n
  inv_mul_cancel := by cases s <;> dsimp <;> exact inv_mul_cancel

end Sum
