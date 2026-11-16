/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Star.SelfAdjoint

/-!
# Ordered module instances on self-adjoint elements

When a star additive group `A` carries a preorder and a compatible scalar action of a preordered
type `R` with trivial star (`[StarModule R A]`), the subtype `selfAdjoint A` inherits the ordered
scalar-multiplication classes `PosSMulMono`, `SMulPosMono`, and `IsOrderedModule` from `A` via the
order-reflecting coercion `Subtype.val : selfAdjoint A → A`.
-/

public section

namespace selfAdjoint

section Preorder

variable {R A : Type*} [Star R] [TrivialStar R] [AddGroup A] [StarAddMonoid A]
  [SMul R A] [StarModule R A] [Preorder R] [Preorder A]

instance instPosSMulMono [Zero R] [PosSMulMono R A] : PosSMulMono R (selfAdjoint A) where
  smul_le_smul_of_nonneg_left _ ha _ _ hb := smul_le_smul_of_nonneg_left (α := R) (β := A) hb ha

instance instSMulPosMono [SMulPosMono R A] : SMulPosMono R (selfAdjoint A) where
  smul_le_smul_of_nonneg_right _ hb _ _ ha := smul_le_smul_of_nonneg_right (α := R) (β := A) ha hb

instance instIsOrderedModule [Zero R] [IsOrderedModule R A] :
    IsOrderedModule R (selfAdjoint A) where

end Preorder

end selfAdjoint
