/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.KernelLemmas

/-!
# Marginalizing the intermediate fiber of a kernel composition-product

Mathlib's `ProbabilityTheory.Kernel.comp_eq_snd_compProd` expresses an ordinary composition
`η ∘ₖ κ` as the second marginal `snd (κ ⊗ₖ prodMkLeft X η)` of a composition-product whose second
kernel ignores the base coordinate. When the second kernel `κ : Kernel (α × β) γ` genuinely
depends on both the base point in `α` and the intermediate fiber in `β`, marginalizing the `β`
coordinate of `η ⊗ₖ κ` feeds `(a, b)` with `b ∼ η a` into `κ`:

`snd (η ⊗ₖ κ) = κ ∘ₖ (Kernel.id ×ₖ η)`.

## Main statements

* `ProbabilityTheory.Kernel.snd_compProd`: for an s-finite kernel `κ : Kernel (α × β) γ` and any
  kernel `η : Kernel α β`, `snd (η ⊗ₖ κ) = κ ∘ₖ (Kernel.id ×ₖ η)`.
-/

public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

/-- Projecting away the intermediate coordinate of `η ⊗ₖ κ` composes `κ` with `Kernel.id ×ₖ η`.
No s-finiteness assumption on `η` is needed because both sides vanish when `η` is not s-finite;
by contrast `IsSFiniteKernel κ` is essential since `η ⊗ₖ κ = 0` when `κ` is not s-finite while
`κ ∘ₖ (Kernel.id ×ₖ η)` need not vanish. -/
theorem snd_compProd (η : Kernel α β) (κ : Kernel (α × β) γ) [IsSFiniteKernel κ] :
    snd (η ⊗ₖ κ) = κ ∘ₖ (Kernel.id ×ₖ η) := by
  by_cases hη : IsSFiniteKernel η
  swap
  · simp [compProd_of_not_isSFiniteKernel_left _ _ hη,
      prod_of_not_isSFiniteKernel_right Kernel.id hη]
  ext a s hs
  rw [snd_apply' _ _ hs, compProd_apply (measurable_snd hs), comp_apply' _ _ _ hs,
    lintegral_id_prod (κ.measurable_coe hs)]
  simp [← Set.preimage_comp]

end ProbabilityTheory.Kernel
