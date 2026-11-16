/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Basic
public import TauCeti.GroupTheory.Amenable.Foelner
public import TauCeti.Topology.Algebra.Group.UCB.Multiplicative
import TauCeti.Topology.Algebra.ContinuousMulEquiv

/-!
# Compatibility of amenability and Følner sets with `Multiplicative` and `Additive`

Precomposing functions on `Multiplicative G` with `Multiplicative.ofAdd` identifies
`TauCeti.UCB (Multiplicative G)` with `TauCeti.AddUCB G` (`TauCeti.UCB.multiplicativeEquiv`) and
intertwines left translations. Dualizing gives an equivalence `TauCeti.Mean.multiplicativeEquiv`
between `TauCeti.Mean (Multiplicative G)` and `TauCeti.AddMean G` that preserves and reflects left
invariance, so `Multiplicative G` is amenable if and only if `G` is additively amenable. The
symmetric equivalences for `Additive G` follow via `TauCeti.AddUCB.additiveEquiv` and
`TauCeti.ContinuousMulEquiv.multiplicativeAdditive`.

Similarly, transporting finite sets along `Multiplicative.ofAdd` and `Multiplicative.toAdd`
identifies `TauCeti.HasFoelnerSets (Multiplicative G)` with `TauCeti.HasAddFoelnerSets G`, and
`TauCeti.HasAddFoelnerSets (Additive G)` with `TauCeti.HasFoelnerSets G`.

## Main definitions

* `TauCeti.Mean.multiplicativeEquiv G`: the equivalence `Mean (Multiplicative G) ≃ AddMean G`.
* `TauCeti.AddMean.additiveEquiv G`: the equivalence `AddMean (Additive G) ≃ Mean G`.

## Main results

* `TauCeti.amenable_multiplicative_iff`, `TauCeti.addAmenable_additive_iff`: equivalence between
  multiplicative and additive amenability under `Multiplicative` and `Additive`.
* `TauCeti.Amenable.multiplicative`, `TauCeti.AddAmenable.additive`: typeclass instances
  transporting amenability across `Multiplicative` and `Additive`.
* `TauCeti.hasFoelnerSets_multiplicative_iff`, `TauCeti.hasAddFoelnerSets_additive_iff`:
  equivalence between multiplicative and additive Følner sets under `Multiplicative` and `Additive`.
-/

public section

noncomputable section

open Finset
open scoped Pointwise symmDiff

namespace TauCeti

section MultiplicativeAmenable

variable {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

namespace Mean

variable (G) in
/-- Means on `UCB (Multiplicative G)` correspond bijectively to means on `AddUCB G` along
`TauCeti.UCB.multiplicativeEquiv`. -/
def multiplicativeEquiv : Mean (Multiplicative G) ≃ AddMean G where
  toFun m := AddMean.mk₀
    (m.toPositiveLinearMap.toLinearMap ∘ₗ (UCB.multiplicativeEquiv G).symm.toLinearMap)
    (fun _ hf => map_nonneg m
      (by simpa using UCB.multiplicativeEquiv_symm_le_multiplicativeEquiv_symm_iff.2 hf))
    (by simp)
  invFun m := Mean.mk₀
    (m.toPositiveLinearMap.toLinearMap ∘ₗ (UCB.multiplicativeEquiv G).toLinearMap)
    (fun _ hf => map_nonneg m
      (by simpa using UCB.multiplicativeEquiv_le_multiplicativeEquiv_iff.2 hf))
    (by simp)
  left_inv m := ext fun f => by simp
  right_inv m := AddMean.ext fun f => by simp

@[simp]
theorem multiplicativeEquiv_apply (m : Mean (Multiplicative G)) (f : AddUCB G) :
    multiplicativeEquiv G m f = m ((UCB.multiplicativeEquiv G).symm f) := by
  simp [multiplicativeEquiv]

@[simp]
theorem multiplicativeEquiv_symm_apply (m : AddMean G) (f : UCB (Multiplicative G)) :
    (multiplicativeEquiv G).symm m f = m (UCB.multiplicativeEquiv G f) := by
  simp [multiplicativeEquiv]

/-- `multiplicativeEquiv` preserves and reflects left invariance of means. -/
@[simp]
theorem isLeftInvariant_multiplicativeEquiv_iff {m : Mean (Multiplicative G)} :
    (multiplicativeEquiv G m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [AddMean.isLeftInvariant_iff, isLeftInvariant_iff]
  constructor
  · intro hm g f
    simpa using hm g.toAdd (UCB.multiplicativeEquiv G f)
  · intro hm g f
    simpa using hm (Multiplicative.ofAdd g) ((UCB.multiplicativeEquiv G).symm f)

/-- `(multiplicativeEquiv G).symm` preserves and reflects left invariance of means. -/
@[simp]
theorem isLeftInvariant_multiplicativeEquiv_symm_iff {m : AddMean G} :
    ((multiplicativeEquiv G).symm m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [← isLeftInvariant_multiplicativeEquiv_iff (G := G), Equiv.apply_symm_apply]

end Mean

variable (G) in
/-- `Multiplicative G` is amenable if and only if `G` is additively amenable. -/
@[simp]
theorem amenable_multiplicative_iff : Amenable (Multiplicative G) ↔ AddAmenable G := by
  rw [amenable_iff, addAmenable_iff]
  exact (Mean.multiplicativeEquiv G).exists_congr fun m =>
    m.isLeftInvariant_multiplicativeEquiv_iff.symm

/-- If `G` is an amenable topological additive group, then `Multiplicative G` is an amenable
topological group. -/
instance Amenable.multiplicative [AddAmenable G] : Amenable (Multiplicative G) :=
  (amenable_multiplicative_iff G).2 ‹_›

end MultiplicativeAmenable

section AdditiveAmenable

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace AddMean

variable (G) in
/-- Means on `AddUCB (Additive G)` correspond bijectively to means on `UCB G` along
`TauCeti.AddUCB.additiveEquiv`. -/
def additiveEquiv : AddMean (Additive G) ≃ Mean G where
  toFun m := Mean.mk₀
    (m.toPositiveLinearMap.toLinearMap ∘ₗ (AddUCB.additiveEquiv G).symm.toLinearMap)
    (fun _ hf => map_nonneg m
      (by simpa using AddUCB.additiveEquiv_symm_le_additiveEquiv_symm_iff.2 hf))
    (by simp)
  invFun m := AddMean.mk₀
    (m.toPositiveLinearMap.toLinearMap ∘ₗ (AddUCB.additiveEquiv G).toLinearMap)
    (fun _ hf => map_nonneg m
      (by simpa using AddUCB.additiveEquiv_le_additiveEquiv_iff.2 hf))
    (by simp)
  left_inv m := ext fun f => by simp
  right_inv m := Mean.ext fun f => by simp

@[simp]
theorem additiveEquiv_apply (m : AddMean (Additive G)) (f : UCB G) :
    additiveEquiv G m f = m ((AddUCB.additiveEquiv G).symm f) := by
  simp [additiveEquiv]

@[simp]
theorem additiveEquiv_symm_apply (m : Mean G) (f : AddUCB (Additive G)) :
    (additiveEquiv G).symm m f = m (AddUCB.additiveEquiv G f) := by
  simp [additiveEquiv]

/-- `additiveEquiv` preserves and reflects left invariance of means. -/
@[simp]
theorem isLeftInvariant_additiveEquiv_iff {m : AddMean (Additive G)} :
    (additiveEquiv G m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [Mean.isLeftInvariant_iff, isLeftInvariant_iff]
  constructor
  · intro hm g f
    simpa using hm g.toMul (AddUCB.additiveEquiv G f)
  · intro hm g f
    simpa using hm (Additive.ofMul g) ((AddUCB.additiveEquiv G).symm f)

/-- `(additiveEquiv G).symm` preserves and reflects left invariance of means. -/
@[simp]
theorem isLeftInvariant_additiveEquiv_symm_iff {m : Mean G} :
    ((additiveEquiv G).symm m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [← isLeftInvariant_additiveEquiv_iff (G := G), Equiv.apply_symm_apply]

end AddMean

variable (G) in
/-- `Additive G` is additively amenable if and only if `G` is amenable. -/
@[simp]
theorem addAmenable_additive_iff : AddAmenable (Additive G) ↔ Amenable G :=
  (amenable_multiplicative_iff (Additive G)).symm.trans
    (ContinuousMulEquiv.multiplicativeAdditive G).amenable_iff

/-- If `G` is an amenable topological group, then `Additive G` is an amenable topological additive
group. -/
instance AddAmenable.additive [Amenable G] : AddAmenable (Additive G) :=
  (addAmenable_additive_iff G).2 ‹_›

end AdditiveAmenable

section Foelner

/-- `Multiplicative G` has Følner sets if and only if `G` has additive Følner sets. -/
@[simp]
theorem hasFoelnerSets_multiplicative_iff (G : Type*) [AddGroup G] :
    HasFoelnerSets (Multiplicative G) ↔ HasAddFoelnerSets G := by
  classical
  rw [hasFoelnerSets_iff, hasAddFoelnerSets_iff]
  have hvadd (g : Multiplicative G) (F : Finset G) :
      g • F.image Multiplicative.ofAdd = (g.toAdd +ᵥ F).image Multiplicative.ofAdd := by
    simp only [smul_finset_def, vadd_finset_def, image_image, smul_eq_mul, vadd_eq_add]
    exact congrArg (F.image ·) (funext fun x => by simp [ofAdd_add])
  have hsmul (g : G) (F : Finset (Multiplicative G)) :
      g +ᵥ F.image Multiplicative.toAdd =
        (Multiplicative.ofAdd g • F).image Multiplicative.toAdd := by
    simp only [vadd_finset_def, smul_finset_def, image_image, vadd_eq_add, smul_eq_mul]
    exact congrArg (F.image ·) (funext fun x => by simp [toAdd_mul])
  constructor
  · intro h K ε hε
    obtain ⟨F, hne, hF⟩ := h (K.image Multiplicative.ofAdd) ε hε
    refine ⟨F.image Multiplicative.toAdd, hne.image _, fun g hg => ?_⟩
    simpa only [hsmul, ← image_symmDiff _ _ Multiplicative.toAdd.injective,
      card_image_of_injective _ Multiplicative.toAdd.injective] using
      hF (Multiplicative.ofAdd g) (mem_image_of_mem _ hg)
  · intro h K ε hε
    obtain ⟨F, hne, hF⟩ := h (K.image Multiplicative.toAdd) ε hε
    refine ⟨F.image Multiplicative.ofAdd, hne.image _, fun g hg => ?_⟩
    simpa only [hvadd, ← image_symmDiff _ _ Multiplicative.ofAdd.injective,
      card_image_of_injective _ Multiplicative.ofAdd.injective] using
      hF g.toAdd (mem_image_of_mem _ hg)

/-- `Additive G` has additive Følner sets if and only if `G` has Følner sets. -/
@[simp]
theorem hasAddFoelnerSets_additive_iff (G : Type*) [Group G] :
    HasAddFoelnerSets (Additive G) ↔ HasFoelnerSets G :=
  (hasFoelnerSets_multiplicative_iff (Additive G)).symm.trans
    (MulEquiv.multiplicativeAdditive G).hasFoelnerSets_iff

end Foelner

end TauCeti
