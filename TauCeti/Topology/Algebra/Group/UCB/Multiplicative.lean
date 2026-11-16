/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.UCB.Translation

/-!
# Compatibility of `UCB` and `AddUCB` with `Multiplicative` and `Additive`

For a topological additive group `G`, the type tag `Multiplicative G` carries the same topology and
is a topological group. Precomposing with `Multiplicative.ofAdd` and `Multiplicative.toAdd`
identifies `TauCeti.ucbSubalgebra 𝕜 (Multiplicative G)` with `TauCeti.addUCBSubalgebra 𝕜 G` as
algebras and linear isometries. Specializing to `𝕜 = ℝ` gives `TauCeti.UCB.multiplicativeEquiv`,
which also preserves and reflects the pointwise order and intertwines left and right translations.

Symmetrically, for a topological group `G`, precomposing with `Additive.ofMul` and `Additive.toMul`
gives `TauCeti.addUCBSubalgebra.additiveEquiv` and `TauCeti.AddUCB.additiveEquiv` between
`AddUCB (Additive G)` and `UCB G`.

## Main definitions

* `TauCeti.ucbSubalgebra.multiplicativeEquiv 𝕜 G`: algebra equivalence between
  `ucbSubalgebra 𝕜 (Multiplicative G)` and `addUCBSubalgebra 𝕜 G`.
* `TauCeti.UCB.multiplicativeEquiv G`, `TauCeti.UCB.multiplicativeLinearIsometryEquiv G`: the real
  case `UCB (Multiplicative G) ≃ₐ[ℝ] AddUCB G` and `UCB (Multiplicative G) ≃ₗᵢ[ℝ] AddUCB G`.
* `TauCeti.addUCBSubalgebra.additiveEquiv 𝕜 G`, `TauCeti.AddUCB.additiveEquiv G`,
  `TauCeti.AddUCB.additiveLinearIsometryEquiv G`: the dual equivalences between
  `AddUCB (Additive G)` and `UCB G`.
-/

public section

noncomputable section

open Filter Topology
open scoped BoundedContinuousFunction

namespace TauCeti

section MultiplicativeTag

variable {𝕜 G : Type*} [NormedField 𝕜] [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

/-- Precomposing an element of `addUCBSubalgebra 𝕜 G` with `Multiplicative.toAdd` gives an element
of `ucbSubalgebra 𝕜 (Multiplicative G)`. -/
theorem compContinuous_toAdd_mem_ucbSubalgebra {f : G →ᵇ 𝕜} (hf : f ∈ addUCBSubalgebra 𝕜 G) :
    f.compContinuous ⟨Multiplicative.toAdd, continuous_toAdd⟩ ∈
      ucbSubalgebra 𝕜 (Multiplicative G) := by
  rw [mem_addUCBSubalgebra_iff] at hf
  rw [mem_ucbSubalgebra_iff]
  intro ε hε
  have hnhds : Tendsto (Multiplicative.toAdd : Multiplicative G → G) (𝓝 1) (𝓝 0) :=
    continuous_toAdd.tendsto' 1 0 toAdd_one
  filter_upwards [hnhds.eventually (hf ε hε)] with u hu x
  simpa using hu x.toAdd

/-- Precomposing an element of `ucbSubalgebra 𝕜 (Multiplicative G)` with `Multiplicative.ofAdd`
gives an element of `addUCBSubalgebra 𝕜 G`. -/
theorem compContinuous_ofAdd_mem_addUCBSubalgebra {f : Multiplicative G →ᵇ 𝕜}
    (hf : f ∈ ucbSubalgebra 𝕜 (Multiplicative G)) :
    f.compContinuous ⟨Multiplicative.ofAdd, continuous_ofAdd⟩ ∈ addUCBSubalgebra 𝕜 G := by
  rw [mem_ucbSubalgebra_iff] at hf
  rw [mem_addUCBSubalgebra_iff]
  intro ε hε
  have hnhds : Tendsto (Multiplicative.ofAdd : G → Multiplicative G) (𝓝 0) (𝓝 1) :=
    continuous_ofAdd.tendsto' 0 1 ofAdd_zero
  filter_upwards [hnhds.eventually (hf ε hε)] with u hu x
  simpa [ofAdd_add] using hu (Multiplicative.ofAdd x)

namespace ucbSubalgebra

variable (𝕜 G) in
/-- Precomposing with `Multiplicative.ofAdd` identifies `ucbSubalgebra 𝕜 (Multiplicative G)` with
`addUCBSubalgebra 𝕜 G` as `𝕜`-algebras. -/
def multiplicativeEquiv :
    ucbSubalgebra 𝕜 (Multiplicative G) ≃ₐ[𝕜] addUCBSubalgebra 𝕜 G where
  toFun f := ⟨(f : Multiplicative G →ᵇ 𝕜).compContinuous ⟨Multiplicative.ofAdd, continuous_ofAdd⟩,
    compContinuous_ofAdd_mem_addUCBSubalgebra f.2⟩
  invFun f := ⟨(f : G →ᵇ 𝕜).compContinuous ⟨Multiplicative.toAdd, continuous_toAdd⟩,
    compContinuous_toAdd_mem_ucbSubalgebra f.2⟩
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- `multiplicativeEquiv` precomposes with `Multiplicative.ofAdd`. -/
theorem coe_multiplicativeEquiv (f : ucbSubalgebra 𝕜 (Multiplicative G)) :
    (multiplicativeEquiv 𝕜 G f : G →ᵇ 𝕜) =
      (f : Multiplicative G →ᵇ 𝕜).compContinuous ⟨Multiplicative.ofAdd, continuous_ofAdd⟩ :=
  (rfl)

@[simp]
theorem multiplicativeEquiv_apply (f : ucbSubalgebra 𝕜 (Multiplicative G)) (x : G) :
    (multiplicativeEquiv 𝕜 G f : G →ᵇ 𝕜) x =
      (f : Multiplicative G →ᵇ 𝕜) (Multiplicative.ofAdd x) :=
  (rfl)

/-- The inverse of `multiplicativeEquiv` precomposes with `Multiplicative.toAdd`. -/
theorem coe_multiplicativeEquiv_symm (f : addUCBSubalgebra 𝕜 G) :
    ((multiplicativeEquiv 𝕜 G).symm f : Multiplicative G →ᵇ 𝕜) =
      (f : G →ᵇ 𝕜).compContinuous ⟨Multiplicative.toAdd, continuous_toAdd⟩ :=
  (rfl)

@[simp]
theorem multiplicativeEquiv_symm_apply (f : addUCBSubalgebra 𝕜 G) (x : Multiplicative G) :
    ((multiplicativeEquiv 𝕜 G).symm f : Multiplicative G →ᵇ 𝕜) x = (f : G →ᵇ 𝕜) x.toAdd :=
  (rfl)

/-- `multiplicativeEquiv` preserves the supremum norm. -/
@[simp]
theorem norm_multiplicativeEquiv (f : ucbSubalgebra 𝕜 (Multiplicative G)) :
    ‖(multiplicativeEquiv 𝕜 G f : G →ᵇ 𝕜)‖ = ‖(f : Multiplicative G →ᵇ 𝕜)‖ := by
  refine le_antisymm ((f : Multiplicative G →ᵇ 𝕜).norm_compContinuous_le _) ?_
  have h := (multiplicativeEquiv 𝕜 G f : G →ᵇ 𝕜).norm_compContinuous_le
    (⟨Multiplicative.toAdd, continuous_toAdd⟩ : C(Multiplicative G, G))
  simpa only [← coe_multiplicativeEquiv_symm, AlgEquiv.symm_apply_apply] using h

/-- The inverse of `multiplicativeEquiv` preserves the supremum norm. -/
@[simp]
theorem norm_multiplicativeEquiv_symm (f : addUCBSubalgebra 𝕜 G) :
    ‖((multiplicativeEquiv 𝕜 G).symm f : Multiplicative G →ᵇ 𝕜)‖ = ‖(f : G →ᵇ 𝕜)‖ := by
  simpa only [AlgEquiv.apply_symm_apply] using
    (norm_multiplicativeEquiv ((multiplicativeEquiv 𝕜 G).symm f)).symm

end ucbSubalgebra

namespace UCB

variable (G) in
/-- Precomposing with `Multiplicative.ofAdd` identifies `UCB (Multiplicative G)` with `AddUCB G`
as real algebras; the case `𝕜 = ℝ` of `ucbSubalgebra.multiplicativeEquiv`. -/
def multiplicativeEquiv : UCB (Multiplicative G) ≃ₐ[ℝ] AddUCB G :=
  ucbSubalgebra.multiplicativeEquiv ℝ G

/-- `multiplicativeEquiv` precomposes with `Multiplicative.ofAdd`. -/
theorem coe_multiplicativeEquiv (f : UCB (Multiplicative G)) :
    (multiplicativeEquiv G f : G →ᵇ ℝ) =
      (f : Multiplicative G →ᵇ ℝ).compContinuous ⟨Multiplicative.ofAdd, continuous_ofAdd⟩ :=
  ucbSubalgebra.coe_multiplicativeEquiv f

@[simp]
theorem multiplicativeEquiv_apply (f : UCB (Multiplicative G)) (x : G) :
    (multiplicativeEquiv G f : G →ᵇ ℝ) x = (f : Multiplicative G →ᵇ ℝ) (Multiplicative.ofAdd x) :=
  ucbSubalgebra.multiplicativeEquiv_apply f x

/-- The inverse of `multiplicativeEquiv` precomposes with `Multiplicative.toAdd`. -/
theorem coe_multiplicativeEquiv_symm (f : AddUCB G) :
    ((multiplicativeEquiv G).symm f : Multiplicative G →ᵇ ℝ) =
      (f : G →ᵇ ℝ).compContinuous ⟨Multiplicative.toAdd, continuous_toAdd⟩ :=
  ucbSubalgebra.coe_multiplicativeEquiv_symm f

@[simp]
theorem multiplicativeEquiv_symm_apply (f : AddUCB G) (x : Multiplicative G) :
    ((multiplicativeEquiv G).symm f : Multiplicative G →ᵇ ℝ) x = (f : G →ᵇ ℝ) x.toAdd :=
  ucbSubalgebra.multiplicativeEquiv_symm_apply f x

/-- `multiplicativeEquiv` preserves the supremum norm. -/
@[simp]
theorem norm_multiplicativeEquiv (f : UCB (Multiplicative G)) :
    ‖(multiplicativeEquiv G f : G →ᵇ ℝ)‖ = ‖(f : Multiplicative G →ᵇ ℝ)‖ :=
  ucbSubalgebra.norm_multiplicativeEquiv f

/-- The inverse of `multiplicativeEquiv` preserves the supremum norm. -/
@[simp]
theorem norm_multiplicativeEquiv_symm (f : AddUCB G) :
    ‖((multiplicativeEquiv G).symm f : Multiplicative G →ᵇ ℝ)‖ = ‖(f : G →ᵇ ℝ)‖ :=
  ucbSubalgebra.norm_multiplicativeEquiv_symm f

variable (G) in
/-- `multiplicativeEquiv` as a real linear isometry equivalence. -/
def multiplicativeLinearIsometryEquiv : UCB (Multiplicative G) ≃ₗᵢ[ℝ] AddUCB G :=
  { (multiplicativeEquiv G).toLinearEquiv with norm_map' := norm_multiplicativeEquiv }

@[simp]
theorem multiplicativeLinearIsometryEquiv_apply (f : UCB (Multiplicative G)) :
    multiplicativeLinearIsometryEquiv G f = multiplicativeEquiv G f :=
  (rfl)

@[simp]
theorem multiplicativeLinearIsometryEquiv_symm_apply (f : AddUCB G) :
    (multiplicativeLinearIsometryEquiv G).symm f = (multiplicativeEquiv G).symm f :=
  (rfl)

/-- `multiplicativeEquiv` preserves and reflects the pointwise order. -/
@[simp]
theorem multiplicativeEquiv_le_multiplicativeEquiv_iff {f h : UCB (Multiplicative G)} :
    multiplicativeEquiv G f ≤ multiplicativeEquiv G h ↔ f ≤ h :=
  ⟨fun hle => le_def.2 fun x => by simpa using AddUCB.le_def.1 hle x.toAdd,
    fun hle => AddUCB.le_def.2 fun x => le_def.1 hle (Multiplicative.ofAdd x)⟩

/-- `(multiplicativeEquiv G).symm` preserves and reflects the pointwise order. -/
@[simp]
theorem multiplicativeEquiv_symm_le_multiplicativeEquiv_symm_iff {f h : AddUCB G} :
    (multiplicativeEquiv G).symm f ≤ (multiplicativeEquiv G).symm h ↔ f ≤ h := by
  rw [← multiplicativeEquiv_le_multiplicativeEquiv_iff (G := G), AlgEquiv.apply_symm_apply,
    AlgEquiv.apply_symm_apply]

/-- `multiplicativeEquiv` intertwines multiplicative left translation with additive left
translation. -/
@[simp]
theorem multiplicativeEquiv_leftTranslation (g : Multiplicative G) (f : UCB (Multiplicative G)) :
    multiplicativeEquiv G (leftTranslation g f) =
      AddUCB.leftTranslation g.toAdd (multiplicativeEquiv G f) := by
  ext x
  simp [ofAdd_add]

/-- `(multiplicativeEquiv G).symm` intertwines additive left translation with multiplicative left
translation. -/
@[simp]
theorem multiplicativeEquiv_symm_leftTranslation (g : G) (f : AddUCB G) :
    (multiplicativeEquiv G).symm (AddUCB.leftTranslation g f) =
      leftTranslation (Multiplicative.ofAdd g) ((multiplicativeEquiv G).symm f) := by
  apply (multiplicativeEquiv G).injective
  simp

/-- `multiplicativeEquiv` intertwines multiplicative right translation with additive right
translation. -/
@[simp]
theorem multiplicativeEquiv_rightTranslation (g : Multiplicative G) (f : UCB (Multiplicative G)) :
    multiplicativeEquiv G (rightTranslation g f) =
      AddUCB.rightTranslation g.toAdd (multiplicativeEquiv G f) := by
  ext x
  simp [ofAdd_add]

/-- `(multiplicativeEquiv G).symm` intertwines additive right translation with multiplicative right
translation. -/
@[simp]
theorem multiplicativeEquiv_symm_rightTranslation (g : G) (f : AddUCB G) :
    (multiplicativeEquiv G).symm (AddUCB.rightTranslation g f) =
      rightTranslation (Multiplicative.ofAdd g) ((multiplicativeEquiv G).symm f) := by
  apply (multiplicativeEquiv G).injective
  simp

end UCB

end MultiplicativeTag

section AdditiveTag

variable {𝕜 G : Type*} [NormedField 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Precomposing an element of `ucbSubalgebra 𝕜 G` with `Additive.toMul` gives an element of
`addUCBSubalgebra 𝕜 (Additive G)`. -/
theorem compContinuous_toMul_mem_addUCBSubalgebra {f : G →ᵇ 𝕜} (hf : f ∈ ucbSubalgebra 𝕜 G) :
    f.compContinuous ⟨Additive.toMul, continuous_toMul⟩ ∈ addUCBSubalgebra 𝕜 (Additive G) := by
  rw [mem_ucbSubalgebra_iff] at hf
  rw [mem_addUCBSubalgebra_iff]
  intro ε hε
  have hnhds : Tendsto (Additive.toMul : Additive G → G) (𝓝 0) (𝓝 1) :=
    continuous_toMul.tendsto' 0 1 toMul_zero
  filter_upwards [hnhds.eventually (hf ε hε)] with u hu x
  simpa using hu x.toMul

/-- Precomposing an element of `addUCBSubalgebra 𝕜 (Additive G)` with `Additive.ofMul` gives an
element of `ucbSubalgebra 𝕜 G`. -/
theorem compContinuous_ofMul_mem_ucbSubalgebra {f : Additive G →ᵇ 𝕜}
    (hf : f ∈ addUCBSubalgebra 𝕜 (Additive G)) :
    f.compContinuous ⟨Additive.ofMul, continuous_ofMul⟩ ∈ ucbSubalgebra 𝕜 G := by
  rw [mem_addUCBSubalgebra_iff] at hf
  rw [mem_ucbSubalgebra_iff]
  intro ε hε
  have hnhds : Tendsto (Additive.ofMul : G → Additive G) (𝓝 1) (𝓝 0) :=
    continuous_ofMul.tendsto' 1 0 ofMul_one
  filter_upwards [hnhds.eventually (hf ε hε)] with u hu x
  simpa [ofMul_mul] using hu (Additive.ofMul x)

namespace addUCBSubalgebra

variable (𝕜 G) in
/-- Precomposing with `Additive.ofMul` identifies `addUCBSubalgebra 𝕜 (Additive G)` with
`ucbSubalgebra 𝕜 G` as `𝕜`-algebras. -/
def additiveEquiv :
    addUCBSubalgebra 𝕜 (Additive G) ≃ₐ[𝕜] ucbSubalgebra 𝕜 G where
  toFun f := ⟨(f : Additive G →ᵇ 𝕜).compContinuous ⟨Additive.ofMul, continuous_ofMul⟩,
    compContinuous_ofMul_mem_ucbSubalgebra f.2⟩
  invFun f := ⟨(f : G →ᵇ 𝕜).compContinuous ⟨Additive.toMul, continuous_toMul⟩,
    compContinuous_toMul_mem_addUCBSubalgebra f.2⟩
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- `additiveEquiv` precomposes with `Additive.ofMul`. -/
theorem coe_additiveEquiv (f : addUCBSubalgebra 𝕜 (Additive G)) :
    (additiveEquiv 𝕜 G f : G →ᵇ 𝕜) =
      (f : Additive G →ᵇ 𝕜).compContinuous ⟨Additive.ofMul, continuous_ofMul⟩ :=
  (rfl)

@[simp]
theorem additiveEquiv_apply (f : addUCBSubalgebra 𝕜 (Additive G)) (x : G) :
    (additiveEquiv 𝕜 G f : G →ᵇ 𝕜) x = (f : Additive G →ᵇ 𝕜) (Additive.ofMul x) :=
  (rfl)

/-- The inverse of `additiveEquiv` precomposes with `Additive.toMul`. -/
theorem coe_additiveEquiv_symm (f : ucbSubalgebra 𝕜 G) :
    ((additiveEquiv 𝕜 G).symm f : Additive G →ᵇ 𝕜) =
      (f : G →ᵇ 𝕜).compContinuous ⟨Additive.toMul, continuous_toMul⟩ :=
  (rfl)

@[simp]
theorem additiveEquiv_symm_apply (f : ucbSubalgebra 𝕜 G) (x : Additive G) :
    ((additiveEquiv 𝕜 G).symm f : Additive G →ᵇ 𝕜) x = (f : G →ᵇ 𝕜) x.toMul :=
  (rfl)

/-- `additiveEquiv` preserves the supremum norm. -/
@[simp]
theorem norm_additiveEquiv (f : addUCBSubalgebra 𝕜 (Additive G)) :
    ‖(additiveEquiv 𝕜 G f : G →ᵇ 𝕜)‖ = ‖(f : Additive G →ᵇ 𝕜)‖ := by
  refine le_antisymm ((f : Additive G →ᵇ 𝕜).norm_compContinuous_le _) ?_
  have h := (additiveEquiv 𝕜 G f : G →ᵇ 𝕜).norm_compContinuous_le
    (⟨Additive.toMul, continuous_toMul⟩ : C(Additive G, G))
  simpa only [← coe_additiveEquiv_symm, AlgEquiv.symm_apply_apply] using h

/-- The inverse of `additiveEquiv` preserves the supremum norm. -/
@[simp]
theorem norm_additiveEquiv_symm (f : ucbSubalgebra 𝕜 G) :
    ‖((additiveEquiv 𝕜 G).symm f : Additive G →ᵇ 𝕜)‖ = ‖(f : G →ᵇ 𝕜)‖ := by
  simpa only [AlgEquiv.apply_symm_apply] using
    (norm_additiveEquiv ((additiveEquiv 𝕜 G).symm f)).symm

end addUCBSubalgebra

namespace AddUCB

variable (G) in
/-- Precomposing with `Additive.ofMul` identifies `AddUCB (Additive G)` with `UCB G` as real
algebras; the case `𝕜 = ℝ` of `addUCBSubalgebra.additiveEquiv`. -/
def additiveEquiv : AddUCB (Additive G) ≃ₐ[ℝ] UCB G :=
  addUCBSubalgebra.additiveEquiv ℝ G

/-- `additiveEquiv` precomposes with `Additive.ofMul`. -/
theorem coe_additiveEquiv (f : AddUCB (Additive G)) :
    (additiveEquiv G f : G →ᵇ ℝ) =
      (f : Additive G →ᵇ ℝ).compContinuous ⟨Additive.ofMul, continuous_ofMul⟩ :=
  addUCBSubalgebra.coe_additiveEquiv f

@[simp]
theorem additiveEquiv_apply (f : AddUCB (Additive G)) (x : G) :
    (additiveEquiv G f : G →ᵇ ℝ) x = (f : Additive G →ᵇ ℝ) (Additive.ofMul x) :=
  addUCBSubalgebra.additiveEquiv_apply f x

/-- The inverse of `additiveEquiv` precomposes with `Additive.toMul`. -/
theorem coe_additiveEquiv_symm (f : UCB G) :
    ((additiveEquiv G).symm f : Additive G →ᵇ ℝ) =
      (f : G →ᵇ ℝ).compContinuous ⟨Additive.toMul, continuous_toMul⟩ :=
  addUCBSubalgebra.coe_additiveEquiv_symm f

@[simp]
theorem additiveEquiv_symm_apply (f : UCB G) (x : Additive G) :
    ((additiveEquiv G).symm f : Additive G →ᵇ ℝ) x = (f : G →ᵇ ℝ) x.toMul :=
  addUCBSubalgebra.additiveEquiv_symm_apply f x

/-- `additiveEquiv` preserves the supremum norm. -/
@[simp]
theorem norm_additiveEquiv (f : AddUCB (Additive G)) :
    ‖(additiveEquiv G f : G →ᵇ ℝ)‖ = ‖(f : Additive G →ᵇ ℝ)‖ :=
  addUCBSubalgebra.norm_additiveEquiv f

/-- The inverse of `additiveEquiv` preserves the supremum norm. -/
@[simp]
theorem norm_additiveEquiv_symm (f : UCB G) :
    ‖((additiveEquiv G).symm f : Additive G →ᵇ ℝ)‖ = ‖(f : G →ᵇ ℝ)‖ :=
  addUCBSubalgebra.norm_additiveEquiv_symm f

variable (G) in
/-- `additiveEquiv` as a real linear isometry equivalence. -/
def additiveLinearIsometryEquiv : AddUCB (Additive G) ≃ₗᵢ[ℝ] UCB G :=
  { (additiveEquiv G).toLinearEquiv with norm_map' := norm_additiveEquiv }

@[simp]
theorem additiveLinearIsometryEquiv_apply (f : AddUCB (Additive G)) :
    additiveLinearIsometryEquiv G f = additiveEquiv G f :=
  (rfl)

@[simp]
theorem additiveLinearIsometryEquiv_symm_apply (f : UCB G) :
    (additiveLinearIsometryEquiv G).symm f = (additiveEquiv G).symm f :=
  (rfl)

/-- `additiveEquiv` preserves and reflects the pointwise order. -/
@[simp]
theorem additiveEquiv_le_additiveEquiv_iff {f h : AddUCB (Additive G)} :
    additiveEquiv G f ≤ additiveEquiv G h ↔ f ≤ h :=
  ⟨fun hle => le_def.2 fun x => by simpa using UCB.le_def.1 hle x.toMul,
    fun hle => UCB.le_def.2 fun x => le_def.1 hle (Additive.ofMul x)⟩

/-- `(additiveEquiv G).symm` preserves and reflects the pointwise order. -/
@[simp]
theorem additiveEquiv_symm_le_additiveEquiv_symm_iff {f h : UCB G} :
    (additiveEquiv G).symm f ≤ (additiveEquiv G).symm h ↔ f ≤ h := by
  rw [← additiveEquiv_le_additiveEquiv_iff (G := G), AlgEquiv.apply_symm_apply,
    AlgEquiv.apply_symm_apply]

/-- `additiveEquiv` intertwines additive left translation with multiplicative left translation. -/
@[simp]
theorem additiveEquiv_leftTranslation (g : Additive G) (f : AddUCB (Additive G)) :
    additiveEquiv G (leftTranslation g f) =
      UCB.leftTranslation g.toMul (additiveEquiv G f) := by
  ext x
  simp [ofMul_mul]

/-- `(additiveEquiv G).symm` intertwines multiplicative left translation with additive left
translation. -/
@[simp]
theorem additiveEquiv_symm_leftTranslation (g : G) (f : UCB G) :
    (additiveEquiv G).symm (UCB.leftTranslation g f) =
      leftTranslation (Additive.ofMul g) ((additiveEquiv G).symm f) := by
  apply (additiveEquiv G).injective
  simp

/-- `additiveEquiv` intertwines additive right translation with multiplicative right
translation. -/
@[simp]
theorem additiveEquiv_rightTranslation (g : Additive G) (f : AddUCB (Additive G)) :
    additiveEquiv G (rightTranslation g f) =
      UCB.rightTranslation g.toMul (additiveEquiv G f) := by
  ext x
  simp [ofMul_mul]

/-- `(additiveEquiv G).symm` intertwines multiplicative right translation with additive right
translation. -/
@[simp]
theorem additiveEquiv_symm_rightTranslation (g : G) (f : UCB G) :
    (additiveEquiv G).symm (UCB.rightTranslation g f) =
      rightTranslation (Additive.ofMul g) ((additiveEquiv G).symm f) := by
  apply (additiveEquiv G).injective
  simp

end AddUCB

end AdditiveTag

end TauCeti
