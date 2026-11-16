/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions
public import TauCeti.Topology.Algebra.Group.UCB.Discrete

/-!
# Bounded functions uniformly continuous under small left addition

For a topological additive group `A`, `TauCeti.addUCB A` is the subalgebra of real bounded
continuous functions `f` such that `f (u + x)` is uniformly close to `f x` for all `u` near `0`:

```text
∀ ε > 0,  ∀ᶠ u in 𝓝 0,  ∀ x,  |f (u + x) - f x| < ε.
```

`TauCeti.AddUCB A` is the corresponding type. Because `G →ᵇ ℝ` and `Subalgebra ℝ (G →ᵇ ℝ)` retain
their ring multiplication on the codomain `ℝ`, `TauCeti.UCB` cannot be translated to additive
groups by `@[to_additive]`; this file provides the native additive counterpart and identifies
`AddUCB A` with `UCB (Multiplicative A)` as an ordered Banach algebra, intertwining additive left
and right translations with their multiplicative counterparts.

## Main definitions

* `TauCeti.addUCBSubalgebra 𝕜 A`: the subalgebra of `A →ᵇ 𝕜` of functions uniformly continuous
  under small left addition, for a normed field `𝕜`.
* `TauCeti.addUCB A`, `TauCeti.AddUCB A`: the real case `𝕜 = ℝ` and its carrier type.
* `TauCeti.AddUCB.multiplicativeAlgEquiv`, `TauCeti.AddUCB.multiplicativeLinearIsometryEquiv`:
  the identification `AddUCB A ≃ UCB (Multiplicative A)`.
* `TauCeti.UCB.additiveAlgEquiv`: the inverse identification `UCB G ≃ₐ[ℝ] AddUCB (Additive G)`.
* `TauCeti.AddUCB.leftTranslation`, `TauCeti.AddUCB.rightTranslation`: left translation
  `(L_a f)(x) = f (-a + x)` and right translation `(R_a f)(x) = f (x + a)` on `AddUCB A`.
* `TauCeti.AddUCB.compRightAlgHom`: pullback `f ↦ f ∘ φ` along `φ : A →ₜ+ B`.
* `TauCeti.AddUCB.discreteAlgEquiv`: the identification `AddUCB A ≃ₐ[ℝ] (A →ᵇ ℝ)` for discrete `A`.

## Main results

* `TauCeti.mem_addUCB_iff_tendsto`, `TauCeti.mem_addUCB_iff_uniformContinuous`: characterizations
  by norm continuity of the left-addition orbit at `0` and by right uniform continuity.
* `TauCeti.isClosed_addUCB`: `addUCB A` is closed in `A →ᵇ ℝ`, so `AddUCB A` is complete.
* `TauCeti.AddUCB.multiplicativeAlgEquiv_leftTranslation`: the multiplicative identification
  intertwines `AddUCB.leftTranslation a` with `UCB.leftTranslation (.ofAdd a)`.
* `TauCeti.AddUCB.continuous_leftTranslation_apply`: the orbit map `a ↦ L_a f` is continuous.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix A.3 and Appendix G.1.
-/

public section

noncomputable section

open Filter Topology Multiplicative Additive
open scoped BoundedContinuousFunction

namespace TauCeti

section Subalgebra

variable {𝕜 A : Type*} [NormedField 𝕜] [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]

variable (𝕜 A) in
/-- The bounded continuous functions `f : A →ᵇ 𝕜` such that `f (u + x)` is uniformly close to
`f x` for all `u` near `0`, as a subalgebra of `A →ᵇ 𝕜`. -/
def addUCBSubalgebra : Subalgebra 𝕜 (A →ᵇ 𝕜) where
  carrier := {f | ∀ ε > 0, ∀ᶠ u in 𝓝 (0 : A), ∀ x, ‖f (u + x) - f x‖ < ε}
  mul_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, ← dist_eq_norm,
      ← BoundedContinuousFunction.tendsto_compContinuous_addLeft_iff] at hf hg ⊢
    exact hf.mul hg
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, ← dist_eq_norm,
      ← BoundedContinuousFunction.tendsto_compContinuous_addLeft_iff] at hf hg ⊢
    exact hf.add hg
  algebraMap_mem' c := by
    simp only [Set.mem_ofPred_eq, ← dist_eq_norm,
      ← BoundedContinuousFunction.tendsto_compContinuous_addLeft_iff]
    exact tendsto_const_nhds

/-- The defining condition of `addUCBSubalgebra 𝕜 A`. -/
theorem mem_addUCBSubalgebra_iff {f : A →ᵇ 𝕜} :
    f ∈ addUCBSubalgebra 𝕜 A ↔ ∀ ε > 0, ∀ᶠ u in 𝓝 (0 : A), ∀ x, ‖f (u + x) - f x‖ < ε :=
  Iff.rfl

/-- Membership in `addUCBSubalgebra 𝕜 A` says that `u ↦ f (u + ·)` tends to `f` in supremum norm
as `u → 0`. -/
theorem mem_addUCBSubalgebra_iff_tendsto {f : A →ᵇ 𝕜} :
    f ∈ addUCBSubalgebra 𝕜 A ↔
      Tendsto (fun u => f.compContinuous (ContinuousMap.addLeft u)) (𝓝 0) (𝓝 f) := by
  simp only [mem_addUCBSubalgebra_iff, ← dist_eq_norm,
    BoundedContinuousFunction.tendsto_compContinuous_addLeft_iff]

/-- Precomposition with `Multiplicative.toAdd` sends `addUCBSubalgebra 𝕜 A` onto
`ucbSubalgebra 𝕜 (Multiplicative A)`. -/
theorem compContinuous_toAdd_mem_ucbSubalgebra_iff {f : A →ᵇ 𝕜} :
    f.compContinuous ⟨toAdd, continuous_toAdd⟩ ∈ ucbSubalgebra 𝕜 (Multiplicative A) ↔
      f ∈ addUCBSubalgebra 𝕜 A := by
  have hnhds : 𝓝 (1 : Multiplicative A) = Filter.map ofAdd (𝓝 (0 : A)) := by
    rw [← ofAdd_zero, nhds_ofAdd]
  simp only [mem_ucbSubalgebra_iff, mem_addUCBSubalgebra_iff, hnhds, Filter.eventually_map,
    BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk, Multiplicative.forall,
    ← ofAdd_add, toAdd_ofAdd]

/-- Precomposition with `Multiplicative.ofAdd` sends `ucbSubalgebra 𝕜 (Multiplicative A)` onto
`addUCBSubalgebra 𝕜 A`. -/
theorem compContinuous_ofAdd_mem_addUCBSubalgebra_iff {f : Multiplicative A →ᵇ 𝕜} :
    f.compContinuous ⟨ofAdd, continuous_ofAdd⟩ ∈ addUCBSubalgebra 𝕜 A ↔
      f ∈ ucbSubalgebra 𝕜 (Multiplicative A) := by
  rw [← compContinuous_toAdd_mem_ucbSubalgebra_iff]
  have hf : (f.compContinuous ⟨ofAdd, continuous_ofAdd⟩).compContinuous
      ⟨toAdd, continuous_toAdd⟩ = f := by
    ext x
    simp
  rw [hf]

/-- A bounded continuous function with compact support belongs to `addUCBSubalgebra 𝕜 A`. -/
theorem mem_addUCBSubalgebra_of_hasCompactSupport {f : A →ᵇ 𝕜} (hf : HasCompactSupport f) :
    f ∈ addUCBSubalgebra 𝕜 A := by
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  simpa only [mem_addUCBSubalgebra_iff, dist_eq_norm] using
    (uniformContinuous_addGroup_rightUniformSpace_iff f).1
      (hf.uniformContinuous_of_continuous f.continuous)

end Subalgebra

section Real

variable {A : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]

variable (A) in
/-- The real bounded continuous functions `f` on `A` such that `f (u + x)` is uniformly close to
`f x` for all `u` near `0`, as a subalgebra of `A →ᵇ ℝ`. -/
@[expose]
def addUCB : Subalgebra ℝ (A →ᵇ ℝ) :=
  addUCBSubalgebra ℝ A

variable (A) in
/-- The real Banach algebra of bounded functions on `A` that are uniformly continuous under small
left addition, with the supremum norm, algebra operations and order of `A →ᵇ ℝ`. -/
abbrev AddUCB : Type _ := addUCB A

variable (A) in
/-- `addUCB A` is the case `𝕜 = ℝ` of `addUCBSubalgebra 𝕜 A`. -/
theorem addUCB_eq_addUCBSubalgebra : addUCB A = addUCBSubalgebra ℝ A :=
  rfl

/-- The defining condition of `addUCB A`. -/
theorem mem_addUCB_iff {f : A →ᵇ ℝ} :
    f ∈ addUCB A ↔ ∀ ε > 0, ∀ᶠ u in 𝓝 (0 : A), ∀ x, |f (u + x) - f x| < ε := by
  simp only [addUCB_eq_addUCBSubalgebra, mem_addUCBSubalgebra_iff, Real.norm_eq_abs]

/-- Membership in `addUCB A` says that `u ↦ f (u + ·)` tends to `f` in supremum norm as `u → 0`. -/
theorem mem_addUCB_iff_tendsto {f : A →ᵇ ℝ} :
    f ∈ addUCB A ↔ Tendsto (fun u => f.compContinuous (ContinuousMap.addLeft u)) (𝓝 0) (𝓝 f) := by
  rw [addUCB_eq_addUCBSubalgebra, mem_addUCBSubalgebra_iff_tendsto]

/-- Membership in `addUCB A` is uniform continuity for the right uniformity of `A`. -/
theorem mem_addUCB_iff_uniformContinuous {f : A →ᵇ ℝ} :
    f ∈ addUCB A ↔
      (letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
       UniformContinuous f) := by
  simp only [mem_addUCB_iff, ← Real.dist_eq, uniformContinuous_addGroup_rightUniformSpace_iff]

/-- A bounded continuous function with compact support belongs to `addUCB A`. -/
theorem mem_addUCB_of_hasCompactSupport {f : A →ᵇ ℝ} (hf : HasCompactSupport f) : f ∈ addUCB A :=
  mem_addUCBSubalgebra_of_hasCompactSupport hf

/-- `addUCB A` is closed in `A →ᵇ ℝ`: a uniform limit of functions in `addUCB A` lies in
`addUCB A`. -/
theorem isClosed_addUCB : IsClosed (addUCB A : Set (A →ᵇ ℝ)) := by
  have hpre : (addUCB A : Set (A →ᵇ ℝ)) =
      (fun f : A →ᵇ ℝ => f.compContinuous ⟨toAdd, continuous_toAdd⟩) ⁻¹'
        (ucb (Multiplicative A) : Set (Multiplicative A →ᵇ ℝ)) :=
    Set.ext fun _ => compContinuous_toAdd_mem_ucbSubalgebra_iff.symm
  rw [hpre]
  exact isClosed_ucb.preimage (BoundedContinuousFunction.continuous_compContinuous _)

/-- `AddUCB A` is a real normed group for the supremum norm of `A →ᵇ ℝ`. -/
instance : NormedAddCommGroup (AddUCB A) :=
  inferInstance

/-- `AddUCB A` is a real Banach space. -/
instance : CompleteSpace (AddUCB A) :=
  isClosed_addUCB.completeSpace_coe

/-- Scalar multiplication on `AddUCB A` scales the supremum norm: `‖c • f‖ = ‖c‖ * ‖f‖`. -/
instance : NormSMulClass ℝ (AddUCB A) :=
  ⟨fun c f => norm_smul c (f : A →ᵇ ℝ)⟩

/-- Constant functions belong to `addUCB A`. -/
@[simp]
theorem const_mem_addUCB (c : ℝ) : BoundedContinuousFunction.const A c ∈ addUCB A :=
  fun _ hε => .of_forall fun _ _ => by simpa using hε

/-- `addUCB A` is closed under the pointwise maximum. -/
theorem sup_mem_addUCB {f g : A →ᵇ ℝ} (hf : f ∈ addUCB A) (hg : g ∈ addUCB A) :
    f ⊔ g ∈ addUCB A := by
  rw [mem_addUCB_iff_tendsto] at hf hg ⊢
  exact hf.sup_nhds hg

/-- `addUCB A` is closed under the pointwise minimum. -/
theorem inf_mem_addUCB {f g : A →ᵇ ℝ} (hf : f ∈ addUCB A) (hg : g ∈ addUCB A) :
    f ⊓ g ∈ addUCB A := by
  rw [mem_addUCB_iff_tendsto] at hf hg ⊢
  exact hf.inf_nhds hg

/-- `addUCB A` is closed under the pointwise absolute value. -/
theorem abs_mem_addUCB {f : A →ᵇ ℝ} (hf : f ∈ addUCB A) : |f| ∈ addUCB A :=
  sup_mem_addUCB hf (neg_mem hf)

/-- `AddUCB A` is a lattice for the pointwise maximum and minimum. -/
instance : Lattice (AddUCB A) :=
  Subtype.lattice (fun _ _ => sup_mem_addUCB) (fun _ _ => inf_mem_addUCB)

/-- The supremum norm of `AddUCB A` is solid for its pointwise order, as in `A →ᵇ ℝ`. -/
instance : HasSolidNorm (AddUCB A) where
  solid _ _ h := HasSolidNorm.solid (α := A →ᵇ ℝ) h

namespace AddUCB

/-- Coercion from `AddUCB A` to `A →ᵇ ℝ` commutes with the pointwise maximum. -/
@[simp, norm_cast]
theorem coe_sup (f g : AddUCB A) : ((f ⊔ g : AddUCB A) : A →ᵇ ℝ) = (f : A →ᵇ ℝ) ⊔ (g : A →ᵇ ℝ) :=
  rfl

/-- Coercion from `AddUCB A` to `A →ᵇ ℝ` commutes with the pointwise minimum. -/
@[simp, norm_cast]
theorem coe_inf (f g : AddUCB A) : ((f ⊓ g : AddUCB A) : A →ᵇ ℝ) = (f : A →ᵇ ℝ) ⊓ (g : A →ᵇ ℝ) :=
  rfl

/-- Coercion from `AddUCB A` to `A →ᵇ ℝ` commutes with the pointwise absolute value. -/
@[simp, norm_cast]
theorem coe_abs (f : AddUCB A) : ((|f| : AddUCB A) : A →ᵇ ℝ) = |(f : A →ᵇ ℝ)| :=
  rfl

/-- Two elements of `AddUCB A` are equal when they agree at every point. -/
@[ext]
theorem ext {f g : AddUCB A} (h : ∀ x, (f : A →ᵇ ℝ) x = (g : A →ᵇ ℝ) x) : f = g :=
  Subtype.ext (BoundedContinuousFunction.ext h)

/-- The order on `AddUCB A` is the pointwise order. -/
theorem le_def {f g : AddUCB A} : f ≤ g ↔ ∀ x, (f : A →ᵇ ℝ) x ≤ (g : A →ᵇ ℝ) x :=
  Iff.rfl

/-- Each value of an element of `AddUCB A` is bounded by its supremum norm. -/
theorem abs_apply_le_norm (f : AddUCB A) (x : A) : |(f : A →ᵇ ℝ) x| ≤ ‖f‖ :=
  (f : A →ᵇ ℝ).norm_coe_le_norm x

/-- Every element of `AddUCB A` lies below the constant function with value its supremum norm. -/
theorem le_norm_smul_one (f : AddUCB A) : f ≤ ‖f‖ • 1 :=
  le_def.2 fun x => by simpa using (f : A →ᵇ ℝ).apply_le_norm x

variable (A) in
/-- Precomposition with `Multiplicative.toAdd` identifies `AddUCB A` with
`UCB (Multiplicative A)` as a unital `ℝ`-algebra. -/
def multiplicativeAlgEquiv : AddUCB A ≃ₐ[ℝ] UCB (Multiplicative A) where
  toFun f := ⟨(f : A →ᵇ ℝ).compContinuous ⟨toAdd, continuous_toAdd⟩,
    compContinuous_toAdd_mem_ucbSubalgebra_iff.2 f.2⟩
  invFun g := ⟨(g : Multiplicative A →ᵇ ℝ).compContinuous ⟨ofAdd, continuous_ofAdd⟩,
    compContinuous_ofAdd_mem_addUCBSubalgebra_iff.2 g.2⟩
  left_inv _ := ext fun _ => rfl
  right_inv _ := UCB.ext fun _ => rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Evaluation of `AddUCB.multiplicativeAlgEquiv` at `x : Multiplicative A`. -/
@[simp]
theorem multiplicativeAlgEquiv_apply (f : AddUCB A) (x : Multiplicative A) :
    (multiplicativeAlgEquiv A f : Multiplicative A →ᵇ ℝ) x = (f : A →ᵇ ℝ) x.toAdd :=
  (rfl)

/-- Evaluation of `(AddUCB.multiplicativeAlgEquiv A).symm` at `a : A`. -/
@[simp]
theorem multiplicativeAlgEquiv_symm_apply (g : UCB (Multiplicative A)) (a : A) :
    ((multiplicativeAlgEquiv A).symm g : A →ᵇ ℝ) a = (g : Multiplicative A →ᵇ ℝ) (ofAdd a) :=
  (rfl)

/-- `AddUCB.multiplicativeAlgEquiv` preserves and reflects the pointwise order. -/
@[simp]
theorem multiplicativeAlgEquiv_le_iff {f g : AddUCB A} :
    multiplicativeAlgEquiv A f ≤ multiplicativeAlgEquiv A g ↔ f ≤ g :=
  Multiplicative.forall

/-- `(AddUCB.multiplicativeAlgEquiv A).symm` preserves and reflects the pointwise order. -/
@[simp]
theorem multiplicativeAlgEquiv_symm_le_iff {f g : UCB (Multiplicative A)} :
    (multiplicativeAlgEquiv A).symm f ≤ (multiplicativeAlgEquiv A).symm g ↔ f ≤ g := by
  rw [← multiplicativeAlgEquiv_le_iff, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

/-- `AddUCB.multiplicativeAlgEquiv` preserves the supremum norm. -/
@[simp]
theorem norm_multiplicativeAlgEquiv (f : AddUCB A) :
    ‖(multiplicativeAlgEquiv A f : Multiplicative A →ᵇ ℝ)‖ = ‖(f : A →ᵇ ℝ)‖ := by
  refine le_antisymm ((f : A →ᵇ ℝ).norm_compContinuous_le _) ?_
  calc ‖(f : A →ᵇ ℝ)‖ =
      ‖((multiplicativeAlgEquiv A).symm (multiplicativeAlgEquiv A f) : A →ᵇ ℝ)‖ := by simp
    _ ≤ ‖(multiplicativeAlgEquiv A f : Multiplicative A →ᵇ ℝ)‖ :=
      (multiplicativeAlgEquiv A f : Multiplicative A →ᵇ ℝ).norm_compContinuous_le _

/-- The inverse of `AddUCB.multiplicativeAlgEquiv` also preserves the supremum norm. -/
@[simp]
theorem norm_multiplicativeAlgEquiv_symm (g : UCB (Multiplicative A)) :
    ‖((multiplicativeAlgEquiv A).symm g : A →ᵇ ℝ)‖ = ‖(g : Multiplicative A →ᵇ ℝ)‖ := by
  simpa only [AlgEquiv.apply_symm_apply] using
    (norm_multiplicativeAlgEquiv ((multiplicativeAlgEquiv A).symm g)).symm

variable (A) in
/-- Precomposition with `Multiplicative.toAdd` identifies `AddUCB A` with
`UCB (Multiplicative A)` as a linear isometry equivalence. -/
def multiplicativeLinearIsometryEquiv : AddUCB A ≃ₗᵢ[ℝ] UCB (Multiplicative A) where
  toLinearEquiv := (multiplicativeAlgEquiv A).toLinearEquiv
  norm_map' := norm_multiplicativeAlgEquiv

/-- `AddUCB.multiplicativeLinearIsometryEquiv` agrees with `AddUCB.multiplicativeAlgEquiv`. -/
@[simp]
theorem multiplicativeLinearIsometryEquiv_apply (f : AddUCB A) :
    multiplicativeLinearIsometryEquiv A f = multiplicativeAlgEquiv A f :=
  (rfl)

/-- The inverse of `AddUCB.multiplicativeLinearIsometryEquiv` agrees with that of
`AddUCB.multiplicativeAlgEquiv`. -/
@[simp]
theorem multiplicativeLinearIsometryEquiv_symm_apply (g : UCB (Multiplicative A)) :
    (multiplicativeLinearIsometryEquiv A).symm g = (multiplicativeAlgEquiv A).symm g :=
  (rfl)

end AddUCB

/-- A left translate `x ↦ f (a + x)` of a function in `addUCB A` lies in `addUCB A`. -/
theorem compContinuous_addLeft_mem_addUCB {f : A →ᵇ ℝ} (hf : f ∈ addUCB A) (a : A) :
    f.compContinuous (ContinuousMap.addLeft a) ∈ addUCB A := by
  rw [addUCB_eq_addUCBSubalgebra, ← compContinuous_toAdd_mem_ucbSubalgebra_iff] at hf ⊢
  have h : (f.compContinuous (ContinuousMap.addLeft a)).compContinuous ⟨toAdd, continuous_toAdd⟩ =
      (f.compContinuous ⟨toAdd, continuous_toAdd⟩).compContinuous
        (ContinuousMap.mulLeft (ofAdd a)) := by
    ext x
    rfl
  rw [h]
  exact compContinuous_mulLeft_mem_ucbSubalgebra hf (ofAdd a)

/-- A right translate `x ↦ f (x + a)` of a function in `addUCB A` lies in `addUCB A`. -/
theorem compContinuous_addRight_mem_addUCB {f : A →ᵇ ℝ} (hf : f ∈ addUCB A) (a : A) :
    f.compContinuous (ContinuousMap.addRight a) ∈ addUCB A := by
  rw [addUCB_eq_addUCBSubalgebra, ← compContinuous_toAdd_mem_ucbSubalgebra_iff] at hf ⊢
  exact compContinuous_mulRight_mem_ucbSubalgebra hf (ofAdd a)

namespace AddUCB

/-- Left translation `L_a`, where `(L_a f)(x) = f (-a + x)`, as a linear isometry equivalence of
`AddUCB A`. -/
def leftTranslation (a : A) : AddUCB A ≃ₗᵢ[ℝ] AddUCB A :=
  BoundedContinuousFunction.compContinuousₗᵢ (addUCB A)
    (ContinuousMap.addLeft (-a)) (ContinuousMap.addLeft a) (by simp) (by simp)
    (fun _ hf => compContinuous_addLeft_mem_addUCB hf _)
    (fun _ hf => compContinuous_addLeft_mem_addUCB hf _)

/-- Right translation `R_a`, where `(R_a f)(x) = f (x + a)`, as a linear isometry equivalence of
`AddUCB A`. -/
def rightTranslation (a : A) : AddUCB A ≃ₗᵢ[ℝ] AddUCB A :=
  BoundedContinuousFunction.compContinuousₗᵢ (addUCB A)
    (ContinuousMap.addRight a) (ContinuousMap.addRight (-a)) (by simp) (by simp)
    (fun _ hf => compContinuous_addRight_mem_addUCB hf _)
    (fun _ hf => compContinuous_addRight_mem_addUCB hf _)

/-- The left translate `L_a f` is the precomposition of `f` with `x ↦ -a + x`. -/
theorem coe_leftTranslation (a : A) (f : AddUCB A) :
    (leftTranslation a f : A →ᵇ ℝ) = (f : A →ᵇ ℝ).compContinuous (ContinuousMap.addLeft (-a)) :=
  BoundedContinuousFunction.compContinuousₗᵢ_apply ..

/-- The right translate `R_a f` is the precomposition of `f` with `x ↦ x + a`. -/
theorem coe_rightTranslation (a : A) (f : AddUCB A) :
    (rightTranslation a f : A →ᵇ ℝ) = (f : A →ᵇ ℝ).compContinuous (ContinuousMap.addRight a) :=
  BoundedContinuousFunction.compContinuousₗᵢ_apply ..

/-- Evaluation of the left translate `(L_a f)(x) = f (-a + x)`. -/
@[simp]
theorem leftTranslation_apply (a : A) (f : AddUCB A) (x : A) :
    (leftTranslation a f : A →ᵇ ℝ) x = (f : A →ᵇ ℝ) (-a + x) :=
  DFunLike.congr_fun (coe_leftTranslation a f) x

/-- Evaluation of the right translate `(R_a f)(x) = f (x + a)`. -/
@[simp]
theorem rightTranslation_apply (a : A) (f : AddUCB A) (x : A) :
    (rightTranslation a f : A →ᵇ ℝ) x = (f : A →ᵇ ℝ) (x + a) :=
  DFunLike.congr_fun (coe_rightTranslation a f) x

/-- Left translation by `0` is the identity equivalence. -/
@[simp]
theorem leftTranslation_zero : leftTranslation (0 : A) = .refl ℝ (AddUCB A) := by
  ext
  simp

/-- Left translation by `a + b` is left translation by `b` followed by left translation by `a`. -/
theorem leftTranslation_add (a b : A) (f : AddUCB A) :
    leftTranslation (a + b) f = leftTranslation a (leftTranslation b f) := by
  ext
  simp [add_assoc]

/-- The inverse of left translation by `a` is left translation by `-a`. -/
@[simp]
theorem leftTranslation_symm (a : A) : (leftTranslation a).symm = leftTranslation (-a) := by
  refine LinearIsometryEquiv.ext fun f => ?_
  rw [LinearIsometryEquiv.symm_apply_eq]
  ext x
  simp

/-- Right translation by `0` is the identity equivalence. -/
@[simp]
theorem rightTranslation_zero : rightTranslation (0 : A) = .refl ℝ (AddUCB A) := by
  ext
  simp

/-- Right translation by `a + b` is right translation by `b` followed by right translation by
`a`. -/
theorem rightTranslation_add (a b : A) (f : AddUCB A) :
    rightTranslation (a + b) f = rightTranslation a (rightTranslation b f) := by
  ext
  simp [add_assoc]

/-- The inverse of right translation by `a` is right translation by `-a`. -/
@[simp]
theorem rightTranslation_symm (a : A) : (rightTranslation a).symm = rightTranslation (-a) := by
  refine LinearIsometryEquiv.ext fun f => ?_
  rw [LinearIsometryEquiv.symm_apply_eq]
  ext x
  simp

/-- Left translation fixes the constant function `1`. -/
@[simp]
theorem leftTranslation_apply_one (a : A) : leftTranslation a 1 = 1 := by
  ext
  simp

/-- Left translation fixes every constant function. -/
@[simp]
theorem leftTranslation_apply_algebraMap (a : A) (c : ℝ) :
    leftTranslation a (algebraMap ℝ (AddUCB A) c) = algebraMap ℝ (AddUCB A) c := by
  simp [Algebra.algebraMap_eq_smul_one]

/-- Left translation preserves and reflects the pointwise order. -/
@[simp]
theorem leftTranslation_le_leftTranslation_iff {a : A} {f f' : AddUCB A} :
    leftTranslation a f ≤ leftTranslation a f' ↔ f ≤ f' := by
  refine ⟨fun h => le_def.2 fun x => ?_, fun h => le_def.2 fun x => by simpa using le_def.1 h _⟩
  simpa using le_def.1 h (a + x)

/-- `AddUCB.multiplicativeAlgEquiv` intertwines additive left translation by `a` with
multiplicative left translation by `Multiplicative.ofAdd a`. -/
theorem multiplicativeAlgEquiv_leftTranslation (a : A) (f : AddUCB A) :
    multiplicativeAlgEquiv A (leftTranslation a f) =
      UCB.leftTranslation (ofAdd a) (multiplicativeAlgEquiv A f) := by
  ext x
  simp [← ofAdd_neg]

/-- `(AddUCB.multiplicativeAlgEquiv A).symm` intertwines multiplicative left translation by `g`
with additive left translation by `g.toAdd`. -/
theorem multiplicativeAlgEquiv_symm_leftTranslation (g : Multiplicative A)
    (f : UCB (Multiplicative A)) :
    (multiplicativeAlgEquiv A).symm (UCB.leftTranslation g f) =
      leftTranslation g.toAdd ((multiplicativeAlgEquiv A).symm f) := by
  ext x
  simp [ofAdd_add]

/-- `AddUCB.multiplicativeAlgEquiv` intertwines additive right translation by `a` with
multiplicative right translation by `Multiplicative.ofAdd a`. -/
theorem multiplicativeAlgEquiv_rightTranslation (a : A) (f : AddUCB A) :
    multiplicativeAlgEquiv A (rightTranslation a f) =
      UCB.rightTranslation (ofAdd a) (multiplicativeAlgEquiv A f) := by
  ext x
  simp

/-- The orbit map `a ↦ L_a f` of a function `f` in `AddUCB A` is continuous for the supremum
norm. -/
theorem continuous_leftTranslation_apply (f : AddUCB A) :
    Continuous fun a : A => leftTranslation a f := by
  have h : (fun a : A => leftTranslation a f) =
      fun a => (multiplicativeLinearIsometryEquiv A).symm
        (UCB.leftTranslation (ofAdd a) (multiplicativeAlgEquiv A f)) := by
    ext a x
    simp
  rw [h]
  exact (multiplicativeLinearIsometryEquiv A).symm.continuous.comp
    ((UCB.continuous_leftTranslation_apply _).comp continuous_ofAdd)

end AddUCB

end Real

section AdditiveTag

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Precomposition with `Additive.toMul` sends `ucb G` onto `addUCB (Additive G)`. -/
theorem compContinuous_toMul_mem_addUCB_iff {f : G →ᵇ ℝ} :
    f.compContinuous ⟨toMul, continuous_toMul⟩ ∈ addUCB (Additive G) ↔ f ∈ ucb G := by
  have hnhds : 𝓝 (0 : Additive G) = Filter.map ofMul (𝓝 (1 : G)) := by
    rw [← ofMul_one, nhds_ofMul]
  simp only [mem_addUCB_iff, mem_ucb_iff, hnhds, Filter.eventually_map,
    BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk, Additive.forall,
    ← ofMul_mul, toMul_ofMul]

/-- Precomposition with `Additive.ofMul` sends `addUCB (Additive G)` onto `ucb G`. -/
theorem compContinuous_ofMul_mem_ucb_iff {f : Additive G →ᵇ ℝ} :
    f.compContinuous ⟨ofMul, continuous_ofMul⟩ ∈ ucb G ↔ f ∈ addUCB (Additive G) := by
  rw [← compContinuous_toMul_mem_addUCB_iff]
  have hf : (f.compContinuous ⟨ofMul, continuous_ofMul⟩).compContinuous
      ⟨toMul, continuous_toMul⟩ = f := by
    ext x
    simp
  rw [hf]

variable (G) in
/-- Precomposition with `Additive.toMul` identifies `UCB G` with `AddUCB (Additive G)` as a unital
`ℝ`-algebra. -/
def UCB.additiveAlgEquiv : UCB G ≃ₐ[ℝ] AddUCB (Additive G) where
  toFun f := ⟨(f : G →ᵇ ℝ).compContinuous ⟨toMul, continuous_toMul⟩,
    compContinuous_toMul_mem_addUCB_iff.2 f.2⟩
  invFun g := ⟨(g : Additive G →ᵇ ℝ).compContinuous ⟨ofMul, continuous_ofMul⟩,
    compContinuous_ofMul_mem_ucb_iff.2 g.2⟩
  left_inv _ := UCB.ext fun _ => rfl
  right_inv _ := AddUCB.ext fun _ => rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Evaluation of `UCB.additiveAlgEquiv` at `x : Additive G`. -/
@[simp]
theorem UCB.additiveAlgEquiv_apply (f : UCB G) (x : Additive G) :
    (UCB.additiveAlgEquiv G f : Additive G →ᵇ ℝ) x = (f : G →ᵇ ℝ) x.toMul :=
  (rfl)

/-- Evaluation of `(UCB.additiveAlgEquiv G).symm` at `g : G`. -/
@[simp]
theorem UCB.additiveAlgEquiv_symm_apply (f : AddUCB (Additive G)) (g : G) :
    ((UCB.additiveAlgEquiv G).symm f : G →ᵇ ℝ) g = (f : Additive G →ᵇ ℝ) (ofMul g) :=
  (rfl)

end AdditiveTag

section CompRight

variable {A B C : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [AddGroup C] [TopologicalSpace C] [IsTopologicalAddGroup C]

/-- The pullback `x ↦ f (φ x)` of a function in `addUCB B` along a continuous additive
homomorphism `φ : A →ₜ+ B` lies in `addUCB A`. -/
theorem compContinuous_mem_addUCB {f : B →ᵇ ℝ} (hf : f ∈ addUCB B) (φ : A →ₜ+ B) :
    f.compContinuous (φ : C(A, B)) ∈ addUCB A := by
  have hφ : Tendsto φ (𝓝 0) (𝓝 0) := by
    simpa using φ.continuous.tendsto (0 : A)
  rw [mem_addUCB_iff] at hf ⊢
  intro ε hε
  filter_upwards [hφ.eventually (hf ε hε)] with u hu x
  simpa using hu (φ x)

namespace AddUCB

/-- The pullback `f ↦ f ∘ φ` along a continuous additive homomorphism `φ : A →ₜ+ B`, as a unital
algebra homomorphism from `AddUCB B` to `AddUCB A`. -/
def compRightAlgHom (φ : A →ₜ+ B) : AddUCB B →ₐ[ℝ] AddUCB A where
  toFun f := ⟨(f : B →ᵇ ℝ).compContinuous (φ : C(A, B)), compContinuous_mem_addUCB f.2 φ⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Evaluation of `AddUCB.compRightAlgHom` at `x : A`. -/
@[simp]
theorem compRightAlgHom_apply (φ : A →ₜ+ B) (f : AddUCB B) (x : A) :
    (compRightAlgHom φ f : A →ᵇ ℝ) x = (f : B →ᵇ ℝ) (φ x) :=
  (rfl)

/-- The pullback along the identity is the identity. -/
@[simp]
theorem compRightAlgHom_id :
    compRightAlgHom (ContinuousAddMonoidHom.id A) = AlgHom.id ℝ (AddUCB A) :=
  (rfl)

/-- Pulling back along `ψ ∘ φ` is pulling back along `ψ` and then along `φ`. -/
theorem compRightAlgHom_comp (ψ : B →ₜ+ C) (φ : A →ₜ+ B) :
    compRightAlgHom (ψ.comp φ) = (compRightAlgHom φ).comp (compRightAlgHom ψ) :=
  (rfl)

/-- The pullback preserves the pointwise order. -/
theorem monotone_compRightAlgHom (φ : A →ₜ+ B) : Monotone (compRightAlgHom φ) :=
  fun _ _ h => le_def.2 fun x => le_def.1 h (φ x)

/-- The pullback does not increase the supremum norm. -/
theorem norm_compRightAlgHom_apply_le (φ : A →ₜ+ B) (f : AddUCB B) :
    ‖compRightAlgHom φ f‖ ≤ ‖f‖ :=
  (f : B →ᵇ ℝ).norm_compContinuous_le _

/-- The pullback intertwines left translation by `φ a` with left translation by `a`. -/
theorem compRightAlgHom_leftTranslation (φ : A →ₜ+ B) (a : A) (f : AddUCB B) :
    compRightAlgHom φ (leftTranslation (φ a) f) = leftTranslation a (compRightAlgHom φ f) := by
  ext
  simp

/-- The pullback intertwines right translation by `φ a` with right translation by `a`. -/
theorem compRightAlgHom_rightTranslation (φ : A →ₜ+ B) (a : A) (f : AddUCB B) :
    compRightAlgHom φ (rightTranslation (φ a) f) = rightTranslation a (compRightAlgHom φ f) := by
  ext
  simp

end AddUCB

end CompRight

section Discrete

variable {A : Type*} [AddGroup A] [TopologicalSpace A] [DiscreteTopology A]

/-- On a discrete additive group, `addUCB A` is the entire bounded-function algebra `A →ᵇ ℝ`. -/
@[simp]
theorem addUCB_eq_top : addUCB A = ⊤ := by
  ext f
  simp [mem_addUCB_iff, nhds_discrete]

namespace AddUCB

variable (A) in
/-- The canonical algebra equivalence from `AddUCB A` to all bounded functions on a discrete
additive group `A`. -/
def discreteAlgEquiv : AddUCB A ≃ₐ[ℝ] (A →ᵇ ℝ) :=
  (Subalgebra.equivOfEq _ _ addUCB_eq_top).trans Subalgebra.topEquiv

/-- Evaluation of `AddUCB.discreteAlgEquiv` is coercion to `A →ᵇ ℝ`. -/
@[simp]
theorem discreteAlgEquiv_apply (f : AddUCB A) : discreteAlgEquiv A f = (f : A →ᵇ ℝ) :=
  (rfl)

/-- Coercing `(AddUCB.discreteAlgEquiv A).symm f` back to `A →ᵇ ℝ` recovers `f`. -/
@[simp]
theorem coe_discreteAlgEquiv_symm (f : A →ᵇ ℝ) :
    ((discreteAlgEquiv A).symm f : A →ᵇ ℝ) = f :=
  (discreteAlgEquiv A).apply_symm_apply f

/-- The inverse discrete identification intertwines additive left translation. -/
@[simp]
theorem discreteAlgEquiv_symm_compContinuous_addLeft (a : A) (f : A →ᵇ ℝ) :
    (discreteAlgEquiv A).symm (f.compContinuous (ContinuousMap.addLeft (-a))) =
      leftTranslation a ((discreteAlgEquiv A).symm f) := by
  apply (discreteAlgEquiv A).injective
  simp [coe_leftTranslation]

end AddUCB

end Discrete

end TauCeti
