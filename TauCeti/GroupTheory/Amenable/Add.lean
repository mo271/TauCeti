/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Content
public import TauCeti.GroupTheory.Amenable.DirectedUnion
public import TauCeti.GroupTheory.Amenable.DiscreteFoelner
public import TauCeti.GroupTheory.Amenable.Extension
public import TauCeti.GroupTheory.Amenable.Linfty
public import TauCeti.GroupTheory.Amenable.Prod
public import TauCeti.GroupTheory.Amenable.Sequence
public import TauCeti.Topology.Algebra.ContinuousMulEquiv
public import TauCeti.Topology.Algebra.Group.UCB.Add

/-!
# Amenable topological additive groups

For a topological additive group `A`, a *mean* on `TauCeti.AddUCB A` (`TauCeti.AddMean A`) is a
positive normalized real linear functional (`0 ≤ f → 0 ≤ m f`, `m 1 = 1`). It is *left invariant*
(`TauCeti.AddMean.IsLeftInvariant`) when `m (L_a f) = m f` for all `a : A` and `f : AddUCB A`, where
`(L_a f)(x) = f (-a + x)`. A topological additive group is *amenable* (`TauCeti.AddAmenable A`) when
`AddUCB A` carries a left-invariant mean.

Because `AddUCB A` and `AddMean A` use the ring multiplication and real linear structure of the
codomain `ℝ`, `@[to_additive]` cannot generate `AddMean` or `AddAmenable` from `Mean` and
`Amenable`. Instead, `TauCeti.AddUCB.multiplicativeAlgEquiv` identifies `AddMean A` with
`Mean (Multiplicative A)` compatibly with left invariance, yielding
`Amenable (Multiplicative A) ↔ AddAmenable A` and `AddAmenable (Additive G) ↔ Amenable G` along
with loop-free instances on `Multiplicative A` and `Additive G` (following the pattern of
`IsMulFG` and `IsAddFG` in `Mathlib.GroupTheory.Finiteness`). From this bridge we derive the full
closure and Følner-set API directly for additive groups `A` without requiring callers to pass
through `Multiplicative`.

## Main definitions

* `TauCeti.AddMean A`: a positive normalized real linear functional on `AddUCB A`.
* `TauCeti.AddMean.IsLeftInvariant`: invariance under additive left translations `L_a`.
* `TauCeti.AddMean.map`: pushforward of means along `φ : A →ₜ+ B`.
* `TauCeti.AddMean.multiplicativeEquiv`: equivalence `AddMean A ≃ Mean (Multiplicative A)`.
* `TauCeti.Mean.additiveEquiv`: equivalence `Mean G ≃ AddMean (Additive G)`.
* `TauCeti.AddAmenable A`: amenability of a topological additive group `A`.

## Main results

* `TauCeti.amenable_multiplicative_iff`, `TauCeti.addAmenable_additive_iff`: compatibility of
  `Amenable` and `AddAmenable` with `Multiplicative` and `Additive`, plus instances
  `TauCeti.Amenable.multiplicative` and `TauCeti.AddAmenable.additive`.
* `TauCeti.AddAmenable.of_denseRange`, `TauCeti.AddAmenable.of_surjective`,
  `ContinuousAddEquiv.addAmenable_iff`, `TauCeti.AddAmenable.of_le`,
  `TauCeti.AddAmenable.of_discrete`: functoriality and topology comparison.
* `TauCeti.AddAmenable.of_finite`, `TauCeti.AddAmenable.of_compactSpace`: finite and compact
  topological additive groups are amenable.
* `TauCeti.addAmenable_iff_hasAddFoelnerSets`, `TauCeti.addAmenable_iff_exists_finset`,
  `TauCeti.addAmenable_iff_exists_seq`, `TauCeti.addAmenable_iff_exists_invariantContent`:
  discrete characterizations via additive Følner sets, Følner sequences, and finitely additive
  probabilities.
* `TauCeti.AddAmenable.addSubgroup`, `TauCeti.AddAmenable.of_ker_le_range`,
  `TauCeti.AddAmenable.prod`, `TauCeti.AddAmenable.pi`,
  `TauCeti.addAmenable_iSup_of_directed`, `TauCeti.AddAmenable.of_forall_fg`: closure under
  discrete subgroups and extensions, topological products, directed suprema, and finitely
  generated subgroups.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.
* A. Garrido, *An introduction to amenable groups*, §§1–3.
-/

public section

noncomputable section

open Filter Topology Multiplicative Additive MeasureTheory Finset
open scoped BoundedContinuousFunction ENNReal Pointwise symmDiff

namespace TauCeti

section AddMean

variable {A B C : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [AddGroup C] [TopologicalSpace C] [IsTopologicalAddGroup C]

variable (A) in
/-- A mean on `AddUCB A`: a positive real linear functional taking the value `1` at the constant
function `1`. -/
structure AddMean extends AddUCB A →ₚ[ℝ] ℝ where
  /-- A mean takes the value `1` at the constant function `1`. -/
  map_one' : toFun 1 = 1

namespace AddMean

/-- Coercion of an `AddMean A` to a function `AddUCB A → ℝ`. -/
instance : FunLike (AddMean A) (AddUCB A) ℝ where
  coe m := m.toFun
  coe_injective := by
    rintro ⟨_, _⟩ ⟨_, _⟩ h
    congr
    exact DFunLike.coe_injective h

/-- An `AddMean A` is an `ℝ`-linear functional on `AddUCB A`. -/
instance : LinearMapClass (AddMean A) ℝ (AddUCB A) ℝ where
  map_add m := map_add m.toPositiveLinearMap
  map_smulₛₗ m := map_smul m.toPositiveLinearMap

/-- An `AddMean A` is monotone for the pointwise order on `AddUCB A`. -/
instance : OrderHomClass (AddMean A) (AddUCB A) ℝ where
  map_rel m _ _ h := OrderHomClass.mono m.toPositiveLinearMap h

/-- Two means on `AddUCB A` are equal when they agree on every function. -/
@[ext]
theorem ext {m n : AddMean A} (h : ∀ f, m f = n f) : m = n :=
  DFunLike.ext m n h

/-- Coercing `m.toPositiveLinearMap` to a function gives `m`. -/
@[simp]
theorem coe_toPositiveLinearMap (m : AddMean A) : ⇑m.toPositiveLinearMap = ⇑m :=
  (rfl)

/-- A mean takes the value `1` at the constant function `1`. -/
@[simp]
theorem map_one (m : AddMean A) : m 1 = 1 :=
  m.map_one'

/-- Build an `AddMean A` from a linear functional which is nonnegative on nonnegative functions and
takes the value `1` at `1`. -/
def mk₀ (φ : AddUCB A →ₗ[ℝ] ℝ) (hφ : ∀ f, 0 ≤ f → 0 ≤ φ f) (h₁ : φ 1 = 1) : AddMean A :=
  { PositiveLinearMap.mk₀ φ hφ with map_one' := h₁ }

/-- Evaluation of `AddMean.mk₀`. -/
@[simp]
theorem mk₀_apply (φ : AddUCB A →ₗ[ℝ] ℝ) (hφ : ∀ f, 0 ≤ f → 0 ≤ φ f) (h₁ : φ 1 = 1)
    (f : AddUCB A) : mk₀ φ hφ h₁ f = φ f :=
  (rfl)

/-- A mean takes the value `c` at the constant function `c`. -/
@[simp]
theorem map_algebraMap (m : AddMean A) (c : ℝ) : m (algebraMap ℝ (AddUCB A) c) = c := by
  simp [Algebra.algebraMap_eq_smul_one]

/-- A mean of a function is bounded in absolute value by its supremum norm. -/
theorem abs_apply_le_norm (m : AddMean A) (f : AddUCB A) : |m f| ≤ ‖f‖ := by
  simpa using PositiveLinearMap.abs_apply_le_mul_norm m (AddUCB.le_norm_smul_one (A := A)) f

/-- A mean on `AddUCB A` is `1`-Lipschitz for the supremum norm. -/
theorem lipschitzWith (m : AddMean A) : LipschitzWith 1 m := by
  simpa using
    PositiveLinearMap.lipschitzWith_of_forall_le_norm_smul m (AddUCB.le_norm_smul_one (A := A))

/-- A mean on `AddUCB A` is continuous for the supremum norm. -/
instance : ContinuousLinearMapClass (AddMean A) ℝ (AddUCB A) ℝ where
  map_continuous m := m.lipschitzWith.continuous

/-- The continuous linear functional underlying an `AddMean A`. -/
def toContinuousLinearMap (m : AddMean A) : AddUCB A →L[ℝ] ℝ where
  toLinearMap := m.toPositiveLinearMap.toLinearMap
  cont := map_continuous m

/-- Coercing `m.toContinuousLinearMap` to a function gives `m`. -/
@[simp]
theorem coe_toContinuousLinearMap (m : AddMean A) : ⇑m.toContinuousLinearMap = ⇑m :=
  (rfl)

/-- A mean on `AddUCB A` has operator norm one. -/
@[simp]
theorem norm_toContinuousLinearMap (m : AddMean A) : ‖m.toContinuousLinearMap‖ = 1 := by
  rw [m.toContinuousLinearMap.opNorm_eq_apply_of_monotone (OrderHomClass.mono m)
    AddUCB.le_norm_smul_one norm_one.le]
  simp

variable (A) in
/-- Evaluation at a point of `A` is a mean on `AddUCB A`. -/
def eval (x : A) : AddMean A :=
  mk₀ ((BoundedContinuousFunction.evalCLM ℝ x).toLinearMap ∘ₗ (addUCB A).val.toLinearMap)
    (fun _ hf => AddUCB.le_def.1 hf x) rfl

/-- Evaluation of `AddMean.eval A x` at `f`. -/
@[simp]
theorem eval_apply (x : A) (f : AddUCB A) : eval A x f = (f : A →ᵇ ℝ) x :=
  (rfl)

/-- The space of means on `AddUCB A` is nonempty, witnessed by evaluation at `0`. -/
instance : Nonempty (AddMean A) :=
  ⟨eval A 0⟩

/-- A mean `m` on `AddUCB A` is left invariant when `m (L_a f) = m f` for every `a : A` and
`f : AddUCB A`, where `(L_a f)(x) = f (-a + x)`. -/
def IsLeftInvariant (m : AddMean A) : Prop :=
  ∀ (a : A) (f : AddUCB A), m (AddUCB.leftTranslation a f) = m f

/-- The defining property of a left-invariant mean on `AddUCB A`. -/
theorem isLeftInvariant_iff {m : AddMean A} :
    m.IsLeftInvariant ↔ ∀ (a : A) (f : AddUCB A), m (AddUCB.leftTranslation a f) = m f :=
  Iff.rfl

/-- A left-invariant mean takes the same value at a function and at its left translates. -/
@[simp]
theorem IsLeftInvariant.apply_leftTranslation {m : AddMean A} (hm : m.IsLeftInvariant) (a : A)
    (f : AddUCB A) : m (AddUCB.leftTranslation a f) = m f :=
  hm a f

variable (A) in
/-- Equivalence between means on `AddUCB A` and means on `UCB (Multiplicative A)`, induced by
`AddUCB.multiplicativeAlgEquiv`. -/
def multiplicativeEquiv : AddMean A ≃ Mean (Multiplicative A) where
  toFun m := Mean.mk₀
    (m.toPositiveLinearMap.toLinearMap ∘ₗ (AddUCB.multiplicativeAlgEquiv A).symm.toLinearMap)
    (fun _ hf => map_nonneg m (by simpa using AddUCB.multiplicativeAlgEquiv_symm_le_iff.2 hf))
    (by simp)
  invFun n := mk₀
    (n.toPositiveLinearMap.toLinearMap ∘ₗ (AddUCB.multiplicativeAlgEquiv A).toLinearMap)
    (fun _ hf => map_nonneg n (by simpa using AddUCB.multiplicativeAlgEquiv_le_iff.2 hf))
    (by simp)
  left_inv m := ext fun f => by simp
  right_inv n := Mean.ext fun f => by simp

/-- Evaluation of `AddMean.multiplicativeEquiv`. -/
@[simp]
theorem multiplicativeEquiv_apply (m : AddMean A) (f : UCB (Multiplicative A)) :
    multiplicativeEquiv A m f = m ((AddUCB.multiplicativeAlgEquiv A).symm f) :=
  Mean.mk₀_apply _ _ _ f

/-- Evaluation of `(AddMean.multiplicativeEquiv A).symm`. -/
@[simp]
theorem multiplicativeEquiv_symm_apply (n : Mean (Multiplicative A)) (f : AddUCB A) :
    (multiplicativeEquiv A).symm n f = n (AddUCB.multiplicativeAlgEquiv A f) :=
  (rfl)

/-- `AddMean.multiplicativeEquiv` preserves and reflects left invariance. -/
@[simp]
theorem isLeftInvariant_multiplicativeEquiv_iff (m : AddMean A) :
    (multiplicativeEquiv A m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [Mean.isLeftInvariant_iff, isLeftInvariant_iff]
  refine ⟨fun hm a f => ?_, fun hm g f => ?_⟩
  · simpa [← AddUCB.multiplicativeAlgEquiv_leftTranslation] using
      hm (ofAdd a) (AddUCB.multiplicativeAlgEquiv A f)
  · simp [AddUCB.multiplicativeAlgEquiv_symm_leftTranslation, hm]

/-- `(AddMean.multiplicativeEquiv A).symm` preserves and reflects left invariance. -/
@[simp]
theorem isLeftInvariant_multiplicativeEquiv_symm_iff (n : Mean (Multiplicative A)) :
    ((multiplicativeEquiv A).symm n).IsLeftInvariant ↔ n.IsLeftInvariant := by
  rw [← isLeftInvariant_multiplicativeEquiv_iff, Equiv.apply_symm_apply]

/-- The pushforward `f ↦ m (f ∘ φ)` of a mean `m` on `AddUCB A` along a continuous additive
homomorphism `φ : A →ₜ+ B`, as a mean on `AddUCB B`. -/
def map (φ : A →ₜ+ B) (m : AddMean A) : AddMean B :=
  mk₀ (m.toPositiveLinearMap.toLinearMap ∘ₗ (AddUCB.compRightAlgHom φ).toLinearMap)
    (fun _ hf => map_nonneg m (by simpa using AddUCB.monotone_compRightAlgHom φ hf)) (by simp)

/-- Evaluation of `AddMean.map`. -/
@[simp]
theorem map_apply (φ : A →ₜ+ B) (m : AddMean A) (f : AddUCB B) :
    m.map φ f = m (AddUCB.compRightAlgHom φ f) :=
  (rfl)

/-- Pushing forward along the identity is the identity. -/
@[simp]
theorem map_id (m : AddMean A) : m.map (ContinuousAddMonoidHom.id A) = m :=
  ext fun _ => by simp

/-- Pushing forward along `φ` and then along `ψ` is pushing forward along `ψ ∘ φ`. -/
@[simp]
theorem map_map (ψ : B →ₜ+ C) (φ : A →ₜ+ B) (m : AddMean A) :
    (m.map φ).map ψ = m.map (ψ.comp φ) :=
  ext fun _ => by simp [AddUCB.compRightAlgHom_comp]

/-- The pushforward of a left-invariant mean along `φ` is invariant under translation by the range
of `φ`. -/
theorem IsLeftInvariant.map_apply_leftTranslation {m : AddMean A} (hm : m.IsLeftInvariant)
    (φ : A →ₜ+ B) (a : A) (f : AddUCB B) :
    m.map φ (AddUCB.leftTranslation (φ a) f) = m.map φ f := by
  rw [map_apply, map_apply, AddUCB.compRightAlgHom_leftTranslation, hm]

/-- The pushforward of a left-invariant mean along a continuous additive homomorphism with dense
range is left invariant. -/
theorem IsLeftInvariant.map {m : AddMean A} (hm : m.IsLeftInvariant) {φ : A →ₜ+ B}
    (hφ : DenseRange φ) : (m.map φ).IsLeftInvariant := by
  let ψ : Multiplicative A →ₜ* Multiplicative B :=
    { toMonoidHom := φ.toAddMonoidHom.toMultiplicative
      continuous_toFun := continuous_ofAdd.comp (φ.continuous.comp continuous_toAdd) }
  have hmap : multiplicativeEquiv B (m.map φ) = (multiplicativeEquiv A m).map ψ :=
    Mean.ext fun f => by
      simp only [multiplicativeEquiv_apply, map_apply, Mean.map_apply]
      exact congrArg m (AddUCB.ext fun _ => by simp [ψ])
  have hψ : DenseRange ψ :=
    (Homeomorph.ofAdd (X := B)).surjective.denseRange.comp
      (hφ.comp (Homeomorph.ofAdd (X := A)).symm.surjective.denseRange φ.continuous)
      continuous_ofAdd
  exact (isLeftInvariant_multiplicativeEquiv_iff _).1
    (hmap ▸ ((isLeftInvariant_multiplicativeEquiv_iff m).2 hm).map hψ)

end AddMean

end AddMean

section AdditiveEquiv

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Equivalence between means on `UCB G` and means on `AddUCB (Additive G)`, induced by
`UCB.additiveAlgEquiv`. -/
def Mean.additiveEquiv : Mean G ≃ AddMean (Additive G) where
  toFun m := AddMean.mk₀
    (m.toPositiveLinearMap.toLinearMap ∘ₗ (UCB.additiveAlgEquiv G).symm.toLinearMap)
    (fun f hf => map_nonneg m <| UCB.le_def.2 fun g => by
      simpa using AddUCB.le_def.1 hf (ofMul g))
    (by simp)
  invFun n := Mean.mk₀
    (n.toPositiveLinearMap.toLinearMap ∘ₗ (UCB.additiveAlgEquiv G).toLinearMap)
    (fun f hf => map_nonneg n <| AddUCB.le_def.2 fun x => by
      simpa using UCB.le_def.1 hf x.toMul)
    (by simp)
  left_inv m := Mean.ext fun _ => by simp
  right_inv n := AddMean.ext fun _ => by simp

/-- Evaluation of `Mean.additiveEquiv`. -/
@[simp]
theorem Mean.additiveEquiv_apply {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (m : Mean G) (f : AddUCB (Additive G)) :
    Mean.additiveEquiv G m f = m ((UCB.additiveAlgEquiv G).symm f) :=
  (rfl)

/-- Evaluation of `(Mean.additiveEquiv G).symm`. -/
@[simp]
theorem Mean.additiveEquiv_symm_apply {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (n : AddMean (Additive G)) (f : UCB G) :
    (Mean.additiveEquiv G).symm n f = n (UCB.additiveAlgEquiv G f) :=
  Mean.mk₀_apply _ _ _ f

end AdditiveEquiv

section Class

variable {A B : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

variable (A) in
/-- A topological additive group `A` is amenable when `AddUCB A` carries a left-invariant mean. -/
class AddAmenable : Prop where
  /-- An amenable additive group has a left-invariant mean on `AddUCB A`. -/
  exists_isLeftInvariant : ∃ m : AddMean A, m.IsLeftInvariant

variable (A) in
/-- A topological additive group is amenable exactly when `AddUCB A` carries a left-invariant
mean. -/
theorem addAmenable_iff : AddAmenable A ↔ ∃ m : AddMean A, m.IsLeftInvariant :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- `Multiplicative A` is amenable if and only if `A` is additively amenable. -/
@[simp]
theorem amenable_multiplicative_iff : Amenable (Multiplicative A) ↔ AddAmenable A := by
  rw [amenable_iff, addAmenable_iff]
  exact ⟨fun ⟨n, hn⟩ => ⟨(AddMean.multiplicativeEquiv A).symm n,
      (AddMean.isLeftInvariant_multiplicativeEquiv_symm_iff n).2 hn⟩,
    fun ⟨m, hm⟩ => ⟨AddMean.multiplicativeEquiv A m,
      (AddMean.isLeftInvariant_multiplicativeEquiv_iff m).2 hm⟩⟩

/-- `Multiplicative A` is amenable when `A` is additively amenable. -/
instance Amenable.multiplicative [AddAmenable A] : Amenable (Multiplicative A) :=
  amenable_multiplicative_iff.2 ‹_›

/-- `Additive G` is additively amenable if and only if `G` is amenable. -/
@[simp]
theorem addAmenable_additive_iff {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : AddAmenable (Additive G) ↔ Amenable G := by
  let e : G ≃ₜ* Multiplicative (Additive G) :=
    { toFun := fun g => ofAdd (ofMul g)
      invFun := fun x => x.toAdd.toMul
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      continuous_toFun := continuous_ofAdd.comp continuous_ofMul
      continuous_invFun := continuous_toMul.comp continuous_toAdd }
  rw [← amenable_multiplicative_iff, e.amenable_iff]

/-- `Additive G` is additively amenable when `G` is amenable. -/
instance AddAmenable.additive {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Amenable G] : AddAmenable (Additive G) :=
  addAmenable_additive_iff.2 ‹_›

/-- The target of a continuous additive homomorphism with dense range from an amenable topological
additive group is amenable. -/
theorem AddAmenable.of_denseRange [AddAmenable A] (φ : A →ₜ+ B) (hφ : DenseRange φ) :
    AddAmenable B :=
  have ⟨m, hm⟩ := AddAmenable.exists_isLeftInvariant (A := A)
  ⟨⟨m.map φ, hm.map hφ⟩⟩

/-- The image of an amenable topological additive group under a surjective continuous additive
homomorphism is amenable. -/
theorem AddAmenable.of_surjective [AddAmenable A] (φ : A →ₜ+ B) (hφ : Function.Surjective φ) :
    AddAmenable B :=
  .of_denseRange φ hφ.denseRange

omit [TopologicalSpace A] [IsTopologicalAddGroup A] in
/-- Amenability of topological additive groups passes from a finer to a coarser additive group
topology. -/
theorem AddAmenable.of_le {t₁ t₂ : TopologicalSpace A}
    [@IsTopologicalAddGroup A t₁ _] [@IsTopologicalAddGroup A t₂ _] (h : t₁ ≤ t₂)
    (ha : @AddAmenable A _ t₁ _) : @AddAmenable A _ t₂ _ := by
  let := t₁
  have h₁ : @Amenable (Multiplicative A) _ t₁ _ := amenable_multiplicative_iff.2 ha
  let := t₂
  exact amenable_multiplicative_iff.1 (@Amenable.of_le (Multiplicative A) _ t₁ t₂ _ _ h h₁)

/-- An additive group which is amenable with the discrete topology is amenable with any additive
group topology. -/
theorem AddAmenable.of_discrete
    (h : letI : TopologicalSpace A := ⊥;
      letI := discreteTopology_bot A; AddAmenable A) :
    AddAmenable A := by
  let : @DiscreteTopology A ⊥ := discreteTopology_bot A
  exact AddAmenable.of_le (t₁ := ⊥) bot_le h

/-- Every finite topological additive group is amenable, for any additive group topology. -/
instance (priority := 100) AddAmenable.of_finite [Finite A] : AddAmenable A :=
  have : Finite (Multiplicative A) := Finite.of_equiv A ofAdd
  amenable_multiplicative_iff.1 inferInstance

/-- Every compact topological additive group is amenable. -/
instance (priority := 100) AddAmenable.of_compactSpace [CompactSpace A] : AddAmenable A :=
  amenable_multiplicative_iff.1 inferInstance

end Class

end TauCeti

namespace ContinuousAddEquiv

open TauCeti

variable {A B : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

/-- Amenability is invariant under isomorphisms of topological additive groups. -/
theorem addAmenable_iff (e : A ≃ₜ+ B) : AddAmenable A ↔ AddAmenable B := by
  rw [← amenable_multiplicative_iff, ← amenable_multiplicative_iff,
    e.toMultiplicative.amenable_iff]

end ContinuousAddEquiv

namespace TauCeti

section Foelner

variable {A : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]

/-- An additive group with additive Følner sets is amenable, for every additive group topology. -/
theorem AddAmenable.of_hasAddFoelnerSets (h : HasAddFoelnerSets A) : AddAmenable A :=
  amenable_multiplicative_iff.1 (.of_hasFoelnerSets (hasFoelnerSets_multiplicative_iff.2 h))

/-- A topological additive group is amenable when it has an additive Følner family for counting
measure along a nontrivial filter. -/
theorem AddAmenable.of_isAddFoelner [MeasurableSpace A] {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → Set A} (hF : IsAddFoelner A Measure.count l F) : AddAmenable A :=
  .of_hasAddFoelnerSets (.of_isAddFoelner hF)

end Foelner

section Discrete

variable {A : Type*} [AddGroup A] [TopologicalSpace A] [DiscreteTopology A]

/-- An amenable discrete additive group has additive Følner sets. -/
theorem AddAmenable.hasAddFoelnerSets [AddAmenable A] : HasAddFoelnerSets A :=
  hasFoelnerSets_multiplicative_iff.1 Amenable.hasFoelnerSets

/-- A discrete additive group is amenable exactly when it has additive Følner sets. -/
theorem addAmenable_iff_hasAddFoelnerSets : AddAmenable A ↔ HasAddFoelnerSets A :=
  ⟨fun _ => AddAmenable.hasAddFoelnerSets, .of_hasAddFoelnerSets⟩

/-- A discrete additive group is amenable exactly when for every finite `K ⊆ A` and every `ε > 0`
there is a finite nonempty `F ⊆ A` with `|(a +ᵥ F) △ F| < ε · |F|` for all `a ∈ K`. -/
theorem addAmenable_iff_exists_finset [DecidableEq A] :
    AddAmenable A ↔ ∀ K : Finset A, ∀ ε : ℝ, 0 < ε →
      ∃ F : Finset A, F.Nonempty ∧ ∀ a ∈ K, (#((a +ᵥ F) ∆ F) : ℝ) < ε * #F := by
  rw [addAmenable_iff_hasAddFoelnerSets, hasAddFoelnerSets_iff]

/-- A countable discrete additive group is amenable exactly when it admits an additive Følner
sequence of nonempty finite sets. -/
theorem addAmenable_iff_exists_seq [Countable A] [DecidableEq A] :
    AddAmenable A ↔ ∃ F : ℕ → Finset A, (∀ n, (F n).Nonempty) ∧
      ∀ a : A, Tendsto (fun n => (#((a +ᵥ F n) ∆ F n) : ℝ) / #(F n)) atTop (𝓝 0) := by
  rw [addAmenable_iff_hasAddFoelnerSets, hasAddFoelnerSets_iff_exists_seq]

/-- A discrete additive group is amenable exactly when it admits a left-invariant finitely
additive probability on all subsets. -/
theorem addAmenable_iff_exists_invariantContent :
    AddAmenable A ↔ ∃ ν : AddContent ℝ≥0∞ (Set.univ : Set (Set A)),
      ν Set.univ = 1 ∧ ∀ (a : A) (s : Set A), ν (a +ᵥ s) = ν s := by
  rw [← amenable_multiplicative_iff, amenable_iff_exists_invariantContent]
  refine ⟨fun ⟨ν, h₁, hν⟩ => ⟨ν.map toAdd (fun _ _ => Set.mem_univ _), ?_, fun a s => ?_⟩,
    fun ⟨ν, h₁, hν⟩ => ⟨ν.map ofAdd (fun _ _ => Set.mem_univ _), ?_, fun g s => ?_⟩⟩
  · simpa [AddContent.map_apply] using h₁
  · have hs : toAdd ⁻¹' (a +ᵥ s) = ofAdd a • (toAdd ⁻¹' s) := by
      ext x
      simp [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_smul_set_iff_inv_smul_mem, ← ofAdd_neg]
    rw [AddContent.map_apply, AddContent.map_apply, hs, hν]
  · simpa [AddContent.map_apply] using h₁
  · have hs : ofAdd ⁻¹' (g • s) = g.toAdd +ᵥ (ofAdd ⁻¹' s) := by
      ext x
      rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_vadd_set_iff_neg_vadd_mem,
        Set.mem_preimage, smul_eq_mul, vadd_eq_add, ← ofAdd_toAdd g, ← ofAdd_neg, ← ofAdd_add,
        toAdd_ofAdd]
    rw [AddContent.map_apply, AddContent.map_apply, hs, hν]

end Discrete

section Closure

/-- An additive group `B` which embeds by an injective homomorphism into an amenable discrete
additive group `A` is amenable, for every additive group topology on `B`. -/
theorem AddAmenable.of_injective {A B : Type*} [AddGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [AddAmenable A] [AddGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] (φ : B →+ A) (hφ : Function.Injective φ) : AddAmenable B :=
  amenable_multiplicative_iff.1 <|
    Amenable.of_injective φ.toMultiplicative (ofAdd.injective.comp (hφ.comp toAdd.injective))

/-- Every additive subgroup of an amenable discrete additive group is amenable. -/
instance AddAmenable.addSubgroup {A : Type*} [AddGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [AddAmenable A] (K : AddSubgroup A) : AddAmenable K :=
  .of_injective K.subtype K.subtype_injective

/-- If `ψ : K →+ A` and `φ : A →+ Q` are homomorphisms with `φ.ker ≤ ψ.range` and `K` and `Q` are
amenable discrete additive groups, then `A` is amenable for every additive group topology. -/
theorem AddAmenable.of_ker_le_range {A K Q : Type*} [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [AddGroup K] [TopologicalSpace K] [DiscreteTopology K]
    [AddGroup Q] [TopologicalSpace Q] [DiscreteTopology Q] [AddAmenable K] [AddAmenable Q]
    (ψ : K →+ A) (φ : A →+ Q) (h : φ.ker ≤ ψ.range) : AddAmenable A := by
  refine .of_discrete (by
    let : TopologicalSpace A := ⊥
    have : DiscreteTopology A := discreteTopology_bot A
    refine amenable_multiplicative_iff.1 (Amenable.of_ker_le_range ψ.toMultiplicative
      φ.toMultiplicative fun x hx => ?_)
    have hx' : x.toAdd ∈ φ.ker := by
      simpa [MonoidHom.mem_ker, AddMonoidHom.coe_toMultiplicative] using hx
    obtain ⟨k, hk⟩ := h hx'
    exact ⟨ofAdd k, by simp [hk]⟩)

/-- The product of two amenable topological additive groups is amenable. -/
instance AddAmenable.prod {A B : Type*} [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
    [AddAmenable A] [AddAmenable B] : AddAmenable (A × B) :=
  amenable_multiplicative_iff.1
    ((ContinuousMulEquiv.prodMultiplicative A B).amenable_iff.2 inferInstance)

/-- A product of two topological additive groups is amenable exactly when both factors are. -/
theorem addAmenable_prod_iff (A B : Type*) [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] :
    AddAmenable (A × B) ↔ AddAmenable A ∧ AddAmenable B := by
  rw [← amenable_multiplicative_iff, (ContinuousMulEquiv.prodMultiplicative A B).amenable_iff,
    amenable_prod_iff, amenable_multiplicative_iff, amenable_multiplicative_iff]

private theorem addAmenable_pi_of_finite {ι : Type*} [Finite ι] {A : ι → Type*}
    [∀ i, AddGroup (A i)] [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalAddGroup (A i)]
    [∀ i, AddAmenable (A i)] : AddAmenable (∀ i, A i) :=
  amenable_multiplicative_iff.1
    ((ContinuousMulEquiv.piMultiplicative A).amenable_iff.2 inferInstance)

/-- Extension by zero from coordinates in `s : Finset ι` to the full product `∀ i, A i`. -/
private def piFinsetHom {ι : Type*} [DecidableEq ι] {A : ι → Type*} [∀ i, AddGroup (A i)]
    [∀ i, TopologicalSpace (A i)] (s : Finset ι) : (∀ i : s, A i) →ₜ+ ∀ i, A i where
  toFun g i := if h : i ∈ s then g ⟨i, h⟩ else 0
  map_zero' := funext fun i => by by_cases h : i ∈ s <;> simp [h]
  map_add' x y := funext fun i => by by_cases h : i ∈ s <;> simp [h]
  continuous_toFun := continuous_pi fun i => by
    by_cases h : i ∈ s <;> simp only [h, ↓reduceDIte]
    exacts [continuous_apply (⟨i, h⟩ : s), continuous_const]

@[simp]
private theorem piFinsetHom_apply {ι : Type*} [DecidableEq ι] {A : ι → Type*}
    [∀ i, AddGroup (A i)] [∀ i, TopologicalSpace (A i)] (s : Finset ι) (g : ∀ i : s, A i)
    (i : ι) : piFinsetHom s g i = if h : i ∈ s then g ⟨i, h⟩ else 0 :=
  (rfl)

/-- A topological additive group `A` is amenable if, for a family of continuous additive
homomorphisms `φ i : K i →ₜ+ A` from amenable topological additive groups, every finite subset of
`A` lies in the range of some `φ i`. -/
theorem AddAmenable.of_forall_finset_subset_range {A : Type*} [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] {ι : Type*} {K : ι → Type*} [∀ i, AddGroup (K i)]
    [∀ i, TopologicalSpace (K i)] [∀ i, IsTopologicalAddGroup (K i)] [∀ i, AddAmenable (K i)]
    (φ : ∀ i, K i →ₜ+ A) (h : ∀ s : Finset A, ∃ i, (s : Set A) ⊆ Set.range (φ i)) :
    AddAmenable A := by
  let ψ : ∀ i, Multiplicative (K i) →ₜ* Multiplicative A := fun i =>
    { toMonoidHom := (φ i).toAddMonoidHom.toMultiplicative
      continuous_toFun := continuous_ofAdd.comp ((φ i).continuous.comp continuous_toAdd) }
  refine amenable_multiplicative_iff.1 (Amenable.of_forall_finset_subset_range ψ fun s => ?_)
  obtain ⟨i, hi⟩ := h (s.map toAdd.toEmbedding)
  refine ⟨i, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hi (Finset.mem_coe.2 (Finset.mem_map_of_mem toAdd.toEmbedding hx))
  exact ⟨ofAdd k, by simp [ψ, hk]⟩

/-- Topological group isomorphism between `Multiplicative K` for `K : AddSubgroup A` and
`AddSubgroup.toSubgroup K : Subgroup (Multiplicative A)`. -/
private def multiplicativeAddSubgroupEquiv {A : Type*} [AddGroup A] [TopologicalSpace A]
    (K : AddSubgroup A) : Multiplicative K ≃ₜ* AddSubgroup.toSubgroup K where
  toFun x := ⟨ofAdd x.toAdd.1, x.toAdd.2⟩
  invFun y := ofAdd ⟨y.1.toAdd, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := (continuous_ofAdd.comp
    (continuous_subtype_val.comp continuous_toAdd)).subtype_mk _
  continuous_invFun := continuous_ofAdd.comp
    ((continuous_toAdd.comp continuous_subtype_val).subtype_mk _)

/-- The supremum `⨆ i, H i` of a directed family of amenable additive subgroups `H i` of a
topological additive group is an amenable additive subgroup. -/
theorem addAmenable_iSup_of_directed {A : Type*} [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] {ι : Type*} {H : ι → AddSubgroup A}
    (hH : Directed (· ≤ ·) H) [∀ i, AddAmenable (H i)] : AddAmenable ↥(⨆ i, H i) := by
  have : ∀ i, Amenable (AddSubgroup.toSubgroup (H i)) := fun i =>
    (multiplicativeAddSubgroupEquiv (H i)).amenable_iff.1 inferInstance
  have hdir : Directed (· ≤ ·) fun i => AddSubgroup.toSubgroup (H i) :=
    hH.mono_comp _ fun _ _ h => AddSubgroup.toSubgroup.monotone h
  have hiSup : AddSubgroup.toSubgroup (⨆ i, H i) = ⨆ i, AddSubgroup.toSubgroup (H i) :=
    le_antisymm (AddSubgroup.toSubgroup.le_symm_apply.1 <| iSup_le fun i =>
      AddSubgroup.toSubgroup.le_symm_apply.2 (le_iSup (fun i => AddSubgroup.toSubgroup (H i)) i))
      (iSup_le fun i => AddSubgroup.toSubgroup.monotone (le_iSup _ i))
  have hsup : Amenable ↥(AddSubgroup.toSubgroup (⨆ i, H i)) := by
    rw [hiSup]
    exact amenable_iSup_of_directed hdir
  exact amenable_multiplicative_iff.1 ((multiplicativeAddSubgroupEquiv _).amenable_iff.2 hsup)

/-- The Tychonoff product of any family of amenable topological additive groups is amenable. -/
instance AddAmenable.pi {ι : Type*} {A : ι → Type*} [∀ i, AddGroup (A i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalAddGroup (A i)] [∀ i, AddAmenable (A i)] :
    AddAmenable (∀ i, A i) := by
  classical
  let H : Finset ι → AddSubgroup (∀ i, A i) :=
    fun s => (piFinsetHom (A := A) s).toAddMonoidHom.range
  have hH_mono : Monotone H := fun s t hst => by
    rintro _ ⟨g, rfl⟩
    refine ⟨fun j => if hj : j.1 ∈ s then g ⟨j.1, hj⟩ else 0, funext fun i => ?_⟩
    by_cases hi : i ∈ s
    · simp [hi, hst hi]
    · by_cases ht : i ∈ t <;> simp [hi, ht]
  have : ∀ s : Finset ι, AddAmenable (∀ i : s, A i) := fun _ => addAmenable_pi_of_finite
  have : ∀ s, AddAmenable (H s) := fun s => .of_surjective
    ⟨(piFinsetHom (A := A) s).toAddMonoidHom.rangeRestrict,
      (piFinsetHom (A := A) s).continuous.subtype_mk _⟩
    fun ⟨_, g, hg⟩ => ⟨g, Subtype.ext hg⟩
  have : AddAmenable ↥(⨆ s, H s) := addAmenable_iSup_of_directed hH_mono.directed_le
  refine .of_denseRange ⟨(⨆ s, H s).subtype, continuous_subtype_val⟩ fun x =>
    mem_closure_iff_nhds.2 fun U hU => ?_
  obtain ⟨I, t, ht, hIU⟩ := Filter.mem_pi'.1 (nhds_pi (a := x) ▸ hU)
  refine ⟨piFinsetHom I (fun i => x i), hIU fun i hi => ?_,
    ⟨piFinsetHom I (fun i => x i), le_iSup H I ⟨fun i => x i, rfl⟩⟩, rfl⟩
  have hi' : i ∈ I := hi
  simpa [hi'] using mem_of_mem_nhds (ht i)

/-- A Tychonoff product of topological additive groups is amenable exactly when every factor is. -/
theorem addAmenable_pi_iff {ι : Type*} {A : ι → Type*} [∀ i, AddGroup (A i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalAddGroup (A i)] :
    AddAmenable (∀ i, A i) ↔ ∀ i, AddAmenable (A i) :=
  ⟨fun _ i => .of_surjective ⟨Pi.evalAddMonoidHom A i, continuous_apply i⟩
      (Function.surjective_eval i),
    fun _ => inferInstance⟩

/-- A topological additive group which is the supremum of a directed family of amenable additive
subgroups is amenable. -/
theorem AddAmenable.of_directed_of_iSup_eq_top {A : Type*} [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] {ι : Type*} {H : ι → AddSubgroup A}
    (hH : Directed (· ≤ ·) H) (htop : ⨆ i, H i = ⊤) [∀ i, AddAmenable (H i)] : AddAmenable A :=
  have := addAmenable_iSup_of_directed hH
  .of_surjective ⟨(⨆ i, H i).subtype, continuous_subtype_val⟩
    fun x => ⟨⟨x, htop ▸ AddSubgroup.mem_top x⟩, rfl⟩

/-- A topological additive group all of whose finitely generated additive subgroups are amenable is
amenable. -/
theorem AddAmenable.of_forall_fg {A : Type*} [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] (h : ∀ K : AddSubgroup A, K.FG → AddAmenable K) : AddAmenable A := by
  refine amenable_multiplicative_iff.1 (Amenable.of_forall_fg fun S hS => ?_)
  obtain ⟨K, rfl⟩ := AddSubgroup.toSubgroup.surjective S
  have : Group.FG (AddSubgroup.toSubgroup K) := (Group.fg_iff_subgroup_fg _).2 hS
  have hK : K.FG := (AddGroup.fg_iff_addSubgroup_fg K).1 <| AddGroup.fg_iff_mul_fg.2 <|
    Group.fg_of_surjective (f := (multiplicativeAddSubgroupEquiv K).symm.toMonoidHom)
      (multiplicativeAddSubgroupEquiv K).symm.surjective
  exact (multiplicativeAddSubgroupEquiv K).amenable_iff.1
    (amenable_multiplicative_iff.2 (h K hK))

end Closure

end TauCeti
