/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.KrullTopology
public import TauCeti.Topology.Algebra.UniformRing
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Completion
import TauCeti.FieldTheory.KrullTopology

/-!
# Continuous Galois actions on completions of algebraic normed fields

Let `K` be a complete, nontrivially normed, ultrametric field and let `L / K` be an algebraic
normed field extension. Since the norm on `L` coincides with the spectral norm over `K`
(`NormedAlgebra.norm_eq_spectralNorm`), every `K`-algebra automorphism `σ : L ≃ₐ[K] L` is an
isometry (`AlgEquiv.isometry`). It therefore extends uniquely by continuity to an isometric
`K`-algebra automorphism `σ.completion : UniformSpace.Completion L ≃ₐ[K] UniformSpace.Completion L`
whose underlying map is `UniformSpace.Completion.map σ`.

Moreover, the resulting action `(L ≃ₐ[K] L) × UniformSpace.Completion L → UniformSpace.Completion L`
is jointly continuous when `L ≃ₐ[K] L` carries the Krull topology: on the dense subset `L` the
orbit map `σ ↦ σ a` is locally constant (`IsIntegral.isLocallyConstant_apply`), and for each `σ`
the map `x ↦ UniformSpace.Completion.map σ x` is `1`-Lipschitz. The same proof applies over any
intermediate field `E` of `L / K` without requiring `E` to be finite-dimensional or complete.

## Main definitions

* `AlgEquiv.completion`: the unique continuous `K`-algebra automorphism of
  `UniformSpace.Completion L` extending `σ : L ≃ₐ[K] L`.
* `AlgEquiv.completionHom`: the group homomorphism
  `(L ≃ₐ[K] L) →* (UniformSpace.Completion L ≃ₐ[K] UniformSpace.Completion L)`.

## Main results

* `AlgEquiv.norm_map` and `AlgEquiv.isometry`: every `σ : L ≃ₐ[K] L` preserves the norm and is an
  isometry.
* `AlgEquiv.eq_completion_of_continuous`: `σ.completion` is the unique continuous extension of `σ`
  to `UniformSpace.Completion L`.
* `AlgEquiv.isometry_completion` and `AlgEquiv.norm_completion`: `σ.completion` is an isometry.
* `TauCeti.continuous_completion_map_of_isometry`: for any integral field extension `L / K` with a
  pseudometric on `L` preserved by `L ≃ₐ[K] L`, the extended action
  `(L ≃ₐ[K] L) × UniformSpace.Completion L → UniformSpace.Completion L` is jointly continuous.
* `TauCeti.continuous_completion_map`, `TauCeti.continuous_completion_apply`, and
  `TauCeti.continuous_completion_map_of_isScalarTower`: joint continuity of the completed Galois
  action over `K` and over any intermediate field `E` of `L / K`.

## References

* O. Brinon and B. Conrad, *CMI Summer School Notes on `p`-adic Hodge Theory*, §2.1, p. 12.
* J.-M. Fontaine and Y. Ouyang, *Theory of `p`-adic Galois Representations*, §4.1.2, p. 91.
-/

public section

namespace AlgEquiv

section Isometry

variable {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [NormedField L] [NormedAlgebra K L] [Algebra.IsAlgebraic K L]

/-- Every `K`-algebra automorphism of an algebraic normed field extension `L` of a complete
ultrametric field `K` preserves the norm. -/
@[simp]
theorem norm_map (σ : L ≃ₐ[K] L) (x : L) : ‖σ x‖ = ‖x‖ := by
  rw [NormedAlgebra.norm_eq_spectralNorm K, NormedAlgebra.norm_eq_spectralNorm K,
    ← spectralNorm_eq_of_equiv σ x]

/-- Every `K`-algebra automorphism of an algebraic normed field extension `L` of a complete
ultrametric field `K` is an isometry. -/
theorem isometry (σ : L ≃ₐ[K] L) : Isometry σ :=
  AddMonoidHomClass.isometry_of_norm σ σ.norm_map

/-- **Extension of a Galois automorphism to the completion.** Every `K`-algebra automorphism
`σ : L ≃ₐ[K] L` of an algebraic normed field extension of a complete ultrametric field `K` extends
to a `K`-algebra automorphism of `UniformSpace.Completion L`. -/
noncomputable def completion (σ : L ≃ₐ[K] L) :
    UniformSpace.Completion L ≃ₐ[K] UniformSpace.Completion L :=
  UniformSpace.Completion.mapAlgEquiv σ σ.isometry.continuous σ.symm.isometry.continuous

/-- Evaluating `σ.completion` agrees with `UniformSpace.Completion.map σ`. -/
theorem completion_apply (σ : L ≃ₐ[K] L) (x : UniformSpace.Completion L) :
    σ.completion x = UniformSpace.Completion.map σ x :=
  UniformSpace.Completion.mapAlgEquiv_apply σ σ.isometry.continuous σ.symm.isometry.continuous x

/-- The underlying function of `σ.completion` is `UniformSpace.Completion.map σ`. -/
theorem coe_completion (σ : L ≃ₐ[K] L) :
    ⇑σ.completion = UniformSpace.Completion.map σ :=
  funext σ.completion_apply

/-- On the dense image of `L`, `σ.completion` agrees with `σ`. -/
@[simp]
theorem completion_coe (σ : L ≃ₐ[K] L) (a : L) :
    σ.completion (a : UniformSpace.Completion L) = (σ a : UniformSpace.Completion L) :=
  UniformSpace.Completion.mapAlgEquiv_coe σ σ.isometry.continuous σ.symm.isometry.continuous a

/-- `σ.completion` is continuous. -/
@[fun_prop, continuity]
theorem continuous_completion (σ : L ≃ₐ[K] L) : Continuous σ.completion :=
  UniformSpace.Completion.continuous_mapAlgEquiv σ σ.isometry.continuous σ.symm.isometry.continuous

/-- `σ.completion` is an isometry of `UniformSpace.Completion L`. -/
theorem isometry_completion (σ : L ≃ₐ[K] L) : Isometry σ.completion := by
  rw [coe_completion]
  exact σ.isometry.completion_map

/-- `σ.completion` preserves the norm on `UniformSpace.Completion L`. -/
@[simp]
theorem norm_completion (σ : L ≃ₐ[K] L) (x : UniformSpace.Completion L) :
    ‖σ.completion x‖ = ‖x‖ := by
  simpa only [dist_zero_right, map_zero] using σ.isometry_completion.dist_eq x 0

/-- **Uniqueness of the continuous extension.** Any continuous self-map of
`UniformSpace.Completion L` extending `σ` on `L` equals `σ.completion`. -/
theorem eq_completion_of_continuous {σ : L ≃ₐ[K] L}
    {f : UniformSpace.Completion L → UniformSpace.Completion L}
    (hf : Continuous f) (h : ∀ a : L, f a = (σ a : UniformSpace.Completion L)) :
    f = ⇑σ.completion :=
  UniformSpace.Completion.ext hf σ.continuous_completion fun a ↦ by
    rw [h a, completion_coe]

/-- The identity automorphism extends to the identity of `UniformSpace.Completion L`. -/
@[simp]
theorem completion_one :
    (1 : L ≃ₐ[K] L).completion = 1 :=
  UniformSpace.Completion.mapAlgEquiv_refl

/-- Extending Galois automorphisms to the completion respects composition. -/
@[simp]
theorem completion_mul (σ τ : L ≃ₐ[K] L) :
    (σ * τ).completion = σ.completion * τ.completion :=
  UniformSpace.Completion.mapAlgEquiv_trans τ σ τ.isometry.continuous τ.symm.isometry.continuous
    σ.isometry.continuous σ.symm.isometry.continuous

/-- The inverse of `σ.completion` is `σ.symm.completion`. -/
@[simp]
theorem completion_symm (σ : L ≃ₐ[K] L) : σ.completion.symm = σ.symm.completion :=
  UniformSpace.Completion.mapAlgEquiv_symm σ σ.isometry.continuous σ.symm.isometry.continuous

/-- Extending Galois automorphisms to the completion respects inversion. -/
@[simp]
theorem completion_inv (σ : L ≃ₐ[K] L) : σ⁻¹.completion = σ.completion⁻¹ :=
  σ.completion_symm.symm

/-- Extension to the completion is injective on `L ≃ₐ[K] L`. -/
theorem completion_injective :
    Function.Injective (AlgEquiv.completion (K := K) (L := L)) := fun σ τ h ↦
  AlgEquiv.ext fun a ↦ UniformSpace.Completion.coe_injective L <| by
    simpa only [completion_coe] using AlgEquiv.congr_fun h (a : UniformSpace.Completion L)

/-- The group homomorphism sending a Galois automorphism to its continuous extension
`UniformSpace.Completion L ≃ₐ[K] UniformSpace.Completion L`. -/
noncomputable def completionHom :
    (L ≃ₐ[K] L) →* (UniformSpace.Completion L ≃ₐ[K] UniformSpace.Completion L) where
  toFun := AlgEquiv.completion
  map_one' := completion_one
  map_mul' := completion_mul

/-- `completionHom` acts by `AlgEquiv.completion`. -/
@[simp]
theorem completionHom_apply (σ : L ≃ₐ[K] L) : completionHom σ = σ.completion := (rfl)

end Isometry

end AlgEquiv

namespace TauCeti

/-- **Joint continuity of the completed Galois action (metric form).** Let `L / K` be an integral
field extension equipped with a pseudometric on `L` for which every `σ : L ≃ₐ[K] L` is an
isometry. Then the extended action
`(σ, x) ↦ UniformSpace.Completion.map σ x` on `(L ≃ₐ[K] L) × UniformSpace.Completion L` is jointly
continuous for the Krull topology on `L ≃ₐ[K] L` and the completion metric on
`UniformSpace.Completion L`. -/
theorem continuous_completion_map_of_isometry {K L : Type*} [Field K] [Field L]
    [PseudoMetricSpace L] [Algebra K L] [Algebra.IsIntegral K L]
    (hiso : ∀ σ : L ≃ₐ[K] L, Isometry σ) :
    Continuous fun p : (L ≃ₐ[K] L) × UniformSpace.Completion L ↦
      UniformSpace.Completion.map p.1 p.2 := by
  refine continuous_prod_of_dense_continuous_lipschitzWith'
    (fun p : (L ≃ₐ[K] L) × UniformSpace.Completion L ↦ UniformSpace.Completion.map p.1 p.2) 1
    (UniformSpace.Completion.denseRange_coe (α := L))
    (fun σ ↦ (hiso σ).completion_map.lipschitzWith) ?_
  rintro _ ⟨a, rfl⟩
  have hcont : Continuous fun σ : L ≃ₐ[K] L ↦ (σ a : UniformSpace.Completion L) :=
    (UniformSpace.Completion.continuous_coe L).comp
      (Algebra.IsIntegral.isIntegral (R := K) a).isLocallyConstant_apply.continuous
  exact hcont.congr fun σ ↦ (UniformSpace.Completion.map_coe (hiso σ).uniformContinuous a).symm

section CompleteUltrametric

variable {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [NormedField L] [NormedAlgebra K L] [Algebra.IsAlgebraic K L]

variable (K) in
/-- **Joint continuity of the completed Galois action over any intermediate field.** For any field
`E` between `K` and `L` (neither finiteness nor completeness of `E` is needed), the action
`(L ≃ₐ[E] L) × UniformSpace.Completion L → UniformSpace.Completion L` via
`UniformSpace.Completion.map` is jointly continuous for the Krull topology on `L ≃ₐ[E] L`. -/
theorem continuous_completion_map_of_isScalarTower {E : Type*} [Field E] [Algebra K E]
    [Algebra E L] [IsScalarTower K E L] :
    Continuous fun p : (L ≃ₐ[E] L) × UniformSpace.Completion L ↦
      UniformSpace.Completion.map p.1 p.2 := by
  have : Algebra.IsIntegral E L := .tower_top K
  exact continuous_completion_map_of_isometry fun σ ↦ (σ.restrictScalars K).isometry

/-- **Joint continuity of the completed Galois action.** The map
`(σ, x) ↦ UniformSpace.Completion.map σ x` is jointly continuous on
`(L ≃ₐ[K] L) × UniformSpace.Completion L`. -/
theorem continuous_completion_map :
    Continuous fun p : (L ≃ₐ[K] L) × UniformSpace.Completion L ↦
      UniformSpace.Completion.map p.1 p.2 :=
  continuous_completion_map_of_isometry fun σ ↦ σ.isometry

/-- **Joint continuity of `AlgEquiv.completion`.** The action `(σ, x) ↦ σ.completion x` is jointly
continuous on `(L ≃ₐ[K] L) × UniformSpace.Completion L`. -/
@[fun_prop, continuity]
theorem continuous_completion_apply :
    Continuous fun p : (L ≃ₐ[K] L) × UniformSpace.Completion L ↦ p.1.completion p.2 :=
  continuous_completion_map.congr fun p ↦ (p.1.completion_apply p.2).symm

end CompleteUltrametric

end TauCeti
