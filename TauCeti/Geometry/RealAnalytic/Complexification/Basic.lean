/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.AnalyticSubmanifold.Basic
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.Complex.TotallyReal.Basic
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Topology.Compactness.Paracompact
import TauCeti.Geometry.Manifold.AnalyticSubmanifold.Complex
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.Complex.TotallyReal.Examples

/-!
# Global complexifications of real-analytic manifolds

A *Bruhat–Whitney complexification* of a real-analytic manifold `M` of real dimension `n` is a
Hausdorff, second-countable complex manifold `X` modelled on `Fin n → ℂ`, together with a closed
real-analytic maximal totally real embedding `ι : M → X` and an anti-holomorphic involution
`σ : X → X` whose fixed-point locus is `Set.range ι`. Anti-holomorphicity of `σ` is expressed in
holomorphic coordinates: around every point of `X` there is a holomorphic chart in the maximal
atlas whose source is `σ`-invariant and in which `σ` reads as coordinatewise complex conjugation
`star`.

This module defines the specification `TauCeti.IsRealAnalyticComplexification`, derives its basic
topological, differential-geometric, and real-analytic submanifold consequences, and establishes the
flat model `ℝⁿ ↪ ℂⁿ`. The general existence theorem for Hausdorff `σ`-compact (and Hausdorff
second-countable) boundaryless `C^ω` manifolds is proved in
`TauCeti.Geometry.RealAnalytic.Complexification.BruhatWhitney`.

## Main declarations

* `TauCeti.IsRealAnalyticComplexification`: predicate characterizing a Hausdorff, second-countable
  complexification `(X, ι, σ)` of a real-analytic manifold `M` with anti-holomorphic involution `σ`.
* `TauCeti.IsRealAnalyticComplexification.contMDiff_conj`,
  `TauCeti.IsRealAnalyticComplexification.diffeomorphConj`: the conjugation `σ` is a real-analytic
  diffeomorphism of `X` (and `C^r` for every smoothness order `r`).
* `TauCeti.IsRealAnalyticComplexification.isTotallyRealEmbedding_ofComplexManifold`: compatibility
  of `isTotallyRealEmbedding` with `SmoothAlmostComplexStructure.ofComplexManifold`.
* `TauCeti.IsRealAnalyticComplexification.isMAnalyticSubmanifold_range`: when `M` is nonempty,
  `Set.range ι` is an `n`-dimensional real-analytic submanifold of `X`.
* `TauCeti.isRealAnalyticComplexification_pi`: the flat model `ℝⁿ ↪ ℂⁿ` with coordinatewise
  conjugation.

## References

* H. Whitney and F. Bruhat, *Quelques propriétés fondamentales des ensembles analytiques-réels*,
  Commentarii Mathematici Helvetici 33 (1959), 132–206, §1, Proposition 1.
-/

open Filter Function IsManifold Manifold Module Set TopologicalSpace Topology
open scoped ContDiff Manifold TauCeti.ComplexManifold

namespace TauCeti

public noncomputable section

/-! ### Specification and properties of a global complexification -/

/-- **Global complexification of a real-analytic manifold.** A complex manifold `X` modelled on
`Fin n → ℂ`, together with an embedding `ι : M → X` and an involution `σ : X → X`, is a
Bruhat–Whitney complexification of the `C^ω` manifold `M` when:

* `X` is Hausdorff, second countable, and a complex manifold modelled on `𝓘(ℂ, Fin n → ℂ)`;
* `ι : M → X` is both a topological closed embedding and a `C^ω` maximal totally real embedding;
* `σ : X → X` is an involution whose fixed-point set is `Set.range ι`, and around every point of `X`
  there is a holomorphic chart in the maximal atlas whose source is `σ`-invariant and in which `σ`
  reads as coordinatewise complex conjugation `star`. -/
structure IsRealAnalyticComplexification
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace (Fin n → ℂ) X]
    (ι : M → X) (σ : X → X) : Prop where
  /-- The complexification is Hausdorff. -/
  t2Space : T2Space X
  /-- The complexification is second countable. -/
  secondCountableTopology : SecondCountableTopology X
  /-- The complexification is a complex manifold modelled on `Fin n → ℂ`. -/
  isManifold : IsManifold 𝓘(ℂ, Fin n → ℂ) ∞ X
  /-- The inclusion of `M` into `X` is a topological closed embedding. -/
  isClosedEmbedding : Topology.IsClosedEmbedding ι
  /-- The inclusion of `M` into `X` is a real-analytic maximal totally real embedding. -/
  isTotallyRealEmbedding :
    IsTotallyRealEmbedding I 𝓘(ℝ, Fin n → ℂ) ω
      (fun _ : X ↦ AlmostComplexStructure.ofComplexModule (Fin n → ℂ)) ι
  /-- The anti-holomorphic conjugation on `X` is an involution. -/
  involutive_conj : Function.Involutive σ
  /-- The fixed-point locus of conjugation is the image of `M`. -/
  fixedPoints_conj : Function.fixedPoints σ = Set.range ι
  /-- Every point of `X` admits a holomorphic chart with conjugation-invariant source in which
  conjugation becomes coordinatewise complex conjugation. -/
  exists_holomorphicChart_conj :
    ∀ x : X, ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin n → ℂ) ∞ X,
      x ∈ φ.source ∧ ∀ y ∈ φ.source, σ y ∈ φ.source ∧ φ (σ y) = star (φ y)

namespace IsRealAnalyticComplexification

variable {E H M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ} [TopologicalSpace X] [ChartedSpace (Fin n → ℂ) X]
  {ι : M → X} {σ : X → X}

/-- A complexification is a complex `C^r` manifold for every smoothness order `r`
(including `ω`). -/
theorem isManifold_complex (h : IsRealAnalyticComplexification I M n X ι σ) (r : ℕ∞ω) :
    IsManifold 𝓘(ℂ, Fin n → ℂ) r X :=
  h.isManifold.of_ne_zero r (by simp)

/-- Viewed over `ℝ`, a complexification is a real `C^r` manifold modelled on `𝓘(ℝ, Fin n → ℂ)` for
every smoothness order `r` (in particular, a real-analytic manifold for `r = ω`). -/
theorem isManifold_real (h : IsRealAnalyticComplexification I M n X ι σ) (r : ℕ∞ω) :
    IsManifold 𝓘(ℝ, Fin n → ℂ) r X :=
  h.isManifold.restrictScalars_of_ne_zero r (by simp)

/-- The complexification is locally compact. -/
theorem locallyCompactSpace (h : IsRealAnalyticComplexification I M n X ι σ) :
    LocallyCompactSpace X :=
  let _ := h.t2Space
  ChartedSpace.locallyCompactSpace (Fin n → ℂ) X

/-- The complexification is `σ`-compact. -/
theorem sigmaCompactSpace (h : IsRealAnalyticComplexification I M n X ι σ) :
    SigmaCompactSpace X := by
  have := h.locallyCompactSpace
  have := h.secondCountableTopology
  infer_instance

/-- The complexification is paracompact. -/
theorem paracompactSpace (h : IsRealAnalyticComplexification I M n X ι σ) :
    ParacompactSpace X := by
  have := h.t2Space
  have := h.locallyCompactSpace
  have := h.sigmaCompactSpace
  infer_instance

/-- The complexification is metrizable. -/
theorem metrizableSpace (h : IsRealAnalyticComplexification I M n X ι σ) :
    MetrizableSpace X := by
  have := h.t2Space
  have := h.sigmaCompactSpace
  exact Manifold.metrizableSpace 𝓘(ℝ, Fin n → ℂ) X

/-- The embedding `ι : M → X` is a `C^ω` smooth embedding. -/
theorem isSmoothEmbedding (h : IsRealAnalyticComplexification I M n X ι σ) :
    Manifold.IsSmoothEmbedding I 𝓘(ℝ, Fin n → ℂ) ω ι :=
  h.isTotallyRealEmbedding.isSmoothEmbedding

/-- The embedding `ι : M → X` is `C^r` for every order `r ≤ ω`. -/
theorem contMDiff_ι (h : IsRealAnalyticComplexification I M n X ι σ) (r : ℕ∞ω) :
    ContMDiff I 𝓘(ℝ, Fin n → ℂ) r ι :=
  h.isSmoothEmbedding.contMDiff.of_le le_top

/-- The embedding `ι : M → X` is a `C^r` immersion for every order `r`. -/
theorem isImmersion (h : IsRealAnalyticComplexification I M n X ι σ) (r : ℕ∞ω) :
    Manifold.IsImmersion I 𝓘(ℝ, Fin n → ℂ) r ι :=
  (h.isSmoothEmbedding.of_le le_top).isImmersion

/-- The real differential of `ι : M → X` is injective at every point of `M`. -/
theorem mfderiv_injective (h : IsRealAnalyticComplexification I M n X ι σ) (p : M) :
    Function.Injective (mfderiv I 𝓘(ℝ, Fin n → ℂ) ι p) :=
  h.isTotallyRealEmbedding.mfderiv_injective p

/-- The embedding `ι : M → X` is injective. -/
theorem injective (h : IsRealAnalyticComplexification I M n X ι σ) :
    Function.Injective ι :=
  h.isClosedEmbedding.injective

/-- The image of `M` in `X` is closed. -/
theorem isClosed_range (h : IsRealAnalyticComplexification I M n X ι σ) :
    IsClosed (Set.range ι) :=
  h.isClosedEmbedding.isClosed_range

/-- The real model dimension of `M` equals the complex dimension `n` of `X`. -/
theorem finrank_eq (h : IsRealAnalyticComplexification I M n X ι σ) :
    Module.finrank ℝ E = n := by
  have hdim := h.isTotallyRealEmbedding.two_mul_finrank
  have hc : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    rw [Module.finrank_pi_fintype ℝ]
    simp [Complex.finrank_real_complex, Finset.sum_const, mul_comm]
  omega

/-- Applying the conjugation involution twice is the identity. -/
theorem conj_apply_conj (h : IsRealAnalyticComplexification I M n X ι σ) (x : X) :
    σ (σ x) = x :=
  h.involutive_conj x

/-- A point of `X` is fixed by `σ` if and only if it lies in the image of `ι`. -/
theorem conj_eq_self_iff (h : IsRealAnalyticComplexification I M n X ι σ) {x : X} :
    σ x = x ↔ x ∈ Set.range ι := by
  change x ∈ Function.fixedPoints σ ↔ x ∈ Set.range ι
  rw [h.fixedPoints_conj]

/-- Every point in the image of `ι` is fixed by the conjugation `σ`. -/
theorem conj_apply_ι (h : IsRealAnalyticComplexification I M n X ι σ) (p : M) :
    σ (ι p) = ι p :=
  h.conj_eq_self_iff.2 ⟨p, rfl⟩

/-- The anti-holomorphic involution `σ : X → X` is `C^r` over `ℝ` for every smoothness order `r`
(in particular real-analytic for `r = ω`). -/
theorem contMDiff_conj (h : IsRealAnalyticComplexification I M n X ι σ) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) r σ := by
  have : IsManifold 𝓘(ℝ, Fin n → ℂ) ω X := h.isManifold_real ω
  refine (ContMDiff.of_le · le_top) fun x ↦ ?_
  obtain ⟨φ, hφ, hx, hφσ⟩ := h.exists_holomorphicChart_conj x
  have hφ_real : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin n → ℂ) ω X :=
    IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero ω (by simp : (∞ : ℕ∞ω) ≠ 0) hφ
  let conjCLE : (Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ) :=
    ContinuousLinearEquiv.piCongrRight fun _ ↦ RCLike.conjCLE
  have hconj_eq : ∀ y ∈ φ.source, σ y = φ.symm (conjCLE (φ y)) := by
    intro y hy
    obtain ⟨hσy, hstar⟩ := hφσ y hy
    have hc : conjCLE (φ y) = star (φ y) := by ext k; simp [conjCLE]
    rw [hc, ← hstar, φ.left_inv hσy]
  have hφx : ContMDiffAt 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) ω φ x :=
    (contMDiffOn_of_mem_maximalAtlas hφ_real).contMDiffAt (φ.open_source.mem_nhds hx)
  have htgt : conjCLE (φ x) ∈ φ.target := by
    have hc : conjCLE (φ x) = star (φ x) := by ext k; simp [conjCLE]
    rw [hc, ← (hφσ x hx).2]
    exact φ.map_source (hφσ x hx).1
  have hφsymm : ContMDiffAt 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) ω φ.symm (conjCLE (φ x)) :=
    (contMDiffOn_symm_of_mem_maximalAtlas hφ_real).contMDiffAt (φ.open_target.mem_nhds htgt)
  exact (hφsymm.comp x (conjCLE.contDiff.contMDiff.contMDiffAt.comp x hφx)).congr_of_eventuallyEq
    (eventually_of_mem (φ.open_source.mem_nhds hx) hconj_eq)

/-- The conjugation `σ : X → X` is continuous. -/
theorem continuous_conj (h : IsRealAnalyticComplexification I M n X ι σ) :
    Continuous σ :=
  (h.contMDiff_conj 0).continuous

/-- The conjugation `σ : X → X` packaged as a real `C^r` diffeomorphism of `X`. -/
def diffeomorphConj (h : IsRealAnalyticComplexification I M n X ι σ) (r : ℕ∞ω) :
    X ≃ₘ^r⟮𝓘(ℝ, Fin n → ℂ), 𝓘(ℝ, Fin n → ℂ)⟯ X where
  toFun := σ
  invFun := σ
  left_inv := h.involutive_conj
  right_inv := h.involutive_conj
  contMDiff_toFun := h.contMDiff_conj r
  contMDiff_invFun := h.contMDiff_conj r

/-- The underlying function of `IsRealAnalyticComplexification.diffeomorphConj` is `σ`. -/
@[simp]
theorem coe_diffeomorphConj (h : IsRealAnalyticComplexification I M n X ι σ) (r : ℕ∞ω) :
    ⇑(h.diffeomorphConj r) = σ :=
  (rfl)

/-- The inverse of `IsRealAnalyticComplexification.diffeomorphConj` is itself. -/
@[simp]
theorem diffeomorphConj_symm (h : IsRealAnalyticComplexification I M n X ι σ) (r : ℕ∞ω) :
    (h.diffeomorphConj r).symm = h.diffeomorphConj r :=
  (rfl)

/-- The embedding `ι : M → X` is maximal totally real with respect to the canonical smooth almost
complex structure `SmoothAlmostComplexStructure.ofComplexManifold` of `X`. -/
theorem isTotallyRealEmbedding_ofComplexManifold
    (h : IsRealAnalyticComplexification I M n X ι σ) :
    letI := h.isManifold
    IsTotallyRealEmbedding I 𝓘(ℝ, Fin n → ℂ) ω
      (SmoothAlmostComplexStructure.ofComplexManifold (Fin n → ℂ) X).almostComplexStructureAt
      ι := by
  let _ := h.isManifold
  refine (isTotallyRealEmbedding_congr fun p ↦ ?_).1 h.isTotallyRealEmbedding
  refine AlmostComplexStructure.toLinearMap_injective (LinearMap.ext fun v ↦ ?_)
  exact ((AlmostComplexStructure.ofComplexModule_apply (V := Fin n → ℂ) v).trans
    (SmoothAlmostComplexStructure.ofComplexManifold_apply (E := Fin n → ℂ) (M := X)
      (ι p) v).symm).trans
    (SmoothAlmostComplexStructure.almostComplexStructureAt_apply _ _ v).symm

/-- When `M` is nonempty, its image `Set.range ι` is an `n`-dimensional real-analytic submanifold of
`X` for any real coordinate equivalence `e_ℝ : (Fin n → ℂ) ≃L[ℝ] Fin m → ℝ`. -/
theorem isMAnalyticSubmanifold_range [Nonempty M]
    (h : IsRealAnalyticComplexification I M n X ι σ) {m : ℕ}
    (e_ℝ : (Fin n → ℂ) ≃L[ℝ] Fin m → ℝ) :
    letI := h.isManifold
    IsMAnalyticSubmanifold 𝓘(ℝ, Fin n → ℂ) e_ℝ n (Set.range ι) := by
  let _ := h.isManifold
  refine isMAnalyticSubmanifold_of_holomorphicChart_star_eq (r := ∞) (by simp)
    (ContinuousLinearEquiv.refl ℂ (Fin n → ℂ)) e_ℝ (Set.range_nonempty ι) fun x _ ↦ ?_
  obtain ⟨φ, hφ, hx, hφσ⟩ := h.exists_holomorphicChart_conj x
  refine ⟨φ, hφ, φ.source, φ.open_source, hx, Subset.rfl, fun y hy ↦ ?_⟩
  rw [← h.conj_eq_self_iff]
  simp only [ContinuousLinearEquiv.refl_apply, ← (hφσ y hy).2]
  exact ⟨fun hσy ↦ congrArg φ hσy, fun hφeq ↦ φ.injOn (hφσ y hy).1 hy hφeq⟩

end IsRealAnalyticComplexification

/-! ### The flat model `ℝⁿ ↪ ℂⁿ` -/

/-- **Flat model complexification.** Standard coordinate space `Fin n → ℂ`, with the real coordinate
inclusion `x ↦ (fun k ↦ (x k : ℂ))` and coordinatewise conjugation `star`, is a real-analytic
complexification of `Fin n → ℝ`. -/
theorem isRealAnalyticComplexification_pi (n : ℕ) :
    IsRealAnalyticComplexification 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ) n (Fin n → ℂ)
      (fun x k ↦ (x k : ℂ)) star where
  t2Space := inferInstance
  secondCountableTopology := inferInstance
  isManifold := inferInstance
  isClosedEmbedding := by
    let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℂ) := ContinuousLinearMap.piMap fun _ ↦ Complex.ofRealCLM
    let R : (Fin n → ℂ) →L[ℝ] (Fin n → ℝ) := ContinuousLinearMap.piMap fun _ ↦ Complex.reCLM
    have hRL : Function.LeftInverse R L := fun x ↦ by ext k; simp [L, R]
    exact hRL.isClosedEmbedding R.continuous L.continuous
  isTotallyRealEmbedding := by
    have hfun : (fun x : Fin n → ℝ ↦ fun k ↦ (x k : ℂ)) =
        ⇑(ContinuousLinearMap.piMap fun _ : Fin n ↦ Complex.ofRealCLM) := rfl
    rw [hfun]
    refine (isTotallyRealEmbedding_congr fun _ ↦ ?_).2
      (isTotallyRealEmbedding_realLocus (ι := Fin n) ω)
    exact (AlmostComplexStructure.constSmooth_almostComplexStructureAt _ _).symm
  involutive_conj := star_involutive
  fixedPoints_conj := by
    ext z
    simp only [Function.mem_fixedPoints, Set.mem_range]
    refine ⟨fun hz ↦ ⟨fun k ↦ (z k).re, funext fun k ↦
      Complex.conj_eq_iff_re.mp (congrFun hz k)⟩, ?_⟩
    rintro ⟨x, rfl⟩
    ext k
    simp
  exists_holomorphicChart_conj x :=
    ⟨OpenPartialHomeomorph.refl (Fin n → ℂ), chart_mem_maximalAtlas x, mem_univ x,
      fun _ _ ↦ ⟨mem_univ _, rfl⟩⟩

end

end TauCeti
