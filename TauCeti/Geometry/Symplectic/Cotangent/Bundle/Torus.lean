/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Geometry.Manifold.DeRham.Torus
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Graph
public import TauCeti.Geometry.Symplectic.Hamiltonian.Integrable

/-!
# Action-angle coordinates and Lagrangian sections of the cotangent bundle of a torus

For a finite family of positive periods `p i`, let `Tⁿ = ∀ i, AddCircle (p i)` be the torus with
coordinate time forms `dt_i` (`TauCeti.torusTimeForm p i`). Because the product charts of `Tⁿ` lift
locally to real coordinates with identity transition derivatives, the cotangent bundle `T*Tⁿ` is
canonically trivialized as `Tⁿ × ((ι → ℝ) →L[ℝ] ℝ)`
(`TauCeti.CotangentBundle.torusTrivialDiffeomorph`), with identity differential in the preferred
charts.

Evaluating a covector `ξ` on the coordinate tangent vectors `e_i = Pi.single i 1` defines the
canonical **action coordinates** `I_i = ξ(e_i)` (`TauCeti.CotangentBundle.torusAction`) and the
**action-angle diffeomorphism**

`T*Tⁿ ≃ₘ Tⁿ × (ι → ℝ)`, `ξ ↦ (π(ξ), I(ξ))`

(`TauCeti.CotangentBundle.torusActionAngleDiffeomorph`). Its inverse sends `(θ, c)` to the covector
at `θ` of the constant-coefficient closed one-form `α_c = ∑ j, c j • dt_j`
(`TauCeti.CotangentBundle.torusActionAngleDiffeomorph_symm_eq_section`). In these coordinates:

* the Liouville form is `λ = ∑ i, I_i dθ_i`
  (`TauCeti.CotangentBundle.mpullback_torusActionAngleDiffeomorph_symm_liouvilleForm_apply`);
* the canonical symplectic form `ω = -dλ` is `∑ i, dθ_i ∧ dI_i`
  (`TauCeti.CotangentBundle.eval₂_torusActionAngleDiffeomorph_symm_symplecticForm`);
* the actions `I` form a completely integrable system whose every point is regular
  (`TauCeti.CotangentBundle.isIntegrableSystem_torusAction`);
* any Hamiltonian `K ∘ I` depending only on the actions has Hamiltonian vector field
  `(∂K/∂I, 0)` (`TauCeti.CotangentBundle.hamiltonianVectorField_comp_torusAction`), so its
  integral curves are uniform linear motions on each invariant torus `(θ₀ + t ν, I₀)` with
  frequencies `ν_i = ∂K/∂I_i(I₀)`
  (`TauCeti.CotangentBundle.isMIntegralCurve_torusActionAngleDiffeomorph_symm_add`).

The constant-action fibres are the graphs of the closed one-forms `α_c = ∑ j, c j • dt_j`:

* The graph of `α_c` is a Lagrangian map for every `c`, since `α_c` is closed
  (`TauCeti.CotangentBundle.isLagrangianMap_section_sum_smul_torusTimeForm`).
* It is an exact Lagrangian map, for the primitive `λ` of `ω` and some primitive on the torus,
  exactly when `c = 0`, that is when it is the zero section
  (`TauCeti.CotangentBundle.exists_isExactLagrangianMap_section_sum_smul_torusTimeForm_iff`). This
  is because `α_c` integrates to `c i * p i` around the `i`-th coordinate circle.
* For `c ≠ 0` the graph of `α_c` meets the zero section nowhere
  (`TauCeti.CotangentBundle.section_sum_smul_torusTimeForm_eq_zeroSection_iff`): the form `α_c`
  vanishes at no point.

In particular the graph of a single angle form `dt_i` is a Lagrangian section of `T*Tⁿ` that is not
exact (`TauCeti.CotangentBundle.isLagrangianMap_section_torusTimeForm`,
`TauCeti.CotangentBundle.not_exists_isExactLagrangianMap_section_torusTimeForm`), and by the last
item it is disjoint from the zero section.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 49–50.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 3 and 18.4.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2.
-/

public section

noncomputable section

open Bundle Filter Function Set
open scoped Manifold ContDiff Topology

namespace TauCeti

namespace CotangentBundle

variable {ι : Type*} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)]

/-! ### Lagrangian sections -/

/-- **The graph of a constant-coefficient angle form is Lagrangian.** For every `c : ι → ℝ`, the
section of the cotangent bundle of the torus defined by the closed one-form `∑ j, c j • dt_j` is a
Lagrangian map for the canonical symplectic form. -/
theorem isLagrangianMap_section_sum_smul_torusTimeForm (c : ι → ℝ) :
    (isSymplectic_symplecticForm (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (M := ∀ i, AddCircle (p i))).isNondegenerate.IsLagrangianMap
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun x ↦ TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) x
        (SmoothForm.degreeOneEquiv (∑ j, c j • torusTimeForm p j) x)) := by
  exact (isLagrangianMap_section_iff _).2 (isClosed_sum_smul_torusTimeForm p c)

/-- **The graph of a constant-coefficient angle form is exact only when it is the zero section.**
The section of the cotangent bundle of the torus defined by `∑ j, c j • dt_j` is an exact
Lagrangian map, for the primitive `λ` of `ω = -dλ` and some primitive on the torus, if and only if
`c = 0`. -/
theorem exists_isExactLagrangianMap_section_sum_smul_torusTimeForm_iff (c : ι → ℝ) :
    (∃ h : (∀ i, AddCircle (p i)) → ℝ,
      (isSymplectic_symplecticForm (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (M := ∀ i, AddCircle (p i))).isNondegenerate.IsExactLagrangianMap
        (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (liouvilleForm _ _)
        (fun x ↦ TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) x
          (SmoothForm.degreeOneEquiv (∑ j, c j • torusTimeForm p j) x)) h) ↔
      c = 0 := by
  rw [exists_isExactLagrangianMap_section_iff, sum_smul_torusTimeForm_mem_exactForms_iff]

/-- **A nonzero constant-coefficient angle form has graph disjoint from the zero section.** At
every point `x` of the torus, the section of the cotangent bundle defined by `∑ j, c j • dt_j`
meets the zero section if and only if `c = 0`. -/
theorem section_sum_smul_torusTimeForm_eq_zeroSection_iff (c : ι → ℝ)
    (x : ∀ i, AddCircle (p i)) :
    TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) x
        (SmoothForm.degreeOneEquiv (∑ j, c j • torusTimeForm p j) x) =
      zeroSection ((ι → ℝ) →L[ℝ] ℝ)
        (fun y : ∀ i, AddCircle (p i) ↦
          TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) y →L[ℝ] ℝ) x ↔
      c = 0 := by
  classical
  rw [zeroSection, TotalSpace.mk_inj]
  refine ⟨fun h ↦ funext fun i ↦ ?_, fun h ↦ ?_⟩
  · -- The form sends every tangent vector `v` to `∑ j, c j * v j`; evaluate on the `i`-th
    -- coordinate vector.
    have hv (v : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x) :
        ∑ j, c j * v j = 0 := by
      have hx := SmoothForm.degreeOneEquiv_apply_apply (∑ j, c j • torusTimeForm p j) x v
      rw [h, sum_smul_torusTimeForm_apply, zero_apply] at hx
      exact hx.symm
    simpa [Pi.single_apply] using hv (Pi.single i 1)
  · ext v
    simp [h]

/-- **The graph of an angle form is Lagrangian.** The section of the cotangent bundle of the torus
defined by the coordinate time form `dt_i` is a Lagrangian map for the canonical symplectic form. -/
theorem isLagrangianMap_section_torusTimeForm (i : ι) :
    (isSymplectic_symplecticForm (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (M := ∀ i, AddCircle (p i))).isNondegenerate.IsLagrangianMap
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun x ↦ TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) x
        (SmoothForm.degreeOneEquiv (torusTimeForm p i) x)) :=
  (isLagrangianMap_section_iff _).2 (isClosed_torusTimeForm p i)

/-- **The graph of an angle form is not exact.** The section of the cotangent bundle of the torus
defined by the coordinate time form `dt_i` is not an exact Lagrangian map for the primitive `λ` of
`ω = -dλ`, whatever primitive on the torus is chosen. -/
@[simp]
theorem not_exists_isExactLagrangianMap_section_torusTimeForm (i : ι) :
    ¬∃ h : (∀ i, AddCircle (p i)) → ℝ,
      (isSymplectic_symplecticForm (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (M := ∀ i, AddCircle (p i))).isNondegenerate.IsExactLagrangianMap
        (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (liouvilleForm _ _)
        (fun x ↦ TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) x
          (SmoothForm.degreeOneEquiv (torusTimeForm p i) x)) h := by
  rw [exists_isExactLagrangianMap_section_iff]
  exact torusTimeForm_notMem_exactForms p i

/-! ### Canonical trivialization of the torus cotangent bundle -/

section Trivialization

/-- On a product chart of the torus `∀ i, AddCircle (p i)`, the inverse tangent trivialization acts
as the identity on every vector `v : ι → ℝ`. -/
private theorem symmL_trivializationAt_torus_apply {x₀ x : ∀ i, AddCircle (p i)}
    (hx : x ∈ (chartAt (ModelPi fun _ : ι ↦ ℝ) x₀).source) (v : ι → ℝ) :
    ((trivializationAt (ι → ℝ)
      (TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) x₀).symmL ℝ x v : ι → ℝ) = v := by
  let IT := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)
  have htriv := TangentBundle.symmL_trivializationAt (I := IT) hx
  have hx_src : x ∈ (extChartAt IT x₀).source := by simpa [extChartAt_source] using hx
  have hu_tgt : extChartAt IT x₀ x ∈ (extChartAt IT x₀).target :=
    (extChartAt IT x₀).map_source hx_src
  -- On `(extChartAt IT x₀).target`, the inverse extended chart is the covering map.
  have heq : (extChartAt IT x₀).symm =ᶠ[𝓝 (extChartAt IT x₀ x)]
      fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p i)) := by
    filter_upwards [(isOpen_extChartAt_target x₀).mem_nhds hu_tgt] with w hw
    ext i
    rw [extChartAt_pi] at hw ⊢
    exact AddCircle.extChartAt_symm_apply (x₀ i) (hw i trivial)
  have hfun := DFunLike.congr_fun htriv v
  rw [IT.range_eq_univ, mfderivWithin_univ] at hfun
  exact hfun.trans (DFunLike.congr_fun (heq.mfderiv_eq.trans (AddCircle.mfderiv_pi_coe _)) v)

/-- On a product chart of the torus, the forward tangent trivialization acts as the identity on
every tangent vector. -/
private theorem continuousLinearMapAt_trivializationAt_torus_apply {x₀ x : ∀ i, AddCircle (p i)}
    (hx : x ∈ (chartAt (ModelPi fun _ : ι ↦ ℝ) x₀).source)
    (v : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x) :
    (trivializationAt (ι → ℝ)
      (TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) x₀).continuousLinearMapAt ℝ x v =
      (v : ι → ℝ) := by
  have hb : x ∈ (trivializationAt (ι → ℝ)
      (TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) x₀).baseSet := by
    simpa using hx
  have h := (trivializationAt (ι → ℝ)
    (TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) x₀).continuousLinearMapAt_symmL
    (R := ℝ) hb (v : ι → ℝ)
  have hsymm : (trivializationAt (ι → ℝ)
      (TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) x₀).symmL ℝ x (v : ι → ℝ) = v :=
    symmL_trivializationAt_torus_apply p hx (v : ι → ℝ)
  rwa [hsymm] at h

/-- On a preferred chart of the torus cotangent bundle, the extended chart leaves the covector
coordinate unchanged. -/
private theorem extChartAt_torus_cotangent_apply
    {z₀ z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))}
    (hz : z.proj ∈ (chartAt (ModelPi fun _ : ι ↦ ℝ) z₀.proj).source) :
    extChartAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) z₀ z =
      (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) z₀.proj z.proj,
        (z.2 : (ι → ℝ) →L[ℝ] ℝ)) := by
  rw [CotangentBundle.extChartAt_apply]
  refine Prod.ext rfl (ContinuousLinearMap.ext fun v ↦ ?_)
  exact congrArg z.2 (symmL_trivializationAt_torus_apply p hz v)

/-- On the target of a base chart of the torus, the inverse preferred chart of the cotangent bundle
inserts the covector coordinate directly. -/
private theorem extChartAt_torus_cotangent_symm_apply
    (z₀ : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))
    {q : ι → ℝ} (ξ : (ι → ℝ) →L[ℝ] ℝ)
    (hq : q ∈ (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) z₀.proj).target) :
    (extChartAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) z₀).symm
        (q, ξ) =
      TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ)
        ((extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) z₀.proj).symm q) ξ := by
  have hx : (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) z₀.proj).symm q ∈
      (chartAt (ModelPi fun _ : ι ↦ ℝ) z₀.proj).source := by
    simpa [extChartAt_source] using
      (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) z₀.proj).map_target hq
  rw [CotangentBundle.extChartAt_symm_apply z₀ ξ hq]
  exact CotangentBundle.ext rfl fun v ↦
    congrArg ξ (continuousLinearMapAt_trivializationAt_torus_apply p hx v)

/-- The **canonical trivialization** of the cotangent bundle of the torus `∀ i, AddCircle (p i)`:
since the tangent space at every point is `ι → ℝ` with identity transition maps between product
charts, `z ↦ (z.proj, z.2)` is a `C^n` diffeomorphism onto
`(∀ i, AddCircle (p i)) × ((ι → ℝ) →L[ℝ] ℝ)` for every `n`. -/
def torusTrivialDiffeomorph (n : ℕ∞ω) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) ≃ₘ^n⟮
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ),
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)⟯
    (∀ i, AddCircle (p i)) × ((ι → ℝ) →L[ℝ] ℝ) where
  toFun z := (z.proj, z.2)
  invFun q := TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) q.1 q.2
  left_inv z := rfl
  right_inv q := rfl
  contMDiff_toFun z₀ := by
    let IT := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)
    let IC := IT.prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)
    -- Near `z₀`, `z ↦ z.2` is the second component of the extended chart at `z₀`.
    have hsnd : ContMDiffAt IC 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ) n (M' := (ι → ℝ) →L[ℝ] ℝ)
        (fun z ↦ z.2) z₀ := by
      have hext : ContMDiffAt IC 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) n
          (extChartAt IC z₀) z₀ :=
        contMDiffAt_extChartAt
      refine ((ContinuousLinearMap.snd ℝ (ι → ℝ)
        ((ι → ℝ) →L[ℝ] ℝ)).contMDiff.contMDiffAt.comp z₀ hext).congr_of_eventuallyEq ?_
      have hnhds : (chartAt (ModelPi fun _ : ι ↦ ℝ) z₀.proj).source ∈ 𝓝 z₀.proj :=
        (chartAt _ z₀.proj).open_source.mem_nhds (mem_chart_source _ z₀.proj)
      filter_upwards [(FiberBundle.continuous_proj ((ι → ℝ) →L[ℝ] ℝ)
        _).continuousAt.preimage_mem_nhds hnhds] with z hz
      exact congrArg Prod.snd (extChartAt_torus_cotangent_apply p hz).symm
    exact (Bundle.contMDiff_proj _ z₀).prodMk hsnd
  contMDiff_invFun q₀ := by
    let IT := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)
    let IC := IT.prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)
    let z₀ : CotangentBundle IT (∀ i, AddCircle (p i)) :=
      TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) q₀.1 q₀.2
    -- Near `q₀`, the inverse map is `(extChartAt IC z₀).symm` composed with
    -- `(extChartAt IT q₀.1, id)`.
    have hchart : ContMDiffAt IC 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) n
        (fun q : (∀ i, AddCircle (p i)) × ((ι → ℝ) →L[ℝ] ℝ) ↦
          (extChartAt IT z₀.proj q.1, q.2)) q₀ :=
      (contMDiffAt_extChartAt.comp q₀ contMDiff_fst.contMDiffAt).prodMk_space
        contMDiff_snd.contMDiffAt
    have hsymm : ContMDiffAt 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) IC n
        (extChartAt IC z₀).symm (extChartAt IT z₀.proj q₀.1, q₀.2) := by
      have hmem : (extChartAt IT z₀.proj q₀.1, q₀.2) ∈ (extChartAt IC z₀).target := by
        have heq : extChartAt IC z₀ z₀ = (extChartAt IT z₀.proj q₀.1, q₀.2) :=
          extChartAt_torus_cotangent_apply p (z₀ := z₀) (z := z₀) (mem_chart_source _ z₀.proj)
        rw [← heq]
        exact mem_extChartAt_target z₀
      exact (contMDiffOn_extChartAt_symm z₀ _ hmem).contMDiffAt
        ((isOpen_extChartAt_target z₀).mem_nhds hmem)
    refine (hsymm.comp q₀ hchart).congr_of_eventuallyEq ?_
    have hnhds : (extChartAt IT z₀.proj).source ∈ 𝓝 q₀.1 :=
      extChartAt_source_mem_nhds z₀.proj
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hnhds] with q hq
    have hqt : extChartAt IT z₀.proj q.1 ∈ (extChartAt IT z₀.proj).target :=
      (extChartAt IT z₀.proj).map_source hq
    refine ((extChartAt_torus_cotangent_symm_apply p z₀ q.2 hqt).trans ?_).symm
    rw [(extChartAt IT z₀.proj).left_inv hq]
    rfl

/-- The canonical trivialization sends `z` to `(z.proj, z.2)`. -/
@[simp]
theorem torusTrivialDiffeomorph_apply (n : ℕ∞ω)
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    torusTrivialDiffeomorph p n z = (z.proj, (z.2 : (ι → ℝ) →L[ℝ] ℝ)) :=
  (rfl)

/-- The inverse of the canonical trivialization constructs a covector from its base point and linear
functional. -/
@[simp]
theorem torusTrivialDiffeomorph_symm_apply (n : ℕ∞ω)
    (q : (∀ i, AddCircle (p i)) × ((ι → ℝ) →L[ℝ] ℝ)) :
    (torusTrivialDiffeomorph p n).symm q = TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) q.1 q.2 :=
  (rfl)

/-- Read in preferred charts, the canonical trivialization of the torus cotangent bundle has
derivative the identity at every point. -/
theorem hasMFDerivAt_torusTrivialDiffeomorph (n : ℕ∞ω)
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    HasMFDerivAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (torusTrivialDiffeomorph p n) z
      (ContinuousLinearMap.id ℝ ((ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))) := by
  let IT := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)
  let IC := IT.prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)
  refine ⟨((torusTrivialDiffeomorph p ⊤).contMDiff.continuous.continuousAt).congr
      (Eventually.of_forall fun _ ↦ rfl), ?_⟩
  rw [IC.range_eq_univ, hasFDerivWithinAt_univ]
  have heq : writtenInExtChartAt IC IC z (torusTrivialDiffeomorph p n)
      =ᶠ[𝓝 (extChartAt IC z z)] id := by
    filter_upwards [(isOpen_extChartAt_target z).mem_nhds (mem_extChartAt_target z)] with w hw
    have hq : w.1 ∈ (extChartAt IT z.proj).target :=
      Bundle.fst_mem_extChartAt_target z hw
    -- Unfold `writtenInExtChartAt` and rewrite the inverse cotangent chart on `w = (w.1, w.2)`.
    have hw_symm := extChartAt_torus_cotangent_symm_apply p z w.2 hq
    rw [Prod.mk.eta (p := w)] at hw_symm
    simp only [writtenInExtChartAt, Function.comp_apply, id_eq]
    rw [hw_symm, torusTrivialDiffeomorph_apply]
    exact Prod.ext ((extChartAt IT z.proj).right_inv hq) rfl
  exact (hasFDerivAt_id _).congr_of_eventuallyEq heq

/-- The differential of the canonical trivialization of the torus cotangent bundle is the identity
at every point. -/
@[simp]
theorem mfderiv_torusTrivialDiffeomorph (n : ℕ∞ω)
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (torusTrivialDiffeomorph p n) z =
      ContinuousLinearMap.id ℝ ((ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) :=
  (hasMFDerivAt_torusTrivialDiffeomorph p n z).mfderiv

/-- The differential of the inverse canonical trivialization of the torus cotangent bundle is the
identity at every point. -/
theorem hasMFDerivAt_torusTrivialDiffeomorph_symm (n : ℕ∞ω)
    (q : (∀ i, AddCircle (p i)) × ((ι → ℝ) →L[ℝ] ℝ)) :
    HasMFDerivAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (torusTrivialDiffeomorph p n).symm q
      (ContinuousLinearMap.id ℝ ((ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))) := by
  have hd : MDifferentiableAt
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (torusTrivialDiffeomorph p n).symm q :=
    (((torusTrivialDiffeomorph p ⊤).symm.contMDiff q).mdifferentiableAt
      (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl)
  refine hd.hasMFDerivAt.congr_mfderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  have h := (torusTrivialDiffeomorph p ⊤).mfderiv_apply_mfderiv_symm_apply (by simp)
    ((torusTrivialDiffeomorph p ⊤).symm q) v
  rw [(torusTrivialDiffeomorph p ⊤).apply_symm_apply q, mfderiv_torusTrivialDiffeomorph] at h
  have heq : mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (torusTrivialDiffeomorph p n).symm q =
      mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (torusTrivialDiffeomorph p ⊤).symm q :=
    Filter.EventuallyEq.mfderiv_eq (Eventually.of_forall fun _ ↦ rfl)
  rw [heq]
  exact h

/-- The differential of the inverse canonical trivialization of the torus cotangent bundle is the
identity at every point. -/
@[simp]
theorem mfderiv_torusTrivialDiffeomorph_symm (n : ℕ∞ω)
    (q : (∀ i, AddCircle (p i)) × ((ι → ℝ) →L[ℝ] ℝ)) :
    mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (torusTrivialDiffeomorph p n).symm q =
      ContinuousLinearMap.id ℝ ((ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) :=
  (hasMFDerivAt_torusTrivialDiffeomorph_symm p n q).mfderiv

end Trivialization

/-! ### Action-angle coordinates on the torus cotangent bundle -/

section ActionAngle

/-- The canonical **action coordinates** on the cotangent bundle of the torus
`∀ i, AddCircle (p i)`: a covector `z` has `i`-th action `z.2 (Pi.single i 1)`, its evaluation on
the `i`-th coordinate vector of the tangent space `ι → ℝ`. -/
def torusAction
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    ι → ℝ :=
  open scoped Classical in
  ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι (z.2 : (ι → ℝ) →L[ℝ] ℝ)

/-- The `i`-th action coordinate evaluates the covector on `Pi.single i 1`. -/
@[simp]
theorem torusAction_apply [DecidableEq ι]
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) (i : ι) :
    torusAction p z i = z.2 (Pi.single i 1) := by
  have hd : Classical.decEq ι = ‹DecidableEq ι› := Subsingleton.elim _ _
  have h1 : torusAction p z i = z.2 (@Pi.single ι (fun _ ↦ ℝ) _ (Classical.decEq ι) i 1) := rfl
  rwa [hd] at h1

/-- Characterization of `torusAction` as evaluation on `Pi.single i 1`. -/
theorem torusAction_def [DecidableEq ι]
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    torusAction p z = fun i ↦ z.2 (Pi.single i 1) :=
  funext (torusAction_apply p z)

/-- The action coordinates vanish along the zero section of the torus cotangent bundle. -/
@[simp]
theorem torusAction_zeroSection (x : ∀ i, AddCircle (p i)) :
    torusAction p (zeroSection ((ι → ℝ) →L[ℝ] ℝ)
      (fun y : ∀ i, AddCircle (p i) ↦
        TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) y →L[ℝ] ℝ) x) = 0 := by
  classical
  ext i
  rw [torusAction_apply]
  rfl

/-- Along the graph of the constant-coefficient closed one-form `∑ j, c j • dt_j`, the action
coordinates take the constant value `c`. -/
theorem torusAction_section_sum_smul_torusTimeForm (c : ι → ℝ) (x : ∀ i, AddCircle (p i)) :
    torusAction p (TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) x
      (SmoothForm.degreeOneEquiv (∑ j, c j • torusTimeForm p j) x)) = c := by
  classical
  ext i
  rw [torusAction_apply]
  exact ((SmoothForm.degreeOneEquiv_apply_apply (∑ j, c j • torusTimeForm p j) x
    (Pi.single i 1)).trans
    (sum_smul_torusTimeForm_apply p c x fun _ ↦ Pi.single i 1)).trans
    (by simp [Pi.single_apply])

/-- The **action-angle diffeomorphism** of the cotangent bundle of the torus
`∀ i, AddCircle (p i)`: a covector `z` is sent to its base point `z.proj` (the angles) and its
coordinate evaluations `torusAction p z` (the actions). -/
def torusActionAngleDiffeomorph :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) ≃ₘ⟮
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ),
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ)⟯
    (∀ i, AddCircle (p i)) × (ι → ℝ) :=
  open scoped Classical in
  { toFun z := (z.proj, torusAction p z)
    invFun q := (torusTrivialDiffeomorph p ∞).symm
      (q.1, (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).symm q.2)
    left_inv _ := CotangentBundle.ext rfl fun v ↦
      DFunLike.congr_fun
        ((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).symm_apply_apply _) v
    right_inv q := Prod.ext rfl
      ((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).apply_symm_apply q.2)
    contMDiff_toFun :=
      (contMDiff_fst.comp (torusTrivialDiffeomorph p ∞).contMDiff).prodMk
        ((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).contDiff.contMDiff.comp
          (contMDiff_snd.comp (torusTrivialDiffeomorph p ∞).contMDiff))
    contMDiff_invFun :=
      (torusTrivialDiffeomorph p ∞).symm.contMDiff.comp
        (contMDiff_fst.prodMk
          ((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).symm.contDiff.contMDiff.comp
            contMDiff_snd)) }

/-- The action-angle diffeomorphism sends `z` to `(z.proj, torusAction p z)`. -/
theorem torusActionAngleDiffeomorph_apply
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    torusActionAngleDiffeomorph p z = (z.proj, torusAction p z) :=
  (rfl)

/-- The angle component of `torusActionAngleDiffeomorph` is the bundle projection. -/
@[simp]
theorem fst_torusActionAngleDiffeomorph
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    (torusActionAngleDiffeomorph p z).1 = z.proj :=
  (rfl)

/-- The action component of `torusActionAngleDiffeomorph` is `torusAction`. -/
@[simp]
theorem snd_torusActionAngleDiffeomorph
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    (torusActionAngleDiffeomorph p z).2 = torusAction p z :=
  (rfl)

/-- The inverse of `torusActionAngleDiffeomorph` lies over the first factor. -/
@[simp]
theorem proj_torusActionAngleDiffeomorph_symm (q : (∀ i, AddCircle (p i)) × (ι → ℝ)) :
    ((torusActionAngleDiffeomorph p).symm q).proj = q.1 :=
  (rfl)

/-- The inverse of `torusActionAngleDiffeomorph` sends `(θ, c)` to the covector `v ↦ ∑ i, c i * v i`
over `θ`. -/
@[simp]
theorem torusActionAngleDiffeomorph_symm_snd_apply (q : (∀ i, AddCircle (p i)) × (ι → ℝ))
    (v : ι → ℝ) :
    ((torusActionAngleDiffeomorph p).symm q).2 v = ∑ i, q.2 i * v i :=
  open scoped Classical in
  (ContinuousLinearEquiv.piRing_symm_apply q.2 v).trans
    (Finset.sum_congr rfl fun i _ ↦ mul_comm (v i) (q.2 i))

/-- The action coordinates of `(torusActionAngleDiffeomorph p).symm q` are `q.2`. -/
@[simp]
theorem torusAction_torusActionAngleDiffeomorph_symm (q : (∀ i, AddCircle (p i)) × (ι → ℝ)) :
    torusAction p ((torusActionAngleDiffeomorph p).symm q) = q.2 :=
  congrArg Prod.snd ((torusActionAngleDiffeomorph p).apply_symm_apply q)

/-- At fixed action `c`, the slice `θ ↦ (torusActionAngleDiffeomorph p).symm (θ, c)` is the graph of
the constant-coefficient closed one-form `∑ j, c j • dt_j`. -/
theorem torusActionAngleDiffeomorph_symm_eq_section (θ : ∀ i, AddCircle (p i)) (c : ι → ℝ) :
    (torusActionAngleDiffeomorph p).symm (θ, c) =
      TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) θ
        (SmoothForm.degreeOneEquiv (∑ j, c j • torusTimeForm p j) θ) :=
  CotangentBundle.ext rfl fun v ↦
    (torusActionAngleDiffeomorph_symm_snd_apply p (θ, c) v).trans
      ((SmoothForm.degreeOneEquiv_apply_apply _ θ v).trans
        (sum_smul_torusTimeForm_apply p c θ fun _ ↦ v)).symm

/-- The canonical action map `torusAction p` is smooth. -/
theorem contMDiff_torusAction :
    ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      𝓘(ℝ, ι → ℝ) ∞ (torusAction p) :=
  contMDiff_snd.comp (torusActionAngleDiffeomorph p).contMDiff

/-- The differential of `(torusActionAngleDiffeomorph p).symm` acts as the identity on the angle
direction and applies `(ContinuousLinearEquiv.piRing ι).symm` in the covector direction. -/
theorem hasMFDerivAt_torusActionAngleDiffeomorph_symm [DecidableEq ι]
    (q : (∀ i, AddCircle (p i)) × (ι → ℝ)) :
    HasMFDerivAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (torusActionAngleDiffeomorph p).symm q
      ((ContinuousLinearMap.id ℝ (ι → ℝ)).prodMap
        ((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).symm :
          (ι → ℝ) →L[ℝ] ((ι → ℝ) →L[ℝ] ℝ))) := by
  have hsymm_eq : ⇑(torusActionAngleDiffeomorph p).symm =
      (torusTrivialDiffeomorph p ∞).symm ∘
        Prod.map id (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).symm := by
    funext r
    exact CotangentBundle.ext rfl fun v ↦
      (torusActionAngleDiffeomorph_symm_snd_apply p r v).trans
        ((Finset.sum_congr rfl fun i _ ↦ mul_comm (r.2 i) (v i)).trans
          (ContinuousLinearEquiv.piRing_symm_apply r.2 v).symm)
  have h1 : HasMFDerivAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (Prod.map id (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).symm) q
      ((ContinuousLinearMap.id ℝ (ι → ℝ)).prodMap
        ((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).symm :
          (ι → ℝ) →L[ℝ] ((ι → ℝ) →L[ℝ] ℝ))) :=
    ((hasMFDerivAt_fst q).prodMk
      (((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).symm :
        (ι → ℝ) →L[ℝ] ((ι → ℝ) →L[ℝ] ℝ)).hasMFDerivAt.comp q
        (hasMFDerivAt_snd q))).congr_mfderiv (ContinuousLinearMap.ext fun _ ↦ rfl)
  exact (((hasMFDerivAt_torusTrivialDiffeomorph_symm p ∞
    (Prod.map id (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).symm q)).comp q
    h1).congr_mfderiv (ContinuousLinearMap.id_comp _)).congr_of_eventuallyEq
    (Eventually.of_forall (congrFun hsymm_eq))

/-- Applying the differential of `(torusActionAngleDiffeomorph p).symm` to `(u, b)` yields
`(u, ∑ i, b i • proj i)`. -/
theorem mfderiv_torusActionAngleDiffeomorph_symm_apply (q : (∀ i, AddCircle (p i)) × (ι → ℝ))
    (w : TangentSpace ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ)) q) :
    (mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (torusActionAngleDiffeomorph p).symm q w : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) =
      (w.1, ∑ i, w.2 i • ContinuousLinearMap.proj i) := by
  classical
  refine (DFunLike.congr_fun (hasMFDerivAt_torusActionAngleDiffeomorph_symm p q).mfderiv
    w).trans (Prod.ext rfl (ContinuousLinearMap.ext fun v ↦ ?_))
  refine (ContinuousLinearEquiv.piRing_symm_apply (w : (ι → ℝ) × (ι → ℝ)).2 v).trans ?_
  simp [sum_apply, mul_comm]

/-- The differential of `torusActionAngleDiffeomorph` acts as the identity on the angle direction
and evaluates covector variations on the standard basis vectors via
`ContinuousLinearEquiv.piRing`. -/
theorem hasMFDerivAt_torusActionAngleDiffeomorph [DecidableEq ι]
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    HasMFDerivAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
      (torusActionAngleDiffeomorph p) z
      ((ContinuousLinearMap.id ℝ (ι → ℝ)).prodMap
        (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι :
          ((ι → ℝ) →L[ℝ] ℝ) →L[ℝ] (ι → ℝ))) := by
  have hfwd_eq : ⇑(torusActionAngleDiffeomorph p) =
      Prod.map id (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι) ∘
        torusTrivialDiffeomorph p ∞ := by
    funext w
    exact Prod.ext rfl (funext fun i ↦
      (torusAction_apply p w i).trans
        (ContinuousLinearEquiv.piRing_apply (w.2 : (ι → ℝ) →L[ℝ] ℝ) i).symm)
  have h2 : HasMFDerivAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
      (Prod.map id (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι))
      (torusTrivialDiffeomorph p ∞ z)
      ((ContinuousLinearMap.id ℝ (ι → ℝ)).prodMap
        (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι :
          ((ι → ℝ) →L[ℝ] ℝ) →L[ℝ] (ι → ℝ))) :=
    ((hasMFDerivAt_fst _).prodMk
      ((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι :
        ((ι → ℝ) →L[ℝ] ℝ) →L[ℝ] (ι → ℝ)).hasMFDerivAt.comp _
        (hasMFDerivAt_snd _))).congr_mfderiv (ContinuousLinearMap.ext fun _ ↦ rfl)
  exact ((h2.comp z (hasMFDerivAt_torusTrivialDiffeomorph p ∞ z)).congr_mfderiv
    (ContinuousLinearMap.comp_id _)).congr_of_eventuallyEq
    (Eventually.of_forall (congrFun hfwd_eq))

/-- The differential of `torusAction` at `z` sends a tangent vector `(u, η)` to
`ContinuousLinearEquiv.piRing ι η`. -/
theorem hasMFDerivAt_torusAction [DecidableEq ι]
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    HasMFDerivAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      𝓘(ℝ, ι → ℝ) (torusAction p) z
      ((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι :
        ((ι → ℝ) →L[ℝ] ℝ) →L[ℝ] (ι → ℝ)).comp
        (ContinuousLinearMap.snd ℝ (ι → ℝ) ((ι → ℝ) →L[ℝ] ℝ))) := by
  have h := (hasMFDerivAt_snd (torusActionAngleDiffeomorph p z)).comp z
    (hasMFDerivAt_torusActionAngleDiffeomorph p z)
  exact h.congr_mfderiv (ContinuousLinearMap.ext fun _ ↦ rfl)

/-- Applying the differential of `torusAction` at `z` to `(u, η)` yields
`ContinuousLinearEquiv.piRing ι η`. -/
@[simp]
theorem mfderiv_torusAction_apply [DecidableEq ι]
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))
    (w : TangentSpace ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) z) :
    mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      𝓘(ℝ, ι → ℝ) (torusAction p) z w =
      ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι
        (w : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)).2 :=
  DFunLike.congr_fun (hasMFDerivAt_torusAction p z).mfderiv w

/-- **Action-angle formula for the Liouville form.** Pulled back along
`(torusActionAngleDiffeomorph p).symm`, the Liouville one-form evaluates `v` at `(θ, I)` as
`∑ i, I i * (v 0).1 i`, that is `λ = ∑ i, I_i dθ_i`. -/
theorem mpullback_torusActionAngleDiffeomorph_symm_liouvilleForm_apply
    (q : (∀ i, AddCircle (p i)) × (ι → ℝ))
    (v : Fin 1 → TangentSpace ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ)) q) :
    (SmoothForm.mpullback (torusActionAngleDiffeomorph p).symm
      (torusActionAngleDiffeomorph p).symm.contMDiff
      (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))).1 q v =
      ∑ i, q.2 i * (v 0).1 i := by
  classical
  rw [SmoothForm.coe_mpullback]
  refine (mpullback_liouvilleForm_apply_of_proj_comp_eq (g := Prod.fst) (fun _ ↦ rfl)
    (hasMFDerivAt_torusActionAngleDiffeomorph_symm p q).mdifferentiableAt v).trans ?_
  have hfst : (mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) Prod.fst q (v 0) : ι → ℝ) = (v 0).1 := by
    rw [mfderiv_fst]
    rfl
  exact (congrArg ((torusActionAngleDiffeomorph p).symm q).2 hfst).trans
    (torusActionAngleDiffeomorph_symm_snd_apply p q (v 0).1)

/-- **Action-angle formula for the canonical symplectic form.** Pulling `ω = -dλ` back along
`(torusActionAngleDiffeomorph p).symm` gives `∑ i, dθ_i ∧ dI_i`: on tangent vectors `v` and `w` at
`(θ, I)` it evaluates to `∑ i, (v.1 i * w.2 i - w.1 i * v.2 i)`. -/
theorem eval₂_torusActionAngleDiffeomorph_symm_symplecticForm
    (q : (∀ i, AddCircle (p i)) × (ι → ℝ))
    (v w : TangentSpace ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ)) q) :
    SmoothBundleForm.eval₂
      (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))
      ((torusActionAngleDiffeomorph p).symm q)
      (mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (torusActionAngleDiffeomorph p).symm q v)
      (mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (torusActionAngleDiffeomorph p).symm q w) =
      ∑ i, (v.1 i * w.2 i - w.1 i * v.2 i) := by
  let v' : (ι → ℝ) × (ι → ℝ) := v
  let w' : (ι → ℝ) × (ι → ℝ) := w
  refine (eval₂_symplecticForm _ _ _).trans ?_
  refine (congrArg₂ (strongDualCotangentSymplecticForm (V := ι → ℝ))
    (mfderiv_torusActionAngleDiffeomorph_symm_apply p q v)
    (mfderiv_torusActionAngleDiffeomorph_symm_apply p q w)).trans ?_
  refine (strongDualCotangentSymplecticForm_apply
    (v'.1, ∑ i, v'.2 i • ContinuousLinearMap.proj i)
    (w'.1, ∑ i, w'.2 i • ContinuousLinearMap.proj i)).trans ?_
  simp only [sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-! ### Integrability and linear Hamiltonian dynamics on the torus cotangent bundle -/

/-- **Hamiltonian vector field of an action-only Hamiltonian.** For any function `K : (ι → ℝ) → ℝ`
differentiable at `torusAction p z`, the Hamiltonian vector field of `K ∘ torusAction p` on the
torus cotangent bundle is `(fun i ↦ ∂K/∂I_i, 0)` in the preferred chart at `z`. -/
theorem hamiltonianVectorField_comp_torusAction [DecidableEq ι]
    {z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))}
    {K : (ι → ℝ) → ℝ} (hK : DifferentiableAt ℝ K (torusAction p z)) :
    ((symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (∀ i, AddCircle (p i))).hamiltonianVectorField (K ∘ torusAction p) z :
      (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) =
      (fun i ↦ fderiv ℝ K (torusAction p z) (Pi.single i 1), 0) := by
  have hnd := (isSymplectic_symplecticForm
    (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (M := ∀ i, AddCircle (p i))).isNondegenerate
  let X : TangentSpace ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) z :=
    (fun i ↦ fderiv ℝ K (torusAction p z) (Pi.single i 1), (0 : (ι → ℝ) →L[ℝ] ℝ))
  suffices (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (∀ i, AddCircle (p i))).hamiltonianVectorField (K ∘ torusAction p) z = X from this
  apply (hnd.isInvertible_flat z).injective
  rw [hnd.flat_hamiltonianVectorField]
  ext w
  let w' : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ) := w
  rw [SmoothTwoForm.flat_apply, eval₂_symplecticForm,
    mvfderiv_comp_apply_of_differentiableAt hK (hasMFDerivAt_torusAction p z).mdifferentiableAt,
    mvfderiv_apply_eq_mfderiv_apply, mfderiv_torusAction_apply]
  refine (?_ : fderiv ℝ K (torusAction p z)
      (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι w'.2) =
    w'.2 (fun i ↦ fderiv ℝ K (torusAction p z) (Pi.single i 1)) -
      (0 : (ι → ℝ) →L[ℝ] ℝ) w'.1).trans
    (strongDualCotangentSymplecticForm_apply
      (fun i ↦ fderiv ℝ K (torusAction p z) (Pi.single i 1), (0 : (ι → ℝ) →L[ℝ] ℝ)) w').symm
  rw [zero_apply, sub_zero]
  have hexp : ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι w'.2 =
      ∑ i, w'.2 (Pi.single i 1) • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  have hexp' : (fun i ↦ fderiv ℝ K (torusAction p z) (Pi.single i 1)) =
      ∑ i, fderiv ℝ K (torusAction p z) (Pi.single i 1) • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  rw [hexp, map_sum, hexp', map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]

/-- The Hamiltonian vector field of the `i`-th action coordinate is the `i`-th coordinate angle
field `(Pi.single i 1, 0)`. -/
theorem hamiltonianVectorField_torusAction [DecidableEq ι] (i : ι)
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    ((symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (∀ i, AddCircle (p i))).hamiltonianVectorField (fun w ↦ torusAction p w i) z :
      (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) = (Pi.single i 1, 0) := by
  let L : (ι → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h := hamiltonianVectorField_comp_torusAction p (z := z) (K := L) L.differentiableAt
  refine h.trans (Prod.ext ?_ rfl)
  ext j
  simp [L, Pi.single_apply, eq_comm]

/-- The canonical action coordinates on the torus cotangent bundle pairwise Poisson-commute. -/
@[simp]
theorem poissonBracket_torusAction (i j : ι)
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (∀ i, AddCircle (p i))).poissonBracket
      (fun w ↦ torusAction p w i) (fun w ↦ torusAction p w j) z = 0 := by
  classical
  have hnd := (isSymplectic_symplecticForm
    (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (M := ∀ i, AddCircle (p i))).isNondegenerate
  rw [hnd.poissonBracket_eq_mvfderiv]
  have hd : HasMFDerivAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      𝓘(ℝ) (fun w ↦ torusAction p w i) z
      ((ContinuousLinearMap.proj i).comp
        ((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι :
          ((ι → ℝ) →L[ℝ] ℝ) →L[ℝ] (ι → ℝ)).comp
          (ContinuousLinearMap.snd ℝ (ι → ℝ) ((ι → ℝ) →L[ℝ] ℝ)))) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).hasMFDerivAt.comp z
      (hasMFDerivAt_torusAction p z)
  rw [mvfderiv_apply_eq_mfderiv_apply]
  refine (DFunLike.congr_fun hd.mfderiv _).trans ?_
  have hX2 : ContinuousLinearMap.snd ℝ (ι → ℝ) ((ι → ℝ) →L[ℝ] ℝ)
      ((symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (∀ i, AddCircle (p i))).hamiltonianVectorField (fun w ↦ torusAction p w j) z) = 0 :=
    congrArg Prod.snd (hamiltonianVectorField_torusAction p j z)
  exact (congrArg (fun η ↦ ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι η i) hX2).trans
    (by simp)

/-- Every point of the torus cotangent bundle is a regular point of `torusAction p`. -/
theorem isRegularPoint_torusAction
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    IsRegularPoint ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      𝓘(ℝ, ι → ℝ) (torusAction p) z := by
  classical
  rw [isRegularPoint_iff]
  intro b
  let w : TangentSpace ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) z :=
    ((0 : ι → ℝ), (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).symm b)
  refine ⟨w, ?_⟩
  rw [mfderiv_torusAction_apply]
  exact (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).apply_symm_apply b

/-- **The canonical actions on `T*Tⁿ` form a completely integrable system.** For any finite family
of positive periods `p`, the action map `torusAction p` on the cotangent bundle of
`∀ i, AddCircle (p i)` is a completely integrable system for the canonical symplectic form. -/
theorem isIntegrableSystem_torusAction :
    (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (∀ i, AddCircle (p i))).IsIntegrableSystem (torusAction p) where
  contMDiff := contMDiff_torusAction p
  poissonBracket_eq_zero := poissonBracket_torusAction p
  dense_setOf_isRegularPoint := dense_univ.mono fun z _ ↦ isRegularPoint_torusAction p z
  two_mul_card_eq_finrank := by
    classical
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).toLinearEquiv.finrank_eq,
      Module.finrank_fintype_fun_eq_card, two_mul]

/-- **Quasiperiodic linear Hamiltonian flow in action-angle coordinates.** For any `K : (ι → ℝ) → ℝ`
differentiable at `I₀`, the curve `t ↦ (θ₀ + [t · ∂K/∂I(I₀)], I₀)` in action-angle coordinates is a
global integral curve of the Hamiltonian vector field of `K ∘ torusAction p`. -/
theorem isMIntegralCurve_torusActionAngleDiffeomorph_symm_add [DecidableEq ι]
    (θ₀ : ∀ i, AddCircle (p i)) {I₀ : ι → ℝ} {K : (ι → ℝ) → ℝ}
    (hK : DifferentiableAt ℝ K I₀) :
    IsMIntegralCurve
      (fun t : ℝ ↦ (torusActionAngleDiffeomorph p).symm
        (θ₀ + fun i ↦ ((t * fderiv ℝ K I₀ (Pi.single i 1) : ℝ) : AddCircle (p i)), I₀))
      ((symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (∀ i, AddCircle (p i))).hamiltonianVectorField (K ∘ torusAction p)) := fun t ↦ by
  set ν : ι → ℝ := fun i ↦ fderiv ℝ K I₀ (Pi.single i 1)
  -- Differentiate `t ↦ t • ν` in `ι → ℝ`, project to the torus, and translate by `θ₀`.
  have hlin : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, ι → ℝ) (fun s : ℝ ↦ fun i ↦ s * ν i) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight ν) :=
    ((hasFDerivAt_id t).smul_const ν).hasMFDerivAt
  have hcov : HasMFDerivAt 𝓘(ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun s : ℝ ↦ fun i ↦ ((s * ν i : ℝ) : AddCircle (p i))) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight ν) :=
    ((AddCircle.hasMFDerivAt_pi_coe (p := p) (fun i ↦ t * ν i)).comp t hlin).congr_mfderiv
      (ContinuousLinearMap.id_comp _)
  have htr : HasMFDerivAt 𝓘(ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun s : ℝ ↦ θ₀ + fun i ↦ ((s * ν i : ℝ) : AddCircle (p i))) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight ν) := by
    have hadd : (fun s : ℝ ↦ θ₀ + fun i ↦ ((s * ν i : ℝ) : AddCircle (p i))) =
        (· + θ₀) ∘ fun s : ℝ ↦ fun i ↦ ((s * ν i : ℝ) : AddCircle (p i)) :=
      funext fun _ ↦ add_comm _ _
    rw [hadd]
    exact ((AddCircle.hasMFDerivAt_pi_add_right θ₀ _).comp t hcov).congr_mfderiv
      (ContinuousLinearMap.id_comp _)
  have hprod : HasMFDerivAt 𝓘(ℝ)
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
      (fun s : ℝ ↦ (θ₀ + fun i ↦ ((s * ν i : ℝ) : AddCircle (p i)), I₀)) t
      (((1 : ℝ →L[ℝ] ℝ).smulRight ν).prod (0 : ℝ →L[ℝ] ι → ℝ)) :=
    htr.prodMk (hasMFDerivAt_const I₀ t)
  have hfull := (hasMFDerivAt_torusActionAngleDiffeomorph_symm p _).comp t hprod
  refine hfull.congr_mfderiv (ContinuousLinearMap.ext fun r ↦ ?_)
  let r' : ℝ := r
  set zt := (torusActionAngleDiffeomorph p).symm
    (θ₀ + fun i ↦ ((t * ν i : ℝ) : AddCircle (p i)), I₀)
  have hact : torusAction p zt = I₀ := torusAction_torusActionAngleDiffeomorph_symm p _
  let X0 : TangentSpace ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) zt :=
    (ν, (0 : (ι → ℝ) →L[ℝ] ℝ))
  have hX_eq : (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (∀ i, AddCircle (p i))).hamiltonianVectorField (K ∘ torusAction p) zt = X0 :=
    (hamiltonianVectorField_comp_torusAction p (z := zt) (hact.symm ▸ hK)).trans
      (by rw [hact])
  have hlhs : ((((ContinuousLinearMap.id ℝ (ι → ℝ)).prodMap
      ((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).symm :
        (ι → ℝ) →L[ℝ] ((ι → ℝ) →L[ℝ] ℝ))).comp
      (((1 : ℝ →L[ℝ] ℝ).smulRight ν).prod (0 : ℝ →L[ℝ] ι → ℝ))) r :
      (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) = (r' • ν, 0) :=
    Prod.ext rfl (map_zero (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) ι).symm)
  have hrhs : (ContinuousLinearMap.toSpanSingleton ℝ
      ((symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (∀ i, AddCircle (p i))).hamiltonianVectorField (K ∘ torusAction p) zt) r :
      (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) = (r' • ν, 0) :=
    (congrArg (fun v : TangentSpace
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) zt ↦
      (ContinuousLinearMap.toSpanSingleton ℝ v r' : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))) hX_eq).trans
      (Prod.ext rfl (smul_zero r'))
  exact hlhs.trans hrhs.symm

end ActionAngle

end CotangentBundle

end TauCeti
