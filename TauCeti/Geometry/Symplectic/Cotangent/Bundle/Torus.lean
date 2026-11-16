/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Torus
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Torus
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Graph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic

/-!
# Lagrangian sections and covering coordinates of the cotangent bundle of a torus

For a finite family of positive periods `p i`, let `Tⁿ = ∀ i, AddCircle (p i)` be the torus with
coordinate time forms `dt_i` (`TauCeti.torusTimeForm p i`), and let `α_c = ∑ j, c j • dt_j` be the
closed one-form with constant coefficients `c : ι → ℝ`. This file records the basic examples of
Lagrangian sections of the cotangent bundle `T*Tⁿ` with its canonical symplectic form `ω = -dλ`,
together with its universal covering parametrization `TauCeti.CotangentBundle.torusCover`.

* The graph of `α_c` is a Lagrangian map for every `c`, since `α_c` is closed
  (`TauCeti.CotangentBundle.isLagrangianMap_section_sum_smul_torusTimeForm`).
* It is an exact Lagrangian map, for the primitive `λ` of `ω` and some primitive on the torus,
  exactly when `c = 0`, that is when it is the zero section
  (`TauCeti.CotangentBundle.exists_isExactLagrangianMap_section_sum_smul_torusTimeForm_iff`). This
  is because `α_c` integrates to `c i * p i` around the `i`-th coordinate circle.
* For `c ≠ 0` the graph of `α_c` meets the zero section nowhere
  (`TauCeti.CotangentBundle.section_sum_smul_torusTimeForm_eq_zeroSection_iff`): the form `α_c`
  vanishes at no point.
* In particular the graph of a single angle form `dt_i` is a Lagrangian section of `T*Tⁿ` that is
  not exact (`TauCeti.CotangentBundle.isLagrangianMap_section_torusTimeForm`,
  `TauCeti.CotangentBundle.not_exists_isExactLagrangianMap_section_torusTimeForm`), and by the last
  item it is disjoint from the zero section.
* The covering map `(ι → ℝ) × (ι → ℝ) → T*Tⁿ`, `(t, c) ↦ ([t], ∑ i, c i • dt_i)`
  (`TauCeti.CotangentBundle.torusCover`), is a surjective smooth local diffeomorphism whose fibres
  are the period-lattice cosets (`TauCeti.CotangentBundle.torusCover_eq_iff`), pulling `λ` back to
  `∑ i, c i dt_i` (`TauCeti.CotangentBundle.mpullback_torusDiffeomorph_symm_liouvilleForm_apply`,
  `TauCeti.CotangentBundle.mpullback_torusCover_liouvilleForm_apply`) and `ω` back to the standard
  symplectic form `a ⬝ᵥ b' - a' ⬝ᵥ b` (`TauCeti.CotangentBundle.eval₂_symplecticForm_torusCover`).

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 3 and 18.4.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable {ι : Type*} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)]

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

/-! ### Covering coordinates and canonical forms -/

/-- The covering parametrization `(ι → ℝ) × (ι → ℝ) → T*Tⁿ`, sending `(t, c)` to the covector
`∑ i, c i • dt_i` over `[t] ∈ ∀ i, AddCircle (p i)`. -/
def torusCover (z : (ι → ℝ) × (ι → ℝ)) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) :=
  (torusDiffeomorph p).symm (fun i ↦ (z.1 i : AddCircle (p i)), z.2)

/-- `torusCover p z` lies over `fun i ↦ (z.1 i : AddCircle (p i))`. -/
@[simp]
theorem proj_torusCover (z : (ι → ℝ) × (ι → ℝ)) :
    (torusCover p z).proj = fun i ↦ (z.1 i : AddCircle (p i)) :=
  proj_torusDiffeomorph_symm p _

/-- The covector of `torusCover p z` pairs with `v : ι → ℝ` as `∑ i, z.2 i * v i`. -/
@[simp]
theorem torusCover_snd_apply (z : (ι → ℝ) × (ι → ℝ))
    (v : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (torusCover p z).proj) :
    (torusCover p z).2 v = ∑ i, z.2 i * v i :=
  torusDiffeomorph_symm_snd_apply p (fun i ↦ (z.1 i : AddCircle (p i)), z.2) v

/-- `torusDiffeomorph p` sends `torusCover p z` to `([z.1], z.2)`. -/
@[simp]
theorem torusDiffeomorph_torusCover (z : (ι → ℝ) × (ι → ℝ)) :
    torusDiffeomorph p (torusCover p z) = (fun i ↦ (z.1 i : AddCircle (p i)), z.2) :=
  (torusDiffeomorph p).apply_symm_apply _

/-- The covering parametrization `(ι → ℝ) × (ι → ℝ) → T*Tⁿ` is surjective. -/
theorem torusCover_surjective : Function.Surjective (torusCover p) := by
  have h : torusCover p =
      ⇑(torusDiffeomorph p).symm ∘ Prod.map (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p i))) id :=
    rfl
  rw [h]
  exact (torusDiffeomorph p).symm.surjective.comp
    ((AddCircle.piMap_coe_surjective p).prodMap Function.surjective_id)

/-- Two pairs `(t, c)` and `(t', c')` have the same image under `torusCover p` if and only if
`c' = c` and each `t' i` differs from `t i` by an integer multiple of `p i`. -/
theorem torusCover_eq_iff {t t' c c' : ι → ℝ} :
    torusCover p (t, c) = torusCover p (t', c') ↔
      c' = c ∧ ∃ m : ι → ℤ, ∀ i, t' i = t i + m i • p i := by
  rw [torusCover, torusCover, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq,
    AddCircle.piMap_coe_eq_iff, and_comm, @eq_comm _ c c']

/-- `torusCover p` is smooth. -/
theorem contMDiff_torusCover :
    ContMDiff 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ (torusCover p) :=
  (torusDiffeomorph p).symm.contMDiff.comp
    (((AddCircle.contMDiff_piMap_coe p ∞).comp contDiff_fst.contMDiff).prodMk
      contDiff_snd.contMDiff)

/-- `torusCover p` is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_torusCover :
    IsLocalDiffeomorph 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ (torusCover p) := by
  have h : torusCover p =
      ⇑(torusDiffeomorph p).symm ∘ Prod.map (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p i))) id :=
    rfl
  rw [h, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact fun z ↦ (IsLocalDiffeomorph.prodMap (AddCircle.isLocalDiffeomorph_piMap_coe p ∞)
    (Diffeomorph.refl 𝓘(ℝ, ι → ℝ) (ι → ℝ) ∞).isLocalDiffeomorph z).comp
    (hg := (torusDiffeomorph p).symm.isLocalDiffeomorph _)

/-- Pulling the Liouville form of `T*Tⁿ` back along `(torusDiffeomorph p).symm` gives
`∑ i, q.2 i * (v 0).1 i`. -/
theorem mpullback_torusDiffeomorph_symm_liouvilleForm_apply
    (q : (∀ i, AddCircle (p i)) × (ι → ℝ))
    (v : Fin 1 → TangentSpace ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ)) q) :
    (SmoothForm.mpullback (torusDiffeomorph p).symm (torusDiffeomorph p).symm.contMDiff
        (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))).1 q v =
      ∑ i, q.2 i * (v 0).1 i := by
  rw [SmoothForm.coe_mpullback, mpullback_liouvilleForm_apply_of_proj_comp_eq (g := Prod.fst)
    (fun r ↦ proj_torusDiffeomorph_symm p r)
    (((torusDiffeomorph p).symm.contMDiff q).mdifferentiableAt (by simp)) v,
    mfderiv_fst, torusDiffeomorph_symm_snd_apply]
  rfl

/-- Pulling the Liouville form of `T*Tⁿ` back along `torusCover p` gives the canonical linear
one-form `z, v ↦ ∑ i, z.2 i * (v 0).1 i` on `(ι → ℝ) × (ι → ℝ)`. -/
theorem mpullback_torusCover_liouvilleForm_apply (z : (ι → ℝ) × (ι → ℝ))
    (v : Fin 1 → TangentSpace 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) z) :
    (SmoothForm.mpullback (torusCover p) (contMDiff_torusCover p)
        (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))).1 z v =
      ∑ i, z.2 i * (v 0).1 i := by
  let w : (ι → ℝ) × (ι → ℝ) := v 0
  have hdg : mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun q : (ι → ℝ) × (ι → ℝ) ↦ fun i ↦ (q.1 i : AddCircle (p i))) z (v 0) = w.1 :=
    DFunLike.congr_fun
      ((AddCircle.hasMFDerivAt_piMap_coe p z.1).comp z
        (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).hasFDerivAt.hasMFDerivAt).mfderiv (v 0)
  rw [SmoothForm.coe_mpullback]
  refine (mpullback_liouvilleForm_apply_of_proj_comp_eq
      (g := fun q : (ι → ℝ) × (ι → ℝ) ↦ fun i ↦ (q.1 i : AddCircle (p i)))
      (fun q ↦ proj_torusCover p q)
      (((contMDiff_torusCover p) z).mdifferentiableAt (by simp)) v).trans ?_
  exact (congrArg (fun u : ι → ℝ ↦ (torusCover p z).2 u) hdg).trans
    (torusCover_snd_apply p z w.1)

/-- On `(ι → ℝ) × (ι → ℝ)`, the exterior derivative of the Liouville form pulled back along
`torusCover p` evaluates on `![(a, b), (a', b')]` to `-(a ⬝ᵥ b' - a' ⬝ᵥ b)`. -/
private theorem extDeriv_mpullback_torusCover_liouvilleForm_apply (t c a b a' b' : ι → ℝ) :
    extDeriv ((SmoothForm.mpullback (torusCover p) (contMDiff_torusCover p)
      (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))).1 :
        ((ι → ℝ) × (ι → ℝ)) → (((ι → ℝ) × (ι → ℝ)) [⋀^Fin 1]→L[ℝ] ℝ))
      (t, c) ![(a, b), (a', b')] = -(a ⬝ᵥ b' - a' ⬝ᵥ b) := by
  let Λ : ((ι → ℝ) × (ι → ℝ)) →L[ℝ] (((ι → ℝ) × (ι → ℝ)) [⋀^Fin 1]→L[ℝ] ℝ) :=
    ∑ i, ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).comp
      (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))).smulRight
      (ContinuousAlternatingMap.ofSubsingleton ℝ ((ι → ℝ) × (ι → ℝ)) ℝ 0
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).comp
          (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))))
  have hΛ_apply (z : (ι → ℝ) × (ι → ℝ)) (v : Fin 1 → (ι → ℝ) × (ι → ℝ)) :
      Λ z v = ∑ i, z.2 i * (v 0).1 i := by
    simp [Λ, ContinuousLinearMap.smulRight_apply]
  have hΛ_fderiv (v : Fin 1 → (ι → ℝ) × (ι → ℝ)) (q : (ι → ℝ) × (ι → ℝ)) :
      fderiv ℝ (fun x ↦ Λ x v) (t, c) q = ∑ i, q.2 i * (v 0).1 i := by
    let L : ((ι → ℝ) × (ι → ℝ)) →L[ℝ] ℝ :=
      ∑ i, (v 0).1 i • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).comp
        (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)))
    have hL : (fun x ↦ Λ x v) = ⇑L := by
      funext x
      simp [hΛ_apply, L, mul_comm]
    rw [hL, L.fderiv]
    simp [L, mul_comm]
  have hα : ((SmoothForm.mpullback (torusCover p) (contMDiff_torusCover p)
      (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))).1 :
        ((ι → ℝ) × (ι → ℝ)) → (((ι → ℝ) × (ι → ℝ)) [⋀^Fin 1]→L[ℝ] ℝ)) = ⇑Λ := by
    funext z
    ext v
    exact (mpullback_torusCover_liouvilleForm_apply p z v).trans (hΛ_apply z v).symm
  rw [hα, extDeriv_apply Λ.differentiableAt, Fin.sum_univ_two]
  simp only [Fin.isValue, Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [hΛ_fderiv _ (a, b), hΛ_fderiv _ (a', b')]
  simp only [Fin.removeNth, Fin.succAbove, Fin.zero_lt_one, ↓reduceIte, Fin.isValue,
    Fin.succ_zero_eq_one, lt_self_iff_false, Fin.castSucc_zero, Matrix.cons_val_one,
    Matrix.cons_val_zero, dotProduct, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **Canonical symplectic form in covering coordinates.** Pulling the canonical symplectic form
`ω = -dλ` of `T*Tⁿ` back along `torusCover p : (ι → ℝ) × (ι → ℝ) → T*Tⁿ` gives the standard
symplectic form `((a, b), (a', b')) ↦ a ⬝ᵥ b' - a' ⬝ᵥ b`, that is `∑ i, dt_i ∧ dc_i`. -/
theorem eval₂_symplecticForm_torusCover (t c a b a' b' : ι → ℝ) :
    SmoothBundleForm.eval₂
      (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))
      (torusCover p (t, c))
      (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (torusCover p) (t, c) (a, b))
      (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (torusCover p) (t, c) (a', b')) =
      a ⬝ᵥ b' - a' ⬝ᵥ b := by
  have hω : SmoothForm.mpullback (torusCover p) (contMDiff_torusCover p)
      (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) =
      -mextDerivₗ 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) 1
        (SmoothForm.mpullback (torusCover p) (contMDiff_torusCover p)
          (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))) := by
    rw [symplecticForm_eq_neg_mextDerivₗ, map_neg, SmoothForm.mextDerivₗ_mpullback]
  let u : TangentSpace 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (t, c) := (a, b)
  let u' : TangentSpace 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (t, c) := (a', b')
  refine (SmoothForm.eval₂_mpullback (torusCover p) (contMDiff_torusCover p)
    (symplecticForm _ _) (t, c) u u').symm.trans ?_
  rw [hω, SmoothBundleForm.eval₂_apply, NegMemClass.coe_neg, mextDerivₗ_apply,
    Pi.neg_apply, ContinuousAlternatingMap.neg_apply]
  refine (congrArg Neg.neg
    (congrArg (fun A : ((ι → ℝ) × (ι → ℝ)) [⋀^Fin 2]→L[ℝ] ℝ ↦ A ![(a, b), (a', b')])
      (mextDeriv_eq_extDeriv (F := ℝ) (k := 1) _ (t, c)))).trans ?_
  rw [extDeriv_mpullback_torusCover_liouvilleForm_apply, neg_neg]

end CotangentBundle

end TauCeti
