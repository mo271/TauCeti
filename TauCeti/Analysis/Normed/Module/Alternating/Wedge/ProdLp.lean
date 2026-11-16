/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.ProdLp
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
public import TauCeti.Topology.Algebra.Module.Alternating.Basic
import Mathlib.GroupTheory.Perm.Finite

/-!
# Block-triangular evaluation and external wedge products on `L^p` products

When a paired wedge `pairedWedge μ hμ φ ψ` is evaluated on a concatenated tuple `Fin.append u w`
and either `φ` vanishes whenever one of its arguments comes from `w`, or `ψ` vanishes whenever one
of its arguments comes from `u`, every shuffle outside `Perm (Fin k) × Perm (Fin l)` vanishes and
each of the `k! l!` block permutations contributes `μ (φ u) (ψ w)`. In particular, when `φ` is
pulled back along a continuous linear map killing every `w j`, the wedge evaluates to the paired
values of the factors.

For real-valued forms `φ` on `E` and `ψ` on `F` and any exponent `1 ≤ p ≤ ∞`, pulling back along
the projections `WithLp.fstL` and `WithLp.sndL` and wedging defines the external wedge product
`φ.externalWedge p ψ` on `WithLp p (E × F)`. On concatenated factor tuples `(u, 0)` followed by
`(0, w)` it evaluates to `φ u * ψ w`, and its operator norm satisfies the two-sided estimate
`‖φ‖ * ‖ψ‖ ≤ ‖φ.externalWedge p ψ‖ ≤ (k + l).choose k * ‖φ‖ * ‖ψ‖`.

## Main definitions

* `ContinuousAlternatingMap.externalWedge`: the external wedge `π₁* φ ∧ π₂* ψ` on
  `WithLp p (E × F)`.

## Main results

* `ContinuousAlternatingMap.pairedWedge_apply_append_of_left`,
  `ContinuousAlternatingMap.pairedWedge_apply_append_of_right`: block-triangular evaluation of
  `pairedWedge` on `Fin.append u w`.
* `ContinuousAlternatingMap.wedge_compContinuousLinearMap_apply_append_of_left`,
  `ContinuousAlternatingMap.wedge_compContinuousLinearMap_apply_append_of_right`: block-triangular
  evaluation of real wedges of pulled-back forms.
* `ContinuousAlternatingMap.externalWedge_apply_append_toLp`: exact evaluation of `externalWedge`
  on a concatenated product tuple.
* `ContinuousAlternatingMap.norm_mul_norm_le_norm_externalWedge`,
  `ContinuousAlternatingMap.norm_externalWedge_le`: two-sided operator-norm bounds for
  `externalWedge`, with equality in degree zero on either side.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14.
* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. 148 (1982), §II.7.
-/

public section

open scoped ENNReal

namespace ContinuousAlternatingMap

section Append

open Equiv

variable {E F₁ F₂ F₃ : Type*}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F₁] [Module ℝ F₁] [TopologicalSpace F₁]
  [AddCommGroup F₂] [Module ℝ F₂] [TopologicalSpace F₂]
  [AddCommGroup F₃] [Module ℝ F₃] [TopologicalSpace F₃]
  [IsTopologicalAddGroup F₃] [ContinuousConstSMul ℝ F₃]
  {k l : ℕ}

/-- A non-block permutation on `Fin k ⊕ Fin l` sends either some left index into the right block
or some right index into the left block, so the corresponding term of `pairedWedge` vanishes under
either block-triangular hypothesis. -/
private theorem pairedWedge_summand_eq_zero_of_not_mem_range
    (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂)
    (u : Fin k → E) (w : Fin l → E)
    (h : (∀ (y : Fin k → E) (i : Fin k) (j : Fin l), y i = w j → φ y = 0) ∨
      (∀ (z : Fin l → E) (j : Fin l) (i : Fin k), z j = u i → ψ z = 0))
    {τ : Perm (Fin k ⊕ Fin l)} (hτ : τ ∉ (Perm.sumCongrHom (Fin k) (Fin l)).range) :
    Perm.sign τ • μ (φ fun i ↦ Sum.elim u w (τ (Sum.inl i)))
      (ψ fun j ↦ Sum.elim u w (τ (Sum.inr j))) = 0 := by
  have hnot_inl : ¬Set.MapsTo τ (Set.range Sum.inl) (Set.range Sum.inl) :=
    mt Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hτ
  rcases h with hw | hu
  · simp only [Set.MapsTo, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
      not_forall] at hnot_inl
    obtain ⟨i, hi⟩ := hnot_inl
    rcases hti : τ (Sum.inl i) with a | j
    · exact absurd ⟨a, hti.symm⟩ hi
    · rw [hw (fun a ↦ Sum.elim u w (τ (Sum.inl a))) i j (by simp [hti])]
      simp
  · have hnot_inr : ¬Set.MapsTo τ (Set.range Sum.inr) (Set.range Sum.inr) :=
      mt (Perm.perm_mapsTo_inl_iff_mapsTo_inr τ).mpr hnot_inl
    simp only [Set.MapsTo, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
      not_forall] at hnot_inr
    obtain ⟨j, hj⟩ := hnot_inr
    rcases htj : τ (Sum.inr j) with i | b
    · rw [hu (fun b ↦ Sum.elim u w (τ (Sum.inr b))) j i (by simp [htj])]
      simp
    · exact absurd ⟨b, htj.symm⟩ hj

/-- Each block permutation `Perm.sumCongr τ₁ τ₂` contributes `μ (φ u) (ψ w)` to the Leibniz sum of
`pairedWedge`. -/
private theorem pairedWedge_summand_sumCongr
    (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂)
    (u : Fin k → E) (w : Fin l → E) (τ₁ : Perm (Fin k)) (τ₂ : Perm (Fin l)) :
    Perm.sign (Perm.sumCongr τ₁ τ₂) •
      μ (φ fun i ↦ Sum.elim u w (Perm.sumCongr τ₁ τ₂ (Sum.inl i)))
        (ψ fun j ↦ Sum.elim u w (Perm.sumCongr τ₁ τ₂ (Sum.inr j))) =
      μ (φ u) (ψ w) := by
  have hφ : (φ fun i ↦ u (τ₁ i)) = Perm.sign τ₁ • φ u :=
    φ.toAlternatingMap.map_perm u τ₁
  have hψ : (ψ fun j ↦ w (τ₂ j)) = Perm.sign τ₂ • ψ w :=
    ψ.toAlternatingMap.map_perm w τ₂
  simp only [Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr,
    Perm.sign_sumCongr, hφ, hψ]
  rcases Int.units_eq_one_or (Perm.sign τ₁) with h1 | h1 <;>
    rcases Int.units_eq_one_or (Perm.sign τ₂) with h2 | h2 <;>
    simp [h1, h2]

private theorem pairedWedge_apply_append_aux
    (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) (u : Fin k → E) (w : Fin l → E)
    (h : (∀ (y : Fin k → E) (i : Fin k) (j : Fin l), y i = w j → φ y = 0) ∨
      (∀ (z : Fin l → E) (j : Fin l) (i : Fin k), z j = u i → ψ z = 0)) :
    pairedWedge μ hμ φ ψ (Fin.append u w) = μ (φ u) (ψ w) := by
  classical
  rw [pairedWedge_apply]
  have hsum :
      (∑ σ : Perm (Fin (k + l)), Perm.sign σ •
        μ (φ fun i ↦ Fin.append u w (σ (Fin.castAdd l i)))
          (ψ fun j ↦ Fin.append u w (σ (Fin.natAdd k j)))) =
      ∑ τ : Perm (Fin k ⊕ Fin l), Perm.sign τ •
        μ (φ fun i ↦ Sum.elim u w (τ (Sum.inl i)))
          (ψ fun j ↦ Sum.elim u w (τ (Sum.inr j))) := by
    refine (Fintype.sum_equiv finSumFinEquiv.permCongr _ _ fun τ ↦ ?_).symm
    have hl (i : Fin k) :
        Fin.append u w (finSumFinEquiv.permCongr τ (Fin.castAdd l i)) =
          Sum.elim u w (τ (Sum.inl i)) := by
      rw [← finSumFinEquiv_apply_left, permCongr_apply, symm_apply_apply]
      rcases τ (Sum.inl i) with a | b <;> simp
    have hr (j : Fin l) :
        Fin.append u w (finSumFinEquiv.permCongr τ (Fin.natAdd k j)) =
          Sum.elim u w (τ (Sum.inr j)) := by
      rw [← finSumFinEquiv_apply_right, permCongr_apply, symm_apply_apply]
      rcases τ (Sum.inr j) with a | b <;> simp
    simp only [Perm.sign_permCongr, hl, hr]
  rw [hsum]
  let f : Perm (Fin k) × Perm (Fin l) → Perm (Fin k ⊕ Fin l) := fun p ↦ Perm.sumCongr p.1 p.2
  have hinj : Function.Injective f := by
    rintro ⟨σ₁, σ₂⟩ ⟨τ₁, τ₂⟩ heq
    have h12 := DFunLike.congr_fun heq
    exact Prod.ext (Equiv.ext fun i ↦ by simpa [f] using h12 (Sum.inl i))
      (Equiv.ext fun j ↦ by simpa [f] using h12 (Sum.inr j))
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f)) fun τ _ hτ ↦
    pairedWedge_summand_eq_zero_of_not_mem_range μ φ ψ u w h fun ⟨p, hp⟩ ↦
      hτ (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, hp⟩)]
  rw [Finset.sum_image fun _ _ _ _ hp ↦ hinj hp,
    Finset.sum_congr rfl fun p _ ↦ pairedWedge_summand_sumCongr μ φ ψ u w p.1 p.2,
    Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_perm,
    Fintype.card_perm, Fintype.card_fin, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
    Nat.cast_mul, smul_smul, inv_mul_cancel₀ (mul_ne_zero (Nat.cast_ne_zero.mpr k.factorial_ne_zero)
      (Nat.cast_ne_zero.mpr l.factorial_ne_zero)), one_smul]

/-- **Block-triangular evaluation of `pairedWedge` (left factor).** If `φ` vanishes on every tuple
sharing an entry with `w`, then `pairedWedge μ hμ φ ψ (Fin.append u w) = μ (φ u) (ψ w)`. -/
theorem pairedWedge_apply_append_of_left
    (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) (u : Fin k → E) (w : Fin l → E)
    (hw : ∀ (y : Fin k → E) (i : Fin k) (j : Fin l), y i = w j → φ y = 0) :
    pairedWedge μ hμ φ ψ (Fin.append u w) = μ (φ u) (ψ w) :=
  pairedWedge_apply_append_aux μ hμ φ ψ u w (Or.inl hw)

/-- **Block-triangular evaluation of `pairedWedge` (right factor).** If `ψ` vanishes on every tuple
sharing an entry with `u`, then `pairedWedge μ hμ φ ψ (Fin.append u w) = μ (φ u) (ψ w)`. -/
theorem pairedWedge_apply_append_of_right
    (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) (u : Fin k → E) (w : Fin l → E)
    (hu : ∀ (z : Fin l → E) (j : Fin l) (i : Fin k), z j = u i → ψ z = 0) :
    pairedWedge μ hμ φ ψ (Fin.append u w) = μ (φ u) (ψ w) :=
  pairedWedge_apply_append_aux μ hμ φ ψ u w (Or.inr hu)

/-- Pulling `φ` and `ψ` back along continuous linear maps `p₁` and `p₂` where `p₁` kills every
`w j` makes their `pairedWedge` evaluate on `Fin.append u w` to `μ (φ (p₁ ∘ u)) (ψ (p₂ ∘ w))`. -/
theorem pairedWedge_compContinuousLinearMap_apply_append_of_left
    {E₁ E₂ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (φ : E₁ [⋀^Fin k]→L[ℝ] F₁) (ψ : E₂ [⋀^Fin l]→L[ℝ] F₂)
    (p₁ : E →L[ℝ] E₁) (p₂ : E →L[ℝ] E₂) (u : Fin k → E) (w : Fin l → E)
    (hw : ∀ j, p₁ (w j) = 0) :
    pairedWedge μ hμ (φ.compContinuousLinearMap p₁) (ψ.compContinuousLinearMap p₂)
        (Fin.append u w) =
      μ (φ (p₁ ∘ u)) (ψ (p₂ ∘ w)) :=
  pairedWedge_apply_append_of_left μ hμ _ _ u w fun y i j hy ↦
    φ.toAlternatingMap.map_coord_zero i (by simp [hy, hw j])

/-- Pulling `φ` and `ψ` back along continuous linear maps `p₁` and `p₂` where `p₂` kills every
`u i` makes their `pairedWedge` evaluate on `Fin.append u w` to `μ (φ (p₁ ∘ u)) (ψ (p₂ ∘ w))`. -/
theorem pairedWedge_compContinuousLinearMap_apply_append_of_right
    {E₁ E₂ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (φ : E₁ [⋀^Fin k]→L[ℝ] F₁) (ψ : E₂ [⋀^Fin l]→L[ℝ] F₂)
    (p₁ : E →L[ℝ] E₁) (p₂ : E →L[ℝ] E₂) (u : Fin k → E) (w : Fin l → E)
    (hu : ∀ i, p₂ (u i) = 0) :
    pairedWedge μ hμ (φ.compContinuousLinearMap p₁) (ψ.compContinuousLinearMap p₂)
        (Fin.append u w) =
      μ (φ (p₁ ∘ u)) (ψ (p₂ ∘ w)) :=
  pairedWedge_apply_append_of_right μ hμ _ _ u w fun z j i hz ↦
    ψ.toAlternatingMap.map_coord_zero j (by simp [hz, hu i])

end Append

section WedgeAppend

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {k l : ℕ}

/-- Block-triangular evaluation of a real wedge product when the first factor vanishes on tuples
sharing an entry with `w`. -/
theorem wedge_apply_append_of_left (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : E [⋀^Fin l]→L[ℝ] ℝ)
    (u : Fin k → E) (w : Fin l → E)
    (hw : ∀ (y : Fin k → E) (i : Fin k) (j : Fin l), y i = w j → φ y = 0) :
    φ.wedge ψ (Fin.append u w) = φ u * ψ w := by
  simpa only [wedge_def, ContinuousLinearMap.mul_apply'] using
    pairedWedge_apply_append_of_left (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂ φ ψ u w hw

/-- Block-triangular evaluation of a real wedge product when the second factor vanishes on tuples
sharing an entry with `u`. -/
theorem wedge_apply_append_of_right (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : E [⋀^Fin l]→L[ℝ] ℝ)
    (u : Fin k → E) (w : Fin l → E)
    (hu : ∀ (z : Fin l → E) (j : Fin l) (i : Fin k), z j = u i → ψ z = 0) :
    φ.wedge ψ (Fin.append u w) = φ u * ψ w := by
  simpa only [wedge_def, ContinuousLinearMap.mul_apply'] using
    pairedWedge_apply_append_of_right (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂ φ ψ u w hu

/-- Block-triangular evaluation of `(p₁* φ) ∧ (p₂* ψ)` when `p₁` kills every `w j`. -/
theorem wedge_compContinuousLinearMap_apply_append_of_left
    {E₁ E₂ : Type*} [SeminormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [SeminormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    (φ : E₁ [⋀^Fin k]→L[ℝ] ℝ) (ψ : E₂ [⋀^Fin l]→L[ℝ] ℝ)
    (p₁ : E →L[ℝ] E₁) (p₂ : E →L[ℝ] E₂) (u : Fin k → E) (w : Fin l → E)
    (hw : ∀ j, p₁ (w j) = 0) :
    (φ.compContinuousLinearMap p₁).wedge (ψ.compContinuousLinearMap p₂) (Fin.append u w) =
      φ (p₁ ∘ u) * ψ (p₂ ∘ w) := by
  simpa only [wedge_def, ContinuousLinearMap.mul_apply'] using
    pairedWedge_compContinuousLinearMap_apply_append_of_left (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂ φ ψ p₁ p₂ u w hw

/-- Block-triangular evaluation of `(p₁* φ) ∧ (p₂* ψ)` when `p₂` kills every `u i`. -/
theorem wedge_compContinuousLinearMap_apply_append_of_right
    {E₁ E₂ : Type*} [SeminormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [SeminormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    (φ : E₁ [⋀^Fin k]→L[ℝ] ℝ) (ψ : E₂ [⋀^Fin l]→L[ℝ] ℝ)
    (p₁ : E →L[ℝ] E₁) (p₂ : E →L[ℝ] E₂) (u : Fin k → E) (w : Fin l → E)
    (hu : ∀ i, p₂ (u i) = 0) :
    (φ.compContinuousLinearMap p₁).wedge (ψ.compContinuousLinearMap p₂) (Fin.append u w) =
      φ (p₁ ∘ u) * ψ (p₂ ∘ w) := by
  simpa only [wedge_def, ContinuousLinearMap.mul_apply'] using
    pairedWedge_compContinuousLinearMap_apply_append_of_right (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂ φ ψ p₁ p₂ u w hu

end WedgeAppend

section ExternalWedge

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F] {k l : ℕ}

/-- The external wedge product `π₁* φ ∧ π₂* ψ` of real-valued forms `φ` on `E` and `ψ` on `F`,
as a `(k + l)`-form on the `L^p` product `WithLp p (E × F)`. For `p = 2` on real inner product
spaces this is the external product on the orthogonal direct sum `E ⊕ F`. -/
noncomputable def externalWedge (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    WithLp p (E × F) [⋀^Fin (k + l)]→L[ℝ] ℝ :=
  (φ.compContinuousLinearMap (WithLp.fstL p ℝ E F)).wedge
    (ψ.compContinuousLinearMap (WithLp.sndL p ℝ E F))

/-- Unfolding `externalWedge` as the wedge of the pullbacks along `WithLp.fstL` and
`WithLp.sndL`. -/
theorem externalWedge_def (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    φ.externalWedge p ψ =
      (φ.compContinuousLinearMap (WithLp.fstL p ℝ E F)).wedge
        (ψ.compContinuousLinearMap (WithLp.sndL p ℝ E F)) :=
  (rfl)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

@[simp]
theorem externalWedge_add_left (φ φ' : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    (φ + φ').externalWedge p ψ = φ.externalWedge p ψ + φ'.externalWedge p ψ := by
  have h : (φ + φ').compContinuousLinearMap (WithLp.fstL p ℝ E F) =
      φ.compContinuousLinearMap (WithLp.fstL p ℝ E F) +
        φ'.compContinuousLinearMap (WithLp.fstL p ℝ E F) := by ext; simp
  rw [externalWedge, h, wedge_add_left]
  rfl

@[simp]
theorem externalWedge_add_right (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ ψ' : F [⋀^Fin l]→L[ℝ] ℝ) :
    φ.externalWedge p (ψ + ψ') = φ.externalWedge p ψ + φ.externalWedge p ψ' := by
  have h : (ψ + ψ').compContinuousLinearMap (WithLp.sndL p ℝ E F) =
      ψ.compContinuousLinearMap (WithLp.sndL p ℝ E F) +
        ψ'.compContinuousLinearMap (WithLp.sndL p ℝ E F) := by ext; simp
  rw [externalWedge, h, wedge_add_right]
  rfl

@[simp]
theorem externalWedge_smul_left (c : ℝ) (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    (c • φ).externalWedge p ψ = c • φ.externalWedge p ψ := by
  have h : (c • φ).compContinuousLinearMap (WithLp.fstL p ℝ E F) =
      c • φ.compContinuousLinearMap (WithLp.fstL p ℝ E F) := by ext; simp
  rw [externalWedge, h, wedge_smul_left]
  rfl

@[simp]
theorem externalWedge_smul_right (c : ℝ) (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    φ.externalWedge p (c • ψ) = c • φ.externalWedge p ψ := by
  have h : (c • ψ).compContinuousLinearMap (WithLp.sndL p ℝ E F) =
      c • ψ.compContinuousLinearMap (WithLp.sndL p ℝ E F) := by ext; simp
  rw [externalWedge, h, wedge_smul_right]
  rfl

@[simp]
theorem externalWedge_zero_left (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    (0 : E [⋀^Fin k]→L[ℝ] ℝ).externalWedge p ψ = 0 := by
  rw [← zero_smul ℝ (0 : E [⋀^Fin k]→L[ℝ] ℝ), externalWedge_smul_left, zero_smul]

@[simp]
theorem externalWedge_zero_right (φ : E [⋀^Fin k]→L[ℝ] ℝ) :
    φ.externalWedge p (0 : F [⋀^Fin l]→L[ℝ] ℝ) = 0 := by
  rw [← zero_smul ℝ (0 : F [⋀^Fin l]→L[ℝ] ℝ), externalWedge_smul_right, zero_smul]

@[simp]
theorem externalWedge_neg_left (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    (-φ).externalWedge p ψ = -φ.externalWedge p ψ := by
  rw [← neg_one_smul ℝ φ, externalWedge_smul_left]
  exact neg_one_smul ℝ (φ.externalWedge p ψ)

@[simp]
theorem externalWedge_neg_right (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    φ.externalWedge p (-ψ) = -φ.externalWedge p ψ := by
  rw [← neg_one_smul ℝ ψ, externalWedge_smul_right]
  exact neg_one_smul ℝ (φ.externalWedge p ψ)

@[simp]
theorem externalWedge_sub_left (φ φ' : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    (φ - φ').externalWedge p ψ = φ.externalWedge p ψ - φ'.externalWedge p ψ := by
  simp [sub_eq_add_neg]

@[simp]
theorem externalWedge_sub_right (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ ψ' : F [⋀^Fin l]→L[ℝ] ℝ) :
    φ.externalWedge p (ψ - ψ') = φ.externalWedge p ψ - φ.externalWedge p ψ' := by
  simp [sub_eq_add_neg]

/-- An external wedge with a `0`-form on the left multiplies its scalar value by the pullback of
the right factor. -/
@[simp]
theorem externalWedge_apply_zero_left (φ : E [⋀^Fin 0]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ)
    (v : Fin (0 + l) → WithLp p (E × F)) :
    φ.externalWedge p ψ v = φ 0 * ψ (fun j ↦ (v (Fin.cast (Nat.zero_add l).symm j)).snd) := by
  rw [externalWedge, wedge_def, pairedWedge_apply_zero_left]
  rfl

/-- An external wedge with a `0`-form on the right multiplies the pullback of the left factor by
its scalar value. -/
@[simp]
theorem externalWedge_apply_zero_right (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin 0]→L[ℝ] ℝ)
    (v : Fin (k + 0) → WithLp p (E × F)) :
    φ.externalWedge p ψ v = φ (fun i ↦ (v i).fst) * ψ 0 := by
  rw [externalWedge, wedge_def, pairedWedge_apply_zero_right]
  rfl

/-- Pulling `φ.externalWedge p ψ` back along a block map `f ⊕ g` pulls each factor back along its
own block. -/
theorem externalWedge_comp_withLpProdMap {E' F' : Type*}
    [SeminormedAddCommGroup E'] [NormedSpace ℝ E']
    [SeminormedAddCommGroup F'] [NormedSpace ℝ F']
    (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ)
    (f : E' →L[ℝ] E) (g : F' →L[ℝ] F) :
    (φ.externalWedge p ψ).compContinuousLinearMap (f.withLpProdMap p g) =
      (φ.compContinuousLinearMap f).externalWedge p (ψ.compContinuousLinearMap g) := by
  have h1 : WithLp.fstL p ℝ E F ∘L f.withLpProdMap p g = f ∘L WithLp.fstL p ℝ E' F' := by ext; simp
  have h2 : WithLp.sndL p ℝ E F ∘L f.withLpProdMap p g = g ∘L WithLp.sndL p ℝ E' F' := by ext; simp
  rw [externalWedge, ← wedge_compContinuousLinearMap,
    compContinuousLinearMap_compContinuousLinearMap,
    compContinuousLinearMap_compContinuousLinearMap, h1, h2]
  rfl

/-- Graded commutativity of `externalWedge` under swapping the two factors of `WithLp p (E × F)`. -/
theorem externalWedge_swap_apply (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ)
    (v : Fin (k + l) → WithLp p (E × F)) :
    φ.externalWedge p ψ v = (-1 : ℝ) ^ (k * l) *
      ψ.externalWedge p φ
        (fun i ↦ WithLp.toLp p ((v (Fin.cast (Nat.add_comm l k) i)).snd,
          (v (Fin.cast (Nat.add_comm l k) i)).fst)) := by
  let swapL : WithLp p (F × E) →L[ℝ] WithLp p (E × F) :=
    (WithLp.prodContinuousLinearEquiv p ℝ E F).symm.toContinuousLinearMap ∘L
      (WithLp.sndL p ℝ F E).prod (WithLp.fstL p ℝ F E)
  have hcomp :
      ((ψ.compContinuousLinearMap (WithLp.sndL p ℝ E F)).wedge
        (φ.compContinuousLinearMap (WithLp.fstL p ℝ E F))).compContinuousLinearMap swapL =
      ψ.externalWedge p φ := by
    rw [← wedge_compContinuousLinearMap, compContinuousLinearMap_compContinuousLinearMap,
      compContinuousLinearMap_compContinuousLinearMap]
    rfl
  rw [externalWedge, wedge_comm, smul_eq_mul, ← hcomp]
  rfl

/-- When the last `l` vectors have zero first component, `φ.externalWedge p ψ` on `Fin.append u w`
factors as `φ (fst ∘ u) * ψ (snd ∘ w)`. -/
theorem externalWedge_apply_append_of_fst_eq_zero
    (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ)
    (u : Fin k → WithLp p (E × F)) (w : Fin l → WithLp p (E × F))
    (hw : ∀ j, (w j).fst = 0) :
    φ.externalWedge p ψ (Fin.append u w) =
      φ (fun i ↦ (u i).fst) * ψ (fun j ↦ (w j).snd) :=
  wedge_compContinuousLinearMap_apply_append_of_left φ ψ
    (WithLp.fstL p ℝ E F) (WithLp.sndL p ℝ E F) u w hw

/-- When the first `k` vectors have zero second component, `φ.externalWedge p ψ` on
`Fin.append u w` factors as `φ (fst ∘ u) * ψ (snd ∘ w)`. -/
theorem externalWedge_apply_append_of_snd_eq_zero
    (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ)
    (u : Fin k → WithLp p (E × F)) (w : Fin l → WithLp p (E × F))
    (hu : ∀ i, (u i).snd = 0) :
    φ.externalWedge p ψ (Fin.append u w) =
      φ (fun i ↦ (u i).fst) * ψ (fun j ↦ (w j).snd) :=
  wedge_compContinuousLinearMap_apply_append_of_right φ ψ
    (WithLp.fstL p ℝ E F) (WithLp.sndL p ℝ E F) u w hu

/-- **Exact evaluation of an external wedge on a concatenated product frame** (first factor first):
`(φ.externalWedge p ψ) ((u₁, 0), …, (uₖ, 0), (0, w₁), …, (0, wₗ)) = φ u * ψ w`. -/
@[simp]
theorem externalWedge_apply_append_toLp (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ)
    (u : Fin k → E) (w : Fin l → F) :
    φ.externalWedge p ψ
        (Fin.append (fun i ↦ WithLp.toLp p (u i, 0)) (fun j ↦ WithLp.toLp p (0, w j))) =
      φ u * ψ w :=
  externalWedge_apply_append_of_fst_eq_zero φ ψ _ _ fun _ ↦ rfl

/-- Evaluating `φ.externalWedge p ψ` on a concatenated product frame with the second factor placed
first introduces the graded sign `(-1) ^ (k * l)`. -/
theorem externalWedge_apply_append_toLp_swap (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ)
    (u : Fin k → E) (w : Fin l → F) :
    φ.externalWedge p ψ
        (Fin.append (fun j ↦ WithLp.toLp p (0, w j)) (fun i ↦ WithLp.toLp p (u i, 0)) ∘
          Fin.cast (Nat.add_comm k l)) =
      (-1 : ℝ) ^ (k * l) * (φ u * ψ w) := by
  rw [externalWedge_swap_apply]
  have harg :
      (fun i : Fin (l + k) ↦ WithLp.toLp p
        (((Fin.append (fun j ↦ WithLp.toLp p ((0 : E), w j))
            (fun i ↦ WithLp.toLp p (u i, (0 : F))) ∘
          Fin.cast (Nat.add_comm k l)) (Fin.cast (Nat.add_comm l k) i)).snd,
          ((Fin.append (fun j ↦ WithLp.toLp p ((0 : E), w j))
            (fun i ↦ WithLp.toLp p (u i, (0 : F))) ∘
          Fin.cast (Nat.add_comm k l)) (Fin.cast (Nat.add_comm l k) i)).fst)) =
      Fin.append (fun j ↦ WithLp.toLp p (w j, 0)) (fun i ↦ WithLp.toLp p (0, u i)) := by
    ext m
    obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective m <;> simp
  rw [harg, externalWedge_apply_append_toLp, mul_comm (ψ w) (φ u)]

/-- **Binomial operator-norm bound for external wedges**:
`‖φ.externalWedge p ψ‖ ≤ (k + l).choose k * ‖φ‖ * ‖ψ‖`. -/
theorem norm_externalWedge_le (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    ‖φ.externalWedge p ψ‖ ≤ (k + l).choose k * ‖φ‖ * ‖ψ‖ := by
  have hfst : ‖φ.compContinuousLinearMap (WithLp.fstL p ℝ E F)‖ ≤ ‖φ‖ := by
    refine (φ.norm_compContinuousLinearMap_le _).trans ?_
    rw [Fintype.card_fin]
    exact mul_le_of_le_one_right (norm_nonneg φ) (pow_le_one₀ (norm_nonneg _)
      (WithLp.norm_fstL_le_one p ℝ E F))
  have hsnd : ‖ψ.compContinuousLinearMap (WithLp.sndL p ℝ E F)‖ ≤ ‖ψ‖ := by
    refine (ψ.norm_compContinuousLinearMap_le _).trans ?_
    rw [Fintype.card_fin]
    exact mul_le_of_le_one_right (norm_nonneg ψ) (pow_le_one₀ (norm_nonneg _)
      (WithLp.norm_sndL_le_one p ℝ E F))
  exact (norm_wedge_le _ _).trans (by gcongr)

/-- **Operator-norm lower bound for external wedges**: testing on concatenated factor tuples gives
`‖φ‖ * ‖ψ‖ ≤ ‖φ.externalWedge p ψ‖` for every `1 ≤ p ≤ ∞`. -/
theorem norm_mul_norm_le_norm_externalWedge (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    ‖φ‖ * ‖ψ‖ ≤ ‖φ.externalWedge p ψ‖ := by
  have hval (u : Fin k → E) (w : Fin l → F) :
      ‖φ u‖ * ‖ψ w‖ ≤ ‖φ.externalWedge p ψ‖ * (∏ i, ‖u i‖) * (∏ j, ‖w j‖) := by
    have h := (φ.externalWedge p ψ).le_opNorm
      (Fin.append (fun i ↦ WithLp.toLp p (u i, 0)) (fun j ↦ WithLp.toLp p (0, w j)))
    rw [externalWedge_apply_append_toLp, norm_mul, Fin.prod_univ_add] at h
    simpa [mul_assoc] using h
  have hu (u : Fin k → E) : ‖φ u‖ * ‖ψ‖ ≤ ‖φ.externalWedge p ψ‖ * ∏ i, ‖u i‖ := by
    rcases eq_or_lt_of_le (norm_nonneg (φ u)) with h0 | hpos
    · rw [← h0, zero_mul]
      positivity
    · rw [mul_comm ‖φ u‖, ← le_div_iff₀ hpos]
      refine ψ.opNorm_le_bound (by positivity) fun w ↦ ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hpos, mul_comm _ ‖φ u‖]
      exact hval u w
  rcases eq_or_lt_of_le (norm_nonneg ψ) with h0 | hpos
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  · rw [← le_div_iff₀ hpos]
    refine φ.opNorm_le_bound (by positivity) fun u ↦ ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    exact hu u

/-- An external wedge on a normed `L^p` product vanishes if and only if one of its factors
vanishes. -/
@[simp]
theorem externalWedge_eq_zero_iff {φ : E [⋀^Fin k]→L[ℝ] ℝ} {ψ : F [⋀^Fin l]→L[ℝ] ℝ} :
    φ.externalWedge p ψ = 0 ↔ φ = 0 ∨ ψ = 0 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hmul : ‖φ‖ * ‖ψ‖ ≤ 0 := by
      simpa [h] using norm_mul_norm_le_norm_externalWedge (p := p) φ ψ
    simpa using mul_eq_zero.mp (le_antisymm hmul (by positivity))
  · rintro (rfl | rfl) <;> simp

/-- When the left factor has degree zero, `‖φ.externalWedge p ψ‖ = ‖φ‖ * ‖ψ‖`. -/
@[simp]
theorem norm_externalWedge_zero_left (φ : E [⋀^Fin 0]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    ‖φ.externalWedge p ψ‖ = ‖φ‖ * ‖ψ‖ :=
  le_antisymm (by simpa using norm_externalWedge_le (p := p) φ ψ)
    (norm_mul_norm_le_norm_externalWedge φ ψ)

/-- When the right factor has degree zero, `‖φ.externalWedge p ψ‖ = ‖φ‖ * ‖ψ‖`. -/
@[simp]
theorem norm_externalWedge_zero_right (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin 0]→L[ℝ] ℝ) :
    ‖φ.externalWedge p ψ‖ = ‖φ‖ * ‖ψ‖ :=
  le_antisymm (by simpa using norm_externalWedge_le (p := p) φ ψ)
    (norm_mul_norm_le_norm_externalWedge φ ψ)

end ExternalWedge

end ContinuousAlternatingMap
