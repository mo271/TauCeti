/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.CalibratedFrame
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.ProdLp

/-!
# Calibrated frames and comass of external wedge products

On the `L²` orthogonal direct sum `WithLp 2 (E × F)` of two inner product spaces, concatenating an
orthonormal `k`-frame in `E × {0}` with an orthonormal `l`-frame in `{0} × F` produces an
orthonormal `(k + l)`-frame, and `φ.externalWedge 2 ψ` evaluates on it to `φ u * ψ w`. A product of
calibrated frames of `φ` and `ψ` is therefore a calibrated frame of `φ.externalWedge 2 ψ`; when
`‖φ‖ ≤ 1` and `‖ψ‖ ≤ 1`, a concatenated factor frame is calibrated by `φ.externalWedge 2 ψ` if and
only if either `(u, w)` is calibrated by `(φ, ψ)` or `(u, w)` is calibrated by `(-φ, -ψ)`. For
general higher-degree forms `φ` and `ψ`, the bounds `‖φ‖ ≤ 1` and `‖ψ‖ ≤ 1` do not force
`‖φ.externalWedge 2 ψ‖ ≤ 1` (Züst, 2025), so comass `1` of a general external wedge requires an
explicit upper bound `‖φ.externalWedge 2 ψ‖ ≤ 1`.

When one factor is a simple `k`-form `v ↦ ⟪u₁ ∧ ⋯ ∧ uₖ, v₁ ∧ ⋯ ∧ vₖ⟫` (and in particular when one
factor is the oriented volume form `o.volumeFormL`), no extra comass bound is needed: any
orthonormal `(k + l)`-frame in `WithLp 2 (E × F)` can be rotated within its own span by `SO(k + l)`
so that its last `l` vectors project orthogonally to `0` in `span(u)`, collapsing the Leibniz sum
of `externalWedge` to a single product term. This yields the exact comass formula
`‖(alternatingFormEquiv E k (ιMulti ℝ k u)).externalWedge 2 ψ‖ = ‖ιMulti ℝ k u‖ * ‖ψ‖` and
**Harvey–Lawson Proposition II.7.10**: for a unit simple `k`-form `φ` and any `l`-form `ψ` with
`‖ψ‖ ≤ 1` (excluding only the degenerate `0`-form sign flip `k > 0`, `l = 0`, `ψ 0 = -1`), the
calibrated frames of `φ.externalWedge 2 ψ` are precisely the orthonormal frames sharing their
oriented `(k + l)`-plane with a product frame `(e₁, 0), …, (eₖ, 0), (0, w₁), …, (0, wₗ)` where `w`
is calibrated by `ψ`.

## Main results

* `WithLp.orthonormal_sumElim_toLp_iff`, `WithLp.orthonormal_append_toLp_iff`: a direct-sum or
  concatenated factor family in `WithLp 2 (E × F)` is orthonormal iff both factor families are.
* `ContinuousAlternatingMap.IsCalibratedFrame.externalWedge_append_toLp`,
  `ContinuousAlternatingMap.isCalibratedFrame_externalWedge_append_toLp_iff`: calibration of
  concatenated factor frames by `φ.externalWedge 2 ψ`.
* `ContinuousAlternatingMap.norm_externalWedge_alternatingFormEquiv_ιMulti_left`,
  `ContinuousAlternatingMap.norm_externalWedge_alternatingFormEquiv_ιMulti_right`,
  `Orientation.norm_externalWedge_volumeFormL_left`,
  `Orientation.norm_externalWedge_volumeFormL_right`: exact comass of an external wedge when one
  factor is a simple form or an oriented volume form.
* `ContinuousAlternatingMap.isCalibratedFrame_externalWedge_alternatingFormEquiv_ιMulti_iff`,
  `Orientation.isCalibratedFrame_externalWedge_volumeFormL_iff`: Harvey–Lawson Proposition II.7.10
  characterizing the calibrated frames of `φ.externalWedge 2 ψ` when `φ` is a unit simple `k`-form
  or an oriented volume form.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. 148 (1982), §II.7,
  Proposition 7.10.
* R. Züst, *Products of calibrations*, Calc. Var. Partial Differential Equations (2025).
-/

public section

noncomputable section

open Module exteriorPower
open scoped ENNReal RealInnerProductSpace Matrix

/-! ### Orthonormal product frames and exterior products on `WithLp` -/

namespace WithLp

section OrthonormalProd

open scoped InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Combining families in `E × {0}` and `{0} × F` via `Sum.elim` yields an orthonormal family in
`WithLp 2 (E × F)` if and only if each factor family is orthonormal. -/
@[simp]
theorem orthonormal_sumElim_toLp_iff {ι₁ ι₂ : Type*} (u : ι₁ → E) (w : ι₂ → F) :
    Orthonormal 𝕜
        (Sum.elim (fun i ↦ WithLp.toLp 2 (u i, (0 : F)))
          (fun j ↦ WithLp.toLp 2 ((0 : E), w j))) ↔
      Orthonormal 𝕜 u ∧ Orthonormal 𝕜 w := by
  refine ⟨fun ⟨hn, hp⟩ ↦ ⟨⟨fun i ↦ ?_, fun i₁ i₂ hne ↦ ?_⟩, ⟨fun j ↦ ?_, fun j₁ j₂ hne ↦ ?_⟩⟩,
    fun ⟨⟨hnu, hpu⟩, ⟨hnw, hpw⟩⟩ ↦ ⟨?_, ?_⟩⟩
  · simpa using hn (Sum.inl i)
  · simpa using hp (Sum.inl_injective.ne hne)
  · simpa using hn (Sum.inr j)
  · simpa using hp (Sum.inr_injective.ne hne)
  · rintro (i | j)
    · simpa using hnu i
    · simpa using hnw j
  · rintro (i₁ | j₁) (i₂ | j₂) hne
    · simpa using hpu fun h ↦ hne (congrArg Sum.inl h)
    · simp
    · simp
    · simpa using hpw fun h ↦ hne (congrArg Sum.inr h)

/-- Concatenating `u : Fin k → E` in the first factor and `w : Fin l → F` in the second factor
yields an orthonormal `(k + l)`-frame in `WithLp 2 (E × F)` if and only if both `u` and `w` are
orthonormal. -/
@[simp]
theorem orthonormal_append_toLp_iff {k l : ℕ} (u : Fin k → E) (w : Fin l → F) :
    Orthonormal 𝕜
        (Fin.append (fun i ↦ WithLp.toLp 2 (u i, (0 : F)))
          (fun j ↦ WithLp.toLp 2 ((0 : E), w j))) ↔
      Orthonormal 𝕜 u ∧ Orthonormal 𝕜 w := by
  have hcomp :
      Fin.append (fun i ↦ WithLp.toLp 2 (u i, (0 : F))) (fun j ↦ WithLp.toLp 2 ((0 : E), w j)) =
        Sum.elim (fun i ↦ WithLp.toLp 2 (u i, (0 : F))) (fun j ↦ WithLp.toLp 2 ((0 : E), w j)) ∘
          finSumFinEquiv.symm := by
    ext m
    obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective m <;> simp
  rw [hcomp, ← orthonormal_sumElim_toLp_iff (𝕜 := 𝕜) u w]
  exact ⟨fun h ↦ by simpa [Function.comp_def] using h.comp finSumFinEquiv finSumFinEquiv.injective,
    fun h ↦ h.comp finSumFinEquiv.symm finSumFinEquiv.symm.injective⟩

end OrthonormalProd

end WithLp

namespace exteriorPower

section AppendToLp

variable {R E F : Type*} [CommRing R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  {p : ℝ≥0∞} {k l : ℕ}

private theorem coe_ιMulti_append_toLp (u : Fin k → E) (w : Fin l → F) :
    (ιMulti R (k + l)
        (Fin.append (fun i ↦ WithLp.toLp p (u i, (0 : F)))
          (fun j ↦ WithLp.toLp p ((0 : E), w j))) :
      ExteriorAlgebra R (WithLp p (E × F))) =
      ExteriorAlgebra.map
          ((WithLp.linearEquiv p R (E × F)).symm.toLinearMap ∘ₗ LinearMap.inl R E F)
          (ιMulti R k u) *
        ExteriorAlgebra.map
          ((WithLp.linearEquiv p R (E × F)).symm.toLinearMap ∘ₗ LinearMap.inr R E F)
          (ιMulti R l w) := by
  simp only [ιMulti_apply_coe, ← ExteriorAlgebra.ιMulti_mul_ιMulti,
    ExteriorAlgebra.map_apply_ιMulti]
  rfl

/-- The exterior product of a concatenated factor tuple `(u, 0)` followed by `(0, w)` depends only
on the exterior products `ιMulti R k u` and `ιMulti R l w`. -/
theorem ιMulti_append_toLp_congr {u u' : Fin k → E} {w w' : Fin l → F}
    (hu : ιMulti R k u = ιMulti R k u') (hw : ιMulti R l w = ιMulti R l w') :
    ιMulti R (k + l)
        (Fin.append (fun i ↦ WithLp.toLp p (u i, (0 : F)))
          (fun j ↦ WithLp.toLp p ((0 : E), w j))) =
      ιMulti R (k + l)
        (Fin.append (fun i ↦ WithLp.toLp p (u' i, (0 : F)))
          (fun j ↦ WithLp.toLp p ((0 : E), w' j))) := by
  apply Subtype.ext
  rw [coe_ιMulti_append_toLp, coe_ιMulti_append_toLp, hu, hw]

/-- Simultaneously reversing the orientations of both factors preserves the exterior product of the
concatenated factor tuple in `WithLp p (E × F)`. -/
theorem ιMulti_append_toLp_of_eq_neg {u u' : Fin k → E} {w w' : Fin l → F}
    (hu : ιMulti R k u = -ιMulti R k u') (hw : ιMulti R l w = -ιMulti R l w') :
    ιMulti R (k + l)
        (Fin.append (fun i ↦ WithLp.toLp p (u i, (0 : F)))
          (fun j ↦ WithLp.toLp p ((0 : E), w j))) =
      ιMulti R (k + l)
        (Fin.append (fun i ↦ WithLp.toLp p (u' i, (0 : F)))
          (fun j ↦ WithLp.toLp p ((0 : E), w' j))) := by
  apply Subtype.ext
  rw [coe_ιMulti_append_toLp, coe_ιMulti_append_toLp, hu, hw]
  simp only [Submodule.coe_neg, map_neg, neg_mul_neg]

end AppendToLp

end exteriorPower

/-! ### Calibrated frames of general external wedges -/

namespace ContinuousAlternatingMap

section GeneralFactors

private theorem eq_one_of_prod_ge_one {ι : Type*} [Fintype ι] {f : ι → ℝ}
    (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) (hprod : 1 ≤ ∏ i, f i) (i : ι) :
    f i = 1 := by
  classical
  by_contra hne
  have hlt : f i < 1 := lt_of_le_of_ne (hf1 i) hne
  have hrest : ∏ j ∈ Finset.univ.erase i, f j ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ ↦ hf0 j) fun j _ ↦ hf1 j
  have hmul : ∏ j, f j < 1 := by
    rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
    nlinarith [hf0 i, Finset.prod_nonneg fun j (_ : j ∈ Finset.univ.erase i) ↦ hf0 j]
  linarith

private theorem eq_toLp_fst_zero_of_norm_eq_one {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {z : WithLp 2 (E × F)} (hz : ‖z‖ = 1)
    (hfst : ‖z.fst‖ = 1) : z = WithLp.toLp 2 (z.fst, 0) := by
  have hsq := WithLp.prod_norm_sq_eq_of_L2 z
  rw [hz, hfst] at hsq
  have hsnd0 : ‖z.snd‖ ^ 2 = 0 := by linarith
  exact (WithLp.ext_iff 2).2 (Prod.ext rfl (norm_eq_zero.mp (sq_eq_zero_iff.mp hsnd0)))

private theorem eq_toLp_zero_snd_of_norm_eq_one {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {z : WithLp 2 (E × F)} (hz : ‖z‖ = 1)
    (hsnd : ‖z.snd‖ = 1) : z = WithLp.toLp 2 (0, z.snd) := by
  have hsq := WithLp.prod_norm_sq_eq_of_L2 z
  rw [hz, hsnd] at hsq
  have hfst0 : ‖z.fst‖ ^ 2 = 0 := by linarith
  exact (WithLp.ext_iff 2).2 (Prod.ext (norm_eq_zero.mp (sq_eq_zero_iff.mp hfst0)) rfl)

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {k l : ℕ}

/-- Equality analysis for `φ (fst ∘ x) * ψ (snd ∘ y) = 1` on an orthonormal `(k + l)`-frame
`Fin.append x y` when `‖φ‖ ≤ 1` and `‖ψ‖ ≤ 1`: every `x i` lies in `E × {0}`, every `y j` lies in
`{0} × F`, and either `(fst ∘ x, snd ∘ y)` is calibrated by `(φ, ψ)` or by `(-φ, -ψ)`. -/
private theorem eq_toLp_and_calibrated_of_mul_eq_one
    {φ : E [⋀^Fin k]→L[ℝ] ℝ} {ψ : F [⋀^Fin l]→L[ℝ] ℝ} (hφ : ‖φ‖ ≤ 1) (hψ : ‖ψ‖ ≤ 1)
    {x : Fin k → WithLp 2 (E × F)} {y : Fin l → WithLp 2 (E × F)}
    (hxy : Orthonormal ℝ (Fin.append x y))
    (hmul : φ (fun i ↦ (x i).fst) * ψ (fun j ↦ (y j).snd) = 1) :
    (x = fun i ↦ WithLp.toLp 2 ((x i).fst, 0)) ∧
      (y = fun j ↦ WithLp.toLp 2 (0, (y j).snd)) ∧
      ((φ.IsCalibratedFrame (fun i ↦ (x i).fst) ∧ ψ.IsCalibratedFrame (fun j ↦ (y j).snd)) ∨
        ((-φ).IsCalibratedFrame (fun i ↦ (x i).fst) ∧
          (-ψ).IsCalibratedFrame (fun j ↦ (y j).snd))) := by
  let x₁ : Fin k → E := fun i ↦ (x i).fst
  let y₂ : Fin l → F := fun j ↦ (y j).snd
  have hx₁_le (i : Fin k) : ‖x₁ i‖ ≤ 1 :=
    (WithLp.norm_fst_le (x := x i)).trans_eq (by simpa using hxy.1 (Fin.castAdd l i))
  have hy₂_le (j : Fin l) : ‖y₂ j‖ ≤ 1 :=
    (WithLp.norm_snd_le (x := y j)).trans_eq (by simpa using hxy.1 (Fin.natAdd k j))
  have hp₁ : ∏ i, ‖x₁ i‖ ≤ 1 := Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ hx₁_le i
  have hp₂ : ∏ j, ‖y₂ j‖ ≤ 1 := Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun j _ ↦ hy₂_le j
  have hp₁0 : 0 ≤ ∏ i, ‖x₁ i‖ := Finset.prod_nonneg fun _ _ ↦ norm_nonneg _
  have hp₂0 : 0 ≤ ∏ j, ‖y₂ j‖ := Finset.prod_nonneg fun _ _ ↦ norm_nonneg _
  have hφ_le : |φ x₁| ≤ ∏ i, ‖x₁ i‖ := by
    simpa only [Real.norm_eq_abs, one_mul] using
      (φ.le_opNorm x₁).trans (mul_le_mul_of_nonneg_right hφ hp₁0)
  have hψ_le : |ψ y₂| ≤ ∏ j, ‖y₂ j‖ := by
    simpa only [Real.norm_eq_abs, one_mul] using
      (ψ.le_opNorm y₂).trans (mul_le_mul_of_nonneg_right hψ hp₂0)
  have habs_mul : 1 = |φ x₁| * |ψ y₂| := by rw [← abs_mul, hmul, abs_one]
  have hprod_ge : 1 ≤ (∏ i, ‖x₁ i‖) * ∏ j, ‖y₂ j‖ :=
    habs_mul.trans_le (mul_le_mul hφ_le hψ_le (abs_nonneg _) hp₁0)
  have hx_eq : x = fun i ↦ WithLp.toLp 2 (x₁ i, 0) := funext fun i ↦
    eq_toLp_fst_zero_of_norm_eq_one (by simpa using hxy.1 (Fin.castAdd l i))
      (eq_one_of_prod_ge_one (fun _ ↦ norm_nonneg _) hx₁_le (by nlinarith) i)
  have hy_eq : y = fun j ↦ WithLp.toLp 2 (0, y₂ j) := funext fun j ↦
    eq_toLp_zero_snd_of_norm_eq_one (by simpa using hxy.1 (Fin.natAdd k j))
      (eq_one_of_prod_ge_one (fun _ ↦ norm_nonneg _) hy₂_le (by nlinarith) j)
  obtain ⟨hx₁_orth, hy₂_orth⟩ : Orthonormal ℝ x₁ ∧ Orthonormal ℝ y₂ := by
    rwa [hx_eq, hy_eq, WithLp.orthonormal_append_toLp_iff] at hxy
  have habs₁ : |φ x₁| = 1 := by
    nlinarith [hφ_le.trans hp₁, hψ_le.trans hp₂, abs_nonneg (φ x₁), abs_nonneg (ψ y₂)]
  refine ⟨hx_eq, hy_eq, ?_⟩
  rcases (abs_eq zero_le_one).mp habs₁ with h1 | h1
  · exact Or.inl ⟨isCalibratedFrame_iff.mpr ⟨hx₁_orth, h1⟩,
      isCalibratedFrame_iff.mpr ⟨hy₂_orth, by nlinarith⟩⟩
  · have h2 : ψ y₂ = -1 := by nlinarith
    exact Or.inr ⟨isCalibratedFrame_iff.mpr ⟨hx₁_orth, by simp [x₁, h1]⟩,
      isCalibratedFrame_iff.mpr ⟨hy₂_orth, by simp [y₂, h2]⟩⟩

/-- Concatenating a calibrated `k`-frame `u` of `φ` in `E × {0}` with a calibrated `l`-frame `w` of
`ψ` in `{0} × F` produces a calibrated `(k + l)`-frame of `φ.externalWedge 2 ψ` on
`WithLp 2 (E × F)`. -/
theorem IsCalibratedFrame.externalWedge_append_toLp
    {φ : E [⋀^Fin k]→L[ℝ] ℝ} {ψ : F [⋀^Fin l]→L[ℝ] ℝ} {u : Fin k → E} {w : Fin l → F}
    (hu : φ.IsCalibratedFrame u) (hw : ψ.IsCalibratedFrame w) :
    (φ.externalWedge 2 ψ).IsCalibratedFrame
      (Fin.append (fun i ↦ WithLp.toLp 2 (u i, 0)) (fun j ↦ WithLp.toLp 2 (0, w j))) := by
  rw [isCalibratedFrame_iff]
  refine ⟨(WithLp.orthonormal_append_toLp_iff u w).mpr ⟨hu.orthonormal, hw.orthonormal⟩, ?_⟩
  rw [externalWedge_apply_append_toLp, hu.apply_eq_one, hw.apply_eq_one, mul_one]

/-- Concatenating calibrated frames of `-φ` and `-ψ` also produces a calibrated frame of
`φ.externalWedge 2 ψ`, since `(-1) * (-1) = 1`. -/
theorem IsCalibratedFrame.externalWedge_append_toLp_of_neg
    {φ : E [⋀^Fin k]→L[ℝ] ℝ} {ψ : F [⋀^Fin l]→L[ℝ] ℝ} {u : Fin k → E} {w : Fin l → F}
    (hu : (-φ).IsCalibratedFrame u) (hw : (-ψ).IsCalibratedFrame w) :
    (φ.externalWedge 2 ψ).IsCalibratedFrame
      (Fin.append (fun i ↦ WithLp.toLp 2 (u i, 0)) (fun j ↦ WithLp.toLp 2 (0, w j))) := by
  simpa using hu.externalWedge_append_toLp hw

/-- When `‖φ‖ ≤ 1` and `‖ψ‖ ≤ 1`, a concatenated factor tuple `(u, 0)` followed by `(0, w)` is
calibrated by `φ.externalWedge 2 ψ` if and only if either `(u, w)` is calibrated by `(φ, ψ)` or
`(u, w)` is calibrated by `(-φ, -ψ)`. -/
theorem isCalibratedFrame_externalWedge_append_toLp_iff
    {φ : E [⋀^Fin k]→L[ℝ] ℝ} {ψ : F [⋀^Fin l]→L[ℝ] ℝ} (hφ : ‖φ‖ ≤ 1) (hψ : ‖ψ‖ ≤ 1)
    {u : Fin k → E} {w : Fin l → F} :
    (φ.externalWedge 2 ψ).IsCalibratedFrame
        (Fin.append (fun i ↦ WithLp.toLp 2 (u i, 0)) (fun j ↦ WithLp.toLp 2 (0, w j))) ↔
      (φ.IsCalibratedFrame u ∧ ψ.IsCalibratedFrame w) ∨
        ((-φ).IsCalibratedFrame u ∧ (-ψ).IsCalibratedFrame w) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hval := h.apply_eq_one
    rw [externalWedge_apply_append_toLp] at hval
    exact (eq_toLp_and_calibrated_of_mul_eq_one hφ hψ h.orthonormal hval).2.2
  · rintro (⟨hu, hw⟩ | ⟨hu, hw⟩)
    · exact hu.externalWedge_append_toLp hw
    · exact hu.externalWedge_append_toLp_of_neg hw

end GeneralFactors

/-! ### Subspace splitting, simple-factor comass, and Harvey–Lawson Proposition II.7.10 -/

section SubspaceSplitting

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {k l : ℕ}

private theorem orthonormal_append_of_inner_eq_zero {G : Type*} [SeminormedAddCommGroup G]
    [InnerProductSpace ℝ G] {x : Fin k → G} {y : Fin l → G}
    (hx : Orthonormal ℝ x) (hy : Orthonormal ℝ y) (hxy : ∀ i j, ⟪x i, y j⟫ = 0) :
    Orthonormal ℝ (Fin.append x y) := by
  refine ⟨fun m ↦ ?_, fun m₁ m₂ hne ↦ ?_⟩
  · obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective m
    · simpa using hx.1 i
    · simpa using hy.1 j
  · obtain ⟨i₁ | j₁, rfl⟩ := finSumFinEquiv.surjective m₁ <;>
      obtain ⟨i₂ | j₂, rfl⟩ := finSumFinEquiv.surjective m₂
    · simpa using hx.2 fun h ↦ hne (congrArg (fun i ↦ finSumFinEquiv (Sum.inl i)) h)
    · simpa using hxy i₁ j₂
    · simpa [real_inner_comm] using hxy i₂ j₁
    · simpa using hy.2 fun h ↦ hne (congrArg (fun j ↦ finSumFinEquiv (Sum.inr j)) h)

/-- Inside the `(k + l)`-dimensional span `V` of an orthonormal frame `v : Fin (k + l) → E ⊕ F`,
rank-nullity on the composition `V → E → U` (where `dim U ≤ k`) produces an orthonormal basis
`Fin.append xV yV` of `V` whose last `l` vectors project orthogonally to `0` in `U`. -/
private theorem exists_orthonormal_append_in_span_starProjection_fst_eq_zero
    (U : Submodule ℝ E) [FiniteDimensional ℝ U] (hU : Module.finrank ℝ U ≤ k)
    {v : Fin (k + l) → WithLp 2 (E × F)} (hv : Orthonormal ℝ v) :
    let V := Submodule.span ℝ (Set.range v)
    ∃ (xV : Fin k → V) (yV : Fin l → V),
      Orthonormal ℝ (Fin.append xV yV) ∧
        ∀ j, U.starProjection ((yV j : WithLp 2 (E × F)).fst) = 0 := by
  intro V
  have : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range v)
  have hdimV : Module.finrank ℝ V = k + l := by
    rw [finrank_span_eq_card hv.linearIndependent, Fintype.card_fin]
  let q : V →ₗ[ℝ] U :=
    (U.orthogonalProjectionOnto.comp (WithLp.fstL 2 ℝ E F)).toLinearMap.comp V.subtype
  have hrn := q.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℝ (LinearMap.range q) ≤ k :=
    (Submodule.finrank_le (LinearMap.range q)).trans hU
  have hl_ker : l ≤ Module.finrank ℝ (LinearMap.ker q) := by omega
  let bKer := stdOrthonormalBasis ℝ (LinearMap.ker q)
  let yV : Fin l → V := ⇑(LinearMap.ker q).subtypeₗᵢ ∘ ⇑bKer ∘ Fin.castLE hl_ker
  have hyV : Orthonormal ℝ yV :=
    (LinearMap.ker q).subtypeₗᵢ.orthonormal_comp_iff.mpr
      (bKer.orthonormal.comp _ (Fin.castLE_injective hl_ker))
  let K : Submodule ℝ V := Submodule.span ℝ (Set.range yV)
  have hdimK : Module.finrank ℝ K = l := by
    rw [finrank_span_eq_card hyV.linearIndependent, Fintype.card_fin]
  have hK_orth := K.finrank_add_finrank_orthogonal
  have hk_orth : Module.finrank ℝ Kᗮ = k := by omega
  let bOrth : OrthonormalBasis (Fin k) ℝ Kᗮ :=
    (stdOrthonormalBasis ℝ Kᗮ).reindex (finCongr hk_orth)
  let xV : Fin k → V := ⇑Kᗮ.subtypeₗᵢ ∘ ⇑bOrth
  have hxV : Orthonormal ℝ xV := Kᗮ.subtypeₗᵢ.orthonormal_comp_iff.mpr bOrth.orthonormal
  have horth_xy (i : Fin k) (j : Fin l) : ⟪xV i, yV j⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self j))
      (bOrth i).2
  exact ⟨xV, yV, orthonormal_append_of_inner_eq_zero hxV hyV horth_xy,
    fun j ↦ congrArg Subtype.val (bKer (Fin.castLE hl_ker j)).2⟩

private theorem fin_append_update_left {α : Type*} (x : Fin k → α) (y : Fin l → α) (i₀ : Fin k)
    (a : α) :
    Fin.append (Function.update x i₀ a) y =
      Function.update (Fin.append x y) (Fin.castAdd l i₀) a := by
  ext m
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective m
  · by_cases hi : i = i₀ <;> simp [hi]
  · have hne : Fin.natAdd k j ≠ Fin.castAdd l i₀ := by
      simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
      omega
    simp [Function.update_of_ne hne]

private theorem fin_append_update_right {α : Type*} (x : Fin k → α) (y : Fin l → α) (j₀ : Fin l)
    (b : α) :
    Fin.append x (Function.update y j₀ b) =
      Function.update (Fin.append x y) (Fin.natAdd k j₀) b := by
  ext m
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective m
  · have hne : Fin.castAdd l i ≠ Fin.natAdd k j₀ := by
      simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
      omega
    simp [Function.update_of_ne hne]
  · by_cases hj : j = j₀ <;> simp [hj]

/-- Negate one vector of `(x₀, y₀)` (when `k + l > 0`) to flip the sign of
`ιMulti ℝ (k + l) (Fin.append x₀ y₀)` while preserving orthonormality and
`U.starProjection ∘ fst = 0` on the second block. -/
private theorem flip_sign_append_starProjection_fst_eq_zero
    (U : Submodule ℝ E) [U.HasOrthogonalProjection] (hk_or_l : 0 < k + l)
    {x₀ : Fin k → WithLp 2 (E × F)} {y₀ : Fin l → WithLp 2 (E × F)}
    (hxy₀ : Orthonormal ℝ (Fin.append x₀ y₀)) (hyU : ∀ j, U.starProjection (y₀ j).fst = 0) :
    ∃ (x : Fin k → WithLp 2 (E × F)) (y : Fin l → WithLp 2 (E × F)),
      Orthonormal ℝ (Fin.append x y) ∧
        (∀ j, U.starProjection (y j).fst = 0) ∧
        ιMulti ℝ (k + l) (Fin.append x y) = -ιMulti ℝ (k + l) (Fin.append x₀ y₀) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · let j₀ : Fin l := ⟨0, by omega⟩
    refine ⟨x₀, Function.update y₀ j₀ (-y₀ j₀), ?_, fun j ↦ ?_, ?_⟩
    · rw [fin_append_update_right, ← Fin.append_right x₀ y₀ j₀, TauCeti.orthonormal_update_neg_iff]
      exact hxy₀
    · by_cases hj : j = j₀ <;> simp [hj, hyU]
    · rw [fin_append_update_right, (ιMulti ℝ (k + l)).map_update_neg, ← Fin.append_right x₀ y₀ j₀,
        Function.update_eq_self]
  · let i₀ : Fin k := ⟨0, hk0⟩
    refine ⟨Function.update x₀ i₀ (-x₀ i₀), y₀, ?_, hyU, ?_⟩
    · rw [fin_append_update_left, ← Fin.append_left x₀ y₀ i₀, TauCeti.orthonormal_update_neg_iff]
      exact hxy₀
    · rw [fin_append_update_left, (ιMulti ℝ (k + l)).map_update_neg, ← Fin.append_left x₀ y₀ i₀,
        Function.update_eq_self]

/-- **Subspace-splitting lemma for orthonormal `(k + l)`-frames in `E ⊕ F`.** Given a subspace
`U ≤ E` with `finrank ℝ U ≤ k`, any orthonormal frame `v : Fin (k + l) → WithLp 2 (E × F)` shares
its simple `(k + l)`-vector `v₁ ∧ ⋯ ∧ v_{k + l}` with a concatenated orthonormal frame
`Fin.append x y` whose last `l` vectors project orthogonally to `0` in `U`. -/
private theorem exists_orthonormal_append_starProjection_fst_eq_zero
    (U : Submodule ℝ E) [FiniteDimensional ℝ U] (hU : Module.finrank ℝ U ≤ k)
    {v : Fin (k + l) → WithLp 2 (E × F)} (hv : Orthonormal ℝ v) :
    ∃ (x : Fin k → WithLp 2 (E × F)) (y : Fin l → WithLp 2 (E × F)),
      Orthonormal ℝ (Fin.append x y) ∧
        (∀ j, U.starProjection (y j).fst = 0) ∧
        ιMulti ℝ (k + l) v = ιMulti ℝ (k + l) (Fin.append x y) := by
  rcases Nat.eq_zero_or_pos (k + l) with h0 | hpos
  · obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.mp h0
    have hv0 : v = Fin.append ![] ![] := funext fun m ↦ Fin.elim0 m
    exact ⟨![], ![], hv0 ▸ hv, fun j ↦ Fin.elim0 j, congrArg (ιMulti ℝ (0 + 0)) hv0⟩
  · obtain ⟨xV, yV, hxyV, hyU⟩ :=
      exists_orthonormal_append_in_span_starProjection_fst_eq_zero U hU hv
    let x₀ : Fin k → WithLp 2 (E × F) := fun i ↦ (xV i : WithLp 2 (E × F))
    let y₀ : Fin l → WithLp 2 (E × F) := fun j ↦ (yV j : WithLp 2 (E × F))
    have happend_coe :
        (fun m ↦ ((Fin.append xV yV m : Submodule.span ℝ (Set.range v)) : WithLp 2 (E × F))) =
          Fin.append x₀ y₀ := by
      ext m
      obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective m <;> simp [x₀, y₀]
    have hxy₀ : Orthonormal ℝ (Fin.append x₀ y₀) := by
      rw [← happend_coe]
      exact (Submodule.span ℝ (Set.range v)).subtypeₗᵢ.orthonormal_comp_iff.mpr hxyV
    have hmem (m : Fin (k + l)) : Fin.append x₀ y₀ m ∈ Submodule.span ℝ (Set.range v) := by
      rw [← congrFun happend_coe m]
      exact (Fin.append xV yV m).2
    rcases hv.ιMulti_eq_or_eq_neg_of_mem_span hxy₀ hmem with h | h
    · exact ⟨x₀, y₀, hxy₀, hyU, h.symm⟩
    · obtain ⟨x, y, hxy, hyU', hflip⟩ :=
        flip_sign_append_starProjection_fst_eq_zero U hpos hxy₀ hyU
      exact ⟨x, y, hxy, hyU', by rw [hflip, h, neg_neg]⟩

end SubspaceSplitting

section SimpleFactorLeft

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {k l : ℕ}

/-- When the last `l` vectors project orthogonally to `0` in `span(range u)`, the external wedge of
the simple `k`-form `TauCeti.alternatingFormEquiv E k (ιMulti ℝ k u)` with `ψ` collapses to the
single product `φ (fst ∘ x) * ψ (snd ∘ y)`. -/
private theorem externalWedge_alternatingFormEquiv_ιMulti_apply_append
    (u : Fin k → E) (ψ : F [⋀^Fin l]→L[ℝ] ℝ)
    (x : Fin k → WithLp 2 (E × F)) (y : Fin l → WithLp 2 (E × F))
    (hy : ∀ j, (Submodule.span ℝ (Set.range u)).starProjection (y j).fst = 0) :
    (TauCeti.alternatingFormEquiv E k (ιMulti ℝ k u)).externalWedge 2 ψ (Fin.append x y) =
      TauCeti.alternatingFormEquiv E k (ιMulti ℝ k u) (fun i ↦ (x i).fst) *
        ψ (fun j ↦ (y j).snd) := by
  let U : Submodule ℝ E := Submodule.span ℝ (Set.range u)
  have hproj := TauCeti.alternatingFormEquiv_ιMulti_comp_starProjection u U
    fun i ↦ Submodule.subset_span (Set.mem_range_self i)
  calc
    (TauCeti.alternatingFormEquiv E k (ιMulti ℝ k u)).externalWedge 2 ψ (Fin.append x y)
      = ((TauCeti.alternatingFormEquiv E k (ιMulti ℝ k u)).compContinuousLinearMap
            (U.starProjection ∘L WithLp.fstL 2 ℝ E F)).wedge
          (ψ.compContinuousLinearMap (WithLp.sndL 2 ℝ E F)) (Fin.append x y) := by
        rw [externalWedge_def, ← compContinuousLinearMap_compContinuousLinearMap, hproj]
    _ = TauCeti.alternatingFormEquiv E k (ιMulti ℝ k u)
          (fun i ↦ U.starProjection (x i).fst) * ψ (fun j ↦ (y j).snd) :=
        wedge_compContinuousLinearMap_apply_append_of_left _ ψ
          (U.starProjection ∘L WithLp.fstL 2 ℝ E F) (WithLp.sndL 2 ℝ E F) x y hy
    _ = TauCeti.alternatingFormEquiv E k (ιMulti ℝ k u) (fun i ↦ (x i).fst) *
          ψ (fun j ↦ (y j).snd) := by
        congr 1
        exact DFunLike.congr_fun hproj (fun i ↦ (x i).fst)

/-- **Exact comass of an external wedge with a simple `k`-form on the left**:
`‖(alternatingFormEquiv E k (ιMulti ℝ k u)).externalWedge 2 ψ‖ = ‖ιMulti ℝ k u‖ * ‖ψ‖`. -/
@[simp]
theorem norm_externalWedge_alternatingFormEquiv_ιMulti_left (u : Fin k → E)
    (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    ‖(TauCeti.alternatingFormEquiv E k (ιMulti ℝ k u)).externalWedge 2 ψ‖ =
      ‖ιMulti ℝ k u‖ * ‖ψ‖ := by
  let φ := TauCeti.alternatingFormEquiv E k (ιMulti ℝ k u)
  refine le_antisymm ?_ ?_
  · rw [opNorm_le_iff_le_orthonormal (by positivity)]
    intro v hv
    let U : Submodule ℝ E := Submodule.span ℝ (Set.range u)
    have hU : Module.finrank ℝ U ≤ k := by
      simpa [Set.finrank] using finrank_range_le_card u
    obtain ⟨x, y, hxy, hy, hι⟩ := exists_orthonormal_append_starProjection_fst_eq_zero U hU hv
    rw [(φ.externalWedge 2 ψ).apply_eq_of_ιMulti_eq hι,
      externalWedge_alternatingFormEquiv_ιMulti_apply_append u ψ x y hy, norm_mul]
    have hx_le (i : Fin k) : ‖(x i).fst‖ ≤ 1 :=
      (WithLp.norm_fst_le (x := x i)).trans_eq (by simpa using hxy.1 (Fin.castAdd l i))
    have hy_le (j : Fin l) : ‖(y j).snd‖ ≤ 1 :=
      (WithLp.norm_snd_le (x := y j)).trans_eq (by simpa using hxy.1 (Fin.natAdd k j))
    have hφ_le : ‖φ (fun i ↦ (x i).fst)‖ ≤ ‖ιMulti ℝ k u‖ := by
      calc ‖φ (fun i ↦ (x i).fst)‖
          ≤ ‖φ‖ * ∏ i, ‖(x i).fst‖ := φ.le_opNorm _
        _ ≤ ‖φ‖ * 1 := mul_le_mul_of_nonneg_left
            (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ hx_le i) (norm_nonneg _)
        _ = ‖ιMulti ℝ k u‖ := by simp [φ, TauCeti.norm_alternatingFormEquiv_ιMulti]
    have hψ_le : ‖ψ (fun j ↦ (y j).snd)‖ ≤ ‖ψ‖ := by
      calc ‖ψ (fun j ↦ (y j).snd)‖
          ≤ ‖ψ‖ * ∏ j, ‖(y j).snd‖ := ψ.le_opNorm _
        _ ≤ ‖ψ‖ * 1 := mul_le_mul_of_nonneg_left
            (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun j _ ↦ hy_le j) (norm_nonneg _)
        _ = ‖ψ‖ := mul_one _
    exact mul_le_mul hφ_le hψ_le (norm_nonneg _) (norm_nonneg _)
  · simpa [φ, TauCeti.norm_alternatingFormEquiv_ιMulti] using
      norm_mul_norm_le_norm_externalWedge (p := 2) φ ψ

private theorem exists_isCalibratedFrame_and_ιMulti_eq_neg
    {e : Fin k → E} (he : Orthonormal ℝ e) {ψ : F [⋀^Fin l]→L[ℝ] ℝ}
    (hl : k = 0 ∨ ψ 0 ≠ -1) {x₁ : Fin k → E} {y₂ : Fin l → F}
    (hx_cal : (-TauCeti.alternatingFormEquiv E k (ιMulti ℝ k e)).IsCalibratedFrame x₁)
    (hy_cal : (-ψ).IsCalibratedFrame y₂) :
    ∃ w : Fin l → F, ψ.IsCalibratedFrame w ∧ ιMulti ℝ l y₂ = -ιMulti ℝ l w := by
  rcases Nat.eq_zero_or_pos l with rfl | hl_pos
  · exfalso
    rcases hl with rfl | hψ0
    · have hx_eq_e : x₁ = e := Subsingleton.elim _ _
      have h1 := (isCalibratedFrame_alternatingFormEquiv_ιMulti_self he).apply_eq_one
      have hneg := hx_cal.apply_eq_one
      rw [neg_apply, hx_eq_e, h1] at hneg
      norm_num at hneg
    · have hy0 : y₂ = 0 := Subsingleton.elim _ _
      have hneg := hy_cal.apply_eq_one
      rw [neg_apply, hy0, neg_eq_iff_eq_neg] at hneg
      exact hψ0 hneg
  · let j₀ : Fin l := ⟨0, hl_pos⟩
    let w : Fin l → F := Function.update y₂ j₀ (-y₂ j₀)
    have hw_cal : ψ.IsCalibratedFrame w := by
      simpa [w] using (isCalibratedFrame_neg_update_neg_iff (-ψ) y₂ j₀).mpr hy_cal
    exact ⟨w, hw_cal, by simp [w]⟩

/-- **Harvey–Lawson Proposition II.7.10** (simple-form version). Let `e` be an orthonormal
`k`-frame in `E`, `φ` its unit simple `k`-form `v ↦ ⟪e₁ ∧ ⋯ ∧ eₖ, v₁ ∧ ⋯ ∧ vₖ⟫`, and `ψ` an `l`-form
on `F` with `‖ψ‖ ≤ 1`. Excluding only the degenerate `0`-form sign flip (`k > 0`, `l = 0`,
`ψ 0 = -1`), a tuple `v : Fin (k + l) → WithLp 2 (E × F)` is calibrated by `φ.externalWedge 2 ψ`
if and only if `v` is orthonormal and shares its oriented `(k + l)`-plane with a product frame
`(e₁, 0), …, (eₖ, 0), (0, w₁), …, (0, wₗ)` for some calibrated `l`-frame `w` of `ψ`. -/
theorem isCalibratedFrame_externalWedge_alternatingFormEquiv_ιMulti_iff
    {e : Fin k → E} (he : Orthonormal ℝ e) {ψ : F [⋀^Fin l]→L[ℝ] ℝ} (hψ : ‖ψ‖ ≤ 1)
    (hl : k = 0 ∨ ψ 0 ≠ -1) {v : Fin (k + l) → WithLp 2 (E × F)} :
    ((TauCeti.alternatingFormEquiv E k (ιMulti ℝ k e)).externalWedge 2 ψ).IsCalibratedFrame v ↔
      Orthonormal ℝ v ∧
        ∃ w : Fin l → F, ψ.IsCalibratedFrame w ∧
          ιMulti ℝ (k + l) v =
            ιMulti ℝ (k + l)
              (Fin.append (fun i ↦ WithLp.toLp 2 (e i, 0)) (fun j ↦ WithLp.toLp 2 (0, w j))) := by
  let φ := TauCeti.alternatingFormEquiv E k (ιMulti ℝ k e)
  refine ⟨fun hcal_v ↦ ⟨hcal_v.orthonormal, ?_⟩, fun ⟨hv, w, hw, hι⟩ ↦
    ((isCalibratedFrame_alternatingFormEquiv_ιMulti_self he).externalWedge_append_toLp
      hw).of_ιMulti_eq hv hι⟩
  have hv := hcal_v.orthonormal
  have hval := hcal_v.apply_eq_one
  let U : Submodule ℝ E := Submodule.span ℝ (Set.range e)
  have hU : Module.finrank ℝ U ≤ k := by simpa [Set.finrank] using finrank_range_le_card e
  obtain ⟨x, y, hxy, hy, hι⟩ := exists_orthonormal_append_starProjection_fst_eq_zero U hU hv
  rw [(φ.externalWedge 2 ψ).apply_eq_of_ιMulti_eq hι,
    externalWedge_alternatingFormEquiv_ιMulti_apply_append e ψ x y hy] at hval
  obtain ⟨hx_eq, hy_eq, hcal⟩ :=
    eq_toLp_and_calibrated_of_mul_eq_one he.norm_alternatingFormEquiv_ιMulti.le hψ hxy hval
  have hι' : ιMulti ℝ (k + l) v =
      ιMulti ℝ (k + l) (Fin.append (fun i ↦ WithLp.toLp 2 ((x i).fst, 0))
        (fun j ↦ WithLp.toLp 2 (0, (y j).snd))) := by
    conv_rhs at hι => rw [hx_eq, hy_eq]
    exact hι
  rcases hcal with ⟨hx_cal, hy_cal⟩ | ⟨hx_cal, hy_cal⟩
  · have hx_ι : ιMulti ℝ k (fun i ↦ (x i).fst) = ιMulti ℝ k e :=
      ((isCalibratedFrame_alternatingFormEquiv_ιMulti_iff he).mp hx_cal).2
    exact ⟨fun j ↦ (y j).snd, hy_cal, hι'.trans (exteriorPower.ιMulti_append_toLp_congr hx_ι rfl)⟩
  · have hx_ι : ιMulti ℝ k (fun i ↦ (x i).fst) = -ιMulti ℝ k e :=
      ((isCalibratedFrame_neg_alternatingFormEquiv_ιMulti_iff he).mp hx_cal).2
    obtain ⟨w, hw_cal, hy_ι⟩ :=
      exists_isCalibratedFrame_and_ιMulti_eq_neg he hl hx_cal hy_cal
    exact ⟨w, hw_cal, hι'.trans (exteriorPower.ιMulti_append_toLp_of_eq_neg hx_ι hy_ι)⟩

/-- For any positive right degree `l ≠ 0`, `ψ 0 = 0 ≠ -1` holds automatically, giving the
unconditional simple-form product calibration characterization. -/
theorem isCalibratedFrame_externalWedge_alternatingFormEquiv_ιMulti_iff_of_ne_zero
    {e : Fin k → E} (he : Orthonormal ℝ e) {ψ : F [⋀^Fin l]→L[ℝ] ℝ} (hψ : ‖ψ‖ ≤ 1)
    (hl : l ≠ 0) {v : Fin (k + l) → WithLp 2 (E × F)} :
    ((TauCeti.alternatingFormEquiv E k (ιMulti ℝ k e)).externalWedge 2 ψ).IsCalibratedFrame v ↔
      Orthonormal ℝ v ∧
        ∃ w : Fin l → F, ψ.IsCalibratedFrame w ∧
          ιMulti ℝ (k + l) v =
            ιMulti ℝ (k + l)
              (Fin.append (fun i ↦ WithLp.toLp 2 (e i, 0)) (fun j ↦ WithLp.toLp 2 (0, w j))) := by
  refine isCalibratedFrame_externalWedge_alternatingFormEquiv_ιMulti_iff he hψ (Or.inr ?_)
  have h0 : ψ 0 = 0 := ψ.toAlternatingMap.map_coord_zero (⟨0, Nat.pos_of_ne_zero hl⟩ : Fin l) rfl
  simp [h0]

end SimpleFactorLeft

section SimpleFactorRight

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {k l : ℕ}

/-- **Exact comass of an external wedge with a simple `l`-form on the right**:
`‖φ.externalWedge 2 (alternatingFormEquiv F l (ιMulti ℝ l w))‖ = ‖φ‖ * ‖ιMulti ℝ l w‖`. -/
@[simp]
theorem norm_externalWedge_alternatingFormEquiv_ιMulti_right (φ : E [⋀^Fin k]→L[ℝ] ℝ)
    (w : Fin l → F) :
    ‖φ.externalWedge 2 (TauCeti.alternatingFormEquiv F l (ιMulti ℝ l w))‖ =
      ‖φ‖ * ‖ιMulti ℝ l w‖ := by
  let ψ := TauCeti.alternatingFormEquiv F l (ιMulti ℝ l w)
  refine le_antisymm ?_ ?_
  · rw [opNorm_le_iff_le_orthonormal (by positivity)]
    intro v hv
    let v' : Fin (l + k) → WithLp 2 (F × E) :=
      fun i ↦ WithLp.toLp 2 ((v (Fin.cast (Nat.add_comm l k) i)).snd,
        (v (Fin.cast (Nat.add_comm l k) i)).fst)
    have hv' : Orthonormal ℝ v' := by
      rw [orthonormal_iff_ite] at hv ⊢
      intro i j
      have hij : Fin.cast (Nat.add_comm l k) i = Fin.cast (Nat.add_comm l k) j ↔ i = j :=
        (Fin.castOrderIso (Nat.add_comm l k)).injective.eq_iff
      simpa [v', WithLp.prod_inner_apply, add_comm, hij] using
        hv (Fin.cast (Nat.add_comm l k) i) (Fin.cast (Nat.add_comm l k) j)
    rw [externalWedge_swap_apply, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc ‖(ψ.externalWedge 2 φ) v'‖
        ≤ ‖ψ.externalWedge 2 φ‖ := by
          simpa [hv'.norm_eq_one] using (ψ.externalWedge 2 φ).le_opNorm v'
      _ = ‖φ‖ * ‖ιMulti ℝ l w‖ := by
          rw [norm_externalWedge_alternatingFormEquiv_ιMulti_left, mul_comm]
  · simpa [ψ, TauCeti.norm_alternatingFormEquiv_ιMulti] using
      norm_mul_norm_le_norm_externalWedge (p := 2) φ ψ

end SimpleFactorRight

end ContinuousAlternatingMap

namespace Orthonormal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {k l : ℕ}

/-- Wedging externally on the left with the unit simple `k`-form of an orthonormal frame `e`
preserves the comass of `ψ`. -/
theorem norm_externalWedge_alternatingFormEquiv_ιMulti_left [FiniteDimensional ℝ E]
    {e : Fin k → E} (he : Orthonormal ℝ e) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    ‖(TauCeti.alternatingFormEquiv E k (ιMulti ℝ k e)).externalWedge 2 ψ‖ = ‖ψ‖ := by
  rw [ContinuousAlternatingMap.norm_externalWedge_alternatingFormEquiv_ιMulti_left,
    he.norm_ιMulti, one_mul]

/-- Wedging externally on the right with the unit simple `l`-form of an orthonormal frame `w`
preserves the comass of `φ`. -/
theorem norm_externalWedge_alternatingFormEquiv_ιMulti_right [FiniteDimensional ℝ F]
    (φ : E [⋀^Fin k]→L[ℝ] ℝ) {w : Fin l → F} (hw : Orthonormal ℝ w) :
    ‖φ.externalWedge 2 (TauCeti.alternatingFormEquiv F l (ιMulti ℝ l w))‖ = ‖φ‖ := by
  rw [ContinuousAlternatingMap.norm_externalWedge_alternatingFormEquiv_ιMulti_right,
    hw.norm_ιMulti, mul_one]

end Orthonormal

namespace Orientation

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {k l n : ℕ}

/-- Wedging externally on the left with an oriented volume form `o.volumeFormL` preserves the
comass: `‖o.volumeFormL.externalWedge 2 ψ‖ = ‖ψ‖`. -/
@[simp]
theorem norm_externalWedge_volumeFormL_left [Fact (Module.finrank ℝ E = n)]
    (o : Orientation ℝ E (Fin n)) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    ‖o.volumeFormL.externalWedge 2 ψ‖ = ‖ψ‖ := by
  rcases n with - | n
  · rw [ContinuousAlternatingMap.norm_externalWedge_zero_left, o.norm_volumeFormL, one_mul]
  · have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
    let b := ((stdOrthonormalBasis ℝ E).reindex (finCongr Fact.out)).adjustToOrientation o
    rw [o.volumeFormL_eq_alternatingFormEquiv_ιMulti b
      (OrthonormalBasis.orientation_adjustToOrientation _ _),
      b.orthonormal.norm_externalWedge_alternatingFormEquiv_ιMulti_left]

/-- Wedging externally on the right with an oriented volume form `o.volumeFormL` preserves the
comass: `‖φ.externalWedge 2 o.volumeFormL‖ = ‖φ‖`. -/
@[simp]
theorem norm_externalWedge_volumeFormL_right [Fact (Module.finrank ℝ F = n)]
    (φ : E [⋀^Fin k]→L[ℝ] ℝ) (o : Orientation ℝ F (Fin n)) :
    ‖φ.externalWedge 2 o.volumeFormL‖ = ‖φ‖ := by
  rcases n with - | n
  · rw [ContinuousAlternatingMap.norm_externalWedge_zero_right, o.norm_volumeFormL, mul_one]
  · have : FiniteDimensional ℝ F := .of_fact_finrank_eq_succ n
    let b := ((stdOrthonormalBasis ℝ F).reindex (finCongr Fact.out)).adjustToOrientation o
    rw [o.volumeFormL_eq_alternatingFormEquiv_ιMulti b
      (OrthonormalBasis.orientation_adjustToOrientation _ _),
      b.orthonormal.norm_externalWedge_alternatingFormEquiv_ιMulti_right]

/-- **Harvey–Lawson Proposition II.7.10** (volume-form version). Let `o` be an orientation of an
`n`-dimensional real inner product space `E`, `b` a positively oriented orthonormal basis of `E`,
and `ψ` an `l`-form on `F` with `‖ψ‖ ≤ 1` and `n = 0 ∨ ψ 0 ≠ -1`. Then
`o.volumeFormL.externalWedge 2 ψ` calibrates `v : Fin (n + l) → WithLp 2 (E × F)` if and only if
`v` is orthonormal and shares its oriented `(n + l)`-plane with `(b₁, 0), …, (bₙ, 0), (0, w₁), …,
(0, wₗ)` for some calibrated `l`-frame `w` of `ψ`. -/
theorem isCalibratedFrame_externalWedge_volumeFormL_iff [FiniteDimensional ℝ E]
    [Fact (Module.finrank ℝ E = n)] (o : Orientation ℝ E (Fin n))
    (b : OrthonormalBasis (Fin n) ℝ E) (hb : b.toBasis.orientation = o)
    {ψ : F [⋀^Fin l]→L[ℝ] ℝ} (hψ : ‖ψ‖ ≤ 1) (hl : n = 0 ∨ ψ 0 ≠ -1)
    {v : Fin (n + l) → WithLp 2 (E × F)} :
    (o.volumeFormL.externalWedge 2 ψ).IsCalibratedFrame v ↔
      Orthonormal ℝ v ∧
        ∃ w : Fin l → F, ψ.IsCalibratedFrame w ∧
          ιMulti ℝ (n + l) v =
            ιMulti ℝ (n + l)
              (Fin.append (fun i ↦ WithLp.toLp 2 (b i, 0)) (fun j ↦ WithLp.toLp 2 (0, w j))) := by
  rw [o.volumeFormL_eq_alternatingFormEquiv_ιMulti b hb]
  exact ContinuousAlternatingMap.isCalibratedFrame_externalWedge_alternatingFormEquiv_ιMulti_iff
    b.orthonormal hψ hl

end Orientation
