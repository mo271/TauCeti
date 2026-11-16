/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Alternating
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family
public import TauCeti.Analysis.InnerProductSpace.Orientation
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Calibrated frames and equality planes of alternating forms

For a real-valued continuous alternating form `φ` on a real inner product space `E`, an
orthonormal tuple `v : ι → E` is a *calibrated frame* of `φ` (`φ.IsCalibratedFrame v`) when
`φ v = 1`. When `φ` has comass at most one (`‖φ‖ ≤ 1`), calibrated frames are the equality cases
of the comass inequality `φ v ≤ ‖φ‖ ≤ 1` on orthonormal tuples; in particular, the existence of
any calibrated frame forces `‖φ‖ = 1`.

Combining the vectors of a tuple `v` with the rows of a square matrix `A` scales every alternating
map, and hence every simple `k`-vector `v₁ ∧ ⋯ ∧ vₖ`, by `det A`. For two orthonormal `k`-frames
`v` and `e`, equality of their exterior products `v₁ ∧ ⋯ ∧ vₖ = e₁ ∧ ⋯ ∧ eₖ` holds if and only if
`v` lies in the `SO(k)`-orbit of `e` (`Orthonormal.ιMulti_eq_iff_exists_specialOrthogonalGroup`),
so `φ.IsCalibratedFrame` depends only on the oriented `k`-plane `v₁ ∧ ⋯ ∧ vₖ`.

For the unit simple `k`-form `v ↦ ⟪e₁ ∧ ⋯ ∧ eₖ, v₁ ∧ ⋯ ∧ vₖ⟫` attached to an orthonormal frame
`e`, Cauchy–Schwarz in `⋀[ℝ]^k E` shows that its calibrated frames are precisely the orthonormal
frames sharing the oriented `k`-plane `e₁ ∧ ⋯ ∧ eₖ`, equivalently the `SO(k)`-orbit of `e`. In top
degree, the oriented volume form `o.volumeFormL` has comass `1`, agrees with the simple `n`-form of
any positively oriented orthonormal basis, and calibrates precisely the positively oriented
orthonormal bases.

## Main definitions

* `ContinuousAlternatingMap.IsCalibratedFrame`: `Orthonormal ℝ v ∧ φ v = 1`.

## Main results

* `AlternatingMap.map_sum_smul`, `ContinuousAlternatingMap.apply_sum_smul`,
  `exteriorPower.ιMulti_sum_smul`: combining arguments with the rows of `A` multiplies by `A.det`.
* `Orthonormal.ιMulti_eq_iff_exists_specialOrthogonalGroup`: two orthonormal `k`-frames determine
  the same simple `k`-vector if and only if they differ by a matrix in
  `Matrix.specialOrthogonalGroup (Fin k) ℝ`.
* `ContinuousAlternatingMap.isCalibratedFrame_sum_smul_iff_of_mem_specialOrthogonalGroup`:
  invariance of calibrated frames under `SO(ι)`.
* `ContinuousAlternatingMap.isCalibratedFrame_alternatingFormEquiv_ιMulti_iff`,
  `Orthonormal.isCalibratedFrame_alternatingFormEquiv_ιMulti_iff_exists_specialOrthogonalGroup`:
  calibrated frames of a unit simple `k`-form are the orthonormal frames with the same oriented
  `k`-plane.
* `Orientation.norm_volumeFormL`, `Orientation.volumeFormL_eq_alternatingFormEquiv_ιMulti`,
  `Orientation.isCalibratedFrame_volumeFormL_iff`: comass and calibrated frames of the oriented
  volume form.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. 148 (1982), §I–II.
* H. Federer, *Geometric Measure Theory*, Grundlehren der mathematischen Wissenschaften 153,
  Springer, 1969, §1.8.1.
-/

public section

noncomputable section

open Module exteriorPower
open scoped RealInnerProductSpace Matrix

/-! ### Matrix action on alternating maps and orthonormal `k`-frames -/

section MatrixAction

variable {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Fintype ι] [DecidableEq ι]

/-- Combining the vectors of `v : ι → M` with the rows of `A : Matrix ι ι R` scales any
alternating map by `A.det`. -/
theorem AlternatingMap.map_sum_smul (f : M [⋀^ι]→ₗ[R] N) (v : ι → M) (A : Matrix ι ι R) :
    f (fun i ↦ ∑ j, A i j • v j) = A.det • f v := by
  let L : (ι → R) →ₗ[R] M := Fintype.linearCombination R v
  let g : (ι → R) [⋀^ι]→ₗ[R] N := f.compLinearMap L
  let h : (ι → R) [⋀^ι]→ₗ[R] N :=
    (LinearMap.toSpanSingleton R N (f v)).compAlternatingMap Matrix.detRowAlternating
  have hd : Matrix.detRowAlternating ⇑(Pi.basisFun R ι) = 1 := by
    rw [← Pi.basisFun_det, Basis.det_self]
  have hgh : g = h := by
    refine Basis.ext_alternating (Pi.basisFun R ι) fun e he ↦ ?_
    let σ : Equiv.Perm ι := Equiv.ofBijective e (Finite.injective_iff_bijective.1 he)
    have hL (i : ι) : L (Pi.basisFun R ι (σ i)) = v (σ i) := by
      simp [L, Pi.basisFun_apply]
    have hg : g ((Pi.basisFun R ι) ∘ σ) = σ.sign • f v := by
      simpa only [g, AlternatingMap.compLinearMap_apply, Function.comp_def, hL] using
        f.map_perm v σ
    have hh : h ((Pi.basisFun R ι) ∘ σ) = σ.sign • f v := by
      simp [h, AlternatingMap.map_perm, hd, Units.smul_def]
    exact hg.trans hh.symm
  have hA := DFunLike.congr_fun hgh (fun i j ↦ A i j)
  simpa only [g, h, L, AlternatingMap.compLinearMap_apply, LinearMap.compAlternatingMap_apply,
    Function.comp_def, Fintype.linearCombination_apply, LinearMap.toSpanSingleton_apply,
    Matrix.det] using hA

/-- Two `k`-tuples with the same exterior product give the same value under any alternating map. -/
theorem AlternatingMap.eq_of_ιMulti_eq {k : ℕ} (f : M [⋀^Fin k]→ₗ[R] N) {u v : Fin k → M}
    (h : ιMulti R k u = ιMulti R k v) : f u = f v := by
  rw [← alternatingMapLinearEquiv_apply_ιMulti f u, h,
    alternatingMapLinearEquiv_apply_ιMulti f v]

/-- Two `k`-tuples with opposite exterior products give opposite values under any alternating
map. -/
theorem AlternatingMap.eq_neg_of_ιMulti_eq_neg {k : ℕ} (f : M [⋀^Fin k]→ₗ[R] N) {u v : Fin k → M}
    (h : ιMulti R k u = -ιMulti R k v) : f u = -f v := by
  rw [← alternatingMapLinearEquiv_apply_ιMulti f u, h, map_neg,
    alternatingMapLinearEquiv_apply_ιMulti f v]

/-- Combining the vectors of `v : Fin k → M` with the rows of `A : Matrix (Fin k) (Fin k) R`
scales their exterior product `v₁ ∧ ⋯ ∧ vₖ` by `A.det`. -/
theorem exteriorPower.ιMulti_sum_smul {k : ℕ} (v : Fin k → M) (A : Matrix (Fin k) (Fin k) R) :
    ιMulti R k (fun i ↦ ∑ j, A i j • v j) = A.det • ιMulti R k v :=
  (ιMulti R k).map_sum_smul v A

/-- Combining the vectors of `v : ι → M` with the rows of `A : Matrix ι ι R` scales any continuous
alternating map by `A.det`. -/
theorem ContinuousAlternatingMap.apply_sum_smul [TopologicalSpace M] [TopologicalSpace N]
    (φ : M [⋀^ι]→L[R] N) (v : ι → M) (A : Matrix ι ι R) :
    φ (fun i ↦ ∑ j, A i j • v j) = A.det • φ v :=
  φ.toAlternatingMap.map_sum_smul v A

/-- Two `k`-tuples with the same exterior product give the same value under any continuous
alternating map. -/
theorem ContinuousAlternatingMap.apply_eq_of_ιMulti_eq [TopologicalSpace M] [TopologicalSpace N]
    {k : ℕ} (φ : M [⋀^Fin k]→L[R] N) {u v : Fin k → M} (h : ιMulti R k u = ιMulti R k v) :
    φ u = φ v :=
  φ.toAlternatingMap.eq_of_ιMulti_eq h

/-- Two `k`-tuples with opposite exterior products give opposite values under any continuous
alternating map. -/
theorem ContinuousAlternatingMap.apply_eq_neg_of_ιMulti_eq_neg [TopologicalSpace M]
    [TopologicalSpace N] {k : ℕ} (φ : M [⋀^Fin k]→L[R] N) {u v : Fin k → M}
    (h : ιMulti R k u = -ιMulti R k v) : φ u = -φ v :=
  φ.toAlternatingMap.eq_neg_of_ιMulti_eq_neg h

end MatrixAction

section OrthonormalOrbit

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι] [DecidableEq ι]

/-- Over `ℝ`, combining an orthonormal family with the rows of a square matrix `A` yields an
orthonormal family if and only if `A ∈ Matrix.orthogonalGroup ι ℝ`. -/
@[simp]
theorem Orthonormal.orthonormal_sum_smul_iff_mem_orthogonalGroup {e : ι → E}
    (he : Orthonormal ℝ e) (A : Matrix ι ι ℝ) :
    Orthonormal ℝ (fun i ↦ ∑ j, A i j • e j) ↔ A ∈ Matrix.orthogonalGroup ι ℝ := by
  rw [he.orthonormal_sum_smul_iff, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.mem_orthogonalGroup_iff]

/-- If `e` and `v` are orthonormal `ι`-tuples and every `v i` lies in `span(range e)`, then `v` is
obtained from `e` by an orthogonal matrix. -/
theorem Orthonormal.exists_orthogonalGroup_of_mem_span {e v : ι → E}
    (he : Orthonormal ℝ e) (hv : Orthonormal ℝ v)
    (hvU : ∀ i, v i ∈ Submodule.span ℝ (Set.range e)) :
    ∃ A ∈ Matrix.orthogonalGroup ι ℝ, v = fun i ↦ ∑ j, A i j • e j := by
  let U : Submodule ℝ E := Submodule.span ℝ (Set.range e)
  have : FiniteDimensional ℝ U := FiniteDimensional.span_of_finite ℝ (Set.finite_range e)
  let A : Matrix ι ι ℝ := Matrix.of fun i j ↦ ⟪e j, v i⟫
  have hvA : v = fun i ↦ ∑ j, A i j • e j := by
    ext i
    rw [← U.starProjection_eq_self_iff.mpr (hvU i), he.starProjection_apply_eq_sum rfl]
    rfl
  exact ⟨A, (he.orthonormal_sum_smul_iff_mem_orthogonalGroup A).mp (hvA ▸ hv), hvA⟩

/-- Two orthonormal `k`-frames where every vector of `v` lies in `span(range e)` determine the same
unoriented `k`-plane, so their simple `k`-vectors agree up to sign. -/
theorem Orthonormal.ιMulti_eq_or_eq_neg_of_mem_span {k : ℕ} {e v : Fin k → E}
    (he : Orthonormal ℝ e) (hv : Orthonormal ℝ v)
    (hvU : ∀ i, v i ∈ Submodule.span ℝ (Set.range e)) :
    ιMulti ℝ k v = ιMulti ℝ k e ∨ ιMulti ℝ k v = -ιMulti ℝ k e := by
  obtain ⟨A, hAo, hvA⟩ := he.exists_orthogonalGroup_of_mem_span hv hvU
  have hdet_sq : A.det * A.det = 1 := by
    simpa [Matrix.det_transpose] using
      congrArg Matrix.det ((Matrix.mem_orthogonalGroup_iff (Fin k) ℝ).mp hAo)
  rcases mul_self_eq_one_iff.mp hdet_sq with hdet | hdet
  · exact Or.inl (by rw [hvA, exteriorPower.ιMulti_sum_smul, hdet, one_smul])
  · refine Or.inr ?_
    rw [hvA, exteriorPower.ιMulti_sum_smul, hdet]
    exact neg_one_smul ℝ (ιMulti ℝ k e)

private theorem Orthonormal.exists_orthogonalGroup_of_ιMulti_eq_smul {k : ℕ} {e v : Fin k → E}
    (he : Orthonormal ℝ e) (hv : Orthonormal ℝ v) {c : ℝ} (hc : c ≠ 0)
    (h : ιMulti ℝ k v = c • ιMulti ℝ k e) :
    ∃ A ∈ Matrix.orthogonalGroup (Fin k) ℝ, A.det = c ∧ v = fun i ↦ ∑ j, A i j • e j := by
  have hvU (i : Fin k) : v i ∈ Submodule.span ℝ (Set.range e) := by
    rw [TauCeti.exteriorPower.mem_span_range_iff_ι_mul_ιMulti_eq_zero he.linearIndependent]
    have hvi : v i ∈ Submodule.span ℝ (Set.range v) := Submodule.subset_span (Set.mem_range_self i)
    rw [TauCeti.exteriorPower.mem_span_range_iff_ι_mul_ιMulti_eq_zero hv.linearIndependent] at hvi
    have hcoe : (ιMulti ℝ k v : ExteriorAlgebra ℝ E) = c • (ιMulti ℝ k e : ExteriorAlgebra ℝ E) :=
      congrArg Subtype.val h
    rwa [hcoe, mul_smul_comm, smul_eq_zero_iff_right hc] at hvi
  obtain ⟨A, hAo, hvA⟩ := he.exists_orthogonalGroup_of_mem_span hv hvU
  have he0 : ιMulti ℝ k e ≠ 0 := (ιMulti_ne_zero_iff e).mpr he.linearIndependent
  have hdet : A.det = c := by
    rw [hvA, exteriorPower.ιMulti_sum_smul] at h
    exact smul_left_injective ℝ he0 h
  exact ⟨A, hAo, hdet, hvA⟩

/-- Two orthonormal `k`-frames determine the same simple `k`-vector if and only if one is obtained
from the other by a matrix in `Matrix.specialOrthogonalGroup (Fin k) ℝ`. -/
theorem Orthonormal.ιMulti_eq_iff_exists_specialOrthogonalGroup {k : ℕ} {e v : Fin k → E}
    (he : Orthonormal ℝ e) :
    Orthonormal ℝ v ∧ ιMulti ℝ k v = ιMulti ℝ k e ↔
      ∃ A ∈ Matrix.specialOrthogonalGroup (Fin k) ℝ, v = fun i ↦ ∑ j, A i j • e j := by
  refine ⟨fun ⟨hv, h⟩ ↦ ?_, ?_⟩
  · obtain ⟨A, hAo, hdet, hvA⟩ :=
      he.exists_orthogonalGroup_of_ιMulti_eq_smul hv one_ne_zero (by simpa using h)
    exact ⟨A, Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨hAo, hdet⟩, hvA⟩
  · rintro ⟨A, hA, rfl⟩
    rw [Matrix.mem_specialOrthogonalGroup_iff] at hA
    exact ⟨(he.orthonormal_sum_smul_iff_mem_orthogonalGroup A).mpr hA.1,
      by rw [exteriorPower.ιMulti_sum_smul, hA.2, one_smul]⟩

/-- Two orthonormal `k`-frames determine opposite simple `k`-vectors if and only if one is obtained
from the other by an orthogonal matrix of determinant `-1`. -/
theorem Orthonormal.ιMulti_eq_neg_iff_exists_orthogonalGroup {k : ℕ} {e v : Fin k → E}
    (he : Orthonormal ℝ e) :
    Orthonormal ℝ v ∧ ιMulti ℝ k v = -ιMulti ℝ k e ↔
      ∃ A ∈ Matrix.orthogonalGroup (Fin k) ℝ, A.det = -1 ∧ v = fun i ↦ ∑ j, A i j • e j := by
  refine ⟨fun ⟨hv, h⟩ ↦ ?_, ?_⟩
  · exact he.exists_orthogonalGroup_of_ιMulti_eq_smul hv (by norm_num)
      (h.trans (neg_one_smul ℝ (ιMulti ℝ k e)).symm)
  · rintro ⟨A, hAo, hdet, rfl⟩
    refine ⟨(he.orthonormal_sum_smul_iff_mem_orthogonalGroup A).mpr hAo, ?_⟩
    rw [exteriorPower.ιMulti_sum_smul, hdet]
    exact neg_one_smul ℝ (ιMulti ℝ k e)

end OrthonormalOrbit

/-- Negating a single vector of an indexed family preserves `Orthonormal`. -/
@[simp]
theorem TauCeti.orthonormal_update_neg_iff {𝕜 G ι : Type*} [RCLike 𝕜] [SeminormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] [DecidableEq ι] (v : ι → G) (i : ι) :
    Orthonormal 𝕜 (Function.update v i (-v i)) ↔ Orthonormal 𝕜 v := by
  simp only [orthonormal_iff_ite, Function.update_apply]
  refine forall_congr' fun a ↦ forall_congr' fun b ↦ ?_
  by_cases ha : a = i <;> by_cases hb : b = i
  · subst ha hb
    simp
  · subst ha
    simp [hb, Ne.symm hb]
  · subst hb
    simp [ha]
  · simp [ha, hb]

/-! ### Calibrated frames of continuous alternating forms -/

namespace ContinuousAlternatingMap

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*}

/-- An `ι`-tuple `v` in a real inner product space `E` is a *calibrated frame* of a real-valued
continuous alternating form `φ` when `v` is orthonormal and `φ v = 1`. When `‖φ‖ ≤ 1`, these are
the orthonormal frames achieving equality in `φ v ≤ ‖φ‖ ≤ 1`. -/
def IsCalibratedFrame (φ : E [⋀^ι]→L[ℝ] ℝ) (v : ι → E) : Prop :=
  Orthonormal ℝ v ∧ φ v = 1

theorem isCalibratedFrame_iff {φ : E [⋀^ι]→L[ℝ] ℝ} {v : ι → E} :
    φ.IsCalibratedFrame v ↔ Orthonormal ℝ v ∧ φ v = 1 :=
  Iff.rfl

theorem IsCalibratedFrame.orthonormal {φ : E [⋀^ι]→L[ℝ] ℝ} {v : ι → E}
    (h : φ.IsCalibratedFrame v) : Orthonormal ℝ v :=
  h.1

theorem IsCalibratedFrame.apply_eq_one {φ : E [⋀^ι]→L[ℝ] ℝ} {v : ι → E}
    (h : φ.IsCalibratedFrame v) : φ v = 1 :=
  h.2

theorem IsCalibratedFrame.linearIndependent {φ : E [⋀^ι]→L[ℝ] ℝ} {v : ι → E}
    (h : φ.IsCalibratedFrame v) : LinearIndependent ℝ v :=
  h.orthonormal.linearIndependent

theorem IsCalibratedFrame.ne_zero {φ : E [⋀^ι]→L[ℝ] ℝ} {v : ι → E}
    (h : φ.IsCalibratedFrame v) : φ ≠ 0 := by
  rintro rfl
  have h1 := h.apply_eq_one
  simp at h1

@[simp]
theorem not_isCalibratedFrame_zero (v : ι → E) :
    ¬(0 : E [⋀^ι]→L[ℝ] ℝ).IsCalibratedFrame v :=
  fun h ↦ h.ne_zero rfl

/-- On an empty index type, `φ` calibrates `v` if and only if `φ v = 1`. -/
@[simp]
theorem isCalibratedFrame_of_isEmpty [IsEmpty ι] (φ : E [⋀^ι]→L[ℝ] ℝ) (v : ι → E) :
    φ.IsCalibratedFrame v ↔ φ v = 1 :=
  ⟨IsCalibratedFrame.apply_eq_one,
    fun h ↦ ⟨orthonormal_iff_ite.mpr fun i ↦ isEmptyElim i, h⟩⟩

/-- If `φ` admits a calibrated frame on a finite index type, then `1 ≤ ‖φ‖`. -/
theorem IsCalibratedFrame.one_le_norm [Fintype ι] {φ : E [⋀^ι]→L[ℝ] ℝ} {v : ι → E}
    (h : φ.IsCalibratedFrame v) : 1 ≤ ‖φ‖ := by
  simpa [h.apply_eq_one, h.orthonormal.norm_eq_one] using φ.le_opNorm v

/-- If `‖φ‖ ≤ 1` and `φ` admits a calibrated frame, then `φ` has comass `1`. -/
theorem IsCalibratedFrame.norm_eq_one_of_le_one [Fintype ι] {φ : E [⋀^ι]→L[ℝ] ℝ} {v : ι → E}
    (h : φ.IsCalibratedFrame v) (hle : ‖φ‖ ≤ 1) : ‖φ‖ = 1 :=
  le_antisymm hle h.one_le_norm

/-- The cardinality of any finite calibrated frame of `φ` is at most `finrank ℝ E`. -/
theorem IsCalibratedFrame.card_le_finrank [Fintype ι] [FiniteDimensional ℝ E]
    {φ : E [⋀^ι]→L[ℝ] ℝ} {v : ι → E} (h : φ.IsCalibratedFrame v) :
    Fintype.card ι ≤ Module.finrank ℝ E :=
  h.linearIndependent.fintype_card_le_finrank

/-- The degree of a form admitting a calibrated `k`-frame is at most `finrank ℝ E`. -/
theorem IsCalibratedFrame.le_finrank [FiniteDimensional ℝ E] {k : ℕ}
    {φ : E [⋀^Fin k]→L[ℝ] ℝ} {v : Fin k → E} (h : φ.IsCalibratedFrame v) :
    k ≤ Module.finrank ℝ E := by
  simpa using h.card_le_finrank

/-- Above the dimension of `E`, no `k`-form admits a calibrated frame. -/
theorem not_isCalibratedFrame_of_finrank_lt [FiniteDimensional ℝ E] {k : ℕ}
    (hk : Module.finrank ℝ E < k) (φ : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E) :
    ¬φ.IsCalibratedFrame v :=
  fun h ↦ hk.not_ge h.le_finrank

/-- Pulling `φ` back along any linear isometry `f : E' →ₗᵢ[ℝ] E` preserves calibrated frames:
`v` is calibrated for `f* φ` if and only if `f ∘ v` is calibrated for `φ`. -/
@[simp]
theorem isCalibratedFrame_compLinearIsometry_iff {E' : Type*}
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (φ : E [⋀^ι]→L[ℝ] ℝ) (f : E' →ₗᵢ[ℝ] E) (v : ι → E') :
    (φ.compContinuousLinearMap f.toContinuousLinearMap).IsCalibratedFrame v ↔
      φ.IsCalibratedFrame (f ∘ v) := by
  simp [IsCalibratedFrame, f.orthonormal_comp_iff]

/-- Pulling `φ` back along a linear isometric equivalence `f : E' ≃ₗᵢ[ℝ] E` preserves calibrated
frames. -/
@[simp]
theorem isCalibratedFrame_compLinearIsometryEquiv_iff {E' : Type*}
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (φ : E [⋀^ι]→L[ℝ] ℝ) (f : E' ≃ₗᵢ[ℝ] E) (v : ι → E') :
    (φ.compContinuousLinearMap (f : E' →L[ℝ] E)).IsCalibratedFrame v ↔
      φ.IsCalibratedFrame (f ∘ v) :=
  isCalibratedFrame_compLinearIsometry_iff φ f.toLinearIsometry v

section Symmetries

section Fintype

variable [Fintype ι] [DecidableEq ι]

private theorem orthonormal_of_sum_smul_mem_orthogonalGroup {A : Matrix ι ι ℝ}
    (hAo : A ∈ Matrix.orthogonalGroup ι ℝ) {v : ι → E}
    (hv' : Orthonormal ℝ (fun i ↦ ∑ j, A i j • v j)) : Orthonormal ℝ v := by
  have hmul : Aᵀ * A = 1 := (Matrix.mem_orthogonalGroup_iff' ι ℝ).mp hAo
  have hAt : Aᵀ ∈ Matrix.orthogonalGroup ι ℝ := by
    rwa [Matrix.mem_orthogonalGroup_iff, Matrix.transpose_transpose]
  have hinv : (fun i ↦ ∑ j, Aᵀ i j • ∑ l, A j l • v l) = v := by
    ext i
    simp_rw [Finset.smul_sum, ← smul_assoc, smul_eq_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, hmul, Matrix.one_apply, ite_smul, one_smul,
      zero_smul]
    simp
  rw [← hinv]
  exact (hv'.orthonormal_sum_smul_iff_mem_orthogonalGroup Aᵀ).mpr hAt

/-- Transforming a tuple by `A ∈ Matrix.specialOrthogonalGroup ι ℝ` preserves
`IsCalibratedFrame`. -/
@[simp]
theorem isCalibratedFrame_sum_smul_iff_of_mem_specialOrthogonalGroup
    (φ : E [⋀^ι]→L[ℝ] ℝ) {A : Matrix ι ι ℝ} (hA : A ∈ Matrix.specialOrthogonalGroup ι ℝ)
    (v : ι → E) :
    φ.IsCalibratedFrame (fun i ↦ ∑ j, A i j • v j) ↔ φ.IsCalibratedFrame v := by
  obtain ⟨hAo, hdet⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp hA
  refine ⟨fun ⟨hv', hφ'⟩ ↦ ?_, fun ⟨hv, hφ⟩ ↦ ?_⟩
  · rw [φ.apply_sum_smul, hdet, one_smul] at hφ'
    exact ⟨orthonormal_of_sum_smul_mem_orthogonalGroup hAo hv', hφ'⟩
  · exact ⟨(hv.orthonormal_sum_smul_iff_mem_orthogonalGroup A).mpr hAo,
      by rw [φ.apply_sum_smul, hdet, one_smul, hφ]⟩

/-- Transforming a tuple by an orthogonal matrix of determinant `-1` sends calibrated frames of `φ`
to calibrated frames of `-φ` and conversely. -/
theorem isCalibratedFrame_neg_sum_smul_iff_of_mem_orthogonalGroup
    (φ : E [⋀^ι]→L[ℝ] ℝ) {A : Matrix ι ι ℝ} (hAo : A ∈ Matrix.orthogonalGroup ι ℝ)
    (hdet : A.det = -1) (v : ι → E) :
    (-φ).IsCalibratedFrame (fun i ↦ ∑ j, A i j • v j) ↔ φ.IsCalibratedFrame v := by
  refine ⟨fun ⟨hv', hφ'⟩ ↦ ?_, fun ⟨hv, hφ⟩ ↦ ?_⟩
  · rw [neg_apply, φ.apply_sum_smul, hdet, neg_one_smul, neg_neg] at hφ'
    exact ⟨orthonormal_of_sum_smul_mem_orthogonalGroup hAo hv', hφ'⟩
  · refine ⟨(hv.orthonormal_sum_smul_iff_mem_orthogonalGroup A).mpr hAo, ?_⟩
    rw [neg_apply, φ.apply_sum_smul, hdet, neg_one_smul, hφ, neg_neg]

/-- Even permutations preserve `IsCalibratedFrame`. -/
theorem isCalibratedFrame_comp_perm_iff (φ : E [⋀^ι]→L[ℝ] ℝ) {σ : Equiv.Perm ι}
    (hσ : Equiv.Perm.sign σ = 1) (v : ι → E) :
    φ.IsCalibratedFrame (v ∘ σ) ↔ φ.IsCalibratedFrame v := by
  have horth : Orthonormal ℝ (v ∘ σ) ↔ Orthonormal ℝ v :=
    ⟨fun h ↦ by simpa [Function.comp_def] using h.comp σ.symm σ.symm.injective,
      fun h ↦ h.comp σ σ.injective⟩
  have hval : φ (v ∘ σ) = φ v := by
    simpa [hσ] using φ.toAlternatingMap.map_perm v σ
  rw [IsCalibratedFrame, IsCalibratedFrame, horth, hval]

/-- Odd permutations exchange calibrated frames of `φ` and `-φ`. -/
theorem isCalibratedFrame_neg_comp_perm_iff (φ : E [⋀^ι]→L[ℝ] ℝ) {σ : Equiv.Perm ι}
    (hσ : Equiv.Perm.sign σ = -1) (v : ι → E) :
    (-φ).IsCalibratedFrame (v ∘ σ) ↔ φ.IsCalibratedFrame v := by
  have horth : Orthonormal ℝ (v ∘ σ) ↔ Orthonormal ℝ v :=
    ⟨fun h ↦ by simpa [Function.comp_def] using h.comp σ.symm σ.symm.injective,
      fun h ↦ h.comp σ σ.injective⟩
  have hval : (-φ) (v ∘ σ) = φ v := by
    rw [neg_apply]
    have hp := φ.toAlternatingMap.map_perm v σ
    rw [coe_toAlternatingMap, hσ, Units.neg_smul, one_smul] at hp
    rw [hp, neg_neg]
  rw [IsCalibratedFrame, IsCalibratedFrame, horth, hval]

end Fintype

/-- Negating a single vector of a frame exchanges calibrated frames of `φ` and `-φ`. -/
@[simp]
theorem isCalibratedFrame_neg_update_neg_iff [DecidableEq ι]
    (φ : E [⋀^ι]→L[ℝ] ℝ) (v : ι → E) (i : ι) :
    (-φ).IsCalibratedFrame (Function.update v i (-v i)) ↔ φ.IsCalibratedFrame v := by
  have hval : (-φ) (Function.update v i (-v i)) = φ v := by
    have hp := φ.toAlternatingMap.map_update_neg v i (v i)
    rw [Function.update_eq_self, coe_toAlternatingMap] at hp
    rw [neg_apply, hp, neg_neg]
  rw [IsCalibratedFrame, IsCalibratedFrame, TauCeti.orthonormal_update_neg_iff, hval]

end Symmetries

/-- `IsCalibratedFrame` depends only on the simple `k`-vector `v₁ ∧ ⋯ ∧ vₖ` of the orthonormal
frame `v`. -/
theorem IsCalibratedFrame.of_ιMulti_eq {k : ℕ} {φ : E [⋀^Fin k]→L[ℝ] ℝ} {u v : Fin k → E}
    (hu : φ.IsCalibratedFrame u) (hv : Orthonormal ℝ v)
    (h : ιMulti ℝ k v = ιMulti ℝ k u) : φ.IsCalibratedFrame v :=
  ⟨hv, (φ.apply_eq_of_ιMulti_eq h).trans hu.apply_eq_one⟩

/-- Reversing the orientation `v₁ ∧ ⋯ ∧ vₖ = -(u₁ ∧ ⋯ ∧ uₖ)` sends a calibrated frame of `φ` to a
calibrated frame of `-φ`. -/
theorem IsCalibratedFrame.neg_of_ιMulti_eq_neg {k : ℕ} {φ : E [⋀^Fin k]→L[ℝ] ℝ} {u v : Fin k → E}
    (hu : φ.IsCalibratedFrame u) (hv : Orthonormal ℝ v)
    (h : ιMulti ℝ k v = -ιMulti ℝ k u) : (-φ).IsCalibratedFrame v :=
  ⟨hv, by rw [neg_apply, φ.apply_eq_neg_of_ιMulti_eq_neg h, hu.apply_eq_one, neg_neg]⟩

end General

/-! ### Simple `k`-forms and oriented volume forms -/

section SimpleForms

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {k : ℕ}

/-- The form `v ↦ ⟪u₁ ∧ ⋯ ∧ uₖ, v₁ ∧ ⋯ ∧ vₖ⟫` of a simple `k`-vector is invariant under
precomposition with the orthogonal projection onto any subspace containing all the `uᵢ`. -/
theorem _root_.TauCeti.alternatingFormEquiv_ιMulti_comp_starProjection (u : Fin k → E)
    (U : Submodule ℝ E) [U.HasOrthogonalProjection] (hu : ∀ i, u i ∈ U) :
    (TauCeti.alternatingFormEquiv E k (ιMulti ℝ k u)).compContinuousLinearMap U.starProjection =
      TauCeti.alternatingFormEquiv E k (ιMulti ℝ k u) := by
  ext v
  simp only [compContinuousLinearMap_apply, Function.comp_def,
    TauCeti.alternatingFormEquiv_ιMulti_apply]
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [← U.inner_starProjection_left_eq_right, U.starProjection_eq_self_iff.mpr (hu j)]

/-- An orthonormal `k`-frame `e` is calibrated by its own simple `k`-form
`TauCeti.alternatingFormEquiv E k (ιMulti ℝ k e)`. -/
theorem isCalibratedFrame_alternatingFormEquiv_ιMulti_self {e : Fin k → E}
    (he : Orthonormal ℝ e) :
    (TauCeti.alternatingFormEquiv E k (ιMulti ℝ k e)).IsCalibratedFrame e := by
  refine ⟨he, ?_⟩
  rw [TauCeti.alternatingFormEquiv_apply, real_inner_self_eq_norm_sq, he.norm_ιMulti, one_pow]

/-- **Calibrated frames of a unit simple `k`-form (oriented-plane form).** For an orthonormal
`k`-frame `e`, the form `v ↦ ⟪e₁ ∧ ⋯ ∧ eₖ, v₁ ∧ ⋯ ∧ vₖ⟫` calibrates an `ℝ`-tuple `v` if and only
if `v` is orthonormal and `v₁ ∧ ⋯ ∧ vₖ = e₁ ∧ ⋯ ∧ eₖ`. -/
theorem isCalibratedFrame_alternatingFormEquiv_ιMulti_iff {e : Fin k → E}
    (he : Orthonormal ℝ e) {v : Fin k → E} :
    (TauCeti.alternatingFormEquiv E k (ιMulti ℝ k e)).IsCalibratedFrame v ↔
      Orthonormal ℝ v ∧ ιMulti ℝ k v = ιMulti ℝ k e := by
  refine ⟨fun ⟨hv, hval⟩ ↦ ⟨hv, ?_⟩, fun ⟨hv, h⟩ ↦
    (isCalibratedFrame_alternatingFormEquiv_ιMulti_self he).of_ιMulti_eq hv h⟩
  rw [TauCeti.alternatingFormEquiv_apply] at hval
  have hsq : ‖ιMulti ℝ k v - ιMulti ℝ k e‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, hv.norm_ιMulti, he.norm_ιMulti, real_inner_comm, hval]
    ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))

/-- The negated unit simple `k`-form `-TauCeti.alternatingFormEquiv E k (ιMulti ℝ k e)` calibrates
`v` if and only if `v` is orthonormal and `v₁ ∧ ⋯ ∧ vₖ = -(e₁ ∧ ⋯ ∧ eₖ)`. -/
theorem isCalibratedFrame_neg_alternatingFormEquiv_ιMulti_iff {e : Fin k → E}
    (he : Orthonormal ℝ e) {v : Fin k → E} :
    (-TauCeti.alternatingFormEquiv E k (ιMulti ℝ k e)).IsCalibratedFrame v ↔
      Orthonormal ℝ v ∧ ιMulti ℝ k v = -ιMulti ℝ k e := by
  refine ⟨fun ⟨hv, hval⟩ ↦ ⟨hv, ?_⟩, fun ⟨hv, h⟩ ↦
    (isCalibratedFrame_alternatingFormEquiv_ιMulti_self he).neg_of_ιMulti_eq_neg hv h⟩
  rw [neg_apply, TauCeti.alternatingFormEquiv_apply, neg_eq_iff_eq_neg] at hval
  have hsq : ‖ιMulti ℝ k v + ιMulti ℝ k e‖ ^ 2 = 0 := by
    rw [norm_add_sq_real, hv.norm_ιMulti, he.norm_ιMulti, real_inner_comm, hval]
    ring
  exact eq_neg_iff_add_eq_zero.mpr (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))

end SimpleForms

end ContinuousAlternatingMap

namespace Orthonormal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {k : ℕ}

/-- The simple `k`-form attached to an orthonormal `k`-frame has comass `1`. -/
theorem norm_alternatingFormEquiv_ιMulti {e : Fin k → E} (he : Orthonormal ℝ e) :
    ‖TauCeti.alternatingFormEquiv E k (ιMulti ℝ k e)‖ = 1 := by
  rw [TauCeti.norm_alternatingFormEquiv_ιMulti, he.norm_ιMulti]

/-- **Calibrated frames of a unit simple `k`-form (`SO(k)`-orbit form).** For an orthonormal
`k`-frame `e`, the calibrated frames of `TauCeti.alternatingFormEquiv E k (ιMulti ℝ k e)` are
precisely the `SO(k)`-transforms of `e`. -/
theorem isCalibratedFrame_alternatingFormEquiv_ιMulti_iff_exists_specialOrthogonalGroup
    {e : Fin k → E} (he : Orthonormal ℝ e) {v : Fin k → E} :
    (TauCeti.alternatingFormEquiv E k (ιMulti ℝ k e)).IsCalibratedFrame v ↔
      ∃ A ∈ Matrix.specialOrthogonalGroup (Fin k) ℝ, v = fun i ↦ ∑ j, A i j • e j :=
  (ContinuousAlternatingMap.isCalibratedFrame_alternatingFormEquiv_ιMulti_iff he).trans
    he.ιMulti_eq_iff_exists_specialOrthogonalGroup

end Orthonormal

namespace Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (Module.finrank ℝ E = n)]

/-- Reversing the orientation negates the continuous volume form `volumeFormL`. -/
@[simp]
theorem volumeFormL_neg (o : Orientation ℝ E (Fin n)) : (-o).volumeFormL = -o.volumeFormL := by
  ext v
  simp [volumeForm_neg_orientation]

/-- The continuous oriented volume form `o.volumeFormL` has comass `1`. -/
@[simp]
theorem norm_volumeFormL (o : Orientation ℝ E (Fin n)) : ‖o.volumeFormL‖ = 1 := by
  rcases n with - | n
  · refine le_antisymm ?_ ?_
    · rw [ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal zero_le_one]
      intro v _
      rcases o.eq_or_eq_neg_of_isEmpty with rfl | rfl <;> simp
    · have hval : |o.volumeForm ![]| = 1 := by
        rcases o.eq_or_eq_neg_of_isEmpty with rfl | rfl <;> simp
      simpa [Real.norm_eq_abs, hval] using o.volumeFormL.le_opNorm (![] : Fin 0 → E)
  · have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
    let b := ((stdOrthonormalBasis ℝ E).reindex (finCongr Fact.out)).adjustToOrientation o
    rw [o.volumeFormL.norm_eq_norm_apply_orthonormalBasis b,
      o.volumeFormL_apply_orthonormal b (OrthonormalBasis.orientation_adjustToOrientation _ _),
      norm_one]

/-- An orthonormal basis `b` is calibrated by `o.volumeFormL` if and only if `b` is positively
oriented for `o`. -/
@[simp]
theorem isCalibratedFrame_volumeFormL_coe_orthonormalBasis_iff (o : Orientation ℝ E (Fin n))
    (b : OrthonormalBasis (Fin n) ℝ E) :
    o.volumeFormL.IsCalibratedFrame b ↔ b.toBasis.orientation = o := by
  refine ⟨fun h ↦ ?_, fun hb ↦ ⟨b.orthonormal, o.volumeFormL_apply_orthonormal b hb⟩⟩
  have hpos : (0 : ℝ) < o.volumeForm b.toBasis := by
    rw [OrthonormalBasis.coe_toBasis, ← o.volumeFormL_apply, h.apply_eq_one]
    exact zero_lt_one
  exact o.volumeForm_apply_pos_iff.mp hpos

/-- On a finite-dimensional space, `o.volumeFormL` equals the simple `n`-form attached to any
positively oriented orthonormal basis. -/
theorem volumeFormL_eq_alternatingFormEquiv_ιMulti [FiniteDimensional ℝ E]
    (o : Orientation ℝ E (Fin n)) (b : OrthonormalBasis (Fin n) ℝ E)
    (hb : b.toBasis.orientation = o) :
    o.volumeFormL = TauCeti.alternatingFormEquiv E n (ιMulti ℝ n b) :=
  (o.eq_volumeFormL_of_apply_orthonormal _ b hb
    (ContinuousAlternatingMap.isCalibratedFrame_alternatingFormEquiv_ιMulti_self
      b.orthonormal).apply_eq_one).symm

/-- On a finite-dimensional space, `o.volumeFormL` calibrates `v` if and only if `v` is a
positively oriented orthonormal basis of `E`. -/
theorem isCalibratedFrame_volumeFormL_iff [FiniteDimensional ℝ E]
    (o : Orientation ℝ E (Fin n)) {v : Fin n → E} :
    o.volumeFormL.IsCalibratedFrame v ↔
      ∃ b : OrthonormalBasis (Fin n) ℝ E, b.toBasis.orientation = o ∧ ⇑b = v := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases n with - | n
    · let b : OrthonormalBasis (Fin 0) ℝ E := (stdOrthonormalBasis ℝ E).reindex (finCongr Fact.out)
      have hb : ⇑b = v := Subsingleton.elim _ _
      exact ⟨b, (o.isCalibratedFrame_volumeFormL_coe_orthonormalBasis_iff b).mp (hb ▸ h), hb⟩
    · have hcard : Fintype.card (Fin (n + 1)) = Module.finrank ℝ E := by
        simp [Fact.out (p := Module.finrank ℝ E = n + 1)]
      let b : OrthonormalBasis (Fin (n + 1)) ℝ E :=
        OrthonormalBasis.mk h.orthonormal
          (h.linearIndependent.span_eq_top_of_card_eq_finrank hcard).ge
      have hb : ⇑b = v := by
        ext i
        simp [b]
      exact ⟨b, (o.isCalibratedFrame_volumeFormL_coe_orthonormalBasis_iff b).mp (hb ▸ h), hb⟩
  · rintro ⟨b, hb, rfl⟩
    exact (o.isCalibratedFrame_volumeFormL_coe_orthonormalBasis_iff b).mpr hb

end Orientation
