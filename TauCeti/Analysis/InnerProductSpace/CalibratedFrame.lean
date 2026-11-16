/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Orientation
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Alternating
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# Calibrated orthonormal frames and top-degree volume pairings

Let `E` be a real inner product space and let `φ : E [⋀^Fin k]→L[ℝ] ℝ` be a continuous alternating
`k`-form. Following Harvey and Lawson, an ordered `k`-frame `v : Fin k → E` is *calibrated* by `φ`
(`TauCeti.IsCalibratedFrame φ v`) when `v` is orthonormal and `φ v = 1`. When `φ` has comass at
most one (`‖φ‖ ≤ 1`), a calibrated frame attains the comass bound `|φ v| ≤ 1` with positive sign,
witnessing `‖φ‖ = 1`.

This file develops the pointwise linear algebra of calibrated frames together with the top-degree
pairing against the oriented volume form `Orientation.volumeFormL` that underlies the calibration
inequality on Riemannian manifolds.

* **Basic properties and comass interaction.** Every calibrated frame is orthonormal and linearly
  independent, forces `1 ≤ ‖φ‖` (`TauCeti.IsCalibratedFrame.one_le_norm`), and therefore forces
  `‖φ‖ = 1` whenever `‖φ‖ ≤ 1` (`TauCeti.IsCalibratedFrame.norm_eq_one`). No frame is calibrated
  by `0`, by a form of comass strictly below `1`, or in degrees strictly above `finrank ℝ E`.
* **Orientation and frame symmetries.** Even permutations of `Fin k` preserve `IsCalibratedFrame`,
  while odd permutations (such as transpositions) and single-slot sign flips calibrate `-φ`. More
  generally, any two orthonormal bases of the same oriented `k`-plane have equal evaluation under
  every real continuous alternating map
  (`ContinuousAlternatingMap.apply_orthonormalBasis_eq_of_orientation_eq`), so `IsCalibratedFrame`
  depends only on the oriented `k`-plane spanned by the frame
  (`TauCeti.isCalibratedFrame_comp_orthonormalBasis_iff_of_orientation_eq`).
* **Top-degree volume form and simple calibrations.** An orthonormal basis `b` of an oriented
  `n`-dimensional space `(E, o)` is calibrated by `o.volumeFormL` if and only if `b` is positively
  oriented (`TauCeti.isCalibratedFrame_volumeFormL_iff`). Pairing any top-degree form `ω` against
  `o.volumeFormL` via `TauCeti.alternatingFormInner` extracts its unique scalar density:
  `⟨vol_o, ω⟩ • vol_o = ω`, `|⟨vol_o, ω⟩| = ‖ω‖`, and `⟨vol_o, ω⟩ = 1 ↔ ω = vol_o`. For a simple
  unit `k`-form `alternatingFormEquiv E k (u₁ ∧ ⋯ ∧ uₖ)` built from an orthonormal frame `u`, the
  calibrated frames are precisely the orthonormal frames with exterior product `u₁ ∧ ⋯ ∧ uₖ`
  (`TauCeti.isCalibratedFrame_alternatingFormEquiv_ιMulti_iff`).

## Main definitions

* `TauCeti.IsCalibratedFrame`: an orthonormal `k`-frame `v : Fin k → E` with `φ v = 1`.

## Main results

* `TauCeti.IsCalibratedFrame.norm_eq_one`: if `IsCalibratedFrame φ v` and `‖φ‖ ≤ 1`, then `‖φ‖ = 1`.
* `ContinuousAlternatingMap.apply_orthonormalBasis_eq_of_orientation_eq`: positively co-oriented
  orthonormal bases have equal evaluation under any real continuous alternating map.
* `TauCeti.isCalibratedFrame_volumeFormL_iff`:
  `IsCalibratedFrame o.volumeFormL b ↔ b.toBasis.orientation = o`.
* `Orientation.alternatingFormInner_volumeFormL_smul`,
  `Orientation.abs_alternatingFormInner_volumeFormL`,
  `Orientation.alternatingFormInner_volumeFormL_eq_one_iff`: top-degree scalar decomposition and
  equality characterization against `o.volumeFormL`.
* `TauCeti.isCalibratedFrame_alternatingFormEquiv_ιMulti_iff`: Grassmannian characterization of
  frames calibrated by a simple unit `k`-form.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157, §I.1 and
  §II.1.
* D. D. Joyce, *Riemannian Holonomy Groups and Calibrated Geometry*, Oxford University Press, 2007,
  §4.1.
-/

public section

noncomputable section

open Module exteriorPower
open scoped RealInnerProductSpace

namespace ContinuousAlternatingMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- Two orthonormal bases of `E` indexed by `Fin n` that induce the same orientation have the same
value under every real continuous alternating map. -/
theorem apply_orthonormalBasis_eq_of_orientation_eq (ω : E [⋀^Fin n]→L[ℝ] ℝ)
    (b b' : OrthonormalBasis (Fin n) ℝ E)
    (horient : b.toBasis.orientation = b'.toBasis.orientation) :
    ω b = ω b' := by
  have : Fact (finrank ℝ E = n) := ⟨by rw [finrank_eq_card_basis b.toBasis, Fintype.card_fin]⟩
  have hdet : b.toBasis.det b' = 1 := by
    rw [← b.toBasis.orientation.volumeForm_robust b rfl, ← Orientation.volumeFormL_apply]
    exact b.toBasis.orientation.volumeFormL_apply_orthonormal b' horient.symm
  rw [ω.apply_eq_det_mul b.toBasis b', hdet, one_mul]
  rfl

end ContinuousAlternatingMap

namespace Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n)]

omit [FiniteDimensional ℝ E] in
/-- On any orthonormal basis `b` indexed by `Fin n`, `o.volumeFormL b` has square `1`. -/
private theorem volumeFormL_apply_mul_self (o : Orientation ℝ E (Fin n))
    (b : OrthonormalBasis (Fin n) ℝ E) :
    o.volumeFormL b * o.volumeFormL b = 1 := by
  have habs : |o.volumeFormL b| = 1 := by
    rcases n with - | n
    · refine o.eq_or_eq_neg_of_isEmpty.elim ?_ ?_ <;> rintro rfl <;> simp
    · simpa using o.abs_volumeForm_apply_of_orthonormal b
  rw [← sq, ← sq_abs, habs, one_pow]

/-- The oriented volume form has unit Hilbert norm in `TauCeti.alternatingFormInner` in every
dimension `n ≥ 0`. -/
@[simp]
theorem alternatingFormInner_volumeFormL_self (o : Orientation ℝ E (Fin n)) :
    TauCeti.alternatingFormInner E n o.volumeFormL o.volumeFormL = 1 := by
  let b : OrthonormalBasis (Fin n) ℝ E := (stdOrthonormalBasis ℝ E).reindex (finCongr Fact.out)
  rw [TauCeti.alternatingFormInner_eq_mul_apply_orthonormalBasis b]
  exact o.volumeFormL_apply_mul_self b

/-- Every continuous top-degree real form `ω` on `(E, o)` is reconstructed from its inner product
with `o.volumeFormL`: `⟨vol_o, ω⟩ • vol_o = ω`. -/
@[simp]
theorem alternatingFormInner_volumeFormL_smul (o : Orientation ℝ E (Fin n))
    (ω : E [⋀^Fin n]→L[ℝ] ℝ) :
    TauCeti.alternatingFormInner E n o.volumeFormL ω • o.volumeFormL = ω := by
  let b : OrthonormalBasis (Fin n) ℝ E := (stdOrthonormalBasis ℝ E).reindex (finCongr Fact.out)
  ext v
  rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    TauCeti.alternatingFormInner_eq_mul_apply_orthonormalBasis b,
    o.volumeFormL.apply_eq_det_mul b.toBasis v, ω.apply_eq_det_mul b.toBasis v]
  calc o.volumeFormL b * ω b * (b.toBasis.det v * o.volumeFormL b)
      = b.toBasis.det v * ((o.volumeFormL b * o.volumeFormL b) * ω b) := by ring
    _ = b.toBasis.det v * ω b := by rw [o.volumeFormL_apply_mul_self b, one_mul]

/-- The absolute value of the inner product of a top-degree form `ω` with `o.volumeFormL` equals
the comass `‖ω‖`. -/
theorem abs_alternatingFormInner_volumeFormL (o : Orientation ℝ E (Fin n))
    (ω : E [⋀^Fin n]→L[ℝ] ℝ) :
    |TauCeti.alternatingFormInner E n o.volumeFormL ω| = ‖ω‖ := by
  let b : OrthonormalBasis (Fin n) ℝ E := (stdOrthonormalBasis ℝ E).reindex (finCongr Fact.out)
  have habs : |o.volumeFormL b| = 1 := by
    have hsq : |o.volumeFormL b| ^ 2 = 1 ^ 2 := by
      rw [sq_abs, sq, o.volumeFormL_apply_mul_self b, one_pow]
    exact (sq_eq_sq₀ (abs_nonneg _) zero_le_one).mp hsq
  rw [TauCeti.alternatingFormInner_eq_mul_apply_orthonormalBasis b, abs_mul, habs, one_mul,
    ω.norm_eq_norm_apply_orthonormalBasis b, Real.norm_eq_abs]

/-- A top-degree form pairs to `1` against `o.volumeFormL` if and only if it equals
`o.volumeFormL`. -/
theorem alternatingFormInner_volumeFormL_eq_one_iff (o : Orientation ℝ E (Fin n))
    (ω : E [⋀^Fin n]→L[ℝ] ℝ) :
    TauCeti.alternatingFormInner E n o.volumeFormL ω = 1 ↔ ω = o.volumeFormL := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rw [← o.alternatingFormInner_volumeFormL_smul ω, h, one_smul]
  · rintro rfl
    exact o.alternatingFormInner_volumeFormL_self

end Orientation

namespace TauCeti

section General

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {k : ℕ}

/-- An ordered `k`-frame `v : Fin k → E` in a real inner product space is *calibrated* by a
continuous alternating `k`-form `φ` if `v` is orthonormal and `φ v = 1`. -/
def IsCalibratedFrame (φ : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E) : Prop :=
  Orthonormal ℝ v ∧ φ v = 1

/-- Definitional unfolding of `TauCeti.IsCalibratedFrame`. -/
theorem isCalibratedFrame_def (φ : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E) :
    IsCalibratedFrame φ v = (Orthonormal ℝ v ∧ φ v = 1) := (rfl)

/-- Orthonormality of a calibrated frame. -/
theorem IsCalibratedFrame.orthonormal {φ : E [⋀^Fin k]→L[ℝ] ℝ} {v : Fin k → E}
    (h : IsCalibratedFrame φ v) : Orthonormal ℝ v := h.1

/-- A calibrated frame evaluates to `1` under the calibrating form. -/
theorem IsCalibratedFrame.apply_eq_one {φ : E [⋀^Fin k]→L[ℝ] ℝ} {v : Fin k → E}
    (h : IsCalibratedFrame φ v) : φ v = 1 := h.2

/-- Every calibrated frame is linearly independent over `ℝ`. -/
theorem IsCalibratedFrame.linearIndependent {φ : E [⋀^Fin k]→L[ℝ] ℝ} {v : Fin k → E}
    (h : IsCalibratedFrame φ v) : LinearIndependent ℝ v :=
  h.orthonormal.linearIndependent

/-- Every vector in a calibrated frame has unit norm. -/
theorem IsCalibratedFrame.norm_eq_one_apply {φ : E [⋀^Fin k]→L[ℝ] ℝ} {v : Fin k → E}
    (h : IsCalibratedFrame φ v) (i : Fin k) : ‖v i‖ = 1 :=
  h.orthonormal.1 i

/-- The exterior product `v₁ ∧ ⋯ ∧ vₖ` of a calibrated frame has unit norm. -/
theorem IsCalibratedFrame.norm_ιMulti [FiniteDimensional ℝ E] {φ : E [⋀^Fin k]→L[ℝ] ℝ}
    {v : Fin k → E} (h : IsCalibratedFrame φ v) : ‖ιMulti ℝ k v‖ = 1 :=
  h.orthonormal.norm_ιMulti

/-- The existence of a frame calibrated by `φ` forces the comass bound `1 ≤ ‖φ‖`. -/
theorem IsCalibratedFrame.one_le_norm {φ : E [⋀^Fin k]→L[ℝ] ℝ} {v : Fin k → E}
    (h : IsCalibratedFrame φ v) : 1 ≤ ‖φ‖ := by
  have hle := φ.le_opNorm v
  simpa [h.apply_eq_one, h.orthonormal.norm_eq_one] using hle

/-- If `φ` has comass at most `1` and admits a calibrated frame `v`, then `φ` has comass `1`. -/
theorem IsCalibratedFrame.norm_eq_one {φ : E [⋀^Fin k]→L[ℝ] ℝ} {v : Fin k → E}
    (h : IsCalibratedFrame φ v) (hφ : ‖φ‖ ≤ 1) : ‖φ‖ = 1 :=
  le_antisymm hφ h.one_le_norm

/-- On a calibrated frame of a form `φ` of comass at most `1`, `|φ v| = ‖φ‖`. -/
theorem IsCalibratedFrame.abs_apply_eq_norm {φ : E [⋀^Fin k]→L[ℝ] ℝ} {v : Fin k → E}
    (h : IsCalibratedFrame φ v) (hφ : ‖φ‖ ≤ 1) : |φ v| = ‖φ‖ := by
  rw [h.apply_eq_one, abs_one, h.norm_eq_one hφ]

/-- The zero `k`-form calibrates no frame in any degree `k ≥ 0`. -/
@[simp]
theorem not_isCalibratedFrame_zero (v : Fin k → E) :
    ¬ IsCalibratedFrame (0 : E [⋀^Fin k]→L[ℝ] ℝ) v := by
  rintro ⟨_, h⟩
  exact zero_ne_one h

/-- A form of comass strictly less than `1` calibrates no frame. -/
theorem not_isCalibratedFrame_of_norm_lt_one {φ : E [⋀^Fin k]→L[ℝ] ℝ} (hφ : ‖φ‖ < 1)
    (v : Fin k → E) : ¬ IsCalibratedFrame φ v :=
  fun h ↦ hφ.not_ge h.one_le_norm

/-- In degree `k` strictly exceeding `finrank ℝ E`, no frame is calibrated. -/
theorem not_isCalibratedFrame_of_finrank_lt [FiniteDimensional ℝ E]
    (hk : finrank ℝ E < k) (φ : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E) :
    ¬ IsCalibratedFrame φ v := by
  intro h
  have hle := h.linearIndependent.fintype_card_le_finrank
  rw [Fintype.card_fin] at hle
  exact hk.not_ge hle

/-- In degree zero, every empty frame is orthonormal, so `IsCalibratedFrame φ v` reduces to
`φ ![] = 1`. -/
theorem isCalibratedFrame_zero_iff (φ : E [⋀^Fin 0]→L[ℝ] ℝ) (v : Fin 0 → E) :
    IsCalibratedFrame φ v ↔ φ ![] = 1 := by
  have hv : v = ![] := Subsingleton.elim _ _
  subst hv
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨by rw [orthonormal_iff_ite]; intro i; exact Fin.elim0 i, h⟩⟩

/-- Permuting a calibrated frame by an even permutation of `Fin k` preserves calibration. -/
theorem IsCalibratedFrame.comp_perm_of_sign_eq_one {φ : E [⋀^Fin k]→L[ℝ] ℝ} {v : Fin k → E}
    (h : IsCalibratedFrame φ v) {σ : Equiv.Perm (Fin k)} (hσ : Equiv.Perm.sign σ = 1) :
    IsCalibratedFrame φ (v ∘ σ) := by
  refine ⟨h.orthonormal.comp σ σ.injective, ?_⟩
  rw [← φ.coe_toAlternatingMap, AlternatingMap.map_perm, hσ, one_smul]
  exact h.apply_eq_one

/-- For an even permutation `σ` of `Fin k`, `v ∘ σ` is calibrated by `φ` if and only if `v` is. -/
theorem isCalibratedFrame_comp_perm_iff_of_sign_eq_one (φ : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E)
    {σ : Equiv.Perm (Fin k)} (hσ : Equiv.Perm.sign σ = 1) :
    IsCalibratedFrame φ (v ∘ σ) ↔ IsCalibratedFrame φ v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp_perm_of_sign_eq_one hσ⟩
  have hσ' : Equiv.Perm.sign σ⁻¹ = 1 := by rw [map_inv, hσ, inv_one]
  simpa [Function.comp_def] using h.comp_perm_of_sign_eq_one hσ'

/-- Permuting a calibrated frame by an odd permutation calibrates `-φ`. -/
theorem IsCalibratedFrame.neg_comp_perm_of_sign_eq_neg_one {φ : E [⋀^Fin k]→L[ℝ] ℝ}
    {v : Fin k → E} (h : IsCalibratedFrame φ v) {σ : Equiv.Perm (Fin k)}
    (hσ : Equiv.Perm.sign σ = -1) :
    IsCalibratedFrame (-φ) (v ∘ σ) := by
  refine ⟨h.orthonormal.comp σ σ.injective, ?_⟩
  rw [ContinuousAlternatingMap.neg_apply, ← φ.coe_toAlternatingMap, AlternatingMap.map_perm, hσ,
    Units.neg_smul, one_smul, neg_neg]
  exact h.apply_eq_one

/-- Swapping two distinct vectors in a calibrated frame calibrates `-φ`. -/
theorem IsCalibratedFrame.neg_comp_swap {φ : E [⋀^Fin k]→L[ℝ] ℝ} {v : Fin k → E}
    (h : IsCalibratedFrame φ v) {i j : Fin k} (hij : i ≠ j) :
    IsCalibratedFrame (-φ) (v ∘ Equiv.swap i j) :=
  h.neg_comp_perm_of_sign_eq_neg_one (Equiv.Perm.sign_swap hij)

/-- Negating a single vector in a calibrated frame calibrates `-φ`. -/
theorem IsCalibratedFrame.neg_update_neg [DecidableEq (Fin k)] {φ : E [⋀^Fin k]→L[ℝ] ℝ}
    {v : Fin k → E} (h : IsCalibratedFrame φ v) (i : Fin k) :
    IsCalibratedFrame (-φ) (Function.update v i (-v i)) := by
  refine ⟨h.orthonormal.orthonormal_of_forall_eq_or_eq_neg fun j ↦ ?_, ?_⟩
  · by_cases hj : j = i <;> simp [hj]
  · rw [ContinuousAlternatingMap.neg_apply, ← φ.coe_toAlternatingMap,
      φ.toAlternatingMap.map_update_neg, Function.update_eq_self, neg_neg, φ.coe_toAlternatingMap,
      h.apply_eq_one]

/-- Pulling `φ` back along a linear isometry `e : F →ₗᵢ[ℝ] E` identifies calibrated frames in `F`
with calibrated frames in `E` lying in the image of `e`. -/
@[simp]
theorem isCalibratedFrame_compContinuousLinearMap_iff (φ : E [⋀^Fin k]→L[ℝ] ℝ)
    (e : F →ₗᵢ[ℝ] E) (v : Fin k → F) :
    IsCalibratedFrame (φ.compContinuousLinearMap e.toContinuousLinearMap) v ↔
      IsCalibratedFrame φ (e ∘ v) := by
  have happ : φ.compContinuousLinearMap e.toContinuousLinearMap v = φ (e ∘ v) := rfl
  rw [isCalibratedFrame_def, isCalibratedFrame_def, happ, e.orthonormal_comp_iff]

/-- Calibration of the image of an orthonormal basis under a linear isometry depends only on the
oriented `k`-plane `(F, b.toBasis.orientation)` and not on the choice of positively co-oriented
orthonormal basis. -/
theorem isCalibratedFrame_comp_orthonormalBasis_iff_of_orientation_eq (φ : E [⋀^Fin k]→L[ℝ] ℝ)
    (e : F →ₗᵢ[ℝ] E) (b b' : OrthonormalBasis (Fin k) ℝ F)
    (horient : b.toBasis.orientation = b'.toBasis.orientation) :
    IsCalibratedFrame φ (e ∘ b) ↔ IsCalibratedFrame φ (e ∘ b') := by
  rw [← isCalibratedFrame_compContinuousLinearMap_iff,
    ← isCalibratedFrame_compContinuousLinearMap_iff]
  have heq :=
    (φ.compContinuousLinearMap e.toContinuousLinearMap).apply_orthonormalBasis_eq_of_orientation_eq
      b b' horient
  simp [IsCalibratedFrame, b.orthonormal, b'.orthonormal, heq]

/-- An orthonormal basis `b` of an oriented `k`-dimensional inner product space `(E, o)` is
calibrated by `o.volumeFormL` if and only if `b` is positively oriented. -/
theorem isCalibratedFrame_volumeFormL_iff [Fact (finrank ℝ E = k)]
    (o : Orientation ℝ E (Fin k)) (b : OrthonormalBasis (Fin k) ℝ E) :
    IsCalibratedFrame o.volumeFormL b ↔ b.toBasis.orientation = o := by
  refine ⟨fun h ↦ ?_, fun hb ↦ ⟨b.orthonormal, o.volumeFormL_apply_orthonormal b hb⟩⟩
  refine o.volumeForm_apply_pos_iff.mp ?_
  rw [← o.volumeFormL_apply, OrthonormalBasis.coe_toBasis, h.apply_eq_one]
  exact zero_lt_one

end General

section SimpleForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {k : ℕ}

/-- An orthonormal frame `u : Fin k → E` is calibrated by its own simple unit `k`-form
`alternatingFormEquiv E k (u₁ ∧ ⋯ ∧ uₖ)`. -/
theorem isCalibratedFrame_alternatingFormEquiv_ιMulti_self {u : Fin k → E}
    (hu : Orthonormal ℝ u) :
    IsCalibratedFrame (alternatingFormEquiv E k (ιMulti ℝ k u)) u := by
  refine ⟨hu, ?_⟩
  rw [alternatingFormEquiv_apply, real_inner_self_eq_norm_sq, hu.norm_ιMulti, one_pow]

/-- **Grassmannian characterization of simple calibrations**: for an orthonormal frame `u`, a frame
`v : Fin k → E` is calibrated by `alternatingFormEquiv E k (u₁ ∧ ⋯ ∧ uₖ)` if and only if `v` is
orthonormal and spans the same oriented `k`-plane (`v₁ ∧ ⋯ ∧ vₖ = u₁ ∧ ⋯ ∧ uₖ`). -/
theorem isCalibratedFrame_alternatingFormEquiv_ιMulti_iff {u : Fin k → E}
    (hu : Orthonormal ℝ u) (v : Fin k → E) :
    IsCalibratedFrame (alternatingFormEquiv E k (ιMulti ℝ k u)) v ↔
      Orthonormal ℝ v ∧ ιMulti ℝ k v = ιMulti ℝ k u := by
  refine ⟨fun ⟨hv, hφv⟩ ↦ ⟨hv, ?_⟩, fun ⟨hv, hvu⟩ ↦ ⟨hv, ?_⟩⟩
  · rw [alternatingFormEquiv_apply] at hφv
    have hsq : ‖ιMulti ℝ k v - ιMulti ℝ k u‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, hv.norm_ιMulti, hu.norm_ιMulti, real_inner_comm, hφv]
      ring
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))
  · rw [alternatingFormEquiv_apply, hvu, real_inner_self_eq_norm_sq, hu.norm_ιMulti, one_pow]

end SimpleForm

end TauCeti
