/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import TauCeti.Analysis.Complex.RootsOfUnity.Circle
public import TauCeti.Geometry.Sphere.UnitaryGroup
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Block
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import TauCeti.Analysis.InnerProductSpace.PiL2

/-!
# Rotation axes, pole stabilizers, and concrete cyclic axis subgroups of `SO(3)`

Every rotation in an odd-dimensional special orthogonal group fixes a nonzero vector: for
`A ∈ SO(n, R)` with `n` odd, the relation `Aᵀ * (A - 1) = -(A - 1)ᵀ` gives
`det (A - 1) = -det (A - 1)`, hence `det (A - 1) = 0` whenever `2` is regular. Over `ℝ` this is
Euler's rotation axis theorem: every `g ∈ SO(n)` (`n` odd), and in particular every `g ∈ SO(3)`,
fixes a point of the Euclidean unit sphere.

In dimension two over `ℝ`, a matrix in `SO(2)` has the form `!![a, -b; b, a]` with `a² + b² = 1`,
which identifies `SO(2)` as a multiplicative group with `Circle` (`a + b i`) and shows that no
nonidentity planar rotation fixes a nonzero vector. Embedding `SO(2)` in `SO(3)` along
`Matrix.SpecialOrthogonalGroup.fromBlocksOne ℝ 1 2` identifies the stabilizer in `SO(3)` of the
standard pole `e₀ = (1, 0, 0) ∈ S²` with `Circle`. Because `SO(3)` acts transitively on `S²`
(`Matrix.SpecialOrthogonalGroup.instIsPretransitiveUnitSphereFinAddTwo`), the stabilizer in `SO(3)`
of every pole `p ∈ S²` is isomorphic to `Circle`.

## Main declarations

* `Matrix.SpecialOrthogonalGroup.det_sub_one_eq_zero_of_odd`,
  `Matrix.SpecialOrthogonalGroup.exists_mulVec_eq_self_of_odd`, and
  `Matrix.SpecialOrthogonalGroup.exists_smul_eq_self_unitSphere`: Euler's rotation axis theorem in
  odd dimension and on `S²`.
* `Matrix.SpecialOrthogonalGroup.finTwoRealMulEquivCircle`: the group isomorphism
  `SO(2, ℝ) ≃* Circle`.
* `TauCeti.Matrix.SpecialOrthogonalGroup.stabilizerBasePoleMulEquivCircle` and
  `TauCeti.Matrix.SpecialOrthogonalGroup.nonempty_stabilizer_mulEquiv_circle`: isomorphism of every
  pole stabilizer in `SO(3)` with `Circle`.
* `TauCeti.Matrix.SpecialOrthogonalGroup.isCyclic_stabilizer_unitSphere` and
  `TauCeti.Matrix.SpecialOrthogonalGroup.eq_of_le_stabilizer_unitSphere_of_natCard_eq`: cyclicity
  and cardinality-uniqueness of finite pole stabilizers.
* `TauCeti.Matrix.SpecialOrthogonalGroup.cyclicAxisSubgroup` and
  `TauCeti.Matrix.SpecialOrthogonalGroup.exists_conj_cyclicAxisSubgroup_of_le_stabilizer`: the
  concrete cyclic axis subgroup of order `n` and conjugacy to it for finite subgroups fixing a pole.
* `TauCeti.Matrix.SpecialOrthogonalGroup.fixedBy_unitSphere_eq_pair_of_ne_one` and
  `TauCeti.Matrix.SpecialOrthogonalGroup.natCard_fixedBy_unitSphere_of_ne_one`: every nonidentity
  rotation in `SO(3)` fixes on `S²` an antipodal pair `{p, -p}` of cardinality `2`.

## Implementation notes

Generic matrix-group statements on `Matrix.specialOrthogonalGroup` (odd-dimensional determinant and
eigenvector existence, `SO(2, ℝ) ≃* Circle`, and planar rotation freeness) live in the
organisational namespace `Matrix.SpecialOrthogonalGroup`, matching
`TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/FinTwo.lean` and `Center.lean`. Domain-specific
notions for the `S²` action of `SO(3)` (`basePole`, `cyclicAxisSubgroup`, and the pole-stabilizer
and fixed-point theorems) live in `TauCeti.Matrix.SpecialOrthogonalGroup`, matching `Frame.lean` and
`CoordinateRotation.lean`.

## References

* F. Klein, *Lectures on the Icosahedron and the Solution of Equations of the Fifth Degree* (1884),
  Part I, Chapter I.
* T. A. Springer, *Invariant Theory*, Lecture Notes in Mathematics 585, Springer, 1977, §4.4.
* J. Stillwell, *Naive Lie Theory*, Undergraduate Texts in Mathematics, Springer, 2008, §2.1.
-/

public section

open Metric Matrix

namespace Matrix.SpecialOrthogonalGroup

section Odd

section CommRing

attribute [local instance] starRingOfComm

/-- **Euler's determinant identity in odd dimension.** Over any commutative ring in which `2` is a
non-zero-divisor, every odd-dimensional special orthogonal matrix `g` satisfies `det (g - 1) = 0`:
from `gᵀ * (g - 1) = -(g - 1)ᵀ` and `det g = 1` one gets `det (g - 1) = -det (g - 1)`. -/
theorem det_sub_one_eq_zero_of_odd {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (h2 : IsRegular (2 : R)) (g : specialOrthogonalGroup n R) (hodd : Odd (Fintype.card n)) :
    ((g : Matrix n n R) - 1).det = 0 := by
  let A : Matrix n n R := g
  obtain ⟨hA_orth, hA_det⟩ := mem_specialOrthogonalGroup_iff.mp g.2
  have hmul : Aᵀ * (A - 1) = -(A - 1)ᵀ := by
    rw [Matrix.mul_sub, Matrix.mul_one, (mem_orthogonalGroup_iff' n R).mp hA_orth,
      Matrix.transpose_sub, Matrix.transpose_one, neg_sub]
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_transpose, hA_det, one_mul, Matrix.det_neg,
    Matrix.det_transpose, hodd.neg_one_pow, neg_one_mul] at hdet
  have htwo : (2 : R) * (A - 1).det = 0 := by linear_combination hdet
  exact h2.left.mul_left_eq_zero_iff.mp htwo

/-- **Existence of a nonzero fixed vector in odd dimension.** Over an integral domain of
characteristic different from `2`, every odd-dimensional special orthogonal matrix fixes a nonzero
coordinate vector. -/
theorem exists_mulVec_eq_self_of_odd {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    [IsDomain R] [NeZero (2 : R)] (g : specialOrthogonalGroup n R) (hodd : Odd (Fintype.card n)) :
    ∃ v : n → R, v ≠ 0 ∧ (g : Matrix n n R) *ᵥ v = v := by
  have h2 : IsRegular (2 : R) :=
    ⟨fun _ _ h ↦ mul_left_cancel₀ (NeZero.ne (2 : R)) h,
      fun _ _ h ↦ mul_right_cancel₀ (NeZero.ne (2 : R)) h⟩
  have hdet : ((g : Matrix n n R) - 1).det = 0 :=
    det_sub_one_eq_zero_of_odd h2 g hodd
  obtain ⟨v, hv, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hmul
  exact ⟨v, hv, hmul⟩

end CommRing

/-- **Euler's rotation axis theorem on the odd-dimensional Euclidean sphere.** Every
`g ∈ SO(n, ℝ)` with `n` odd fixes a point of the unit sphere `Sⁿ⁻¹`. -/
theorem exists_smul_eq_self_unitSphere_of_odd {n : Type*} [Fintype n] [DecidableEq n]
    (g : specialOrthogonalGroup n ℝ) (hodd : Odd (Fintype.card n)) :
    ∃ p : sphere (0 : EuclideanSpace ℝ n) 1, g • p = p := by
  obtain ⟨v, hv, hmul⟩ := exists_mulVec_eq_self_of_odd g hodd
  let u : EuclideanSpace ℝ n := WithLp.toLp 2 v
  have hu : u ≠ 0 := fun h ↦ hv (congrArg WithLp.ofLp h)
  have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  refine ⟨⟨‖u‖⁻¹ • u, by simp [norm_smul, inv_mul_cancel₀ hnorm]⟩, ?_⟩
  rw [specialUnitaryGroup.smul_unitSphere_eq_iff]
  simp [u, Matrix.mulVec_smul, hmul]

/-- **Euler's rotation axis theorem for `SO(3)`.** Every rotation of `ℝ³` fixes a point of the
unit sphere `S²`. -/
theorem exists_smul_eq_self_unitSphere (g : specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, g • p = p :=
  exists_smul_eq_self_unitSphere_of_odd g (by decide)

end Odd

section FinTwoReal

/-- **The isomorphism `SO(2, ℝ) ≃* Circle`**, sending a planar rotation matrix
`!![a, -b; b, a]` to `a + b i` on the unit circle in `ℂ`. -/
noncomputable def finTwoRealMulEquivCircle : specialOrthogonalGroup (Fin 2) ℝ ≃* Circle where
  toFun B := (⟨⟨(B : Matrix (Fin 2) (Fin 2) ℝ) 0 0, (B : Matrix (Fin 2) (Fin 2) ℝ) 1 0⟩, by
    obtain ⟨_, h01, hsq⟩ := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp B.2
    refine mem_sphere_zero_iff_norm.mpr ?_
    rw [Complex.norm_def, Real.sqrt_eq_one, Complex.normSq_mk]
    rw [h01] at hsq
    linear_combination hsq⟩ : Circle)
  invFun ζ := ⟨!![(ζ : ℂ).re, -(ζ : ℂ).im; (ζ : ℂ).im, (ζ : ℂ).re], by
    rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
    refine ⟨rfl, rfl, ?_⟩
    have hsq := Circle.normSq_coe ζ
    rw [Complex.normSq_apply] at hsq
    linear_combination hsq⟩
  left_inv B := by
    obtain ⟨h11, h01, _⟩ := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp B.2
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h11, h01]
  right_inv ζ := Circle.ext <| Complex.ext (by simp) (by simp)
  map_mul' A B := by
    obtain ⟨hA11, hA01, _⟩ := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp A.2
    refine Circle.ext ?_
    rw [Circle.coe_mul ⟨_, _⟩ ⟨_, _⟩]
    refine Complex.ext ?_ ?_
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination hA01 * (B : Matrix (Fin 2) (Fin 2) ℝ) 1 0
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination -hA11 * (B : Matrix (Fin 2) (Fin 2) ℝ) 1 0

@[simp]
theorem coe_finTwoRealMulEquivCircle (B : specialOrthogonalGroup (Fin 2) ℝ) :
    (finTwoRealMulEquivCircle B : ℂ) =
      ⟨(B : Matrix (Fin 2) (Fin 2) ℝ) 0 0, (B : Matrix (Fin 2) (Fin 2) ℝ) 1 0⟩ :=
  (rfl)

@[simp]
theorem coe_finTwoRealMulEquivCircle_symm (ζ : Circle) :
    ((finTwoRealMulEquivCircle.symm ζ : specialOrthogonalGroup (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      !![(ζ : ℂ).re, -(ζ : ℂ).im; (ζ : ℂ).im, (ζ : ℂ).re] :=
  (rfl)

/-- Under `(w 0, w 1) ↦ w 0 + w 1 i`, planar matrix-vector multiplication by `B ∈ SO(2, ℝ)` is
complex multiplication by `finTwoRealMulEquivCircle B`. -/
theorem coe_finTwoRealMulEquivCircle_mul_mk (B : specialOrthogonalGroup (Fin 2) ℝ)
    (w : Fin 2 → ℝ) :
    (finTwoRealMulEquivCircle B : ℂ) * ⟨w 0, w 1⟩ =
      ⟨((B : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ w) 0, ((B : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ w) 1⟩ := by
  obtain ⟨hB11, hB01, _⟩ := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp B.2
  refine Complex.ext ?_ ?_
  · simp only [coe_finTwoRealMulEquivCircle, Complex.mul_re, mulVec, dotProduct,
      Fin.sum_univ_two, Fin.isValue]
    rw [hB01]
    ring
  · simp only [coe_finTwoRealMulEquivCircle, Complex.mul_im, mulVec, dotProduct,
      Fin.sum_univ_two, Fin.isValue]
    rw [hB11]
    ring

/-- **A nonidentity planar rotation fixes only the zero vector.** -/
theorem mulVec_eq_self_iff_of_ne_one {B : specialOrthogonalGroup (Fin 2) ℝ} (hB : B ≠ 1)
    (w : Fin 2 → ℝ) :
    (B : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ w = w ↔ w = 0 := by
  refine ⟨fun hw ↦ ?_, fun hw ↦ by rw [hw, Matrix.mulVec_zero]⟩
  have hmul : (finTwoRealMulEquivCircle B : ℂ) * ⟨w 0, w 1⟩ = ⟨w 0, w 1⟩ := by
    rw [coe_finTwoRealMulEquivCircle_mul_mk, hw]
  have hζ : (finTwoRealMulEquivCircle B : ℂ) ≠ 1 := by
    rw [Ne, Circle.coe_eq_one, MulEquiv.map_eq_one_iff]
    exact hB
  have hz : (⟨w 0, w 1⟩ : ℂ) = 0 := by
    by_contra hne
    exact hζ (mul_eq_right₀ hne |>.mp hmul)
  ext i
  fin_cases i
  · exact congrArg Complex.re hz
  · exact congrArg Complex.im hz

end FinTwoReal

end Matrix.SpecialOrthogonalGroup

namespace TauCeti.Matrix.SpecialOrthogonalGroup

/-- The standard pole `e₀ = (1, 0, 0)` on the unit sphere `S² ⊆ ℝ³`. -/
noncomputable def basePole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

@[simp]
theorem coe_basePole :
    (basePole : EuclideanSpace ℝ (Fin 3)) = EuclideanSpace.single 0 1 :=
  (rfl)

@[simp]
theorem ofLp_coe_basePole :
    (basePole : EuclideanSpace ℝ (Fin 3)).ofLp = Pi.single 0 1 :=
  (rfl)

/-- Every point of the Euclidean unit sphere is distinct from its antipode. -/
theorem neg_ne_self_unitSphere {n : Type*} [Fintype n]
    (p : sphere (0 : EuclideanSpace ℝ n) 1) : -p ≠ p := by
  intro h
  have hp0 : (p : EuclideanSpace ℝ n) = 0 := by
    have h2 : (2 : ℝ) • (p : EuclideanSpace ℝ n) = 0 := by
      rw [two_smul]
      exact add_eq_zero_iff_neg_eq.mpr (congrArg Subtype.val h)
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  have hnorm : ‖(p : EuclideanSpace ℝ n)‖ = 1 := mem_sphere_zero_iff_norm.mp p.2
  simp [hp0] at hnorm

/-- **The stabilizer of `basePole` in `SO(3)` is the block-diagonal image of `SO(2)`.** -/
theorem stabilizer_basePole_eq_range_fromBlocksOne :
    MulAction.stabilizer (specialOrthogonalGroup (Fin 3) ℝ) basePole =
      (_root_.Matrix.SpecialOrthogonalGroup.fromBlocksOne ℝ 1 2).range := by
  ext g
  rw [MulAction.mem_stabilizer_iff, specialUnitaryGroup.smul_unitSphere_eq_iff, ofLp_coe_basePole,
    _root_.Matrix.SpecialOrthogonalGroup.mem_range_fromBlocksOne_iff, Fin.forall_fin_one]
  rfl

/-- The injective homomorphism `Circle →* SO(3)` of rotations about the `e₀`-axis. -/
noncomputable def basePoleAxisHom : Circle →* specialOrthogonalGroup (Fin 3) ℝ :=
  (_root_.Matrix.SpecialOrthogonalGroup.fromBlocksOne ℝ 1 2).comp
    _root_.Matrix.SpecialOrthogonalGroup.finTwoRealMulEquivCircle.symm.toMonoidHom

theorem basePoleAxisHom_apply (ζ : Circle) :
    basePoleAxisHom ζ =
      _root_.Matrix.SpecialOrthogonalGroup.fromBlocksOne ℝ 1 2
        (_root_.Matrix.SpecialOrthogonalGroup.finTwoRealMulEquivCircle.symm ζ) :=
  (rfl)

@[simp]
theorem basePoleAxisHom_mulVec_zero (ζ : Circle) (w : Fin 3 → ℝ) :
    ((basePoleAxisHom ζ : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w) 0 = w 0 := by
  let B := _root_.Matrix.SpecialOrthogonalGroup.finTwoRealMulEquivCircle.symm ζ
  have h00 := _root_.Matrix.SpecialOrthogonalGroup.fromBlocksOne_apply_castAdd_castAdd ℝ 1 B 0 0
  have h01 := _root_.Matrix.SpecialOrthogonalGroup.fromBlocksOne_apply_castAdd_natAdd ℝ 1 B 0 0
  have h02 := _root_.Matrix.SpecialOrthogonalGroup.fromBlocksOne_apply_castAdd_natAdd ℝ 1 B 0 1
  rw [basePoleAxisHom_apply]
  simp only [mulVec, dotProduct, Fin.sum_univ_three]
  dsimp [B] at h00 h01 h02 ⊢
  linear_combination h00 * w 0 + h01 * w 1 + h02 * w 2

@[simp]
theorem basePoleAxisHom_mulVec_one (ζ : Circle) (w : Fin 3 → ℝ) :
    ((basePoleAxisHom ζ : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w) 1 =
      (ζ : ℂ).re * w 1 - (ζ : ℂ).im * w 2 := by
  let B := _root_.Matrix.SpecialOrthogonalGroup.finTwoRealMulEquivCircle.symm ζ
  have h10 := _root_.Matrix.SpecialOrthogonalGroup.fromBlocksOne_apply_natAdd_castAdd ℝ 1 B 0 0
  have h11 := _root_.Matrix.SpecialOrthogonalGroup.fromBlocksOne_apply_natAdd_natAdd ℝ 1 B 0 0
  have h12 := _root_.Matrix.SpecialOrthogonalGroup.fromBlocksOne_apply_natAdd_natAdd ℝ 1 B 0 1
  simp only [B, _root_.Matrix.SpecialOrthogonalGroup.coe_finTwoRealMulEquivCircle_symm,
    of_apply, cons_val_zero, cons_val_one, cons_val_fin_one] at h11 h12
  rw [basePoleAxisHom_apply]
  simp only [mulVec, dotProduct, Fin.sum_univ_three]
  dsimp [B] at h10 h11 h12 ⊢
  linear_combination h10 * w 0 + h11 * w 1 + h12 * w 2

@[simp]
theorem basePoleAxisHom_mulVec_two (ζ : Circle) (w : Fin 3 → ℝ) :
    ((basePoleAxisHom ζ : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w) 2 =
      (ζ : ℂ).im * w 1 + (ζ : ℂ).re * w 2 := by
  let B := _root_.Matrix.SpecialOrthogonalGroup.finTwoRealMulEquivCircle.symm ζ
  have h20 := _root_.Matrix.SpecialOrthogonalGroup.fromBlocksOne_apply_natAdd_castAdd ℝ 1 B 1 0
  have h21 := _root_.Matrix.SpecialOrthogonalGroup.fromBlocksOne_apply_natAdd_natAdd ℝ 1 B 1 0
  have h22 := _root_.Matrix.SpecialOrthogonalGroup.fromBlocksOne_apply_natAdd_natAdd ℝ 1 B 1 1
  simp only [B, _root_.Matrix.SpecialOrthogonalGroup.coe_finTwoRealMulEquivCircle_symm,
    of_apply, cons_val_zero, cons_val_one, cons_val_fin_one] at h21 h22
  rw [basePoleAxisHom_apply]
  simp only [mulVec, dotProduct, Fin.sum_univ_three]
  dsimp [B] at h20 h21 h22 ⊢
  linear_combination h20 * w 0 + h21 * w 1 + h22 * w 2

theorem basePoleAxisHom_injective : Function.Injective basePoleAxisHom :=
  (_root_.Matrix.SpecialOrthogonalGroup.fromBlocksOne_injective ℝ 1).comp
    _root_.Matrix.SpecialOrthogonalGroup.finTwoRealMulEquivCircle.symm.injective

/-- The image of `basePoleAxisHom` is the stabilizer of `basePole` in `SO(3)`. -/
@[simp]
theorem range_basePoleAxisHom :
    basePoleAxisHom.range = MulAction.stabilizer (specialOrthogonalGroup (Fin 3) ℝ) basePole := by
  rw [stabilizer_basePole_eq_range_fromBlocksOne]
  ext g
  simp only [basePoleAxisHom, MonoidHom.mem_range, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom]
  exact ⟨fun ⟨ζ, hζ⟩ ↦ ⟨_, hζ⟩, fun ⟨B, hB⟩ ↦
    ⟨_root_.Matrix.SpecialOrthogonalGroup.finTwoRealMulEquivCircle B, by simpa using hB⟩⟩

/-- **The stabilizer of `basePole` in `SO(3)` is isomorphic to `Circle`.** -/
noncomputable def stabilizerBasePoleMulEquivCircle :
    MulAction.stabilizer (specialOrthogonalGroup (Fin 3) ℝ) basePole ≃* Circle :=
  (MulEquiv.subgroupCongr range_basePoleAxisHom.symm).trans
    (MonoidHom.ofInjective basePoleAxisHom_injective).symm

@[simp]
theorem coe_stabilizerBasePoleMulEquivCircle_symm (ζ : Circle) :
    (stabilizerBasePoleMulEquivCircle.symm ζ : specialOrthogonalGroup (Fin 3) ℝ) =
      basePoleAxisHom ζ :=
  (rfl)

/-- **The stabilizer in `SO(3)` of every point of `S²` is isomorphic to `Circle`.** -/
theorem nonempty_stabilizer_mulEquiv_circle (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Nonempty (MulAction.stabilizer (specialOrthogonalGroup (Fin 3) ℝ) p ≃* Circle) := by
  obtain ⟨F, hF⟩ := MulAction.exists_smul_eq (specialOrthogonalGroup (Fin 3) ℝ) basePole p
  exact ⟨(MulAction.stabilizerEquivStabilizer hF.symm).symm.trans stabilizerBasePoleMulEquivCircle⟩

/-- For any subgroup `K ≤ SO(3)` and any point `p ∈ S²`, the stabilizer `MulAction.stabilizer K p`
embeds as a multiplicative monoid into `ℂ`. -/
theorem exists_injective_monoidHom_stabilizer_complex
    (K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ))
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ φ : MulAction.stabilizer K p →* ℂ, Function.Injective φ := by
  obtain ⟨e⟩ := nonempty_stabilizer_mulEquiv_circle p
  let ι : MulAction.stabilizer K p →* MulAction.stabilizer (specialOrthogonalGroup (Fin 3) ℝ) p :=
    { toFun := fun g ↦ ⟨g.1.1, g.2⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hι : Function.Injective ι := fun _ _ h ↦
    Subtype.ext (Subtype.ext (congrArg
      (fun z : MulAction.stabilizer (specialOrthogonalGroup (Fin 3) ℝ) p ↦ z.1) h))
  exact ⟨Circle.coeHom.comp (e.toMonoidHom.comp ι),
    Circle.coe_injective.comp (e.injective.comp hι)⟩

/-- **Finite pole stabilizers are cyclic.** For any subgroup `K ≤ SO(3)` and any `p ∈ S²`, if
`MulAction.stabilizer K p` is finite, then it is cyclic (via `isCyclic_of_injective_ringHom` into
`ℂ`). -/
instance isCyclic_stabilizer_unitSphere (K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ))
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) [Finite (MulAction.stabilizer K p)] :
    IsCyclic (MulAction.stabilizer K p) := by
  obtain ⟨φ, hφ⟩ := exists_injective_monoidHom_stabilizer_complex K p
  exact isCyclic_of_injective_ringHom φ hφ

/-- **Two finite subgroups of `SO(3)` fixing the same point of `S²` and having the same cardinality
are equal.** -/
theorem eq_of_le_stabilizer_unitSphere_of_natCard_eq
    {H₁ H₂ : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)} [Finite H₁] [Finite H₂]
    {p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    (h₁ : H₁ ≤ MulAction.stabilizer (specialOrthogonalGroup (Fin 3) ℝ) p)
    (h₂ : H₂ ≤ MulAction.stabilizer (specialOrthogonalGroup (Fin 3) ℝ) p)
    (hc : Nat.card H₁ = Nat.card H₂) :
    H₁ = H₂ := by
  let S := MulAction.stabilizer (specialOrthogonalGroup (Fin 3) ℝ) p
  obtain ⟨e⟩ := nonempty_stabilizer_mulEquiv_circle p
  let L₁ : Subgroup Circle := (H₁.subgroupOf S).map (e : S →* Circle)
  let L₂ : Subgroup Circle := (H₂.subgroupOf S).map (e : S →* Circle)
  have hcard₁ : Nat.card L₁ = Nat.card H₁ :=
    (Nat.card_congr (e.subgroupMap (H₁.subgroupOf S)).symm.toEquiv).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₁).toEquiv)
  have hcard₂ : Nat.card L₂ = Nat.card H₂ :=
    (Nat.card_congr (e.subgroupMap (H₂.subgroupOf S)).symm.toEquiv).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₂).toEquiv)
  have : Finite L₁ := Nat.finite_of_card_ne_zero (hcard₁ ▸ Nat.card_pos.ne')
  have : Finite L₂ := Nat.finite_of_card_ne_zero (hcard₂ ▸ Nat.card_pos.ne')
  have hL : L₁ = L₂ := Subgroup.eq_of_subgroup_circle_of_natCard_eq (by rw [hcard₁, hc, hcard₂])
  have hsub : H₁.subgroupOf S = H₂.subgroupOf S :=
    Subgroup.map_injective (f := (e : S →* Circle)) e.injective hL
  ext g
  refine ⟨fun hg ↦ ?_, fun hg ↦ ?_⟩
  · have : (⟨g, h₁ hg⟩ : S) ∈ H₂.subgroupOf S := hsub ▸ Subgroup.mem_subgroupOf.mpr hg
    exact Subgroup.mem_subgroupOf.mp this
  · have : (⟨g, h₂ hg⟩ : S) ∈ H₁.subgroupOf S := hsub.symm ▸ Subgroup.mem_subgroupOf.mpr hg
    exact Subgroup.mem_subgroupOf.mp this

section CyclicModel

variable (n : ℕ) [NeZero n]

/-- The faithful homomorphism `Multiplicative (ZMod n) →* SO(3)` rotating by multiples of `2π / n`
about `basePole`. -/
noncomputable def cyclicAxisHom :
    Multiplicative (ZMod n) →* specialOrthogonalGroup (Fin 3) ℝ :=
  basePoleAxisHom.comp ZMod.toCircle.toMonoidHom

@[simp]
theorem cyclicAxisHom_apply (x : Multiplicative (ZMod n)) :
    cyclicAxisHom n x = basePoleAxisHom (ZMod.toCircle x.toAdd) :=
  (rfl)

theorem cyclicAxisHom_injective : Function.Injective (cyclicAxisHom n) :=
  basePoleAxisHom_injective.comp ZMod.injective_toCircle

/-- **The concrete cyclic subgroup of order `n` in `SO(3)`**, consisting of rotations by multiples
of `2π / n` in the `(e₁, e₂)`-plane fixing `basePole = e₀`. -/
noncomputable def cyclicAxisSubgroup : Subgroup (specialOrthogonalGroup (Fin 3) ℝ) :=
  (cyclicAxisHom n).range

theorem mem_cyclicAxisSubgroup_iff {g : specialOrthogonalGroup (Fin 3) ℝ} :
    g ∈ cyclicAxisSubgroup n ↔ ∃ x : Multiplicative (ZMod n), cyclicAxisHom n x = g :=
  Iff.rfl

/-- The coordinate isomorphism `Multiplicative (ZMod n) ≃* cyclicAxisSubgroup n`. -/
noncomputable def cyclicAxisEquiv : Multiplicative (ZMod n) ≃* cyclicAxisSubgroup n :=
  MonoidHom.ofInjective (cyclicAxisHom_injective n)

@[simp]
theorem coe_cyclicAxisEquiv (x : Multiplicative (ZMod n)) :
    (cyclicAxisEquiv n x : specialOrthogonalGroup (Fin 3) ℝ) = cyclicAxisHom n x :=
  (rfl)

instance : Finite (cyclicAxisSubgroup n) :=
  Finite.of_equiv _ (cyclicAxisEquiv n).toEquiv

instance : IsCyclic (cyclicAxisSubgroup n) :=
  let e := cyclicAxisEquiv n
  isCyclic_of_surjective e e.surjective

@[simp]
theorem natCard_cyclicAxisSubgroup : Nat.card (cyclicAxisSubgroup n) = n := by
  rw [← Nat.card_congr (cyclicAxisEquiv n).toEquiv]
  exact Nat.card_zmod n

theorem cyclicAxisSubgroup_le_stabilizer_basePole :
    cyclicAxisSubgroup n ≤ MulAction.stabilizer (specialOrthogonalGroup (Fin 3) ℝ) basePole := by
  rw [← range_basePoleAxisHom]
  rintro _ ⟨j, rfl⟩
  exact ⟨ZMod.toCircle j.toAdd, rfl⟩

@[simp]
theorem cyclicAxisSubgroup_one : cyclicAxisSubgroup 1 = ⊥ :=
  Subgroup.eq_bot_of_card_eq _ (natCard_cyclicAxisSubgroup 1)

theorem cyclicAxisSubgroup_ne_bot_iff : cyclicAxisSubgroup n ≠ ⊥ ↔ 2 ≤ n := by
  rw [Ne, Subgroup.eq_bot_iff_card, natCard_cyclicAxisSubgroup]
  have hn : 0 < n := NeZero.pos n
  omega

end CyclicModel

/-- **Every finite subgroup of `SO(3)` fixing a point `p ∈ S²` is conjugate in `SO(3)` to the
concrete cyclic model `cyclicAxisSubgroup (Nat.card K)`.** -/
theorem exists_conj_cyclicAxisSubgroup_of_le_stabilizer
    (K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) [Finite K]
    {p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    (hK : K ≤ MulAction.stabilizer (specialOrthogonalGroup (Fin 3) ℝ) p) :
    ∃ F : specialOrthogonalGroup (Fin 3) ℝ,
      K = (cyclicAxisSubgroup (Nat.card K)).map (MulAut.conj F).toMonoidHom := by
  have : NeZero (Nat.card K) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨F, hF⟩ := MulAction.exists_smul_eq (specialOrthogonalGroup (Fin 3) ℝ) basePole p
  let M := (cyclicAxisSubgroup (Nat.card K)).map (MulAut.conj F).toMonoidHom
  have hM_le : M ≤ MulAction.stabilizer (specialOrthogonalGroup (Fin 3) ℝ) p := by
    rw [← hF, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    exact Subgroup.map_mono (cyclicAxisSubgroup_le_stabilizer_basePole (Nat.card K))
  have hM_card : Nat.card M = Nat.card K :=
    (Nat.card_congr
      ((MulAut.conj F).subgroupMap (cyclicAxisSubgroup (Nat.card K))).symm.toEquiv).trans
      (natCard_cyclicAxisSubgroup (Nat.card K))
  have : Finite M := Nat.finite_of_card_ne_zero (hM_card ▸ Nat.card_pos.ne')
  exact ⟨F, eq_of_le_stabilizer_unitSphere_of_natCard_eq hK hM_le hM_card.symm⟩

section FixedPoints

/-- A nonidentity rotation in `SO(3)` fixing `basePole` fixes on `S²` only `basePole` and
`-basePole`. -/
theorem smul_eq_self_unitSphere_iff_of_smul_basePole_eq {g : specialOrthogonalGroup (Fin 3) ℝ}
    (hg : g ≠ 1) (hbase : g • basePole = basePole)
    (q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    g • q = q ↔ q = basePole ∨ q = -basePole := by
  refine ⟨fun hq ↦ ?_, ?_⟩
  · have hmem : g ∈ (_root_.Matrix.SpecialOrthogonalGroup.fromBlocksOne ℝ 1 2).range := by
      rw [← stabilizer_basePole_eq_range_fromBlocksOne]
      exact hbase
    obtain ⟨B, rfl⟩ := hmem
    have hB : B ≠ 1 := fun h1 ↦ hg (by simp [h1])
    let w : Fin 2 → ℝ := fun k ↦ q.1.ofLp (Fin.natAdd 1 k)
    have hw_fix : (B : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ w = w := by
      have hq' := (specialUnitaryGroup.smul_unitSphere_eq_iff _ q q).mp hq
      ext k
      have hk := congrFun hq' (Fin.natAdd 1 k)
      have h0 := _root_.Matrix.SpecialOrthogonalGroup.fromBlocksOne_apply_natAdd_castAdd ℝ 1 B k 0
      have h10 := _root_.Matrix.SpecialOrthogonalGroup.fromBlocksOne_apply_natAdd_natAdd ℝ 1 B k 0
      have h11 := _root_.Matrix.SpecialOrthogonalGroup.fromBlocksOne_apply_natAdd_natAdd ℝ 1 B k 1
      dsimp only [w]
      rw [← hk]
      simp only [mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three]
      dsimp at h0 h10 h11 ⊢
      linear_combination -(h0 * q.1.ofLp 0 + h10 * q.1.ofLp 1 + h11 * q.1.ofLp 2)
    have hw0 : w = 0 := (_root_.Matrix.SpecialOrthogonalGroup.mulVec_eq_self_iff_of_ne_one hB w).mp
      hw_fix
    have hq1 : q.1.ofLp 1 = 0 := congrFun hw0 0
    have hq2 : q.1.ofLp 2 = 0 := congrFun hw0 1
    have hnorm : q.1.ofLp ⬝ᵥ q.1.ofLp = 1 :=
      (EuclideanSpace.toLp_mem_sphere_zero_one_iff (v := q.1.ofLp)).mp q.2
    rw [dotProduct, Fin.sum_univ_three, hq1, hq2] at hnorm
    have hsq : q.1.ofLp 0 ^ 2 = 1 := by linear_combination hnorm
    rcases sq_eq_one_iff.mp hsq with hq0 | hq0
    · left
      refine Subtype.ext <| (WithLp.ofLp_injective 2) <| funext fun i ↦ ?_
      rw [ofLp_coe_basePole]
      fin_cases i <;> simp [hq0, hq1, hq2]
    · right
      refine Subtype.ext <| (WithLp.ofLp_injective 2) <| funext fun i ↦ ?_
      have hneg : ((-basePole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
          EuclideanSpace ℝ (Fin 3)).ofLp = -Pi.single 0 1 := by simp
      rw [hneg]
      fin_cases i <;> simp [hq0, hq1, hq2]
  · rintro (rfl | rfl)
    · exact hbase
    · rw [specialUnitaryGroup.smul_neg_unitSphere, hbase]

/-- **A nonidentity rotation in `SO(3)` fixing `p ∈ S²` fixes on `S²` precisely `p` and `-p`.** -/
theorem smul_eq_self_unitSphere_iff_of_ne_one {g : specialOrthogonalGroup (Fin 3) ℝ} (hg : g ≠ 1)
    {p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1} (hp : g • p = p)
    (q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    g • q = q ↔ q = p ∨ q = -p := by
  obtain ⟨F, rfl⟩ := MulAction.exists_smul_eq (specialOrthogonalGroup (Fin 3) ℝ) basePole p
  let g' : specialOrthogonalGroup (Fin 3) ℝ := F⁻¹ * g * F
  have hg' : g' ≠ 1 := by
    intro h1
    apply hg
    calc
      g = F * g' * F⁻¹ := by simp [g', mul_assoc]
      _ = 1 := by simp [h1]
  have hbase : g' • basePole = basePole := by
    simp [g', mul_smul, hp]
  have hconj : g • q = q ↔ g' • (F⁻¹ • q) = F⁻¹ • q := by
    refine ⟨fun hq ↦ ?_, fun hq ↦ ?_⟩
    · simp [g', mul_smul, hq]
    · calc
        g • q = F • (g' • (F⁻¹ • q)) := by simp [g', mul_smul]
        _ = F • (F⁻¹ • q) := by rw [hq]
        _ = q := by simp
  rw [hconj, smul_eq_self_unitSphere_iff_of_smul_basePole_eq hg' hbase]
  refine or_congr ?_ ?_
  · exact ⟨fun h ↦ by simpa [mul_smul] using congrArg (F • ·) h,
      fun h ↦ by simpa [mul_smul] using congrArg (F⁻¹ • ·) h⟩
  · exact ⟨fun h ↦ by simpa [mul_smul] using congrArg (F • ·) h,
      fun h ↦ by simpa [mul_smul] using congrArg (F⁻¹ • ·) h⟩

/-- **The fixed-point set on `S²` of a nonidentity rotation fixing `p` is the antipodal pair
`{p, -p}`.** -/
theorem fixedBy_unitSphere_eq_pair_of_ne_one {g : specialOrthogonalGroup (Fin 3) ℝ} (hg : g ≠ 1)
    {p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1} (hp : g • p = p) :
    MulAction.fixedBy (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) g = {p, -p} := by
  ext q
  simp [MulAction.mem_fixedBy, smul_eq_self_unitSphere_iff_of_ne_one hg hp q]

/-- **Every nonidentity rotation in `SO(3)` has exactly two fixed points on `S²`.** -/
theorem natCard_fixedBy_unitSphere_of_ne_one {g : specialOrthogonalGroup (Fin 3) ℝ} (hg : g ≠ 1) :
    Nat.card (MulAction.fixedBy (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) g) = 2 := by
  obtain ⟨p, hp⟩ := _root_.Matrix.SpecialOrthogonalGroup.exists_smul_eq_self_unitSphere g
  rw [fixedBy_unitSphere_eq_pair_of_ne_one hg hp, Nat.card_coe_set_eq,
    Set.ncard_pair (neg_ne_self_unitSphere p).symm]

end FixedPoints

end TauCeti.Matrix.SpecialOrthogonalGroup
