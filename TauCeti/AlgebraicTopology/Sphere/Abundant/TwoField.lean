/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Quaternion
public import Mathlib.Topology.FiberBundle.Trivialization
public import TauCeti.AlgebraicTopology.Sphere.Abundant.Basic
public import TauCeti.AlgebraicTopology.Sphere.TwoFieldFamily
public import TauCeti.Topology.Homotopy.SerreFibration.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Geometry.Manifold.Instances.Sphere
import TauCeti.AlgebraicTopology.Sphere.Abundant.FiberedFamily
import TauCeti.AlgebraicTopology.Sphere.Abundant.Group
import TauCeti.AlgebraicTopology.Sphere.DoubleTangentCircle
import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
import TauCeti.Geometry.Manifold.Instances.EuclideanProd
import TauCeti.Geometry.Sphere.LinearIsometry
import TauCeti.Geometry.Sphere.Quaternion
import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle
import TauCeti.Topology.Homotopy.SerreFibration.TotalSpace
import TauCeti.Topology.MappingSpace.Sphere.Basic

/-!
# Abundance with two-spheres from two orthonormal tangent fields

Let `E` be a finite-dimensional real inner product space of dimension `n + 1`, and let
`u, v : Sⁿ → E` be two continuous vector fields which are pointwise orthonormal. For each `x ∈ Sⁿ`
the points `q ∈ Sⁿ` orthogonal to `u x` and `v x` form a sphere of dimension `n - 2`. Taken
together they form the space of equators `Σ = twoFieldEquators u v`
(`TauCeti.twoFieldEquators`), with projection `twoFieldEquatorsProj u v : Σ → Sⁿ`.

Near any `x₀ ∈ Sⁿ`, orthogonal projection onto the subspace `W₀ = (ℝ ∙ u x₀ ⊔ ℝ ∙ v x₀)ᗮ` is
uniformly bounded below on the fibres `Wₓ = (ℝ ∙ u x ⊔ ℝ ∙ v x)ᗮ` inside the open neighbourhood
`U = {x | ‖u x - u x₀‖² + ‖v x - v x₀‖² < 1}`. Restricting and normalizing yields an explicit
local trivialization of `twoFieldEquatorsProj u v` with model fibre `Sⁿ⁻²`
(`TauCeti.exists_trivialization_twoFieldEquators`). Consequently:

* `twoFieldEquatorsProj u v` is a Serre fibration
  (`TauCeti.TopCat.mem_serreFibrations_twoFieldEquatorsProj`);
* when `dim E ≥ 5` (so `n ≥ 4` and both base `Sⁿ` and fibre `Sⁿ⁻²` are simply connected), the total
  space `Σ` is simply connected (`TauCeti.simplyConnectedSpace_twoFieldEquators`).

When `x`, `u x`, `v x` are pointwise orthonormal (so `u` and `v` are tangent vector fields on `Sⁿ`)
and `n ≥ 4`, the family `σ = twoFieldSphereFamily h hu hv : Σ → Map(S², Sⁿ)` of Barraud, Damian,
Humilière and Oancea (Example 6.20) lies over `Sⁿ`. Under the identification
`Map_*(S², Sⁿ) ≃ₜ Ω² Sⁿ`
(`TauCeti.BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace`), the restriction of `σ`
to the fibre over `b` agrees with `TauCeti.tangentCircleDoubleLoop`, which by Proposition 6.21
(`TauCeti.isIso_singularHomologyFunctor_map_tangentCircleDoubleLoop`) induces an isomorphism on
`H_{n-2}(·; ℤ)`. Applying the fibred-family criterion
(`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_pos`) gives abundance with two-spheres
for every sphere `Sⁿ` (`n ≥ 4`) carrying two continuous orthonormal tangent vector fields
(`TauCeti.isAbundantWithTwoSpheres_sphere_of_twoField`).

In particular, any real inner product space with a norm-compatible right quaternionic structure
carries three such fields (`TauCeti.quaternionFrame`), so its unit sphere is abundant with
two-spheres when `n ≥ 4` (`TauCeti.isAbundantWithTwoSpheres_sphere_of_quaternion`). Combining this
with linear isometries to `ℍ` (`k = 1`, where `S³` is handled by
`TauCeti.isAbundantWithTwoSpheres_sphere_quaternion`) and `ℍ^k` (`k ≥ 2`) together with
homeomorphism invariance (`Homeomorph.isAbundantWithTwoSpheres_iff`), every unit sphere `S^{4k-1}`
(`k ≥ 1`) in any real inner product space of dimension `4k` is abundant with two-spheres
(`TauCeti.isAbundantWithTwoSpheres_sphere_of_finrank_eq_four_mul`).

## Main declarations

* `TauCeti.twoFieldEquatorsProj`: the projection `twoFieldEquators u v → Sⁿ`.
* `TauCeti.exists_trivialization_twoFieldEquators`: local trivializations of
  `twoFieldEquatorsProj u v` with model fibre `sphere (0 : EuclideanSpace ℝ (Fin d)) 1`.
* `TauCeti.TopCat.mem_serreFibrations_twoFieldEquatorsProj`: `twoFieldEquatorsProj u v` is a
  Serre fibration.
* `TauCeti.simplyConnectedSpace_twoFieldEquators`: `twoFieldEquators u v` is simply connected when
  `5 ≤ finrank ℝ E`.
* `TauCeti.isAbundantWithTwoSpheres_sphere_of_twoField`: every sphere `Sⁿ` (`n ≥ 4`) carrying two
  continuous pointwise orthonormal tangent fields is abundant with two-spheres.
* `TauCeti.isAbundantWithTwoSpheres_sphere_of_quaternion`: every sphere `Sⁿ` (`n ≥ 4`) in a
  quaternionic inner product space is abundant with two-spheres.
* `TauCeti.isAbundantWithTwoSpheres_sphere_of_finrank_eq_four_mul`: every sphere `S^{4k-1}`
  (`k ≥ 1`) in a real inner product space of dimension `4k` is abundant with two-spheres.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, Definition 6.14, Proposition 6.15,
  Example 6.20, and Proposition 6.21.
-/

public section

noncomputable section

open AlgebraicTopology Bundle CategoryTheory Metric Module MulOpposite Real Set
open scoped RealInnerProductSpace RightActions Topology Quaternion unitInterval Topology.Homotopy

namespace TauCeti

section EquatorBundle

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The projection `Σ → Sⁿ` from the space of equators `twoFieldEquators u v` to the unit sphere,
sending `(x, q)` to `x`. -/
def twoFieldEquatorsProj (u v : sphere (0 : E) 1 → E) :
    C(twoFieldEquators u v, sphere (0 : E) 1) :=
  ContinuousMap.fst.comp (ContinuousMap.subtypeVal (twoFieldEquators u v))

@[simp]
theorem twoFieldEquatorsProj_apply (u v : sphere (0 : E) 1 → E) (xq : twoFieldEquators u v) :
    twoFieldEquatorsProj u v xq = xq.1.1 :=
  (rfl)

/-! ### Local triviality via orthogonal projection -/

/-- Orthogonal projection onto the complement of `span {a, b}`, when `a, b` are orthonormal:
`z ↦ z - ⟪a, z⟫ • a - ⟪b, z⟫ • b`. -/
private def twoFieldProj (a b : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - ContinuousLinearMap.smulRightL ℝ E E (innerSL ℝ a) a -
    ContinuousLinearMap.smulRightL ℝ E E (innerSL ℝ b) b

private theorem twoFieldProj_apply (a b z : E) :
    twoFieldProj a b z = z - ⟪a, z⟫ • a - ⟪b, z⟫ • b :=
  (rfl)

private theorem continuous_twoFieldProj {X : Type*} [TopologicalSpace X] {u v : X → E}
    (hu : Continuous u) (hv : Continuous v) :
    Continuous fun x ↦ twoFieldProj (u x) (v x) := by
  have h1 : Continuous fun x ↦ ContinuousLinearMap.smulRightL ℝ E E (innerSL ℝ (u x)) (u x) :=
    ((ContinuousLinearMap.smulRightL ℝ E E).continuous.comp
      ((innerSL ℝ).continuous.comp hu)).clm_apply hu
  have h2 : Continuous fun x ↦ ContinuousLinearMap.smulRightL ℝ E E (innerSL ℝ (v x)) (v x) :=
    ((ContinuousLinearMap.smulRightL ℝ E E).continuous.comp
      ((innerSL ℝ).continuous.comp hv)).clm_apply hv
  exact (continuous_const.sub h1).sub h2

private theorem twoFieldProj_eq_self_of_inner {a b z : E} (hza : ⟪z, a⟫ = 0) (hzb : ⟪z, b⟫ = 0) :
    twoFieldProj a b z = z := by
  rw [twoFieldProj_apply, real_inner_comm z a, hza, real_inner_comm z b, hzb]
  simp

private theorem mem_orthogonal_sup_span_iff {a b z : E} :
    z ∈ (ℝ ∙ a ⊔ ℝ ∙ b)ᗮ ↔ ⟪z, a⟫ = 0 ∧ ⟪z, b⟫ = 0 := by
  rw [Submodule.mem_orthogonal']
  refine ⟨fun hz ↦ ⟨hz a (Submodule.mem_sup_left (Submodule.mem_span_singleton_self a)),
      hz b (Submodule.mem_sup_right (Submodule.mem_span_singleton_self b))⟩,
    fun ⟨ha, hb⟩ y hy ↦ ?_⟩
  rcases Submodule.mem_sup.1 hy with ⟨y₁, hy₁, y₂, hy₂, rfl⟩
  rcases Submodule.mem_span_singleton.1 hy₁ with ⟨c₁, rfl⟩
  rcases Submodule.mem_span_singleton.1 hy₂ with ⟨c₂, rfl⟩
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, ha, hb]
  ring

section ProjFacts

variable {a b : E} (hab : Orthonormal ℝ ![a, b])
include hab

private theorem norm_fst_of_orthonormal : ‖a‖ = 1 := by
  simpa using hab.norm_eq_one 0

private theorem norm_snd_of_orthonormal : ‖b‖ = 1 := by
  simpa using hab.norm_eq_one 1

private theorem inner_of_orthonormal : ⟪a, b⟫ = 0 := by
  simpa using hab.inner_eq_zero (by decide : (0 : Fin 2) ≠ 1)

private theorem inner_twoFieldProj_fst (z : E) : ⟪twoFieldProj a b z, a⟫ = 0 := by
  have ha : ‖a‖ = 1 := norm_fst_of_orthonormal hab
  have ho : ⟪a, b⟫ = 0 := inner_of_orthonormal hab
  rw [twoFieldProj_apply, inner_sub_left, inner_sub_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, ha, real_inner_comm a b, ho,
    real_inner_comm z a]
  ring

private theorem inner_twoFieldProj_snd (z : E) : ⟪twoFieldProj a b z, b⟫ = 0 := by
  have hb : ‖b‖ = 1 := norm_snd_of_orthonormal hab
  have ho : ⟪a, b⟫ = 0 := inner_of_orthonormal hab
  rw [twoFieldProj_apply, inner_sub_left, inner_sub_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, hb, ho, real_inner_comm z b]
  ring

private theorem norm_sq_sub_twoFieldProj (z : E) :
    ‖z - twoFieldProj a b z‖ ^ 2 = ⟪a, z⟫ ^ 2 + ⟪b, z⟫ ^ 2 := by
  have ha : ‖a‖ = 1 := norm_fst_of_orthonormal hab
  have hb : ‖b‖ = 1 := norm_snd_of_orthonormal hab
  have ho : ⟪a, b⟫ = 0 := inner_of_orthonormal hab
  have hsub : z - twoFieldProj a b z = ⟪a, z⟫ • a + ⟪b, z⟫ • b := by
    rw [twoFieldProj_apply]
    abel
  rw [hsub, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ha, hb, real_inner_comm a b, ho]
  ring

private theorem norm_sq_twoFieldProj (z : E) :
    ‖twoFieldProj a b z‖ ^ 2 = ‖z‖ ^ 2 - ⟪a, z⟫ ^ 2 - ⟪b, z⟫ ^ 2 := by
  have horth : ⟪twoFieldProj a b z, z - twoFieldProj a b z⟫ = 0 := by
    have hsub : z - twoFieldProj a b z = ⟪a, z⟫ • a + ⟪b, z⟫ • b := by
      rw [twoFieldProj_apply]
      abel
    rw [hsub, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      inner_twoFieldProj_fst hab z, inner_twoFieldProj_snd hab z]
    ring
  have hdecomp : ‖z‖ ^ 2 = ‖twoFieldProj a b z‖ ^ 2 + ‖z - twoFieldProj a b z‖ ^ 2 := by
    have hz : z = twoFieldProj a b z + (z - twoFieldProj a b z) := by abel
    conv_lhs => rw [hz]
    rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      real_inner_comm (twoFieldProj a b z) (z - twoFieldProj a b z), horth]
    ring
  rw [norm_sq_sub_twoFieldProj hab z] at hdecomp
  linarith

private theorem norm_twoFieldProj_le (z : E) : ‖twoFieldProj a b z‖ ≤ ‖z‖ := by
  have hsq : ‖twoFieldProj a b z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [norm_sq_twoFieldProj hab z]
    nlinarith [sq_nonneg ⟪a, z⟫, sq_nonneg ⟪b, z⟫]
  exact le_of_sq_le_sq hsq (norm_nonneg z)

private theorem finrank_orthogonal_pair [FiniteDimensional ℝ E] {d : ℕ}
    (hE : finrank ℝ E = d + 2) :
    finrank ℝ ((ℝ ∙ a ⊔ ℝ ∙ b)ᗮ : Submodule ℝ E) = d := by
  have hrange : Set.range ![a, b] = {a, b} := by
    ext y
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hspan : Submodule.span ℝ (Set.range ![a, b]) = ℝ ∙ a ⊔ ℝ ∙ b := by
    rw [hrange, Submodule.span_insert]
  have hdim : finrank ℝ ↥(ℝ ∙ a ⊔ ℝ ∙ b) = 2 := by
    rw [← hspan, finrank_span_eq_card hab.linearIndependent]
    simp
  have hadd := (ℝ ∙ a ⊔ ℝ ∙ b).finrank_add_finrank_orthogonal
  omega

end ProjFacts

/-- The empty-fibre (`d = 0`) case of `exists_trivialization_twoFieldEquators`. -/
private theorem exists_trivialization_twoFieldEquators_zero [FiniteDimensional ℝ E]
    (hE : finrank ℝ E = 0 + 2) {u v : sphere (0 : E) 1 → E}
    (h : ∀ x : sphere (0 : E) 1, Orthonormal ℝ ![u x, v x]) (x₀ : sphere (0 : E) 1) :
    ∃ t : Trivialization (sphere (0 : EuclideanSpace ℝ (Fin 0)) 1) (twoFieldEquatorsProj u v),
      x₀ ∈ t.baseSet := by
  have hemptyF : IsEmpty (sphere (0 : EuclideanSpace ℝ (Fin 0)) 1) :=
    ⟨fun w ↦ by
      have h1 : ‖(w : EuclideanSpace ℝ (Fin 0))‖ = 1 := norm_eq_of_mem_sphere w
      rw [Subsingleton.eq_zero (w : EuclideanSpace ℝ (Fin 0)), norm_zero] at h1
      exact zero_ne_one h1⟩
  have hemptyZ : IsEmpty (twoFieldEquators u v) :=
    ⟨fun xq ↦ by
      have hW := finrank_orthogonal_pair (h xq.1.1) hE
      have : Subsingleton ((ℝ ∙ u xq.1.1 ⊔ ℝ ∙ v xq.1.1)ᗮ : Submodule ℝ E) :=
        Module.finrank_zero_iff.1 hW
      have hmem : (xq.1.2 : E) ∈ (ℝ ∙ u xq.1.1 ⊔ ℝ ∙ v xq.1.1)ᗮ :=
        mem_orthogonal_sup_span_iff.2 (mem_twoFieldEquators.1 xq.2)
      have hz : (xq.1.2 : E) = 0 := congrArg Subtype.val
        (Subsingleton.elim (⟨(xq.1.2 : E), hmem⟩ : (ℝ ∙ u xq.1.1 ⊔ ℝ ∙ v xq.1.1)ᗮ) 0)
      have h1 : ‖(xq.1.2 : E)‖ = 1 := norm_eq_of_mem_sphere xq.1.2
      rw [hz, norm_zero] at h1
      exact zero_ne_one h1⟩
  exact ⟨{
    toFun := isEmptyElim
    invFun := fun p ↦ isEmptyElim p.2
    source := ∅
    target := ∅
    map_source' := fun _ hz ↦ False.elim hz
    map_target' := fun _ hp ↦ False.elim hp
    left_inv' := fun _ hz ↦ False.elim hz
    right_inv' := fun _ hp ↦ False.elim hp
    open_source := isOpen_empty
    open_target := isOpen_empty
    continuousOn_toFun := continuousOn_empty _
    continuousOn_invFun := continuousOn_empty _
    baseSet := Set.univ
    open_baseSet := isOpen_univ
    source_eq := (Set.eq_empty_of_isEmpty _).symm
    target_eq := (Set.eq_empty_of_isEmpty _).symm
    proj_toFun := fun _ hz ↦ False.elim hz }, trivial⟩

/-- **Local triviality of the bundle of equators.** Let `u, v : Sⁿ → E` be continuous vector fields
on the unit sphere of a finite-dimensional real inner product space `E` of dimension `d + 2` that
are pointwise orthonormal (`Orthonormal ℝ ![u x, v x]`). Then the projection
`twoFieldEquatorsProj u v : twoFieldEquators u v → Sⁿ` admits a trivialization with model fibre
`sphere (0 : EuclideanSpace ℝ (Fin d)) 1` around every point of `Sⁿ`. -/
theorem exists_trivialization_twoFieldEquators [FiniteDimensional ℝ E] {d : ℕ}
    (hE : finrank ℝ E = d + 2) {u v : sphere (0 : E) 1 → E}
    (hu : Continuous u) (hv : Continuous v)
    (h : ∀ x : sphere (0 : E) 1, Orthonormal ℝ ![u x, v x]) :
    ∀ x₀ : sphere (0 : E) 1,
      ∃ t : Trivialization (sphere (0 : EuclideanSpace ℝ (Fin d)) 1) (twoFieldEquatorsProj u v),
        x₀ ∈ t.baseSet := by
  intro x₀
  cases d with
  | zero => exact exists_trivialization_twoFieldEquators_zero hE h x₀
  | succ d =>
    classical
    let B := sphere (0 : E) 1
    let F := sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1
    let a₀ : E := u x₀
    let b₀ : E := v x₀
    let W₀ : Submodule ℝ E := (ℝ ∙ a₀ ⊔ ℝ ∙ b₀)ᗮ
    have hW₀_dim : finrank ℝ W₀ = d + 1 := finrank_orthogonal_pair (h x₀) hE
    let eW₀ : W₀ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
      (stdOrthonormalBasis ℝ W₀).repr.trans
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr hW₀_dim))
    let eS : sphere (0 : W₀) 1 ≃ₜ F := eW₀.unitSphereIsometryEquiv.toHomeomorph
    let P₀ : E →L[ℝ] W₀ :=
      (twoFieldProj a₀ b₀).codRestrict W₀ fun z ↦
        mem_orthogonal_sup_span_iff.2 ⟨inner_twoFieldProj_fst (h x₀) z,
          inner_twoFieldProj_snd (h x₀) z⟩
    have hP₀_val : ∀ z : E, (P₀ z : E) = twoFieldProj a₀ b₀ z := fun _ ↦ rfl
    let U : Set B := {x | ‖u x - a₀‖ ^ 2 + ‖v x - b₀‖ ^ 2 < 1}
    have hU_open : IsOpen U :=
      isOpen_lt (((hu.sub continuous_const).norm.pow 2).add ((hv.sub continuous_const).norm.pow 2))
        continuous_const
    have hx₀U : x₀ ∈ U := by
      have : ‖u x₀ - a₀‖ ^ 2 + ‖v x₀ - b₀‖ ^ 2 < 1 := by simp [a₀, b₀]
      exact this
    -- The operator `A x : W₀ →L[ℝ] W₀` composing `twoFieldProj (u x) (v x)` with `P₀`.
    let A : B → (W₀ →L[ℝ] W₀) := fun x ↦ P₀.comp ((twoFieldProj (u x) (v x)).comp W₀.subtypeL)
    have hA_cont : Continuous A := by
      have hR : Continuous fun x : B ↦ (twoFieldProj (u x) (v x)).comp W₀.subtypeL :=
        ((ContinuousLinearMap.compL ℝ W₀ E E).flip W₀.subtypeL).continuous.comp
          (continuous_twoFieldProj hu hv)
      exact ((ContinuousLinearMap.compL ℝ W₀ E W₀) P₀).continuous.comp hR
    have hA_bound : ∀ x ∈ U, ‖(1 : W₀ →L[ℝ] W₀) - A x‖ < 1 := by
      intro x hx
      let c : ℝ := √(‖u x - a₀‖ ^ 2 + ‖v x - b₀‖ ^ 2)
      have hc0 : 0 ≤ c := Real.sqrt_nonneg _
      have hc1 : c < 1 := by
        rw [Real.sqrt_lt' zero_lt_one]
        simpa [U] using hx
      refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ hc0 fun w ↦ ?_) hc1
      have hw := mem_orthogonal_sup_span_iff.1 w.2
      have hdiff : (((1 : W₀ →L[ℝ] W₀) - A x) w : E) =
          twoFieldProj a₀ b₀ ((w : E) - twoFieldProj (u x) (v x) (w : E)) := by
        simp [A, hP₀_val, map_sub, twoFieldProj_eq_self_of_inner hw.1 hw.2]
      have hle1 : ‖((1 : W₀ →L[ℝ] W₀) - A x) w‖ ≤
          ‖(w : E) - twoFieldProj (u x) (v x) (w : E)‖ := by
        rw [← Submodule.norm_coe, hdiff]
        exact norm_twoFieldProj_le (h x₀) _
      have hiu : |⟪u x, (w : E)⟫| ≤ ‖u x - a₀‖ * ‖w‖ := by
        have : ⟪u x, (w : E)⟫ = ⟪u x - a₀, (w : E)⟫ := by
          rw [inner_sub_left, real_inner_comm (w : E) a₀, hw.1, sub_zero]
        rw [this]
        simpa [Submodule.norm_coe] using abs_real_inner_le_norm (u x - a₀) (w : E)
      have hiv : |⟪v x, (w : E)⟫| ≤ ‖v x - b₀‖ * ‖w‖ := by
        have : ⟪v x, (w : E)⟫ = ⟪v x - b₀, (w : E)⟫ := by
          rw [inner_sub_left, real_inner_comm (w : E) b₀, hw.2, sub_zero]
        rw [this]
        simpa [Submodule.norm_coe] using abs_real_inner_le_norm (v x - b₀) (w : E)
      have hsq : ‖(w : E) - twoFieldProj (u x) (v x) (w : E)‖ ^ 2 ≤ (c * ‖w‖) ^ 2 := by
        rw [norm_sq_sub_twoFieldProj (h x), mul_pow,
          Real.sq_sqrt (by positivity : 0 ≤ ‖u x - a₀‖ ^ 2 + ‖v x - b₀‖ ^ 2)]
        have hu2 : ⟪u x, (w : E)⟫ ^ 2 ≤ (‖u x - a₀‖ * ‖w‖) ^ 2 := by
          simpa [sq_abs] using sq_le_sq' (by linarith [abs_nonneg ⟪u x, (w : E)⟫]) hiu
        have hv2 : ⟪v x, (w : E)⟫ ^ 2 ≤ (‖v x - b₀‖ * ‖w‖) ^ 2 := by
          simpa [sq_abs] using sq_le_sq' (by linarith [abs_nonneg ⟪v x, (w : E)⟫]) hiv
        nlinarith
      exact hle1.trans (le_of_sq_le_sq hsq (mul_nonneg hc0 (norm_nonneg w)))
    have hA_unit : ∀ x ∈ U, IsUnit (A x) := fun x hx ↦
      sub_sub_self (1 : W₀ →L[ℝ] W₀) (A x) ▸ (Units.oneSub (1 - A x) (hA_bound x hx)).isUnit
    -- Lower bound for `P₀` on `Wₓ`, showing `P₀` is injective and nonvanishing on unit vectors.
    have hP₀_sq_ge : ∀ x ∈ U, ∀ q : E, ⟪q, u x⟫ = 0 → ⟪q, v x⟫ = 0 →
        (1 - ‖u x - a₀‖ ^ 2 - ‖v x - b₀‖ ^ 2) * ‖q‖ ^ 2 ≤ ‖P₀ q‖ ^ 2 := by
      intro x _ q hqu hqv
      have haq : |⟪a₀, q⟫| ≤ ‖u x - a₀‖ * ‖q‖ := by
        have : ⟪a₀, q⟫ = -⟪u x - a₀, q⟫ := by
          rw [inner_sub_left, real_inner_comm q (u x), hqu, zero_sub, neg_neg]
        rw [this, abs_neg]
        exact abs_real_inner_le_norm (u x - a₀) q
      have hbq : |⟪b₀, q⟫| ≤ ‖v x - b₀‖ * ‖q‖ := by
        have : ⟪b₀, q⟫ = -⟪v x - b₀, q⟫ := by
          rw [inner_sub_left, real_inner_comm q (v x), hqv, zero_sub, neg_neg]
        rw [this, abs_neg]
        exact abs_real_inner_le_norm (v x - b₀) q
      have ha2 : ⟪a₀, q⟫ ^ 2 ≤ (‖u x - a₀‖ * ‖q‖) ^ 2 := by
        simpa [sq_abs] using sq_le_sq' (by linarith [abs_nonneg ⟪a₀, q⟫]) haq
      have hb2 : ⟪b₀, q⟫ ^ 2 ≤ (‖v x - b₀‖ * ‖q‖) ^ 2 := by
        simpa [sq_abs] using sq_le_sq' (by linarith [abs_nonneg ⟪b₀, q⟫]) hbq
      rw [← Submodule.norm_coe, hP₀_val, norm_sq_twoFieldProj (h x₀) q]
      nlinarith
    have hP₀_ne : ∀ (xq : twoFieldEquators u v), xq.1.1 ∈ U → P₀ (xq.1.2 : E) ≠ 0 := by
      intro xq hx hz
      have hxq := mem_twoFieldEquators.1 xq.2
      have hge := hP₀_sq_ge xq.1.1 hx (xq.1.2 : E) hxq.1 hxq.2
      have h1 : ‖(xq.1.2 : E)‖ = 1 := norm_eq_of_mem_sphere xq.1.2
      rw [hz, norm_zero, h1] at hge
      have : ‖u xq.1.1 - a₀‖ ^ 2 + ‖v xq.1.1 - b₀‖ ^ 2 < 1 := hx
      linarith
    have hP₀_inj : ∀ x ∈ U, ∀ {q₁ q₂ : E}, ⟪q₁, u x⟫ = 0 → ⟪q₁, v x⟫ = 0 →
        ⟪q₂, u x⟫ = 0 → ⟪q₂, v x⟫ = 0 → P₀ q₁ = P₀ q₂ → q₁ = q₂ := by
      intro x hx q₁ q₂ h1u h1v h2u h2v hEq
      have hge := hP₀_sq_ge x hx (q₁ - q₂)
        (by rw [inner_sub_left, h1u, h2u, sub_self])
        (by rw [inner_sub_left, h1v, h2v, sub_self])
      have h0 : P₀ (q₁ - q₂) = 0 := by rw [map_sub, hEq, sub_self]
      rw [h0, norm_zero, zero_pow two_ne_zero] at hge
      have hpos : 0 < 1 - ‖u x - a₀‖ ^ 2 - ‖v x - b₀‖ ^ 2 := by
        have : ‖u x - a₀‖ ^ 2 + ‖v x - b₀‖ ^ 2 < 1 := hx
        linarith
      have hnsq : ‖q₁ - q₂‖ ^ 2 ≤ 0 := by nlinarith
      have hn0 : ‖q₁ - q₂‖ = 0 := by nlinarith [norm_nonneg (q₁ - q₂)]
      exact sub_eq_zero.1 (norm_eq_zero.1 hn0)
    -- Default points for values outside `U`.
    let w₀F : F := ⟨EuclideanSpace.basisFun (Fin (d + 1)) ℝ 0,
      mem_sphere_zero_iff_norm.2
        ((EuclideanSpace.basisFun (Fin (d + 1)) ℝ).orthonormal.norm_eq_one 0)⟩
    let w₀ : sphere (0 : W₀) 1 := eS.symm w₀F
    let z₀ : twoFieldEquators u v :=
      ⟨(x₀, ⟨((w₀ : W₀) : E), by
        rw [mem_sphere_zero_iff_norm, Submodule.norm_coe]
        exact norm_eq_of_mem_sphere w₀⟩),
      mem_twoFieldEquators.2 (mem_orthogonal_sup_span_iff.1 (w₀ : W₀).2)⟩
    -- Raw inverse vector `invVec (x, w) = twoFieldProj (u x) (v x) ((A x)⁻¹ʳ w)`.
    let invVec : B × sphere (0 : W₀) 1 → E := fun p ↦
      twoFieldProj (u p.1) (v p.1) ((Ring.inverse (A p.1) (p.2 : W₀) : W₀) : E)
    have hA_inv_mul : ∀ x ∈ U, ∀ w : W₀, A x (Ring.inverse (A x) w) = w := by
      intro x hx w
      have hmul : A x * Ring.inverse (A x) = 1 := Ring.mul_inverse_cancel _ (hA_unit x hx)
      exact congrArg (fun T : W₀ →L[ℝ] W₀ ↦ T w) hmul
    have hP₀_invVec : ∀ p : B × sphere (0 : W₀) 1, p.1 ∈ U → P₀ (invVec p) = (p.2 : W₀) :=
      fun p hp ↦ hA_inv_mul p.1 hp (p.2 : W₀)
    have hinvVec_ne : ∀ p : B × sphere (0 : W₀) 1, p.1 ∈ U → invVec p ≠ 0 := by
      intro p hp hz
      have hEq : (p.2 : W₀) = 0 := by rw [← hP₀_invVec p hp, hz, map_zero]
      have h1 : ‖(p.2 : W₀)‖ = 1 := norm_eq_of_mem_sphere p.2
      rw [hEq, norm_zero] at h1
      exact zero_ne_one h1
    have hinvVec_cont : ContinuousOn invVec (U ×ˢ Set.univ) := by
      have hinvA : ContinuousOn (fun x : B ↦ Ring.inverse (A x)) U := fun x hx ↦
        ((NormedRing.inverse_continuousAt (R := W₀ →L[ℝ] W₀) (hA_unit x hx).unit).comp_of_eq
          hA_cont.continuousAt (hA_unit x hx).unit_spec.symm).continuousWithinAt
      have hclm : ContinuousOn (fun p : B × sphere (0 : W₀) 1 ↦
          Ring.inverse (A p.1) (p.2 : W₀)) (U ×ˢ Set.univ) :=
        (hinvA.comp (continuousOn_fst (s := U ×ˢ Set.univ))
          (fun _ hp ↦ (Set.mem_prod.1 hp).1)).clm_apply
          (continuous_subtype_val.comp continuous_snd).continuousOn
      exact ((continuous_twoFieldProj hu hv).comp continuous_fst).continuousOn.clm_apply
        (continuous_subtype_val.comp_continuousOn hclm)
    let toF : twoFieldEquators u v → B × F := fun xq ↦
      if hx : xq.1.1 ∈ U then
        (xq.1.1, eS ⟨‖P₀ (xq.1.2 : E)‖⁻¹ • P₀ (xq.1.2 : E),
          mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm (hP₀_ne xq hx))⟩)
      else (xq.1.1, w₀F)
    let invF : B × F → twoFieldEquators u v := fun p ↦
      if hp : p.1 ∈ U then
        let q := invVec (p.1, eS.symm p.2)
        ⟨(p.1, ⟨‖q‖⁻¹ • q, mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm (hinvVec_ne _ hp))⟩),
          mem_twoFieldEquators.2
            ⟨by rw [real_inner_smul_left]; simp [q, invVec, inner_twoFieldProj_fst (h p.1)],
             by rw [real_inner_smul_left]; simp [q, invVec, inner_twoFieldProj_snd (h p.1)]⟩⟩
      else z₀
    have htoF : ∀ (xq : twoFieldEquators u v) (hx : xq.1.1 ∈ U),
        toF xq = (xq.1.1, eS ⟨‖P₀ (xq.1.2 : E)‖⁻¹ • P₀ (xq.1.2 : E),
          mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm (hP₀_ne xq hx))⟩) :=
      fun _ hx ↦ dite_eq_left hx
    have hinvF_fst : ∀ p : B × F, p.1 ∈ U → (invF p).1.1 = p.1 := fun _ hp ↦ by
      simp only [invF, dite_eq_left hp]
    have hinvF_snd : ∀ p : B × F, p.1 ∈ U →
        ((invF p).1.2 : E) = ‖invVec (p.1, eS.symm p.2)‖⁻¹ • invVec (p.1, eS.symm p.2) :=
      fun _ hp ↦ by simp only [invF, dite_eq_left hp]
    have hleft : ∀ xq : twoFieldEquators u v, xq.1.1 ∈ U → invF (toF xq) = xq := by
      intro xq hx
      have hxq := mem_twoFieldEquators.1 xq.2
      have hto : (toF xq).1 = xq.1.1 := by rw [htoF xq hx]
      have htoU : (toF xq).1 ∈ U := hto ▸ hx
      apply Subtype.ext
      refine Prod.ext (by rw [hinvF_fst _ htoU, hto]) (Subtype.ext ?_)
      rw [hinvF_snd _ htoU, htoF xq hx]
      dsimp only
      rw [eS.symm_apply_apply]
      set r := ‖P₀ (xq.1.2 : E)‖
      have hr : 0 < r := norm_pos_iff.2 (hP₀_ne xq hx)
      set w : sphere (0 : W₀) 1 := ⟨r⁻¹ • P₀ (xq.1.2 : E),
        mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm (hP₀_ne xq hx))⟩
      set q0 := invVec (xq.1.1, w)
      have hq0_eq : q0 = r⁻¹ • (xq.1.2 : E) := by
        refine hP₀_inj xq.1.1 hx
          (inner_twoFieldProj_fst (h xq.1.1) _) (inner_twoFieldProj_snd (h xq.1.1) _)
          (by rw [real_inner_smul_left, hxq.1, mul_zero])
          (by rw [real_inner_smul_left, hxq.2, mul_zero]) ?_
        rw [map_smul]
        exact hP₀_invVec (xq.1.1, w) hx
      have hq0_norm : ‖q0‖ = r⁻¹ := by
        rw [hq0_eq, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le),
          norm_eq_of_mem_sphere xq.1.2, mul_one]
      rw [hq0_norm, inv_inv, hq0_eq, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hright : ∀ p : B × F, p.1 ∈ U → toF (invF p) = p := by
      intro p hp
      have hfst : (invF p).1.1 = p.1 := hinvF_fst p hp
      have hU' : (invF p).1.1 ∈ U := hfst.symm ▸ hp
      rw [htoF (invF p) hU']
      refine Prod.ext hfst ?_
      set w : sphere (0 : W₀) 1 := eS.symm p.2
      set q := invVec (p.1, w)
      have hsnd : ((invF p).1.2 : E) = ‖q‖⁻¹ • q := hinvF_snd p hp
      have hq_pos : 0 < ‖q‖ := norm_pos_iff.2 (hinvVec_ne (p.1, w) hp)
      have hPq : P₀ ((invF p).1.2 : E) = ‖q‖⁻¹ • (w : W₀) := by
        rw [hsnd, map_smul, hP₀_invVec (p.1, w) hp]
      have hPq_norm : ‖P₀ ((invF p).1.2 : E)‖ = ‖q‖⁻¹ := by
        rw [hPq, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hq_pos.le),
          norm_eq_of_mem_sphere w, mul_one]
      have hEqW : (⟨‖P₀ ((invF p).1.2 : E)‖⁻¹ • P₀ ((invF p).1.2 : E),
          mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm (hP₀_ne (invF p) hU'))⟩ :
          sphere (0 : W₀) 1) = w := by
        apply Subtype.ext
        dsimp only
        rw [hPq_norm, inv_inv, hPq, smul_smul, mul_inv_cancel₀ hq_pos.ne', one_smul]
      rw [hEqW, eS.apply_symm_apply]
    have hmem : ∀ {xq : twoFieldEquators u v},
        xq ∈ twoFieldEquatorsProj u v ⁻¹' U → xq.1.1 ∈ U := fun {xq} hx ↦ by
      have h' : twoFieldEquatorsProj u v xq ∈ U := Set.mem_preimage.1 hx
      rwa [twoFieldEquatorsProj_apply] at h'
    have hcont_toF : ContinuousOn toF (twoFieldEquatorsProj u v ⁻¹' U) := by
      rw [continuousOn_iff_continuous_domRestrict]
      refine Continuous.prodMk ?_ ?_
      · exact (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).congr
          fun xq ↦ congrArg Prod.fst (htoF xq.1 (hmem xq.2)).symm
      · have hP : Continuous fun xq : twoFieldEquatorsProj u v ⁻¹' U ↦ P₀ (xq.1.1.2 : E) :=
          P₀.continuous.comp (continuous_subtype_val.comp (continuous_snd.comp
            (continuous_subtype_val.comp continuous_subtype_val)))
        have hraw : Continuous fun xq : twoFieldEquatorsProj u v ⁻¹' U ↦
            ‖P₀ (xq.1.1.2 : E)‖⁻¹ • P₀ (xq.1.1.2 : E) :=
          (hP.norm.inv₀ fun xq ↦ norm_ne_zero_iff.2 (hP₀_ne xq.1 (hmem xq.2))).smul hP
        have hS : Continuous fun xq : twoFieldEquatorsProj u v ⁻¹' U ↦
            (⟨‖P₀ (xq.1.1.2 : E)‖⁻¹ • P₀ (xq.1.1.2 : E),
              mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm (hP₀_ne xq.1 (hmem xq.2)))⟩ :
              sphere (0 : W₀) 1) :=
          continuous_induced_rng.2 hraw
        exact (eS.continuous.comp hS).congr
          fun xq ↦ congrArg Prod.snd (htoF xq.1 (hmem xq.2)).symm
    have hcont_invF : ContinuousOn invF (U ×ˢ Set.univ) := by
      rw [continuousOn_iff_continuous_domRestrict]
      refine continuous_induced_rng.2 (Continuous.prodMk ?_ ?_)
      · refine (continuous_fst.comp continuous_subtype_val).congr fun p ↦ ?_
        exact (hinvF_fst p.1 p.2.1).symm
      · refine continuous_induced_rng.2 ?_
        have hpair : Continuous fun p : B × F ↦ (p.1, eS.symm p.2) :=
          continuous_fst.prodMk (eS.symm.continuous.comp continuous_snd)
        have hq_on : ContinuousOn (fun p : B × F ↦ invVec (p.1, eS.symm p.2)) (U ×ˢ Set.univ) :=
          hinvVec_cont.comp hpair.continuousOn (fun _ hp ↦ ⟨hp.1, trivial⟩)
        have hq : Continuous fun p : U ×ˢ Set.univ ↦ invVec (p.1.1, eS.symm p.1.2) :=
          continuousOn_iff_continuous_domRestrict.1 hq_on
        have hnormed : Continuous fun p : U ×ˢ Set.univ ↦
            ‖invVec (p.1.1, eS.symm p.1.2)‖⁻¹ • invVec (p.1.1, eS.symm p.1.2) :=
          (hq.norm.inv₀ fun p ↦ norm_ne_zero_iff.2 (hinvVec_ne _ p.2.1)).smul hq
        refine hnormed.congr fun p ↦ ?_
        exact (hinvF_snd p.1 p.2.1).symm
    exact ⟨{
      toFun := toF
      invFun := invF
      source := twoFieldEquatorsProj u v ⁻¹' U
      target := U ×ˢ Set.univ
      map_source' := fun xq hx ↦ by
        rw [htoF xq (hmem hx)]
        exact ⟨hmem hx, trivial⟩
      map_target' := fun p hp ↦ by
        rw [Set.mem_preimage, twoFieldEquatorsProj_apply, hinvF_fst p hp.1]
        exact hp.1
      left_inv' := fun xq hx ↦ hleft xq (hmem hx)
      right_inv' := fun p hp ↦ hright p hp.1
      open_source := hU_open.preimage (twoFieldEquatorsProj u v).continuous
      open_target := hU_open.prod isOpen_univ
      continuousOn_toFun := hcont_toF
      continuousOn_invFun := hcont_invF
      baseSet := U
      open_baseSet := hU_open
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun xq hx ↦
        (congrArg Prod.fst (htoF xq (hmem hx))).trans (twoFieldEquatorsProj_apply u v xq).symm },
      hx₀U⟩

/-- The projection `twoFieldEquatorsProj u v : twoFieldEquators u v → Sⁿ` is a Serre fibration
whenever `u, v` are continuous pointwise orthonormal vector fields on the unit sphere of a
finite-dimensional real inner product space of dimension at least `2`. -/
theorem TopCat.mem_serreFibrations_twoFieldEquatorsProj [FiniteDimensional ℝ E] {d : ℕ}
    (hE : finrank ℝ E = d + 2) {u v : sphere (0 : E) 1 → E}
    (hu : Continuous u) (hv : Continuous v)
    (h : ∀ x : sphere (0 : E) 1, Orthonormal ℝ ![u x, v x]) :
    TopCat.serreFibrations (_root_.TopCat.ofHom (twoFieldEquatorsProj u v)) :=
  TopCat.mem_serreFibrations_of_exists_trivialization
    (exists_trivialization_twoFieldEquators hE hu hv h)

/-- **Simple connectivity of the space of equators.** When `dim E ≥ 5` (so `n ≥ 4`, and both the
base sphere `Sⁿ` and the model fibre `Sⁿ⁻²` are simply connected), the total space
`twoFieldEquators u v` is simply connected. -/
theorem simplyConnectedSpace_twoFieldEquators [FiniteDimensional ℝ E] {d : ℕ}
    (hE : finrank ℝ E = d + 5) {u v : sphere (0 : E) 1 → E}
    (hu : Continuous u) (hv : Continuous v)
    (h : ∀ x : sphere (0 : E) 1, Orthonormal ℝ ![u x, v x]) :
    SimplyConnectedSpace (twoFieldEquators u v) := by
  have hrank : 2 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank, hE]
    exact_mod_cast (by omega : 2 < d + 5)
  have : SimplyConnectedSpace (sphere (0 : E) 1) := simplyConnectedSpace_sphere hrank 0 zero_le_one
  have : SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (d + 3))) 1) :=
    simplyConnectedSpace_sphere_euclideanSpace (n := d + 2) (by omega)
  exact simplyConnectedSpace_of_exists_trivialization
    (exists_trivialization_twoFieldEquators (d := d + 3) (by omega) hu hv h)

end EquatorBundle

/-! ### Local charts on a locally trivial bundle -/

/-- A local `ChartedSpace (B × F)` structure on the total space `Z` of a map `p : Z → B` admitting
local trivializations with fibre `F` over every point of `B`. Kept private and local to avoid
registering a competing `ChartedSpace` instance globally. -/
@[instance_reducible]
private def chartedSpaceOfExistsTrivialization {B F Z : Type*} [TopologicalSpace B]
    [TopologicalSpace F] [TopologicalSpace Z] {p : Z → B}
    (h : ∀ b, ∃ t : Trivialization F p, b ∈ t.baseSet) : ChartedSpace (B × F) Z where
  atlas := {t.toOpenPartialHomeomorph | t : Trivialization F p}
  chartAt z := (h (p z)).choose.toOpenPartialHomeomorph
  mem_chart_source z := (h (p z)).choose.mem_source.2 (h (p z)).choose_spec
  chart_mem_atlas z := ⟨(h (p z)).choose, rfl⟩

/-! ### Abundance with two-spheres from two tangent fields -/

section Abundance

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Homeomorphism between the unit sphere of `(ℝ ∙ v₀)ᗮ` inside `(ℝ ∙ u₀)ᗮ` and the equator of
`sphere (0 : (ℝ ∙ u₀)ᗮ) 1` orthogonal to `v₀`. -/
private def orthogonalSphereHomeomorphEquator {u₀ : E} (v₀ : (ℝ ∙ u₀)ᗮ) :
    sphere (0 : (ℝ ∙ v₀)ᗮ) 1 ≃ₜ sphereEquator v₀ where
  toFun := orthogonalSphereToEquator v₀
  invFun q := ⟨⟨q.1.1, Submodule.mem_orthogonal_singleton_iff_inner_left.2
    (mem_sphereEquator.1 q.2)⟩, by simp [norm_eq_of_mem_sphere]⟩
  left_inv s := Subtype.ext (Subtype.ext (coe_orthogonalSphereToEquator v₀ s))
  right_inv q := Subtype.ext (Subtype.ext (coe_orthogonalSphereToEquator v₀ _))
  continuous_toFun := (orthogonalSphereToEquator v₀).continuous
  continuous_invFun := by fun_prop

/-- Homeomorphism between `sphereEquator v₀` (where `v₀ : (ℝ ∙ u b)ᗮ` has underlying vector `v b`)
and the fibre of `twoFieldEquatorsProj u v` over `b`. -/
private def sphereEquatorHomeomorphFiber {u v : sphere (0 : E) 1 → E} (b : sphere (0 : E) 1)
    (huv : ⟪u b, v b⟫ = 0) :
    sphereEquator (⟨v b, Submodule.mem_orthogonal_singleton_iff_inner_right.2 huv⟩ : (ℝ ∙ u b)ᗮ) ≃ₜ
      (twoFieldEquatorsProj u v ⁻¹' {b} : Set (twoFieldEquators u v)) where
  toFun q :=
    ⟨⟨(b, ⟨((q.1 : (ℝ ∙ u b)ᗮ) : E), by
        rw [mem_sphere_zero_iff_norm, Submodule.norm_coe]
        exact norm_eq_of_mem_sphere q.1⟩),
      mem_twoFieldEquators.2
        ⟨Submodule.mem_orthogonal_singleton_iff_inner_left.1 (q.1 : (ℝ ∙ u b)ᗮ).2,
          (Submodule.coe_inner _ _ _).symm.trans (mem_sphereEquator.1 q.2)⟩⟩, rfl⟩
  invFun z :=
    ⟨⟨⟨(z.1.1.2 : E), Submodule.mem_orthogonal_singleton_iff_inner_left.2 (by
        have hz : z.1.1.1 = b := by
          have h' : twoFieldEquatorsProj u v z.1 = b := Set.mem_singleton_iff.1 z.2
          rwa [twoFieldEquatorsProj_apply] at h'
        have hmem := (mem_twoFieldEquators.1 z.1.2).1
        rwa [hz] at hmem)⟩, by
        rw [mem_sphere_zero_iff_norm]
        exact (Submodule.norm_coe _).symm.trans (norm_eq_of_mem_sphere z.1.1.2)⟩,
      mem_sphereEquator.2 (by
        have hz : z.1.1.1 = b := by
          have h' : twoFieldEquatorsProj u v z.1 = b := Set.mem_singleton_iff.1 z.2
          rwa [twoFieldEquatorsProj_apply] at h'
        have hmem := (mem_twoFieldEquators.1 z.1.2).2
        rw [hz] at hmem
        exact (Submodule.coe_inner _ _ _).trans hmem)⟩
  left_inv q := Subtype.ext (Subtype.ext (Subtype.ext rfl))
  right_inv z := by
    have hz : z.1.1.1 = b := by
      have h' : twoFieldEquatorsProj u v z.1 = b := Set.mem_singleton_iff.1 z.2
      rwa [twoFieldEquatorsProj_apply] at h'
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hz.symm (Subtype.ext rfl)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem orthonormal_pair_of_triple {x a b : E} (h : Orthonormal ℝ ![x, a, b]) :
    Orthonormal ℝ ![a, b] := by
  have hinj : Function.Injective (![1, 2] : Fin 2 → Fin 3) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  convert h.comp (![1, 2] : Fin 2 → Fin 3) hinj using 1
  ext i
  fin_cases i <;> rfl

private theorem isIso_map_homeomorph {α β : Type} [TopologicalSpace α] [TopologicalSpace β]
    (G : _root_.TopCat.{0} ⥤ ModuleCat.{0} ℤ) (e : α ≃ₜ β) :
    IsIso (G.map (_root_.TopCat.ofHom (⟨e, e.continuous⟩ : C(α, β)))) := by
  refine ⟨⟨G.map (_root_.TopCat.ofHom (⟨e.symm, e.symm.continuous⟩ : C(β, α))), ?_, ?_⟩⟩
  · rw [← G.map_comp, ← G.map_id]
    congr 1
    ext x
    exact e.symm_apply_apply x
  · rw [← G.map_comp, ← G.map_id]
    congr 1
    ext y
    exact e.apply_symm_apply y

open BasedTopologicalSpace in
/-- On the fibre over `b`, the restriction of `twoFieldSphereFamily h hu hv` induces an isomorphism
on degree `m + 2` singular homology with `ULift ℤ` coefficients. -/
private theorem isIso_twoFieldSphereFamily_fiber {m : ℕ}
    (hE5 : finrank ℝ E = m + 5) {u v : sphere (0 : E) 1 → E}
    (hu : Continuous u) (hv : Continuous v)
    (h : ∀ x : sphere (0 : E) 1, Orthonormal ℝ ![(x : E), u x, v x])
    (b : sphere (0 : E) 1) (huv_b : ⟪u b, v b⟫ = 0)
    (σbEq : C(sphereEquator (⟨v b, Submodule.mem_orthogonal_singleton_iff_inner_right.2 huv_b⟩ :
        (ℝ ∙ u b)ᗮ), BasedMap Sphere2 (sphere (0 : E) 1) Sphere2.north b))
    (hσ : ∀ q,
      (σbEq q).1 = twoFieldSphereFamily h hu hv (sphereEquatorHomeomorphFiber b huv_b q).1) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 2)).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map (_root_.TopCat.ofHom σbEq)) := by
  let u₀ : E := u b
  have hu₀ : ‖u₀‖ = 1 := by simpa [u₀] using (h b).norm_eq_one 1
  let v₀ : (ℝ ∙ u₀)ᗮ := ⟨v b, Submodule.mem_orthogonal_singleton_iff_inner_right.2 huv_b⟩
  have hv₀ : ‖v₀‖ = 1 := by
    rw [← Submodule.norm_coe]
    simpa [v₀] using (h b).norm_eq_one 2
  have hbu : ⟪u₀, (b : E)⟫ = 0 := by
    rw [real_inner_comm]
    simpa [u₀] using (h b).inner_eq_zero (by decide : (0 : Fin 3) ≠ 1)
  have hbv : ⟪(b : E), v b⟫ = 0 := by
    simpa using (h b).inner_eq_zero (by decide : (0 : Fin 3) ≠ 2)
  let b_orth : sphere (0 : (ℝ ∙ u₀)ᗮ) 1 :=
    ⟨⟨(b : E), Submodule.mem_orthogonal_singleton_iff_inner_right.2 hbu⟩, by
      rw [mem_sphere_zero_iff_norm]
      exact (Submodule.norm_coe _).symm.trans (norm_eq_of_mem_sphere b)⟩
  let b₀ : sphereEquator v₀ := ⟨b_orth, mem_sphereEquator.2 hbv⟩
  let b' : sphere (0 : E) 1 :=
    (orthogonalSphereToEquator u₀ (b₀ : sphere (0 : (ℝ ∙ u₀)ᗮ) 1) : sphere (0 : E) 1)
  have hb' : b' = b := Subtype.ext (coe_orthogonalSphereToEquator u₀ b_orth)
  let X : BasedTopologicalSpace.{0} := ⟨sphere (0 : E) 1, b'⟩
  let eBase : BasedMap Sphere2 (sphere (0 : E) 1) Sphere2.north b ≃ₜ
      BasedMap Sphere2 (sphere (0 : E) 1) Sphere2.north b' :=
    { toFun f := ⟨f.1, f.2.trans hb'.symm⟩
      invFun f := ⟨f.1, f.2.trans hb'⟩
      left_inv _ := Subtype.ext rfl
      right_inv _ := Subtype.ext rfl
      continuous_toFun := continuous_induced_rng.2 continuous_subtype_val
      continuous_invFun := continuous_induced_rng.2 continuous_subtype_val }
  let eLoop₀ : BasedMap Sphere2 (sphere (0 : E) 1) Sphere2.north b' ≃ₜ
      (X.iteratedLoopSpace 2).carrier :=
    basedMapSphereHomeomorphIteratedLoopSpace 2 X Sphere2.north
  let eLoop : BasedMap Sphere2 (sphere (0 : E) 1) Sphere2.north b ≃ₜ
      Ω (Ω (sphere (0 : E) 1) b') (Path.refl b') :=
    eBase.trans eLoop₀
  have hcomm : ∀ q, eLoop (σbEq q) = tangentCircleDoubleLoop hu₀ hv₀ b₀ q := by
    intro q
    apply (iteratedLoopSpaceHomeomorph 2 X).injective
    refine GenLoop.ext _ _ fun y ↦ Subtype.ext ?_
    have hL : (iteratedLoopSpaceHomeomorph 2 X (eLoop₀ (eBase (σbEq q))) y : E) =
        tangentCircle (b : E) u₀
          (tangentCircle (b : E) (v b) (((q.1 : (ℝ ∙ u₀)ᗮ) : E)) (2 * π * y 0)) (2 * π * y 1) := by
      rw [iteratedLoopSpaceHomeomorph_basedMapSphereHomeomorphIteratedLoopSpace,
        basedMapSphereHomeomorph_apply]
      have hq : (eBase (σbEq q)).1 =
          twoFieldSphereFamily h hu hv (sphereEquatorHomeomorphFiber b huv_b q).1 := hσ q
      rw [hq]
      exact coe_twoFieldSphereFamily_sphereCollapse h hu hv
        (sphereEquatorHomeomorphFiber b huv_b q).1 y
    have hR : (iteratedLoopSpaceHomeomorph 2 X (tangentCircleDoubleLoop hu₀ hv₀ b₀ q) y : E) =
        tangentCircle (b : E) u₀
          (tangentCircle (b : E) (v b) (((q.1 : (ℝ ∙ u₀)ᗮ) : E)) (2 * π * y 0)) (2 * π * y 1) := by
      rw [iteratedLoopSpaceHomeomorph_two_apply]
      rw [coe_tangentCircleDoubleLoop_apply hu₀ hv₀ b₀ q (y 0) (y 1)]
      simp [tangentCircle_def, b₀, b_orth, v₀]
    exact hL.trans hR.symm
  let R := ModuleCat.of ℤ ℤ
  let R₀ := ModuleCat.of ℤ (ULift.{0} ℤ)
  let H_Z := (singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 2)).obj R
  let H_U := (singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 2)).obj R₀
  let eLoopC : C(BasedMap Sphere2 (sphere (0 : E) 1) Sphere2.north b,
      Ω (Ω (sphere (0 : E) 1) b') (Path.refl b')) := ⟨eLoop, eLoop.continuous⟩
  have hIsoDouble : IsIso (H_Z.map (_root_.TopCat.ofHom (tangentCircleDoubleLoop hu₀ hv₀ b₀))) :=
    isIso_singularHomologyFunctor_map_tangentCircleDoubleLoop hE5 hu₀ hv₀ b₀
  have hIsoLoop : IsIso (H_Z.map (_root_.TopCat.ofHom eLoopC)) :=
    isIso_map_homeomorph H_Z eLoop
  have hEqMap : _root_.TopCat.ofHom σbEq ≫ _root_.TopCat.ofHom eLoopC =
      _root_.TopCat.ofHom (tangentCircleDoubleLoop hu₀ hv₀ b₀) :=
    ConcreteCategory.ext (DFunLike.ext _ _ hcomm)
  have hIsoσbEq_Z : IsIso (H_Z.map (_root_.TopCat.ofHom σbEq)) := by
    have hcomp : H_Z.map (_root_.TopCat.ofHom σbEq) ≫ H_Z.map (_root_.TopCat.ofHom eLoopC) =
        H_Z.map (_root_.TopCat.ofHom (tangentCircleDoubleLoop hu₀ hv₀ b₀)) := by
      rw [← H_Z.map_comp, hEqMap]
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ (H_Z.map (_root_.TopCat.ofHom σbEq))
      (H_Z.map (_root_.TopCat.ofHom eLoopC)) hIsoLoop (hcomp.symm ▸ hIsoDouble)
  let φ : R ≅ R₀ := (ULift.moduleEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ).toModuleIso.symm
  let η := (singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 2)).mapIso φ
  have hnat := η.hom.naturality (_root_.TopCat.ofHom σbEq)
  have heq : H_U.map (_root_.TopCat.ofHom σbEq) =
      η.inv.app _ ≫ H_Z.map (_root_.TopCat.ofHom σbEq) ≫ η.hom.app _ := by
    rw [hnat, ← Category.assoc, ← NatTrans.comp_app, η.inv_hom_id, NatTrans.id_app,
      Category.id_comp]
  rw [heq]
  exact IsIso.comp_isIso' (Iso.isIso_inv (η.app _))
    (IsIso.comp_isIso' hIsoσbEq_Z (Iso.isIso_hom (η.app _)))

/-- **Abundance with two-spheres from two orthonormal tangent fields** (Barraud–Damian–Humilière–
Oancea, Example 6.20 and Propositions 6.15 and 6.21). If the unit sphere `Sⁿ` of a real inner
product space `E` of dimension `n + 1 ≥ 5` carries two continuous vector fields `u, v : Sⁿ → E`
such that `(x, u x, v x)` is orthonormal for every `x ∈ Sⁿ`, then `Sⁿ` is abundant with two-spheres
at every point `b ∈ Sⁿ`. -/
theorem isAbundantWithTwoSpheres_sphere_of_twoField {n : ℕ} (hn : 4 ≤ n)
    (hE : finrank ℝ E = n + 1) {u v : sphere (0 : E) 1 → E}
    (hu : Continuous u) (hv : Continuous v)
    (h : ∀ x : sphere (0 : E) 1, Orthonormal ℝ ![(x : E), u x, v x])
    (b : sphere (0 : E) 1) :
    IsAbundantWithTwoSpheres (sphere (0 : E) 1) n b := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have hE5 : finrank ℝ E = m + 5 := by omega
  have huv : ∀ x : sphere (0 : E) 1, Orthonormal ℝ ![u x, v x] := fun x ↦
    orthonormal_pair_of_triple (h x)
  have htriv : ∀ x₀ : sphere (0 : E) 1,
      ∃ t : Trivialization (sphere (0 : EuclideanSpace ℝ (Fin (m + 3))) 1)
        (twoFieldEquatorsProj u v), x₀ ∈ t.baseSet :=
    exists_trivialization_twoFieldEquators (d := m + 3) (by omega) hu hv huv
  have hp : TopCat.serreFibrations (_root_.TopCat.ofHom (twoFieldEquatorsProj u v)) :=
    TopCat.mem_serreFibrations_of_exists_trivialization htriv
  have : SimplyConnectedSpace (twoFieldEquators u v) :=
    simplyConnectedSpace_twoFieldEquators hE5 hu hv huv
  have : CompactSpace (twoFieldEquators u v) :=
    isCompact_iff_compactSpace.1 (isCompact_twoFieldEquators hu hv)
  -- Put a local Euclidean manifold chart structure on `twoFieldEquators u v`.
  let F₀ := sphere (0 : EuclideanSpace ℝ (Fin (m + 3))) 1
  have : Fact (finrank ℝ E = (m + 4) + 1) := ⟨hE⟩
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (m + 3))) = (m + 2) + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let _ : ChartedSpace (sphere (0 : E) 1 × F₀) (twoFieldEquators u v) :=
    chartedSpaceOfExistsTrivialization htriv
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin ((m + 4) + (m + 2)))) (sphere (0 : E) 1 × F₀) :=
    prodEuclideanChartedSpace
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin ((m + 4) + (m + 2)))) (twoFieldEquators u v) :=
    ChartedSpace.comp (EuclideanSpace ℝ (Fin ((m + 4) + (m + 2)))) (sphere (0 : E) 1 × F₀)
      (twoFieldEquators u v)
  have hdimM : finrank ℝ (EuclideanSpace ℝ (Fin ((m + 4) + (m + 2)))) = (m + 4) + (m + 2) :=
    finrank_euclideanSpace_fin
  obtain ⟨oM⟩ := HomologicalOrientation.nonempty_of_simplyConnectedSpace
    (M := twoFieldEquators u v) (E := EuclideanSpace ℝ (Fin ((m + 4) + (m + 2)))) hdimM
  -- Set up the fibre manifold `F = sphere (0 : (ℝ ∙ v₀)ᗮ) 1` over `b`.
  let u₀ : E := u b
  have hu₀ : ‖u₀‖ = 1 := by simpa [u₀] using (h b).norm_eq_one 1
  have huv_b : ⟪u₀, v b⟫ = 0 := by
    simpa [u₀] using (h b).inner_eq_zero (by decide : (1 : Fin 3) ≠ 2)
  let v₀ : (ℝ ∙ u₀)ᗮ := ⟨v b, Submodule.mem_orthogonal_singleton_iff_inner_right.2 huv_b⟩
  have hv₀ : ‖v₀‖ = 1 := by
    rw [← Submodule.norm_coe]
    simpa [v₀] using (h b).norm_eq_one 2
  have hu₀_ne : u₀ ≠ 0 := by intro hz; simp [hz] at hu₀
  have hv₀_ne : v₀ ≠ 0 := by intro hz; simp [hz] at hv₀
  have hU_dim : finrank ℝ (ℝ ∙ u₀)ᗮ = m + 4 :=
    Submodule.finrank_orthogonal_span_singleton (n := m + 4) hu₀_ne
  have : Fact (finrank ℝ (ℝ ∙ u₀)ᗮ = (m + 3) + 1) := ⟨hU_dim⟩
  have hF_dim : finrank ℝ (ℝ ∙ v₀)ᗮ = m + 3 :=
    Submodule.finrank_orthogonal_span_singleton (n := m + 3) hv₀_ne
  have : Fact (finrank ℝ (ℝ ∙ v₀)ᗮ = (m + 2) + 1) := ⟨hF_dim⟩
  let F := sphere (0 : (ℝ ∙ v₀)ᗮ) 1
  have hrankF : 2 < Module.rank ℝ (ℝ ∙ v₀)ᗮ := by
    rw [← Module.finrank_eq_rank, hF_dim]
    exact_mod_cast (by omega : 2 < m + 3)
  have : SimplyConnectedSpace F := simplyConnectedSpace_sphere hrankF 0 zero_le_one
  have hdimF : finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2 := finrank_euclideanSpace_fin
  obtain ⟨oF⟩ := HomologicalOrientation.nonempty_of_simplyConnectedSpace
    (M := F) (E := EuclideanSpace ℝ (Fin (m + 2))) hdimF
  let eEq : F ≃ₜ sphereEquator v₀ := orthogonalSphereHomeomorphEquator v₀
  let eEqFib : sphereEquator v₀ ≃ₜ
      (twoFieldEquatorsProj u v ⁻¹' {b} : Set (twoFieldEquators u v)) :=
    sphereEquatorHomeomorphFiber b huv_b
  let eF : F ≃ₜ (twoFieldEquatorsProj u v ⁻¹' {b} : Set (twoFieldEquators u v)) :=
    eEq.trans eEqFib
  -- Restrict `twoFieldSphereFamily h hu hv` to the fibre over `b`.
  let fam := twoFieldSphereFamily h hu hv
  have hfam : mappingSpaceEval Sphere2.north ∘ fam = twoFieldEquatorsProj u v :=
    congrArg DFunLike.coe (mappingSpaceEval_comp_twoFieldSphereFamily h hu hv)
  let σbEq : C(sphereEquator v₀, BasedMap Sphere2 (sphere (0 : E) 1) Sphere2.north b) :=
    ⟨fun q ↦ ⟨fam (eEqFib q).1, twoFieldSphereFamily_north h hu hv (eEqFib q).1⟩,
      continuous_induced_rng.2
        (fam.continuous.comp (continuous_subtype_val.comp eEqFib.continuous))⟩
  let eEqC : C(F, sphereEquator v₀) := ⟨eEq, eEq.continuous⟩
  let σb : C(F, BasedMap Sphere2 (sphere (0 : E) 1) Sphere2.north b) := σbEq.comp eEqC
  let H_U := (singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 2)).obj (ModuleCat.of ℤ (ULift.{0} ℤ))
  have hIsoσbEq : IsIso (H_U.map (_root_.TopCat.ofHom σbEq)) :=
    isIso_twoFieldSphereFamily_fiber hE5 hu hv h b huv_b σbEq (fun _ ↦ rfl)
  have hIsoEq : IsIso (H_U.map (_root_.TopCat.ofHom eEqC)) :=
    isIso_map_homeomorph H_U eEq
  have hIsoσb_U : IsIso (H_U.map (_root_.TopCat.ofHom σb)) := by
    have hfac : _root_.TopCat.ofHom σb =
        _root_.TopCat.ofHom eEqC ≫ _root_.TopCat.ofHom σbEq := by
      ext _
      rfl
    rw [hfac, H_U.map_comp]
    exact IsIso.comp_isIso' hIsoEq hIsoσbEq
  have hσb_ne : oF.mapFundamentalClass hdimF σb ≠ 0 := by
    obtain ⟨f₀⟩ : Nonempty F := inferInstance
    let γF : H_U.obj (_root_.TopCat.of F) := oF.fundamentalClass hdimF
    have hneF : γF ≠ 0 :=
      (oF.livesOverFundamentalClass_id_iff hdimF f₀ (oF.fundamentalClass hdimF)).1
        (oF.livesOverFundamentalClass_id_fundamentalClass hdimF f₀)
    intro hz
    rw [oF.mapFundamentalClass_def hdimF σb] at hz
    have hinv := @IsIso.hom_inv_id _ _ _ _ (H_U.map (_root_.TopCat.ofHom σb)) hIsoσb_U
    have h1 := ConcreteCategory.congr_hom hinv γF
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at h1
    have h2 : (@inv _ _ _ _ (H_U.map (_root_.TopCat.ofHom σb)) hIsoσb_U)
        (H_U.map (_root_.TopCat.ofHom σb) γF) = γF := h1
    rw [hz, map_zero] at h2
    exact hneF h2.symm
  exact oM.isAbundantWithTwoSpheres_of_pos hdimM oF hdimF
    (chartAt (EuclideanSpace ℝ (Fin (m + 4))) b) (mem_chart_source _ b)
    (finrank_euclideanSpace_fin (n := m + 4)) (by omega) (by omega)
    hp eF fam hfam σb (fun _ ↦ rfl) hσb_ne

omit [InnerProductSpace ℝ E] in
/-- Right multiplication by a quaternion is continuous under `[NormSMulClass ℍᵐᵒᵖ E]`. -/
private theorem continuous_op_smul_quaternion [Module ℍᵐᵒᵖ E] [NormSMulClass ℍᵐᵒᵖ E] (q : ℍ) :
    Continuous fun x : E ↦ x <• q :=
  (LipschitzWith.of_dist_le_mul (K := ‖q‖₊) fun x y ↦ by
    simp [dist_eq_norm, ← smul_sub, norm_smul, norm_op]).continuous

/-- **Abundance with two-spheres for quaternionic unit spheres `Sⁿ` (`n ≥ 4`).** Any real inner
product space `E` carrying a norm-compatible right action of `ℍ` carries two pointwise orthonormal
tangent vector fields (`x <• i` and `x <• j`), so its unit sphere is abundant with two-spheres
whenever `dim E = n + 1 ≥ 5`. -/
theorem isAbundantWithTwoSpheres_sphere_of_quaternion [Module ℍᵐᵒᵖ E] [NormSMulClass ℍᵐᵒᵖ E]
    {n : ℕ} (hn : 4 ≤ n) (hE : finrank ℝ E = n + 1) (b : sphere (0 : E) 1) :
    IsAbundantWithTwoSpheres (sphere (0 : E) 1) n b := by
  let u : sphere (0 : E) 1 → E := fun x ↦ quaternionFrame (x : E) 0
  let v : sphere (0 : E) 1 → E := fun x ↦ quaternionFrame (x : E) 1
  have hu : Continuous u :=
    ((continuous_op_smul_quaternion _).comp continuous_subtype_val).congr
      fun x ↦ (quaternionFrame_zero (x : E)).symm
  have hv : Continuous v :=
    ((continuous_op_smul_quaternion _).comp continuous_subtype_val).congr
      fun x ↦ (quaternionFrame_one (x : E)).symm
  exact isAbundantWithTwoSpheres_sphere_of_twoField hn hE hu hv
    (fun x ↦ orthonormal_vecCons_quaternionFrame_of_ne (norm_eq_of_mem_sphere x)
      (by decide : (0 : Fin 3) ≠ 1)) b

/-- **All spheres `S^{4k-1}` (`k ≥ 1`) are abundant with two-spheres** (Barraud–Damian–Humilière–
Oancea, Example 6.20 and Propositions 6.15, 6.21, and 6.31). Every unit sphere in a real inner
product space of dimension `4k` (`k ≥ 1`) is abundant with two-spheres at every point: `S³`
(`k = 1`) via the group structure of the unit quaternions
(`TauCeti.isAbundantWithTwoSpheres_sphere_quaternion`), and `S^{4k-1}` (`k ≥ 2`) via the fibred
family of two-spheres swept out by two quaternionic tangent vector fields. -/
theorem isAbundantWithTwoSpheres_sphere_of_finrank_eq_four_mul {k : ℕ} (hk : k ≠ 0)
    (hE : finrank ℝ E = 4 * k) (b : sphere (0 : E) 1) :
    IsAbundantWithTwoSpheres (sphere (0 : E) 1) (4 * k - 1) b := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  by_cases hk1 : k = 1
  · subst hk1
    have hdim : finrank ℝ E = finrank ℝ ℍ := by rw [hE, Quaternion.finrank_eq_four]
    let e : E ≃ₗᵢ[ℝ] ℍ :=
      (stdOrthonormalBasis ℝ E).equiv (stdOrthonormalBasis ℝ ℍ) (finCongr hdim)
    exact (e.unitSphereIsometryEquiv.toHomeomorph.isAbundantWithTwoSpheres_iff 3 b).2
      (isAbundantWithTwoSpheres_sphere_quaternion _)
  · have hdim : finrank ℝ E = finrank ℝ (PiLp 2 fun _ : Fin k ↦ ℍ) := by
      rw [hE, finrank_piLp_quaternion]
      simp
    let e : E ≃ₗᵢ[ℝ] PiLp 2 fun _ : Fin k ↦ ℍ :=
      (stdOrthonormalBasis ℝ E).equiv (stdOrthonormalBasis ℝ _) (finCongr hdim)
    refine (e.unitSphereIsometryEquiv.toHomeomorph.isAbundantWithTwoSpheres_iff (4 * k - 1) b).2 ?_
    exact isAbundantWithTwoSpheres_sphere_of_quaternion (n := 4 * k - 1) (by omega)
      (by rw [finrank_piLp_quaternion]; simp; omega) _

end Abundance

end TauCeti
