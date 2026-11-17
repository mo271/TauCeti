/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Contraction
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence

/-!
# Smooth good covers of manifolds

A *smooth good cover* (`TauCeti.SmoothGoodCover`) of a manifold `M` is a locally finite open
cover `openSet : Index → TopologicalSpace.Opens M` equipped, for every nonempty finite subset `s`
of indices whose intersection `W = s.inf openSet` is nonempty, with a chosen centre `q ∈ W` and a
globally smooth contraction `contract : ℝ × W → W` that collapses `W` to `q` at time `0`, is the
identity at time `1`, and fixes `q` at all times.

Every nonempty finite intersection of a smooth good cover is therefore path-connected
(`TauCeti.SmoothGoodCover.isPathConnected_inter`,
`TauCeti.SmoothGoodCover.pathConnectedSpace_inter`), connected
(`TauCeti.SmoothGoodCover.isConnected_inter`), and contractible
(`TauCeti.SmoothGoodCover.contractibleSpace_inter`). Restricting and swapping the arguments of
`contract` produces a smooth cylinder map `W × [0, 1] → W` (`TauCeti.SmoothGoodCover.contractIcc`)
for the model `I.prod (𝓡∂ 1)`, feeding directly into `TauCeti.homotopyOperator` to establish the
cochain-homotopy identity `d (h (H^* φ)) + h (d (H^* φ)) = φ` and exactness of closed forms of
positive degree on every nonempty finite intersection.

Using strongly geodesically convex uniformly normal balls for a Riemannian metric
(`TauCeti.Manifold.exists_pos_forall_isNormalDomain_and_isStronglyGeodesicallyConvex_eball`) and
their smooth radial contractions (`TauCeti.Manifold.geodesicContractionOpens`), we prove that
every open cover of a finite-dimensional σ-compact boundaryless smooth Riemannian manifold admits
a locally finite refinement by a smooth good cover
(`TauCeti.exists_smoothGoodCover_refining_of_riemannian`, via a compact exhaustion into annuli).
Restricting to nonempty open sets (`TauCeti.SmoothGoodCover.restrictNonempty`) immediately yields
a finite smooth good cover when `M` is compact
(`TauCeti.exists_finite_smoothGoodCover_refining_of_riemannian`). Choosing an auxiliary smooth
Riemannian metric via `TauCeti.nonempty_contMDiffRiemannianMetric` and transporting across
`TauCeti.WithMetric.diffeomorph` removes the prescribed metric hypothesis
(`TauCeti.exists_smoothGoodCover_refining_of_sigmaCompact`,
`TauCeti.exists_smoothGoodCover_refining`, and `TauCeti.exists_finite_smoothGoodCover_refining`).

## Main definitions and results

* `TauCeti.SmoothGoodCover`: locally finite open covers with smooth contractions on nonempty finite
  intersections.
* `TauCeti.SmoothGoodCover.isPathConnected_inter`, `TauCeti.SmoothGoodCover.isConnected_inter`,
  `TauCeti.SmoothGoodCover.contractibleSpace_inter`: topological consequences on nonempty finite
  intersections.
* `TauCeti.SmoothGoodCover.contractIcc`, `TauCeti.SmoothGoodCover.contMDiff_contractIcc`,
  `TauCeti.SmoothGoodCover.mextDeriv_homotopyOperator_mpullback_contractIcc`: cylinder restriction
  and compatibility with `TauCeti.homotopyOperator`.
* `TauCeti.SmoothGoodCover.empty`, `TauCeti.SmoothGoodCover.ofConvex`,
  `TauCeti.SmoothGoodCover.ofNormedSpace`: concrete smooth good covers.
* `TauCeti.SmoothGoodCover.restrictNonempty`,
  `TauCeti.SmoothGoodCover.finite_index_restrictNonempty`,
  `TauCeti.SmoothGoodCover.comapDiffeomorph`: restricting to nonempty sets and transport along a
  diffeomorphism.
* `TauCeti.exists_smoothGoodCover_refining_of_riemannian`,
  `TauCeti.exists_finite_smoothGoodCover_refining_of_riemannian`: refinement theorems for any given
  smooth Riemannian metric.
* `TauCeti.exists_smoothGoodCover_refining_of_sigmaCompact`,
  `TauCeti.exists_smoothGoodCover_refining`, `TauCeti.exists_finite_smoothGoodCover_refining`:
  refinement theorems for smooth manifolds without a prescribed metric.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Springer GTM 82, 1982, §5
  (good covers, Theorem 5.1).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, 2018, Ch. 6,
  Theorem 6.17 (strongly convex neighbourhoods).
-/

public section

noncomputable section

open Bundle Filter Function Manifold Metric Set TopologicalSpace
open scoped ContDiff ENNReal Manifold Topology

namespace TauCeti

/-! ### Definition and basic API -/

section Basic

universe u v

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

/-- A **smooth good cover** of a manifold `M`: a locally finite open cover such that every nonempty
finite intersection `W` carries a chosen centre and a globally smooth contraction `ℝ × W → W` from
the constant map at the centre (time `0`) to the identity (time `1`) fixing the centre at all
times. -/
structure SmoothGoodCover where
  /-- The index type of the cover. -/
  Index : Type u
  /-- The open sets of the cover. -/
  openSet : Index → Opens M
  /-- The open sets cover `M`. -/
  covers : ∀ x : M, ∃ i, x ∈ openSet i
  /-- The cover is locally finite. -/
  locallyFinite : LocallyFinite (fun i ↦ (openSet i : Set M))
  /-- The chosen centre of each nonempty finite intersection. -/
  centre : ∀ (s : Finset Index), s.Nonempty →
    ((s.inf openSet : Opens M) : Set M).Nonempty → ↥(s.inf openSet)
  /-- The chosen smooth contraction of each nonempty finite intersection. -/
  contract : ∀ (s : Finset Index) (_hs : s.Nonempty)
    (_hW : ((s.inf openSet : Opens M) : Set M).Nonempty),
    ℝ × ↥(s.inf openSet) → ↥(s.inf openSet)
  /-- Each contraction is smooth on `ℝ × W`. -/
  smooth : ∀ s hs hW, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (contract s hs hW)
  /-- At time `0`, the contraction collapses every point to the centre. -/
  at_zero : ∀ s hs hW x, contract s hs hW (0, x) = centre s hs hW
  /-- At time `1`, the contraction is the identity. -/
  at_one : ∀ s hs hW x, contract s hs hW (1, x) = x
  /-- The contraction fixes the centre at every time. -/
  fixes_centre : ∀ s hs hW t, contract s hs hW (t, centre s hs hW) = centre s hs hW

namespace SmoothGoodCover

variable {I}

/-- The finite intersection `s.inf C.openSet` associated to a finite index set `s`. -/
abbrev inter (C : SmoothGoodCover I (M := M)) (s : Finset C.Index) : Opens M :=
  s.inf C.openSet

/-- The carrier set of a finite intersection `C.inter s` is the indexed intersection
`⋂ i ∈ s, (C.openSet i : Set M)`. -/
theorem coe_inter (C : SmoothGoodCover I (M := M)) (s : Finset C.Index) :
    ((C.inter s : Opens M) : Set M) = ⋂ i ∈ s, (C.openSet i : Set M) := by
  rw [inter, Opens.coe_finset_inf, Finset.inf_eq_iInf]
  simp [Set.iInf_eq_iInter]

/-- Membership in a finite intersection `C.inter s`. -/
@[simp]
theorem mem_inter_iff (C : SmoothGoodCover I (M := M)) {s : Finset C.Index} {x : M} :
    x ∈ C.inter s ↔ ∀ i ∈ s, x ∈ C.openSet i := by
  rw [← SetLike.mem_coe, C.coe_inter s]
  simp

/-- At time `0`, `C.contract` collapses every point to the chosen centre. -/
@[simp]
theorem contract_zero (C : SmoothGoodCover I (M := M)) (s : Finset C.Index) (hs : s.Nonempty)
    (hW : ((C.inter s : Opens M) : Set M).Nonempty) (x : ↥(C.inter s)) :
    C.contract s hs hW (0, x) = C.centre s hs hW :=
  C.at_zero s hs hW x

/-- At time `1`, `C.contract` is the identity. -/
@[simp]
theorem contract_one (C : SmoothGoodCover I (M := M)) (s : Finset C.Index) (hs : s.Nonempty)
    (hW : ((C.inter s : Opens M) : Set M).Nonempty) (x : ↥(C.inter s)) :
    C.contract s hs hW (1, x) = x :=
  C.at_one s hs hW x

/-- `C.contract` fixes the chosen centre at every time. -/
@[simp]
theorem contract_centre (C : SmoothGoodCover I (M := M)) (s : Finset C.Index) (hs : s.Nonempty)
    (hW : ((C.inter s : Opens M) : Set M).Nonempty) (t : ℝ) :
    C.contract s hs hW (t, C.centre s hs hW) = C.centre s hs hW :=
  C.fixes_centre s hs hW t

/-! ### Topological properties of finite intersections -/

/-- Every nonempty finite intersection of a smooth good cover is path-connected as a subspace. -/
theorem pathConnectedSpace_inter (C : SmoothGoodCover I (M := M)) (s : Finset C.Index)
    (hs : s.Nonempty) (hW : ((C.inter s : Opens M) : Set M).Nonempty) :
    PathConnectedSpace ↥(C.inter s) := by
  refine PathConnectedSpace.mk ⟨C.centre s hs hW⟩ fun x y ↦ ?_
  have hjoin (z : ↥(C.inter s)) : Joined (C.centre s hs hW) z := by
    refine ⟨⟨⟨fun t ↦ C.contract s hs hW (t.1, z), ?_⟩, ?_, ?_⟩⟩
    · exact (C.smooth s hs hW).continuous.comp
        (continuous_subtype_val.prodMk continuous_const)
    · simp
    · simp
  exact (hjoin x).symm.trans (hjoin y)

/-- Every nonempty finite intersection of a smooth good cover is path-connected as a subset of
`M`. -/
theorem isPathConnected_inter (C : SmoothGoodCover I (M := M)) (s : Finset C.Index)
    (hs : s.Nonempty) (hW : ((C.inter s : Opens M) : Set M).Nonempty) :
    IsPathConnected ((C.inter s : Opens M) : Set M) := by
  have := C.pathConnectedSpace_inter s hs hW
  exact isPathConnected_iff_pathConnectedSpace.2 inferInstance

/-- Every nonempty finite intersection of a smooth good cover is connected as a subspace. -/
theorem connectedSpace_inter (C : SmoothGoodCover I (M := M)) (s : Finset C.Index)
    (hs : s.Nonempty) (hW : ((C.inter s : Opens M) : Set M).Nonempty) :
    ConnectedSpace ↥(C.inter s) := by
  have := C.pathConnectedSpace_inter s hs hW
  infer_instance

/-- Every nonempty finite intersection of a smooth good cover is connected as a subset of `M`. -/
theorem isConnected_inter (C : SmoothGoodCover I (M := M)) (s : Finset C.Index)
    (hs : s.Nonempty) (hW : ((C.inter s : Opens M) : Set M).Nonempty) :
    IsConnected ((C.inter s : Opens M) : Set M) :=
  (C.isPathConnected_inter s hs hW).isConnected

/-- Every nonempty finite intersection of a smooth good cover is contractible. -/
theorem contractibleSpace_inter (C : SmoothGoodCover I (M := M)) (s : Finset C.Index)
    (hs : s.Nonempty) (hW : ((C.inter s : Opens M) : Set M).Nonempty) :
    ContractibleSpace ↥(C.inter s) := by
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨C.centre s hs hW, ⟨⟨⟨fun p ↦ C.contract s hs hW (1 - p.1.1, p.2), ?_⟩, ?_, ?_⟩⟩⟩
  · exact (C.smooth s hs hW).continuous.comp
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
  · intro x
    simp [C.at_one]
  · intro x
    simp [C.at_zero]

/-! ### Cylinder restriction and compatibility with `TauCeti.homotopyOperator` -/

/-- The product-swapped restriction of `C.contract` to the cylinder `W × [0, 1]` with model
`I.prod (𝓡∂ 1)`, matching the domain convention of `TauCeti.homotopyOperator`. -/
def contractIcc (C : SmoothGoodCover I (M := M)) (s : Finset C.Index) (hs : s.Nonempty)
    (hW : ((C.inter s : Opens M) : Set M).Nonempty)
    (p : ↥(C.inter s) × Icc (0 : ℝ) 1) : ↥(C.inter s) :=
  C.contract s hs hW (p.2.1, p.1)

/-- The cylinder contraction `C.contractIcc s hs hW` is smooth for the boundary cylinder model
`I.prod (𝓡∂ 1)`. -/
theorem contMDiff_contractIcc (C : SmoothGoodCover I (M := M)) (s : Finset C.Index)
    (hs : s.Nonempty) (hW : ((C.inter s : Opens M) : Set M).Nonempty) :
    ContMDiff (I.prod (𝓡∂ 1)) I ∞ (C.contractIcc s hs hW) :=
  (C.smooth s hs hW).comp
    ((contMDiff_subtypeVal_Icc.comp contMDiff_snd).prodMk contMDiff_fst)

/-- At time `0`, `C.contractIcc` collapses every point to the chosen centre. -/
@[simp]
theorem contractIcc_zero (C : SmoothGoodCover I (M := M)) (s : Finset C.Index) (hs : s.Nonempty)
    (hW : ((C.inter s : Opens M) : Set M).Nonempty) (x : ↥(C.inter s)) :
    C.contractIcc s hs hW (x, (0 : Icc (0 : ℝ) 1)) = C.centre s hs hW :=
  C.at_zero s hs hW x

/-- At time `1`, `C.contractIcc` is the identity. -/
@[simp]
theorem contractIcc_one (C : SmoothGoodCover I (M := M)) (s : Finset C.Index) (hs : s.Nonempty)
    (hW : ((C.inter s : Opens M) : Set M).Nonempty) (x : ↥(C.inter s)) :
    C.contractIcc s hs hW (x, (1 : Icc (0 : ℝ) 1)) = x :=
  C.at_one s hs hW x

/-- `C.contractIcc` fixes the chosen centre at every time in `[0, 1]`. -/
@[simp]
theorem contractIcc_centre (C : SmoothGoodCover I (M := M)) (s : Finset C.Index) (hs : s.Nonempty)
    (hW : ((C.inter s : Opens M) : Set M).Nonempty) (t : Icc (0 : ℝ) 1) :
    C.contractIcc s hs hW (C.centre s hs hW, t) = C.centre s hs hW :=
  C.fixes_centre s hs hW t.1

section HomotopyOperator

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The time-`1` slice of the pullback of a form along `contractIcc` recovers the original form. -/
theorem mpullback_contractIcc_slice_one (C : SmoothGoodCover I (M := M)) (s : Finset C.Index)
    (hs : s.Nonempty) (hW : ((C.inter s : Opens M) : Set M).Nonempty) {k : ℕ}
    (φ : RoughForm I ↥(C.inter s) F k) :
    mpullback I (I.prod (𝓡∂ 1)) (fun x ↦ (x, (1 : Icc (0 : ℝ) 1)))
        (mpullback (I.prod (𝓡∂ 1)) I (C.contractIcc s hs hW) φ) = φ := by
  have h1 : MDifferentiable I (I.prod (𝓡∂ 1))
      (fun x : ↥(C.inter s) ↦ (x, (1 : Icc (0 : ℝ) 1))) :=
    mdifferentiable_id.prodMk mdifferentiable_const
  have hH : MDifferentiable (I.prod (𝓡∂ 1)) I (C.contractIcc s hs hW) :=
    (C.contMDiff_contractIcc s hs hW).mdifferentiable (by simp)
  rw [← mpullback_comp h1 hH]
  have hcomp : (C.contractIcc s hs hW ∘ fun x ↦ (x, (1 : Icc (0 : ℝ) 1))) = id :=
    funext fun x ↦ C.contractIcc_one s hs hW x
  rw [hcomp, mpullback_id]

/-- The time-`0` slice of the pullback of a positive-degree form along `contractIcc` vanishes,
since `contractIcc (·, 0)` is constant at the centre. -/
theorem mpullback_contractIcc_slice_zero (C : SmoothGoodCover I (M := M)) (s : Finset C.Index)
    (hs : s.Nonempty) (hW : ((C.inter s : Opens M) : Set M).Nonempty) {k : ℕ}
    (φ : RoughForm I ↥(C.inter s) F (k + 1)) :
    mpullback I (I.prod (𝓡∂ 1)) (fun x ↦ (x, (0 : Icc (0 : ℝ) 1)))
        (mpullback (I.prod (𝓡∂ 1)) I (C.contractIcc s hs hW) φ) = 0 := by
  have h0 : MDifferentiable I (I.prod (𝓡∂ 1))
      (fun x : ↥(C.inter s) ↦ (x, (0 : Icc (0 : ℝ) 1))) :=
    mdifferentiable_id.prodMk mdifferentiable_const
  have hH : MDifferentiable (I.prod (𝓡∂ 1)) I (C.contractIcc s hs hW) :=
    (C.contMDiff_contractIcc s hs hW).mdifferentiable (by simp)
  rw [← mpullback_comp h0 hH]
  have hcomp : (C.contractIcc s hs hW ∘ fun x ↦ (x, (0 : Icc (0 : ℝ) 1))) =
      fun _ ↦ C.centre s hs hW :=
    funext fun x ↦ C.contractIcc_zero s hs hW x
  rw [hcomp]
  funext x
  ext v
  rw [mpullback_apply, mfderiv_const]
  exact (φ (C.centre s hs hW)).map_coord_zero 0 rfl

/-- **Cochain-homotopy identity on nonempty finite intersections.** For any `C¹` `(k + 1)`-form `φ`
with values in a Banach space on a nonempty finite intersection `W` of a smooth good cover (on a
`C²` manifold), pulling `φ` back along `C.contractIcc` and applying `TauCeti.homotopyOperator`
satisfies `d (h (H^* φ)) + h (d (H^* φ)) = φ`. -/
theorem mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv_mpullback_contractIcc
    [IsManifold I 2 M] [CompleteSpace F] (C : SmoothGoodCover I (M := M)) (s : Finset C.Index)
    (hs : s.Nonempty) (hW : ((C.inter s : Opens M) : Set M).Nonempty) {k : ℕ}
    {φ : RoughForm I ↥(C.inter s) F (k + 1)} (hφ : IsSmoothForm I 1 φ) :
    mextDeriv (homotopyOperator (mpullback (I.prod (𝓡∂ 1)) I (C.contractIcc s hs hW) φ)) +
        homotopyOperator (mextDeriv (mpullback (I.prod (𝓡∂ 1)) I (C.contractIcc s hs hW) φ)) =
      φ := by
  have hH : ContMDiff (I.prod (𝓡∂ 1)) I ((1 : ℕ∞) + 1) (C.contractIcc s hs hW) :=
    (C.contMDiff_contractIcc s hs hW).of_le (by simp)
  have hψ : IsSmoothForm (I.prod (𝓡∂ 1)) 1
      (mpullback (I.prod (𝓡∂ 1)) I (C.contractIcc s hs hW) φ) :=
    hφ.mpullback hH
  funext x
  have h := mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv hψ x
  rw [C.mpullback_contractIcc_slice_one s hs hW φ, C.mpullback_contractIcc_slice_zero s hs hW φ,
    Pi.zero_apply, sub_zero] at h
  exact h

/-- **Exactness of closed forms on nonempty finite intersections.** Every closed `C¹` `(k + 1)`-form
`φ` with values in a Banach space on a nonempty finite intersection `W` of a smooth good cover (on
a `C²` manifold) is the exterior derivative of `homotopyOperator (H^* φ)`. -/
theorem mextDeriv_homotopyOperator_mpullback_contractIcc
    [IsManifold I 2 M] [CompleteSpace F] (C : SmoothGoodCover I (M := M)) (s : Finset C.Index)
    (hs : s.Nonempty) (hW : ((C.inter s : Opens M) : Set M).Nonempty) {k : ℕ}
    {φ : RoughForm I ↥(C.inter s) F (k + 1)} (hφ : IsSmoothForm I 1 φ)
    (hclosed : mextDeriv φ = 0) :
    mextDeriv (homotopyOperator (mpullback (I.prod (𝓡∂ 1)) I (C.contractIcc s hs hW) φ)) = φ := by
  have hH2 : ContMDiff (I.prod (𝓡∂ 1)) I 2 (C.contractIcc s hs hW) :=
    (C.contMDiff_contractIcc s hs hW).of_le (by simp)
  have hdψ : mextDeriv (mpullback (I.prod (𝓡∂ 1)) I (C.contractIcc s hs hW) φ) = 0 :=
    hφ.mextDeriv_mpullback_eq_zero hclosed hH2
  have h := C.mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv_mpullback_contractIcc
    s hs hW hφ
  rwa [hdψ, homotopyOperator_zero, add_zero] at h

end HomotopyOperator

/-! ### Concrete smooth good covers -/

/-- The empty manifold carries the smooth good cover with empty index type. -/
@[expose]
def empty [IsEmpty M] : SmoothGoodCover I (M := M) where
  Index := PEmpty.{u + 1}
  openSet i := i.elim
  covers x := (IsEmpty.false x).elim
  locallyFinite x := (IsEmpty.false x).elim
  centre _ _ hW := (IsEmpty.false hW.some).elim
  contract _ _ hW := (IsEmpty.false hW.some).elim
  smooth _ _ hW := (IsEmpty.false hW.some).elim
  at_zero _ _ hW := (IsEmpty.false hW.some).elim
  at_one _ _ hW := (IsEmpty.false hW.some).elim
  fixes_centre _ _ hW := (IsEmpty.false hW.some).elim

/-- Any nonempty convex open subset `U` of a real normed space `E`, with a chosen point `x₀ ∈ U`,
is covered by the one-member smooth good cover `{U}` contracted by
`(t, x) ↦ (1 - Real.smoothTransition t) • x₀ + Real.smoothTransition t • x`. -/
@[expose]
def ofConvex {U : Opens E} (hconv : Convex ℝ (U : Set E)) (x₀ : U) :
    SmoothGoodCover 𝓘(ℝ, E) (M := U) where
  Index := PUnit.{v + 1}
  openSet _ := ⊤
  covers _ := ⟨PUnit.unit, trivial⟩
  locallyFinite _ := ⟨univ, univ_mem, Set.toFinite _⟩
  centre _ _ _ := ⟨x₀, by simp⟩
  contract _ _ _ p :=
    ⟨⟨(1 - Real.smoothTransition p.1) • x₀.1 + Real.smoothTransition p.1 • p.2.1.1,
      hconv x₀.2 p.2.1.2 (sub_nonneg.2 (Real.smoothTransition.le_one p.1))
        (Real.smoothTransition.nonneg p.1) (sub_add_cancel 1 _)⟩,
      by simp⟩
  smooth s _ _ := by
    rw [← TauCeti.ContMDiff.subtypeVal_comp_iff, ← TauCeti.ContMDiff.subtypeVal_comp_iff]
    have hρ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × ↥(s.inf fun _ : PUnit ↦ (⊤ : Opens U)) ↦ Real.smoothTransition p.1) :=
      (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).contMDiff.comp contMDiff_fst
    have hx : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun p : ℝ × ↥(s.inf fun _ : PUnit ↦ (⊤ : Opens U)) ↦ p.2.1.1) :=
      contMDiff_subtype_val.comp (contMDiff_subtype_val.comp contMDiff_snd)
    exact ((contMDiff_const.sub hρ).smul contMDiff_const).add (hρ.smul hx)
  at_zero _ _ _ _ := by ext; simp [Real.smoothTransition.zero]
  at_one _ _ _ _ := by ext; simp [Real.smoothTransition.one]
  fixes_centre _ _ _ t := by
    ext
    dsimp only
    rw [← add_smul, sub_add_cancel, one_smul]

/-- Every member of `SmoothGoodCover.ofConvex` is the full open set `⊤`. -/
@[simp]
theorem ofConvex_openSet {U : Opens E} (hconv : Convex ℝ (U : Set E)) (x₀ : U)
    (i : (ofConvex hconv x₀).Index) :
    (ofConvex hconv x₀).openSet i = ⊤ :=
  (rfl)

/-- Any real normed space `E` carries the canonical one-member smooth good cover `{E}` with centre
`0` and contraction `(t, x) ↦ Real.smoothTransition t • x`. -/
@[expose]
def ofNormedSpace : SmoothGoodCover 𝓘(ℝ, E) (M := E) where
  Index := PUnit.{v + 1}
  openSet _ := ⊤
  covers _ := ⟨PUnit.unit, trivial⟩
  locallyFinite _ := ⟨univ, univ_mem, Set.toFinite _⟩
  centre _ _ _ := ⟨0, by simp⟩
  contract _ _ _ p := ⟨Real.smoothTransition p.1 • p.2.1, by simp⟩
  smooth s _ _ := by
    rw [← TauCeti.ContMDiff.subtypeVal_comp_iff]
    have hρ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × ↥(s.inf fun _ : PUnit ↦ (⊤ : Opens E)) ↦ Real.smoothTransition p.1) :=
      (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).contMDiff.comp contMDiff_fst
    have hx : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun p : ℝ × ↥(s.inf fun _ : PUnit ↦ (⊤ : Opens E)) ↦ p.2.1) :=
      contMDiff_subtype_val.comp contMDiff_snd
    exact hρ.smul hx
  at_zero _ _ _ _ := by ext; simp [Real.smoothTransition.zero]
  at_one _ _ _ _ := by ext; simp [Real.smoothTransition.one]
  fixes_centre _ _ _ _ := by ext; simp

/-- Every member of `SmoothGoodCover.ofNormedSpace` is the full open set `⊤`. -/
@[simp]
theorem ofNormedSpace_openSet (i : (ofNormedSpace (E := E)).Index) :
    (ofNormedSpace (E := E)).openSet i = ⊤ :=
  (rfl)

/-! ### Restricting to nonempty open sets -/

/-- Restrict a smooth good cover to its nonempty open sets. The resulting cover has the same
nonempty finite intersections and, when `M` is compact, a finite index type. -/
@[expose]
def restrictNonempty (C : SmoothGoodCover I (M := M)) : SmoothGoodCover I (M := M) :=
  let e := Function.Embedding.subtype fun i : C.Index ↦ (C.openSet i : Set M).Nonempty
  have hmem (s : Finset {i : C.Index // (C.openSet i : Set M).Nonempty}) (x : M) :
      x ∈ s.inf (fun i ↦ C.openSet i.1) ↔ x ∈ (s.map e).inf C.openSet := by
    rw [Finset.inf_map]; rfl
  have hW' (s : Finset {i : C.Index // (C.openSet i : Set M).Nonempty})
      (hW : ((s.inf (fun i ↦ C.openSet i.1) : Opens M) : Set M).Nonempty) :
      (((s.map e).inf C.openSet : Opens M) : Set M).Nonempty :=
    ⟨hW.some, (hmem s _).1 hW.some_mem⟩
  { Index := {i : C.Index // (C.openSet i : Set M).Nonempty}
    openSet i := C.openSet i.1
    covers x := by
      obtain ⟨i, hi⟩ := C.covers x
      exact ⟨⟨i, ⟨x, hi⟩⟩, hi⟩
    locallyFinite := C.locallyFinite.comp_injective Subtype.val_injective
    centre s hs hW :=
      ⟨(C.centre (s.map e) hs.map (hW' s hW)).1,
        (hmem s _).2 (C.centre (s.map e) hs.map (hW' s hW)).2⟩
    contract s hs hW p :=
      let q : ↥((s.map e).inf C.openSet) := ⟨p.2.1, (hmem s _).1 p.2.2⟩
      ⟨(C.contract (s.map e) hs.map (hW' s hW) (p.1, q)).1,
        (hmem s _).2 (C.contract (s.map e) hs.map (hW' s hW) (p.1, q)).2⟩
    smooth s hs hW := by
      rw [← TauCeti.ContMDiff.subtypeVal_comp_iff]
      have hinner : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
          (fun p : ℝ × ↥(s.inf fun i ↦ C.openSet i.1) ↦
            (p.1, (⟨p.2.1, (hmem s _).1 p.2.2⟩ : ↥((s.map e).inf C.openSet)))) := by
        refine contMDiff_fst.prodMk ?_
        rw [← TauCeti.ContMDiff.subtypeVal_comp_iff]
        exact (contMDiff_subtype_val : ContMDiff I I ∞
          (Subtype.val : ↥(s.inf fun i ↦ C.openSet i.1) → M)).comp contMDiff_snd
      exact (contMDiff_subtype_val : ContMDiff I I ∞
        (Subtype.val : ↥((s.map e).inf C.openSet) → M)).comp
        ((C.smooth (s.map e) hs.map (hW' s hW)).comp hinner)
    at_zero s hs hW x := by
      apply Subtype.ext
      dsimp only
      rw [C.at_zero]
    at_one s hs hW x := by
      apply Subtype.ext
      dsimp only
      rw [C.at_one]
    fixes_centre s hs hW t := by
      apply Subtype.ext
      dsimp only
      rw [C.fixes_centre] }

/-- The open sets of `C.restrictNonempty` are the nonempty open sets of `C`. -/
@[simp]
theorem restrictNonempty_openSet (C : SmoothGoodCover I (M := M))
    (i : C.restrictNonempty.Index) :
    C.restrictNonempty.openSet i = C.openSet i.1 :=
  (rfl)

/-- On a compact space, restricting a smooth good cover to its nonempty open sets yields a finite
index type. -/
theorem finite_index_restrictNonempty [CompactSpace M] (C : SmoothGoodCover I (M := M)) :
    Finite C.restrictNonempty.Index := by
  have hfin : {i : C.Index | ((C.openSet i : Set M) ∩ univ).Nonempty}.Finite :=
    C.locallyFinite.finite_nonempty_inter_compact isCompact_univ
  have heq : {i : C.Index | (C.openSet i : Set M).Nonempty} =
      {i : C.Index | ((C.openSet i : Set M) ∩ univ).Nonempty} := by
    ext i
    simp
  rw [← heq] at hfin
  exact hfin.to_subtype

/-! ### Transport along a diffeomorphism -/

section Diffeomorph

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type u} [TopologicalSpace N] [ChartedSpace H' N]

/-- Pull a smooth good cover on `M` back along a smooth diffeomorphism `e : N ≃ₘ^∞⟮J, I⟯ M`. The
index type is unchanged, so finiteness is preserved. -/
@[expose]
def comapDiffeomorph (e : N ≃ₘ^∞⟮J, I⟯ M) (C : SmoothGoodCover I (M := M)) :
    SmoothGoodCover J (M := N) :=
  have hmem (s : Finset C.Index) (x : N) :
      x ∈ s.inf (fun i ↦ Opens.comap ⟨e, e.continuous⟩ (C.openSet i)) ↔
        e x ∈ s.inf C.openSet := by
    have hinf : s.inf (fun i ↦ Opens.comap ⟨e, e.continuous⟩ (C.openSet i)) =
        Opens.comap ⟨e, e.continuous⟩ (s.inf C.openSet) :=
      (map_finset_inf (Opens.comap (⟨e, e.continuous⟩ : C(N, M))) s C.openSet).symm
    rw [hinf]
    rfl
  have hWe (s : Finset C.Index)
      (hW : ((s.inf (fun i ↦ Opens.comap ⟨e, e.continuous⟩ (C.openSet i)) : Opens N) :
        Set N).Nonempty) :
      ((s.inf C.openSet : Opens M) : Set M).Nonempty :=
    ⟨e hW.some, (hmem s hW.some).1 hW.some_mem⟩
  { Index := C.Index
    openSet i := Opens.comap ⟨e, e.continuous⟩ (C.openSet i)
    covers x := by
      obtain ⟨i, hi⟩ := C.covers (e x)
      exact ⟨i, hi⟩
    locallyFinite := C.locallyFinite.preimage_continuous e.continuous
    centre s hs hW :=
      ⟨e.symm (C.centre s hs (hWe s hW)).1,
        (hmem s _).2 (by rw [e.apply_symm_apply]; exact (C.centre s hs (hWe s hW)).2)⟩
    contract s hs hW p :=
      let q : ↥(s.inf C.openSet) := ⟨e p.2.1, (hmem s p.2.1).1 p.2.2⟩
      ⟨e.symm (C.contract s hs (hWe s hW) (p.1, q)).1,
        (hmem s _).2 (by rw [e.apply_symm_apply]; exact (C.contract s hs (hWe s hW) (p.1, q)).2)⟩
    smooth s hs hW := by
      rw [← TauCeti.ContMDiff.subtypeVal_comp_iff]
      have hinner : ContMDiff (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, ℝ).prod I) ∞
          (fun p : ℝ × ↥(s.inf fun i ↦ Opens.comap ⟨e, e.continuous⟩ (C.openSet i)) ↦
            (p.1, (⟨e p.2.1, (hmem s p.2.1).1 p.2.2⟩ : ↥(s.inf C.openSet)))) := by
        refine contMDiff_fst.prodMk ?_
        rw [← TauCeti.ContMDiff.subtypeVal_comp_iff]
        exact e.contMDiff.comp (contMDiff_subtype_val.comp contMDiff_snd)
      exact e.symm.contMDiff.comp
        (contMDiff_subtype_val.comp ((C.smooth s hs (hWe s hW)).comp hinner))
    at_zero s hs hW x := by
      apply Subtype.ext
      dsimp only
      rw [C.at_zero]
    at_one s hs hW x := by
      apply Subtype.ext
      dsimp only
      rw [C.at_one]
      exact e.symm_apply_apply x.1
    fixes_centre s hs hW t := by
      apply Subtype.ext
      dsimp only
      have hq :
          (⟨e (e.symm (C.centre s hs (hWe s hW)).1),
            (hmem s _).1 ((hmem s _).2
              (by rw [e.apply_symm_apply]; exact (C.centre s hs (hWe s hW)).2))⟩ :
            ↥(s.inf C.openSet)) = C.centre s hs (hWe s hW) :=
        Subtype.ext (e.apply_symm_apply _)
      rw [hq, C.fixes_centre] }

/-- The open sets of `C.comapDiffeomorph e` are the preimages of those of `C` under `e`. -/
@[simp]
theorem comapDiffeomorph_openSet (e : N ≃ₘ^∞⟮J, I⟯ M) (C : SmoothGoodCover I (M := M))
    (i : C.Index) :
    (C.comapDiffeomorph e).openSet i = Opens.comap ⟨e, e.continuous⟩ (C.openSet i) :=
  (rfl)

end Diffeomorph

end SmoothGoodCover

end Basic

/-! ### Construction from Riemannian strongly geodesically convex covers -/

section Riemannian

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

open TauCeti.Manifold

/-- Any locally finite open cover of a Riemannian manifold by uniformly normal, strongly
geodesically convex open sets is a smooth good cover, with contractions given by the reparametrized
radial geodesic contraction `TauCeti.Manifold.geodesicContractionOpens`. -/
@[expose]
def SmoothGoodCover.ofStronglyGeodesicallyConvex
    {α : Type u} (V : α → Opens M) (hcov : ∀ x : M, ∃ a, x ∈ V a)
    (hlf : LocallyFinite (fun a ↦ (V a : Set M)))
    (hunif : ∀ a, IsUniformlyNormal I M (V a : Set M))
    (hconv : ∀ a, IsStronglyGeodesicallyConvex I M (V a : Set M)) :
    SmoothGoodCover I (M := M) := by
  have hinf_eq (s : Finset α) : ((s.inf V : Opens M) : Set M) = ⋂ a ∈ s, (V a : Set M) := by
    rw [Opens.coe_finset_inf, Finset.inf_eq_iInf]
    simp [Set.iInf_eq_iInter]
  have hinf_unif (s : Finset α) (hs : s.Nonempty) :
      IsUniformlyNormal I M ((s.inf V : Opens M) : Set M) := by
    rw [hinf_eq s]
    exact IsUniformlyNormal.biInter hs fun a _ ↦ hunif a
  have hinf_conv (s : Finset α) (hs : s.Nonempty) :
      IsStronglyGeodesicallyConvex I M ((s.inf V : Opens M) : Set M) := by
    rw [hinf_eq s]
    exact IsStronglyGeodesicallyConvex.biInter hs fun a _ ↦ hconv a
  let q (s : Finset α) (_hs : s.Nonempty)
      (hW : ((s.inf V : Opens M) : Set M).Nonempty) : ↥(s.inf V) :=
    ⟨hW.some, hW.some_mem⟩
  let rad (s : Finset α) (hs : s.Nonempty)
      (hW : ((s.inf V : Opens M) : Set M).Nonempty) :=
    (hinf_unif s hs).exists_radius (q s hs hW).1 (q s hs hW).2
  exact
    { Index := α
      openSet := V
      covers := hcov
      locallyFinite := hlf
      centre := q
      contract := fun s hs hW ↦
        geodesicContractionOpens (hinf_conv s hs) (q s hs hW)
          (rad s hs hW).choose_spec.2.1 (rad s hs hW).choose_spec.2.2
      smooth := fun s hs hW ↦
        contMDiff_geodesicContractionOpens (hinf_conv s hs) (q s hs hW)
          (rad s hs hW).choose_spec.2.1 (rad s hs hW).choose_spec.2.2
      at_zero := fun s hs hW x ↦
        geodesicContractionOpens_zero (hinf_conv s hs) (q s hs hW)
          (rad s hs hW).choose_spec.2.1 (rad s hs hW).choose_spec.2.2 x
      at_one := fun s hs hW x ↦
        geodesicContractionOpens_one (hinf_conv s hs) (q s hs hW)
          (rad s hs hW).choose_spec.2.1 (rad s hs hW).choose_spec.2.2 x
      fixes_centre := fun s hs hW t ↦
        geodesicContractionOpens_centre (hinf_conv s hs) (q s hs hW)
          (rad s hs hW).choose_spec.2.1 (rad s hs hW).choose_spec.2.2 t }

/-- The open sets of `SmoothGoodCover.ofStronglyGeodesicallyConvex` are the given family `V`. -/
@[simp]
theorem SmoothGoodCover.ofStronglyGeodesicallyConvex_openSet
    {α : Type u} (V : α → Opens M) (hcov : ∀ x : M, ∃ a, x ∈ V a)
    (hlf : LocallyFinite (fun a ↦ (V a : Set M)))
    (hunif : ∀ a, IsUniformlyNormal I M (V a : Set M))
    (hconv : ∀ a, IsStronglyGeodesicallyConvex I M (V a : Set M)) (a : α) :
    (SmoothGoodCover.ofStronglyGeodesicallyConvex (I := I) V hcov hlf hunif hconv).openSet a =
      V a :=
  (rfl)

/-- Around any point `x` inside an open set `W`, there exists a positive radius `ε` such that
`Metric.eball x (ENNReal.ofReal ε)` is uniformly normal, strongly geodesically convex, and
contained in `W`. -/
private theorem exists_eball_subset_isUniformlyNormal_isStronglyGeodesicallyConvex
    {x : M} {W : Set M} (hWo : IsOpen W) (hxW : x ∈ W) :
    ∃ ε > 0, Metric.eball x (ENNReal.ofReal ε) ⊆ W ∧
      IsUniformlyNormal I M (Metric.eball x (ENNReal.ofReal ε)) ∧
      IsStronglyGeodesicallyConvex I M (Metric.eball x (ENNReal.ofReal ε)) := by
  obtain ⟨_, _, δ, hδ, _, hDconv⟩ :=
    exists_pos_forall_isNormalDomain_and_isStronglyGeodesicallyConvex_eball (I := I) (M := M) x
  obtain ⟨R, hR, hRW⟩ := EMetric.isOpen_iff.1 hWo x hxW
  obtain ⟨ε₀, hε₀, hε₀R⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ENNReal.ofReal ε₀ ≤ R := by
    rcases eq_or_ne R ∞ with rfl | hRtop
    · exact ⟨1, one_pos, le_top⟩
    · exact ⟨R.toReal, ENNReal.toReal_pos hR.ne' hRtop, by rw [ENNReal.ofReal_toReal hRtop]⟩
  set ε : ℝ := min δ ε₀
  have hε : 0 < ε := lt_min hδ hε₀
  have hsub : Metric.eball x (ENNReal.ofReal ε) ⊆ W :=
    (Metric.eball_subset_eball
      ((ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans hε₀R)).trans hRW
  have hconv := hDconv x (Metric.mem_eball_self (ENNReal.ofReal_pos.2 hδ)) ε hε (min_le_left _ _)
  exact ⟨ε, hε, hsub, hconv.1, hconv.2⟩

/-- Cover a compact set `A` inside an open shell `O` by finitely many uniformly normal, strongly
geodesically convex open balls contained in `O` and refining `U`. -/
private theorem exists_finset_eball_cover_of_isCompact
    {ι : Type*} (U : ι → Opens M) (hU : ∀ x : M, ∃ i, x ∈ U i)
    {A O : Set M} (hAc : IsCompact A) (hOo : IsOpen O) (hAO : A ⊆ O) :
    ∃ (t : Finset M) (ε : M → ℝ) (idx : M → ι),
      (∀ x ∈ t, 0 < ε x ∧ Metric.eball x (ENNReal.ofReal (ε x)) ⊆ O ∧
        Metric.eball x (ENNReal.ofReal (ε x)) ⊆ (U (idx x) : Set M) ∧
        IsUniformlyNormal I M (Metric.eball x (ENNReal.ofReal (ε x))) ∧
        IsStronglyGeodesicallyConvex I M (Metric.eball x (ENNReal.ofReal (ε x)))) ∧
      A ⊆ ⋃ x ∈ t, Metric.eball x (ENNReal.ofReal (ε x)) := by
  have hpt (x : M) : ∃ ε > 0, ∃ i,
      (x ∈ A → Metric.eball x (ENNReal.ofReal ε) ⊆ O) ∧
      Metric.eball x (ENNReal.ofReal ε) ⊆ (U i : Set M) ∧
      IsUniformlyNormal I M (Metric.eball x (ENNReal.ofReal ε)) ∧
      IsStronglyGeodesicallyConvex I M (Metric.eball x (ENNReal.ofReal ε)) := by
    obtain ⟨i, hi⟩ := hU x
    by_cases hxA : x ∈ A
    · obtain ⟨ε, hε, hsub, hunif, hconv⟩ :=
        exists_eball_subset_isUniformlyNormal_isStronglyGeodesicallyConvex (I := I)
          (hOo.inter (U i).isOpen) ⟨hAO hxA, hi⟩
      exact ⟨ε, hε, i, fun _ ↦ hsub.trans inter_subset_left, hsub.trans inter_subset_right,
        hunif, hconv⟩
    · obtain ⟨ε, hε, hsub, hunif, hconv⟩ :=
        exists_eball_subset_isUniformlyNormal_isStronglyGeodesicallyConvex (I := I)
          (U i).isOpen hi
      exact ⟨ε, hε, i, fun h ↦ (hxA h).elim, hsub, hunif, hconv⟩
  choose ε hε idx hOsub hUsub hunif hconv using hpt
  obtain ⟨t, htA, htfin, htcov⟩ := hAc.elim_finite_subcover_image
    (fun x _ ↦ Metric.isOpen_eball (x := x) (r := ENNReal.ofReal (ε x)))
    (fun x hx ↦ mem_iUnion₂.2 ⟨x, hx, Metric.mem_eball_self (ENNReal.ofReal_pos.2 (hε x))⟩)
  refine ⟨htfin.toFinset, ε, idx, fun x hxt ↦ ?_, ?_⟩
  · have hxt' : x ∈ t := htfin.mem_toFinset.1 hxt
    exact ⟨hε x, hOsub x (htA hxt'), hUsub x, hunif x, hconv x⟩
  · simpa only [Set.Finite.mem_toFinset] using htcov

/-- **Existence of smooth good cover refinements for a given Riemannian metric.** On a σ-compact
finite-dimensional Riemannian manifold with boundaryless model, every open cover admits a locally
finite refinement by a smooth good cover consisting of strongly geodesically convex uniformly
normal balls. -/
theorem exists_smoothGoodCover_refining_of_riemannian [SigmaCompactSpace M]
    {ι : Type*} (U : ι → Opens M) (hU : ∀ x : M, ∃ i, x ∈ U i) :
    ∃ C : SmoothGoodCover I (M := M), ∀ a, ∃ i, C.openSet a ≤ U i := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  let K₀ : CompactExhaustion M := CompactExhaustion.choice M
  let K : CompactExhaustion M := K₀.shiftr.shiftr
  -- Decompose `M` into compact annuli `A n = K (n + 2) \ interior (K (n + 1))` inside open shells
  -- `O n = interior (K (n + 3)) \ K n`; `interior (K m)` meets `O n` only when `n < m`.
  let A : ℕ → Set M := fun n ↦ K (n + 2) \ interior (K (n + 1))
  have hstep (n : ℕ) := exists_finset_eball_cover_of_isCompact (I := I) U hU
    ((K.isCompact (n + 2)).diff isOpen_interior)
    (isOpen_interior.sdiff (K.isCompact n).isClosed)
    (fun x hx ↦ ⟨K.subset_interior_succ (n + 2) hx.1,
      fun hxn ↦ hx.2 (K.subset_interior_succ n hxn)⟩)
  choose t ε idx hball hcovA using hstep
  let V : (Σ n : ℕ, {x : M // x ∈ t n}) → Opens M :=
    fun a ↦ ⟨Metric.eball a.2.1 (ENNReal.ofReal (ε a.1 a.2.1)), Metric.isOpen_eball⟩
  have hcov : ∀ y : M, ∃ a, y ∈ V a := by
    intro y
    set n : ℕ := K₀.find y
    have hn : K.find y = n + 2 := by
      simp only [K, CompactExhaustion.find_shiftr, n]
    have hyA : y ∈ A n := ⟨hn ▸ K.mem_find y, fun hy ↦ by
      have hle : K.find y ≤ n + 1 := K.mem_iff_find_le.1 (interior_subset hy)
      omega⟩
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (hcovA n hyA)
    exact ⟨⟨n, ⟨x, hxt⟩⟩, hyx⟩
  have hlf : LocallyFinite (fun a ↦ (V a : Set M)) := by
    intro y
    set m : ℕ := K.find y + 1
    refine ⟨interior (K m), isOpen_interior.mem_nhds (K.subset_interior_succ _ (K.mem_find y)), ?_⟩
    have hsub : {a : Σ n : ℕ, {x : M // x ∈ t n} | ((V a : Set M) ∩ interior (K m)).Nonempty} ⊆
        Set.range (fun p : Σ n : Fin m, {x : M // x ∈ t n.1} ↦ (⟨p.1.1, p.2⟩ :
          Σ n : ℕ, {x : M // x ∈ t n})) := by
      rintro ⟨n, x⟩ ⟨z, hzV, hzm⟩
      have hlt : n < m := by
        by_contra hge
        exact ((hball n x.1 x.2).2.1 hzV).2 (K.subset (not_lt.1 hge) (interior_subset hzm))
      exact ⟨⟨⟨n, hlt⟩, x⟩, rfl⟩
    exact (Set.finite_range _).subset hsub
  refine ⟨SmoothGoodCover.ofStronglyGeodesicallyConvex V hcov hlf
    (fun a ↦ (hball a.1 a.2.1 a.2.2).2.2.2.1) (fun a ↦ (hball a.1 a.2.1 a.2.2).2.2.2.2),
    fun a ↦ ⟨idx a.1 a.2.1, (hball a.1 a.2.1 a.2.2).2.2.1⟩⟩

/-- **Existence of finite smooth good cover refinements for a given Riemannian metric.** On a
compact Riemannian manifold with boundaryless model, every open cover admits a finite refinement by
a smooth good cover consisting of strongly geodesically convex uniformly normal balls. -/
theorem exists_finite_smoothGoodCover_refining_of_riemannian [CompactSpace M]
    {ι : Type*} (U : ι → Opens M) (hU : ∀ x : M, ∃ i, x ∈ U i) :
    ∃ C : SmoothGoodCover I (M := M), Finite C.Index ∧ ∀ a, ∃ i, C.openSet a ≤ U i := by
  obtain ⟨C, hC⟩ := exists_smoothGoodCover_refining_of_riemannian (I := I) U hU
  exact ⟨C.restrictNonempty, C.finite_index_restrictNonempty, fun a ↦ hC a.1⟩

end Riemannian

/-! ### Existence of smooth good covers on smooth manifolds -/

section Existence

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

/-- **Existence of smooth good cover refinements on σ-compact manifolds.** Every open cover of a
finite-dimensional Hausdorff σ-compact boundaryless smooth manifold admits a locally finite
refinement by a smooth good cover. -/
theorem exists_smoothGoodCover_refining_of_sigmaCompact [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {ι : Type*} (U : ι → Opens M) (hU : ∀ x : M, ∃ i, x ∈ U i) :
    ∃ C : SmoothGoodCover I (M := M), ∀ a, ∃ i, C.openSet a ≤ U i := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := I) (n := (⊤ : ℕ∞)) (F := E)
    (E := fun x : M ↦ TangentSpace I x)
  have : SigmaCompactSpace (WithMetric g) :=
    (WithMetric.homeomorph g).isClosedEmbedding.sigmaCompactSpace
  let : EMetricSpace (WithMetric g) := .ofRiemannianMetric I (WithMetric g)
  let e : WithMetric g ≃ₘ^∞⟮I, I⟯ M := WithMetric.diffeomorph g ∞
  obtain ⟨C, hCref⟩ := exists_smoothGoodCover_refining_of_riemannian (I := I)
    (M := WithMetric g) (fun i ↦ Opens.comap ⟨e, e.continuous⟩ (U i))
    (fun x ↦ by obtain ⟨i, hi⟩ := hU (e x); exact ⟨i, hi⟩)
  refine ⟨C.comapDiffeomorph e.symm, fun a ↦ ?_⟩
  obtain ⟨i, hi⟩ := hCref a
  refine ⟨i, fun x hx ↦ ?_⟩
  have hx' : e (e.symm x) ∈ U i := hi hx
  rwa [e.apply_symm_apply] at hx'

/-- **Existence of smooth good cover refinements.** Every open cover of a finite-dimensional
Hausdorff second-countable boundaryless smooth manifold admits a locally finite refinement by a
smooth good cover. -/
theorem exists_smoothGoodCover_refining [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M]
    [SecondCountableTopology M] [I.Boundaryless]
    {ι : Type*} (U : ι → Opens M) (hU : ∀ x : M, ∃ i, x ∈ U i) :
    ∃ C : SmoothGoodCover I (M := M), ∀ a, ∃ i, C.openSet a ≤ U i := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  exact exists_smoothGoodCover_refining_of_sigmaCompact (I := I) U hU

/-- **Existence of finite smooth good cover refinements on compact manifolds.** Every open cover of
a compact finite-dimensional Hausdorff boundaryless smooth manifold admits a finite refinement by a
smooth good cover. -/
theorem exists_finite_smoothGoodCover_refining [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    [T2Space M] [CompactSpace M] [I.Boundaryless]
    {ι : Type*} (U : ι → Opens M) (hU : ∀ x : M, ∃ i, x ∈ U i) :
    ∃ C : SmoothGoodCover I (M := M), Finite C.Index ∧ ∀ a, ∃ i, C.openSet a ≤ U i := by
  obtain ⟨C, hC⟩ := exists_smoothGoodCover_refining_of_sigmaCompact (I := I) U hU
  exact ⟨C.restrictNonempty, C.finite_index_restrictNonempty, fun a ↦ hC a.1⟩

end Existence

end TauCeti

end
