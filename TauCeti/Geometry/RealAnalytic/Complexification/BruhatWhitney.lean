/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAnalytic.Complexification.Basic
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.ShrinkingLemma
import TauCeti.Analysis.Analytic.Complexification.Chart
import TauCeti.Analysis.Analytic.Complexification.Neighborhood
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.Complex.TotallyReal.Examples
import TauCeti.Geometry.Manifold.ContMDiff.Analytic
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.Gluing.GlueData
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars
import TauCeti.LinearAlgebra.TotallyReal.Complex
import TauCeti.Topology.Category.TopCat.GlueData

/-!
# Bruhat–Whitney complexification of real-analytic manifolds

Every Hausdorff, `σ`-compact (equivalently, Hausdorff and second-countable) real-analytic manifold
`M` without boundary of real dimension `n` embeds as a closed, maximal totally real `C^ω`
submanifold into a Hausdorff, second-countable complex manifold `X` of complex dimension `n`,
equipped with an anti-holomorphic involution `σ : X → X` whose fixed-point locus is the image of
`M`.

This is Proposition 1 of §1 of Whitney and Bruhat (1959). The construction proceeds in six stages:

1. Refine the preferred `C^ω` charts of `M` to a countable, locally finite open cover `Tᵢ` with
   compact closures inside chart domains, and apply the shrinking lemma twice to obtain open covers
   `Vᵢ` and `Uᵢ` with `closure Vᵢ ⊆ Uᵢ` and `closure Uᵢ ⊆ Tᵢ`.
2. Extend the real-analytic chart transitions on `Tᵢ ∩ Tⱼ` to conjugation-equivariant holomorphic
   open partial homeomorphisms `τᵢⱼ`
   (`OpenPartialHomeomorph.exists_complexification_of_analyticOnNhd`), chosen symmetrically so that
   `τᵢⱼ⁻¹ = τⱼᵢ`.
3. Cut out open, conjugation-invariant, relatively compact neighbourhoods `Ωᵢⱼ` of the real middle
   overlaps inside the domains of `τᵢⱼ`, constrained to project onto `Uᵢ ∩ Uⱼ` under the real-part
   map so that real boundary points of `Ωᵢⱼ` still represent genuine manifold overlaps.
4. Separate the compact real closures `Kᵢ = closure Vᵢ` from the boundary locus of `Ωᵢⱼ` and from
   the locus where the triple cocycle `τⱼₖ ∘ τᵢⱼ = τᵢₖ` fails, using the generalized tube lemma on
   compact difference graphs, and intersect the finitely many resulting buffers over the locally
   finite cover to define complexified chart pieces `V̂ᵢ ⊆ ℂⁿ`.
5. Glue the pieces `V̂ᵢ` via `TopCat.GlueData.mk'`; the pair buffers keep the closure of every
   gluing relation inside the overlap, giving `T2Space X` via
   `TopCat.GlueData.t2Space_iff_isClosed_chartRel`.
6. Descend coordinatewise complex conjugation `star` to an involution `σ : X → X` and assemble the
   closed real-analytic maximal totally real embedding `ι : M → X` from the real loci of the charts.

## Main declarations

* `TauCeti.exists_isRealAnalyticComplexification_of_continuousLinearEquiv`: Bruhat–Whitney existence
  theorem for a Hausdorff, `σ`-compact boundaryless `C^ω` manifold equipped with an explicit model
  coordinate equivalence `E ≃L[ℝ] (Fin n → ℝ)`.
* `TauCeti.exists_isRealAnalyticComplexification_of_sigmaCompact`: Bruhat–Whitney existence theorem
  for Hausdorff, `σ`-compact boundaryless `C^ω` manifolds of real dimension `n`.
* `TauCeti.exists_isRealAnalyticComplexification`: Bruhat–Whitney existence theorem for Hausdorff,
  second-countable boundaryless `C^ω` manifolds of real dimension `n`.

## References

* H. Whitney and F. Bruhat, *Quelques propriétés fondamentales des ensembles analytiques-réels*,
  Commentarii Mathematici Helvetici 33 (1959), 132–206, §1, Proposition 1.
-/

open CategoryTheory CategoryTheory.Limits Filter Function IsManifold Manifold Module Set
  TopologicalSpace Topology
open scoped ContDiff Manifold TauCeti.ComplexManifold

namespace TauCeti

/-! ### Internal Bruhat–Whitney gluing construction -/

noncomputable section BruhatWhitney

abbrev realToComplex {n : ℕ} (x : Fin n → ℝ) : Fin n → ℂ :=
  fun k ↦ (x k : ℂ)

abbrev complexToReal {n : ℕ} (z : Fin n → ℂ) : Fin n → ℝ :=
  fun k ↦ (z k).re

theorem continuous_realToComplex {n : ℕ} : Continuous (@realToComplex n) := by
  fun_prop

theorem continuous_complexToReal {n : ℕ} : Continuous (@complexToReal n) := by
  fun_prop

theorem realToComplex_injective {n : ℕ} : Function.Injective (@realToComplex n) :=
  fun _ _ h ↦ funext fun k ↦ Complex.ofReal_injective (congrFun h k)

@[simp]
theorem complexToReal_realToComplex {n : ℕ} (x : Fin n → ℝ) :
    complexToReal (realToComplex x) = x := by
  ext k; simp [realToComplex, complexToReal]

@[simp]
theorem star_realToComplex {n : ℕ} (x : Fin n → ℝ) :
    star (realToComplex x) = realToComplex x := by
  ext k; simp [realToComplex]

@[simp]
theorem complexToReal_star {n : ℕ} (z : Fin n → ℂ) :
    complexToReal (star z) = complexToReal z := by
  ext k; simp [complexToReal]

theorem star_eq_self_iff_exists_realToComplex {n : ℕ} {z : Fin n → ℂ} :
    star z = z ↔ ∃ x : Fin n → ℝ, realToComplex x = z := by
  refine ⟨fun hz ↦ ⟨complexToReal z, funext fun k ↦ ?_⟩, ?_⟩
  · exact Complex.conj_eq_iff_re.mp (congrFun hz k)
  · rintro ⟨x, rfl⟩
    exact star_realToComplex x

/-- Given a compact subset `K` of an open set `O ⊆ Fin n → ℂ`, produce an open conjugation-invariant
set `B` with `K ∩ star ⁻¹' K ⊆ B`, `closure B ⊆ O ∩ star ⁻¹' O`, and `IsCompact (closure B)`. -/
theorem exists_isOpen_star_closure_compact {n : ℕ} {K O : Set (Fin n → ℂ)}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ B : Set (Fin n → ℂ), IsOpen B ∧ (K ∩ star ⁻¹' K ⊆ B) ∧
      closure B ⊆ O ∩ star ⁻¹' O ∧ IsCompact (closure B) ∧ ∀ z, star z ∈ B ↔ z ∈ B := by
  obtain ⟨B₀, hB₀_open, hKB₀, hB₀_sub, hB₀_comp⟩ :=
    exists_open_between_and_isCompact_closure hK hO hKO
  let B := B₀ ∩ star ⁻¹' B₀
  have hB_open : IsOpen B := hB₀_open.inter (hB₀_open.preimage continuous_star)
  have hcl_sub : closure B ⊆ closure B₀ ∩ star ⁻¹' closure B₀ := fun z hz ↦
    ⟨closure_mono inter_subset_left hz,
      continuous_star.closure_preimage_subset B₀ (closure_mono inter_subset_right hz)⟩
  refine ⟨B, hB_open, fun z hz ↦ ⟨hKB₀ hz.1, hKB₀ hz.2⟩,
    hcl_sub.trans (inter_subset_inter hB₀_sub (preimage_mono hB₀_sub)),
    hB₀_comp.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left), fun z ↦ ?_⟩
  simp [B, and_comm]

/-- Given conjugation-invariant compact sets `K₁, K₂ ⊆ Fin n → ℂ` and an open neighbourhood `N` of
`K₁ ×ˢ K₂`, produce conjugation-invariant open sets `A ⊇ K₁` and `B ⊇ K₂` with `A ×ˢ B ⊆ N`. -/
theorem exists_star_open_prod_subset {n : ℕ} {K₁ K₂ : Set (Fin n → ℂ)}
    (hK₁ : IsCompact K₁) (hK₁_star : ∀ z ∈ K₁, star z ∈ K₁)
    (hK₂ : IsCompact K₂) (hK₂_star : ∀ z ∈ K₂, star z ∈ K₂)
    {N : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hN : IsOpen N) (hsub : K₁ ×ˢ K₂ ⊆ N) :
    ∃ A B : Set (Fin n → ℂ), IsOpen A ∧ IsOpen B ∧ K₁ ⊆ A ∧ K₂ ⊆ B ∧
      (∀ z, star z ∈ A ↔ z ∈ A) ∧ (∀ z, star z ∈ B ↔ z ∈ B) ∧ A ×ˢ B ⊆ N := by
  obtain ⟨A₀, B₀, hA₀, hB₀, hKA₀, hKB₀, hprod⟩ := generalized_tube_lemma hK₁ hK₂ hN hsub
  refine ⟨A₀ ∩ star ⁻¹' A₀, B₀ ∩ star ⁻¹' B₀,
    hA₀.inter (hA₀.preimage continuous_star), hB₀.inter (hB₀.preimage continuous_star),
    fun z hz ↦ ⟨hKA₀ hz, hKA₀ (hK₁_star z hz)⟩,
    fun z hz ↦ ⟨hKB₀ hz, hKB₀ (hK₂_star z hz)⟩,
    fun z ↦ by simp [and_comm], fun z ↦ by simp [and_comm],
    fun p hp ↦ hprod ⟨hp.1.1, hp.2.1⟩⟩

/-! #### Step 1: Countable 3-fold shrunk chart cover -/

/-- A countable, linearly ordered, locally finite 3-fold shrunk `C^ω` chart cover `Vᵢ ⋐ Uᵢ ⋐ Tᵢ`
of `M` indexed in `Type 0`. -/
structure ShrunkChartCover
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : ℕ} (e₀ : E ≃L[ℝ] (Fin n → ℝ)) where
  J : Type
  countable : Countable J
  linearOrder : LinearOrder J
  c : J → M
  φ : J → OpenPartialHomeomorph M (Fin n → ℝ)
  T : J → Set M
  U : J → Set M
  V : J → Set M
  φ_eq : ∀ i, φ i = (chartAt H (c i)).extendTrans I e₀.toHomeomorph
  isOpen_T : ∀ i, IsOpen (T i)
  isOpen_U : ∀ i, IsOpen (U i)
  isOpen_V : ∀ i, IsOpen (V i)
  isCompact_closure_T : ∀ i, IsCompact (closure (T i))
  closure_T_subset : ∀ i, closure (T i) ⊆ (φ i).source
  closure_U_subset : ∀ i, closure (U i) ⊆ T i
  closure_V_subset : ∀ i, closure (V i) ⊆ U i
  iUnion_V : ⋃ i, V i = Set.univ
  locallyFinite_T : LocallyFinite T

attribute [instance] ShrunkChartCover.countable ShrunkChartCover.linearOrder

theorem nhds_hasBasis_open_compact_closure_chart
    {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [LocallyCompactSpace M] (x : M) :
    (𝓝 x).HasBasis
      (fun O : Set M ↦ x ∈ O ∧ IsOpen O ∧ IsCompact (closure O) ∧
        closure O ⊆ (chartAt H x).source) id := by
  refine ⟨fun S ↦ ⟨fun hS ↦ ?_, fun ⟨O, hO, hOS⟩ ↦ mem_of_superset (hO.2.1.mem_nhds hO.1) hOS⟩⟩
  obtain ⟨W, hWS, hW_open, hxW⟩ := mem_nhds_iff.1
    (Filter.inter_mem hS ((chartAt H x).open_source.mem_nhds (mem_chart_source H x)))
  obtain ⟨O, hO_open, hxO, hO_cl, hO_comp⟩ :=
    exists_open_between_and_isCompact_closure isCompact_singleton hW_open
      (singleton_subset_iff.2 hxW)
  exact ⟨O, ⟨hxO rfl, hO_open, hO_comp, hO_cl.trans (hWS.trans inter_subset_right)⟩,
    subset_closure.trans (hO_cl.trans (hWS.trans inter_subset_left))⟩

theorem exists_shrunkChartCover
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [SigmaCompactSpace M]
    {n : ℕ} (e₀ : E ≃L[ℝ] (Fin n → ℝ)) :
    Nonempty (ShrunkChartCover (I := I) (M := M) e₀) := by
  have : FiniteDimensional ℝ E := e₀.symm.toLinearEquiv.finiteDimensional
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : MetrizableSpace M := Manifold.metrizableSpace I M
  obtain ⟨α, c₀, T₀, hT₀, hT₀_cov, hT₀_lf⟩ :=
    refinement_of_locallyCompact_sigmaCompact_of_nhds_basis
      (nhds_hasBasis_open_compact_closure_chart (H := H) (M := M))
  obtain ⟨U₀, hU₀_cov, hU₀_open, hU₀_cl⟩ :=
    exists_iUnion_eq_closure_subset (fun a ↦ (hT₀ a).2.1) (fun x ↦ hT₀_lf.point_finite x) hT₀_cov
  have hU₀_lf : LocallyFinite U₀ :=
    hT₀_lf.subset fun a ↦ subset_closure.trans (hU₀_cl a)
  obtain ⟨V₀, hV₀_cov, hV₀_open, hV₀_cl⟩ :=
    exists_iUnion_eq_closure_subset hU₀_open (fun x ↦ hU₀_lf.point_finite x) hU₀_cov
  let α' := {a : α // (V₀ a).Nonempty}
  have hV₀_lf : LocallyFinite (fun a : α' ↦ V₀ a.1) :=
    (hU₀_lf.subset fun a ↦ subset_closure.trans (hV₀_cl a)).comp_injective Subtype.val_injective
  let enc : Encodable α' := hV₀_lf.encodable fun a ↦ a.2
  let J : Type := Set.range enc.encode
  let eJ : J ≃ α' := (Equiv.ofInjective enc.encode enc.encode_injective).symm
  let idx : J → α := fun i ↦ (eJ i).1
  have hidx_inj : Function.Injective idx := Subtype.val_injective.comp eJ.injective
  refine ⟨{
    J := J
    countable := inferInstance
    linearOrder := inferInstance
    c := fun i ↦ c₀ (idx i)
    φ := fun i ↦ (chartAt H (c₀ (idx i))).extendTrans I e₀.toHomeomorph
    T := fun i ↦ T₀ (idx i)
    U := fun i ↦ U₀ (idx i)
    V := fun i ↦ V₀ (idx i)
    φ_eq := fun _ ↦ rfl
    isOpen_T := fun i ↦ (hT₀ (idx i)).2.1
    isOpen_U := fun i ↦ hU₀_open (idx i)
    isOpen_V := fun i ↦ hV₀_open (idx i)
    isCompact_closure_T := fun i ↦ (hT₀ (idx i)).2.2.1
    closure_T_subset := fun i ↦ by
      simpa [OpenPartialHomeomorph.extendTrans_source] using (hT₀ (idx i)).2.2.2
    closure_U_subset := fun i ↦ hU₀_cl (idx i)
    closure_V_subset := fun i ↦ hV₀_cl (idx i)
    iUnion_V := eq_univ_iff_forall.2 fun p ↦ by
      obtain ⟨a, hp⟩ := mem_iUnion.1 (hV₀_cov ▸ mem_univ p)
      exact mem_iUnion.2 ⟨eJ.symm ⟨a, ⟨p, hp⟩⟩, by simpa [idx] using hp⟩
    locallyFinite_T := hT₀_lf.comp_injective hidx_inj }⟩

namespace ShrunkChartCover

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ} {e₀ : E ≃L[ℝ] (Fin n → ℝ)} (C : ShrunkChartCover (I := I) (M := M) e₀)

theorem T_subset_source (i : C.J) : C.T i ⊆ (C.φ i).source :=
  subset_closure.trans (C.closure_T_subset i)

theorem U_subset_T (i : C.J) : C.U i ⊆ C.T i :=
  subset_closure.trans (C.closure_U_subset i)

theorem V_subset_U (i : C.J) : C.V i ⊆ C.U i :=
  subset_closure.trans (C.closure_V_subset i)

theorem U_subset_source (i : C.J) : C.U i ⊆ (C.φ i).source :=
  (C.U_subset_T i).trans (C.T_subset_source i)

theorem V_subset_source (i : C.J) : C.V i ⊆ (C.φ i).source :=
  (C.V_subset_U i).trans (C.U_subset_source i)

theorem isOpen_image_φ {i : C.J} {S : Set M} (hS : IsOpen S) (hsub : S ⊆ (C.φ i).source) :
    IsOpen (C.φ i '' S) :=
  (C.φ i).isOpen_image_of_subset_source hS hsub

def realTrans (i j : C.J) : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ) :=
  ((C.φ i).restrOpen (C.T i) (C.isOpen_T i)).symm.trans
    ((C.φ j).restrOpen (C.T j) (C.isOpen_T j))

theorem realTrans_symm (i j : C.J) : (C.realTrans i j).symm = C.realTrans j i :=
  (rfl : (C.realTrans i j).symm = C.realTrans j i)

theorem realTrans_source (i j : C.J) :
    (C.realTrans i j).source = C.φ i '' (C.T i ∩ C.T j) := by
  have ht : ((C.φ i).restrOpen (C.T i) (C.isOpen_T i)).target =
      (C.φ i).target ∩ (C.φ i).symm ⁻¹' C.T i := rfl
  ext x
  simp only [realTrans, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, ht,
    OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.coe_restrOpen_symm,
    mem_inter_iff, mem_preimage, mem_image]
  refine ⟨fun ⟨⟨hx_t, hx_Ti⟩, _, hx_Tj⟩ ↦
    ⟨(C.φ i).symm x, ⟨hx_Ti, hx_Tj⟩, (C.φ i).right_inv hx_t⟩, ?_⟩
  rintro ⟨p, ⟨hp_Ti, hp_Tj⟩, rfl⟩
  have hp_i := C.T_subset_source i hp_Ti
  have hp_j := C.T_subset_source j hp_Tj
  rw [(C.φ i).left_inv hp_i]
  exact ⟨⟨(C.φ i).map_source hp_i, hp_Ti⟩, hp_j, hp_Tj⟩

theorem realTrans_target (i j : C.J) :
    (C.realTrans i j).target = C.φ j '' (C.T i ∩ C.T j) := by
  rw [← OpenPartialHomeomorph.symm_source, C.realTrans_symm, C.realTrans_source, inter_comm]

theorem realTrans_apply {i j : C.J} {p : M} (hp : p ∈ C.T i ∩ C.T j) :
    C.realTrans i j (C.φ i p) = C.φ j p := by
  have hpi := C.T_subset_source i hp.1
  simp [realTrans, (C.φ i).left_inv hpi]

def K (i : C.J) : Set (Fin n → ℂ) :=
  realToComplex '' (C.φ i '' closure (C.V i))

theorem closure_V_subset_source (i : C.J) : closure (C.V i) ⊆ (C.φ i).source :=
  (C.closure_V_subset i).trans (C.U_subset_source i)

theorem isCompact_K (i : C.J) : IsCompact (C.K i) := by
  have hcl_comp : IsCompact (closure (C.V i)) :=
    (C.isCompact_closure_T i).of_isClosed_subset isClosed_closure
      ((C.closure_V_subset i).trans ((C.U_subset_T i).trans subset_closure))
  exact (hcl_comp.image_of_continuousOn
    ((C.φ i).continuousOn.mono (C.closure_V_subset_source i))).image continuous_realToComplex

theorem star_mem_K {i : C.J} {z : Fin n → ℂ} (hz : z ∈ C.K i) : star z ∈ C.K i := by
  rcases hz with ⟨x, hx, rfl⟩
  simpa only [star_realToComplex] using ⟨x, hx, rfl⟩

theorem finite_neighbors (a : C.J) : {b : C.J | (C.U a ∩ C.U b).Nonempty}.Finite := by
  have hlf : LocallyFinite C.U := C.locallyFinite_T.subset fun b ↦ C.U_subset_T b
  refine (hlf.finite_nonempty_inter_compact (C.isCompact_closure_T a)).subset ?_
  rintro b ⟨p, hpa, hpb⟩
  exact ⟨p, hpb, subset_closure (C.U_subset_T a hpa)⟩

def neighbors (a : C.J) : Finset C.J :=
  (C.finite_neighbors a).toFinset

@[simp]
theorem mem_neighbors {a b : C.J} : b ∈ C.neighbors a ↔ (C.U a ∩ C.U b).Nonempty :=
  Set.Finite.mem_toFinset _

def embedIdx (p : M) : C.J :=
  Classical.choose (mem_iUnion.1 (C.iUnion_V ▸ mem_univ p))

theorem mem_V_embedIdx (p : M) : p ∈ C.V (C.embedIdx p) :=
  Classical.choose_spec (mem_iUnion.1 (C.iUnion_V ▸ mem_univ p))

variable [IsManifold I ω M]

def chartPartialDiffeomorph (i : C.J) :
    PartialDiffeomorph I 𝓘(ℝ, Fin n → ℝ) M (Fin n → ℝ) ω where
  toPartialEquiv := (C.φ i).toPartialEquiv
  open_source := (C.φ i).open_source
  open_target := (C.φ i).open_target
  contMDiffOn_toFun := by
    rw [C.φ_eq i]
    exact (chartAt H (C.c i)).contMDiffOn_extendTrans (chart_mem_maximalAtlas _) e₀.contDiff
  contMDiffOn_invFun := by
    change ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ω (C.φ i).symm (C.φ i).target
    rw [C.φ_eq i]
    exact (chartAt H (C.c i)).contMDiffOn_extendTrans_symm (chart_mem_maximalAtlas _)
      e₀.symm.contDiff

/-! #### Step 2: Symmetric complexified transitions `τ i j` -/

theorem analyticOnNhd_realTrans (i j : C.J) :
    AnalyticOnNhd ℝ (C.realTrans i j) (C.realTrans i j).source := by
  have hfull : AnalyticOnNhd ℝ (((C.φ i).symm).trans (C.φ j))
      (((C.φ i).symm).trans (C.φ j)).source := by
    rw [C.φ_eq i, C.φ_eq j]
    exact OpenPartialHomeomorph.analyticOnNhd_extendTrans_symm_trans
      (chart_mem_maximalAtlas _) (chart_mem_maximalAtlas _) e₀.symm.contDiff e₀.contDiff
  have hsub : (C.realTrans i j).source ⊆ (((C.φ i).symm).trans (C.φ j)).source := by
    rw [C.realTrans_source]
    rintro _ ⟨p, ⟨hp_i, hp_j⟩, rfl⟩
    have hpi := C.T_subset_source i hp_i
    refine ⟨(C.φ i).map_source hpi, ?_⟩
    change (C.φ i).symm (C.φ i p) ∈ (C.φ j).source
    rw [(C.φ i).left_inv hpi]
    exact C.T_subset_source j hp_j
  exact (hfull.mono hsub).congr (C.realTrans i j).open_source fun _ _ ↦ rfl

structure RawComplexTrans (i j : C.J) where
  E : OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ)
  analytic_toFun : AnalyticOnNhd ℂ E E.source
  analytic_symm : AnalyticOnNhd ℂ E.symm E.target
  real_mem_source : ∀ x : Fin n → ℝ, realToComplex x ∈ E.source ↔ x ∈ (C.realTrans i j).source
  real_mem_target : ∀ y : Fin n → ℝ, realToComplex y ∈ E.target ↔ y ∈ (C.realTrans i j).target
  star_mem_source : ∀ z, star z ∈ E.source ↔ z ∈ E.source
  star_mem_target : ∀ w, star w ∈ E.target ↔ w ∈ E.target
  apply_real : ∀ x ∈ (C.realTrans i j).source,
    E (realToComplex x) = realToComplex (C.realTrans i j x)
  symm_apply_real : ∀ y ∈ (C.realTrans i j).target,
    E.symm (realToComplex y) = realToComplex ((C.realTrans i j).symm y)
  apply_star : ∀ z, E (star z) = star (E z)
  symm_apply_star : ∀ w, E.symm (star w) = star (E.symm w)

def rawComplexTrans (i j : C.J) : C.RawComplexTrans i j :=
  have hex := (C.realTrans i j).exists_complexification_of_analyticOnNhd
    (C.analyticOnNhd_realTrans i j) (C.analyticOnNhd_realTrans j i)
  Classical.choice <| hex.elim fun E h ↦
    ⟨⟨E, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
      h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩⟩

def τ (i j : C.J) : OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ) :=
  if i < j then (C.rawComplexTrans i j).E
  else if j < i then (C.rawComplexTrans j i).E.symm
  else OpenPartialHomeomorph.refl (Fin n → ℂ)

@[simp]
theorem τ_self (i : C.J) : C.τ i i = OpenPartialHomeomorph.refl (Fin n → ℂ) := by
  simp [τ]

theorem τ_symm (i j : C.J) : (C.τ i j).symm = C.τ j i := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [τ, hij, asymm hij]
  · simp [τ]
  · simp [τ, hji, asymm hji]

theorem analyticOnNhd_τ (i j : C.J) : AnalyticOnNhd ℂ (C.τ i j) (C.τ i j).source := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · simpa [τ, hij] using (C.rawComplexTrans i j).analytic_toFun
  · rw [C.τ_self]; exact fun _ _ ↦ analyticAt_id
  · simpa [τ, hji, not_lt_of_gt hji] using (C.rawComplexTrans j i).analytic_symm

theorem realToComplex_mem_τ_source {i j : C.J} {x : Fin n → ℝ}
    (hx : x ∈ C.φ i '' (C.T i ∩ C.T j)) : realToComplex x ∈ (C.τ i j).source := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [← C.realTrans_source] at hx
    simpa [τ, hij] using ((C.rawComplexTrans i j).real_mem_source x).2 hx
  · simp [τ]
  · rw [inter_comm, ← C.realTrans_target j i] at hx
    simpa [τ, hji, not_lt_of_gt hji] using ((C.rawComplexTrans j i).real_mem_target x).2 hx

theorem star_mem_τ_source {i j : C.J} {z : Fin n → ℂ} :
    star z ∈ (C.τ i j).source ↔ z ∈ (C.τ i j).source := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · simpa [τ, hij] using (C.rawComplexTrans i j).star_mem_source z
  · simp [τ]
  · simpa [τ, hji, not_lt_of_gt hji] using (C.rawComplexTrans j i).star_mem_target z

theorem τ_star (i j : C.J) (z : Fin n → ℂ) : C.τ i j (star z) = star (C.τ i j z) := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · simpa [τ, hij] using (C.rawComplexTrans i j).apply_star z
  · simp [τ]
  · simpa [τ, hji, not_lt_of_gt hji] using (C.rawComplexTrans j i).symm_apply_star z

theorem τ_realToComplex {i j : C.J} {p : M} (hp : p ∈ C.T i ∩ C.T j) :
    C.τ i j (realToComplex (C.φ i p)) = realToComplex (C.φ j p) := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hx : C.φ i p ∈ (C.realTrans i j).source := by
      rw [C.realTrans_source]; exact mem_image_of_mem _ hp
    simpa [τ, hij, C.realTrans_apply hp] using (C.rawComplexTrans i j).apply_real (C.φ i p) hx
  · simp [τ]
  · have hy : C.φ i p ∈ (C.realTrans j i).target := by
      rw [C.realTrans_target, inter_comm]; exact mem_image_of_mem _ hp
    simpa [τ, hji, not_lt_of_gt hji, C.realTrans_symm, C.realTrans_apply hp] using
      (C.rawComplexTrans j i).symm_apply_real (C.φ i p) hy

/-! #### Step 3: Relatively compact middle overlaps `Ω i j` -/

structure RawMidOverlap (i j : C.J) where
  G : Set (Fin n → ℂ)
  isOpen : IsOpen G
  isCompact_closure : IsCompact (closure G)
  closure_subset_source : closure G ⊆ (C.τ i j).source
  subset_preimage_U : G ⊆ complexToReal ⁻¹' (C.φ i '' (C.U i ∩ C.U j))
  star_mem : ∀ z, star z ∈ G ↔ z ∈ G
  image_U_subset : realToComplex '' (C.φ i '' (C.U i ∩ C.U j)) ⊆ G

theorem nonempty_rawMidOverlap (i j : C.J) :
    Nonempty (C.RawMidOverlap i j) := by
  let KU : Set (Fin n → ℂ) := realToComplex '' (C.φ i '' closure (C.U i ∩ C.U j))
  have hcl_sub : closure (C.U i ∩ C.U j) ⊆ closure (C.T i) :=
    (closure_mono inter_subset_left).trans (closure_mono (C.U_subset_T i))
  have hcl_comp : IsCompact (closure (C.U i ∩ C.U j)) :=
    (C.isCompact_closure_T i).of_isClosed_subset isClosed_closure hcl_sub
  have hKU_comp : IsCompact KU :=
    (hcl_comp.image_of_continuousOn
      ((C.φ i).continuousOn.mono (hcl_sub.trans (C.closure_T_subset i)))).image
      continuous_realToComplex
  have hKU_src : KU ⊆ (C.τ i j).source := by
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    refine C.realToComplex_mem_τ_source ⟨p, ⟨?_, ?_⟩, rfl⟩
    · exact C.closure_U_subset i (closure_mono inter_subset_left hp)
    · exact C.closure_U_subset j (closure_mono inter_subset_right hp)
  obtain ⟨B, hB_open, hKB, hBcl, hBcomp, hBstar⟩ :=
    exists_isOpen_star_closure_compact hKU_comp (C.τ i j).open_source hKU_src
  let Uimg := C.φ i '' (C.U i ∩ C.U j)
  have hUimg_open : IsOpen Uimg :=
    C.isOpen_image_φ ((C.isOpen_U i).inter (C.isOpen_U j))
      (inter_subset_left.trans (C.U_subset_source i))
  let G := B ∩ complexToReal ⁻¹' Uimg
  refine ⟨⟨G, hB_open.inter (hUimg_open.preimage continuous_complexToReal),
    hBcomp.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left),
    (closure_mono inter_subset_left).trans (hBcl.trans inter_subset_left),
    inter_subset_right, fun z ↦ by simp [G, hBstar], ?_⟩⟩
  rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  have hmemKU : realToComplex (C.φ i p) ∈ KU := ⟨C.φ i p, ⟨p, subset_closure hp, rfl⟩, rfl⟩
  refine ⟨hKB ⟨hmemKU, ?_⟩, by simpa [Uimg] using mem_image_of_mem (C.φ i) hp⟩
  simpa only [mem_preimage, star_realToComplex] using hmemKU

def midOverlap (i j : C.J) : C.RawMidOverlap i j :=
  Classical.choice (C.nonempty_rawMidOverlap i j)

def Ω (i j : C.J) : Set (Fin n → ℂ) :=
  (C.midOverlap i j).G ∩ C.τ i j ⁻¹' (C.midOverlap j i).G

theorem Ω_subset_τ_source (i j : C.J) : C.Ω i j ⊆ (C.τ i j).source :=
  inter_subset_left.trans (subset_closure.trans (C.midOverlap i j).closure_subset_source)

theorem isOpen_Ω (i j : C.J) : IsOpen (C.Ω i j) := by
  have hsub : (C.midOverlap i j).G ⊆ (C.τ i j).source :=
    subset_closure.trans (C.midOverlap i j).closure_subset_source
  exact ((C.τ i j).continuousOn.mono hsub).isOpen_inter_preimage
    (C.midOverlap i j).isOpen (C.midOverlap j i).isOpen

theorem isCompact_closure_Ω (i j : C.J) : IsCompact (closure (C.Ω i j)) :=
  (C.midOverlap i j).isCompact_closure.of_isClosed_subset isClosed_closure
    (closure_mono inter_subset_left)

theorem closure_Ω_subset_τ_source (i j : C.J) :
    closure (C.Ω i j) ⊆ (C.τ i j).source :=
  (closure_mono inter_subset_left).trans (C.midOverlap i j).closure_subset_source

theorem Ω_subset_preimage_U (i j : C.J) :
    C.Ω i j ⊆ complexToReal ⁻¹' (C.φ i '' (C.U i ∩ C.U j)) :=
  inter_subset_left.trans (C.midOverlap i j).subset_preimage_U

theorem star_mem_Ω {i j : C.J} {z : Fin n → ℂ} :
    star z ∈ C.Ω i j ↔ z ∈ C.Ω i j := by
  simp only [Ω, mem_inter_iff, mem_preimage, C.τ_star,
    (C.midOverlap i j).star_mem, (C.midOverlap j i).star_mem]

theorem mapsTo_τ_Ω (i j : C.J) : MapsTo (C.τ i j) (C.Ω i j) (C.Ω j i) := by
  intro z hz
  refine ⟨hz.2, ?_⟩
  have hsrc : z ∈ (C.τ i j).source := C.Ω_subset_τ_source i j hz
  rw [mem_preimage, ← C.τ_symm i j, (C.τ i j).left_inv hsrc]
  exact hz.1

theorem realToComplex_mem_Ω {i j : C.J} {p : M} (hp : p ∈ C.U i ∩ C.U j) :
    realToComplex (C.φ i p) ∈ C.Ω i j := by
  refine ⟨(C.midOverlap i j).image_U_subset ⟨_, mem_image_of_mem _ hp, rfl⟩, ?_⟩
  rw [mem_preimage, C.τ_realToComplex ⟨C.U_subset_T i hp.1, C.U_subset_T j hp.2⟩]
  exact (C.midOverlap j i).image_U_subset ⟨_, mem_image_of_mem _ ⟨hp.2, hp.1⟩, rfl⟩

/-- **Real-locus boundary uniqueness.** Any real point `p ∈ Uᵢ` whose complex coordinate lies in
`closure (Ωᵢⱼ)` and is sent by `τᵢⱼ` to the coordinate of `q ∈ Tⱼ` must satisfy `p = q`. -/
theorem eq_of_mem_closure_Ω {i j : C.J} {p q : M}
    (hp : p ∈ C.U i) (hq : q ∈ C.T j)
    (hcl : realToComplex (C.φ i p) ∈ closure (C.Ω i j))
    (hτ : C.τ i j (realToComplex (C.φ i p)) = realToComplex (C.φ j q)) : p = q := by
  have hre : C.φ i p ∈ closure (C.φ i '' (C.U i ∩ C.U j)) := by
    have h1 := continuous_complexToReal.closure_preimage_subset (C.φ i '' (C.U i ∩ C.U j))
      (closure_mono (C.Ω_subset_preimage_U i j) hcl)
    simpa only [mem_preimage, complexToReal_realToComplex] using h1
  have hpi_src : p ∈ (C.φ i).source := C.U_subset_source i hp
  have hp_cl : p ∈ closure (C.U i ∩ C.U j) := by
    rw [mem_closure_iff]
    intro O hO hpO
    have hW_open : IsOpen ((C.φ i).target ∩ (C.φ i).symm ⁻¹' O) :=
      (C.φ i).continuousOn_symm.isOpen_inter_preimage (C.φ i).open_target hO
    have hW_mem : C.φ i p ∈ (C.φ i).target ∩ (C.φ i).symm ⁻¹' O :=
      ⟨(C.φ i).map_source hpi_src, by rw [mem_preimage, (C.φ i).left_inv hpi_src]; exact hpO⟩
    obtain ⟨_, ⟨h_in_W, r, hr_U, rfl⟩⟩ := mem_closure_iff.1 hre _ hW_open hW_mem
    have hr_O : r ∈ O := by
      have := h_in_W.2
      rwa [mem_preimage, (C.φ i).left_inv (C.U_subset_source i hr_U.1)] at this
    exact ⟨r, hr_O, hr_U⟩
  have hp_Tj : p ∈ C.T j := C.closure_U_subset j (closure_mono inter_subset_right hp_cl)
  have hφ_eq : C.φ j p = C.φ j q :=
    realToComplex_injective ((C.τ_realToComplex ⟨C.U_subset_T i hp, hp_Tj⟩).symm.trans hτ)
  exact (C.φ j).injOn (C.T_subset_source j hp_Tj) (C.T_subset_source j hq) hφ_eq

/-! #### Step 4: Pair buffers, triple-cocycle buffers, and complex pieces `VHat` -/

structure PairBuffer (i j : C.J) where
  W : Set (Fin n → ℂ)
  A : Set (Fin n → ℂ)
  B : Set (Fin n → ℂ)
  isOpen_A : IsOpen A
  isOpen_B : IsOpen B
  closure_W_subset : closure W ⊆ C.Ω i j
  K_subset_A : C.K i ⊆ A
  K_subset_B : C.K j ⊆ B
  star_mem_A : ∀ z, star z ∈ A ↔ z ∈ A
  star_mem_B : ∀ z, star z ∈ B ↔ z ∈ B
  mem_W_of_closure : ∀ z ∈ closure (C.Ω i j), z ∈ A → C.τ i j z ∈ B → z ∈ W

theorem nonempty_pairBuffer (i j : C.J) :
    Nonempty (C.PairBuffer i j) := by
  let KV : Set (Fin n → ℂ) := realToComplex '' (C.φ i '' (closure (C.V i) ∩ closure (C.V j)))
  have hKV_comp : IsCompact KV := by
    have hcl : IsCompact (closure (C.V i) ∩ closure (C.V j)) :=
      ((C.isCompact_closure_T i).of_isClosed_subset isClosed_closure
        ((C.closure_V_subset i).trans ((C.U_subset_T i).trans subset_closure))).inter_right
        isClosed_closure
    exact (hcl.image_of_continuousOn
      ((C.φ i).continuousOn.mono (inter_subset_left.trans (C.closure_V_subset_source i)))).image
      continuous_realToComplex
  have hKV_Ω : KV ⊆ C.Ω i j := by
    rintro _ ⟨_, ⟨p, ⟨hpi, hpj⟩, rfl⟩, rfl⟩
    exact C.realToComplex_mem_Ω ⟨C.closure_V_subset i hpi, C.closure_V_subset j hpj⟩
  obtain ⟨W, hW_open, hKV_W, hW_cl, _, _⟩ :=
    exists_isOpen_star_closure_compact hKV_comp (C.isOpen_Ω i j) hKV_Ω
  let S : Set (Fin n → ℂ) := closure (C.Ω i j) \ W
  have hS_comp : IsCompact S := (C.isCompact_closure_Ω i j).diff hW_open
  let Γ : Set ((Fin n → ℂ) × (Fin n → ℂ)) := (fun z ↦ (z, C.τ i j z)) '' S
  have hΓ_comp : IsCompact Γ :=
    hS_comp.image_of_continuousOn (continuousOn_id.prodMk
      ((C.τ i j).continuousOn.mono (sdiff_subset.trans (C.closure_Ω_subset_τ_source i j))))
  have hdisj : C.K i ×ˢ C.K j ⊆ Γᶜ := by
    rintro ⟨_, _⟩ ⟨⟨_, ⟨p, hpi, rfl⟩, rfl⟩, ⟨_, ⟨q, hqj, rfl⟩, rfl⟩⟩ ⟨z, ⟨hz_cl, hz_notW⟩, hzeq⟩
    obtain ⟨rfl, hτeq⟩ := Prod.mk.inj hzeq
    obtain rfl : p = q := C.eq_of_mem_closure_Ω (C.closure_V_subset i hpi)
      (C.U_subset_T j (C.closure_V_subset j hqj)) hz_cl hτeq
    have hmemKV : realToComplex (C.φ i p) ∈ KV := ⟨_, ⟨p, ⟨hpi, hqj⟩, rfl⟩, rfl⟩
    exact hz_notW (hKV_W ⟨hmemKV, by simpa only [mem_preimage, star_realToComplex] using hmemKV⟩)
  obtain ⟨A, B, hA_open, hB_open, hKA, hKB, hA_star, hB_star, hAB⟩ :=
    exists_star_open_prod_subset (C.isCompact_K i) (fun _ ↦ C.star_mem_K)
      (C.isCompact_K j) (fun _ ↦ C.star_mem_K) hΓ_comp.isClosed.isOpen_compl hdisj
  refine ⟨⟨W, A, B, hA_open, hB_open, hW_cl.trans inter_subset_left, hKA, hKB,
    hA_star, hB_star, fun z hz_cl hzA hzB ↦ ?_⟩⟩
  by_contra hzW
  exact hAB ⟨hzA, hzB⟩ ⟨z, ⟨hz_cl, hzW⟩, rfl⟩

def pairBuf (i j : C.J) : C.PairBuffer i j :=
  Classical.choice (C.nonempty_pairBuffer i j)

theorem exists_cocycleOpen (i j k : C.J) :
    ∃ O : Set (Fin n → ℂ),
      O ⊆ (C.Ω i j ∩ C.Ω i k) ∩ C.τ i j ⁻¹' C.Ω j k ∧
      IsOpen O ∧
      (∀ x : Fin n → ℝ, realToComplex x ∈ O ↔ x ∈ C.φ i '' (C.U i ∩ C.U j ∩ C.U k)) ∧
      (∀ z ∈ O, C.τ j k (C.τ i j z) = C.τ i k z) := by
  let Ddom : Set (Fin n → ℂ) := (C.Ω i j ∩ C.Ω i k) ∩ C.τ i j ⁻¹' C.Ω j k
  have hD_open : IsOpen Ddom :=
    ((C.τ i j).continuousOn.mono
      (inter_subset_left.trans (C.Ω_subset_τ_source i j))).isOpen_inter_preimage
      ((C.isOpen_Ω i j).inter (C.isOpen_Ω i k)) (C.isOpen_Ω j k)
  let Rdom : Set (Fin n → ℝ) := C.φ i '' (C.U i ∩ C.U j ∩ C.U k)
  have hR_open : IsOpen Rdom :=
    C.isOpen_image_φ (((C.isOpen_U i).inter (C.isOpen_U j)).inter (C.isOpen_U k))
      ((inter_subset_left.trans inter_subset_left).trans (C.U_subset_source i))
  have hRD : ∀ x ∈ Rdom, realToComplex x ∈ Ddom := by
    rintro _ ⟨p, ⟨⟨hpi, hpj⟩, hpk⟩, rfl⟩
    refine ⟨⟨C.realToComplex_mem_Ω ⟨hpi, hpj⟩, C.realToComplex_mem_Ω ⟨hpi, hpk⟩⟩, ?_⟩
    rw [mem_preimage, C.τ_realToComplex ⟨C.U_subset_T i hpi, C.U_subset_T j hpj⟩]
    exact C.realToComplex_mem_Ω ⟨hpj, hpk⟩
  have han₁ : AnalyticOnNhd ℂ (C.τ j k ∘ C.τ i j) Ddom := fun z hz ↦
    (C.analyticOnNhd_τ j k _ (C.Ω_subset_τ_source j k hz.2)).comp
      (C.analyticOnNhd_τ i j z (C.Ω_subset_τ_source i j hz.1.1))
  have han₂ : AnalyticOnNhd ℂ (C.τ i k) Ddom :=
    (C.analyticOnNhd_τ i k).mono (inter_subset_left.trans
      (inter_subset_right.trans (C.Ω_subset_τ_source i k)))
  have hReq : ∀ x ∈ Rdom, (C.τ j k ∘ C.τ i j) (realToComplex x) = C.τ i k (realToComplex x) := by
    rintro _ ⟨p, ⟨⟨hpi, hpj⟩, hpk⟩, rfl⟩
    simp only [Function.comp_apply,
      C.τ_realToComplex ⟨C.U_subset_T i hpi, C.U_subset_T j hpj⟩,
      C.τ_realToComplex ⟨C.U_subset_T j hpj, C.U_subset_T k hpk⟩,
      C.τ_realToComplex ⟨C.U_subset_T i hpi, C.U_subset_T k hpk⟩]
  obtain ⟨O, hOD, hO_open, hOR, _, hO_eq⟩ :=
    han₁.exists_eqOn_of_forall_real han₂ hR_open hD_open hRD hReq
  exact ⟨O, hOD, hO_open, hOR, fun z hz ↦ hO_eq hz⟩

structure TripleBuffer (i j k : C.J) where
  O : Set (Fin n → ℂ)
  C₁ : Set (Fin n → ℂ)
  C₂ : Set (Fin n → ℂ)
  C₃ : Set (Fin n → ℂ)
  isOpen_C₁ : IsOpen C₁
  isOpen_C₂ : IsOpen C₂
  isOpen_C₃ : IsOpen C₃
  O_subset : O ⊆ (C.Ω i j ∩ C.Ω i k) ∩ C.τ i j ⁻¹' C.Ω j k
  cocycle_eq : ∀ z ∈ O, C.τ j k (C.τ i j z) = C.τ i k z
  K_subset_C₁ : C.K i ⊆ C₁
  K_subset_C₂ : C.K j ⊆ C₂
  K_subset_C₃ : C.K k ⊆ C₃
  star_mem_C₁ : ∀ z, star z ∈ C₁ ↔ z ∈ C₁
  star_mem_C₂ : ∀ z, star z ∈ C₂ ↔ z ∈ C₂
  star_mem_C₃ : ∀ z, star z ∈ C₃ ↔ z ∈ C₃
  mem_O_of_closure : ∀ z ∈ closure (C.Ω i j) ∩ closure (C.Ω i k),
    z ∈ C₁ → C.τ i j z ∈ C₂ → C.τ i k z ∈ C₃ → z ∈ O

theorem nonempty_tripleBuffer (i j k : C.J) :
    Nonempty (C.TripleBuffer i j k) := by
  obtain ⟨O, hOD, hO_open, hOR, hO_eq⟩ := C.exists_cocycleOpen i j k
  let S : Set (Fin n → ℂ) := (closure (C.Ω i j) ∩ closure (C.Ω i k)) \ O
  have hS_comp : IsCompact S :=
    ((C.isCompact_closure_Ω i j).inter_right isClosed_closure).diff hO_open
  let Γ : Set ((Fin n → ℂ) × ((Fin n → ℂ) × (Fin n → ℂ))) :=
    (fun z ↦ (z, (C.τ i j z, C.τ i k z))) '' S
  have hΓ_comp : IsCompact Γ :=
    hS_comp.image_of_continuousOn (continuousOn_id.prodMk
      (((C.τ i j).continuousOn.mono
          (sdiff_subset.trans (inter_subset_left.trans (C.closure_Ω_subset_τ_source i j)))).prodMk
        ((C.τ i k).continuousOn.mono
          (sdiff_subset.trans (inter_subset_right.trans (C.closure_Ω_subset_τ_source i k))))))
  have hdisj : C.K i ×ˢ (C.K j ×ˢ C.K k) ⊆ Γᶜ := by
    rintro ⟨_, _, _⟩
      ⟨⟨_, ⟨p, hpi, rfl⟩, rfl⟩, ⟨_, ⟨q, hqj, rfl⟩, rfl⟩, ⟨_, ⟨r, hrk, rfl⟩, rfl⟩⟩
      ⟨z, ⟨⟨hz_ij, hz_ik⟩, hz_notO⟩, hzeq⟩
    obtain ⟨rfl, hpair⟩ := Prod.mk.inj hzeq
    obtain ⟨hτ_ij, hτ_ik⟩ := Prod.mk.inj hpair
    obtain rfl : p = q := C.eq_of_mem_closure_Ω (C.closure_V_subset i hpi)
      (C.U_subset_T j (C.closure_V_subset j hqj)) hz_ij hτ_ij
    obtain rfl : p = r := C.eq_of_mem_closure_Ω (C.closure_V_subset i hpi)
      (C.U_subset_T k (C.closure_V_subset k hrk)) hz_ik hτ_ik
    exact hz_notO ((hOR (C.φ i p)).2 ⟨p,
      ⟨⟨C.closure_V_subset i hpi, C.closure_V_subset j hqj⟩, C.closure_V_subset k hrk⟩, rfl⟩)
  obtain ⟨C₁₀, Q, hC₁₀_open, hQ_open, hKC₁₀, hKQ, hC₁Q⟩ :=
    generalized_tube_lemma (C.isCompact_K i) ((C.isCompact_K j).prod (C.isCompact_K k))
      hΓ_comp.isClosed.isOpen_compl hdisj
  obtain ⟨C₂, C₃, hC₂_open, hC₃_open, hKC₂, hKC₃, hC₂_star, hC₃_star, hC₂₃⟩ :=
    exists_star_open_prod_subset (C.isCompact_K j) (fun _ ↦ C.star_mem_K)
      (C.isCompact_K k) (fun _ ↦ C.star_mem_K) hQ_open hKQ
  let C₁ := C₁₀ ∩ star ⁻¹' C₁₀
  refine ⟨⟨O, C₁, C₂, C₃, hC₁₀_open.inter (hC₁₀_open.preimage continuous_star),
    hC₂_open, hC₃_open, hOD, hO_eq,
    fun z hz ↦ ⟨hKC₁₀ hz, hKC₁₀ (C.star_mem_K hz)⟩, hKC₂, hKC₃,
    fun z ↦ by simp [C₁, and_comm], hC₂_star, hC₃_star,
    fun z hz_cl hz₁ hz₂ hz₃ ↦ ?_⟩⟩
  by_contra hzO
  exact hC₁Q ⟨hz₁.1, hC₂₃ ⟨hz₂, hz₃⟩⟩ ⟨z, ⟨hz_cl, hzO⟩, rfl⟩

def tripleBuf (i j k : C.J) : C.TripleBuffer i j k :=
  Classical.choice (C.nonempty_tripleBuffer i j k)

theorem mem_neighbors_of_mem_Ω {i j : C.J} {z : Fin n → ℂ}
    (hz : z ∈ C.Ω i j) : j ∈ C.neighbors i := by
  obtain ⟨p, hp, _⟩ := C.Ω_subset_preimage_U i j hz
  exact C.mem_neighbors.2 ⟨p, hp⟩

def VHat (a : C.J) : Set (Fin n → ℂ) :=
  (C.Ω a a ∩ complexToReal ⁻¹' (C.φ a '' C.V a)) ∩
    (⋂ b ∈ C.neighbors a, (C.pairBuf a b).A ∩ (C.pairBuf b a).B) ∩
    (⋂ j ∈ C.neighbors a, ⋂ k ∈ C.neighbors a, (C.tripleBuf a j k).C₁) ∩
    (⋂ i ∈ C.neighbors a, ⋂ k ∈ C.neighbors i, (C.tripleBuf i a k).C₂) ∩
    (⋂ i ∈ C.neighbors a, ⋂ j ∈ C.neighbors i, (C.tripleBuf i j a).C₃)

theorem isOpen_VHat (a : C.J) : IsOpen (C.VHat a) := by
  have hV_open : IsOpen (C.φ a '' C.V a) :=
    C.isOpen_image_φ (C.isOpen_V a) (C.V_subset_source a)
  have h0 : IsOpen (C.Ω a a ∩ complexToReal ⁻¹' (C.φ a '' C.V a)) :=
    (C.isOpen_Ω a a).inter (hV_open.preimage continuous_complexToReal)
  have h1 : IsOpen (⋂ b ∈ C.neighbors a, (C.pairBuf a b).A ∩ (C.pairBuf b a).B) :=
    isOpen_biInter_finset fun b _ ↦ (C.pairBuf a b).isOpen_A.inter (C.pairBuf b a).isOpen_B
  have h2 : IsOpen (⋂ j ∈ C.neighbors a, ⋂ k ∈ C.neighbors a, (C.tripleBuf a j k).C₁) :=
    isOpen_biInter_finset fun j _ ↦ isOpen_biInter_finset fun k _ ↦ (C.tripleBuf a j k).isOpen_C₁
  have h3 : IsOpen (⋂ i ∈ C.neighbors a, ⋂ k ∈ C.neighbors i, (C.tripleBuf i a k).C₂) :=
    isOpen_biInter_finset fun i _ ↦ isOpen_biInter_finset fun k _ ↦ (C.tripleBuf i a k).isOpen_C₂
  have h4 : IsOpen (⋂ i ∈ C.neighbors a, ⋂ j ∈ C.neighbors i, (C.tripleBuf i j a).C₃) :=
    isOpen_biInter_finset fun i _ ↦ isOpen_biInter_finset fun j _ ↦ (C.tripleBuf i j a).isOpen_C₃
  exact (((h0.inter h1).inter h2).inter h3).inter h4

theorem star_mem_VHat {a : C.J} {z : Fin n → ℂ} :
    star z ∈ C.VHat a ↔ z ∈ C.VHat a := by
  have hA (b) : star z ∈ (C.pairBuf a b).A ↔ z ∈ (C.pairBuf a b).A :=
    (C.pairBuf a b).star_mem_A z
  have hB (b) : star z ∈ (C.pairBuf b a).B ↔ z ∈ (C.pairBuf b a).B :=
    (C.pairBuf b a).star_mem_B z
  have hC₁ (j k) : star z ∈ (C.tripleBuf a j k).C₁ ↔ z ∈ (C.tripleBuf a j k).C₁ :=
    (C.tripleBuf a j k).star_mem_C₁ z
  have hC₂ (i k) : star z ∈ (C.tripleBuf i a k).C₂ ↔ z ∈ (C.tripleBuf i a k).C₂ :=
    (C.tripleBuf i a k).star_mem_C₂ z
  have hC₃ (i j) : star z ∈ (C.tripleBuf i j a).C₃ ↔ z ∈ (C.tripleBuf i j a).C₃ :=
    (C.tripleBuf i j a).star_mem_C₃ z
  simp only [VHat, mem_inter_iff, mem_iInter, mem_preimage, C.star_mem_Ω, complexToReal_star,
    hA, hB, hC₁, hC₂, hC₃]

theorem realToComplex_mem_VHat {a : C.J} {x : Fin n → ℝ} :
    realToComplex x ∈ C.VHat a ↔ x ∈ C.φ a '' C.V a := by
  refine ⟨fun hz ↦ by simpa using hz.1.1.1.1.2, ?_⟩
  rintro ⟨p, hp, rfl⟩
  have hK : realToComplex (C.φ a p) ∈ C.K a := ⟨_, ⟨p, subset_closure hp, rfl⟩, rfl⟩
  refine ⟨⟨⟨⟨⟨C.realToComplex_mem_Ω ⟨C.V_subset_U a hp, C.V_subset_U a hp⟩,
      by simpa using mem_image_of_mem (C.φ a) hp⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact mem_iInter₂.2 fun b _ ↦
      ⟨(C.pairBuf a b).K_subset_A hK, (C.pairBuf b a).K_subset_B hK⟩
  · exact mem_iInter₂.2 fun j _ ↦ mem_iInter₂.2 fun k _ ↦ (C.tripleBuf a j k).K_subset_C₁ hK
  · exact mem_iInter₂.2 fun i _ ↦ mem_iInter₂.2 fun k _ ↦ (C.tripleBuf i a k).K_subset_C₂ hK
  · exact mem_iInter₂.2 fun i _ ↦ mem_iInter₂.2 fun j _ ↦ (C.tripleBuf i j a).K_subset_C₃ hK

/-! #### Step 5: Gluing, Hausdorffness, second countability, and complex manifold structure -/

def VInter (i j : C.J) : Set (Fin n → ℂ) :=
  (C.VHat i ∩ C.Ω i j) ∩ C.τ i j ⁻¹' C.VHat j

theorem isOpen_VInter (i j : C.J) : IsOpen (C.VInter i j) :=
  ((C.τ i j).continuousOn.mono
    (inter_subset_right.trans (C.Ω_subset_τ_source i j))).isOpen_inter_preimage
    ((C.isOpen_VHat i).inter (C.isOpen_Ω i j)) (C.isOpen_VHat j)

theorem VInter_self (i : C.J) : C.VInter i i = C.VHat i := by
  ext z
  simp only [VInter, τ_self, mem_inter_iff, mem_preimage, OpenPartialHomeomorph.refl_apply]
  exact ⟨fun hz ↦ hz.1.1, fun hz ↦ ⟨⟨hz, hz.1.1.1.1.1⟩, hz⟩⟩

theorem mapsTo_τ_VInter {i j : C.J} {z : Fin n → ℂ}
    (hz : z ∈ C.VInter i j) : C.τ i j z ∈ C.VInter j i := by
  refine ⟨⟨hz.2, C.mapsTo_τ_Ω i j hz.1.2⟩, ?_⟩
  have hsrc : z ∈ (C.τ i j).source := C.Ω_subset_τ_source i j hz.1.2
  rw [mem_preimage, ← C.τ_symm i j, (C.τ i j).left_inv hsrc]
  exact hz.1.1

/-- **Pair buffer lemma.** Every overlap point `z ∈ VInter i j` lies inside the shrunk buffer
`(C.pairBuf i j).W`, whose closure is strictly inside `Ω i j`. -/
theorem VInter_subset_W {i j : C.J} {z : Fin n → ℂ}
    (hz : z ∈ C.VInter i j) : z ∈ (C.pairBuf i j).W := by
  have hj_mem : j ∈ C.neighbors i := C.mem_neighbors_of_mem_Ω hz.1.2
  have hi_mem : i ∈ C.neighbors j := C.mem_neighbors_of_mem_Ω (C.mapsTo_τ_Ω i j hz.1.2)
  have hzA : z ∈ (C.pairBuf i j).A := (mem_iInter₂.1 hz.1.1.1.1.1.2 j hj_mem).1
  have hzB : C.τ i j z ∈ (C.pairBuf i j).B := (mem_iInter₂.1 hz.2.1.1.1.2 i hi_mem).2
  exact (C.pairBuf i j).mem_W_of_closure z (subset_closure hz.1.2) hzA hzB

/-- **Triple cocycle lemma.** On `VInter i j ∩ VInter i k`, `τ i j` lands in `Ω j k` and
satisfies `τ j k (τ i j z) = τ i k z`. -/
theorem mem_cocycleO_of_VInter {i j k : C.J} {z : Fin n → ℂ}
    (hij : z ∈ C.VInter i j) (hik : z ∈ C.VInter i k) : z ∈ (C.tripleBuf i j k).O := by
  have hj_i : j ∈ C.neighbors i := C.mem_neighbors_of_mem_Ω hij.1.2
  have hk_i : k ∈ C.neighbors i := C.mem_neighbors_of_mem_Ω hik.1.2
  have hi_j : i ∈ C.neighbors j := C.mem_neighbors_of_mem_Ω (C.mapsTo_τ_Ω i j hij.1.2)
  have hi_k : i ∈ C.neighbors k := C.mem_neighbors_of_mem_Ω (C.mapsTo_τ_Ω i k hik.1.2)
  have hz₁ : z ∈ (C.tripleBuf i j k).C₁ :=
    mem_iInter₂.1 (mem_iInter₂.1 hij.1.1.1.1.2 j hj_i) k hk_i
  have hz₂ : C.τ i j z ∈ (C.tripleBuf i j k).C₂ :=
    mem_iInter₂.1 (mem_iInter₂.1 hij.2.1.2 i hi_j) k hk_i
  have hz₃ : C.τ i k z ∈ (C.tripleBuf i j k).C₃ :=
    mem_iInter₂.1 (mem_iInter₂.1 hik.2.2 i hi_k) j hj_i
  exact (C.tripleBuf i j k).mem_O_of_closure z
    ⟨subset_closure hij.1.2, subset_closure hik.1.2⟩ hz₁ hz₂ hz₃

def pieceOpen (i : C.J) : Opens (Fin n → ℂ) :=
  ⟨C.VHat i, C.isOpen_VHat i⟩

def overlapOpen (i j : C.J) : Opens (C.pieceOpen i) :=
  ⟨Subtype.val ⁻¹' C.VInter i j, (C.isOpen_VInter i j).preimage continuous_subtype_val⟩

def glueCore : TopCat.GlueData.MkCore.{0} where
  J := C.J
  U i := (Opens.toTopCat (TopCat.of (Fin n → ℂ))).obj (C.pieceOpen i)
  V i j := C.overlapOpen i j
  t i j := TopCat.ofHom
    { toFun := fun x ↦
        ⟨⟨C.τ i j x.1.1, (C.mapsTo_τ_VInter x.2).1.1⟩, C.mapsTo_τ_VInter x.2⟩
      continuous_toFun := by
        have hcont : Continuous fun x : C.overlapOpen i j ↦ C.τ i j x.1.1 :=
          (C.τ i j).continuousOn.comp_continuous
            (continuous_subtype_val.comp continuous_subtype_val)
            fun x ↦ C.Ω_subset_τ_source i j x.2.1.2
        exact (hcont.subtype_mk _).subtype_mk _ }
  V_id i := by
    ext x
    change x.1 ∈ C.VInter i i ↔ True
    rw [C.VInter_self]
    exact ⟨fun _ ↦ trivial, fun _ ↦ x.2⟩
  t_id i := by
    ext x
    exact Subtype.ext (Subtype.ext (by change C.τ i i x.1.1 = x.1.1; simp [τ_self]))
  t_inter {i j} k x hx := by
    have hO := C.mem_cocycleO_of_VInter x.2 hx
    have hD := (C.tripleBuf i j k).O_subset hO
    have heq := (C.tripleBuf i j k).cocycle_eq _ hO
    exact ⟨⟨x.2.2, hD.2⟩, by change C.τ j k (C.τ i j x.1.1) ∈ C.VHat k; rw [heq]; exact hx.2⟩
  cocycle i j k x hx := by
    apply Subtype.ext
    exact (C.tripleBuf i j k).cocycle_eq _ (C.mem_cocycleO_of_VInter x.2 hx)

def glueData : TopCat.GlueData.{0} :=
  TopCat.GlueData.mk'.{0} C.glueCore

abbrev X : Type :=
  C.glueData.toGlueData.glued

instance instChartedSpaceU (i : C.glueData.J) :
    ChartedSpace (Fin n → ℂ) (C.glueData.U i) :=
  inferInstanceAs (ChartedSpace (Fin n → ℂ) (C.pieceOpen i))

instance instChartedSpaceV (ij : C.glueData.J × C.glueData.J) :
    ChartedSpace (Fin n → ℂ) (C.glueData.V ij) :=
  inferInstanceAs (ChartedSpace (Fin n → ℂ) (C.overlapOpen ij.1 ij.2))

instance instIsManifoldU (i : C.glueData.J) :
    IsManifold 𝓘(ℂ, Fin n → ℂ) ω (C.glueData.U i) :=
  inferInstanceAs (IsManifold 𝓘(ℂ, Fin n → ℂ) ω (C.pieceOpen i))

instance instChartedSpaceX : ChartedSpace (Fin n → ℂ) C.X :=
  C.glueData.chartedSpace (Fin n → ℂ)

theorem isCompatible_glueData :
    C.glueData.IsCompatible 𝓘(ℂ, Fin n → ℂ) ω := by
  have hU (k : C.J) :
      IsLocalDiffeomorph 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω
        (Subtype.val : C.glueData.U k → Fin n → ℂ) :=
    TauCeti.isLocalDiffeomorph_subtype_val
  have hf (i j : C.glueData.J) :
      IsLocalDiffeomorph 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω (C.glueData.f i j) :=
    TauCeti.isLocalDiffeomorph_subtype_val
  refine .of_isLocalDiffeomorph_t hf fun i j x ↦ ?_
  have hsymm_cd : ContDiffOn ℂ ω (C.τ (i : C.J) (j : C.J)).symm
      (C.τ (i : C.J) (j : C.J)).target := by
    rw [← OpenPartialHomeomorph.symm_source, C.τ_symm (i : C.J) (j : C.J)]
    exact (C.analyticOnNhd_τ j i).contDiffOn (C.τ j i).open_source.uniqueDiffOn
  let Θ : PartialDiffeomorph 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ)
      (Fin n → ℂ) (Fin n → ℂ) ω :=
    TauCeti.PartialDiffeomorph.ofOpenPartialHomeomorph (C.τ i j)
      ((C.analyticOnNhd_τ i j).contDiffOn (C.τ i j).open_source.uniqueDiffOn) hsymm_cd
  have hx_src : x.1.1 ∈ Θ.source := by
    simpa [Θ] using C.Ω_subset_τ_source i j x.2.1.2
  have hτ_ld : IsLocalDiffeomorphAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω
      (C.τ i j) x.1.1 :=
    TauCeti.isLocalDiffeomorphAt_of_eqOn hx_src fun _ _ ↦ by simp [Θ]
  have hcomp : IsLocalDiffeomorphAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω
      (C.τ i j ∘ (Subtype.val : C.glueData.U i → Fin n → ℂ) ∘ C.glueData.f i j) x :=
    ((hf i j x).comp (hg := hU i (C.glueData.f i j x))).comp (hg := hτ_ld)
  exact IsLocalDiffeomorphAt.of_comp_left hcomp
    ((hf j i (C.glueData.t i j x)).comp (hg := hU j _))
    (C.glueData.t i j).hom.continuous.continuousAt

theorem isManifold_X : IsManifold 𝓘(ℂ, Fin n → ℂ) ∞ C.X :=
  C.isCompatible_glueData.isManifold.of_ne_zero ∞ (by simp)

theorem secondCountableTopology_X : SecondCountableTopology C.X := by
  have : Countable C.glueData.J := C.countable
  have : ∀ i, SecondCountableTopology (C.glueData.U i) :=
    fun i ↦ inferInstanceAs (SecondCountableTopology (C.pieceOpen i))
  exact TopCat.GlueData.secondCountableTopology C.glueData

theorem t2Space_X : T2Space C.X := by
  have : ∀ i, T2Space (C.glueData.U i) :=
    fun i ↦ inferInstanceAs (T2Space (C.pieceOpen i))
  refine C.glueData.t2Space_iff_isClosed_chartRel.2 fun i j ↦
    isClosed_of_closure_subset fun ⟨a, b⟩ hab ↦ ?_
  have hrel_sub_W : C.glueData.chartRel i j ⊆
      (fun p : C.glueData.U i × C.glueData.U j ↦ p.1.1) ⁻¹' closure (C.pairBuf i j).W := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨z, rfl, -⟩ := C.glueData.mem_chartRel_iff_exists.1 hxy
    exact subset_closure (C.VInter_subset_W z.2)
  have ha_clW : a.1 ∈ closure (C.pairBuf i j).W :=
    (isClosed_closure.preimage (continuous_subtype_val.comp continuous_fst)).closure_subset_iff.2
      hrel_sub_W hab
  have ha_Ω : a.1 ∈ C.Ω i j := (C.pairBuf i j).closure_W_subset ha_clW
  have hτ_eq : C.τ i j a.1 = b.1 := by
    by_contra hne
    obtain ⟨U₁, U₂, hU₁, hU₂, haU₁, hbU₂, hdisj⟩ := t2_separation hne
    have hcont : ContinuousAt
        (fun p : C.glueData.U i × C.glueData.U j ↦ C.τ i j p.1.1) (a, b) :=
      ContinuousAt.comp (g := C.τ i j) (f := fun p : C.glueData.U i × C.glueData.U j ↦ p.1.1)
        ((C.τ i j).continuousOn.continuousAt
          ((C.τ i j).open_source.mem_nhds (C.Ω_subset_τ_source i j ha_Ω)))
        (continuous_subtype_val.comp continuous_fst).continuousAt
    have hnhds :
        {p : C.glueData.U i × C.glueData.U j | C.τ i j p.1.1 ∈ U₁ ∧ p.2.1 ∈ U₂} ∈ 𝓝 (a, b) :=
      Filter.inter_mem (hcont.preimage_mem_nhds (hU₁.mem_nhds haU₁))
        ((continuous_subtype_val.comp continuous_snd).continuousAt.preimage_mem_nhds
          (hU₂.mem_nhds hbU₂))
    obtain ⟨⟨x, y⟩, ⟨hxU₁, hyU₂⟩, hxy⟩ := mem_closure_iff_nhds.1 hab _ hnhds
    obtain ⟨z, rfl, rfl⟩ := C.glueData.mem_chartRel_iff_exists.1 hxy
    exact Set.disjoint_left.1 hdisj hxU₁ hyU₂
  have ha_inter : a.1 ∈ C.VInter i j :=
    ⟨⟨a.2, ha_Ω⟩, by rw [mem_preimage, hτ_eq]; exact b.2⟩
  exact C.glueData.mem_chartRel_of_mem_closure hab ⟨⟨a, ha_inter⟩, rfl⟩

/-! #### Step 6: Conjugation involution `σ` and real-analytic embedding `ι` -/

def conjHom : C.glueData.toGlueData.glued ⟶ C.glueData.toGlueData.glued :=
  Multicoequalizer.desc C.glueData.toGlueData.diagram C.glueData.toGlueData.glued
    (fun i ↦ TopCat.ofHom (X := C.glueData.U i) (Y := C.glueData.U i)
      { toFun := fun z ↦ ⟨star z.1, C.star_mem_VHat.2 z.2⟩
        continuous_toFun := (continuous_star.comp continuous_subtype_val).subtype_mk _ } ≫
      C.glueData.toGlueData.ι i)
    (by
      rintro ⟨i, j⟩
      ext x
      have hx_star : star x.1.1 ∈ C.VInter i j := by
        refine ⟨⟨C.star_mem_VHat.2 x.2.1.1, C.star_mem_Ω.2 x.2.1.2⟩, ?_⟩
        rw [mem_preimage, C.τ_star (i : C.J) (j : C.J)]
        exact C.star_mem_VHat.2 x.2.2
      let y : C.glueData.V (i, j) := ⟨⟨star x.1.1, C.star_mem_VHat.2 x.2.1.1⟩, hx_star⟩
      have h1 := (C.glueData.glue_condition_apply i j y).symm
      change C.glueData.toGlueData.ι i ⟨star x.1.1, C.star_mem_VHat.2 x.2.1.1⟩ =
        C.glueData.toGlueData.ι j ⟨star (C.τ i j x.1.1),
          C.star_mem_VHat.2 (C.mapsTo_τ_VInter x.2).1.1⟩
      refine Eq.trans h1 (congrArg (C.glueData.toGlueData.ι j) ?_)
      exact Subtype.ext (C.τ_star i j x.1.1))

def conj : C.X → C.X :=
  C.conjHom

def conjPiece (i : C.glueData.J) (z : C.glueData.U i) : C.glueData.U i :=
  ⟨star z.1, C.star_mem_VHat.2 z.2⟩

theorem conj_ι (i : C.glueData.J) (z : C.glueData.U i) :
    C.conj (C.glueData.toGlueData.ι i z) =
      C.glueData.toGlueData.ι i (C.conjPiece i z) := by
  unfold conj conjHom conjPiece
  exact ConcreteCategory.congr_hom
    (Multicoequalizer.π_desc C.glueData.toGlueData.diagram C.glueData.toGlueData.glued _ _ i) z

theorem involutive_conj : Function.Involutive C.conj := by
  intro x
  obtain ⟨i, z, rfl⟩ := C.glueData.ι_jointly_surjective x
  rw [C.conj_ι, C.conj_ι]
  congr 1
  exact Subtype.ext (star_star z.1)

theorem exists_holomorphicChart_conj (x : C.X) :
    letI := C.isManifold_X
    ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin n → ℂ) ∞ C.X,
      x ∈ φ.source ∧ ∀ y ∈ φ.source, C.conj y ∈ φ.source ∧ φ (C.conj y) = star (φ y) := by
  let _ := C.isManifold_X
  refine ⟨chartAt (Fin n → ℂ) x, chart_mem_maximalAtlas x,
    mem_chart_source (Fin n → ℂ) x, ?_⟩
  obtain ⟨i, z₀, rfl, hchart⟩ :=
    C.glueData.exists_chartAt_chartedSpace_eq (H := Fin n → ℂ) x
  have : Nonempty (C.glueData.U i) := ⟨z₀⟩
  have hne : Nonempty (C.pieceOpen (i : C.J)) := ⟨z₀⟩
  have hchartU_src : (chartAt (Fin n → ℂ) z₀).source = univ := by
    change ((OpenPartialHomeomorph.refl (Fin n → ℂ)).subtypeRestr hne).source = univ
    simp
  have hchartU_app (z : C.glueData.U i) : chartAt (Fin n → ℂ) z₀ z = z.1 := rfl
  have hsrc : (chartAt (Fin n → ℂ) (C.glueData.toGlueData.ι i z₀)).source =
      Set.range (C.glueData.toGlueData.ι i) := by
    rw [hchart, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      IsOpenEmbedding.toOpenPartialHomeomorph_target, hchartU_src, preimage_univ, inter_univ]
  have happ (z : C.glueData.U i) :
      chartAt (Fin n → ℂ) (C.glueData.toGlueData.ι i z₀)
        (C.glueData.toGlueData.ι i z) = z.1 := by
    rw [hchart, OpenPartialHomeomorph.trans_apply,
      (C.glueData.ι_isOpenEmbedding i).toOpenPartialHomeomorph_left_inv, hchartU_app]
  intro y hy
  rw [hsrc] at hy
  obtain ⟨z, rfl⟩ := hy
  rw [hsrc, C.conj_ι]
  exact ⟨⟨_, rfl⟩, by rw [happ, happ]; rfl⟩

def embedCoord {i : C.J} {p : M} (hp : p ∈ C.V i) : C.glueData.U (i : C.glueData.J) :=
  ⟨realToComplex (C.φ i p), C.realToComplex_mem_VHat.2 (mem_image_of_mem _ hp)⟩

def embed (p : M) : C.X :=
  C.glueData.toGlueData.ι (C.embedIdx p : C.glueData.J) (C.embedCoord (C.mem_V_embedIdx p))

theorem embed_eq_ι {i : C.J} {p : M} (hp : p ∈ C.V i) :
    C.embed p = C.glueData.toGlueData.ι (i : C.glueData.J) (C.embedCoord hp) := by
  let j := C.embedIdx p
  have hpj : p ∈ C.V j := C.mem_V_embedIdx p
  refine (C.glueData.ι_eq_iff_rel (j : C.glueData.J) (i : C.glueData.J) _ _).2 ?_
  have hinter : realToComplex (C.φ j p) ∈ C.VInter j i := by
    refine ⟨⟨(C.embedCoord hpj).2,
      C.realToComplex_mem_Ω ⟨C.V_subset_U j hpj, C.V_subset_U i hp⟩⟩, ?_⟩
    rw [mem_preimage, C.τ_realToComplex ⟨C.U_subset_T j (C.V_subset_U j hpj),
      C.U_subset_T i (C.V_subset_U i hp)⟩]
    exact (C.embedCoord hp).2
  refine ⟨⟨C.embedCoord hpj, hinter⟩, rfl, Subtype.ext ?_⟩
  exact C.τ_realToComplex ⟨C.U_subset_T j (C.V_subset_U j hpj),
    C.U_subset_T i (C.V_subset_U i hp)⟩

theorem fixedPoints_conj :
    Function.fixedPoints C.conj = Set.range C.embed := by
  ext x
  change C.conj x = x ↔ x ∈ Set.range C.embed
  refine ⟨fun hfix ↦ ?_, ?_⟩
  · obtain ⟨i, z, rfl⟩ := C.glueData.ι_jointly_surjective x
    rw [C.conj_ι] at hfix
    have hz_star : star z.1 = z.1 := congrArg Subtype.val (C.glueData.ι_injective i hfix)
    obtain ⟨u, hu⟩ := star_eq_self_iff_exists_realToComplex.1 hz_star
    have hu_V : u ∈ C.φ (i : C.J) '' C.V (i : C.J) :=
      C.realToComplex_mem_VHat.1 (hu ▸ z.2)
    obtain ⟨p, hp, rfl⟩ := hu_V
    refine ⟨p, ?_⟩
    rw [C.embed_eq_ι hp]
    congr 1
    exact Subtype.ext hu
  · rintro ⟨p, rfl⟩
    rw [embed, C.conj_ι (C.embedIdx p : C.glueData.J)]
    congr 1
    exact Subtype.ext (star_realToComplex _)

theorem injective_embed : Function.Injective C.embed := by
  intro p q hpq
  have hp := C.mem_V_embedIdx p
  have hq := C.mem_V_embedIdx q
  obtain ⟨z, hz1, hz2⟩ :=
    (C.glueData.ι_eq_iff_rel (C.embedIdx p : C.glueData.J) (C.embedIdx q : C.glueData.J) _ _).1
      hpq
  have hz_val : z.1.1 = realToComplex (C.φ (C.embedIdx p) p) := congrArg Subtype.val hz1
  have hτ_val : C.τ (C.embedIdx p) (C.embedIdx q) z.1.1 =
      realToComplex (C.φ (C.embedIdx q) q) := congrArg Subtype.val hz2
  have hcl :
      realToComplex (C.φ (C.embedIdx p) p) ∈
        closure (C.Ω (C.embedIdx p) (C.embedIdx q)) :=
    subset_closure (hz_val ▸ z.2.1.2)
  exact C.eq_of_mem_closure_Ω (C.V_subset_U _ hp)
    (C.U_subset_T _ (C.V_subset_U _ hq)) hcl (hz_val ▸ hτ_val)

theorem contMDiff_embed :
    ContMDiff I 𝓘(ℝ, Fin n → ℂ) ω C.embed := by
  classical
  have : IsManifold 𝓘(ℝ, Fin n → ℂ) ω C.X :=
    C.isManifold_X.restrictScalars_of_ne_zero ω (by simp)
  intro p
  let i : C.J := C.embedIdx p
  let iG : C.glueData.J := i
  have hp : p ∈ C.V i := C.mem_V_embedIdx p
  have : IsManifold 𝓘(ℝ, Fin n → ℂ) ω (C.glueData.U iG) :=
    (inferInstance :
      IsManifold 𝓘(ℂ, Fin n → ℂ) ω (C.glueData.U iG)).restrictScalars_of_ne_zero ω (by simp)
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℂ) :=
    ContinuousLinearMap.piMap fun _ ↦ Complex.ofRealCLM
  have hφp : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ω (C.φ i) p :=
    (C.chartPartialDiffeomorph i).contMDiffOn_toFun.contMDiffAt
      ((C.φ i).open_source.mem_nhds (C.V_subset_source i hp))
  have hLφ : ContMDiffAt I 𝓘(ℝ, Fin n → ℂ) ω (fun q ↦ L (C.φ i q)) p :=
    L.contDiff.contMDiff.contMDiffAt.comp p hφp
  let g : M → C.glueData.U iG := fun q ↦
    if hq : q ∈ C.V i then ⟨L (C.φ i q), C.realToComplex_mem_VHat.2 (mem_image_of_mem _ hq)⟩
    else ⟨L (C.φ i p), C.realToComplex_mem_VHat.2 (mem_image_of_mem _ hp)⟩
  have hg_q {q : M} (hq : q ∈ C.V i) :
      g q = ⟨L (C.φ i q), C.realToComplex_mem_VHat.2 (mem_image_of_mem _ hq)⟩ := by
    simp only [g, hq, ↓reduceDIte]
    exact Subtype.ext rfl
  have hg_val :
      (Subtype.val : C.glueData.U iG → Fin n → ℂ) ∘ g =ᶠ[𝓝 p] fun q ↦ L (C.φ i q) := by
    filter_upwards [(C.isOpen_V i).mem_nhds hp] with q hq
    exact congrArg Subtype.val (hg_q hq)
  have hg_cont : ContinuousAt g p :=
    IsInducing.subtypeVal.continuousAt_iff.2 (hLφ.continuousAt.congr hg_val.symm)
  have hg_mdiff : ContMDiffAt I 𝓘(ℝ, Fin n → ℂ) ω g p := by
    rw [← contMDiffWithinAt_univ]
    have hpf := contMDiffWithinAt_univ.2 (hLφ.congr_of_eventuallyEq hg_val)
    exact hpf.of_comp_isLocalDiffeomorph
      (TauCeti.isLocalDiffeomorph_subtype_val (U := C.pieceOpen i) (g p))
      hg_cont.continuousWithinAt
  have hι_real :
      ContMDiff 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) ω (C.glueData.toGlueData.ι iG) := by
    simpa only [modelWithCornersSelf_restrictScalars] using
      (C.isCompatible_glueData.contMDiff_ι iG).restrictScalars ℝ
  have hcomp :
      ContMDiffAt I 𝓘(ℝ, Fin n → ℂ) ω (fun q ↦ C.glueData.toGlueData.ι iG (g q)) p :=
    hι_real.contMDiffAt.comp p hg_mdiff
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(C.isOpen_V i).mem_nhds hp] with q hq
  rw [C.embed_eq_ι hq, hg_q hq]
  exact congrArg (C.glueData.toGlueData.ι iG) (Subtype.ext (funext fun _ ↦ rfl))

theorem isClosedEmbedding_embed :
    Topology.IsClosedEmbedding C.embed := by
  have : T2Space C.X := C.t2Space_X
  have hcont_embed : Continuous C.embed := C.contMDiff_embed.continuous
  have hcont_conj : Continuous C.conj := C.conjHom.hom.continuous
  have hclosed_range : IsClosed (Set.range C.embed) := by
    rw [← C.fixedPoints_conj]
    exact isClosed_eq hcont_conj continuous_id
  have hind : Topology.IsInducing C.embed := by
    refine ⟨le_antisymm hcont_embed.le_induced fun O hO ↦ isOpen_induced_iff.2 ?_⟩
    let W : Set C.X := ⋃ i : C.J, C.glueData.toGlueData.ι i ''
      {z : C.glueData.U i | complexToReal z.1 ∈ C.φ i '' (O ∩ C.V i)}
    have hW_open : IsOpen W := isOpen_iUnion fun i ↦ by
      have hOV : IsOpen (C.φ i '' (O ∩ C.V i)) :=
        C.isOpen_image_φ (hO.inter (C.isOpen_V i))
          (inter_subset_right.trans (C.V_subset_source i))
      exact (C.glueData.ι_isOpenEmbedding i).isOpenMap _
        (hOV.preimage (continuous_complexToReal.comp continuous_subtype_val))
    refine ⟨W, hW_open, Subset.antisymm (fun p hpW ↦ ?_) (fun p hpO ↦ ?_)⟩
    · obtain ⟨i, z, hz, hiz⟩ := mem_iUnion.1 hpW
      have hp_j := C.mem_V_embedIdx p
      have hrel : C.glueData.toGlueData.ι (C.embedIdx p : C.glueData.J) (C.embedCoord hp_j) =
          C.glueData.toGlueData.ι (i : C.glueData.J) z := hiz.symm
      obtain ⟨w, hw1, hw2⟩ := (C.glueData.ι_eq_iff_rel _ _ _ _).1 hrel
      have hw_val : w.1.1 = realToComplex (C.φ (C.embedIdx p) p) := congrArg Subtype.val hw1
      have hz_val : z.1 = C.τ (C.embedIdx p) i (realToComplex (C.φ (C.embedIdx p) p)) := by
        rw [← hw_val]
        exact (congrArg Subtype.val hw2).symm
      have hz_star : star z.1 = z.1 := by
        rw [hz_val, ← C.τ_star, star_realToComplex]
      obtain ⟨u, hu⟩ := star_eq_self_iff_exists_realToComplex.1 hz_star
      have hu_re : u = complexToReal z.1 := by rw [← hu, complexToReal_realToComplex]
      have hz' : u ∈ C.φ i '' (O ∩ C.V i) := by
        rw [hu_re]
        exact hz
      obtain ⟨q, ⟨hqO, hqV⟩, hφq⟩ := hz'
      have hτ_eq : C.τ (C.embedIdx p) i (realToComplex (C.φ (C.embedIdx p) p)) =
          realToComplex (C.φ i q) := by
        rw [← hz_val, ← hu, hφq]
      have hcl : realToComplex (C.φ (C.embedIdx p) p) ∈ closure (C.Ω (C.embedIdx p) i) :=
        subset_closure (hw_val ▸ w.2.1.2)
      obtain rfl : p = q := C.eq_of_mem_closure_Ω (C.V_subset_U _ hp_j)
        (C.U_subset_T i (C.V_subset_U i hqV)) hcl hτ_eq
      exact hqO
    · rw [mem_preimage]
      let i := C.embedIdx p
      have hpV : p ∈ C.V i := C.mem_V_embedIdx p
      refine mem_iUnion_of_mem i ?_
      rw [C.embed_eq_ι hpV]
      refine mem_image_of_mem (C.glueData.toGlueData.ι (i : C.glueData.J)) ?_
      exact ⟨p, ⟨hpO, hpV⟩, (complexToReal_realToComplex _).symm⟩
  exact { toIsEmbedding := ⟨hind, C.injective_embed⟩, isClosed_range := hclosed_range }

theorem exists_holomorphicChart_comp_embed (p : M) :
    letI := C.isCompatible_glueData.isManifold
    ∃ χ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin n → ℂ) ω C.X,
      C.embed p ∈ χ.source ∧
      χ ∘ (C.embed ∘ (C.φ (C.embedIdx p)).symm) =ᶠ[𝓝 (C.φ (C.embedIdx p) p)]
        (ContinuousLinearMap.piMap fun _ : Fin n ↦ Complex.ofRealCLM) := by
  let _ := C.isCompatible_glueData.isManifold
  let i : C.J := C.embedIdx p
  let iG : C.glueData.J := i
  have hp : p ∈ C.V i := C.mem_V_embedIdx p
  let y₀ : C.glueData.U iG := C.embedCoord hp
  have : Nonempty (C.glueData.U iG) := ⟨y₀⟩
  let χ : OpenPartialHomeomorph C.X (Fin n → ℂ) :=
    (C.isCompatible_glueData.partialDiffeomorphι iG).symm.toOpenPartialHomeomorph.trans
      (chartAt (Fin n → ℂ) y₀)
  have hχ_atlas : χ ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin n → ℂ) ω C.X :=
    (C.isCompatible_glueData.partialDiffeomorphι iG).symm.trans_mem_maximalAtlas
      (chart_mem_maximalAtlas y₀)
  have hι_apply (z : C.glueData.U iG) :
      (C.isCompatible_glueData.partialDiffeomorphι iG).symm
        (C.glueData.toGlueData.ι iG z) = z := by
    have hz : z ∈ (C.isCompatible_glueData.partialDiffeomorphι iG).source := by simp
    simpa using (C.isCompatible_glueData.partialDiffeomorphι iG).left_inv hz
  have hιp_src : C.embed p ∈ χ.source := by
    have hιp_eq : C.embed p = C.glueData.toGlueData.ι iG y₀ := rfl
    rw [hιp_eq, OpenPartialHomeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · change C.glueData.toGlueData.ι iG y₀ ∈
        (C.isCompatible_glueData.partialDiffeomorphι iG).target
      rw [TopCat.GlueData.IsCompatible.partialDiffeomorphι_target]
      exact ⟨y₀, rfl⟩
    · rw [mem_preimage]
      change (C.isCompatible_glueData.partialDiffeomorphι iG).symm
        (C.glueData.toGlueData.ι iG y₀) ∈ (chartAt (Fin n → ℂ) y₀).source
      rw [hι_apply y₀]
      exact mem_chart_source _ y₀
  refine ⟨χ, hχ_atlas, hιp_src, ?_⟩
  have hU₀_open : IsOpen (C.φ i '' C.V i) :=
    C.isOpen_image_φ (C.isOpen_V i) (C.V_subset_source i)
  filter_upwards [hU₀_open.mem_nhds (mem_image_of_mem _ hp)] with u hu
  obtain ⟨q, hqV, rfl⟩ := hu
  have hq_src := C.V_subset_source i hqV
  change χ (C.embed ((C.φ i).symm (C.φ i q))) =
    (ContinuousLinearMap.piMap fun _ : Fin n ↦ Complex.ofRealCLM) (C.φ i q)
  rw [(C.φ i).left_inv hq_src, C.embed_eq_ι hqV]
  change chartAt (Fin n → ℂ) y₀
    ((C.isCompatible_glueData.partialDiffeomorphι iG).symm
      (C.glueData.toGlueData.ι iG (C.embedCoord hqV))) =
    (ContinuousLinearMap.piMap fun _ : Fin n ↦ Complex.ofRealCLM) (C.φ i q)
  rw [hι_apply (C.embedCoord hqV)]
  rfl

abbrev mfderivEmbed (p : M) : TangentSpace I p →L[ℝ] (Fin n → ℂ) :=
  mfderiv I 𝓘(ℝ, Fin n → ℂ) C.embed p

theorem exists_linearEquiv_map_range_mfderiv_embed (p : M) :
    ∃ A_ℂ : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ),
      LinearMap.range
        (ContinuousLinearMap.piMap fun _ : Fin n ↦ Complex.ofRealCLM).toLinearMap =
        (LinearMap.range (C.mfderivEmbed p).toLinearMap).map
          ((A_ℂ : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)).restrictScalars ℝ) := by
  let _ : IsManifold 𝓘(ℂ, Fin n → ℂ) ω C.X := C.isCompatible_glueData.isManifold
  let _ : IsManifold 𝓘(ℝ, Fin n → ℂ) ω C.X :=
    C.isManifold_X.restrictScalars_of_ne_zero ω (by simp)
  let i := C.embedIdx p
  have hp : p ∈ C.V i := C.mem_V_embedIdx p
  let x₀ : Fin n → ℝ := C.φ i p
  have hx₀_tgt : x₀ ∈ (C.φ i).target := (C.φ i).map_source (C.V_subset_source i hp)
  have hφsymm_ld : IsLocalDiffeomorphAt 𝓘(ℝ, Fin n → ℝ) I ω (C.φ i).symm x₀ :=
    TauCeti.isLocalDiffeomorphAt_of_eqOn (Φ := (C.chartPartialDiffeomorph i).symm) hx₀_tgt
      fun _ _ ↦ rfl
  have hp_symm : (C.φ i).symm x₀ = p := (C.φ i).left_inv (C.V_subset_source i hp)
  have hrange₁ :
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℂ) (C.embed ∘ (C.φ i).symm) x₀).range =
        (C.mfderivEmbed p).range :=
    (hφsymm_ld.range_mfderiv_comp (K := 𝓘(ℝ, Fin n → ℂ)) (g := C.embed)
      (by simp : (ω : ℕ∞ω) ≠ 0)).trans
      (congrArg (fun q ↦ (C.mfderivEmbed q).range) hp_symm)
  obtain ⟨χ, hχ_atlas, hιp_src, hev⟩ := C.exists_holomorphicChart_comp_embed p
  let y₀ : C.X := (C.embed ∘ (C.φ i).symm) x₀
  have hy₀_eq : y₀ = C.embed p := congrArg C.embed hp_symm
  have hχ_ld_ℂ : IsLocalDiffeomorphAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω χ y₀ :=
    χ.isLocalDiffeomorphAt_of_mem_maximalAtlas hχ_atlas (hy₀_eq.symm ▸ hιp_src)
  have hχ_mdiff_ℂ : MDifferentiableAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) χ y₀ :=
    hχ_ld_ℂ.mdifferentiableAt (by simp)
  let A_ℂ : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
    hχ_ld_ℂ.mfderivToContinuousLinearEquiv (by simp)
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℂ) :=
    ContinuousLinearMap.piMap fun _ ↦ Complex.ofRealCLM
  have hgm_diff : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℂ)
      (C.embed ∘ (C.φ i).symm) x₀ :=
    (C.contMDiff_embed.contMDiffAt.comp x₀ hφsymm_ld.contMDiffAt).mdifferentiableAt (by simp)
  have hchain : mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℂ)
      (χ ∘ (C.embed ∘ (C.φ i).symm)) x₀ = L :=
    (L.hasMFDerivAt.congr_of_eventuallyEq_abuse hev).mfderiv
  rw [mfderiv_comp x₀ (hχ_mdiff_ℂ.restrictScalars ℝ) hgm_diff] at hchain
  have hA_eq (v : Fin n → ℂ) :
      mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) χ y₀ v = A_ℂ v :=
    DFunLike.congr_fun (hχ_mdiff_ℂ.mfderiv_restrictScalars ℝ) v
  have hchain_app (u : Fin n → ℝ) :
      A_ℂ (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℂ) (C.embed ∘ (C.φ i).symm) x₀ u) = L u :=
    (hA_eq _).symm.trans (DFunLike.congr_fun hchain u)
  refine ⟨A_ℂ.toLinearEquiv, ?_⟩
  change LinearMap.range L.toLinearMap =
    (C.mfderivEmbed p).range.map
      ((A_ℂ.toLinearEquiv : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)).restrictScalars ℝ)
  rw [← hrange₁]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨u, rfl⟩
    exact ⟨mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℂ) (C.embed ∘ (C.φ i).symm) x₀ u,
      ⟨u, rfl⟩, hchain_app u⟩
  · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, (hchain_app u).symm⟩

theorem isTotallyRealEmbedding_embed [FiniteDimensional ℝ E] :
    IsTotallyRealEmbedding I 𝓘(ℝ, Fin n → ℂ) ω
      (fun _ : C.X ↦ AlmostComplexStructure.ofComplexModule (Fin n → ℂ)) C.embed := by
  have : IsManifold 𝓘(ℝ, Fin n → ℂ) ω C.X :=
    C.isManifold_X.restrictScalars_of_ne_zero ω (by simp)
  have hdim : 2 * Module.finrank ℝ E = Module.finrank ℝ (Fin n → ℂ) := by
    rw [e₀.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype ℝ, Module.finrank_pi_fintype ℝ]
    simp [Complex.finrank_real_complex, Finset.sum_const, mul_comm]
  refine isTotallyRealEmbedding_of_contMDiff (by simp) C.contMDiff_embed
    C.isClosedEmbedding_embed.isEmbedding hdim
    (isMaximalTotallyRealMap_iff.2 fun p ↦ ?_)
  obtain ⟨A_ℂ, hmap_range⟩ := C.exists_linearEquiv_map_range_mfderiv_embed p
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℂ) :=
    ContinuousLinearMap.piMap fun _ ↦ Complex.ofRealCLM
  have hJ_eq : (AlmostComplexStructure.ofComplexModule (Fin n → ℂ)).toLinearMap =
      (LinearMap.lsmul ℂ (Fin n → ℂ) Complex.I).restrictScalars ℝ := by
    ext v k
    simp [AlmostComplexStructure.ofComplexModule_apply]
  have hL_tot : IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (Fin n → ℂ) Complex.I).restrictScalars ℝ)
      (LinearMap.range L.toLinearMap) := by
    have h1 := ((L.isTotallyRealEmbedding_iff ω).1 (isTotallyRealEmbedding_realLocus ω)).2
    rwa [hJ_eq] at h1
  change IsMaximalTotallyReal (AlmostComplexStructure.ofComplexModule (Fin n → ℂ)).toLinearMap
    (LinearMap.range (C.mfderivEmbed p).toLinearMap)
  rw [hJ_eq]
  exact hL_tot.of_map_linearEquiv A_ℂ hmap_range

end ShrunkChartCover

end BruhatWhitney

public noncomputable section

/-! ### Main existence theorems -/

/-- **Bruhat–Whitney complexification (with explicit model coordinates, `σ`-compact form).**
Every Hausdorff, `σ`-compact real-analytic manifold `M` without boundary modelled on `E`,
equipped with a continuous linear equivalence `e₀ : E ≃L[ℝ] (Fin n → ℝ)`, admits a global
complexification `X : Type` modelled on `Fin n → ℂ`. -/
theorem exists_isRealAnalyticComplexification_of_continuousLinearEquiv
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
    [T2Space M] [SigmaCompactSpace M]
    {n : ℕ} (e₀ : E ≃L[ℝ] (Fin n → ℝ)) :
    haveI : FiniteDimensional ℝ E := e₀.symm.toLinearEquiv.finiteDimensional
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : ChartedSpace (Fin n → ℂ) X)
      (ι : M → X) (σ : X → X),
      IsRealAnalyticComplexification I M n X ι σ := by
  have : FiniteDimensional ℝ E := e₀.symm.toLinearEquiv.finiteDimensional
  obtain ⟨C⟩ := exists_shrunkChartCover (I := I) (M := M) e₀
  refine ⟨C.X, inferInstance, C.instChartedSpaceX, C.embed, C.conj,
    { t2Space := C.t2Space_X
      secondCountableTopology := C.secondCountableTopology_X
      isManifold := C.isManifold_X
      isClosedEmbedding := C.isClosedEmbedding_embed
      isTotallyRealEmbedding := C.isTotallyRealEmbedding_embed
      involutive_conj := C.involutive_conj
      fixedPoints_conj := C.fixedPoints_conj
      exists_holomorphicChart_conj := C.exists_holomorphicChart_conj }⟩

/-- **Bruhat–Whitney complexification (`σ`-compact form).** Every Hausdorff, `σ`-compact
real-analytic manifold `M` without boundary of real dimension `n` embeds as the fixed-point locus
of an anti-holomorphic involution into a Hausdorff, second-countable complex manifold `X : Type`
of complex dimension `n`. -/
theorem exists_isRealAnalyticComplexification_of_sigmaCompact
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
    [T2Space M] [SigmaCompactSpace M]
    {n : ℕ} (hn : Module.finrank ℝ E = n) :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : ChartedSpace (Fin n → ℂ) X)
      (ι : M → X) (σ : X → X),
      IsRealAnalyticComplexification I M n X ι σ := by
  have hfr : Module.finrank ℝ E = Module.finrank ℝ (Fin n → ℝ) := by
    rw [hn, Module.finrank_pi]
    simp
  exact exists_isRealAnalyticComplexification_of_continuousLinearEquiv I
    (LinearEquiv.ofFinrankEq E (Fin n → ℝ) hfr).toContinuousLinearEquiv

/-- **Bruhat–Whitney global complexification.** Every Hausdorff, second-countable real-analytic
manifold `M` without boundary of real dimension `n` embeds as a closed, maximal totally real `C^ω`
submanifold into a Hausdorff, second-countable complex manifold `X : Type` of complex dimension
`n`, equipped with an anti-holomorphic involution `σ : X → X` whose fixed-point locus is
`Set.range ι`. -/
theorem exists_isRealAnalyticComplexification
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
    [T2Space M] [SecondCountableTopology M]
    {n : ℕ} (hn : Module.finrank ℝ E = n) :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : ChartedSpace (Fin n → ℂ) X)
      (ι : M → X) (σ : X → X),
      IsRealAnalyticComplexification I M n X ι σ := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  exact exists_isRealAnalyticComplexification_of_sigmaCompact I M hn

end

end TauCeti
