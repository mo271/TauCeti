/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.RingTheory.Finiteness.Cofinite
public import TauCeti.Topology.Algebra.OpenMapping.Henkel
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.LocallyConvex.Bounded
import TauCeti.Analysis.Normed.Ring.PseudoUniformizer
import TauCeti.Topology.Algebra.OpenMapping.Converse

/-!
# Schwartz's finiteness theorem for compact perturbations

L. Schwartz's theorem (1953) asserts that if `T, K : E →L[𝕜] F` are continuous linear maps with
`T` surjective (or, more generally, an open map) and `K` a compact operator, then `T + K` has
finite-dimensional cokernel, closed range, and is a strict morphism (open onto its range), with
no finite-dimensionality or complementability hypothesis on `ker T`.

This file proves Schwartz's theorem over any complete nontrivially normed field `𝕜` (in particular
`ℝ`, `ℂ`, or `ℚ_[p]`), for a complete first-countable uniform polynormable space `E` and a `T0`
topological vector space `F`. When `T` is assumed directly to be an open map (`IsOpenMap T`), no
`BaireSpace`, completeness, metrisability, uniform structure, or local convexity is needed on the
target `F`. When `T` is assumed surjective (`Function.Surjective T`) and `F` is a `BaireSpace`,
the Banach–Schauder / Henkel open mapping theorem (`ContinuousLinearMap.isOpenMap_of_surjective`)
supplies openness of `T`.

For a complex Fréchet space stated via `[LocallyConvexSpace ℝ E]` (without opening `ComplexOrder`),
`LocallyConvexSpace.toPolynormableSpace_of_rclike` in `TauCeti.Analysis.LocallyConvex.WithSeminorms`
supplies `PolynormableSpace ℂ E`. For a completely metrisable uniform target `F` carrying
`[UniformSpace F] [IsUniformAddGroup F] [MetrizableSpace F] [CompleteSpace F]`, Mathlib's
`IsUniformAddGroup.uniformity_countably_generated` supplies `(𝓤 F).IsCountablyGenerated` so that
`BaireSpace F` synthesizes automatically via `Mathlib.Topology.Baire.CompleteMetrizable`.

The proof follows Demailly, Chapter IX, §1.10 (originally Schwartz 1953):

1. Using an antitone scaling factor `c : 𝕜` with `0 < ‖c‖ < 1` and compactness of
   `closure (K '' U)`, a finite-iteration argument produces a finite subset `s : Finset F` such
   that `(T + K).range ⊔ Submodule.span 𝕜 s` is dense in `F`.
2. When `(T + K).range` is dense and `E` is polynormable, the same iteration combined with a
   geometric-series seminorm estimate shows that `closure ((T + K) '' V)` is a neighbourhood of
   zero for every `V ∈ 𝓝 (0 : E)`. Removing the closure via
   `TauCeti.isOpenMap_of_closure_image_mem_nhds` shows that `T + K` is open
   (`ContinuousLinearMap.isOpenMap_add_of_isOpenMap_of_isCompactOperator_of_denseRange`), requiring
   neither `CompleteSpace 𝕜` nor `BaireSpace F`.
3. Applying step 2 to `(T + K).coprod g` on `E × (s → 𝕜)` forces `(T + K).range ⊔ span 𝕜 s = ⊤`,
   yielding finite-dimensional cokernel (`(T + K).range.CoFG`).
4. Replacing `s` by a lift of a finite basis of `F ⧸ (T + K).range`, applying step 2 once more shows
   that `(T + K).coprod ψ` is open and surjective, hence a quotient map whose preimage of
   `(T + K).range` is `E × {0}`, giving both closedness of `(T + K).range` and strictness of
   `T + K`.

## Main results

* `ContinuousLinearMap.isOpenMap_add_of_isOpenMap_of_isCompactOperator_of_denseRange`: a compact
  perturbation of an open continuous linear map with dense range is open.
* `ContinuousLinearMap.cofg_range_add_of_isOpenMap_of_isCompactOperator`,
  `ContinuousLinearMap.isClosed_range_add_of_isOpenMap_of_isCompactOperator`,
  `ContinuousLinearMap.isStrictMap_add_of_isOpenMap_of_isCompactOperator`: Schwartz's theorem for
  an open map `T` into an arbitrary `T0` topological vector space `F`.
* `ContinuousLinearMap.cofg_range_add_of_surjective_of_isCompactOperator`,
  `ContinuousLinearMap.isClosed_range_add_of_surjective_of_isCompactOperator`,
  `ContinuousLinearMap.isStrictMap_add_of_surjective_of_isCompactOperator`: the surjective forms
  into a `T0` Baire target `F`.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter IX, §§1.7–1.10.
* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §14.
* L. Schwartz, *Homomorphismes et applications complètement continues*,
  C. R. Acad. Sci. Paris **236** (1953), 2472–2473.
-/

public noncomputable section

open Filter Topology
open scoped Pointwise

namespace ContinuousLinearMap

/-! ### Private iteration and estimation helpers -/

private theorem iterate_decomp {R E F ι : Type*} [Ring R]
    [AddCommGroup E] [TopologicalSpace E] [Module R E]
    [AddCommGroup F] [TopologicalSpace F] [ContinuousAdd F] [Module R F]
    (T K : E →L[R] F) (c : R) (g : ι → F) {U : Set E} {A : Set ι}
    (hstep : ∀ x ∈ U, ∃ i ∈ A, ∃ x' ∈ U, K x - g i = c • T x')
    {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ (x : ℕ → E) (i : ℕ → ι), x 0 = x₀ ∧ (∀ n, x n ∈ U) ∧ (∀ n, i n ∈ A) ∧
      ∀ n, T x₀ =
        (∑ k ∈ Finset.range n, (-c) ^ k • ((T + K) (x k) - g (i k))) +
          (-c) ^ n • (T + K) (x n) - (-c) ^ n • K (x n) := by
  choose fi hi fx' hx' hrel using hstep
  let seq : ℕ → {x : E // x ∈ U} := Nat.rec ⟨x₀, hx₀⟩ fun _ s ↦ ⟨fx' s.1 s.2, hx' s.1 s.2⟩
  refine ⟨fun n ↦ (seq n).1, fun n ↦ fi (seq n).1 (seq n).2, rfl,
    fun n ↦ (seq n).2, fun n ↦ hi (seq n).1 (seq n).2, ?_⟩
  intro n
  induction n with
  | zero => simp [seq]
  | succ n ih =>
    have hK : K (seq n).1 = g (fi (seq n).1 (seq n).2) + c • T (seq (n + 1)).1 :=
      eq_add_of_sub_eq' (hrel (seq n).1 (seq n).2)
    have hpow : (-c) ^ (n + 1) • T (seq (n + 1)).1 = -((-c) ^ n • (c • T (seq (n + 1)).1)) := by
      rw [pow_succ, mul_neg, neg_smul, mul_smul]
    have hT : (T + K) (seq (n + 1)).1 - K (seq (n + 1)).1 = T (seq (n + 1)).1 := by simp
    rw [ih, Finset.sum_range_succ, hK, smul_add, sub_add_eq_sub_sub, add_sub_assoc]
    rw [← smul_sub, ← sub_add_eq_add_sub, add_assoc]
    rw [sub_eq_add_neg, add_assoc, ← hpow, ← hT, smul_sub, sub_eq_add_neg, add_assoc, add_comm]
    abel

private theorem seminorm_geom_sum_le {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (p : Seminorm 𝕜 E) {c : 𝕜} (hc : ‖c‖ < 1) {x e : ℕ → E} {R : ℝ} (hR : 0 ≤ R)
    (hx : ∀ k, p (x k) < 1) (he : ∀ k, p (e k) ≤ R) (n : ℕ) :
    p ((∑ k ∈ Finset.range n, (-c) ^ k • (x k - e k)) + (-c) ^ n • x n) ≤
      (1 + R) / (1 - ‖c‖) + 1 := by
  have hgeom : ∑ k ∈ Finset.range n, ‖c‖ ^ k ≤ 1 / (1 - ‖c‖) := by
    rw [geom_sum_eq hc.ne]
    have hdiv : (‖c‖ ^ n - 1) / (‖c‖ - 1) = (1 - ‖c‖ ^ n) / (1 - ‖c‖) := by
      rw [← neg_div_neg_eq]; ring_nf
    rw [hdiv]
    exact div_le_div_of_nonneg_right (sub_le_self 1 (pow_nonneg (norm_nonneg c) n))
      (sub_pos.mpr hc).le
  have hterm : ∀ k, p ((-c) ^ k • (x k - e k)) ≤ ‖c‖ ^ k * (1 + R) := fun k ↦ by
    rw [map_smul_eq_mul, norm_pow, norm_neg]
    exact mul_le_mul_of_nonneg_left
      ((map_sub_le_add p (x k) (e k)).trans (add_le_add (hx k).le (he k)))
      (pow_nonneg (norm_nonneg c) k)
  have hlast : p ((-c) ^ n • x n) ≤ 1 := by
    rw [map_smul_eq_mul, norm_pow, norm_neg]
    calc ‖c‖ ^ n * p (x n)
        ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (norm_nonneg c) hc.le) (hx n).le
          (apply_nonneg p _) zero_le_one
      _ = 1 := one_mul 1
  have hsum_le : p (∑ k ∈ Finset.range n, (-c) ^ k • (x k - e k)) ≤
      ∑ k ∈ Finset.range n, p ((-c) ^ k • (x k - e k)) :=
    Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
  calc p ((∑ k ∈ Finset.range n, (-c) ^ k • (x k - e k)) + (-c) ^ n • x n)
      ≤ p (∑ k ∈ Finset.range n, (-c) ^ k • (x k - e k)) + p ((-c) ^ n • x n) :=
        map_add_le_add p _ _
    _ ≤ (∑ k ∈ Finset.range n, p ((-c) ^ k • (x k - e k))) + 1 := add_le_add hsum_le hlast
    _ ≤ (∑ k ∈ Finset.range n, ‖c‖ ^ k * (1 + R)) + 1 :=
        add_le_add (Finset.sum_le_sum fun k _ ↦ hterm k) le_rfl
    _ = (∑ k ∈ Finset.range n, ‖c‖ ^ k) * (1 + R) + 1 := by rw [Finset.sum_mul]
    _ ≤ (1 / (1 - ‖c‖)) * (1 + R) + 1 :=
        add_le_add (mul_le_mul_of_nonneg_right hgeom (add_nonneg zero_le_one hR)) le_rfl
    _ = (1 + R) / (1 - ‖c‖) + 1 := by ring

/-! ### Step A: finite-dimensional dense supplement -/

private theorem exists_finset_dense_sup_range_add {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
    [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [T0Space F]
    [Module 𝕜 F] [ContinuousSMul 𝕜 F]
    (T K : E →L[𝕜] F) (hT : IsOpenMap T) (hK : IsCompactOperator K) :
    ∃ s : Finset F,
      Dense (((T + K).range ⊔ Submodule.span 𝕜 (s : Set F) : Submodule 𝕜 F) : Set F) := by
  obtain ⟨U, hU, hL⟩ := (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image K).mp hK
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one 𝕜
  have hc_ne : c ≠ 0 := norm_pos_iff.mp hc0
  have hW_open : IsOpen (c • (T '' interior U)) := (hT _ isOpen_interior).smul₀ hc_ne
  have hW0 : (0 : F) ∈ c • (T '' interior U) :=
    ⟨0, ⟨0, mem_interior_iff_mem_nhds.mpr hU, map_zero T⟩, smul_zero c⟩
  obtain ⟨s, -, hsfin, hcov⟩ := hL.elim_finite_subcover_image
    (fun y _ ↦ hW_open.preimage (continuous_sub_right y))
    fun y hy ↦ Set.mem_biUnion hy (by simpa using hW0)
  refine ⟨hsfin.toFinset, ?_⟩
  let M : Submodule 𝕜 F := (T + K).range ⊔ Submodule.span 𝕜 (hsfin.toFinset : Set F)
  have hstep : ∀ x ∈ interior U,
      ∃ y ∈ (hsfin.toFinset : Set F), ∃ x' ∈ interior U, K x - y = c • T x' := by
    intro x hx
    obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.mp (hcov (subset_closure ⟨x, interior_subset hx, rfl⟩))
    obtain ⟨w, ⟨x', hx', rfl⟩, hcw⟩ := Set.mem_smul_set.mp hzy
    exact ⟨y, by simpa using hy, x', hx', hcw.symm⟩
  have hsub : T '' interior U ⊆ (M.topologicalClosure : Set F) := by
    rintro _ ⟨x₀, hx₀, rfl⟩
    obtain ⟨x, y, -, hxU, hyS, hdecomp⟩ := iterate_decomp T K c id hstep hx₀
    have htend : Tendsto (fun n ↦ (-c) ^ n • K (x n)) atTop (𝓝 (0 : F)) :=
      (hL.isVonNBounded 𝕜).smul_tendsto_zero
        (Eventually.of_forall fun n ↦ subset_closure ⟨x n, interior_subset (hxU n), rfl⟩)
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by simpa using hc1))
    have hmem : ∀ n, T x₀ + (-c) ^ n • K (x n) ∈ (M : Set F) := fun n ↦ by
      rw [hdecomp n, sub_add_cancel]
      refine M.add_mem (M.sum_mem fun k _ ↦ M.smul_mem _ ?_) (M.smul_mem _ ?_)
      · exact M.sub_mem (Submodule.mem_sup_left (LinearMap.mem_range_self _ (x k)))
          (Submodule.mem_sup_right (Submodule.subset_span (hyS k)))
      · exact Submodule.mem_sup_left (LinearMap.mem_range_self _ (x n))
    exact mem_closure_of_tendsto (by simpa using htend.const_add (T x₀)) (Eventually.of_forall hmem)
  have htop : M.topologicalClosure = ⊤ :=
    Submodule.eq_top_of_nonempty_interior' _ ⟨0, mem_interior.mpr
      ⟨T '' interior U, hsub, hT _ isOpen_interior,
        ⟨0, mem_interior_iff_mem_nhds.mpr hU, map_zero T⟩⟩⟩
  rw [Dense]
  intro y
  exact (SetLike.ext_iff.mp htop y).mpr trivial

/-! ### Step B: openness under dense range -/

private theorem exists_approx_finset_of_denseRange {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
    [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [Module 𝕜 F] [ContinuousSMul 𝕜 F]
    (T K : E →L[𝕜] F) (hT : IsOpenMap T) (hdense : Dense ((T + K).range : Set F))
    {V₁ : Set E} (hV₁_open : IsOpen V₁) (hV₁0 : (0 : E) ∈ V₁)
    (hL₁ : IsCompact (closure (K '' V₁))) {c : 𝕜} (hc_ne : c ≠ 0) :
    ∃ a : Finset E, ∀ x ∈ V₁, ∃ e ∈ (a : Set E), ∃ x' ∈ V₁, K x - (T + K) e = c • T x' := by
  have hW_open : IsOpen (c • (T '' V₁)) := (hT _ hV₁_open).smul₀ hc_ne
  have hW0 : (0 : F) ∈ c • (T '' V₁) := ⟨0, ⟨0, hV₁0, map_zero T⟩, smul_zero c⟩
  obtain ⟨W₁, hW₁, W₂, hW₂, hWadd⟩ := mem_nhds_prod_iff.mp <|
    continuous_add.continuousAt (x := ((0 : F), 0)) (by simpa using hW_open.mem_nhds hW0)
  let W' : Set F := interior (W₁ ∩ W₂)
  have hW'_open : IsOpen W' := isOpen_interior
  have hW'0 : (0 : F) ∈ W' := mem_interior_iff_mem_nhds.mpr (Filter.inter_mem hW₁ hW₂)
  obtain ⟨t, -, htfin, hcov⟩ := hL₁.elim_finite_subcover_image
    (fun y _ ↦ hW'_open.preimage (continuous_sub_right y))
    fun y hy ↦ Set.mem_biUnion hy (by simpa using hW'0)
  have happrox : ∀ y : F, ∃ e : E, y - (T + K) e ∈ W' := fun y ↦ by
    have hne := hdense.inter_open_nonempty _ (hW'_open.preimage (continuous_sub_left y))
      ⟨y, by simpa using hW'0⟩
    obtain ⟨_, he, ⟨e, rfl⟩⟩ := hne
    exact ⟨e, he⟩
  choose fe hfe using happrox
  classical
  refine ⟨htfin.toFinset.image fe, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcov (subset_closure ⟨x, hx, rfl⟩))
  have hsum : K x - (T + K) (fe y) ∈ c • (T '' V₁) := by
    have h1 : K x - y ∈ W₁ := (interior_subset hxy).1
    have h2 : y - (T + K) (fe y) ∈ W₂ := (interior_subset (hfe y)).2
    simpa [sub_add_sub_cancel] using hWadd (Set.mk_mem_prod h1 h2)
  obtain ⟨_, ⟨x', hx', rfl⟩, hcw⟩ := Set.mem_smul_set.mp hsum
  exact ⟨fe y, Finset.mem_coe.mpr (Finset.mem_image_of_mem fe (htfin.mem_toFinset.mpr hy)),
    x', hx', hcw.symm⟩

private theorem image_ball_subset_smul_closure {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
    [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [Module 𝕜 F] [ContinuousSMul 𝕜 F]
    (T K : E →L[𝕜] F) (p : Seminorm 𝕜 E) {c d : 𝕜} (hc1 : ‖c‖ < 1) {a : Finset E}
    (hL₁ : IsCompact (closure (K '' p.ball 0 1)))
    (hstep : ∀ x ∈ p.ball 0 1, ∃ e ∈ (a : Set E), ∃ x' ∈ p.ball 0 1, K x - (T + K) e = c • T x')
    (hd : (1 + ∑ e ∈ a, p e) / (1 - ‖c‖) + 1 < ‖d‖) :
    T '' p.ball 0 1 ⊆ d • closure ((T + K) '' p.ball 0 1) := by
  let R : ℝ := ∑ e ∈ a, p e
  have hR : 0 ≤ R := Finset.sum_nonneg fun e _ ↦ apply_nonneg p e
  have hd_pos : 0 < ‖d‖ := lt_of_le_of_lt (by positivity [sub_pos.mpr hc1]) hd
  have hd_ne : d ≠ 0 := norm_pos_iff.mp hd_pos
  rintro _ ⟨x₀, hx₀, rfl⟩
  obtain ⟨x, e, -, hxV, hea, hdecomp⟩ := iterate_decomp T K c (T + K) hstep hx₀
  have htend : Tendsto (fun n ↦ (-c) ^ n • K (x n)) atTop (𝓝 (0 : F)) :=
    (hL₁.isVonNBounded 𝕜).smul_tendsto_zero
      (Eventually.of_forall fun n ↦ subset_closure ⟨x n, hxV n, rfl⟩)
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by simpa using hc1))
  have hmem : ∀ n, T x₀ + (-c) ^ n • K (x n) ∈ d • ((T + K) '' p.ball 0 1) := fun n ↦ by
    let w : E := (∑ k ∈ Finset.range n, (-c) ^ k • (x k - e k)) + (-c) ^ n • x n
    have hTw : T x₀ + (-c) ^ n • K (x n) = (T + K) w := by
      rw [hdecomp n, sub_add_cancel]; simp [w, map_add, map_sum, map_smul, map_sub]
    have hpw : p w ≤ (1 + R) / (1 - ‖c‖) + 1 := seminorm_geom_sum_le p hc1 hR
      (fun k ↦ by simpa [Seminorm.mem_ball_zero] using hxV k)
      (fun k ↦ Finset.single_le_sum (fun u _ ↦ apply_nonneg p u) (Finset.mem_coe.mp (hea k))) n
    have hdw : d⁻¹ • w ∈ p.ball 0 1 := by
      rw [Seminorm.mem_ball_zero, map_smul_eq_mul, norm_inv]
      exact (inv_mul_lt_iff₀ hd_pos).mpr (by simpa using hpw.trans_lt hd)
    refine ⟨(T + K) (d⁻¹ • w), ⟨d⁻¹ • w, hdw, rfl⟩, ?_⟩
    dsimp only
    rw [← map_smul (T + K), smul_inv_smul₀ hd_ne, hTw]
  have hcl : T x₀ ∈ closure (d • ((T + K) '' p.ball 0 1)) :=
    mem_closure_of_tendsto (by simpa using htend.const_add (T x₀)) (Eventually.of_forall hmem)
  have heq : closure (d • ((T + K) '' p.ball 0 1)) = d • closure ((T + K) '' p.ball 0 1) :=
    ((Homeomorph.smulOfNeZero d hd_ne).image_closure ((T + K) '' p.ball 0 1)).symm
  exact heq ▸ hcl

private theorem closure_image_mem_nhds_of_denseRange {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] [PolynormableSpace 𝕜 E]
    [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [T0Space F]
    [Module 𝕜 F] [ContinuousSMul 𝕜 F]
    (T K : E →L[𝕜] F) (hT : IsOpenMap T) (hK : IsCompactOperator K)
    (hdense : Dense ((T + K).range : Set F)) {V : Set E} (hV : V ∈ 𝓝 (0 : E)) :
    closure ((T + K) '' V) ∈ 𝓝 (0 : F) := by
  obtain ⟨U, hU, hL⟩ := (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image K).mp hK
  obtain ⟨p, hp_cont, hp_sub⟩ :=
    (PolynormableSpace.hasBasis_zero_ball 𝕜 E).mem_iff.mp (Filter.inter_mem hV hU)
  have hV₁_open : IsOpen (p.ball 0 1) := by
    rw [Seminorm.ball_zero_eq]; exact isOpen_Iio.preimage hp_cont
  have hV₁0 : (0 : E) ∈ p.ball 0 1 := by simp
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one 𝕜
  have hL₁ : IsCompact (closure (K '' p.ball 0 1)) :=
    hL.of_isClosed_subset isClosed_closure
      (closure_mono (Set.image_mono (hp_sub.trans Set.inter_subset_right)))
  obtain ⟨a, hstep⟩ :=
    exists_approx_finset_of_denseRange T K hT hdense hV₁_open hV₁0 hL₁ (norm_pos_iff.mp hc0)
  have : 0 ≤ ∑ e ∈ a, p e := Finset.sum_nonneg fun e _ ↦ apply_nonneg p e
  obtain ⟨d, hd⟩ := NormedField.exists_lt_norm 𝕜 ((1 + ∑ e ∈ a, p e) / (1 - ‖c‖) + 1)
  have hd_ne : d ≠ 0 :=
    norm_pos_iff.mp <| lt_of_le_of_lt (by positivity [sub_pos.mpr hc1]) hd
  have hTV₁ := image_ball_subset_smul_closure T K p hc1 hL₁ hstep hd
  have hsub : d⁻¹ • (T '' p.ball 0 1) ⊆ closure ((T + K) '' V) := by
    calc d⁻¹ • (T '' p.ball 0 1)
        ⊆ d⁻¹ • (d • closure ((T + K) '' p.ball 0 1)) := Set.smul_set_mono hTV₁
      _ = closure ((T + K) '' p.ball 0 1) := by rw [smul_smul, inv_mul_cancel₀ hd_ne, one_smul]
      _ ⊆ closure ((T + K) '' V) :=
          closure_mono (Set.image_mono (hp_sub.trans Set.inter_subset_left))
  exact Filter.mem_of_superset
    (((hT _ hV₁_open).smul₀ (inv_ne_zero hd_ne)).mem_nhds
      ⟨0, ⟨0, hV₁0, map_zero T⟩, smul_zero _⟩) hsub

section DenseRange

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [Module 𝕜 E] [PolynormableSpace 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [T0Space F]
  [Module 𝕜 F] [ContinuousSMul 𝕜 F]

/-- A compact perturbation of an open continuous linear map with dense range is open.

Neither completeness of the scalar field `𝕜` nor `BaireSpace F` is required here. In particular,
`T + K` is also surjective by `LinearMap.surjective_of_isOpenMap`. -/
theorem isOpenMap_add_of_isOpenMap_of_isCompactOperator_of_denseRange
    (T K : E →L[𝕜] F) (hT : IsOpenMap T) (hK : IsCompactOperator K)
    (hdense : Dense ((T + K).range : Set F)) :
    IsOpenMap (T + K) :=
  TauCeti.isOpenMap_of_closure_image_mem_nhds (T + K) (T + K).continuous.continuousAt fun _ hV ↦
    closure_image_mem_nhds_of_denseRange T K hT hK hdense hV

end DenseRange

/-! ### Schwartz's finiteness theorem -/

section OpenMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [Module 𝕜 E] [PolynormableSpace 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [T0Space F]
  [Module 𝕜 F] [ContinuousSMul 𝕜 F]

/-- **Schwartz's theorem (open-map form, finite codimension).** If `T : E →L[𝕜] F` is an open
continuous linear map and `K : E →L[𝕜] F` is a compact operator, then `T + K` has
finite-dimensional cokernel (`(T + K).range.CoFG`). No `BaireSpace` or completeness hypothesis is
needed on `F`, and no hypothesis is imposed on `ker T`. -/
theorem cofg_range_add_of_isOpenMap_of_isCompactOperator
    (T K : E →L[𝕜] F) (hT : IsOpenMap T) (hK : IsCompactOperator K) :
    (T + K).range.CoFG := by
  obtain ⟨s, hdense⟩ := exists_finset_dense_sup_range_add T K hT hK
  let g : (s → 𝕜) →L[𝕜] F :=
    ⟨Fintype.linearCombination 𝕜 ((↑) : s → F), LinearMap.continuous_on_pi _⟩
  let T' : (E × (s → 𝕜)) →L[𝕜] F := T.coprod g
  let K' : (E × (s → 𝕜)) →L[𝕜] F := K.comp (fst 𝕜 E (s → 𝕜))
  have : (𝓝 (0 : s → 𝕜)).IsCountablyGenerated := by rw [nhds_pi]; infer_instance
  have : (𝓝 (0 : E × (s → 𝕜))).IsCountablyGenerated := by rw [nhds_prod_eq]; infer_instance
  have hT' : IsOpenMap T' := T.isOpenMap_coprod_of_left g hT
  have hK' : IsCompactOperator K' := hK.comp_clm (fst 𝕜 E (s → 𝕜))
  have hsum : T' + K' = (T + K).coprod g := by ext <;> simp [T', K']
  have hrange : (T' + K').range = (T + K).range ⊔ Submodule.span 𝕜 (s : Set F) := by
    rw [hsum]
    simpa [g, Fintype.range_linearCombination] using range_coprod (T + K) g
  have hopen : IsOpenMap (T' + K') :=
    isOpenMap_add_of_isOpenMap_of_isCompactOperator_of_denseRange T' K' hT' hK'
      (hrange.symm ▸ hdense)
  have hsurj : Function.Surjective (T' + K') :=
    (T' + K').toLinearMap.surjective_of_isOpenMap hopen
  have htop : (T + K).range ⊔ Submodule.span 𝕜 (s : Set F) = ⊤ :=
    hrange.symm.trans (LinearMap.range_eq_top.mpr hsurj)
  have hL :
      Function.Surjective ((T + K).range.mkQ.comp (Submodule.span 𝕜 (s : Set F)).subtype) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, Submodule.range_subtype]
    exact (Submodule.map_mkQ_eq_top _ _).mpr htop
  have : Module.Finite 𝕜 (Submodule.span 𝕜 (s : Set F)) :=
    Module.Finite.span_of_finite 𝕜 s.finite_toSet
  exact Module.Finite.of_surjective _ hL

private theorem exists_open_coprod_complement (T K : E →L[𝕜] F) (hT : IsOpenMap T)
    (hK : IsCompactOperator K) :
    ∃ (m : ℕ) (ψ : (Fin m → 𝕜) →L[𝕜] F),
      IsOpenMap ((T + K).coprod ψ) ∧
      Function.Surjective ((T + K).coprod ψ) ∧
      ∀ a, ψ a ∈ (T + K).range → a = 0 := by
  have : FiniteDimensional 𝕜 (F ⧸ (T + K).range) :=
    cofg_range_add_of_isOpenMap_of_isCompactOperator T K hT hK
  let b := Module.finBasis 𝕜 (F ⧸ (T + K).range)
  choose v hv using fun i ↦ (T + K).range.mkQ_surjective (b i)
  let ψ : (Fin (Module.finrank 𝕜 (F ⧸ (T + K).range)) → 𝕜) →L[𝕜] F :=
    ⟨Fintype.linearCombination 𝕜 v, LinearMap.continuous_on_pi _⟩
  let T' : (E × (Fin (Module.finrank 𝕜 (F ⧸ (T + K).range)) → 𝕜)) →L[𝕜] F := T.coprod ψ
  let K' : (E × (Fin (Module.finrank 𝕜 (F ⧸ (T + K).range)) → 𝕜)) →L[𝕜] F :=
    K.comp (fst 𝕜 E _)
  have : (𝓝 (0 : Fin (Module.finrank 𝕜 (F ⧸ (T + K).range)) → 𝕜)).IsCountablyGenerated := by
    rw [nhds_pi]; infer_instance
  have : (𝓝 (0 : E × (Fin (Module.finrank 𝕜 (F ⧸ (T + K).range)) → 𝕜))).IsCountablyGenerated := by
    rw [nhds_prod_eq]; infer_instance
  have hsum : T' + K' = (T + K).coprod ψ := by ext <;> simp [T', K']
  have hsurj : Function.Surjective ((T + K).coprod ψ) := by
    intro y
    let a : Fin (Module.finrank 𝕜 (F ⧸ (T + K).range)) → 𝕜 := b.repr ((T + K).range.mkQ y)
    have hmk : (T + K).range.mkQ (y - ψ a) = 0 := by
      rw [map_sub]
      have hψ : (T + K).range.mkQ (ψ a) = (T + K).range.mkQ y := by
        simp only [ψ, coe_mk', Fintype.linearCombination_apply, map_sum, map_smul, hv, a]
        exact b.sum_repr _
      rw [hψ, sub_self]
    obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero _).mp hmk
    exact ⟨(x, a), by rw [coprod_apply, ← ContinuousLinearMap.coe_coe, hx, sub_add_cancel]⟩
  have hdense : Dense ((T' + K').range : Set F) := fun y ↦ by
    rw [hsum]
    obtain ⟨p, rfl⟩ := hsurj y
    exact subset_closure ⟨p, rfl⟩
  have hopen : IsOpenMap ((T + K).coprod ψ) :=
    hsum ▸ isOpenMap_add_of_isOpenMap_of_isCompactOperator_of_denseRange T' K'
      (T.isOpenMap_coprod_of_left ψ hT) (hK.comp_clm (fst 𝕜 E _)) hdense
  refine ⟨_, ψ, hopen, hsurj, fun a ha ↦ ?_⟩
  have h0 : ∑ i, a i • b i = 0 := by
    have hmk : (T + K).range.mkQ (ψ a) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ha
    simpa only [ψ, coe_mk', Fintype.linearCombination_apply, map_sum, map_smul, hv] using hmk
  exact funext (Fintype.linearIndependent_iff.mp b.linearIndependent a h0)

/-- **Schwartz's theorem (open-map form, closed range).** If `T : E →L[𝕜] F` is an open continuous
linear map and `K : E →L[𝕜] F` is a compact operator, then `T + K` has closed range. No
`BaireSpace` or completeness hypothesis is needed on `F`. -/
theorem isClosed_range_add_of_isOpenMap_of_isCompactOperator
    (T K : E →L[𝕜] F) (hT : IsOpenMap T) (hK : IsCompactOperator K) :
    IsClosed ((T + K).range : Set F) := by
  obtain ⟨m, ψ, hopen, hsurj, hinj⟩ := exists_open_coprod_complement T K hT hK
  let Φ : (E × (Fin m → 𝕜)) →L[𝕜] F := (T + K).coprod ψ
  have hpre : Φ ⁻¹' ((T + K).range : Set F) = {p : E × (Fin m → 𝕜) | p.2 = 0} := by
    ext ⟨x, a⟩
    simp only [Set.mem_preimage, SetLike.mem_coe, Set.mem_ofPred_eq, Φ, coprod_apply]
    constructor
    · intro hmem
      exact hinj a (by simpa using (T + K).range.sub_mem hmem (LinearMap.mem_range_self _ x))
    · intro ha
      simp [ha]
  have hclosed : IsClosed (Φ ⁻¹' ((T + K).range : Set F)) := by
    rw [hpre]
    exact isClosed_eq continuous_snd continuous_const
  exact (hopen.isQuotientMap Φ.continuous hsurj).isClosed_preimage.mp hclosed

/-- **Schwartz's theorem (open-map form, strictness).** If `T : E →L[𝕜] F` is an open continuous
linear map and `K : E →L[𝕜] F` is a compact operator, then `T + K` is a strict morphism
(open onto its range). No `BaireSpace` or complete metrisability hypothesis is needed on `F`. -/
theorem isStrictMap_add_of_isOpenMap_of_isCompactOperator
    (T K : E →L[𝕜] F) (hT : IsOpenMap T) (hK : IsCompactOperator K) :
    Topology.IsStrictMap (T + K) := by
  obtain ⟨m, ψ, hopen, -, hinj⟩ := exists_open_coprod_complement T K hT hK
  let Φ : (E × (Fin m → 𝕜)) →L[𝕜] F := (T + K).coprod ψ
  refine LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict.mpr
    ⟨(T + K).toLinearMap.surjective_rangeRestrict, (T + K).continuous.subtype_mk _, fun U hU ↦ ?_⟩
  have hO : IsOpen (Φ '' (U ×ˢ Set.univ)) := hopen _ (hU.prod isOpen_univ)
  have heq : ((T + K).toLinearMap.rangeRestrict '' U) =
      ((↑) : (T + K).range → F) ⁻¹' (Φ '' (U ×ˢ Set.univ)) := by
    ext ⟨y, hy⟩
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, hxy⟩
      refine ⟨(x, 0), ⟨hx, trivial⟩, ?_⟩
      simpa [Φ] using congrArg Subtype.val hxy
    · rintro ⟨⟨x, a⟩, ⟨hx, -⟩, hxy⟩
      have ha : a = 0 := hinj a <| by
        have hψ : ψ a = y - (T + K) x := eq_sub_of_add_eq' hxy
        rw [hψ]
        exact (T + K).range.sub_mem hy (LinearMap.mem_range_self _ x)
      exact ⟨x, hx, Subtype.ext (by simpa [Φ, ha] using hxy)⟩
  rw [heq]
  exact hO.preimage continuous_subtype_val

end OpenMap

section Surjective

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [Module 𝕜 E] [PolynormableSpace 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [T0Space F] [BaireSpace F]
  [Module 𝕜 F] [ContinuousSMul 𝕜 F]

/-- **Schwartz's lemma.** A compact perturbation of a continuous linear surjection from a complete
first-countable polynormable space into a `T0` Baire topological vector space over a complete
nontrivially normed field has finite-dimensional cokernel, without any hypothesis on its kernel. -/
theorem cofg_range_add_of_surjective_of_isCompactOperator
    (T K : E →L[𝕜] F) (hT : Function.Surjective T) (hK : IsCompactOperator K) :
    (T + K).range.CoFG :=
  cofg_range_add_of_isOpenMap_of_isCompactOperator T K (T.isOpenMap_of_surjective hT) hK

/-- A compact perturbation of a continuous linear surjection from a complete first-countable
polynormable space into a `T0` Baire topological vector space over a complete nontrivially normed
field has closed range. -/
theorem isClosed_range_add_of_surjective_of_isCompactOperator
    (T K : E →L[𝕜] F) (hT : Function.Surjective T) (hK : IsCompactOperator K) :
    IsClosed ((T + K).range : Set F) :=
  isClosed_range_add_of_isOpenMap_of_isCompactOperator T K (T.isOpenMap_of_surjective hT) hK

/-- A compact perturbation of a continuous linear surjection from a complete first-countable
polynormable space into a `T0` Baire topological vector space over a complete nontrivially normed
field is strict (open onto its range). -/
theorem isStrictMap_add_of_surjective_of_isCompactOperator
    (T K : E →L[𝕜] F) (hT : Function.Surjective T) (hK : IsCompactOperator K) :
    Topology.IsStrictMap (T + K) :=
  isStrictMap_add_of_isOpenMap_of_isCompactOperator T K (T.isOpenMap_of_surjective hT) hK

end Surjective

end ContinuousLinearMap
