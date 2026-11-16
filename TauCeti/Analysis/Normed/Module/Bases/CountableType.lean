/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.Normed.Group.Quotient
public import TauCeti.Analysis.Normed.Module.Bases.TOrthogonal
public import TauCeti.Analysis.Normed.Module.RieszLemma
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# `t`-orthogonal bases and subspaces of normed spaces of countable type

Let `K` be a complete nontrivially normed field and `E` an ultrametric normed `K`-space. The space
`E` is *of countable type* if some sequence `v : ℕ → E` has dense span. Over a field whose value
group is not discrete, such a space need not have an orthogonal basis, but for every `t < 1` it
has a `t`-orthogonal one. This file constructs these bases by an approximate Gram–Schmidt process.

* `TauCeti.exists_isTOrthogonalFamily_span_image_Iio_eq`: every sequence `w : ℕ → E` can be
  replaced by a `t`-orthogonal sequence `e` with the same initial spans,
  `span (e '' Iio n) = span (w '' Iio n)`. The vector `e n` is `w n` minus an almost best
  approximation of `w n` in the span of the previous vectors (`TauCeti.riesz_lemma_translate`);
  the losses at the successive steps are chosen with product at least `t`.
* `TauCeti.exists_dual_of_notMem` and `TauCeti.exists_dual_of_linearIndependent`: separating a
  vector `x` outside a finite-dimensional subspace `D` (in particular, one member of a finite
  linearly independent family from the span of the remaining vectors) by a linear functional
  `φ : E →ₗ[K] K` with `φ x = 1`, `φ = 0` on `D`, and quantitative `t`-orthogonal norm control on
  any finite family of test vectors.
* `TauCeti.exists_isTOrthogonalBasis_of_dense_span`: a space of countable type has a
  `t`-orthogonal basis indexed by a set of natural numbers.
* `TauCeti.exists_basis_isTOrthogonalFamily`: a finite-dimensional space has a `t`-orthogonal
  basis in the sense of `Module.Basis`, indexed by `Fin (finrank K E)`.
* `TauCeti.exists_isTOrthogonalBasis_nat_of_dense_span`: an infinite-dimensional space of
  countable type has a `t`-orthogonal basis indexed by `ℕ`.
* `Submodule.exists_finiteDimensional_le_infDist_le`: for a closed subspace `D`, a
  finite-dimensional subspace `G` and `c > 1`, some finite-dimensional `W ≤ D` satisfies
  `infDist g W ≤ c * infDist g D` for every `g ∈ G`. The subspace `W` is cut out of `D` by lifts
  of a `t`-orthogonal basis of the image of `G` in `E ⧸ D`.
* `Submodule.exists_dense_span_of_dense_span`: every subspace of a space of countable type, closed
  or not, is of countable type. The approximation theorem is applied to the closed subspace
  `closure D`: the finite-dimensional subspaces `W ≤ closure D` attached to the initial spans of a
  densely spanning sequence together span a dense subspace of `closure D`, and each of their
  countably many spanning vectors is then replaced by a sequence in `D` converging to it.
* `TauCeti.separatingDual_of_dense_span` and `Submodule.separatingDual_span_of_countable`: the
  coordinate functionals of a `t`-orthogonal basis separate points on any ultrametric normed space
  of countable type, and in particular on the span of any countable set.

Neither a discrete valuation nor completeness of `E` is needed: only the finite-dimensional
subspaces spanned by initial segments have to be closed, which holds over a complete field.
The constant `c` in the approximation theorem does not depend on `G`; this uniformity is what
lets the subspaces `W` attached to the increasing initial spans together span a dense subspace of
the closure of `D`. Quotients of spaces of countable type are of countable type by
`DenseRange.dense_span_range_comp`, applied to the quotient map.
Together with `TauCeti.IsTOrthogonalBasis.toUnconditionalSchauderBasis`, these bases give the
coordinates in which Banach spaces of countable type are compared with `C₀(ℕ, K)`.

## References

* C. Perez-Garcia and W. H. Schikhof, *Locally Convex Spaces over Non-Archimedean Valued
  Fields*, Cambridge Studies in Advanced Mathematics 119, Cambridge University Press, 2010,
  Chapter 2.
-/

public section

open Set Submodule Metric Filter
open scoped NNReal

namespace TauCeti

variable {K E : Type*} [NontriviallyNormedField K] [NormedAddCommGroup E] [NormedSpace K E]

variable [CompleteSpace K] [IsUltrametricDist E]

/-- **Approximate Gram–Schmidt process**: over a complete nontrivially normed field, every sequence
`w` in an ultrametric normed space can be replaced, for each `t < 1`, by a `t`-orthogonal sequence
`e` with the same initial spans: `span K (e '' Iio n) = span K (w '' Iio n)` for every `n`. -/
theorem exists_isTOrthogonalFamily_span_image_Iio_eq (w : ℕ → E) {t : ℝ≥0} (ht : t < 1) :
    ∃ e : ℕ → E, IsTOrthogonalFamily K t e ∧
      ∀ n, span K (e '' Iio n) = span K (w '' Iio n) := by
  -- Orthogonality constants of the successive initial segments: a strictly decreasing sequence
  -- in `(t, 1)`.
  obtain ⟨T, hT, hTt, -⟩ := exists_seq_strictAnti_tendsto' ht
  have hT' (n : ℕ) : 0 < T n ∧ t ≤ T n ∧ T n ≤ 1 :=
    ⟨zero_le.trans_lt (hTt n).1, (hTt n).1.le, (hTt n).2.le⟩
  -- The initial spans `span K (w '' Iio n)` are finite-dimensional, hence closed.
  have hF (n : ℕ) : IsClosed (span K (w '' Iio n) : Set E) :=
    have := FiniteDimensional.span_of_finite K ((finite_Iio n).image w)
    (span K (w '' Iio n)).isClosed_of_finiteDimensional
  -- Subtract from `w n` an almost best approximation `y n` in the previous span, with loss
  -- `T (n + 1) / T n < 1`.
  have hr (n : ℕ) : ((T (n + 1) / T n : ℝ≥0) : ℝ) < 1 := by
    exact_mod_cast (div_lt_one (hT' n).1).2 (hT n.lt_succ_self)
  choose y hyF hy using fun n ↦ riesz_lemma_translate (hF n) (w n) (hr n)
  set e : ℕ → E := fun n ↦ w n - y n
  have hspan (n : ℕ) : span K (e '' Iio n) = span K (w '' Iio n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← Order.succ_eq_add_one, Order.Iio_succ_eq_insert, image_insert_eq, image_insert_eq,
        span_insert, span_insert, ih]
      refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)
      · exact span_singleton_le_iff_mem _ _ |>.2 <|
          sub_mem (mem_sup_left (mem_span_singleton_self _)) (mem_sup_right (hyF n))
      · rw [span_singleton_le_iff_mem, ← sub_add_cancel (w n) (y n)]
        exact add_mem (mem_sup_left (mem_span_singleton_self _)) (mem_sup_right (hyF n))
  -- Each `e n` is `T (n + 1) / T n`-orthogonal to the previous vectors, so for every `N` the
  -- vectors `e i` with `i < N` are `T N`-orthogonal, and `t ≤ T N`.
  have key := isTOrthogonalFamily_Iio_of_mul_nnnorm_le_nnnorm_sub (K := K) hT.antitone
    (fun n ↦ ⟨(hT' n).1, (hT' n).2.2⟩) fun N z hz ↦ by
      rw [hspan] at hz
      exact_mod_cast hy N z hz
  refine ⟨e, isTOrthogonalFamily_def.2 fun s a ↦ ?_, hspan⟩
  have hs (i : ℕ) (hi : i ∈ s) : i ∈ Iio (s.sup id + 1) :=
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  rw [← Finset.subtype_map_of_mem hs, Finset.sup_map, Finset.sum_map]
  exact (mul_le_mul_of_nonneg_right (hT' _).2.1 zero_le).trans
    (isTOrthogonalFamily_def.1 (key _) _ fun i ↦ a i)

/-- **`t`-orthogonal bases of spaces of countable type**: over a complete nontrivially normed
field, if a sequence `v` has dense span in an ultrametric normed space `E`, then for every `t < 1`
the space `E` has a `t`-orthogonal basis indexed by a set of natural numbers. -/
theorem exists_isTOrthogonalBasis_of_dense_span {v : ℕ → E}
    (hv : Dense (span K (range v) : Set E)) {t : ℝ≥0} (ht : t < 1) :
    ∃ (S : Set ℕ) (e : S → E), IsTOrthogonalBasis K t e := by
  obtain ⟨e, he, hspan⟩ := exists_isTOrthogonalFamily_span_image_Iio_eq (K := K) v ht
  -- Discard the zero vectors of `e`; they do not change its span.
  refine ⟨{n | e n ≠ 0}, fun n ↦ e n, he.comp Subtype.val_injective, fun n ↦ n.2, ?_⟩
  have hrange : range e ⊆ insert 0 (range fun n : {n | e n ≠ 0} ↦ e n) := by
    rintro _ ⟨n, rfl⟩
    by_cases h : e n = 0
    · exact Or.inl h
    · exact Or.inr ⟨⟨n, h⟩, rfl⟩
  -- Equal initial spans give equal spans, as `range` is the union of the initial segments.
  have hspan' : span K (range e) = span K (range v) := by
    simp only [← image_univ, ← iUnion_Iio, image_iUnion, span_iUnion, hspan]
  have : span K (range fun n : {n | e n ≠ 0} ↦ e n) = span K (range v) := by
    refine le_antisymm ((span_mono ?_).trans hspan'.le) ?_
    · rintro _ ⟨n, rfl⟩
      exact ⟨n, rfl⟩
    · calc span K (range v) = span K (range e) := hspan'.symm
        _ ≤ span K (insert 0 (range fun n : {n | e n ≠ 0} ↦ e n)) := span_mono hrange
        _ = _ := span_insert_zero
  rw [this]
  exact hv

/-- **`t`-orthogonal bases of finite-dimensional spaces**: over a complete nontrivially normed
field, a finite-dimensional ultrametric normed space has, for every `t < 1`, a basis indexed by
`Fin (finrank K E)` which is a `t`-orthogonal family. -/
theorem exists_basis_isTOrthogonalFamily [FiniteDimensional K E] {t : ℝ≥0} (ht : t < 1) :
    ∃ b : Module.Basis (Fin (Module.finrank K E)) K E, IsTOrthogonalFamily K t b := by
  set d := Module.finrank K E
  let b₀ := Module.finBasis K E
  -- Run the Gram–Schmidt process on `b₀`, extended by zero to a sequence.
  let w : ℕ → E := fun n ↦ if h : n < d then b₀ ⟨n, h⟩ else 0
  obtain ⟨e, he, hspan⟩ := exists_isTOrthogonalFamily_span_image_Iio_eq (K := K) w ht
  have htop : ⊤ ≤ span K (range fun i : Fin d ↦ e i) :=
    calc ⊤ = span K (range b₀) := b₀.span_eq.symm
      _ ≤ span K (w '' Iio d) :=
        span_mono <| range_subset_iff.2 fun i ↦ ⟨i, i.2, by simp [w, d, i.isLt]⟩
      _ = span K (e '' Iio d) := (hspan d).symm
      _ ≤ span K (range fun i : Fin d ↦ e i) := span_mono <| by
        rintro _ ⟨n, hn, rfl⟩
        exact ⟨⟨n, hn⟩, rfl⟩
  refine ⟨basisOfTopLeSpanOfCardEqFinrank (fun i : Fin d ↦ e i) htop (Fintype.card_fin d), ?_⟩
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]
  exact he.comp Fin.val_injective

/-- **`t`-orthogonal bases of infinite-dimensional spaces of countable type**: over a complete
nontrivially normed field, if a sequence has dense span in an infinite-dimensional ultrametric
normed space `E`, then for every `t < 1` the space `E` has a `t`-orthogonal basis indexed by `ℕ`. -/
theorem exists_isTOrthogonalBasis_nat_of_dense_span (hE : ¬FiniteDimensional K E) {v : ℕ → E}
    (hv : Dense (span K (range v) : Set E)) {t : ℝ≥0} (ht : t < 1) :
    ∃ e : ℕ → E, IsTOrthogonalBasis K t e := by
  obtain ⟨S, e, he⟩ := exists_isTOrthogonalBasis_of_dense_span hv ht
  -- A finite basis would span a closed, hence everything, finite-dimensional subspace.
  have : Infinite S := by
    refine not_finite_iff_infinite.1 fun hS ↦ hE ?_
    have := FiniteDimensional.span_of_finite K (finite_range e)
    have htop : span K (range e) = ⊤ := eq_top_iff'.2 fun x ↦
      (span K (range e)).isClosed_of_finiteDimensional.closure_subset (he.dense_span x)
    exact Module.finite_def.2 (htop ▸ fg_span (finite_range e))
  obtain ⟨σ⟩ : Nonempty (ℕ ≃ S) := nonempty_equiv_of_countable
  exact ⟨e ∘ σ, he.comp_equiv σ⟩

/-- **Relative approximation by finite-dimensional subspaces**: let `D` be a closed subspace and
`G` a finite-dimensional subspace of an ultrametric normed space over a complete nontrivially
normed field. For every `c > 1` there is a finite-dimensional subspace `W ≤ D` such that every
`g ∈ G` is within `c * infDist g D` of `W`. -/
theorem _root_.Submodule.exists_finiteDimensional_le_infDist_le (D G : Submodule K E)
    (hD : IsClosed (D : Set E)) [FiniteDimensional K G] {c : ℝ} (hc : 1 < c) :
    ∃ W : Submodule K E, W ≤ D ∧ FiniteDimensional K W ∧
      ∀ g ∈ G, infDist g W ≤ c * infDist g D := by
  -- A `t`-orthogonal basis `b` of the image of `G` in the normed quotient `E ⧸ D`, for some
  -- `c⁻¹ < t < 1`.
  obtain ⟨t, hct, ht⟩ : ∃ t : ℝ≥0, (c⁻¹ : ℝ) < t ∧ t < 1 := by
    obtain ⟨t, h₁, h₂⟩ := exists_between (inv_lt_one_of_one_lt₀ hc)
    exact ⟨⟨t, (inv_pos.2 (one_pos.trans hc)).le.trans h₁.le⟩, h₁, by exact_mod_cast h₂⟩
  have hct' : 1 < c * t := by
    rw [inv_lt_iff_one_lt_mul₀ (one_pos.trans hc)] at hct
    linarith
  obtain ⟨b, hb⟩ := exists_basis_isTOrthogonalFamily (K := K) (E := G.map D.mkQ) ht
  -- Lift each `b i` to a vector `y i` of norm at most `c * t * ‖b i‖`.
  have hlift (i : Fin (Module.finrank K (G.map D.mkQ))) :
      ∃ y : E, D.mkQ y = b i ∧ ‖y‖ ≤ c * t * ‖b i‖ := by
    have hpos : 0 < ‖b i‖ := norm_pos_iff.2 (b.ne_zero i)
    obtain ⟨y, hy, hny⟩ := Submodule.Quotient.norm_mk_lt (b i : E ⧸ D)
      (mul_pos (sub_pos.2 hct') hpos)
    refine ⟨y, hy, ?_⟩
    rw [norm_coe] at hny
    linarith
  choose y hy hny using hlift
  refine ⟨D ⊓ (G ⊔ span K (range y)), inf_le_left, ?_, fun g hg ↦ ?_⟩
  · have := FiniteDimensional.span_of_finite K (finite_range y)
    exact Submodule.finiteDimensional_inf_right _ _
  -- Expand the class `x` of `g` in the basis `b`; subtracting the same combination of the lifts
  -- from `g` gives a point of `W = D ⊓ (G ⊔ span K (range y))`.
  obtain ⟨x, hxg⟩ : ∃ x : G.map D.mkQ, (x : E ⧸ D) = D.mkQ g :=
    ⟨⟨D.mkQ g, mem_map_of_mem hg⟩, rfl⟩
  set a := b.repr x
  have hx : D.mkQ g = ∑ i, a i • (b i : E ⧸ D) := by
    rw [← hxg, ← b.sum_repr x, Submodule.coe_sum]
    simp only [Submodule.coe_smul, a]
  have hmem : g - ∑ i, a i • y i ∈ D ⊓ (G ⊔ span K (range y)) := by
    refine ⟨?_, sub_mem (mem_sup_left hg) (mem_sup_right
      (sum_mem fun i _ ↦ smul_mem _ _ (subset_span (mem_range_self i))))⟩
    rw [SetLike.mem_coe, ← Submodule.Quotient.mk_eq_zero, ← mkQ_apply, map_sub, map_sum]
    simp only [map_smul, hy, hx, sub_self]
  -- `E ⧸ D` is the quotient group by `D.toAddSubgroup`, carrying its quotient norm.
  have hnorm : ‖D.mkQ g‖ = infDist g D := QuotientAddGroup.norm_mk (S := D.toAddSubgroup) g
  -- By the ultrametric inequality and `t`-orthogonality, the combination of the lifts has norm
  -- at most `c * ‖x‖`.
  calc infDist g (D ⊓ (G ⊔ span K (range y)) : Submodule K E)
      ≤ dist g (g - ∑ i, a i • y i) := infDist_le_dist_of_mem hmem
    _ = ‖∑ i, a i • y i‖ := by rw [dist_eq_norm, sub_sub_cancel]
    _ ≤ c * ‖x‖ := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
        (mul_nonneg (one_pos.trans hc).le (norm_nonneg _)) fun i _ ↦ ?_
      have h := hb.mul_norm_smul_le (Finset.mem_univ i) a
      rw [b.sum_repr, norm_smul] at h
      rw [norm_smul]
      calc ‖a i‖ * ‖y i‖ ≤ ‖a i‖ * (c * t * ‖b i‖) := by gcongr; exact hny i
        _ = c * (t * (‖a i‖ * ‖b i‖)) := by ring
        _ ≤ c * ‖x‖ := by gcongr
    _ = c * infDist g D := by rw [← norm_coe, hxg, hnorm]

/-- A closed subspace of a space of countable type is the closure of the span of a countable
subset of it. -/
private theorem exists_countable_subset_closure_span_of_isClosed {v : ℕ → E}
    (hv : Dense (span K (range v) : Set E)) {D : Submodule K E} (hD : IsClosed (D : Set E)) :
    ∃ S : Set E, S.Countable ∧ S ⊆ D ∧ (D : Set E) ⊆ closure (span K S) := by
  -- For each initial span `G n` of `v`, a finite-dimensional `W n ≤ D` approximating the points
  -- of `G n` as well as `D` does, up to the factor `2`; `s n` is a finite spanning set of `W n`.
  set G : ℕ → Submodule K E := fun n ↦ span K (v '' Iio n)
  have (n : ℕ) : FiniteDimensional K (G n) :=
    FiniteDimensional.span_of_finite K ((finite_Iio n).image v)
  choose W hWD hWfin hW using fun n ↦ D.exists_finiteDimensional_le_infDist_le (G n) hD one_lt_two
  choose s hs using fun n ↦ (fg_iff_finiteDimensional (W n)).2 (hWfin n)
  have hsW (n : ℕ) : (s n : Set E) ⊆ span K (⋃ n, (s n : Set E)) :=
    subset_span.trans' (subset_iUnion (fun n ↦ (s n : Set E)) n)
  refine ⟨⋃ n, (s n : Set E), countable_iUnion fun n ↦ (s n).countable_toSet,
    iUnion_subset fun n ↦ fun x hx ↦ hWD n (hs n ▸ subset_span hx), fun d hd ↦ ?_⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  -- Approximate `d` by a point `g` of some `G n`, then `g` by a point of `W n`.
  obtain ⟨g, hg, hdg⟩ := Metric.mem_closure_iff.1 (hv d) (ε / 3) (by positivity)
  have hGmono : Monotone G := fun m n hmn ↦ span_mono (image_mono (Iio_subset_Iio hmn))
  have hrange : span K (range v) = ⨆ n, G n := by
    simp only [G, ← image_univ, ← iUnion_Iio, image_iUnion, span_iUnion]
  rw [SetLike.mem_coe, hrange, mem_iSup_of_directed _ hGmono.directed_le] at hg
  obtain ⟨n, hgn⟩ := hg
  have hgW : infDist g (W n) < 2 * (ε / 3) :=
    (hW n g hgn).trans_lt (by
      gcongr
      exact (infDist_le_dist_of_mem hd).trans_lt (by rwa [dist_comm]))
  obtain ⟨w, hw, hgw⟩ := (infDist_lt_iff ⟨0, (W n).zero_mem⟩).1 hgW
  refine ⟨w, ?_, ?_⟩
  · rw [← hs n] at hw
    exact span_le.2 (hsW n) hw
  · calc dist d w ≤ dist d g + dist g w := dist_triangle _ _ _
      _ < ε / 3 + 2 * (ε / 3) := add_lt_add hdg hgw
      _ = ε := by ring

/-- **Subspaces of spaces of countable type**: over a complete nontrivially normed field, if a
sequence has dense span in an ultrametric normed space `E`, then every subspace `D` of `E`, closed
or not, is of countable type: some sequence in `D` has dense span in `D`. -/
theorem _root_.Submodule.exists_dense_span_of_dense_span (D : Submodule K E) {v : ℕ → E}
    (hv : Dense (span K (range v) : Set E)) :
    ∃ w : ℕ → D, Dense (span K (range w) : Set D) := by
  obtain ⟨S, hS, hSD, hDS⟩ :=
    exists_countable_subset_closure_span_of_isClosed hv D.isClosed_topologicalClosure
  -- Replace each point of `S ⊆ closure D` by a sequence in `D` converging to it.
  choose! u hu hlim using fun x (hx : x ∈ S) ↦ mem_closure_iff_seq_limit.1 (hSD hx)
  set T : Set E := insert 0 (⋃ x ∈ S, range (u x))
  have hTD : T ⊆ D :=
    insert_subset D.zero_mem (iUnion₂_subset fun x hx ↦ range_subset_iff.2 (hu x hx))
  have hST : S ⊆ (span K T).topologicalClosure := fun x hx ↦
    mem_closure_of_tendsto (hlim x hx) (Eventually.of_forall fun n ↦
      subset_span (mem_insert_of_mem _ (mem_biUnion hx (mem_range_self n))))
  have hDT : (D : Set E) ⊆ closure (span K T) :=
    calc (D : Set E) ⊆ D.topologicalClosure := D.le_topologicalClosure
      _ ⊆ closure (span K S) := hDS
      _ ⊆ closure (span K T) :=
        closure_minimal (span_le.2 hST) (span K T).isClosed_topologicalClosure
  -- Enumerate the countable set `T ⊆ D`.
  obtain ⟨f, hf⟩ : ∃ f : ℕ → E, T = range f :=
    ((hS.biUnion fun x _ ↦ countable_range (u x)).insert 0).exists_eq_range (insert_nonempty _ _)
  have hfD (n : ℕ) : f n ∈ D := hTD (hf ▸ mem_range_self n)
  let w : ℕ → D := fun n ↦ ⟨f n, hfD n⟩
  have hspan : ((↑) '' (span K (range w) : Set D) : Set E) = span K T := by
    -- `D.subtype ∘ w` is `f` by the definition of `w`.
    rw [hf, ← D.coe_subtype, ← Submodule.map_coe, Submodule.map_span, ← range_comp]
    rfl
  exact ⟨w, Subtype.dense_iff.2 (hspan ▸ hDT)⟩

/-- **Continuous linear functionals separate points on spaces of countable type**: over a complete
nontrivially normed field, if a sequence has dense span in an ultrametric normed space `E`, then
`StrongDual K E` separates points of `E`, without assuming completeness of `E` or spherical
completeness of `K`. -/
theorem separatingDual_of_dense_span {v : ℕ → E}
    (hv : Dense (span K (range v) : Set E)) : SeparatingDual K E where
  exists_ne_zero' {x} hx := by
    have ht : (2⁻¹ : ℝ≥0) < 1 := by norm_num
    obtain ⟨S, e, he⟩ := exists_isTOrthogonalBasis_of_dense_span hv ht
    let b := he.toUnconditionalSchauderBasis (by norm_num)
    by_contra! h
    have hsum := b.expansion x
    simp only [h, zero_smul] at hsum
    exact hx (hsum.unique hasSum_zero)

/-- Continuous linear functionals separate points on the span of any countable set in an
ultrametric normed space over a complete nontrivially normed field. -/
theorem _root_.Submodule.separatingDual_span_of_countable {S : Set E} (hS : S.Countable) :
    SeparatingDual K (span K S) := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → E, insert 0 S = range f :=
    (hS.insert 0).exists_eq_range (insert_nonempty _ _)
  have hfS (n : ℕ) : f n ∈ span K S := by
    have : f n ∈ insert (0 : E) S := hf ▸ mem_range_self n
    rcases mem_insert_iff.mp this with h0 | hn
    · rw [h0]
      exact zero_mem _
    · exact subset_span hn
  let v : ℕ → span K S := fun n ↦ ⟨f n, hfS n⟩
  have hv : (span K S).subtype ∘ v = f := by
    ext n
    exact (span K S).subtype_apply (v n)
  have htop : span K (range v) = ⊤ := by
    apply Submodule.map_injective_of_injective (span K S).injective_subtype
    rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span, ← range_comp, hv, ← hf,
      span_insert_zero]
  refine separatingDual_of_dense_span (v := v) ?_
  rw [htop]
  exact dense_univ

omit [CompleteSpace K] [IsUltrametricDist E] in
/-- Coordinate functional of a finite `t`-orthogonal family of nonzero vectors, extended to all of
`E` along a linear retraction onto `span K (range e')`. -/
private theorem exists_coord_of_isTOrthogonalFamily {S : Type*} [Finite S] [DecidableEq S]
    {e' : S → E} {t : ℝ≥0} (he' : IsTOrthogonalFamily K t e') (ht0 : 0 < t)
    (he_ne : ∀ i, e' i ≠ 0) (rIdx : S) :
    ∃ ψ : E →ₗ[K] K,
      (∀ i : S, ψ (e' i) = if i = rIdx then 1 else 0) ∧
      ∀ u ∈ span K (range e'), (t : ℝ) * ‖ψ u‖ * ‖e' rIdx‖ ≤ ‖u‖ := by
  cases nonempty_fintype S
  have hli : LinearIndependent K e' := he'.linearIndependent ht0 he_ne
  let E_S : Submodule K E := span K (range e')
  let bS : Module.Basis S K E_S := Module.Basis.span hli
  obtain ⟨π, hπ⟩ := E_S.subtype.exists_leftInverse_of_injective E_S.ker_subtype
  refine ⟨(bS.coord rIdx).comp π, fun i ↦ ?_, fun u hu ↦ ?_⟩
  · have hπi : π (e' i) = ⟨e' i, subset_span ⟨i, rfl⟩⟩ :=
      LinearMap.congr_fun hπ ⟨e' i, subset_span ⟨i, rfl⟩⟩
    rw [LinearMap.comp_apply, hπi, (Module.Basis.span_apply hli i).symm, Module.Basis.coord_apply,
      bS.repr_self, Finsupp.single_apply]
  · let u' : E_S := ⟨u, hu⟩
    have hπu : π u = u' := LinearMap.congr_fun hπ u'
    have hbS (i : S) : ((bS i : E_S) : E) = e' i :=
      congrArg Subtype.val (Module.Basis.span_apply hli i)
    have hexp : ∑ i : S, bS.repr u' i • e' i = u := by
      simpa only [map_sum, map_smul, Submodule.coe_subtype, hbS] using
        congrArg (E_S.subtype : E_S →ₗ[K] E) (bS.sum_repr u')
    have horth := he'.mul_norm_smul_le (Finset.mem_univ rIdx) (fun i ↦ bS.repr u' i)
    rwa [hexp, norm_smul, ← mul_assoc, ← Module.Basis.coord_apply, ← hπu] at horth

/-- Approximate Gram–Schmidt step on a basis of a finite-dimensional subspace `D`, followed by
`x ∉ D` and a finite family `y : Fin m → E`: the `(finrank K D)`-th orthogonalized vector separates
`x` from `D` while the first `finrank K D + 1 + m` vectors span all `y k`. -/
private theorem exists_isTOrthogonalFamily_of_notMem {D : Submodule K E} [FiniteDimensional K D]
    {x : E} (hx : x ∉ D) {m : ℕ} (y : Fin m → E) {t : ℝ≥0} (ht1 : t < 1) :
    ∃ (e : ℕ → E) (α : K) (d : E),
      IsTOrthogonalFamily K t e ∧
      α ≠ 0 ∧ e (Module.finrank K D) ≠ 0 ∧
      d ∈ D ∧ α • e (Module.finrank K D) + d = x ∧
      infDist x D ≤ ‖α • e (Module.finrank K D)‖ ∧
      span K (e '' Iio (Module.finrank K D)) = D ∧
      ∀ k : Fin m, y k ∈ span K (e '' Iio (Module.finrank K D + 1 + m)) := by
  classical
  set r := Module.finrank K D
  let bD := Module.finBasis K D
  let z : ℕ → E := fun n ↦
    if h₁ : n < r then (bD ⟨n, h₁⟩ : E)
    else if _ : n = r then x
    else if _ : n < r + 1 + m then y ⟨n - (r + 1), by omega⟩
    else 0
  obtain ⟨e, he, hspan⟩ := exists_isTOrthogonalFamily_span_image_Iio_eq (K := K) z ht1
  have hzD : span K (z '' Iio r) = D := by
    have himg : z '' Iio r = range (fun i : Fin r ↦ (bD i : E)) := by
      ext u
      exact ⟨fun ⟨n, hn, hu⟩ ↦ ⟨⟨n, hn⟩, by simpa [z, mem_Iio.mp hn] using hu⟩,
        fun ⟨i, hi⟩ ↦ ⟨i.1, i.2, by simpa [z, i.2] using hi⟩⟩
    rw [himg, show (fun i : Fin r ↦ (bD i : E)) = D.subtype ∘ bD from rfl, range_comp,
      ← Submodule.map_span, bD.span_eq, Submodule.map_top, Submodule.range_subtype]
  have heD : span K (e '' Iio r) = D := (hspan r).trans hzD
  -- `x = z r` lies in `span (e '' Iio (r + 1)) = (K ∙ e r) ⊔ D`, with nonzero `e r` component.
  have hx_mem : x ∈ (K ∙ e r) ⊔ D := by
    have hz_mem : z r ∈ span K (z '' Iio (r + 1)) := subset_span ⟨r, Nat.lt_succ_self r, rfl⟩
    rw [← hspan (r + 1), ← Order.succ_eq_add_one, Order.Iio_succ_eq_insert, image_insert_eq,
      span_insert, heD] at hz_mem
    simpa [z] using hz_mem
  obtain ⟨u₁, hu₁, d, hd, hud⟩ := Submodule.mem_sup.mp hx_mem
  obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp hu₁
  have hαer_ne : α • e r ≠ 0 := fun h0 ↦ hx ((zero_add d ▸ h0 ▸ hud) ▸ hd)
  have hdist : infDist x D ≤ ‖α • e r‖ :=
    (infDist_le_dist_of_mem hd).trans_eq (by rw [dist_eq_norm, ← hud, add_sub_cancel_right])
  refine ⟨e, α, d, he, left_ne_zero_of_smul hαer_ne, right_ne_zero_of_smul hαer_ne,
    hd, hud, hdist, heD, fun k ↦ ?_⟩
  rw [hspan (r + 1 + m)]
  refine subset_span ⟨r + 1 + k.1, mem_Iio.mpr (by omega), ?_⟩
  have h1 : ¬ (r + 1 + k.1 < r) := by omega
  have h2 : r + 1 + k.1 ≠ r := by omega
  have h3 : r + 1 + k.1 < r + 1 + m := by omega
  simp [z, h1, h2, h3]

/-- **Finite-dimensional Gram–Schmidt dual separation**: over a complete nontrivially normed field
`K`, given a finite-dimensional subspace `D` of an ultrametric normed `K`-space `E`, a vector
`x ∉ D`, a finite family `y : ι → E`, and `0 < t < 1`, there exist `c > 0` with `infDist x D ≤ c`
and a linear functional `φ : E →ₗ[K] K` vanishing on `D`, sending `x` to `1`, and satisfying
`t * ‖φ (y k)‖ * c ≤ ‖y k‖` for every `k`. -/
theorem exists_dual_of_notMem {D : Submodule K E} [FiniteDimensional K D] {x : E} (hx : x ∉ D)
    {ι : Type*} [Finite ι] (y : ι → E) {t : ℝ≥0} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ (c : ℝ) (φ : E →ₗ[K] K),
      0 < c ∧
      infDist x D ≤ c ∧
      φ x = 1 ∧
      (∀ u ∈ D, φ u = 0) ∧
      ∀ k : ι, (t : ℝ) * ‖φ (y k)‖ * c ≤ ‖y k‖ := by
  classical
  cases nonempty_fintype ι
  let σ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  obtain ⟨e, α, d, he, hα_ne, her_ne, hd, hud, hdist, heD, hy_mem⟩ :=
    exists_isTOrthogonalFamily_of_notMem hx (y ∘ σ) ht1
  set r := Module.finrank K D
  -- Build the coordinate functional `ψ` at index `r` on the nonzero vectors of `e`, then scale.
  let S := {i : Fin (r + 1 + Fintype.card ι) // e i ≠ 0}
  let e' : S → E := fun i ↦ e i.1.1
  let rIdx : S := ⟨⟨r, by omega⟩, her_ne⟩
  obtain ⟨ψ, hψ_e', hψ_bound⟩ := exists_coord_of_isTOrthogonalFamily (e' := e')
    (he.comp (Fin.val_injective.comp Subtype.val_injective)) ht0 (fun i ↦ i.2) rIdx
  let φ : E →ₗ[K] K := α⁻¹ • ψ
  have hφ_D {u : E} (hu : u ∈ D) : φ u = 0 := by
    rw [← heD] at hu
    refine Submodule.span_induction (p := fun u _ ↦ φ u = 0) ?_ (map_zero φ)
      (fun a b _ _ ha hb ↦ by rw [map_add, ha, hb, add_zero])
      (fun c a _ ha ↦ by rw [map_smul, ha, smul_eq_mul, mul_zero]) hu
    rintro _ ⟨n, hn, rfl⟩
    have hn' : n < r + 1 + Fintype.card ι := (mem_Iio.mp hn).trans (by omega)
    by_cases h0 : e n = 0
    · simp [h0]
    · have hne : (⟨⟨n, hn'⟩, h0⟩ : S) ≠ rIdx :=
        fun h ↦ (mem_Iio.mp hn).ne (congrArg (fun s : S ↦ s.1.1) h)
      have hψ_n : ψ (e n) = 0 := by simpa [e', hne] using hψ_e' ⟨⟨n, hn'⟩, h0⟩
      simp [φ, hψ_n]
  have hφ_x : φ x = 1 := by
    have hψ_er : ψ (e r) = 1 := by simpa [e', rIdx] using hψ_e' rIdx
    rw [← hud, map_add, map_smul, hφ_D hd, add_zero]
    simp [φ, hψ_er, mul_inv_cancel₀ hα_ne]
  refine ⟨‖α • e r‖, φ, norm_pos_iff.mpr (smul_ne_zero hα_ne her_ne), hdist, hφ_x,
    fun _ hu ↦ hφ_D hu, fun k ↦ ?_⟩
  have hy_S : y k ∈ span K (range e') := by
    have hk : y (σ (σ.symm k)) ∈ span K (e '' Iio (r + 1 + Fintype.card ι)) := hy_mem (σ.symm k)
    rw [σ.apply_symm_apply] at hk
    refine span_le.mpr ?_ hk
    rintro _ ⟨n, hn, rfl⟩
    have hn' : n < r + 1 + Fintype.card ι := mem_Iio.mp hn
    by_cases h0 : e n = 0
    · simp [h0]
    · exact subset_span ⟨⟨⟨n, hn'⟩, h0⟩, rfl⟩
  calc (t : ℝ) * ‖φ (y k)‖ * ‖α • e r‖
      = (t : ℝ) * (‖α‖⁻¹ * ‖ψ (y k)‖) * (‖α‖ * ‖e' rIdx‖) := by
          simp [φ, e', rIdx, norm_smul]
    _ = (t : ℝ) * ‖ψ (y k)‖ * ‖e' rIdx‖ := by
          have hα0 : ‖α‖ ≠ 0 := norm_ne_zero_iff.mpr hα_ne
          calc (t : ℝ) * (‖α‖⁻¹ * ‖ψ (y k)‖) * (‖α‖ * ‖e' rIdx‖)
              = (‖α‖⁻¹ * ‖α‖) * ((t : ℝ) * ‖ψ (y k)‖ * ‖e' rIdx‖) := by ring
            _ = (t : ℝ) * ‖ψ (y k)‖ * ‖e' rIdx‖ := by rw [inv_mul_cancel₀ hα0, one_mul]
    _ ≤ ‖y k‖ := hψ_bound (y k) hy_S

/-- **Gram–Schmidt coordinate functional**: over a complete nontrivially normed field `K`, given a
finite linearly independent family `w : ι → E` in an ultrametric normed `K`-space `E`, an index
`i₀ : ι`, a finite family `y : κ → E`, and `0 < t < 1`, there exist `c > 0` with
`infDist (w i₀) (span K (w '' (univ \ {i₀}))) ≤ c` and a linear functional `φ : E →ₗ[K] K` sending
`w i₀` to `1`, vanishing on `span K (w '' (univ \ {i₀}))`, and satisfying
`t * ‖φ (y k)‖ * c ≤ ‖y k‖` for every `k`. -/
theorem exists_dual_of_linearIndependent {ι κ : Type*} [Finite ι] [Finite κ] {w : ι → E}
    (hw : LinearIndependent K w) (i₀ : ι) (y : κ → E) {t : ℝ≥0} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ (c : ℝ) (φ : E →ₗ[K] K),
      0 < c ∧
      infDist (w i₀) (span K (w '' (univ \ {i₀})) : Set E) ≤ c ∧
      φ (w i₀) = 1 ∧
      (∀ u ∈ span K (w '' (univ \ {i₀})), φ u = 0) ∧
      ∀ k : κ, (t : ℝ) * ‖φ (y k)‖ * c ≤ ‖y k‖ := by
  have : FiniteDimensional K (span K (w '' (univ \ {i₀}))) :=
    FiniteDimensional.span_of_finite K (toFinite _)
  exact exists_dual_of_notMem (linearIndependent_iff_notMem_span.mp hw i₀) y ht0 ht1

end TauCeti
