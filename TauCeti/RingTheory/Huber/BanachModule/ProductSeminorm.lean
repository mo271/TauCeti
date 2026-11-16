/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Group.CompatibleNorm
public import TauCeti.Analysis.Normed.Operator.BoundedLinearMaps
public import TauCeti.Analysis.Normed.Ring.PseudoUniformizer
public import TauCeti.RingTheory.Huber.BanachModule.CompletedTensor
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Topology.MetricSpace.HausdorffDistance
import TauCeti.Analysis.Normed.Module.Bases.CountableType

/-!
# The product seminorm and Banach norm on completed module tensor products

Let `A` be a commutative ring and `V`, `W` seminormed `A`-modules. The *product seminorm*
`TauCeti.Huber.BanachModule.productSeminorm A V W` of `u : V ⊗[A] W` is the infimum of the
finite-presentation maxima `max_i ‖v_i‖ * ‖w_i‖` over all presentations `u = ∑ i, v_i ⊗ₜ w_i`,
with the empty maximum taken to be zero. The `Fin`-indexed `sInf` construction and algebraic
seminorm API adapt `TensorProduct.projectiveSeminorm` in
`TauCeti.Analysis.Normed.Module.TensorProduct.ProjectiveSeminorm` (itself adapted from Mathlib's
`PiTensorProduct.projectiveSeminorm`), replacing the sum of products `‖v_i‖ * ‖w_i‖` by their
maximum so that the ultrametric inequality `π (u₁ + u₂) ≤ max (π u₁) (π u₂)` holds and
`productSeminorm A V W` is the largest nonarchimedean additive group seminorm on `V ⊗[A] W`
bounded on pure tensors by `‖v‖ * ‖w‖`.

When `A` is a seminormed commutative ring acting boundedly on `V` or `W`
(`‖a • v‖ ≤ C * ‖a‖ * ‖v‖`), the tensor topology `TauCeti.Huber.banachTensorTopology A V W` is
finer than the topology of the product seminorm, so `productSeminorm A V W` is uniformly continuous
and its `Completion.extension` `TauCeti.Huber.BanachModule.CompletedTensor.productNorm A V W`
extends it along `V ⊗[A] W → V ⊗̂_A W` (`CompletedTensor.productNorm_toCompletion_of_bounded`,
`CompletedTensor.productNorm_toCompletion_of_bounded_right`, and
`CompletedTensor.productNorm_toCompletion` under a contractive action). If `A` moreover has a
multiplicative pseudo-uniformiser (`TauCeti.NormedRing.IsTate A`) and acts boundedly on both `V`
and `W`, rescaling elementary
tensors by integer powers of the pseudo-uniformiser balances the norms of their two factors.
Consequently the positive-radius open balls of `productSeminorm A V W` form a neighbourhood basis
of zero for `banachTensorTopology A V W` (`hasBasis_banachTensorTopology`), and `productNorm A V W`
is a definite ultrametric norm on `V ⊗̂_A W` whose open balls form a neighbourhood basis of zero for
the completion topology (`CompletedTensor.productNorm_eq_zero_iff_of_bounded` and
`CompletedTensor.hasBasis_nhds_zero_productNorm_of_bounded`, with contractive specialisations
`CompletedTensor.productNorm_eq_zero_iff` and `CompletedTensor.hasBasis_nhds_zero_productNorm`).

Over a complete nontrivially normed field `K`, approximate Gram–Schmidt orthogonalisation on the
finite-dimensional subspaces spanned by tensor presentations shows without any countable-type or
spherical-completeness hypothesis that for ultrametric seminormed `K`-spaces `V` and `W`,
`productSeminorm K V W` satisfies the pure-tensor cross-norm identity
`productSeminorm K V W (v ⊗ₜ w) = ‖v‖ * ‖w‖` (`productSeminorm_tmul`), and when `V` and `W` are
ultrametric normed `K`-spaces it vanishes only at `0` (`productSeminorm_eq_zero_iff`), so the
canonical map `V ⊗[K] W → V ⊗̂_K W` is injective (`CompletedTensor.toCompletion_injective`).

## Main definitions

* `TauCeti.Huber.BanachModule.productSeminorm A V W`: the nonarchimedean product seminorm on
  `V ⊗[A] W`.
* `TauCeti.Huber.BanachModule.CompletedTensor.productNorm A V W`: `Completion.extension` of
  `productSeminorm A V W` to `V ⊗̂_A W`, agreeing with `productSeminorm A V W` on `V ⊗[A] W`
  whenever `productSeminorm A V W` is uniformly continuous
  (`CompletedTensor.productNorm_toCompletion_of_uniformContinuous`).
* `TauCeti.Huber.BanachModule.CompletedTensor.productNormAddGroupNorm`: `productNorm` bundled as
  an additive group norm on `V ⊗̂_A W` over a Tate seminormed commutative ring with bounded module
  actions.
* `TauCeti.Huber.BanachModule.CompletedTensor.productNormedAddCommGroup` and
  `CompletedTensor.productNormedSpace`: the compatible `NormedAddCommGroup`
  (and `NormedSpace` over a nontrivially normed field) structures on `V ⊗̂_A W` retaining its
  existing uniformity, topology, and module structure definitionally.

## Main results

* `TauCeti.Huber.BanachModule.isNonarchimedean_productSeminorm`: `productSeminorm` satisfies the
  ultrametric inequality.
* `TauCeti.Huber.BanachModule.apply_le_mul_productSeminorm`, `le_productSeminorm` and
  `productSeminorm_map_le`: universal property and functoriality bound of `productSeminorm` among
  nonarchimedean additive group seminorms.
* `TauCeti.Huber.BanachModule.hasBasis_banachTensorTopology`,
  `banachTensorTopology_eq_productSeminorm` and `banachTensorUniformSpace_eq_productSeminorm`:
  identification of the tensor topology and uniformity with those of `productSeminorm` over a Tate
  seminormed commutative ring with bounded module actions.
* `TauCeti.Huber.BanachModule.CompletedTensor.productNorm_toCompletion_of_bounded`,
  `productNorm_toCompletion`, `productNorm_eq_zero_iff_of_bounded`, `productNorm_eq_zero_iff`,
  `hasBasis_nhds_zero_productNorm_of_bounded`, `hasBasis_nhds_zero_productNorm`,
  `norm_lift_le_mul_productNorm`, `productNorm_map_le`, `productNorm_le_of_hasSum` and
  `isBoundedSMul_productNormedAddCommGroup`: norm and compatibility properties on the completed
  tensor product.
* `TauCeti.Huber.BanachModule.infDist_mul_norm_le_productSeminorm`, `productSeminorm_tmul`,
  `CompletedTensor.productNorm_tmul` and `CompletedTensor.productNorm_tmul_sub_tmul_of_norm_eq_one`
  (for ultrametric seminormed spaces over a complete nontrivially normed field), together with
  `productSeminorm_eq_zero_iff` and `CompletedTensor.toCompletion_injective` (for ultrametric
  normed spaces over a complete nontrivially normed field).

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  Definitions 2.1.10 and 2.2.7, and Lemma 2.2.9(a).
* `TauCeti.Analysis.Normed.Module.TensorProduct.ProjectiveSeminorm`
  (`TensorProduct.projectiveSeminorm`, adapted from Mathlib's
  `PiTensorProduct.projectiveSeminorm`).
-/

public section

open Filter Topology UniformSpace TensorProduct
open scoped NNReal Uniformity

namespace TauCeti.Huber.BanachModule

private theorem apply_sum_le_of_isNonarchimedean {ι M : Type*} [AddCommMonoid M] {p : M → ℝ}
    (hp0 : p 0 = 0) (hp : IsNonarchimedean p) (s : Finset ι) (f : ι → M) {b : ℝ}
    (hb : 0 ≤ b) (hf : ∀ i ∈ s, p (f i) ≤ b) :
    p (∑ i ∈ s, f i) ≤ b := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa [hp0] using hb
  · exact (hp.apply_sum_le_sup hs).trans (Finset.sup'_le hs _ hf)

section Algebraic

variable (A V W : Type*) [CommRing A] [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- The finite-presentation maxima `max_i ‖v i‖ * ‖w i‖` for `u = ∑ i, v i ⊗ₜ[A] w i`, with the
empty presentation having maximum `0`. -/
private def maxCosts (u : V ⊗[A] W) : Set ℝ :=
  {c | ∃ (n : ℕ) (v : Fin n → V) (w : Fin n → W),
    ∑ i, v i ⊗ₜ[A] w i = u ∧ ((Finset.univ.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊ : ℝ≥0) : ℝ) = c}

variable {A V W}

private theorem maxCosts_nonempty (u : V ⊗[A] W) : (maxCosts A V W u).Nonempty := by
  obtain ⟨n, v, w, hu⟩ := _root_.TensorProduct.exists_sum_tmul_eq u
  exact ⟨_, n, v, w, hu.symm, rfl⟩

private theorem maxCosts_bddBelow (u : V ⊗[A] W) : BddBelow (maxCosts A V W u) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨_, _, _, -, rfl⟩
  exact NNReal.coe_nonneg _

private theorem sInf_maxCosts_le {n : ℕ} (v : Fin n → V) (w : Fin n → W) :
    sInf (maxCosts A V W (∑ i, v i ⊗ₜ[A] w i)) ≤
      ((Finset.univ.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊ : ℝ≥0) : ℝ) :=
  csInf_le (maxCosts_bddBelow _) ⟨n, v, w, rfl, rfl⟩

private theorem sInf_maxCosts_nonneg (u : V ⊗[A] W) : 0 ≤ sInf (maxCosts A V W u) := by
  refine le_csInf (maxCosts_nonempty u) ?_
  rintro _ ⟨_, _, _, -, rfl⟩
  exact NNReal.coe_nonneg _

private theorem sInf_maxCosts_zero : sInf (maxCosts A V W 0) = 0 :=
  le_antisymm
    (by simpa using sInf_maxCosts_le (A := A) (Fin.elim0 : Fin 0 → V) (Fin.elim0 : Fin 0 → W))
    (sInf_maxCosts_nonneg 0)

private theorem sInf_maxCosts_add_le_max (u₁ u₂ : V ⊗[A] W) :
    sInf (maxCosts A V W (u₁ + u₂)) ≤
      max (sInf (maxCosts A V W u₁)) (sInf (maxCosts A V W u₂)) := by
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  set r := max (sInf (maxCosts A V W u₁)) (sInf (maxCosts A V W u₂)) + ε
  have hr₁ : sInf (maxCosts A V W u₁) < r := lt_add_of_le_of_pos (le_max_left _ _) hε
  have hr₂ : sInf (maxCosts A V W u₂) < r := lt_add_of_le_of_pos (le_max_right _ _) hε
  obtain ⟨_, ⟨n, v₁, w₁, rfl, rfl⟩, hc₁⟩ := exists_lt_of_csInf_lt (maxCosts_nonempty u₁) hr₁
  obtain ⟨_, ⟨m, v₂, w₂, rfl, rfl⟩, hc₂⟩ := exists_lt_of_csInf_lt (maxCosts_nonempty u₂) hr₂
  have hsum : ∑ k : Fin (n + m), Fin.append v₁ v₂ k ⊗ₜ[A] Fin.append w₁ w₂ k =
      (∑ i, v₁ i ⊗ₜ[A] w₁ i) + ∑ j, v₂ j ⊗ₜ[A] w₂ j := by
    simpa [Fin.append] using Fin.sum_univ_add fun k ↦ Fin.append v₁ v₂ k ⊗ₜ[A] Fin.append w₁ w₂ k
  rw [← hsum]
  refine (sInf_maxCosts_le (Fin.append v₁ v₂) (Fin.append w₁ w₂)).trans_lt ?_
  refine lt_of_le_of_lt ?_ (max_lt hc₁ hc₂)
  rw [← NNReal.coe_max, NNReal.coe_le_coe]
  refine Finset.sup_le fun k _ ↦ k.addCases (fun i ↦ ?_) (fun j ↦ ?_)
  · simp only [Fin.append_left]
    exact (Finset.le_sup (f := fun i ↦ ‖v₁ i‖₊ * ‖w₁ i‖₊) (Finset.mem_univ i)).trans
      (le_max_left _ _)
  · simp only [Fin.append_right]
    exact (Finset.le_sup (f := fun j ↦ ‖v₂ j‖₊ * ‖w₂ j‖₊) (Finset.mem_univ j)).trans
      (le_max_right _ _)

private theorem sInf_maxCosts_neg_le (u : V ⊗[A] W) :
    sInf (maxCosts A V W (-u)) ≤ sInf (maxCosts A V W u) := by
  refine le_csInf (maxCosts_nonempty u) ?_
  rintro _ ⟨n, v, w, rfl, rfl⟩
  have hneg : ∑ i, (-v i) ⊗ₜ[A] w i = -∑ i, v i ⊗ₜ[A] w i := by
    simp [TensorProduct.neg_tmul, Finset.sum_neg_distrib]
  rw [← hneg]
  simpa [nnNorm_neg] using sInf_maxCosts_le (A := A) (fun i ↦ -v i) w

variable (A V W) in
/-- **The nonarchimedean product seminorm** on `V ⊗[A] W`: the infimum of the finite-presentation
maxima `max_i ‖v i‖ * ‖w i‖` over all decompositions `u = ∑ i, v i ⊗ₜ[A] w i`, with the empty
presentation having maximum `0`. -/
noncomputable def productSeminorm : AddGroupSeminorm (V ⊗[A] W) where
  toFun u := sInf (maxCosts A V W u)
  map_zero' := sInf_maxCosts_zero
  add_le' u₁ u₂ := (sInf_maxCosts_add_le_max u₁ u₂).trans
    (max_le_add_of_nonneg (sInf_maxCosts_nonneg u₁) (sInf_maxCosts_nonneg u₂))
  neg' u := le_antisymm (sInf_maxCosts_neg_le u) (by simpa using sInf_maxCosts_neg_le (-u))

private theorem productSeminorm_apply (u : V ⊗[A] W) :
    productSeminorm A V W u = sInf (maxCosts A V W u) :=
  rfl

/-- **Ultrametric inequality** for the product seminorm. -/
theorem productSeminorm_add_le_max (u₁ u₂ : V ⊗[A] W) :
    productSeminorm A V W (u₁ + u₂) ≤
      max (productSeminorm A V W u₁) (productSeminorm A V W u₂) :=
  sInf_maxCosts_add_le_max u₁ u₂

variable (A V W) in
/-- The product seminorm is nonarchimedean. -/
theorem isNonarchimedean_productSeminorm : IsNonarchimedean (productSeminorm A V W) :=
  productSeminorm_add_le_max

/-- Ultrametric inequality for differences under the product seminorm. -/
theorem productSeminorm_sub_le_max (u₁ u₂ : V ⊗[A] W) :
    productSeminorm A V W (u₁ - u₂) ≤
      max (productSeminorm A V W u₁) (productSeminorm A V W u₂) := by
  simpa [sub_eq_add_neg, map_neg_eq_map] using productSeminorm_add_le_max u₁ (-u₂)

/-- The product seminorm of a finite sum is at most any nonnegative bound on the product seminorms
of its terms. -/
theorem productSeminorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → V ⊗[A] W) {b : ℝ}
    (hb : 0 ≤ b) (hf : ∀ i ∈ s, productSeminorm A V W (f i) ≤ b) :
    productSeminorm A V W (∑ i ∈ s, f i) ≤ b :=
  apply_sum_le_of_isNonarchimedean (map_zero _) (isNonarchimedean_productSeminorm A V W) s f hb hf

/-- The product seminorm of a pure tensor is at most the product of the norms. -/
theorem productSeminorm_tmul_le (v : V) (w : W) :
    productSeminorm A V W (v ⊗ₜ[A] w) ≤ ‖v‖ * ‖w‖ := by
  simpa [productSeminorm_apply] using
    sInf_maxCosts_le (A := A) (fun _ : Fin 1 ↦ v) (fun _ : Fin 1 ↦ w)

/-- If every term of `∑ i ∈ s, v i ⊗ₜ[A] w i` satisfies `‖v i‖ * ‖w i‖ ≤ b` for some `b ≥ 0`,
then the product seminorm of the sum is at most `b`. -/
theorem productSeminorm_sum_tmul_le_of_le {ι : Type*} (s : Finset ι) (v : ι → V) (w : ι → W)
    {b : ℝ} (hb : 0 ≤ b) (h : ∀ i ∈ s, ‖v i‖ * ‖w i‖ ≤ b) :
    productSeminorm A V W (∑ i ∈ s, v i ⊗ₜ[A] w i) ≤ b :=
  productSeminorm_sum_le s _ hb fun i hi ↦ (productSeminorm_tmul_le (v i) (w i)).trans (h i hi)

/-- The product seminorm of a finite sum of pure tensors is at most the maximum of the products
`‖v i‖ * ‖w i‖`. -/
theorem productSeminorm_sum_tmul_le {ι : Type*} (s : Finset ι) (v : ι → V) (w : ι → W) :
    productSeminorm A V W (∑ i ∈ s, v i ⊗ₜ[A] w i) ≤
      ((s.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊ : ℝ≥0) : ℝ) :=
  productSeminorm_sum_tmul_le_of_le s v w (NNReal.coe_nonneg _) fun i hi ↦ by
    exact_mod_cast Finset.le_sup (f := fun j ↦ ‖v j‖₊ * ‖w j‖₊) hi

/-- A strict upper bound on the product seminorm is witnessed by some finite tensor
presentation. -/
theorem exists_sum_tmul_eq_of_productSeminorm_lt {u : V ⊗[A] W} {c : ℝ}
    (h : productSeminorm A V W u < c) :
    ∃ (n : ℕ) (v : Fin n → V) (w : Fin n → W),
      ∑ i, v i ⊗ₜ[A] w i = u ∧ ((Finset.univ.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊ : ℝ≥0) : ℝ) < c := by
  obtain ⟨_, ⟨n, v, w, hu, rfl⟩, hc⟩ := exists_lt_of_csInf_lt (maxCosts_nonempty u) h
  exact ⟨n, v, w, hu, hc⟩

/-- A strict upper bound `productSeminorm A V W u < c` forces `c > 0` and produces a finite
presentation `u = ∑ i, v i ⊗ₜ[A] w i` with `‖v i‖ * ‖w i‖ < c` for every `i`. -/
theorem exists_sum_tmul_eq_forall_lt_of_productSeminorm_lt {u : V ⊗[A] W} {c : ℝ}
    (h : productSeminorm A V W u < c) :
    0 < c ∧ ∃ (n : ℕ) (v : Fin n → V) (w : Fin n → W),
      ∑ i, v i ⊗ₜ[A] w i = u ∧ ∀ i, ‖v i‖ * ‖w i‖ < c := by
  have hc0 : 0 < c := (apply_nonneg (productSeminorm A V W) u).trans_lt h
  obtain ⟨n, v, w, hu, hc⟩ := exists_sum_tmul_eq_of_productSeminorm_lt h
  refine ⟨hc0, n, v, w, hu, fun i ↦ ?_⟩
  have hi : ‖v i‖₊ * ‖w i‖₊ ≤ Finset.univ.sup fun j ↦ ‖v j‖₊ * ‖w j‖₊ :=
    Finset.le_sup (f := fun j ↦ ‖v j‖₊ * ‖w j‖₊) (Finset.mem_univ i)
  exact lt_of_le_of_lt (by exact_mod_cast hi) hc

/-- **Infimum description by upper bounds**: `productSeminorm A V W u` is the infimum of all
`c ≥ 0` bounding the products `‖v i‖ * ‖w i‖` of a finite presentation of `u`. -/
theorem productSeminorm_eq_sInf (u : V ⊗[A] W) :
    productSeminorm A V W u = sInf {c : ℝ | 0 ≤ c ∧
      ∃ (n : ℕ) (v : Fin n → V) (w : Fin n → W),
        ∑ i, v i ⊗ₜ[A] w i = u ∧ ∀ i, ‖v i‖ * ‖w i‖ ≤ c} := by
  let S : Set ℝ := {c : ℝ | 0 ≤ c ∧ ∃ (n : ℕ) (v : Fin n → V) (w : Fin n → W),
    ∑ i, v i ⊗ₜ[A] w i = u ∧ ∀ i, ‖v i‖ * ‖w i‖ ≤ c}
  have hsub : maxCosts A V W u ⊆ S := by
    rintro _ ⟨n, v, w, rfl, rfl⟩
    refine ⟨NNReal.coe_nonneg _, n, v, w, rfl, fun i ↦ ?_⟩
    exact_mod_cast Finset.le_sup (f := fun j ↦ ‖v j‖₊ * ‖w j‖₊) (Finset.mem_univ i)
  refine le_antisymm ?_ (csInf_le_csInf ⟨0, fun _ h ↦ h.1⟩ (maxCosts_nonempty u) hsub)
  refine le_csInf ((maxCosts_nonempty u).mono hsub) ?_
  rintro c ⟨hc0, n, v, w, rfl, hw⟩
  exact productSeminorm_sum_tmul_le_of_le Finset.univ v w hc0 fun i _ ↦ hw i

/-- **Universal bound for nonarchimedean seminorms**: a nonarchimedean additive group seminorm `p`
bounded on the images of pure tensors by `C * (‖v‖ * ‖w‖)` (`C ≥ 0`) is bounded on the image of
every tensor by `C` times the product seminorm. -/
theorem apply_le_mul_productSeminorm {M : Type*} [AddCommGroup M] {p : AddGroupSeminorm M}
    (hp : IsNonarchimedean p) {f : V ⊗[A] W →+ M} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v w, p (f (v ⊗ₜ[A] w)) ≤ C * (‖v‖ * ‖w‖)) (u : V ⊗[A] W) :
    p (f u) ≤ C * productSeminorm A V W u := by
  rw [productSeminorm_apply, ← smul_eq_mul, ← Real.sInf_smul_of_nonneg hC]
  refine le_csInf (maxCosts_nonempty u).smul_set ?_
  rintro _ ⟨_, ⟨n, v, w, rfl, rfl⟩, rfl⟩
  simp only [smul_eq_mul, map_sum]
  refine apply_sum_le_of_isNonarchimedean (map_zero p) hp Finset.univ _ (by positivity) fun i _ ↦ ?_
  refine (h (v i) (w i)).trans ?_
  gcongr
  exact_mod_cast Finset.le_sup (f := fun j ↦ ‖v j‖₊ * ‖w j‖₊) (Finset.mem_univ i)

/-- **Extremality of the product seminorm**: `productSeminorm A V W` is the largest
nonarchimedean additive group seminorm on `V ⊗[A] W` bounded on pure tensors by `‖v‖ * ‖w‖`. -/
theorem le_productSeminorm {p : AddGroupSeminorm (V ⊗[A] W)} (hp : IsNonarchimedean p)
    (h : ∀ v w, p (v ⊗ₜ[A] w) ≤ ‖v‖ * ‖w‖) : p ≤ productSeminorm A V W := fun u ↦ by
  simpa using apply_le_mul_productSeminorm hp (f := AddMonoidHom.id _) zero_le_one
    (by simpa using h) u

/-- The linear map on `V ⊗[A] W` induced by a bounded `A`-bilinear map into an ultrametric
seminormed module `M` has norm bounded by `C` times the product seminorm. -/
theorem norm_lift_le_mul_productSeminorm {M : Type*} [SeminormedAddCommGroup M]
    [IsUltrametricDist M] [Module A M] (β : V →ₗ[A] W →ₗ[A] M) {C : ℝ} (hC : 0 ≤ C)
    (hβ : ∀ v w, ‖β v w‖ ≤ C * (‖v‖ * ‖w‖)) (u : V ⊗[A] W) :
    ‖TensorProduct.lift β u‖ ≤ C * productSeminorm A V W u :=
  apply_le_mul_productSeminorm (p := normAddGroupSeminorm M)
    IsUltrametricDist.isNonarchimedean_norm (f := (TensorProduct.lift β).toAddMonoidHom) hC
    (fun v w ↦ by simpa using hβ v w) u

/-- A tensor product of bounded `A`-linear maps `f : V →ₗ[A] V'` and `g : W →ₗ[A] W'` scales the
product seminorm by at most the product `C₁ * C₂` of their bounds. -/
theorem productSeminorm_map_le {V' W' : Type*} [SeminormedAddCommGroup V'] [Module A V']
    [SeminormedAddCommGroup W'] [Module A W'] (f : V →ₗ[A] V') (g : W →ₗ[A] W') {C₁ C₂ : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hf : ∀ v, ‖f v‖ ≤ C₁ * ‖v‖) (hg : ∀ w, ‖g w‖ ≤ C₂ * ‖w‖)
    (u : V ⊗[A] W) :
    productSeminorm A V' W' (TensorProduct.map f g u) ≤
      C₁ * C₂ * productSeminorm A V W u :=
  apply_le_mul_productSeminorm (isNonarchimedean_productSeminorm A V' W')
    (f := (TensorProduct.map f g).toAddMonoidHom) (mul_nonneg hC₁ hC₂)
    (fun v w ↦ by
      simp only [LinearMap.toAddMonoidHom_coe, TensorProduct.map_tmul]
      refine (productSeminorm_tmul_le (f v) (g w)).trans ?_
      calc ‖f v‖ * ‖g w‖ ≤ (C₁ * ‖v‖) * (C₂ * ‖w‖) :=
            mul_le_mul (hf v) (hg w) (norm_nonneg _) (mul_nonneg hC₁ (norm_nonneg _))
        _ = C₁ * C₂ * (‖v‖ * ‖w‖) := by ring) u

private theorem productSeminorm_comm_le (u : V ⊗[A] W) :
    productSeminorm A W V (TensorProduct.comm A V W u) ≤ productSeminorm A V W u := by
  simpa using apply_le_mul_productSeminorm (isNonarchimedean_productSeminorm A W V)
    (f := (TensorProduct.comm A V W).toLinearMap.toAddMonoidHom) zero_le_one
    (fun v w ↦ by simpa [mul_comm ‖v‖] using productSeminorm_tmul_le w v) u

/-- The product seminorm is symmetric: exchanging the two factors preserves it. -/
@[simp]
theorem productSeminorm_comm (u : V ⊗[A] W) :
    productSeminorm A W V (TensorProduct.comm A V W u) = productSeminorm A V W u :=
  (productSeminorm_comm_le u).antisymm <| by
    simpa using productSeminorm_comm_le (TensorProduct.comm A V W u)

/-- If `a : A` scales norms on `V` by at most `C ≥ 0`, it scales the product seminorm by at most
`C`. -/
theorem productSeminorm_smul_le_of_le_left {a : A} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ v : V, ‖a • v‖ ≤ C * ‖v‖) (u : V ⊗[A] W) :
    productSeminorm A V W (a • u) ≤ C * productSeminorm A V W u :=
  apply_le_mul_productSeminorm (isNonarchimedean_productSeminorm A V W)
    (f := (LinearMap.lsmul A (V ⊗[A] W) a).toAddMonoidHom) hC
    (fun v w ↦ by
      simp only [LinearMap.toAddMonoidHom_coe, LinearMap.lsmul_apply, TensorProduct.smul_tmul']
      exact (productSeminorm_tmul_le (a • v) w).trans
        (by rw [← mul_assoc]; gcongr; exact ha v)) u

/-- If `a : A` scales norms on `W` by at most `C ≥ 0`, it scales the product seminorm by at most
`C`. -/
theorem productSeminorm_smul_le_of_le_right {a : A} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ w : W, ‖a • w‖ ≤ C * ‖w‖) (u : V ⊗[A] W) :
    productSeminorm A V W (a • u) ≤ C * productSeminorm A V W u := by
  rw [← productSeminorm_comm, map_smul, ← productSeminorm_comm (u := u)]
  exact productSeminorm_smul_le_of_le_left hC ha (TensorProduct.comm A V W u)

/-- Tensoring a zero module on the left gives product seminorm zero everywhere. -/
@[simp]
theorem productSeminorm_eq_zero_of_subsingleton_left [Subsingleton V] (u : V ⊗[A] W) :
    productSeminorm A V W u = 0 := by
  rw [Subsingleton.elim u 0, map_zero]

/-- Tensoring a zero module on the right gives product seminorm zero everywhere. -/
@[simp]
theorem productSeminorm_eq_zero_of_subsingleton_right [Subsingleton W] (u : V ⊗[A] W) :
    productSeminorm A V W u = 0 := by
  rw [Subsingleton.elim u 0, map_zero]

end Algebraic

section SeminormedRing

variable {A V W : Type*} [SeminormedCommRing A] [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- Under a contractive `A`-action on `V`, the product seminorm is submultiplicative for scalar
multiplication. -/
theorem productSeminorm_smul_le [IsBoundedSMul A V] (a : A) (u : V ⊗[A] W) :
    productSeminorm A V W (a • u) ≤ ‖a‖ * productSeminorm A V W u :=
  productSeminorm_smul_le_of_le_left (norm_nonneg a) (norm_smul_le a) u

/-- A unit of `A` scaling the norm of `A` exactly also scales the product seminorm exactly under a
contractive `A`-action on `V`. -/
theorem productSeminorm_units_smul_of_norm_mul [IsBoundedSMul A V] {a : Aˣ}
    (ha : ∀ x : A, ‖(a : A) * x‖ = ‖(a : A)‖ * ‖x‖) (u : V ⊗[A] W) :
    productSeminorm A V W ((a : A) • u) = ‖(a : A)‖ * productSeminorm A V W u := by
  let : SeminormedAddCommGroup (V ⊗[A] W) := (productSeminorm A V W).toSeminormedAddCommGroup
  have : IsBoundedSMul A (V ⊗[A] W) := .of_norm_smul_le productSeminorm_smul_le
  exact TauCeti.NormedRing.norm_units_smul_of_norm_mul ha u

/-- On `A ⊗[A] V` for an ultrametric `A`-module `V` with contractive action over a norm-one
ring `A`, the product seminorm is the norm of the image under `TensorProduct.lid A V`. -/
theorem productSeminorm_eq_norm_lid [NormOneClass A] [IsUltrametricDist V] [IsBoundedSMul A V]
    (u : A ⊗[A] V) : productSeminorm A A V u = ‖TensorProduct.lid A V u‖ := by
  refine le_antisymm ?_ ?_
  · calc productSeminorm A A V u
        = productSeminorm A A V ((1 : A) ⊗ₜ[A] TensorProduct.lid A V u) := by
            rw [← TensorProduct.lid_symm_apply, LinearEquiv.symm_apply_apply]
      _ ≤ ‖(1 : A)‖ * ‖TensorProduct.lid A V u‖ := productSeminorm_tmul_le _ _
      _ = ‖TensorProduct.lid A V u‖ := by rw [norm_one, one_mul]
  · simpa using apply_le_mul_productSeminorm (p := normAddGroupSeminorm V)
      IsUltrametricDist.isNonarchimedean_norm
      (f := (TensorProduct.lid A V).toLinearMap.toAddMonoidHom) zero_le_one
      (fun a v ↦ by simpa using norm_smul_le a v) u

/-- On `V ⊗[A] A` for an ultrametric `A`-module `V` with contractive action over a norm-one
ring `A`, the product seminorm is the norm of the image under `TensorProduct.rid A V`. -/
theorem productSeminorm_eq_norm_rid [NormOneClass A] [IsUltrametricDist V] [IsBoundedSMul A V]
    (u : V ⊗[A] A) : productSeminorm A V A u = ‖TensorProduct.rid A V u‖ := by
  rw [← productSeminorm_comm, productSeminorm_eq_norm_lid, ← TensorProduct.comm_trans_lid,
    LinearEquiv.trans_apply]

end SeminormedRing

section NormedFieldAlgebraic

variable {K V W : Type*} [NormedField K] [SeminormedAddCommGroup V] [NormedSpace K V]
  [SeminormedAddCommGroup W] [Module K W]

/-- Over a normed field, the product seminorm is homogeneous under scalar multiplication. -/
@[simp]
theorem productSeminorm_smul (c : K) (u : V ⊗[K] W) :
    productSeminorm K V W (c • u) = ‖c‖ * productSeminorm K V W u := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact productSeminorm_units_smul_of_norm_mul (a := Units.mk0 c hc) (fun x ↦ norm_mul _ _) u

end NormedFieldAlgebraic

section CompleteFieldAlgebraic

section Seminormed

variable {K V : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [SeminormedAddCommGroup V] [NormedSpace K V] [IsUltrametricDist V]

/-- Helper for `infDist_mul_norm_le_productSeminorm` when the right factor `W` is Hausdorff. -/
private theorem infDist_mul_norm_le_productSeminorm_of_normed {W : Type*}
    [NormedAddCommGroup W] [NormedSpace K W] [IsUltrametricDist W]
    {ι : Type*} [Fintype ι] (v : ι → V) (w : ι → W) (i₀ : ι) :
    Metric.infDist (w i₀) (Submodule.span K (w '' (Set.univ \ {i₀})) : Set W) * ‖v i₀‖ ≤
      productSeminorm K V W (∑ j, v j ⊗ₜ[K] w j) := by
  classical
  set D : Submodule K W := Submodule.span K (w '' (Set.univ \ {i₀}))
  by_cases hw : w i₀ ∈ D
  · rw [Metric.infDist_zero_of_mem hw, zero_mul]
    exact apply_nonneg _ _
  rcases (Metric.infDist_nonneg (x := w i₀) (s := (D : Set W))).eq_or_lt with hd0 | hd_pos
  · rw [← hd0, zero_mul]
    exact apply_nonneg _ _
  rcases (norm_nonneg (v i₀)).eq_or_lt with hv0 | hv_pos
  · rw [← hv0, mul_zero]
    exact apply_nonneg _ _
  set P := Metric.infDist (w i₀) (D : Set W) * ‖v i₀‖
  have hP : 0 < P := mul_pos hd_pos hv_pos
  -- Pass to `t → 1⁻` after applying finite-dimensional `t`-orthogonal dual separation.
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨s, hs0, hs1⟩ := exists_between (max_lt one_pos (sub_lt_self 1 (div_pos hε hP)))
  let t : ℝ≥0 := ⟨s, ((le_max_left _ _).trans_lt hs0).le⟩
  have ht0 : 0 < t := by exact_mod_cast (le_max_left _ _).trans_lt hs0
  have ht1 : t < 1 := by exact_mod_cast hs1
  have htε : P < (t : ℝ) * P + ε := by
    have hmul := mul_lt_mul_of_pos_right ((le_max_right _ _).trans_lt hs0) hP
    have hsub : (1 - ε / P) * P = P - ε := by field_simp
    have ht_coe : (t : ℝ) = s := rfl
    rw [hsub, ← ht_coe] at hmul
    linarith
  have hle_t : (t : ℝ) * P ≤ productSeminorm K V W (∑ j, v j ⊗ₜ[K] w j) := by
    rw [productSeminorm_apply]
    refine le_csInf (maxCosts_nonempty _) ?_
    rintro _ ⟨m, x, y, hxy, rfl⟩
    have : FiniteDimensional K D := FiniteDimensional.span_of_finite K (Set.toFinite _)
    obtain ⟨c, φ, hc_pos, hdist, hφ_wi0, hφ_D, hφ_yk⟩ :=
      TauCeti.exists_dual_of_notMem hw y ht0 ht1
    let Φ : V ⊗[K] W →ₗ[K] V := (TensorProduct.rid K V).toLinearMap.comp (φ.lTensor V)
    have hvi0_eq : v i₀ = ∑ k : Fin m, φ (y k) • x k := by
      have hΦ_rhs : Φ (∑ j, v j ⊗ₜ[K] w j) = v i₀ := by
        rw [map_sum, Finset.sum_eq_single i₀]
        · simp [Φ, hφ_wi0]
        · intro j _ hj
          simp [Φ, hφ_D _ (Submodule.subset_span ⟨j, ⟨Set.mem_univ j, hj⟩, rfl⟩)]
        · simp
      rw [← hΦ_rhs, ← hxy, map_sum]
      simp [Φ]
    have hpos : 0 < (t : ℝ) * c := mul_pos (by exact_mod_cast ht0) hc_pos
    have hle : ‖v i₀‖ ≤ (((t : ℝ) * c)⁻¹) *
        ((Finset.univ.sup fun k : Fin m ↦ ‖x k‖₊ * ‖y k‖₊ : ℝ≥0) : ℝ) := by
      rw [hvi0_eq]
      refine apply_sum_le_of_isNonarchimedean norm_zero IsUltrametricDist.isNonarchimedean_norm
        Finset.univ _ (by positivity) fun k _ ↦ ?_
      rw [norm_smul, le_inv_mul_iff₀ hpos]
      calc (t : ℝ) * c * (‖φ (y k)‖ * ‖x k‖)
          = ‖x k‖ * ((t : ℝ) * ‖φ (y k)‖ * c) := by ring
        _ ≤ ‖x k‖ * ‖y k‖ := by gcongr; exact hφ_yk k
        _ ≤ ((Finset.univ.sup fun j : Fin m ↦ ‖x j‖₊ * ‖y j‖₊ : ℝ≥0) : ℝ) := by
            exact_mod_cast Finset.le_sup (f := fun j ↦ ‖x j‖₊ * ‖y j‖₊) (Finset.mem_univ k)
    calc (t : ℝ) * P
        = (t : ℝ) * Metric.infDist (w i₀) (D : Set W) * ‖v i₀‖ := (mul_assoc _ _ _).symm
      _ ≤ (t : ℝ) * c * ‖v i₀‖ := by gcongr
      _ ≤ ((Finset.univ.sup fun k : Fin m ↦ ‖x k‖₊ * ‖y k‖₊ : ℝ≥0) : ℝ) :=
          (le_inv_mul_iff₀ hpos).mp hle
  linarith

variable {W : Type*} [SeminormedAddCommGroup W] [NormedSpace K W] [IsUltrametricDist W]

/-- **Finite-dimensional Gram–Schmidt lower bound** for the product seminorm: for ultrametric
seminormed `K`-spaces `V` and `W` over a complete nontrivially normed field `K`, any finite family
`∑ j, v j ⊗ₜ[K] w j` satisfies
`infDist (w i₀) (span K (w '' (univ \ {i₀}))) * ‖v i₀‖ ≤ productSeminorm K V W (∑ j, v j ⊗ₜ w j)`.
-/
theorem infDist_mul_norm_le_productSeminorm {ι : Type*} [Fintype ι]
    (v : ι → V) (w : ι → W) (i₀ : ι) :
    Metric.infDist (w i₀) (Submodule.span K (w '' (Set.univ \ {i₀})) : Set W) * ‖v i₀‖ ≤
      productSeminorm K V W (∑ j, v j ⊗ₜ[K] w j) := by
  -- Reduce `W` to its Hausdorff quotient `SeparationQuotient W`, where `exists_dual_of_notMem`
  -- applies and the quotient map is an isometry.
  have : IsUltrametricDist (SeparationQuotient W) :=
    ⟨SeparationQuotient.surjective_mk.forall₃.2 fun x y z ↦ by
      simpa only [SeparationQuotient.dist_mk] using dist_triangle_max x y z⟩
  let q : W →ₗ[K] SeparationQuotient W := (SeparationQuotient.mkCLM K W).toLinearMap
  have hq_apply (x : W) : q x = SeparationQuotient.mk x := rfl
  have hiso : Isometry (SeparationQuotient.mk : W → SeparationQuotient W) :=
    Isometry.of_dist_eq SeparationQuotient.dist_mk
  have hspan : (Submodule.span K ((q ∘ w) '' (Set.univ \ {i₀})) : Set (SeparationQuotient W)) =
      SeparationQuotient.mk '' (Submodule.span K (w '' (Set.univ \ {i₀})) : Set W) := by
    rw [Set.image_comp q w, ← Submodule.map_span, Submodule.map_coe]
    rfl
  have hdist : Metric.infDist (q (w i₀))
      (Submodule.span K ((q ∘ w) '' (Set.univ \ {i₀})) : Set (SeparationQuotient W)) =
      Metric.infDist (w i₀) (Submodule.span K (w '' (Set.univ \ {i₀})) : Set W) := by
    rw [hspan, hq_apply, Metric.infDist_image hiso]
  have hmap : productSeminorm K V (SeparationQuotient W) (∑ j, v j ⊗ₜ[K] q (w j)) ≤
      productSeminorm K V W (∑ j, v j ⊗ₜ[K] w j) := by
    have h := productSeminorm_map_le (LinearMap.id : V →ₗ[K] V) q zero_le_one zero_le_one
      (fun x ↦ by simp) (fun y ↦ by simp [hq_apply]) (∑ j, v j ⊗ₜ[K] w j)
    simpa [map_sum] using h
  exact (hdist ▸ infDist_mul_norm_le_productSeminorm_of_normed v (q ∘ w) i₀).trans hmap

/-- **Cross-norm on pure tensors**: for ultrametric seminormed `K`-spaces `V` and `W` over a
complete nontrivially normed field `K`, the product seminorm of `v ⊗ₜ[K] w` equals `‖v‖ * ‖w‖`. -/
@[simp]
theorem productSeminorm_tmul (v : V) (w : W) :
    productSeminorm K V W (v ⊗ₜ[K] w) = ‖v‖ * ‖w‖ := by
  refine le_antisymm (productSeminorm_tmul_le v w) ?_
  have h := infDist_mul_norm_le_productSeminorm (K := K) (fun _ : Unit ↦ v) (fun _ : Unit ↦ w) ()
  have hemp : (Set.univ : Set Unit) \ {()} = ∅ := by ext x; cases x; simp
  have hD : (Submodule.span K ((fun _ : Unit ↦ w) '' (Set.univ \ {()})) : Set W) = {0} := by
    simp [hemp]
  rw [hD] at h
  simpa [Metric.infDist_singleton, mul_comm] using h

end Seminormed

section Normed

variable {K V W : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup V] [NormedSpace K V] [IsUltrametricDist V]
  [NormedAddCommGroup W] [NormedSpace K W] [IsUltrametricDist W]

/-- **Definiteness of the product seminorm**: for ultrametric normed `K`-spaces `V` and `W` over a
complete nontrivially normed field `K` (KL15, Lemma 2.2.9(a)), `productSeminorm K V W u = 0` if and
only if `u = 0`. -/
@[simp]
theorem productSeminorm_eq_zero_iff {u : V ⊗[K] W} :
    productSeminorm K V W u = 0 ↔ u = 0 := by
  refine ⟨fun h0 ↦ ?_, fun h ↦ h ▸ map_zero _⟩
  by_contra hu
  obtain ⟨n, a, b, hab⟩ := _root_.TensorProduct.exists_sum_tmul_eq u
  let W₁ : Submodule K W := Submodule.span K (Set.range b)
  have : FiniteDimensional K W₁ := FiniteDimensional.span_of_finite K (Set.finite_range b)
  let f := Module.finBasis K W₁
  set d := Module.finrank K W₁
  let b' : Fin n → W₁ := fun i ↦ ⟨b i, Submodule.subset_span ⟨i, rfl⟩⟩
  let v' : Fin d → V := fun j ↦ ∑ i : Fin n, f.repr (b' i) j • a i
  let w : Fin d → W := fun j ↦ (f j : W)
  have hu_eq : u = ∑ j : Fin d, v' j ⊗ₜ[K] w j := by
    rw [hab]
    have hb_eq (i : Fin n) : b i = ∑ j : Fin d, f.repr (b' i) j • w j := by
      have h := congrArg (W₁.subtype : W₁ →ₗ[K] W) (f.sum_repr (b' i)).symm
      simpa only [map_sum, map_smul, Submodule.coe_subtype, w] using h
    calc ∑ i : Fin n, a i ⊗ₜ[K] b i
        = ∑ i : Fin n, ∑ j : Fin d, (f.repr (b' i) j • a i) ⊗ₜ[K] w j := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            conv_lhs => rw [hb_eq i]
            simp [TensorProduct.tmul_sum, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      _ = ∑ j : Fin d, v' j ⊗ₜ[K] w j := by
            rw [Finset.sum_comm]
            simp [v', TensorProduct.sum_tmul]
  obtain ⟨j₀, hj₀⟩ : ∃ j : Fin d, v' j ≠ 0 := by
    by_contra! hall
    exact hu (by simp [hu_eq, hall])
  have hw_li : LinearIndependent K w := f.linearIndependent.map' W₁.subtype W₁.ker_subtype
  set D : Submodule K W := Submodule.span K (w '' (Set.univ \ {j₀}))
  have : FiniteDimensional K D := FiniteDimensional.span_of_finite K (Set.toFinite _)
  have hw_notMem : w j₀ ∉ (D : Set W) := linearIndependent_iff_notMem_span.mp hw_li j₀
  have hdist_pos : 0 < Metric.infDist (w j₀) (D : Set W) :=
    (D.isClosed_of_finiteDimensional.notMem_iff_infDist_pos ⟨0, D.zero_mem⟩).mp hw_notMem
  have hv_pos : 0 < ‖v' j₀‖ := norm_pos_iff.mpr hj₀
  have hkey := infDist_mul_norm_le_productSeminorm (K := K) v' w j₀
  rw [← hu_eq, h0] at hkey
  exact (mul_pos hdist_pos hv_pos).not_ge hkey

end Normed

end CompleteFieldAlgebraic

section TensorTopology

section TopologicalRing

variable {A V W : Type*} [CommRing A] [TopologicalSpace A]
  [SeminormedAddCommGroup V] [Module A V] [SeminormedAddCommGroup W] [Module A W]

/-- Whenever scalar multiplication by `A` on `V ⊗[A] W` is continuous for `productSeminorm A V W`,
the tensor topology `banachTensorTopology A V W` is finer than the topology of
`productSeminorm A V W`. -/
theorem banachTensorTopology_le_productSeminorm
    (hsmul : @ContinuousSMul A (V ⊗[A] W) _ _
      (productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace) :
    banachTensorTopology A V W ≤
      (productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace := by
  let : SeminormedAddCommGroup (V ⊗[A] W) := (productSeminorm A V W).toSeminormedAddCommGroup
  have : IsUltrametricDist (V ⊗[A] W) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_productSeminorm A V W)
  have htmul : Continuous fun p : V × W ↦ p.1 ⊗ₜ[A] p.2 :=
    (TensorProduct.mk A V W).continuous₂_of_bound 1 fun v w ↦ by
      rw [one_mul, TensorProduct.mk_apply]
      exact productSeminorm_tmul_le v w
  exact banachTensorTopology_le inferInstance hsmul htmul

/-- Whenever `banachTensorTopology A V W` is finer than the topology of `productSeminorm A V W`,
`productSeminorm A V W` is uniformly continuous for `banachTensorUniformSpace A V W`. -/
theorem uniformContinuous_productSeminorm_of_le
    (hle : banachTensorTopology A V W ≤
      (productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace) :
    @UniformContinuous (V ⊗[A] W) ℝ (banachTensorUniformSpace A V W) _
      (productSeminorm A V W) := by
  let g : SeminormedAddCommGroup (V ⊗[A] W) := (productSeminorm A V W).toSeminormedAddCommGroup
  have hu₁ : @uniformity (V ⊗[A] W) (banachTensorUniformSpace A V W) =
      Filter.comap (fun p : (V ⊗[A] W) × (V ⊗[A] W) ↦ p.2 - p.1)
        (@nhds (V ⊗[A] W) (banachTensorTopology A V W) 0) := by
    let : UniformSpace (V ⊗[A] W) := banachTensorUniformSpace A V W
    have : IsUniformAddGroup (V ⊗[A] W) := isUniformAddGroup_banachTensorUniformSpace A V W
    rw [← banachTensorUniformSpace_toTopologicalSpace]
    exact uniformity_eq_comap_nhds_zero (V ⊗[A] W)
  have hu₂ : @uniformity (V ⊗[A] W) g.toUniformSpace =
      Filter.comap (fun p : (V ⊗[A] W) × (V ⊗[A] W) ↦ p.2 - p.1)
        (@nhds (V ⊗[A] W) g.toUniformSpace.toTopologicalSpace 0) :=
    letI : SeminormedAddCommGroup (V ⊗[A] W) := g
    uniformity_eq_comap_nhds_zero (V ⊗[A] W)
  exact (@uniformContinuous_norm (V ⊗[A] W) g.toSeminormedAddGroup).mono_left
    (hu₁ ▸ hu₂ ▸ Filter.comap_mono (nhds_mono hle))

end TopologicalRing

variable {A V W : Type*} [SeminormedCommRing A] [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- When `A` acts boundedly on `V`, the tensor topology `banachTensorTopology A V W` is finer than
the topology of `productSeminorm A V W`. -/
theorem banachTensorTopology_le_productSeminorm_of_left
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) :
    banachTensorTopology A V W ≤
      (productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace := by
  obtain ⟨C, hC⟩ := hV
  let : SeminormedAddCommGroup (V ⊗[A] W) := (productSeminorm A V W).toSeminormedAddCommGroup
  exact banachTensorTopology_le_productSeminorm <|
    TauCeti.continuousSMul_of_norm_smul_le ⟨C, fun a u ↦
      productSeminorm_smul_le_of_le_left (by positivity) (hC a) u⟩

/-- When `A` acts boundedly on `W`, the tensor topology `banachTensorTopology A V W` is finer than
the topology of `productSeminorm A V W`. -/
theorem banachTensorTopology_le_productSeminorm_of_right
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    banachTensorTopology A V W ≤
      (productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace := by
  obtain ⟨C, hC⟩ := hW
  let : SeminormedAddCommGroup (V ⊗[A] W) := (productSeminorm A V W).toSeminormedAddCommGroup
  exact banachTensorTopology_le_productSeminorm <|
    TauCeti.continuousSMul_of_norm_smul_le ⟨C, fun a u ↦
      productSeminorm_smul_le_of_le_right (by positivity) (hC a) u⟩

/-- When `A` acts boundedly on `V`, `productSeminorm A V W` is uniformly continuous for
`banachTensorUniformSpace A V W`. -/
theorem uniformContinuous_productSeminorm
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) :
    @UniformContinuous (V ⊗[A] W) ℝ (banachTensorUniformSpace A V W) _
      (productSeminorm A V W) :=
  uniformContinuous_productSeminorm_of_le (banachTensorTopology_le_productSeminorm_of_left hV)

/-- When `A` acts boundedly on `W`, `productSeminorm A V W` is uniformly continuous for
`banachTensorUniformSpace A V W`. -/
theorem uniformContinuous_productSeminorm_of_right
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    @UniformContinuous (V ⊗[A] W) ℝ (banachTensorUniformSpace A V W) _
      (productSeminorm A V W) :=
  uniformContinuous_productSeminorm_of_le (banachTensorTopology_le_productSeminorm_of_right hW)

/-- Real-number balancing by integer powers of `q ∈ (0, 1)`: when `x * y < q * δ ^ 2` for
`x, y ≥ 0` and `δ > 0`, some integer `k` satisfies `q ^ k * x < δ` and `q ^ (-k) * y < δ`. -/
private theorem exists_zpow_mul_lt {q δ x y : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hδ : 0 < δ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x * y < q * δ ^ 2) :
    ∃ k : ℤ, q ^ k * x < δ ∧ q ^ (-k) * y < δ := by
  -- Degenerate cases where `x = 0` or `y = 0`.
  rcases hx.eq_or_lt with rfl | hx_pos
  · have hy1 : 0 < y + 1 := by linarith
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hδ hy1) hq1
    refine ⟨-(m : ℤ), by simp [hδ], ?_⟩
    rw [neg_neg, zpow_natCast]
    exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (by positivity)).trans_lt
      ((lt_div_iff₀ hy1).mp hm)
  rcases hy.eq_or_lt with rfl | hy_pos
  · obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hδ hx_pos) hq1
    refine ⟨(m : ℤ), ?_, by simp [hδ]⟩
    rwa [zpow_natCast, ← lt_div_iff₀ hx_pos]
  -- Nonzero case: place `q ^ k * x` in the shell `[q * δ, δ)`.
  obtain ⟨m, ⟨hm_gt, hm_le⟩, -⟩ :=
    TauCeti.existsUnique_zpow_mul_mem_Ioc hq0 hq1 (div_pos hx_pos hδ)
  have hrew (j : ℤ) : q ^ j * (x / δ) = q ^ j * x / δ := (mul_div_assoc _ _ _).symm
  set k : ℤ := if q ^ m * (x / δ) = 1 then m + 1 else m
  have hk : q ^ k * x < δ ∧ q * δ ≤ q ^ k * x := by
    by_cases h_eq : q ^ m * (x / δ) = 1 <;> simp only [k, h_eq, ↓reduceIte]
    · have hm1 : q ^ (m + 1) * x / δ = q := by
        rw [← hrew, zpow_add_one₀ hq0.ne', mul_right_comm, h_eq, one_mul]
      exact ⟨(div_lt_one hδ).mp (hm1.trans_lt hq1), ((div_eq_iff hδ.ne').mp hm1).ge⟩
    · exact ⟨(div_lt_one hδ).mp (hrew m ▸ hm_le.lt_of_ne h_eq),
        ((lt_div_iff₀ hδ).mp (hrew m ▸ hm_gt)).le⟩
  refine ⟨k, hk.1, lt_of_mul_lt_mul_left ?_ (mul_pos hq0 hδ).le⟩
  have hq_inv : q ^ k * q ^ (-k) = 1 := by
    rw [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ hq0.ne')]
  calc (q * δ) * (q ^ (-k) * y)
      ≤ (q ^ k * x) * (q ^ (-k) * y) := mul_le_mul_of_nonneg_right hk.2 (by positivity)
    _ = (q ^ k * q ^ (-k)) * (x * y) := by ring
    _ = x * y := by rw [hq_inv, one_mul]
    _ < (q * δ) * δ := by linarith

/-- Balancing a pure tensor `v ⊗ₜ[A] w` by an integer power of a multiplicative pseudo-uniformiser
`ϖ`: when `‖v‖ * ‖w‖` is small enough relative to `δ ^ 2`, rescaling `(v, w)` to
`(ϖ ^ k • v, ϖ ^ (-k) • w)` puts both factors inside the `δ`-ball without changing `v ⊗ₜ[A] w`. -/
private theorem exists_zpow_smul_tmul_lt (ϖ : TauCeti.NormedRing.PseudoUniformizer A)
    {C₁ C₂ : ℝ≥0} (hC₁ : ∀ (a : A) (v : V), ‖a • v‖ ≤ C₁ * ‖a‖ * ‖v‖)
    (hC₂ : ∀ (a : A) (w : W), ‖a • w‖ ≤ C₂ * ‖a‖ * ‖w‖) {δ : ℝ} (hδ : 0 < δ) {v : V} {w : W}
    (hvw : ‖v‖ * ‖w‖ < ‖(ϖ.unit : A)‖ * δ ^ 2 / ((max (C₁ : ℝ) 1) * (max (C₂ : ℝ) 1))) :
    ∃ (v' : V) (w' : W), v' ⊗ₜ[A] w' = v ⊗ₜ[A] w ∧ ‖v'‖ < δ ∧ ‖w'‖ < δ := by
  set B₁ : ℝ := max C₁ 1
  set B₂ : ℝ := max C₂ 1
  have hB : 0 < B₁ * B₂ :=
    mul_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hprod : (B₁ * ‖v‖) * (B₂ * ‖w‖) < ‖(ϖ.unit : A)‖ * δ ^ 2 := by
    calc (B₁ * ‖v‖) * (B₂ * ‖w‖) = (‖v‖ * ‖w‖) * (B₁ * B₂) := by ring
      _ < ‖(ϖ.unit : A)‖ * δ ^ 2 := (lt_div_iff₀ hB).mp hvw
  obtain ⟨k, hkv, hkw⟩ :=
    exists_zpow_mul_lt ϖ.norm_pos ϖ.norm_lt_one hδ (by positivity) (by positivity) hprod
  refine ⟨((ϖ.unit ^ k : Aˣ) : A) • v, ((ϖ.unit ^ (-k) : Aˣ) : A) • w, ?_, ?_, ?_⟩
  · rw [TensorProduct.smul_tmul, smul_smul, ← Units.val_mul, zpow_neg, mul_inv_cancel,
      Units.val_one, one_smul]
  · refine (hC₁ _ v).trans_lt (lt_of_le_of_lt ?_ hkv)
    rw [ϖ.norm_zpow k]
    calc (C₁ : ℝ) * ‖(ϖ.unit : A)‖ ^ k * ‖v‖
        ≤ B₁ * ‖(ϖ.unit : A)‖ ^ k * ‖v‖ := by
          have := ϖ.norm_pos
          gcongr; exact le_max_left _ _
      _ = ‖(ϖ.unit : A)‖ ^ k * (B₁ * ‖v‖) := by ring
  · refine (hC₂ _ w).trans_lt (lt_of_le_of_lt ?_ hkw)
    rw [ϖ.norm_zpow (-k)]
    calc (C₂ : ℝ) * ‖(ϖ.unit : A)‖ ^ (-k) * ‖w‖
        ≤ B₂ * ‖(ϖ.unit : A)‖ ^ (-k) * ‖w‖ := by
          have := ϖ.norm_pos
          gcongr; exact le_max_left _ _
      _ = ‖(ϖ.unit : A)‖ ^ (-k) * (B₂ * ‖w‖) := by ring

section IsTate

variable [TauCeti.NormedRing.IsTate A]

/-- **Equality of uniformities**: over a Tate seminormed commutative ring `A` acting boundedly on
`V` and `W`, `banachTensorUniformSpace A V W` coincides with the uniformity induced by
`productSeminorm A V W`. -/
theorem banachTensorUniformSpace_eq_productSeminorm
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    banachTensorUniformSpace A V W =
      (productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace := by
  refine (isUniformAddGroup_banachTensorUniformSpace A V W).ext
    (productSeminorm A V W).toSeminormedAddCommGroup.to_isUniformAddGroup ?_
  rw [banachTensorUniformSpace_toTopologicalSpace]
  refine le_antisymm (nhds_mono (banachTensorTopology_le_productSeminorm_of_left hV)) ?_
  intro U hU
  let : TopologicalSpace (V ⊗[A] W) := banachTensorTopology A V W
  have : NonarchimedeanAddGroup (V ⊗[A] W) := nonarchimedeanAddGroup_banachTensorTopology A V W
  obtain ⟨G, hGU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  have hcont := (continuous_tmul_banachTensorTopology A V W).tendsto ((0 : V), (0 : W))
  simp only [TensorProduct.zero_tmul] at hcont
  obtain ⟨U₁, hU₁, U₂, hU₂, hU₁₂⟩ := mem_nhds_prod_iff.mp
    (hcont (G.isOpen.mem_nhds G.zero_mem))
  obtain ⟨δ₁, hδ₁, hδ₁U⟩ := Metric.mem_nhds_iff.mp hU₁
  obtain ⟨δ₂, hδ₂, hδ₂U⟩ := Metric.mem_nhds_iff.mp hU₂
  set δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  obtain ⟨ϖ⟩ := ‹TauCeti.NormedRing.IsTate A›.nonempty_pseudoUniformizer
  obtain ⟨C₁, hC₁⟩ := hV
  obtain ⟨C₂, hC₂⟩ := hW
  set r : ℝ := ‖(ϖ.unit : A)‖ * δ ^ 2 / ((max (C₁ : ℝ) 1) * (max (C₂ : ℝ) 1))
  have hr : 0 < r := by
    have := ϖ.norm_pos
    positivity
  refine Filter.mem_of_superset
    (@Metric.ball_mem_nhds _
      (productSeminorm A V W).toSeminormedAddCommGroup.toPseudoMetricSpace 0 r hr) ?_
  intro u hu
  have hlt : productSeminorm A V W u < r := by
    let : SeminormedAddCommGroup (V ⊗[A] W) :=
      (productSeminorm A V W).toSeminormedAddCommGroup
    rwa [Metric.mem_ball, dist_zero_right] at hu
  obtain ⟨-, n, v, w, rfl, hvw⟩ := exists_sum_tmul_eq_forall_lt_of_productSeminorm_lt hlt
  refine hGU (G.sum_mem fun i _ ↦ ?_)
  obtain ⟨v', w', hbal, hv', hw'⟩ := exists_zpow_smul_tmul_lt ϖ hC₁ hC₂ hδ (hvw i)
  rw [← hbal]
  exact @hU₁₂ (v', w') ⟨hδ₁U (mem_ball_zero_iff.mpr (hv'.trans_le (min_le_left _ _))),
    hδ₂U (mem_ball_zero_iff.mpr (hw'.trans_le (min_le_right _ _)))⟩

/-- **Equality of topologies**: over a Tate seminormed commutative ring `A` acting boundedly on
`V` and `W`, `banachTensorTopology A V W` coincides with the topology induced by
`productSeminorm A V W`. -/
theorem banachTensorTopology_eq_productSeminorm
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    banachTensorTopology A V W =
      (productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace := by
  rw [← banachTensorUniformSpace_toTopologicalSpace]
  exact congrArg (@UniformSpace.toTopologicalSpace (V ⊗[A] W))
    (banachTensorUniformSpace_eq_productSeminorm hV hW)

/-- **Neighbourhood basis of the tensor topology**: over a Tate seminormed commutative ring `A`
acting boundedly on `V` and `W`, the positive-radius open balls of `productSeminorm A V W` form a
neighbourhood basis of `0` for `banachTensorTopology A V W`. -/
theorem hasBasis_banachTensorTopology
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    (@nhds (V ⊗[A] W) (banachTensorTopology A V W) 0).HasBasis (0 < ·)
      fun r ↦ {u | productSeminorm A V W u < r} := by
  rw [banachTensorTopology_eq_productSeminorm hV hW]
  let : SeminormedAddCommGroup (V ⊗[A] W) := (productSeminorm A V W).toSeminormedAddCommGroup
  refine (Metric.nhds_basis_ball (x := (0 : V ⊗[A] W))).congr (fun _ ↦ Iff.rfl) fun r _ ↦ ?_
  ext u
  simp only [Metric.mem_ball, dist_zero_right]
  rfl

end IsTate

end TensorTopology

namespace CompletedTensor

section Def

variable (A V W : Type*) [CommRing A] [TopologicalSpace A]
  [SeminormedAddCommGroup V] [Module A V] [SeminormedAddCommGroup W] [Module A W]

/-- **The completed product norm** (or seminorm) on `V ⊗̂_A W`, defined via `Completion.extension`
of `productSeminorm A V W` along `V ⊗[A] W → V ⊗̂_A W`. It agrees with `productSeminorm A V W` on
`V ⊗[A] W` whenever `productSeminorm A V W` is uniformly continuous
(`productNorm_toCompletion_of_uniformContinuous`, for instance when `A` is a seminormed commutative
ring acting boundedly on `V` or `W`, `productNorm_toCompletion_of_bounded`,
`productNorm_toCompletion`). Over a Tate seminormed commutative ring `A` acting boundedly on `V`
and `W`, it is a definite ultrametric norm whose open balls generate the topology of `V ⊗̂_A W`. -/
noncomputable def productNorm (z : CompletedTensor A V W) : ℝ :=
  @Completion.extension (V ⊗[A] W) (banachTensorUniformSpace A V W) ℝ _
    (productSeminorm A V W) (equivCompletion A V W z)

/-- `productNorm A V W` is uniformly continuous on `V ⊗̂_A W`. -/
theorem uniformContinuous_productNorm : UniformContinuous (productNorm A V W) := by
  let : UniformSpace (V ⊗[A] W) := banachTensorUniformSpace A V W
  exact (Completion.uniformContinuous_extension (f := productSeminorm A V W)).comp
    (uniformContinuous_equivCompletion A V W)

/-- `productNorm A V W` is continuous on `V ⊗̂_A W`. -/
@[continuity, fun_prop]
theorem continuous_productNorm : Continuous (productNorm A V W) :=
  (uniformContinuous_productNorm A V W).continuous

variable {A V W}

/-- Whenever `productSeminorm A V W` is uniformly continuous for `banachTensorUniformSpace A V W`,
`productNorm` extends `productSeminorm` along `toCompletion`. -/
theorem productNorm_toCompletion_of_uniformContinuous
    (huc : @UniformContinuous (V ⊗[A] W) ℝ (banachTensorUniformSpace A V W) _
      (productSeminorm A V W))
    (u : V ⊗[A] W) :
    productNorm A V W (toCompletion A V W u) = productSeminorm A V W u := by
  simp only [productNorm, equivCompletion_toCompletion]
  exact @Completion.extension_coe (V ⊗[A] W) (banachTensorUniformSpace A V W) ℝ _ _ _ huc u

/-- Whenever `banachTensorTopology A V W` is finer than the topology of `productSeminorm A V W`,
`productNorm` extends `productSeminorm` along `toCompletion`. -/
theorem productNorm_toCompletion_of_le
    (hle : banachTensorTopology A V W ≤
      (productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace)
    (u : V ⊗[A] W) :
    productNorm A V W (toCompletion A V W u) = productSeminorm A V W u :=
  productNorm_toCompletion_of_uniformContinuous (uniformContinuous_productSeminorm_of_le hle) u

/-- Tensoring a zero module on the left gives `productNorm` zero on the entire completion. -/
@[simp]
theorem productNorm_eq_zero_of_subsingleton_left [Subsingleton V]
    (z : CompletedTensor A V W) : productNorm A V W z = 0 := by
  have hzero : (productSeminorm A V W : V ⊗[A] W → ℝ) = fun _ ↦ 0 :=
    funext productSeminorm_eq_zero_of_subsingleton_left
  have huc : @UniformContinuous (V ⊗[A] W) ℝ (banachTensorUniformSpace A V W) _
      (productSeminorm A V W) :=
    hzero ▸ @uniformContinuous_const (V ⊗[A] W) ℝ (banachTensorUniformSpace A V W) _ 0
  refine (denseRange_toCompletion A V W).induction_on z
    (isClosed_eq (continuous_productNorm A V W) continuous_const) fun u ↦ ?_
  rw [productNorm_toCompletion_of_uniformContinuous huc,
    productSeminorm_eq_zero_of_subsingleton_left]

/-- Tensoring a zero module on the right gives `productNorm` zero on the entire completion. -/
@[simp]
theorem productNorm_eq_zero_of_subsingleton_right [Subsingleton W]
    (z : CompletedTensor A V W) : productNorm A V W z = 0 := by
  have hzero : (productSeminorm A V W : V ⊗[A] W → ℝ) = fun _ ↦ 0 :=
    funext productSeminorm_eq_zero_of_subsingleton_right
  have huc : @UniformContinuous (V ⊗[A] W) ℝ (banachTensorUniformSpace A V W) _
      (productSeminorm A V W) :=
    hzero ▸ @uniformContinuous_const (V ⊗[A] W) ℝ (banachTensorUniformSpace A V W) _ 0
  refine (denseRange_toCompletion A V W).induction_on z
    (isClosed_eq (continuous_productNorm A V W) continuous_const) fun u ↦ ?_
  rw [productNorm_toCompletion_of_uniformContinuous huc,
    productSeminorm_eq_zero_of_subsingleton_right]

end Def

section Bounded

variable {A V W : Type*} [SeminormedCommRing A] [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- When `A` acts boundedly on `V`, `productNorm` agrees with `productSeminorm` on the image of
`V ⊗[A] W`. -/
theorem productNorm_toCompletion_of_bounded
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) (u : V ⊗[A] W) :
    productNorm A V W (toCompletion A V W u) = productSeminorm A V W u :=
  productNorm_toCompletion_of_uniformContinuous (uniformContinuous_productSeminorm hV) u

/-- When `A` acts boundedly on `W`, `productNorm` agrees with `productSeminorm` on the image of
`V ⊗[A] W`. -/
theorem productNorm_toCompletion_of_bounded_right
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) (u : V ⊗[A] W) :
    productNorm A V W (toCompletion A V W u) = productSeminorm A V W u :=
  productNorm_toCompletion_of_uniformContinuous (uniformContinuous_productSeminorm_of_right hW) u

/-- Under a contractive `A`-action on `V`, `productNorm` agrees with `productSeminorm` on the
algebraic tensor product. -/
@[simp]
theorem productNorm_toCompletion [IsBoundedSMul A V] (u : V ⊗[A] W) :
    productNorm A V W (toCompletion A V W u) = productSeminorm A V W u :=
  productNorm_toCompletion_of_bounded TauCeti.exists_norm_smul_le u

/-- Under a contractive `A`-action on `W`, `productNorm` agrees with `productSeminorm` on the
algebraic tensor product. -/
theorem productNorm_toCompletion_of_right [IsBoundedSMul A W] (u : V ⊗[A] W) :
    productNorm A V W (toCompletion A V W u) = productSeminorm A V W u :=
  productNorm_toCompletion_of_bounded_right TauCeti.exists_norm_smul_le u

/-- `productNorm` vanishes at `0`. -/
theorem productNorm_zero_of_bounded
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) :
    productNorm A V W 0 = 0 := by
  rw [← map_zero (toCompletion A V W), productNorm_toCompletion_of_bounded hV, map_zero]

/-- Under a contractive `A`-action on `V`, `productNorm A V W 0 = 0`. -/
@[simp]
theorem productNorm_zero [IsBoundedSMul A V] : productNorm A V W 0 = 0 :=
  productNorm_zero_of_bounded TauCeti.exists_norm_smul_le

/-- `productNorm` is nonnegative. -/
theorem productNorm_nonneg_of_bounded
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (z : CompletedTensor A V W) : 0 ≤ productNorm A V W z := by
  refine (denseRange_toCompletion A V W).induction_on z
    (isClosed_le continuous_const (continuous_productNorm A V W)) fun u ↦ ?_
  rw [productNorm_toCompletion_of_bounded hV]
  exact apply_nonneg _ _

/-- Under a contractive `A`-action on `V`, `productNorm` is nonnegative. -/
theorem productNorm_nonneg [IsBoundedSMul A V] (z : CompletedTensor A V W) :
    0 ≤ productNorm A V W z :=
  productNorm_nonneg_of_bounded TauCeti.exists_norm_smul_le z

/-- `productNorm` is invariant under negation. -/
theorem productNorm_neg_of_bounded
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (z : CompletedTensor A V W) : productNorm A V W (-z) = productNorm A V W z := by
  refine (denseRange_toCompletion A V W).induction_on z
    (isClosed_eq ((continuous_productNorm A V W).comp continuous_neg)
      (continuous_productNorm A V W)) fun u ↦ ?_
  rw [← map_neg, productNorm_toCompletion_of_bounded hV, productNorm_toCompletion_of_bounded hV,
    map_neg_eq_map]

/-- Under a contractive `A`-action on `V`, `productNorm` is invariant under negation. -/
@[simp]
theorem productNorm_neg [IsBoundedSMul A V] (z : CompletedTensor A V W) :
    productNorm A V W (-z) = productNorm A V W z :=
  productNorm_neg_of_bounded TauCeti.exists_norm_smul_le z

/-- **Ultrametric inequality** for `productNorm` on `V ⊗̂_A W`. -/
theorem productNorm_add_le_max_of_bounded
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (z₁ z₂ : CompletedTensor A V W) :
    productNorm A V W (z₁ + z₂) ≤ max (productNorm A V W z₁) (productNorm A V W z₂) := by
  have hclosed₁ : ∀ u₁ : V ⊗[A] W,
      productNorm A V W (toCompletion A V W u₁ + z₂) ≤
        max (productNorm A V W (toCompletion A V W u₁)) (productNorm A V W z₂) := fun u₁ ↦ by
    refine (denseRange_toCompletion A V W).induction_on z₂
      (isClosed_le ((continuous_productNorm A V W).comp (continuous_const.add continuous_id))
        (continuous_const.max (continuous_productNorm A V W))) fun u₂ ↦ ?_
    rw [← map_add, productNorm_toCompletion_of_bounded hV,
      productNorm_toCompletion_of_bounded hV, productNorm_toCompletion_of_bounded hV]
    exact productSeminorm_add_le_max u₁ u₂
  exact (denseRange_toCompletion A V W).induction_on z₁
    (isClosed_le ((continuous_productNorm A V W).comp (continuous_id.add continuous_const))
      ((continuous_productNorm A V W).max continuous_const)) hclosed₁

/-- Under a contractive `A`-action on `V`, `productNorm` satisfies the ultrametric inequality. -/
theorem productNorm_add_le_max [IsBoundedSMul A V] (z₁ z₂ : CompletedTensor A V W) :
    productNorm A V W (z₁ + z₂) ≤ max (productNorm A V W z₁) (productNorm A V W z₂) :=
  productNorm_add_le_max_of_bounded TauCeti.exists_norm_smul_le z₁ z₂

/-- Ultrametric inequality for differences under `productNorm`. -/
theorem productNorm_sub_le_max_of_bounded
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (z₁ z₂ : CompletedTensor A V W) :
    productNorm A V W (z₁ - z₂) ≤ max (productNorm A V W z₁) (productNorm A V W z₂) := by
  simpa [sub_eq_add_neg, productNorm_neg_of_bounded hV] using
    productNorm_add_le_max_of_bounded hV z₁ (-z₂)

/-- Under a contractive `A`-action on `V`, `productNorm` satisfies the ultrametric inequality on
differences. -/
theorem productNorm_sub_le_max [IsBoundedSMul A V] (z₁ z₂ : CompletedTensor A V W) :
    productNorm A V W (z₁ - z₂) ≤ max (productNorm A V W z₁) (productNorm A V W z₂) :=
  productNorm_sub_le_max_of_bounded TauCeti.exists_norm_smul_le z₁ z₂

/-- On elementary tensors `v ⊗ w`, `productNorm` is at most `‖v‖ * ‖w‖`. -/
theorem productNorm_tmul_le_of_bounded
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) (v : V) (w : W) :
    productNorm A V W (tmul A V W v w) ≤ ‖v‖ * ‖w‖ := by
  rw [← toCompletion_tmul, productNorm_toCompletion_of_bounded hV]
  exact productSeminorm_tmul_le v w

/-- Under a contractive `A`-action on `V`, `productNorm A V W (tmul A V W v w) ≤ ‖v‖ * ‖w‖`. -/
theorem productNorm_tmul_le [IsBoundedSMul A V] (v : V) (w : W) :
    productNorm A V W (tmul A V W v w) ≤ ‖v‖ * ‖w‖ :=
  productNorm_tmul_le_of_bounded TauCeti.exists_norm_smul_le v w

/-- **Infinite-sum bound for `productNorm`**: if `HasSum f z` in `V ⊗̂_A W` and every term has
`productNorm` at most `b ≥ 0`, then `productNorm A V W z ≤ b`. -/
theorem productNorm_le_of_hasSum
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    {ι : Type*} {f : ι → CompletedTensor A V W} {z : CompletedTensor A V W} (hf : HasSum f z)
    {b : ℝ} (hb : 0 ≤ b) (hfb : ∀ i, productNorm A V W (f i) ≤ b) :
    productNorm A V W z ≤ b := by
  have hsum_fin (s : Finset ι) : productNorm A V W (∑ i ∈ s, f i) ≤ b :=
    apply_sum_le_of_isNonarchimedean (productNorm_zero_of_bounded hV)
      (productNorm_add_le_max_of_bounded hV) s f hb fun i _ ↦ hfb i
  have hT : Tendsto (fun s : Finset ι ↦ productNorm A V W (∑ i ∈ s, f i))
      atTop (𝓝 (productNorm A V W z)) :=
    ((continuous_productNorm A V W).tendsto z).comp
      (by simpa only [HasSum, SummationFilter.unconditional_filter] using hf)
  exact le_of_tendsto hT (Eventually.of_forall hsum_fin)

/-- If `a : A` scales norms on `V` by at most `C ≥ 0`, it scales `productNorm` on `V ⊗̂_A W` by at
most `C`. -/
theorem productNorm_smul_le_of_le
    (hV : ∃ C₀ : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C₀ * ‖a‖ * ‖v‖)
    {a : A} {C : ℝ} (hC : 0 ≤ C) (ha : ∀ v : V, ‖a • v‖ ≤ C * ‖v‖)
    (z : CompletedTensor A V W) :
    productNorm A V W (a • z) ≤ C * productNorm A V W z := by
  refine (denseRange_toCompletion A V W).induction_on z
    (isClosed_le ((continuous_productNorm A V W).comp (continuous_const_smul a))
      (continuous_const.mul (continuous_productNorm A V W))) fun u ↦ ?_
  rw [← map_smul, productNorm_toCompletion_of_bounded hV, productNorm_toCompletion_of_bounded hV]
  exact productSeminorm_smul_le_of_le_left hC ha u

/-- If `a : A` scales norms on `W` by at most `C ≥ 0`, it scales `productNorm` on `V ⊗̂_A W` by at
most `C`. -/
theorem productNorm_smul_le_of_le_right
    (hW : ∃ C₀ : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C₀ * ‖a‖ * ‖w‖)
    {a : A} {C : ℝ} (hC : 0 ≤ C) (ha : ∀ w : W, ‖a • w‖ ≤ C * ‖w‖)
    (z : CompletedTensor A V W) :
    productNorm A V W (a • z) ≤ C * productNorm A V W z := by
  refine (denseRange_toCompletion A V W).induction_on z
    (isClosed_le ((continuous_productNorm A V W).comp (continuous_const_smul a))
      (continuous_const.mul (continuous_productNorm A V W))) fun u ↦ ?_
  rw [← map_smul, productNorm_toCompletion_of_bounded_right hW,
    productNorm_toCompletion_of_bounded_right hW]
  exact productSeminorm_smul_le_of_le_right hC ha u

/-- Under a contractive `A`-action on `V`, `productNorm` is submultiplicative for scalar
multiplication. -/
theorem productNorm_smul_le [IsBoundedSMul A V] (a : A) (z : CompletedTensor A V W) :
    productNorm A V W (a • z) ≤ ‖a‖ * productNorm A V W z :=
  productNorm_smul_le_of_le TauCeti.exists_norm_smul_le (norm_nonneg a) (norm_smul_le a) z

/-- Under a contractive `A`-action on `W`, `productNorm` is submultiplicative for scalar
multiplication. -/
theorem productNorm_smul_le_of_right [IsBoundedSMul A W] (a : A) (z : CompletedTensor A V W) :
    productNorm A V W (a • z) ≤ ‖a‖ * productNorm A V W z :=
  productNorm_smul_le_of_le_right TauCeti.exists_norm_smul_le (norm_nonneg a) (norm_smul_le a) z

/-- **Universal norm bound on `CompletedTensor.lift`**: for a bounded `A`-bilinear map `β` into a
complete ultrametric normed `A`-module `M` with continuous action, the lifted continuous linear
map satisfies `‖lift β hβ z‖ ≤ C * productNorm A V W z`. -/
theorem norm_lift_le_mul_productNorm
    (hV : ∃ C₀ : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C₀ * ‖a‖ * ‖v‖)
    {M : Type*} [NormedAddCommGroup M] [IsUltrametricDist M] [CompleteSpace M]
    [Module A M] [ContinuousSMul A M] (β : V →ₗ[A] W →ₗ[A] M)
    (hβ : Continuous fun p : V × W ↦ β p.1 p.2) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ v w, ‖β v w‖ ≤ C * (‖v‖ * ‖w‖)) (z : CompletedTensor A V W) :
    ‖lift β hβ z‖ ≤ C * productNorm A V W z := by
  refine (denseRange_toCompletion A V W).induction_on z
    (isClosed_le (continuous_norm.comp (lift β hβ).continuous)
      (continuous_const.mul (continuous_productNorm A V W))) fun u ↦ ?_
  rw [lift_toCompletion, productNorm_toCompletion_of_bounded hV]
  exact norm_lift_le_mul_productSeminorm β hC hbound u

/-- A completed tensor product of bounded continuous `A`-linear maps `f : V →L[A] V'` and
`g : W →L[A] W'` scales `productNorm` by at most `C₁ * C₂`. -/
theorem productNorm_map_le_of_bounded {V' W' : Type*}
    [SeminormedAddCommGroup V'] [Module A V'] [SeminormedAddCommGroup W'] [Module A W']
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hV' : ∃ C : ℝ≥0, ∀ (a : A) (v' : V'), ‖a • v'‖ ≤ C * ‖a‖ * ‖v'‖)
    (f : V →L[A] V') (g : W →L[A] W') {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hf : ∀ v, ‖f v‖ ≤ C₁ * ‖v‖) (hg : ∀ w, ‖g w‖ ≤ C₂ * ‖w‖)
    (z : CompletedTensor A V W) :
    productNorm A V' W' (map f g z) ≤ C₁ * C₂ * productNorm A V W z := by
  refine (denseRange_toCompletion A V W).induction_on z
    (isClosed_le ((continuous_productNorm A V' W').comp (map f g).continuous)
      (continuous_const.mul (continuous_productNorm A V W))) fun u ↦ ?_
  rw [map_toCompletion, productNorm_toCompletion_of_bounded hV',
    productNorm_toCompletion_of_bounded hV]
  exact productSeminorm_map_le f.toLinearMap g.toLinearMap hC₁ hC₂ hf hg u

/-- Under contractive `A`-actions on the left factors, `CompletedTensor.map f g` scales
`productNorm` by at most the product `C₁ * C₂` of bounds for `f` and `g`. -/
theorem productNorm_map_le {V' W' : Type*}
    [SeminormedAddCommGroup V'] [Module A V'] [IsBoundedSMul A V] [IsBoundedSMul A V']
    [SeminormedAddCommGroup W'] [Module A W']
    (f : V →L[A] V') (g : W →L[A] W') {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hf : ∀ v, ‖f v‖ ≤ C₁ * ‖v‖) (hg : ∀ w, ‖g w‖ ≤ C₂ * ‖w‖)
    (z : CompletedTensor A V W) :
    productNorm A V' W' (map f g z) ≤ C₁ * C₂ * productNorm A V W z :=
  productNorm_map_le_of_bounded TauCeti.exists_norm_smul_le TauCeti.exists_norm_smul_le
    f g hC₁ hC₂ hf hg z

/-- Exchanging the factors via `CompletedTensor.comm` preserves `productNorm` whenever `A` acts
boundedly on `V`. -/
theorem productNorm_comm_of_bounded
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (z : CompletedTensor A V W) :
    productNorm A W V (comm A V W z) = productNorm A V W z := by
  refine (denseRange_toCompletion A V W).induction_on z
    (isClosed_eq ((continuous_productNorm A W V).comp (comm A V W).continuous)
      (continuous_productNorm A V W)) fun u ↦ ?_
  rw [comm_toCompletion, productNorm_toCompletion_of_bounded_right hV,
    productNorm_toCompletion_of_bounded hV, productSeminorm_comm]

/-- Under a contractive `A`-action on `V`, `CompletedTensor.comm` preserves `productNorm`. -/
@[simp]
theorem productNorm_comm [IsBoundedSMul A V] (z : CompletedTensor A V W) :
    productNorm A W V (comm A V W z) = productNorm A V W z :=
  productNorm_comm_of_bounded TauCeti.exists_norm_smul_le z

/-- On `A ⊗̂_A M` for a complete ultrametric normed `A`-module `M` with contractive action over a
norm-one commutative ring `A`, `productNorm` is the norm of the image under `lid A M`. -/
theorem productNorm_eq_norm_lid [NormOneClass A] {M : Type*} [NormedAddCommGroup M]
    [IsUltrametricDist M] [CompleteSpace M] [Module A M] [IsBoundedSMul A M]
    (z : CompletedTensor A A M) : productNorm A A M z = ‖lid A M z‖ := by
  refine (denseRange_toCompletion A A M).induction_on z
    (isClosed_eq (continuous_productNorm A A M) (continuous_norm.comp (lid A M).continuous))
    fun u ↦ ?_
  rw [productNorm_toCompletion, lid_toCompletion, productSeminorm_eq_norm_lid]

/-- On `M ⊗̂_A A` for a complete ultrametric normed `A`-module `M` with contractive action over a
norm-one commutative ring `A`, `productNorm` is the norm of the image under `rid A M`. -/
theorem productNorm_eq_norm_rid [NormOneClass A] {M : Type*} [NormedAddCommGroup M]
    [IsUltrametricDist M] [CompleteSpace M] [Module A M] [IsBoundedSMul A M]
    (z : CompletedTensor A M A) : productNorm A M A z = ‖rid A M z‖ := by
  refine (denseRange_toCompletion A M A).induction_on z
    (isClosed_eq (continuous_productNorm A M A) (continuous_norm.comp (rid A M).continuous))
    fun u ↦ ?_
  rw [productNorm_toCompletion, rid_toCompletion, productSeminorm_eq_norm_rid]

end Bounded

section IsTateCompletion

/-- When a uniform additive group structure on `V ⊗[A] W` agrees with that of `productSeminorm`,
the open balls of `Completion.extension (productSeminorm A V W)` form a neighbourhood basis of `0`
in `Completion (V ⊗[A] W)`. -/
private theorem hasBasis_nhds_zero_completion_productSeminorm {A V W : Type*} [CommRing A]
    [SeminormedAddCommGroup V] [Module A V] [SeminormedAddCommGroup W] [Module A W]
    [u : UniformSpace (V ⊗[A] W)] [hu_grp : IsUniformAddGroup (V ⊗[A] W)]
    (hu : u = (productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace) :
    (𝓝 (0 : Completion (V ⊗[A] W))).HasBasis (0 < ·)
      fun r ↦ {w | Completion.extension (productSeminorm A V W) w < r} := by
  subst hu
  have hgrp : hu_grp = @SeminormedAddCommGroup.to_isUniformAddGroup (V ⊗[A] W)
      (productSeminorm A V W).toSeminormedAddCommGroup :=
    Subsingleton.elim _ _
  subst hgrp
  let : SeminormedAddCommGroup (V ⊗[A] W) := (productSeminorm A V W).toSeminormedAddCommGroup
  have hnorm (w : Completion (V ⊗[A] W)) :
      ‖w‖ = Completion.extension (productSeminorm A V W) w := rfl
  refine (Metric.nhds_basis_ball (x := (0 : Completion (V ⊗[A] W)))).congr (fun _ ↦ Iff.rfl)
    fun r _ ↦ ?_
  ext w
  simp [Metric.mem_ball, dist_zero_right, hnorm]

variable {A V W : Type*} [SeminormedCommRing A] [TauCeti.NormedRing.IsTate A]
  [SeminormedAddCommGroup V] [Module A V] [SeminormedAddCommGroup W] [Module A W]

/-- **Norm-ball basis of the completion topology**: over a Tate seminormed commutative ring `A`
acting boundedly on `V` and `W`, the positive-radius open balls of `productNorm A V W` form a
neighbourhood basis of `0` in `CompletedTensor A V W`. -/
theorem hasBasis_nhds_zero_productNorm_of_bounded
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    (𝓝 (0 : CompletedTensor A V W)).HasBasis (0 < ·)
      fun r ↦ {z | productNorm A V W z < r} := by
  let : UniformSpace (V ⊗[A] W) := banachTensorUniformSpace A V W
  have : IsUniformAddGroup (V ⊗[A] W) := isUniformAddGroup_banachTensorUniformSpace A V W
  have hb := hasBasis_nhds_zero_completion_productSeminorm
    (banachTensorUniformSpace_eq_productSeminorm hV hW)
  rw [nhds_eq_comap_equivCompletion A V W 0, map_zero]
  exact hb.comap (equivCompletion A V W)

/-- Under contractive `A`-actions over a Tate seminormed commutative ring `A`, the positive-radius
open balls of `productNorm A V W` form a neighbourhood basis of `0` in `CompletedTensor A V W`. -/
theorem hasBasis_nhds_zero_productNorm [IsBoundedSMul A V] [IsBoundedSMul A W] :
    (𝓝 (0 : CompletedTensor A V W)).HasBasis (0 < ·)
      fun r ↦ {z | productNorm A V W z < r} :=
  hasBasis_nhds_zero_productNorm_of_bounded
    TauCeti.exists_norm_smul_le TauCeti.exists_norm_smul_le

/-- Bundled `AddGroupNorm` on `V ⊗̂_A W` induced by `productNorm` over a Tate seminormed
commutative ring `A` acting boundedly on `V` and `W`. -/
noncomputable def productNormAddGroupNorm
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    AddGroupNorm (CompletedTensor A V W) where
  toFun := productNorm A V W
  map_zero' := productNorm_zero_of_bounded hV
  add_le' z₁ z₂ := (productNorm_add_le_max_of_bounded hV z₁ z₂).trans
    (max_le_add_of_nonneg (productNorm_nonneg_of_bounded hV z₁)
      (productNorm_nonneg_of_bounded hV z₂))
  neg' := productNorm_neg_of_bounded hV
  eq_zero_of_map_eq_zero' z hz := by
    by_contra hne
    obtain ⟨r, hr, hsub⟩ := (hasBasis_nhds_zero_productNorm_of_bounded hV hW).mem_iff.mp
      (isOpen_compl_singleton.mem_nhds (Ne.symm hne))
    exact hsub (by simp [hz, hr]) rfl

/-- `productNormAddGroupNorm` evaluates to `productNorm A V W`. -/
@[simp]
theorem productNormAddGroupNorm_apply
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖)
    (z : CompletedTensor A V W) :
    productNormAddGroupNorm hV hW z = productNorm A V W z :=
  (rfl)

/-- **Definiteness of `productNorm`** on `V ⊗̂_A W` over a Tate seminormed commutative ring with
bounded module actions. -/
theorem productNorm_eq_zero_iff_of_bounded
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖)
    {z : CompletedTensor A V W} :
    productNorm A V W z = 0 ↔ z = 0 :=
  map_eq_zero_iff_eq_zero (productNormAddGroupNorm hV hW)

/-- Under contractive `A`-actions over a Tate seminormed commutative ring `A`,
`productNorm A V W z = 0 ↔ z = 0`. -/
@[simp]
theorem productNorm_eq_zero_iff [IsBoundedSMul A V] [IsBoundedSMul A W]
    {z : CompletedTensor A V W} : productNorm A V W z = 0 ↔ z = 0 :=
  productNorm_eq_zero_iff_of_bounded TauCeti.exists_norm_smul_le TauCeti.exists_norm_smul_le

/-- The uniformity of `CompletedTensor A V W` agrees with that induced by
`productNormAddGroupNorm`. -/
theorem uniformity_eq_productNorm
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    𝓤 (CompletedTensor A V W) =
      @uniformity (CompletedTensor A V W)
        (productNormAddGroupNorm hV hW).toNormedAddCommGroup.toUniformSpace :=
  (productNormAddGroupNorm hV hW).uniformity_eq_of_hasBasis_nhds_zero
    (hasBasis_nhds_zero_productNorm_of_bounded hV hW)

/-- **Compatible `NormedAddCommGroup` structure** on `V ⊗̂_A W` over a Tate seminormed commutative
ring `A` acting boundedly on `V` and `W`, with norm `productNorm A V W` and with the existing
uniformity and topology of `CompletedTensor A V W` retained definitionally. -/
noncomputable abbrev productNormedAddCommGroup
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    NormedAddCommGroup (CompletedTensor A V W) :=
  (productNormAddGroupNorm hV hW).toNormedAddCommGroupOfUniformity (uniformity_eq_productNorm hV hW)

/-- The norm of `productNormedAddCommGroup` is `productNorm A V W`. -/
@[simp]
theorem norm_productNormedAddCommGroup
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖)
    (z : CompletedTensor A V W) :
    @norm (CompletedTensor A V W) (productNormedAddCommGroup hV hW).toNorm z =
      productNorm A V W z :=
  (productNormAddGroupNorm hV hW).norm_toNormedAddCommGroupOfUniformity
    (uniformity_eq_productNorm hV hW) z

/-- `productNormedAddCommGroup` retains the existing uniform space of `CompletedTensor A V W`. -/
@[simp]
theorem uniformSpace_productNormedAddCommGroup
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    (productNormedAddCommGroup hV hW).toUniformSpace =
      (inferInstance : UniformSpace (CompletedTensor A V W)) :=
  (rfl)

/-- `productNormedAddCommGroup` is ultrametric. -/
theorem isUltrametricDist_productNormedAddCommGroup
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    letI := productNormedAddCommGroup hV hW
    IsUltrametricDist (CompletedTensor A V W) := by
  have hadd := productNorm_add_le_max_of_bounded hV (W := W)
  let := productNormedAddCommGroup hV hW
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm hadd

/-- Under a contractive `A`-action on `V`, `A` acts contractively on `CompletedTensor A V W`
equipped with `productNormedAddCommGroup`. -/
theorem isBoundedSMul_productNormedAddCommGroup [IsBoundedSMul A V]
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    letI := productNormedAddCommGroup hV hW
    IsBoundedSMul A (CompletedTensor A V W) := by
  have hsmul := productNorm_smul_le (A := A) (V := V) (W := W)
  let := productNormedAddCommGroup hV hW
  exact IsBoundedSMul.of_norm_smul_le hsmul

/-- Under a contractive `A`-action on `W`, `A` acts contractively on `CompletedTensor A V W`
equipped with `productNormedAddCommGroup`. -/
theorem isBoundedSMul_productNormedAddCommGroup_of_right [IsBoundedSMul A W]
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    letI := productNormedAddCommGroup hV hW
    IsBoundedSMul A (CompletedTensor A V W) := by
  have hsmul := productNorm_smul_le_of_right (A := A) (V := V) (W := W)
  let := productNormedAddCommGroup hV hW
  exact IsBoundedSMul.of_norm_smul_le hsmul

end IsTateCompletion

section NormedFieldCompletion

/-- Over a normed field `L`, `productNorm` is homogeneous under scalar multiplication. -/
@[simp]
theorem productNorm_smul {L V W : Type*} [NormedField L]
    [SeminormedAddCommGroup V] [NormedSpace L V]
    [SeminormedAddCommGroup W] [Module L W]
    (a : L) (z : CompletedTensor L V W) :
    productNorm L V W (a • z) = ‖a‖ * productNorm L V W z := by
  refine (denseRange_toCompletion L V W).induction_on z
    (isClosed_eq ((continuous_productNorm L V W).comp (continuous_const_smul a))
      (continuous_const.mul (continuous_productNorm L V W))) fun u ↦ ?_
  rw [← map_smul, productNorm_toCompletion, productNorm_toCompletion, productSeminorm_smul]

variable {L V W : Type*} [NontriviallyNormedField L] [SeminormedAddCommGroup V] [NormedSpace L V]
  [SeminormedAddCommGroup W] [NormedSpace L W]

/-- Over a nontrivially normed field `L`, `CompletedTensor L V W` equipped with
`productNormedAddCommGroup` is a `NormedSpace` over `L`, retaining its existing `L`-module
structure definitionally. -/
noncomputable abbrev productNormedSpace
    (hV : ∃ C : ℝ≥0, ∀ (a : L) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : L) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    @NormedSpace L (CompletedTensor L V W) _
      (productNormedAddCommGroup hV hW).toSeminormedAddCommGroup :=
  letI : NormedAddCommGroup (CompletedTensor L V W) := productNormedAddCommGroup hV hW
  { (inferInstance : Module L (CompletedTensor L V W)) with
    norm_smul_le a z := by
      rw [norm_productNormedAddCommGroup, norm_productNormedAddCommGroup, productNorm_smul] }

/-- Bundled structure theorem for `productNorm` over a nontrivially normed field: nonnegativity,
definiteness, the ultrametric inequality, scalar homogeneity, and the norm-ball neighbourhood basis
of zero. -/
theorem productNorm_structure :
    (∀ z : CompletedTensor L V W, 0 ≤ productNorm L V W z) ∧
      (∀ z : CompletedTensor L V W, productNorm L V W z = 0 ↔ z = 0) ∧
      (∀ z₁ z₂ : CompletedTensor L V W,
        productNorm L V W (z₁ + z₂) ≤ max (productNorm L V W z₁) (productNorm L V W z₂)) ∧
      (∀ (a : L) (z : CompletedTensor L V W),
        productNorm L V W (a • z) = ‖a‖ * productNorm L V W z) ∧
      (𝓝 (0 : CompletedTensor L V W)).HasBasis (0 < ·)
        fun r ↦ {z | productNorm L V W z < r} :=
  ⟨productNorm_nonneg, fun _ ↦ productNorm_eq_zero_iff, productNorm_add_le_max,
    productNorm_smul, hasBasis_nhds_zero_productNorm⟩

end NormedFieldCompletion

section CompleteFieldCompletion

section Seminormed

variable {L V W : Type*} [NontriviallyNormedField L] [CompleteSpace L]
  [SeminormedAddCommGroup V] [NormedSpace L V] [IsUltrametricDist V]
  [SeminormedAddCommGroup W] [NormedSpace L W] [IsUltrametricDist W]

/-- **Cross-norm on elementary completed tensors**: for ultrametric seminormed `L`-spaces `V` and
`W` over a complete nontrivially normed field `L`, `productNorm L V W (tmul L V W v w) = ‖v‖ * ‖w‖`.
-/
@[simp]
theorem productNorm_tmul (v : V) (w : W) :
    productNorm L V W (tmul L V W v w) = ‖v‖ * ‖w‖ := by
  rw [← toCompletion_tmul, productNorm_toCompletion, productSeminorm_tmul]

/-- **Unit-vector distance formula** on `V ⊗̂_L W`: for ultrametric seminormed `L`-spaces `V` and
`W` over a complete nontrivially normed field `L`, when `‖w‖ = 1`, tensoring on the right by `w`
is isometric, `productNorm L V W (tmul L V W v w - tmul L V W v' w) = ‖v - v'‖`. -/
theorem productNorm_tmul_sub_tmul_of_norm_eq_one (v v' : V) {w : W} (hw : ‖w‖ = 1) :
    productNorm L V W (tmul L V W v w - tmul L V W v' w) = ‖v - v'‖ := by
  have hsub : tmul L V W v w - tmul L V W v' w = tmul L V W (v - v') w := by
    rw [← LinearMap.sub_apply, map_sub]
  rw [hsub, productNorm_tmul, hw, mul_one]

end Seminormed

section Normed

variable {L V W : Type*} [NontriviallyNormedField L] [CompleteSpace L]
  [NormedAddCommGroup V] [NormedSpace L V] [IsUltrametricDist V]
  [NormedAddCommGroup W] [NormedSpace L W] [IsUltrametricDist W]

variable (L V W) in
/-- **Injectivity of the canonical map into the completed tensor product**: for ultrametric normed
`L`-spaces `V` and `W` over a complete nontrivially normed field `L` (KL15, Lemma 2.2.9(a)),
`toCompletion L V W : V ⊗[L] W → V ⊗̂_L W` is injective. -/
theorem toCompletion_injective : Function.Injective (toCompletion L V W) := by
  refine (injective_iff_map_eq_zero (toCompletion L V W)).mpr fun u hu ↦ ?_
  have hnorm : productSeminorm L V W u = 0 := by
    rw [← productNorm_toCompletion, hu, productNorm_zero]
  exact productSeminorm_eq_zero_iff.mp hnorm

end Normed

end CompleteFieldCompletion

end CompletedTensor

end TauCeti.Huber.BanachModule
