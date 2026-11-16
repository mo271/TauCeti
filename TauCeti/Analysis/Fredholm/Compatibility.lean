/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.Fredholm.Adjoint
public import TauCeti.Analysis.Fredholm.Basic
public import TauCeti.LinearAlgebra.Dual.CommonKernel
import TauCeti.Analysis.Normed.Lp.Reindex

/-!
# Compatibility conditions and the index-zero Fredholm alternative

This file develops the index-zero Fredholm alternative and the adjoint-kernel compatibility
conditions for closed-range and Fredholm operators between Hilbert spaces.

For a continuous linear map `T : E →L[𝕜] F` with finite-dimensional kernel and cokernel, having
index zero is equivalent to `finrank 𝕜 T.ker = finrank 𝕜 (F ⧸ T.range)`. Consuming
`ContinuousLinearMap.bijective_of_surjective_of_index_eq_zero` and
`ContinuousLinearMap.bijective_of_injective_of_index_eq_zero`, injectivity, surjectivity, and
bijectivity become equivalent at index zero, and `T.index = 0` is equivalent to the dichotomy that
either `T` is bijective or both `T.ker ≠ ⊥` and `T.range ≠ ⊤` with equal kernel and cokernel
dimensions (`ContinuousLinearMap.IsFredholm.index_eq_zero_iff_bijective_or`). Dropping the
dimension equality fails: the backward shift on `ℓ²(ℕ, 𝕜)` is Fredholm and surjective with
one-dimensional kernel `𝕜 ∙ δ₀` and index `1 ≠ 0`
(`TauCeti.exists_isFredholm_surjective_ker_ne_bot_index_eq_one`), while `0 : 𝕜 →L[𝕜] 𝕜 × 𝕜` has
cokernel dimension `2`, kernel dimension `1`, and index `-1 ≠ 0`
(`TauCeti.zero_prod_isFredholm_and_index_eq_neg_one`).

For a Hilbert-space operator `T : E →L[𝕜] F` with closed range, `range T = (ker T†)ᗮ`, so `T x = y`
is solvable if and only if `⟪z, y⟫ = 0` for every `z ∈ ker T†`
(`ContinuousLinearMap.mem_range_iff_forall_inner_ker_adjoint_eq_zero_of_isClosed_range`). When `T`
is Fredholm, evaluating against a basis of `ker T†` produces `finrank 𝕜 (F ⧸ T.range)` linearly
independent continuous linear compatibility functionals cutting out `range T`
(`ContinuousLinearMap.IsFredholm.exists_compatibilityFunctionals`). By
`TauCeti.LinearAlgebra.Dual.CommonKernel`, this number is minimal among all finite or arbitrary
families of (not necessarily continuous) linear functionals whose common kernel is `range T`, and
equals `finrank 𝕜 T.ker` if and only if `(T : E →ₗ[𝕜] F).index = 0`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Chapter 6.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix A.1.
* W. Rudin, *Functional Analysis*, 2nd ed., Chapter 4.
-/

public section

open Module
open scoped InnerProduct InnerProductSpace ENNReal

namespace LinearMap

variable {𝕜 M N : Type*} [DivisionRing 𝕜] [AddCommGroup M] [Module 𝕜 M]
  [AddCommGroup N] [Module 𝕜 N]

/-- A linear map has index zero if and only if its kernel and cokernel have the same `finrank`. -/
theorem index_eq_zero_iff_finrank_ker_eq (f : M →ₗ[𝕜] N) :
    f.index = 0 ↔ finrank 𝕜 f.ker = finrank 𝕜 (N ⧸ f.range) := by
  rw [index_eq_finrank_sub, sub_eq_zero, Nat.cast_inj]

/-- Symmetric form of `LinearMap.index_eq_zero_iff_finrank_ker_eq`. -/
theorem finrank_coker_eq_finrank_ker_iff_index_eq_zero (f : M →ₗ[𝕜] N) :
    finrank 𝕜 (N ⧸ f.range) = finrank 𝕜 f.ker ↔ f.index = 0 := by
  rw [index_eq_zero_iff_finrank_ker_eq, eq_comm]

/-- A surjective linear map of index zero with finite-dimensional kernel is bijective. -/
theorem bijective_of_surjective_of_index_eq_zero {f : M →ₗ[𝕜] N} [FiniteDimensional 𝕜 f.ker]
    (hf : Function.Surjective f) (h0 : f.index = 0) : Function.Bijective f := by
  have hker0 : finrank 𝕜 f.ker = 0 := by
    have := f.index_of_surjective hf
    omega
  exact ⟨ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker0), hf⟩

/-- An injective linear map of index zero with finite-dimensional cokernel is bijective. -/
theorem bijective_of_injective_of_index_eq_zero {f : M →ₗ[𝕜] N} [FiniteDimensional 𝕜 (N ⧸ f.range)]
    (hf : Function.Injective f) (h0 : f.index = 0) : Function.Bijective f := by
  have hcoker0 : finrank 𝕜 (N ⧸ f.range) = 0 := by
    have := f.index_of_injective hf
    omega
  have hrange : f.range = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp (finrank_zero_iff.mp hcoker0)
  exact ⟨hf, range_eq_top.mp hrange⟩

/-- At index zero with finite-dimensional cokernel, bijectivity is equivalent to injectivity. -/
theorem bijective_iff_injective_of_index_eq_zero {f : M →ₗ[𝕜] N} [FiniteDimensional 𝕜 (N ⧸ f.range)]
    (h0 : f.index = 0) : Function.Bijective f ↔ Function.Injective f :=
  ⟨Function.Bijective.injective, fun hf ↦ bijective_of_injective_of_index_eq_zero hf h0⟩

/-- At index zero with finite-dimensional kernel, bijectivity is equivalent to surjectivity. -/
theorem bijective_iff_surjective_of_index_eq_zero {f : M →ₗ[𝕜] N} [FiniteDimensional 𝕜 f.ker]
    (h0 : f.index = 0) : Function.Bijective f ↔ Function.Surjective f :=
  ⟨Function.Bijective.surjective, fun hf ↦ bijective_of_surjective_of_index_eq_zero hf h0⟩

/-- At index zero with finite-dimensional kernel and cokernel, injectivity and surjectivity are
equivalent. -/
theorem injective_iff_surjective_of_index_eq_zero {f : M →ₗ[𝕜] N} [FiniteDimensional 𝕜 f.ker]
    [FiniteDimensional 𝕜 (N ⧸ f.range)] (h0 : f.index = 0) :
    Function.Injective f ↔ Function.Surjective f :=
  (bijective_iff_injective_of_index_eq_zero h0).symm.trans
    (bijective_iff_surjective_of_index_eq_zero h0)

/-- **Algebraic index-zero alternative.** For a linear map with finite-dimensional kernel and
cokernel, having index zero is equivalent to either being bijective or having nontrivial kernel and
proper range with `finrank 𝕜 (N ⧸ f.range) = finrank 𝕜 f.ker`. -/
theorem index_eq_zero_iff_bijective_or (f : M →ₗ[𝕜] N) [FiniteDimensional 𝕜 f.ker]
    [FiniteDimensional 𝕜 (N ⧸ f.range)] :
    f.index = 0 ↔ Function.Bijective f ∨
      (f.ker ≠ ⊥ ∧ f.range ≠ ⊤ ∧ finrank 𝕜 (N ⧸ f.range) = finrank 𝕜 f.ker) := by
  constructor
  · intro h0
    by_cases hker : f.ker = ⊥
    · exact Or.inl (bijective_of_injective_of_index_eq_zero (ker_eq_bot.mp hker) h0)
    · refine Or.inr ⟨hker, fun htop ↦ hker ?_,
        ((index_eq_zero_iff_finrank_ker_eq f).mp h0).symm⟩
      exact ker_eq_bot.mpr
        (bijective_of_surjective_of_index_eq_zero (range_eq_top.mp htop) h0).injective
  · rintro (hbij | ⟨_, _, hdim⟩)
    · exact f.index_of_bijective hbij
    · exact (finrank_coker_eq_finrank_ker_iff_index_eq_zero f).mp hdim

end LinearMap

namespace ContinuousLinearMap

section DivisionRing

variable {𝕜 E F : Type*} [DivisionRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- A continuous linear map has index zero if and only if its kernel and cokernel have the same
`finrank`. -/
theorem index_eq_zero_iff_finrank_ker_eq (T : E →L[𝕜] F) :
    T.index = 0 ↔ finrank 𝕜 T.ker = finrank 𝕜 (F ⧸ T.range) := by
  rw [index_def]
  exact (T : E →ₗ[𝕜] F).index_eq_zero_iff_finrank_ker_eq

/-- Symmetric form of `ContinuousLinearMap.index_eq_zero_iff_finrank_ker_eq`. -/
theorem finrank_coker_eq_finrank_ker_iff_index_eq_zero (T : E →L[𝕜] F) :
    finrank 𝕜 (F ⧸ T.range) = finrank 𝕜 T.ker ↔ T.index = 0 := by
  rw [index_def]
  exact (T : E →ₗ[𝕜] F).finrank_coker_eq_finrank_ker_iff_index_eq_zero

/-- At index zero with finite-dimensional cokernel, bijectivity is equivalent to injectivity. -/
theorem bijective_iff_injective_of_index_eq_zero (T : E →L[𝕜] F)
    [FiniteDimensional 𝕜 (F ⧸ T.range)] (h0 : T.index = 0) :
    Function.Bijective T ↔ Function.Injective T :=
  ⟨Function.Bijective.injective, fun hT ↦ T.bijective_of_injective_of_index_eq_zero hT h0⟩

/-- At index zero with finite-dimensional kernel, bijectivity is equivalent to surjectivity. -/
theorem bijective_iff_surjective_of_index_eq_zero (T : E →L[𝕜] F)
    [FiniteDimensional 𝕜 T.ker] (h0 : T.index = 0) :
    Function.Bijective T ↔ Function.Surjective T :=
  ⟨Function.Bijective.surjective,
    fun hT ↦ T.bijective_of_surjective_of_index_eq_zero inferInstance hT h0⟩

/-- At index zero with finite-dimensional kernel and cokernel, injectivity and surjectivity are
equivalent. -/
theorem injective_iff_surjective_of_index_eq_zero (T : E →L[𝕜] F)
    [FiniteDimensional 𝕜 T.ker] [FiniteDimensional 𝕜 (F ⧸ T.range)] (h0 : T.index = 0) :
    Function.Injective T ↔ Function.Surjective T :=
  (T.bijective_iff_injective_of_index_eq_zero h0).symm.trans
    (T.bijective_iff_surjective_of_index_eq_zero h0)

/-- At index zero with finite-dimensional cokernel, bijectivity is equivalent to `T.ker = ⊥`. -/
theorem bijective_iff_ker_eq_bot_of_index_eq_zero (T : E →L[𝕜] F)
    [FiniteDimensional 𝕜 (F ⧸ T.range)] (h0 : T.index = 0) :
    Function.Bijective T ↔ LinearMap.ker (T : E →ₗ[𝕜] F) = ⊥ :=
  (T.bijective_iff_injective_of_index_eq_zero h0).trans LinearMap.ker_eq_bot.symm

/-- At index zero with finite-dimensional cokernel, unique solvability for every right-hand side is
equivalent to `T.ker = ⊥`. -/
theorem existsUnique_iff_ker_eq_bot_of_index_eq_zero (T : E →L[𝕜] F)
    [FiniteDimensional 𝕜 (F ⧸ T.range)] (h0 : T.index = 0) :
    (∀ y, ∃! x, T x = y) ↔ LinearMap.ker (T : E →ₗ[𝕜] F) = ⊥ :=
  (Function.bijective_iff_existsUnique T).symm.trans
    (T.bijective_iff_ker_eq_bot_of_index_eq_zero h0)

/-- **Index-zero alternative for continuous linear maps.** With finite-dimensional kernel and
cokernel, `T.index = 0` holds if and only if either `T` is bijective or `T` has nontrivial kernel,
proper range, and equal kernel and cokernel dimensions. -/
theorem index_eq_zero_iff_bijective_or (T : E →L[𝕜] F)
    [FiniteDimensional 𝕜 T.ker] [FiniteDimensional 𝕜 (F ⧸ T.range)] :
    T.index = 0 ↔ Function.Bijective T ∨
      (LinearMap.ker (T : E →ₗ[𝕜] F) ≠ ⊥ ∧ LinearMap.range (T : E →ₗ[𝕜] F) ≠ ⊤ ∧
        finrank 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) =
          finrank 𝕜 (LinearMap.ker (T : E →ₗ[𝕜] F))) := by
  rw [index_def]
  exact (T : E →ₗ[𝕜] F).index_eq_zero_iff_bijective_or

/-- **Minimality of compatibility conditions (finite families).** Every finite family of linear
functionals on `F` (continuous or not) whose common kernel is `range T` has at least
`finrank 𝕜 (F ⧸ range T)` members. -/
theorem finrank_coker_le_card_of_iInf_ker_eq_range {ι : Type*} [Fintype ι] (T : E →L[𝕜] F)
    {ℓ : ι → Module.Dual 𝕜 F}
    (hℓ : (⨅ i, LinearMap.ker (ℓ i)) = LinearMap.range (T : E →ₗ[𝕜] F)) :
    finrank 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) ≤ Fintype.card ι :=
  Submodule.finrank_quotient_le_card_of_iInf_ker_eq hℓ

/-- **Cardinal minimality of compatibility conditions.** Under finite cokernel dimension (in
particular when `T` is Fredholm), every family `ℓ : ι → Module.Dual 𝕜 F` (continuous or not) with
common kernel `range T` has `#ι` at least the cardinal rank of `F ⧸ range T` (up to universe lift).
-/
theorem lift_rank_coker_le_lift_mk_of_iInf_ker_eq_range.{u₀, uE, uF, w}
    {𝕜' : Type u₀} {E' : Type uE} {F' : Type uF} {ι : Type w} [DivisionRing 𝕜']
    [AddCommGroup E'] [Module 𝕜' E'] [TopologicalSpace E']
    [AddCommGroup F'] [Module 𝕜' F'] [TopologicalSpace F'] (T : E' →L[𝕜'] F')
    [FiniteDimensional 𝕜' (F' ⧸ LinearMap.range (T : E' →ₗ[𝕜'] F'))] {ℓ : ι → Module.Dual 𝕜' F'}
    (hℓ : (⨅ i, LinearMap.ker (ℓ i)) = LinearMap.range (T : E' →ₗ[𝕜'] F')) :
    Cardinal.lift.{w} (Module.rank 𝕜' (F' ⧸ LinearMap.range (T : E' →ₗ[𝕜'] F'))) ≤
      Cardinal.lift.{uF} (Cardinal.mk ι) :=
  Submodule.lift_rank_quotient_le_lift_mk_of_iInf_ker_eq hℓ

end DivisionRing

section Field

variable {𝕜 E F ι : Type*} [Field 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- A finite family of linear functionals on `F` with common kernel `range T` is linearly
independent if and only if its cardinality equals `finrank 𝕜 (F ⧸ range T)`. -/
theorem linearIndependent_iff_card_eq_finrank_coker_of_iInf_ker_eq_range (T : E →L[𝕜] F)
    [Fintype ι] {ℓ : ι → Module.Dual 𝕜 F}
    (hℓ : (⨅ i, LinearMap.ker (ℓ i)) = LinearMap.range (T : E →ₗ[𝕜] F)) :
    LinearIndependent 𝕜 ℓ ↔ Fintype.card ι = finrank 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) :=
  Submodule.linearIndependent_iff_card_eq_finrank_quotient_of_iInf_ker_eq hℓ

end Field

section Fredholm

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]

/-- **Index-zero Fredholm alternative (equivalence form).** A Fredholm operator `T` has index zero
if and only if either `T` is bijective or `T` has nontrivial kernel, proper range, and
`finrank 𝕜 (F ⧸ T.range) = finrank 𝕜 T.ker`. -/
theorem IsFredholm.index_eq_zero_iff_bijective_or {T : E →L[𝕜] F} (hT : IsFredholm T) :
    T.index = 0 ↔ Function.Bijective T ∨
      (LinearMap.ker (T : E →ₗ[𝕜] F) ≠ ⊥ ∧ LinearMap.range (T : E →ₗ[𝕜] F) ≠ ⊤ ∧
        finrank 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) =
          finrank 𝕜 (LinearMap.ker (T : E →ₗ[𝕜] F))) := by
  have := hT.finite_ker
  have := hT.finite_coker
  exact T.index_eq_zero_iff_bijective_or

/-- **Index-zero Fredholm alternative (invertibility form).** If `T` is Fredholm of index zero, then
either `T` is invertible as a continuous linear map (and bijective) or `T` has nontrivial kernel and
proper range of equal positive finite dimension and codimension. -/
theorem IsFredholm.alternative_of_index_eq_zero {T : E →L[𝕜] F} (hT : IsFredholm T)
    (h0 : T.index = 0) :
    (T.IsInvertible ∧ Function.Bijective T) ∨
      (LinearMap.ker (T : E →ₗ[𝕜] F) ≠ ⊥ ∧ LinearMap.range (T : E →ₗ[𝕜] F) ≠ ⊤ ∧
        finrank 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) =
          finrank 𝕜 (LinearMap.ker (T : E →ₗ[𝕜] F))) := by
  rcases hT.index_eq_zero_iff_bijective_or.mp h0 with hbij | hsing
  · exact Or.inl ⟨isInvertible_iff_isFredholm_and_bijective.mpr ⟨hT, hbij⟩, hbij⟩
  · exact Or.inr hsing

end Fredholm

end ContinuousLinearMap

namespace InnerProductSpace

variable {𝕜 F ι : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Applying the conjugate-linear Riesz embedding `innerSL 𝕜` preserves and reflects linear
independence. -/
theorem linearIndependent_innerSL_iff {v : ι → F} :
    LinearIndependent 𝕜 (fun i ↦ innerSL 𝕜 (v i)) ↔ LinearIndependent 𝕜 v := by
  have hsurj : Function.Surjective (starRingEnd 𝕜) :=
    fun c ↦ ⟨starRingEnd 𝕜 c, starRingEnd_self_apply c⟩
  constructor
  · intro h
    refine linearIndependent_iff'.mpr fun s g hg i hi ↦ ?_
    have hg' : ∑ j ∈ s, starRingEnd 𝕜 (g j) • innerSL 𝕜 (v j) = 0 := by
      simpa only [map_sum, map_smulₛₗ, map_zero] using congrArg (innerSL 𝕜) hg
    exact (RingHom.injective (starRingEnd 𝕜)) <|
      (linearIndependent_iff'.mp h s (fun j ↦ starRingEnd 𝕜 (g j)) hg' i hi).trans
        (map_zero (starRingEnd 𝕜)).symm
  · intro h
    exact h.map_of_surjective_injective (starRingEnd 𝕜)
      (toDualMap 𝕜 F).toAddMonoidHom hsurj
      (fun x hx ↦ (toDualMap 𝕜 F).injective (by simpa using hx))
      fun r x ↦ map_smulₛₗ (toDualMap 𝕜 F) r x

/-- Applying `innerSL 𝕜` followed by forgetting continuity preserves and reflects linear
independence in the algebraic dual `Module.Dual 𝕜 F`. -/
theorem linearIndependent_coe_innerSL_iff {v : ι → F} :
    LinearIndependent 𝕜 (fun i ↦ (innerSL 𝕜 (v i) : Module.Dual 𝕜 F)) ↔ LinearIndependent 𝕜 v := by
  rw [← linearIndependent_innerSL_iff]
  simp only [linearIndependent_iff']
  refine ⟨fun h s g hg i hi ↦ h s g ?_ i hi, fun h s g hg i hi ↦ h s g ?_ i hi⟩
  · ext y
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    simpa only [sum_apply, smul_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      zero_apply] using congrArg (fun φ : StrongDual 𝕜 F ↦ φ y) hg
  · ext y
    rw [sum_apply, zero_apply]
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_apply,
      ContinuousLinearMap.coe_coe, LinearMap.zero_apply] using LinearMap.congr_fun hg y

/-- If `b` is a basis of a subspace `S ⊆ F`, then the common kernel of the Riesz functionals
`innerSL 𝕜 (b i)` is the orthogonal complement `Sᗮ`. -/
theorem iInf_ker_innerSL_basis_eq_orthogonal {S : Submodule 𝕜 F} (b : Basis ι 𝕜 S) :
    (⨅ i, LinearMap.ker (innerSL 𝕜 (b i : F) : Module.Dual 𝕜 F)) = Sᗮ := by
  ext y
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    innerSL_apply_apply, Submodule.mem_orthogonal]
  refine ⟨fun hy z hz ↦ ?_, fun hy i ↦ hy (b i) (b i).2⟩
  have hrepr : z = ∑ i ∈ (b.repr ⟨z, hz⟩).support, b.repr ⟨z, hz⟩ i • (b i : F) := by
    simpa only [Submodule.coe_sum, SetLike.val_smul, Finsupp.linearCombination_apply,
      Finsupp.sum] using congrArg Subtype.val (b.linearCombination_repr ⟨z, hz⟩).symm
  rw [hrepr, sum_inner]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [inner_smul_left, hy i, mul_zero]

end InnerProductSpace

namespace ContinuousLinearMap

section Hilbert

variable {𝕜 E F ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- If `T : E →L[𝕜] F` has closed range, then `range T` equals the orthogonal complement of
`ker T†`. -/
theorem range_eq_orthogonal_ker_adjoint_of_isClosed_range (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) :
    LinearMap.range (T : E →ₗ[𝕜] F) = (LinearMap.ker (T† : F →ₗ[𝕜] E))ᗮ := by
  simpa only [adjoint_adjoint] using
    (T†).range_adjoint_eq_orthogonal_ker_of_isClosed_range
      (T.isClosed_range_adjoint_of_isClosed_range hT)

/-- **Closed-range compatibility condition.** For an operator `T : E →L[𝕜] F` between Hilbert spaces
with closed range, `y ∈ range T` holds if and only if `⟪z, y⟫_𝕜 = 0` for every `z ∈ ker T†`. -/
theorem mem_range_iff_forall_inner_ker_adjoint_eq_zero_of_isClosed_range (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) {y : F} :
    y ∈ LinearMap.range (T : E →ₗ[𝕜] F) ↔ ∀ z ∈ LinearMap.ker (T† : F →ₗ[𝕜] E), ⟪z, y⟫_𝕜 = 0 := by
  rw [T.range_eq_orthogonal_ker_adjoint_of_isClosed_range hT, Submodule.mem_orthogonal]

/-- **Fredholm compatibility condition.** For a Fredholm operator `T : E →L[𝕜] F` between Hilbert
spaces, `y ∈ range T` holds if and only if `⟪z, y⟫_𝕜 = 0` for every `z ∈ ker T†`. -/
theorem IsFredholm.mem_range_iff_forall_inner_ker_adjoint_eq_zero {T : E →L[𝕜] F}
    (hT : IsFredholm T) {y : F} :
    y ∈ LinearMap.range (T : E →ₗ[𝕜] F) ↔ ∀ z ∈ LinearMap.ker (T† : F →ₗ[𝕜] E), ⟪z, y⟫_𝕜 = 0 :=
  T.mem_range_iff_forall_inner_ker_adjoint_eq_zero_of_isClosed_range hT.isClosed_range

/-- Equation-solvability form of
`ContinuousLinearMap.IsFredholm.mem_range_iff_forall_inner_ker_adjoint_eq_zero`. -/
theorem IsFredholm.exists_apply_eq_iff_forall_inner_ker_adjoint_eq_zero {T : E →L[𝕜] F}
    (hT : IsFredholm T) {y : F} :
    (∃ x, T x = y) ↔ ∀ z ∈ LinearMap.ker (T† : F →ₗ[𝕜] E), ⟪z, y⟫_𝕜 = 0 :=
  hT.mem_range_iff_forall_inner_ker_adjoint_eq_zero

/-- For an operator with closed range, the dimension of `ker T†` equals the dimension of the
cokernel `F ⧸ range T`. -/
theorem finrank_ker_adjoint_eq_finrank_coker (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) :
    finrank 𝕜 (LinearMap.ker (T† : F →ₗ[𝕜] E)) =
      finrank 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) :=
  (T.cokerEquivKerAdjoint hT).symm.toLinearEquiv.finrank_eq

/-- For a Fredholm operator between Hilbert spaces, `finrank 𝕜 (ker T†) = finrank 𝕜 (F ⧸ range T)`.
-/
theorem IsFredholm.finrank_ker_adjoint {T : E →L[𝕜] F} (hT : IsFredholm T) :
    finrank 𝕜 (LinearMap.ker (T† : F →ₗ[𝕜] E)) =
      finrank 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)) :=
  T.finrank_ker_adjoint_eq_finrank_coker hT.isClosed_range

/-- Evaluating `innerSL 𝕜` along any basis of `ker T†` cuts out `range T` when `T` has closed
range. -/
theorem iInf_ker_innerSL_basis_ker_adjoint_eq_range (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F))
    (b : Basis ι 𝕜 (LinearMap.ker (T† : F →ₗ[𝕜] E))) :
    (⨅ i, LinearMap.ker (innerSL 𝕜 (b i : F) : Module.Dual 𝕜 F)) =
      LinearMap.range (T : E →ₗ[𝕜] F) := by
  rw [InnerProductSpace.iInf_ker_innerSL_basis_eq_orthogonal b,
    T.range_eq_orthogonal_ker_adjoint_of_isClosed_range hT]

/-- For any basis `b` of `ker T†`, the compatibility functionals `innerSL 𝕜 (b i)` are linearly
independent in the algebraic dual `Module.Dual 𝕜 F` (and hence in `StrongDual 𝕜 F`). -/
theorem linearIndependent_coe_innerSL_basis_ker_adjoint (T : E →L[𝕜] F)
    (b : Basis ι 𝕜 (LinearMap.ker (T† : F →ₗ[𝕜] E))) :
    LinearIndependent 𝕜 (fun i ↦ (innerSL 𝕜 (b i : F) : Module.Dual 𝕜 F)) := by
  rw [InnerProductSpace.linearIndependent_coe_innerSL_iff]
  exact b.linearIndependent.map' (Submodule.subtype _)
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)

/-- **Adjoint-kernel compatibility functionals.** For every Hilbert Fredholm operator `T`, there
exists a family of `finrank 𝕜 (F ⧸ range T)` continuous linear functionals, obtained by applying
`innerSL 𝕜` to a basis of `ker T†`, which are linearly independent even as algebraic functionals
and whose common kernel is `range T`. -/
theorem IsFredholm.exists_compatibilityFunctionals {T : E →L[𝕜] F} (hT : IsFredholm T) :
    ∃ ℓ : Fin (finrank 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F))) → StrongDual 𝕜 F,
      LinearIndependent 𝕜 (fun i ↦ (ℓ i : Module.Dual 𝕜 F)) ∧
        (⨅ i, LinearMap.ker (ℓ i : Module.Dual 𝕜 F)) = LinearMap.range (T : E →ₗ[𝕜] F) ∧
        ∀ i, ∃ z ∈ LinearMap.ker (T† : F →ₗ[𝕜] E), ℓ i = innerSL 𝕜 z := by
  have : FiniteDimensional 𝕜 (LinearMap.ker (T† : F →ₗ[𝕜] E)) := hT.adjoint.finite_ker
  let b : Basis (Fin (finrank 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F)))) 𝕜
      (LinearMap.ker (T† : F →ₗ[𝕜] E)) :=
    (finBasis 𝕜 (LinearMap.ker (T† : F →ₗ[𝕜] E))).reindex
      (finCongr hT.finrank_ker_adjoint)
  refine ⟨fun i ↦ innerSL 𝕜 (b i : F), T.linearIndependent_coe_innerSL_basis_ker_adjoint b,
    T.iInf_ker_innerSL_basis_ker_adjoint_eq_range hT.isClosed_range b,
    fun i ↦ ⟨(b i : F), (b i).2, rfl⟩⟩

/-- For a Hilbert Fredholm operator `T`, the minimal number `finrank 𝕜 (ker T†) =
finrank 𝕜 (F ⧸ range T)` of compatibility conditions equals `finrank 𝕜 (ker T)` if and only if
`(T : E →ₗ[𝕜] F).index = 0`. -/
theorem IsFredholm.finrank_ker_adjoint_eq_finrank_ker_iff_index_eq_zero {T : E →L[𝕜] F}
    (hT : IsFredholm T) :
    finrank 𝕜 (LinearMap.ker (T† : F →ₗ[𝕜] E)) =
      finrank 𝕜 (LinearMap.ker (T : E →ₗ[𝕜] F)) ↔ (T : E →ₗ[𝕜] F).index = 0 := by
  rw [hT.finrank_ker_adjoint, LinearMap.finrank_coker_eq_finrank_ker_iff_index_eq_zero]

end Hilbert

end ContinuousLinearMap

namespace TauCeti

section Sharpness

/-- **Finite-dimensional non-zero-index check.** The zero operator `0 : 𝕜 →L[𝕜] 𝕜 × 𝕜` is Fredholm
with two independent compatibility conditions (`finrank coker = 2`), one-dimensional kernel
(`finrank ker = 1`), and index `1 - 2 = -1 ≠ 0`. -/
theorem zero_prod_isFredholm_and_index_eq_neg_one (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] :
    let T : 𝕜 →L[𝕜] 𝕜 × 𝕜 := 0
    T.IsFredholm ∧
      finrank 𝕜 ((𝕜 × 𝕜) ⧸ LinearMap.range (T : 𝕜 →ₗ[𝕜] 𝕜 × 𝕜)) = 2 ∧
      finrank 𝕜 (LinearMap.ker (T : 𝕜 →ₗ[𝕜] 𝕜 × 𝕜)) = 1 ∧
      T.index = -1 := by
  dsimp only
  refine ⟨ContinuousLinearMap.isFredholm_of_finiteDimensional 0, ?_, ?_, ?_⟩
  · rw [ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero]
    simpa using (Submodule.quotEquivOfEqBot (⊥ : Submodule 𝕜 (𝕜 × 𝕜)) rfl).finrank_eq
  · rw [ContinuousLinearMap.toLinearMap_zero, LinearMap.ker_zero]
    simp
  · simp

/-- Auxiliary backward shift `(B u) n = u (n + 1)` on `ℓ²(ℕ, 𝕜)`, kept private to this file's
sharpness witness so `Analysis/Fredholm/` does not export sequence-space operator API. -/
private noncomputable def backwardShift (𝕜 : Type*) [RCLike 𝕜] :
    lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2 :=
  LinearMap.mkContinuous
    { toFun := fun u ↦ ⟨fun n ↦ u (n + 1), (memℓp_nat_add_iff 1).mpr (lp.memℓp u)⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 fun u ↦ by
      rw [one_mul]
      exact lp.norm_le_of_forall_eq_indicator_comp (by norm_num)
        (s := Set.univ) (g := fun n ↦ n + 1) (fun _ _ _ _ h ↦ Nat.succ.inj h)
        fun n ↦ (congrFun (Set.indicator_univ _) n).symm

/-- **Backward-shift sharpness witness on `ℓ²(ℕ, 𝕜)`.** There exists a bounded Fredholm operator `B`
on `ℓ²(ℕ, 𝕜)` acting by `(B u) n = u (n + 1)` which is surjective with kernel `𝕜 ∙ δ₀` and index
`1`. In particular `B` satisfies `Bijective B ∨ ker B ≠ ⊥` while `B.index ≠ 0`, showing that the
weaker disjunction without `finrank coker = finrank ker` is not equivalent to index zero. -/
theorem exists_isFredholm_surjective_ker_ne_bot_index_eq_one (𝕜 : Type*) [RCLike 𝕜] :
    ∃ B : lp (fun _ : ℕ ↦ 𝕜) 2 →L[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2,
      (∀ u n, B u n = u (n + 1)) ∧
        B.IsFredholm ∧
        Function.Surjective B ∧
        LinearMap.ker (B : lp (fun _ : ℕ ↦ 𝕜) 2 →ₗ[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2) =
          (𝕜 ∙ lp.single 2 0 (1 : 𝕜)) ∧
        B.index = 1 ∧
        ((Function.Bijective B ∨
          LinearMap.ker (B : lp (fun _ : ℕ ↦ 𝕜) 2 →ₗ[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2) ≠ ⊥) ∧
          B.index ≠ 0) := by
  let B := backwardShift 𝕜
  have hB_apply (u : lp (fun _ : ℕ ↦ 𝕜) 2) (n : ℕ) : B u n = u (n + 1) := rfl
  have hsurj : Function.Surjective B := fun v ↦ by
    let u : ℕ → 𝕜 := fun n ↦ match n with | 0 => 0 | n + 1 => v n
    have hu : Memℓp u 2 := (memℓp_nat_add_iff 1).mp (lp.memℓp v)
    exact ⟨⟨u, hu⟩, lp.ext <| funext fun _ ↦ rfl⟩
  have hker : LinearMap.ker (B : lp (fun _ : ℕ ↦ 𝕜) 2 →ₗ[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2) =
      (𝕜 ∙ lp.single 2 0 (1 : 𝕜)) := by
    ext u
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, lp.ext_iff, funext_iff, hB_apply,
      lp.coeFn_zero, Pi.zero_apply, Submodule.mem_span_singleton]
    refine ⟨fun hu ↦ ⟨u 0, fun k ↦ ?_⟩, ?_⟩
    · cases k with
      | zero => simp
      | succ k => simp [hu k]
    · rintro ⟨c, hc⟩ n
      simpa using (hc (n + 1)).symm
  have hδ0 : (lp.single 2 0 (1 : 𝕜) : lp (fun _ : ℕ ↦ 𝕜) 2) ≠ 0 := fun h ↦
    (one_ne_zero : (1 : 𝕜) ≠ 0) (by simpa using congrFun (congrArg Subtype.val h) 0)
  have hfin_ker : FiniteDimensional 𝕜
      (LinearMap.ker (B : lp (fun _ : ℕ ↦ 𝕜) 2 →ₗ[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2)) := by
    rw [hker]
    infer_instance
  have hfin_coker : FiniteDimensional 𝕜
      (lp (fun _ : ℕ ↦ 𝕜) 2 ⧸
        LinearMap.range (B : lp (fun _ : ℕ ↦ 𝕜) 2 →ₗ[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2)) := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    infer_instance
  have hFred : B.IsFredholm := .of_finite_ker_coker B hfin_ker hfin_coker
  have hind : B.index = 1 := by
    rw [B.index_of_surjective hsurj, hker, finrank_span_singleton hδ0, Nat.cast_one]
  refine ⟨B, hB_apply, hFred, hsurj, hker, hind, ⟨Or.inr ?_, by omega⟩⟩
  rw [hker]
  exact Submodule.span_singleton_eq_bot.not.mpr hδ0

end Sharpness

end TauCeti

end
