/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import TauCeti.Topology.Algebra.OpenMapping.Henkel
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Closed range from a finite complement or finite projective cokernel

This file establishes that a continuous linear map `T : E →L[R] F` from a complete
first-countable uniform module to a `T0` Baire topological module over a complete first-countable
topological ring `R` with a zero sequence of units has closed range whenever either:

* `T.range` admits a finitely generated algebraic complement `N : Submodule R F`
  (`ContinuousLinearMap.isClosed_range_of_isCompl_finite`), or
* the cokernel `F ⧸ T.range` is finitely generated and projective
  (`ContinuousLinearMap.isClosed_range_of_finite_coker`).

Over a complete nontrivially normed field `𝕜` (such as `ℝ`, `ℂ`, or `ℚ_[p]`), importing
`Mathlib.LinearAlgebra.Basis.VectorSpace` supplies `Module.Projective` via
`Module.Free.of_divisionRing` and `Module.Projective.of_free`, and importing
`TauCeti.Analysis.Normed.Ring.PseudoUniformizer` supplies `TauCeti.HasZeroSequenceOfUnits 𝕜` via
`TauCeti.NormedRing.IsTate.of_nontriviallyNormedField`, so
`ContinuousLinearMap.isClosed_range_of_finite_coker` specializes automatically to any continuous
linear map with finite-dimensional cokernel between Fréchet or Banach spaces (and more generally
into any `T0` Baire topological vector space).

The proof lifts a finite generating family of the complement `N` to a surjection
`f : (Fin n → R) →ₗ[R] N`, forms the continuous linear surjection
`Φ : E × (Fin n → R) →L[R] F`, `Φ (x, a) = T x + f a`, and applies the quotient form of the open
mapping theorem (`ContinuousLinearMap.isQuotientMap_of_surjective`). Because `T.range ⊓ N = ⊥`,
the preimage `Φ ⁻¹' T.range` is `{p | (f p.2 : F) = 0}`, which is closed in `E × (Fin n → R)` since
`F` is `T2` (`T0Space` plus `IsTopologicalAddGroup`).

## Main declarations

* `ContinuousLinearMap.isClosed_range_of_isCompl_finite`: if `T.range` has a finitely generated
  algebraic complement, then `T.range` is closed.
* `ContinuousLinearMap.isClosed_range_of_finite_coker`: if `F ⧸ T.range` is finitely generated and
  projective (in particular, finite-dimensional over a complete nontrivially normed field), then
  `T.range` is closed.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter IX, §1.10.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix A.1.
* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  [arXiv:1407.5647](https://arxiv.org/abs/1407.5647).
-/

public section

open Filter Topology

namespace ContinuousLinearMap

variable {R E F : Type*} [Ring R] [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R]
  [ContinuousMul R] [(𝓝 (0 : R)).IsCountablyGenerated] [TauCeti.HasZeroSequenceOfUnits R]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
  [(𝓝 (0 : E)).IsCountablyGenerated] [Module R E] [ContinuousSMul R E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [T0Space F] [BaireSpace F]
  [Module R F] [ContinuousSMul R F]

/-- If the range of a continuous linear map `T : E →L[R] F` admits a finitely generated algebraic
complement `N`, then `T.range` is closed in `F`.

No uniformity, completeness, first countability, or local convexity is assumed on `F` beyond
`T0Space` and `BaireSpace`, and `R` need not be commutative or separated. -/
theorem isClosed_range_of_isCompl_finite (T : E →L[R] F) {N : Submodule R F}
    (hN : IsCompl (LinearMap.range (T : E →ₗ[R] F)) N) [Module.Finite R N] :
    IsClosed (LinearMap.range (T : E →ₗ[R] F) : Set F) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R N
  have : (𝓝 (0 : Fin n → R)).IsCountablyGenerated := by rw [nhds_pi]; infer_instance
  have : (𝓝 (0 : E × (Fin n → R))).IsCountablyGenerated := by rw [nhds_prod_eq]; infer_instance
  let ψ : (Fin n → R) →L[R] F := ⟨N.subtype ∘ₗ f, LinearMap.continuous_on_pi _⟩
  let Φ : (E × (Fin n → R)) →L[R] F := T.coprod ψ
  have hsurj : Function.Surjective Φ := by
    intro y
    have hy : y ∈ LinearMap.range (T : E →ₗ[R] F) ⊔ N := by rw [hN.sup_eq_top]; trivial
    obtain ⟨r, hr, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨x, rfl⟩ := hr
    obtain ⟨a, ha⟩ := hf ⟨z, hz⟩
    exact ⟨(x, a), by simp [Φ, ψ, ha]⟩
  have hpre : Φ ⁻¹' (LinearMap.range (T : E →ₗ[R] F) : Set F) =
      {p : E × (Fin n → R) | ψ p.2 = 0} := by
    ext ⟨x, a⟩
    simp only [Set.mem_preimage, SetLike.mem_coe, Set.mem_ofPred_eq, Φ, coprod_apply]
    constructor
    · intro hmem
      have hψ : ψ a ∈ LinearMap.range (T : E →ₗ[R] F) := by
        simpa using (LinearMap.range (T : E →ₗ[R] F)).sub_mem hmem ⟨x, rfl⟩
      exact (Submodule.mem_bot R).mp <| hN.inf_eq_bot ▸ ⟨hψ, (f a).2⟩
    · intro h0
      simp [h0]
  have hclosed : IsClosed (Φ ⁻¹' (LinearMap.range (T : E →ₗ[R] F) : Set F)) := by
    rw [hpre]
    exact isClosed_eq (ψ.continuous.comp continuous_snd) continuous_const
  exact (Φ.isQuotientMap_of_surjective hsurj).isClosed_preimage.mp hclosed

/-- A continuous linear map `T : E →L[R] F` whose cokernel `F ⧸ range T` is finitely generated and
projective has closed range.

Over a complete nontrivially normed field `𝕜`, every module is free and hence projective, so
`[Module.Projective 𝕜 (F ⧸ LinearMap.range (T : E →ₗ[𝕜] F))]` and `[HasZeroSequenceOfUnits 𝕜]`
are synthesized automatically: finite dimensionality of the cokernel alone forces `range T` to be
closed. Over a non-field ring `R`, projectivity cannot be dropped (for example, multiplication by
`x` on `C([0, 1])` has cyclic cokernel yet non-closed range). -/
theorem isClosed_range_of_finite_coker (T : E →L[R] F)
    [Module.Finite R (F ⧸ LinearMap.range (T : E →ₗ[R] F))]
    [Module.Projective R (F ⧸ LinearMap.range (T : E →ₗ[R] F))] :
    IsClosed (LinearMap.range (T : E →ₗ[R] F) : Set F) := by
  let S := LinearMap.range (T : E →ₗ[R] F)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property S.mkQ LinearMap.id S.mkQ_surjective
  have hcompl : IsCompl S (LinearMap.range s) := by
    rw [isCompl_iff, disjoint_iff, codisjoint_iff]
    constructor
    · refine eq_bot_iff.mpr fun y ⟨hyS, hys⟩ ↦ ?_
      obtain ⟨q, rfl⟩ := hys
      have hq : q = 0 :=
        (LinearMap.congr_fun hs q).symm.trans ((Submodule.Quotient.mk_eq_zero S).mpr hyS)
      simp [hq]
    · refine eq_top_iff.mpr fun y _ ↦ ?_
      have hsub : y - s (S.mkQ y) ∈ S := by
        rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub,
          ← LinearMap.comp_apply, hs, LinearMap.id_apply, sub_self]
      simpa [sub_add_cancel] using Submodule.add_mem_sup hsub (LinearMap.mem_range_self s (S.mkQ y))
  have : Module.Finite R (LinearMap.range s) :=
    Module.Finite.of_surjective s.rangeRestrict s.surjective_rangeRestrict
  exact T.isClosed_range_of_isCompl_finite hcompl

end ContinuousLinearMap
