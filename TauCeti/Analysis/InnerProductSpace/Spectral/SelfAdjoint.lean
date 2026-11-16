/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.LinearAlgebra.BilinearForm.RelativeEigenspace
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative
import TauCeti.LinearAlgebra.BilinearForm.Basic
import TauCeti.LinearAlgebra.Eigenspace.Semisimple
import TauCeti.LinearAlgebra.QuadraticForm.PosDef

/-!
# Diagonalizability of endomorphisms self-adjoint for a positive definite form

Let `g` be a symmetric positive definite bilinear form on a real vector space `V`. Rather than
fixing a global `InnerProductSpace ℝ V` instance, many geometric and Lie-theoretic constructions
carry `g` as explicit data (for instance, the twisted Killing form `-B(·, θ ·)` associated with a
Cartan involution `θ`). This file provides:

* packaging of `g` as `InnerProductSpace.Core ℝ V` (`LinearMap.BilinForm.toInnerProductCore`), so
  that callers can locally install `InnerProductSpace.ofCore` without committing `V` to a canonical
  norm; and
* real diagonalizability and semisimplicity of every `g`-self-adjoint endomorphism `T` when `V` is
  finite-dimensional (`LinearMap.BilinForm.iSup_eigenspace_eq_top_of_isSelfAdjoint` and
  `LinearMap.BilinForm.isSemisimple_of_isSelfAdjoint`).

The spectral argument reduces directly to `LinearMap.BilinForm.relativeSpectralSubspace_univ`
applied to the symmetric form `(x, y) ↦ g (T x) y`, whose relative eigenspaces with respect to any
left-separating `g` are the ordinary eigenspaces of `T`.

## Main declarations

* `LinearMap.BilinForm.toInnerProductCore`: packages a symmetric positive definite real bilinear
  form as `InnerProductSpace.Core ℝ V`.
* `LinearMap.BilinForm.isSymm_compl₁₂_id_of_isSelfAdjoint`: for symmetric `g` and `g`-self-adjoint
  `T`, the form `(x, y) ↦ g (T x) y` is symmetric.
* `LinearMap.BilinForm.relativeEigenspace_compl₁₂_id`: for left-separating `g`, the relative
  eigenspaces of `(x, y) ↦ g (T x) y` with respect to `g` are the eigenspaces of `T`.
* `LinearMap.BilinForm.iSup_eigenspace_eq_top_of_isSelfAdjoint`: on a finite-dimensional real
  space, the real eigenspaces of a `g`-self-adjoint endomorphism span `V`.
* `LinearMap.BilinForm.isSemisimple_of_isSelfAdjoint`: consequently, every `g`-self-adjoint
  endomorphism on a finite-dimensional real space is semisimple.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, §4.1 and §7.6.
-/

public section

namespace LinearMap.BilinForm

section CommRing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- If `g` is symmetric and `T` is self-adjoint with respect to `g`, then the bilinear form
`(x, y) ↦ g (T x) y` is symmetric. -/
theorem isSymm_compl₁₂_id_of_isSelfAdjoint {g : LinearMap.BilinForm R V} (hg : g.IsSymm)
    {T : Module.End R V} (hT : g.IsSelfAdjoint T) :
    LinearMap.BilinForm.IsSymm (g.compl₁₂ T LinearMap.id) :=
  isSymm_def.mpr fun x y ↦ by
    simp only [LinearMap.compl₁₂_apply, LinearMap.id_apply]
    rw [hT x y, hg.eq]

/-- For a left-separating bilinear form `g`, the relative eigenspace of `(x, y) ↦ g (T x) y` with
respect to `g` at `μ` is the `μ`-eigenspace of `T`. -/
theorem relativeEigenspace_compl₁₂_id {g : LinearMap.BilinForm R V} (hsep : g.SeparatingLeft)
    (T : Module.End R V) (μ : R) :
    g.relativeEigenspace (g.compl₁₂ T LinearMap.id) μ = T.eigenspace μ := by
  ext v
  rw [mem_relativeEigenspace_iff, Module.End.mem_eigenspace_iff]
  simp only [LinearMap.compl₁₂_apply, LinearMap.id_apply]
  refine ⟨fun hv ↦ sub_eq_zero.mp (hsep (T v - μ • v) fun w ↦ ?_), fun hv w ↦ ?_⟩
  · simp [sub_eq_zero.mpr (hv w)]
  · simp [hv]

end CommRing

section Real

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Package a symmetric positive definite real bilinear form as `InnerProductSpace.Core ℝ V`,
without installing a global norm on `V`. -/
@[implicit_reducible]
def toInnerProductCore (g : LinearMap.BilinForm ℝ V) (hg : g.IsSymm)
    (hpos : g.toQuadraticMap.PosDef) : InnerProductSpace.Core ℝ V where
  inner v w := g v w
  conj_inner_symm v w := by simpa using hg.eq w v
  re_inner_nonneg v := by simpa using hpos.nonneg v
  add_left v w x := by simp
  smul_left v w r := by simp [smul_eq_mul]
  definite v hv := hpos.anisotropic v (by simpa using hv)

/-- The inner product induced by `LinearMap.BilinForm.toInnerProductCore` evaluates as `g`. -/
@[simp]
theorem toInnerProductCore_inner (g : LinearMap.BilinForm ℝ V) (hg : g.IsSymm)
    (hpos : g.toQuadraticMap.PosDef) (v w : V) :
    @inner ℝ V (g.toInnerProductCore hg hpos).toInner v w = g v w :=
  (rfl)

variable [FiniteDimensional ℝ V]

/-- **Real spectral spanning for `g`-self-adjoint endomorphisms.** For a symmetric positive
definite bilinear form `g` on a finite-dimensional real vector space `V`, the real eigenspaces of
every `g`-self-adjoint endomorphism `T` span `V`. -/
theorem iSup_eigenspace_eq_top_of_isSelfAdjoint {g : LinearMap.BilinForm ℝ V} (hg : g.IsSymm)
    (hpos : g.toQuadraticMap.PosDef) {T : Module.End ℝ V} (hT : g.IsSelfAdjoint T) :
    ⨆ μ : ℝ, T.eigenspace μ = ⊤ := by
  have hsep : g.SeparatingLeft := (g.nondegenerate_of_anisotropic hpos.anisotropic).1
  have huniv := g.relativeSpectralSubspace_univ hg ((g.posDef_toQuadraticMap_iff).mp hpos)
    (isSymm_compl₁₂_id_of_isSelfAdjoint hg hT)
  simpa only [relativeSpectralSubspace_def, Set.mem_univ, iSup_pos,
    relativeEigenspace_compl₁₂_id hsep T] using huniv

/-- **Every `g`-self-adjoint endomorphism is semisimple.** For a symmetric positive definite
bilinear form `g` on a finite-dimensional real vector space `V`, every `g`-self-adjoint
endomorphism of `V` is semisimple (diagonalizable over `ℝ`). -/
theorem isSemisimple_of_isSelfAdjoint {g : LinearMap.BilinForm ℝ V} (hg : g.IsSymm)
    (hpos : g.toQuadraticMap.PosDef) {T : Module.End ℝ V} (hT : g.IsSelfAdjoint T) :
    T.IsSemisimple :=
  TauCeti.isSemisimple_of_iSup_eigenspace_eq_top
    (iSup_eigenspace_eq_top_of_isSelfAdjoint hg hpos hT)

end Real

end LinearMap.BilinForm
