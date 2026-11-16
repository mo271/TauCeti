/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- The local-diffeomorphism witnesses are needed to construct their finite product.
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Finite products of local diffeomorphisms

Let `M i` and `M' i` be finite families of charted spaces, with `∀ i, M i` and `∀ i, M' i`
carrying the product manifold structures `ModelWithCorners.pi I` and `ModelWithCorners.pi I'`.
This file provides the finite-product analogues of `PartialDiffeomorph.prod`,
`IsLocalDiffeomorphAt.prodMap`, and `IsLocalDiffeomorph.prodMap`:

* `ContMDiffOn.piMap`: a finite product of `C^n` maps on sets is `C^n` on the product set
  `univ.pi s`.
* `PartialDiffeomorph.pi`: the finite product of partial diffeomorphisms, with source `univ.pi` of
  their sources and target `univ.pi` of their targets.
* `IsLocalDiffeomorphAt.piMap`, `IsLocalDiffeomorph.piMap`: finite products of `C^n` local
  diffeomorphisms are `C^n` local diffeomorphisms.
* `Diffeomorph.modelWithCornersPi`: on a finite product `∀ i, E i` of normed spaces, the identity
  map is a `C^n` diffeomorphism between the normed-space model `𝓘(𝕜, ∀ i, E i)` and the product
  model `ModelWithCorners.pi fun i ↦ 𝓘(𝕜, E i)`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 4.
-/

public noncomputable section

open Set
open scoped Manifold ContDiff

section PiMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {E E' : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (E' i)] [∀ i, NormedSpace 𝕜 (E' i)]
  {H H' : ι → Type*} [∀ i, TopologicalSpace (H i)] [∀ i, TopologicalSpace (H' i)]
  {I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)} {I' : ∀ i, ModelWithCorners 𝕜 (E' i) (H' i)}
  {M M' : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]
  [∀ i, TopologicalSpace (M' i)] [∀ i, ChartedSpace (H' i) (M' i)]
  {n : ℕ∞ω}

/-- A finite product of maps between manifolds, each `C^n` on a set, is `C^n` on the product of
these sets. -/
theorem ContMDiffOn.piMap {f : ∀ i, M i → M' i} {s : ∀ i, Set (M i)}
    (hf : ∀ i, ContMDiffOn (I i) (I' i) n (f i) (s i)) :
    ContMDiffOn (ModelWithCorners.pi I) (ModelWithCorners.pi I') n (Pi.map f) (univ.pi s) :=
  contMDiffOn_pi_iff.2 fun i ↦ (hf i).comp contMDiff_apply.contMDiffOn
    fun _ hx ↦ hx i (mem_univ i)

/-- The finite product of partial diffeomorphisms, on the product of their sources. -/
def PartialDiffeomorph.pi (e : ∀ i, PartialDiffeomorph (I i) (I' i) (M i) (M' i) n) :
    PartialDiffeomorph (ModelWithCorners.pi I) (ModelWithCorners.pi I') (∀ i, M i) (∀ i, M' i)
      n where
  toPartialEquiv := PartialEquiv.pi fun i ↦ (e i).toPartialEquiv
  open_source := isOpen_set_pi finite_univ fun i _ ↦ (e i).open_source
  open_target := isOpen_set_pi finite_univ fun i _ ↦ (e i).open_target
  contMDiffOn_toFun := ContMDiffOn.piMap fun i ↦ (e i).contMDiffOn
  contMDiffOn_invFun := ContMDiffOn.piMap fun i ↦ (e i).symm.contMDiffOn

/-- The source of a finite-product partial diffeomorphism is the product of its sources. -/
@[simp]
theorem PartialDiffeomorph.pi_source
    (e : ∀ i, PartialDiffeomorph (I i) (I' i) (M i) (M' i) n) :
    (PartialDiffeomorph.pi e).source = univ.pi fun i ↦ (e i).source :=
  (rfl)

/-- The target of a finite-product partial diffeomorphism is the product of its targets. -/
@[simp]
theorem PartialDiffeomorph.pi_target
    (e : ∀ i, PartialDiffeomorph (I i) (I' i) (M i) (M' i) n) :
    (PartialDiffeomorph.pi e).target = univ.pi fun i ↦ (e i).target :=
  (rfl)

/-- A finite-product partial diffeomorphism acts coordinatewise. -/
@[simp]
theorem PartialDiffeomorph.pi_apply
    (e : ∀ i, PartialDiffeomorph (I i) (I' i) (M i) (M' i) n) (x : ∀ i, M i) (i : ι) :
    PartialDiffeomorph.pi e x i = e i (x i) :=
  (rfl)

/-- The inverse of a finite product of partial diffeomorphisms is the product of their inverses. -/
@[simp]
theorem PartialDiffeomorph.pi_symm
    (e : ∀ i, PartialDiffeomorph (I i) (I' i) (M i) (M' i) n) :
    (PartialDiffeomorph.pi e).symm = PartialDiffeomorph.pi fun i ↦ (e i).symm :=
  (rfl)

/-- The coordinatewise map `Pi.map f` is a local diffeomorphism at `x` when each `f i` is a local
diffeomorphism at `x i`. -/
theorem IsLocalDiffeomorphAt.piMap {f : ∀ i, M i → M' i} {x : ∀ i, M i}
    (hf : ∀ i, IsLocalDiffeomorphAt (I i) (I' i) n (f i) (x i)) :
    IsLocalDiffeomorphAt (ModelWithCorners.pi I) (ModelWithCorners.pi I') n (Pi.map f) x := by
  choose e hx he using hf
  exact ⟨PartialDiffeomorph.pi e, fun i _ ↦ hx i,
    fun z hz ↦ funext fun i ↦ he i (hz i (mem_univ i))⟩

/-- A finite product of local diffeomorphisms is a local diffeomorphism. -/
theorem IsLocalDiffeomorph.piMap {f : ∀ i, M i → M' i}
    (hf : ∀ i, IsLocalDiffeomorph (I i) (I' i) n (f i)) :
    IsLocalDiffeomorph (ModelWithCorners.pi I) (ModelWithCorners.pi I') n (Pi.map f) :=
  fun x ↦ IsLocalDiffeomorphAt.piMap fun i ↦ hf i (x i)

end PiMap

namespace Diffeomorph

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] (n : ℕ∞ω)

/-- On a finite product `∀ i, E i` of normed spaces, the identity map is a `C^n` diffeomorphism
between the normed-space manifold structure `𝓘(𝕜, ∀ i, E i)` and the product manifold structure
`ModelWithCorners.pi fun i ↦ 𝓘(𝕜, E i)` carried by `piChartedSpace`. -/
def modelWithCornersPi :
    (∀ i, E i) ≃ₘ^n⟮𝓘(𝕜, ∀ i, E i), ModelWithCorners.pi fun i ↦ 𝓘(𝕜, E i)⟯ (∀ i, E i) where
  toEquiv := Equiv.refl (∀ i, E i)
  contMDiff_toFun := contMDiff_pi_iff.2 fun i ↦
    (ContinuousLinearMap.proj (R := 𝕜) (φ := E) i).contMDiff
  contMDiff_invFun := contMDiff_pi_module_iff.2 fun _ ↦ contMDiff_apply

/-- `Diffeomorph.modelWithCornersPi` has underlying function `id`. -/
@[simp]
theorem coe_modelWithCornersPi : ⇑(modelWithCornersPi 𝕜 E n) = id :=
  (rfl)

/-- `Diffeomorph.modelWithCornersPi` acts as the identity. -/
@[simp]
theorem modelWithCornersPi_apply (x : ∀ i, E i) : modelWithCornersPi 𝕜 E n x = x :=
  (rfl)

/-- The inverse of `Diffeomorph.modelWithCornersPi` has underlying function `id`. -/
@[simp]
theorem coe_modelWithCornersPi_symm : ⇑(modelWithCornersPi 𝕜 E n).symm = id :=
  (rfl)

/-- The inverse of `Diffeomorph.modelWithCornersPi` acts as the identity. -/
@[simp]
theorem modelWithCornersPi_symm_apply (x : ∀ i, E i) : (modelWithCornersPi 𝕜 E n).symm x = x :=
  (rfl)

end Diffeomorph
