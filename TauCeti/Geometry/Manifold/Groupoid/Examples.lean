/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Groupoid.Fibers
public import TauCeti.Geometry.Manifold.Groupoid.Nerve
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Topology.CategoryTheory.Groupoid.Examples

import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Submersion.Split

/-!
# Unit and pair Lie groupoids

Given a `C^n` manifold `N`, both the unit groupoid `Discrete N` and the pair groupoid
`Codiscrete N` inherit `C^n` manifold structures on objects and total arrows by pulling charts back
along `objectHomeomorph` and `arrowHomeomorph` (`Homeomorph.pullbackChartedSpace`).

For the unit groupoid `Discrete N`:
* source and target are global (hence local) `C^n` diffeomorphisms (`sourceDiffeomorph`,
  `isLocalDiffeomorph_source`, `isLocalDiffeomorph_target`);
* every source fibre is a singleton (`uniqueSourceFiber`), hence Hausdorff **without** assuming
  `T2Space N`;
* when `N` is a finite-dimensional boundaryless smooth real manifold (not necessarily Hausdorff),
  `Discrete N` is a Lie groupoid (`UnitGroupoid.isLieGroupoid`), its composable pairs are
  diffeomorphic to `N` (`UnitGroupoid.composablePairsDiffeomorph`), and the `k`-simplex manifold of
  its smooth nerve has dimension `finrank ℝ E` for every `k`.

For the pair groupoid `Codiscrete N`:
* arrows are parametrized by `(target, source)` coordinates via `arrowDiffeomorph :
  Quiver.Total (Codiscrete N) ≃ₘ^n N × N`;
* source and target are smooth submersions over any `NontriviallyNormedField`
  (`isSubmersion_source`, `isSubmersion_target`);
* every source fibre is homeomorphic to `N` (`sourceFiberHomeomorph`), so Hausdorffness of the
  source fibres is equivalent to `T2Space N` when `N` is nonempty (`t2Space_sourceFiber_iff`);
* when `N` is a Hausdorff finite-dimensional boundaryless smooth real manifold, `Codiscrete N` is a
  Lie groupoid (`PairGroupoid.isLieGroupoid`) with `2 * finrank ℝ E`-dimensional arrow manifold,
  source and target fibres diffeomorphic to `N` (`sourceFiberDiffeomorph`,
  `targetFiberDiffeomorph`), composable pairs diffeomorphic to `N × N × N` of dimension
  `3 * finrank ℝ E` (`composablePairsDiffeomorph`), and `k`-simplex nerve dimension
  `(k + 1) * finrank ℝ E`;
* left translation by `g = (y, x)` acts on target fibres by `(x, w) ↦ (y, w)` and right translation
  acts on source fibres by `(w, y) ↦ (w, x)`; the witness `same_source_not_composable` shows that
  two arrows `(y, x)` and `(z, x)` with `z ≠ x` share the same source `x` yet do not compose.

## Main declarations

* `TauCeti.UnitGroupoid.instChartedSpaceObjects`, `TauCeti.UnitGroupoid.instIsManifoldObjects`,
  `TauCeti.UnitGroupoid.objectDiffeomorph`, `TauCeti.UnitGroupoid.instChartedSpaceArrows`,
  `TauCeti.UnitGroupoid.instIsManifoldArrows`, `TauCeti.UnitGroupoid.arrowDiffeomorph`,
  `TauCeti.UnitGroupoid.sourceDiffeomorph`, `TauCeti.UnitGroupoid.isLocalDiffeomorph_source`,
  `TauCeti.UnitGroupoid.isLocalDiffeomorph_target`: `C^n` structures on `Discrete N`.
* `TauCeti.UnitGroupoid.isLieGroupoid`, `TauCeti.UnitGroupoid.composablePairsDiffeomorph`,
  `TauCeti.UnitGroupoid.nerveModelDim_eq`: Lie groupoid structure on `Discrete N` (without
  `T2Space N`), composable pairs, and nerve dimensions.
* `TauCeti.PairGroupoid.instChartedSpaceObjects`, `TauCeti.PairGroupoid.instIsManifoldObjects`,
  `TauCeti.PairGroupoid.objectDiffeomorph`, `TauCeti.PairGroupoid.instChartedSpaceArrows`,
  `TauCeti.PairGroupoid.instIsManifoldArrows`, `TauCeti.PairGroupoid.arrowDiffeomorph`,
  `TauCeti.PairGroupoid.isSubmersion_source`, `TauCeti.PairGroupoid.isSubmersion_target`: `C^n`
  structures and submersions on `Codiscrete N`.
* `TauCeti.PairGroupoid.isLieGroupoid`, `TauCeti.PairGroupoid.sourceFiberDiffeomorph`,
  `TauCeti.PairGroupoid.targetFiberDiffeomorph`, `TauCeti.PairGroupoid.composablePairsDiffeomorph`,
  `TauCeti.PairGroupoid.leftTranslationDiffeomorph_apply_mk`,
  `TauCeti.PairGroupoid.rightTranslationDiffeomorph_apply_mk`,
  `TauCeti.PairGroupoid.same_source_not_composable`, `TauCeti.PairGroupoid.nerveModelDim_eq`:
  Lie groupoid structure, fibres, composable pairs, translations, and dimensions for `Codiscrete N`.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Cambridge Stud. Adv.
  Math. 91, Cambridge University Press (2003), Section 5.1.
* M. Crainic and R. L. Fernandes, *Lectures on integrability of Lie brackets*, Geom. Topol. Monogr.
  17 (2011), 1–107, Chapter 1.
-/

public section

open CategoryTheory Manifold Module Topology
open scoped Manifold ContDiff

namespace TauCeti.UnitGroupoid

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]

/-- Objects of `Discrete N` carry the charted-space structure pulled back from `N`. -/
instance instChartedSpaceObjects : ChartedSpace H (Discrete N) :=
  (objectHomeomorph N).pullbackChartedSpace

/-- Objects of `Discrete N` form a `C^n` manifold whenever `N` does. -/
instance instIsManifoldObjects (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n N] :
    IsManifold I n (Discrete N) :=
  (objectHomeomorph N).pullback_isManifold I n

/-- Forgetting the categorical wrapper on `Discrete N` as a `C^n` diffeomorphism. -/
def objectDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (N : Type*) [TopologicalSpace N] [ChartedSpace H N] : Discrete N ≃ₘ^n⟮I, I⟯ N :=
  (objectHomeomorph N).pullbackDiffeomorph I n

@[simp]
theorem objectDiffeomorph_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (x : Discrete N) :
    objectDiffeomorph I n N x = x.as := by simp [objectDiffeomorph]

@[simp]
theorem objectDiffeomorph_symm_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (x : N) :
    (objectDiffeomorph I n N).symm x = Discrete.mk x := by simp [objectDiffeomorph]

@[simp]
theorem objectDiffeomorph_toHomeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    (objectDiffeomorph I n N).toHomeomorph = objectHomeomorph N := by simp [objectDiffeomorph]

/-- Total arrows of `Discrete N` carry the charted-space structure pulled back from `N` along
`arrowHomeomorph`. -/
instance instChartedSpaceArrows : ChartedSpace H (Quiver.Total (Discrete N)) :=
  (arrowHomeomorph N).pullbackChartedSpace

/-- Total arrows of `Discrete N` form a `C^n` manifold whenever `N` does. -/
instance instIsManifoldArrows (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n N] :
    IsManifold I n (Quiver.Total (Discrete N)) :=
  (arrowHomeomorph N).pullback_isManifold I n

/-- The total-arrow space of `Discrete N` is `C^n` diffeomorphic to `N`. -/
def arrowDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (N : Type*) [TopologicalSpace N] [ChartedSpace H N] : Quiver.Total (Discrete N) ≃ₘ^n⟮I, I⟯ N :=
  (arrowHomeomorph N).pullbackDiffeomorph I n

@[simp]
theorem arrowDiffeomorph_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (a : Quiver.Total (Discrete N)) : arrowDiffeomorph I n N a = a.left.as := by
  simp [arrowDiffeomorph]

@[simp]
theorem arrowDiffeomorph_symm_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (x : N) :
    (arrowDiffeomorph I n N).symm x = ⟨⟨x⟩, ⟨x⟩, 𝟙 _⟩ := by simp [arrowDiffeomorph]

@[simp]
theorem arrowDiffeomorph_toHomeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    (arrowDiffeomorph I n N).toHomeomorph = arrowHomeomorph N := by simp [arrowDiffeomorph]

/-- The source map of `Discrete N` as a global `C^n` diffeomorphism. -/
def sourceDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (N : Type*) [TopologicalSpace N] [ChartedSpace H N] :
    Quiver.Total (Discrete N) ≃ₘ^n⟮I, I⟯ Discrete N :=
  (arrowDiffeomorph I n N).trans (objectDiffeomorph I n N).symm

@[simp]
theorem coe_sourceDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    ⇑(sourceDiffeomorph I n N) = (Quiver.Total.left : Quiver.Total (Discrete N) → Discrete N) :=
  funext fun _ ↦ by simp [sourceDiffeomorph]

@[simp]
theorem coe_sourceDiffeomorph_symm (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    ⇑(sourceDiffeomorph I n N).symm =
      fun x : Discrete N ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total (Discrete N)) :=
  funext fun _ ↦ (sourceDiffeomorph I n N).injective (by simp)

/-- The source map of `Discrete N` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_source {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} :
    IsLocalDiffeomorph I I n (Quiver.Total.left : Quiver.Total (Discrete N) → Discrete N) :=
  coe_sourceDiffeomorph I n (N := N) ▸ (sourceDiffeomorph I n N).isLocalDiffeomorph

/-- The target map of `Discrete N` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_target {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} :
    IsLocalDiffeomorph I I n (Quiver.Total.right : Quiver.Total (Discrete N) → Discrete N) :=
  target_eq_source N ▸ isLocalDiffeomorph_source

section LieGroupoid

/-- Every source fibre of `Discrete N` has at most one arrow. -/
theorem subsingleton_sourceFiber {X : Type*} (x : Discrete X) :
    Subsingleton {a : Quiver.Total (Discrete X) // a.left = x} where
  allEq := by
    rintro ⟨⟨⟨a⟩, ⟨b⟩, f⟩, h1⟩ ⟨⟨⟨c⟩, ⟨d⟩, g⟩, h2⟩
    obtain rfl := Discrete.eq_of_hom f
    obtain rfl := Discrete.eq_of_hom g
    cases h1
    cases h2
    obtain rfl := Subsingleton.elim f g
    rfl

/-- Every source fibre of `Discrete N` is canonically a singleton `{𝟙 x}`. -/
@[instance_reducible]
def uniqueSourceFiber {X : Type*} (x : Discrete X) :
    Unique {a : Quiver.Total (Discrete X) // a.left = x} where
  default := ⟨⟨x, x, 𝟙 x⟩, rfl⟩
  uniq a := (subsingleton_sourceFiber x).allEq a _

/-- Every source fibre of `Discrete N` is Hausdorff, with no Hausdorffness hypothesis on `N`. -/
theorem t2Space_sourceFiber {X : Type*} [TopologicalSpace X] (x : Discrete X) :
    T2Space {a : Quiver.Total (Discrete X) // a.left = x} := by
  have := subsingleton_sourceFiber x
  infer_instance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]

/-- The source map of `Discrete N` is a `C^n` submersion (`1 ≤ n`) for a finite-dimensional
boundaryless real manifold `N`. -/
theorem isSubmersion_source {I : ModelWithCorners ℝ E H} [I.Boundaryless] {n : ℕ∞ω}
    [IsManifold I n N] (hn : 1 ≤ n) :
    Manifold.IsSubmersion I I n (Quiver.Total.left : Quiver.Total (Discrete N) → Discrete N) := by
  have hne : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hsub : Manifold.IsSubmersion I I n (sourceDiffeomorph I n N) :=
    ((sourceDiffeomorph I n N).contMDiff.isSubmersionOfComplement_of_surjective_mfderiv hn
      fun a ↦ by
        have hid := mfderiv_comp (sourceDiffeomorph I n N a)
          ((sourceDiffeomorph I n N).contMDiff.mdifferentiable hne _)
          ((sourceDiffeomorph I n N).symm.contMDiff.mdifferentiable hne _)
        have heq : ⇑(sourceDiffeomorph I n N) ∘ ⇑(sourceDiffeomorph I n N).symm = id :=
          funext (sourceDiffeomorph I n N).apply_symm_apply
        rw [(sourceDiffeomorph I n N).symm_apply_apply, heq, mfderiv_id] at hid
        intro v
        refine ⟨mfderiv I I (sourceDiffeomorph I n N).symm (sourceDiffeomorph I n N a) v, ?_⟩
        exact congrArg (fun f : TangentSpace I _ →L[ℝ] TangentSpace I _ ↦ f v)
          hid.symm).isSubmersion
  exact coe_sourceDiffeomorph I n (N := N) ▸ hsub

/-- The target map of `Discrete N` is a `C^n` submersion (`1 ≤ n`). -/
theorem isSubmersion_target {I : ModelWithCorners ℝ E H} [I.Boundaryless] {n : ℕ∞ω}
    [IsManifold I n N] (hn : 1 ≤ n) :
    Manifold.IsSubmersion I I n (Quiver.Total.right : Quiver.Total (Discrete N) → Discrete N) :=
  target_eq_source N ▸ isSubmersion_source hn

/-- The unit groupoid `Discrete N` of any finite-dimensional boundaryless smooth real manifold `N`
(not necessarily Hausdorff) is a Lie groupoid. -/
instance isLieGroupoid (I : ModelWithCorners ℝ E H) [I.Boundaryless] [IsManifold I ∞ N] :
    IsLieGroupoid I I (Discrete N) := by
  have hs : Manifold.IsSubmersion I I ∞
      (Quiver.Total.left : Quiver.Total (Discrete N) → Discrete N) :=
    isSubmersion_source (by simp)
  have hinv_eq : (fun a : Quiver.Total (Discrete N) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (Discrete N))) = id := by
    funext a
    rcases a with ⟨⟨x⟩, ⟨y⟩, f⟩
    obtain rfl := Discrete.eq_of_hom f
    exact Quiver.Total.mk.injEq .. |>.mpr
      ⟨rfl, rfl, heq_of_eq (by simp [Subsingleton.elim f (𝟙 _)])⟩
  have hinv : ContMDiff I I ∞ fun a : Quiver.Total (Discrete N) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (Discrete N)) :=
    hinv_eq ▸ contMDiff_id
  refine IsLieGroupoid.of_source_inverse_mul I I (Discrete N) hs hinv ?_ t2Space_sourceFiber
  let := transverseFiberProductChartedSpace
    (f := (Quiver.Total.left : Quiver.Total (Discrete N) → Discrete N))
    (g := (Quiver.Total.right : Quiver.Total (Discrete N) → Discrete N))
    (n := (∞ : ℕ∞ω)) (by simp)
    hs.contMDiff (hs.contMDiff.comp hinv)
    (transverse_of_isSubmersion_left (by simp) hs)
  have hemb := isSmoothEmbedding_coe_transverseFiberProduct
    (f := (Quiver.Total.left : Quiver.Total (Discrete N) → Discrete N))
    (g := (Quiver.Total.right : Quiver.Total (Discrete N) → Discrete N))
    (n := (∞ : ℕ∞ω)) (by simp)
    hs.contMDiff (hs.contMDiff.comp hinv)
    (transverse_of_isSubmersion_left (by simp) hs)
  have heq : (fun p : {p : Quiver.Total (Discrete N) × Quiver.Total (Discrete N) //
      p.1.left = p.2.right} ↦ p.1.2.comp p.1.1 p.2.symm) = fun p ↦ p.1.1 := by
    funext p
    rcases p with ⟨⟨⟨⟨x⟩, ⟨y⟩, f⟩, ⟨⟨w⟩, ⟨z⟩, g⟩⟩, hp⟩
    obtain rfl := Discrete.eq_of_hom f
    obtain rfl := Discrete.eq_of_hom g
    cases hp
    rw [Quiver.Total.comp_def]
    simp only [eqToHom_refl, Category.id_comp]
    congr 1
    exact Subsingleton.elim _ _
  exact heq ▸ hemb.contMDiff.fst

/-- Composable pairs of the unit groupoid `Discrete N` form the diagonal, diffeomorphic to `N`. -/
noncomputable def composablePairsDiffeomorph (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (N : Type*) [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] :
    letI := IsLieGroupoid.composablePairsChartedSpace I I (Discrete N)
    {p : Quiver.Total (Discrete N) × Quiver.Total (Discrete N) // p.1.left = p.2.right} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ E + finrank ℝ E - finrank ℝ E) → ℝ), I⟯ N := by
  letI := IsLieGroupoid.composablePairsChartedSpace I I (Discrete N)
  have hemb := IsLieGroupoid.isSmoothEmbedding_coe_composablePairs I I (Discrete N)
  exact
    { toFun := fun p ↦ arrowDiffeomorph I ∞ N p.1.1
      invFun := fun x ↦ ⟨((arrowDiffeomorph I ∞ N).symm x, (arrowDiffeomorph I ∞ N).symm x),
        by simp⟩
      left_inv := fun p ↦ by
        rcases p with ⟨⟨⟨⟨x⟩, ⟨y⟩, f⟩, ⟨⟨w⟩, ⟨z⟩, g⟩⟩, hp⟩
        obtain rfl := Discrete.eq_of_hom f
        obtain rfl := Discrete.eq_of_hom g
        cases hp
        apply Subtype.ext
        simp [Subsingleton.elim f (𝟙 _), Subsingleton.elim g (𝟙 _)]
      right_inv := fun x ↦ by simp
      contMDiff_toFun := (arrowDiffeomorph I ∞ N).contMDiff.comp hemb.contMDiff.fst
      contMDiff_invFun := hemb.contMDiff_iff_comp.mpr
        ((arrowDiffeomorph I ∞ N).symm.contMDiff.prodMk (arrowDiffeomorph I ∞ N).symm.contMDiff) }

@[simp]
theorem composablePairsDiffeomorph_apply (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [IsManifold I ∞ N]
    (p : {p : Quiver.Total (Discrete N) × Quiver.Total (Discrete N) // p.1.left = p.2.right}) :
    letI := IsLieGroupoid.composablePairsChartedSpace I I (Discrete N)
    composablePairsDiffeomorph I N p = p.1.1.left.as := by
  let := IsLieGroupoid.composablePairsChartedSpace I I (Discrete N)
  simp [composablePairsDiffeomorph]
  rfl

@[simp]
theorem composablePairsDiffeomorph_symm_apply (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [IsManifold I ∞ N] (x : N) :
    letI := IsLieGroupoid.composablePairsChartedSpace I I (Discrete N)
    (composablePairsDiffeomorph I N).symm x =
      ⟨(⟨⟨x⟩, ⟨x⟩, 𝟙 _⟩, ⟨⟨x⟩, ⟨x⟩, 𝟙 _⟩), rfl⟩ := by
  let := IsLieGroupoid.composablePairsChartedSpace I I (Discrete N)
  simp [composablePairsDiffeomorph]
  rfl

/-- The model dimension of composable pairs of `Discrete N` equals `dim N`. -/
theorem finrank_composablePairs (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    finrank ℝ E + finrank ℝ E - finrank ℝ E = finrank ℝ E :=
  Nat.add_sub_cancel _ _

/-- Every degree `k` of the smooth nerve of `Discrete N` has dimension `dim N`. -/
@[simp]
theorem nerveModelDim_eq (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) :
    IsLieGroupoid.nerveModelDim (finrank ℝ E) (finrank ℝ E) k = finrank ℝ E := by
  simp [IsLieGroupoid.nerveModelDim_eq_add_mul le_rfl]

end LieGroupoid

end TauCeti.UnitGroupoid

namespace TauCeti.PairGroupoid

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]

/-- Objects of `Codiscrete N` carry the charted-space structure pulled back from `N`. -/
instance instChartedSpaceObjects : ChartedSpace H (Codiscrete N) :=
  (objectHomeomorph N).pullbackChartedSpace

/-- Objects of `Codiscrete N` form a `C^n` manifold whenever `N` does. -/
instance instIsManifoldObjects (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n N] :
    IsManifold I n (Codiscrete N) :=
  (objectHomeomorph N).pullback_isManifold I n

/-- Forgetting the categorical wrapper on `Codiscrete N` as a `C^n` diffeomorphism. -/
def objectDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (N : Type*) [TopologicalSpace N] [ChartedSpace H N] : Codiscrete N ≃ₘ^n⟮I, I⟯ N :=
  (objectHomeomorph N).pullbackDiffeomorph I n

@[simp]
theorem objectDiffeomorph_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (x : Codiscrete N) :
    objectDiffeomorph I n N x = x.as := by simp [objectDiffeomorph]

@[simp]
theorem objectDiffeomorph_symm_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (x : N) :
    (objectDiffeomorph I n N).symm x = Codiscrete.mk x := by simp [objectDiffeomorph]

@[simp]
theorem objectDiffeomorph_toHomeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    (objectDiffeomorph I n N).toHomeomorph = objectHomeomorph N := by simp [objectDiffeomorph]

/-- Total arrows of `Codiscrete N` carry the charted-space structure pulled back from `N × N` along
`arrowHomeomorph`, in `(target, source)` coordinates. -/
instance instChartedSpaceArrows : ChartedSpace (ModelProd H H) (Quiver.Total (Codiscrete N)) :=
  (arrowHomeomorph N).pullbackChartedSpace

/-- Total arrows of `Codiscrete N` form a `C^n` manifold whenever `N` does. -/
instance instIsManifoldArrows (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n N] :
    IsManifold (I.prod I) n (Quiver.Total (Codiscrete N)) :=
  (arrowHomeomorph N).pullback_isManifold (I.prod I) n

/-- The total-arrow space of `Codiscrete N` is `C^n` diffeomorphic to `N × N` in `(target, source)`
coordinates. -/
def arrowDiffeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (N : Type*) [TopologicalSpace N] [ChartedSpace H N] :
    Quiver.Total (Codiscrete N) ≃ₘ^n⟮I.prod I, I.prod I⟯ N × N :=
  (arrowHomeomorph N).pullbackDiffeomorph (I.prod I) n

@[simp]
theorem arrowDiffeomorph_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (a : Quiver.Total (Codiscrete N)) : arrowDiffeomorph I n N a = (a.right.as, a.left.as) := by
  simp [arrowDiffeomorph]

@[simp]
theorem arrowDiffeomorph_symm_apply (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (p : N × N) :
    (arrowDiffeomorph I n N).symm p = ⟨⟨p.2⟩, ⟨p.1⟩, default⟩ := by simp [arrowDiffeomorph]

@[simp]
theorem arrowDiffeomorph_toHomeomorph (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    (arrowDiffeomorph I n N).toHomeomorph = arrowHomeomorph N := by simp [arrowDiffeomorph]

/-- The source map of `Codiscrete N` is a `C^n` submersion over any `NontriviallyNormedField`. -/
theorem isSubmersion_source {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} [IsManifold I n N] :
    Manifold.IsSubmersion (I.prod I) I n
      (Quiver.Total.left : Quiver.Total (Codiscrete N) → Codiscrete N) := by
  have heq : (Quiver.Total.left : Quiver.Total (Codiscrete N) → Codiscrete N) =
      ⇑(objectDiffeomorph I n N).symm ∘ (Prod.snd ∘ ⇑(arrowDiffeomorph I n N)) := by
    funext a
    simp
  rw [heq]
  exact (Manifold.isSubmersionOfComplement_iff.mpr fun a ↦
    ((objectDiffeomorph I n N).symm.isLocalDiffeomorph _).comp_isSubmersionAtOfComplement
      (((arrowDiffeomorph I n N).isLocalDiffeomorph a).isSubmersionAtOfComplement_comp
        ((Manifold.isSubmersionOfComplement_snd (I := I) (J := I) (n := n) (M := N)
          (N := N)).isSubmersionAt (arrowDiffeomorph I n N a)))).isSubmersion

/-- The target map of `Codiscrete N` is a `C^n` submersion over any `NontriviallyNormedField`. -/
theorem isSubmersion_target {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} [IsManifold I n N] :
    Manifold.IsSubmersion (I.prod I) I n
      (Quiver.Total.right : Quiver.Total (Codiscrete N) → Codiscrete N) := by
  have heq : (Quiver.Total.right : Quiver.Total (Codiscrete N) → Codiscrete N) =
      ⇑(objectDiffeomorph I n N).symm ∘ (Prod.fst ∘ ⇑(arrowDiffeomorph I n N)) := by
    funext a
    simp
  rw [heq]
  exact (Manifold.isSubmersionOfComplement_iff.mpr fun a ↦
    ((objectDiffeomorph I n N).symm.isLocalDiffeomorph _).comp_isSubmersionAtOfComplement
      (((arrowDiffeomorph I n N).isLocalDiffeomorph a).isSubmersionAtOfComplement_comp
        ((Manifold.isSubmersionOfComplement_fst (I := I) (J := I) (n := n) (M := N)
          (N := N)).isSubmersionAt (arrowDiffeomorph I n N a)))).isSubmersion

end General

section Topology

/-- Every source fibre `{a // a.left = x}` of the pair groupoid is homeomorphic to `X`. -/
def sourceFiberHomeomorph {X : Type*} [TopologicalSpace X] (x : Codiscrete X) :
    {a : Quiver.Total (Codiscrete X) // a.left = x} ≃ₜ X where
  toFun a := a.1.right.as
  invFun y := ⟨⟨x, ⟨y⟩, default⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨x', y, f⟩, h⟩
    dsimp only at h
    subst h
    rfl
  right_inv _ := rfl
  continuous_toFun := by
    have h : Continuous (fun a : {a : Quiver.Total (Codiscrete X) // a.left = x} ↦
        (arrowHomeomorph X a.1).1) :=
      continuous_fst.comp ((arrowHomeomorph X).continuous.comp continuous_subtype_val)
    simpa only [arrowHomeomorph_apply] using h
  continuous_invFun := by
    have h : Continuous (fun y : X ↦ (arrowHomeomorph X).symm (y, x.as)) :=
      (arrowHomeomorph X).symm.continuous.comp (continuous_id.prodMk continuous_const)
    refine Continuous.subtype_mk ?_ _
    simpa only [arrowHomeomorph_symm_apply] using h

@[simp]
theorem sourceFiberHomeomorph_apply {X : Type*} [TopologicalSpace X] (x : Codiscrete X)
    (a : {a : Quiver.Total (Codiscrete X) // a.left = x}) :
    sourceFiberHomeomorph x a = a.1.right.as := (rfl)

@[simp]
theorem sourceFiberHomeomorph_symm_apply {X : Type*} [TopologicalSpace X] (x : Codiscrete X)
    (y : X) : (sourceFiberHomeomorph x).symm y = ⟨⟨x, ⟨y⟩, default⟩, rfl⟩ := (rfl)

/-- A source fibre of the pair groupoid is Hausdorff if and only if the base space is Hausdorff. -/
theorem t2Space_sourceFiber_iff {X : Type*} [TopologicalSpace X] (x : Codiscrete X) :
    T2Space {a : Quiver.Total (Codiscrete X) // a.left = x} ↔ T2Space X :=
  ⟨fun _ ↦ (sourceFiberHomeomorph x).t2Space, fun _ ↦ (sourceFiberHomeomorph x).symm.t2Space⟩

/-- In the pair groupoid, composing `⟨x⟩ → ⟨y⟩` followed by `⟨y⟩ → ⟨z⟩` yields `⟨x⟩ → ⟨z⟩`. -/
theorem comp_mk {X : Type*} (x y z : X) :
    (⟨⟨x⟩, ⟨y⟩, default⟩ : Quiver.Total (Codiscrete X)).comp
      ⟨⟨y⟩, ⟨z⟩, default⟩ rfl = ⟨⟨x⟩, ⟨z⟩, default⟩ := by
  rw [Quiver.Total.comp_def]
  rfl

/-- Witness showing that left translation cannot act on source fibres: for `z ≠ x`, the arrows
`g = (y, x)` (`x → y`) and `h = (z, x)` (`x → z`) share source `x` (`h.left = g.left`), yet
`g.left ≠ h.right` (`s(g) ≠ t(h)`), so the product `gh` is undefined. -/
theorem same_source_not_composable {X : Type*} (x y z : X) (hz : z ≠ x) :
    let g : Quiver.Total (Codiscrete X) := ⟨⟨x⟩, ⟨y⟩, default⟩
    let h : Quiver.Total (Codiscrete X) := ⟨⟨x⟩, ⟨z⟩, default⟩
    h.left = g.left ∧ g.left ≠ h.right :=
  ⟨rfl, fun h ↦ hz (congrArg Codiscrete.as h.symm)⟩

end Topology

section LieGroupoid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]

/-- The pair groupoid `Codiscrete N` of any Hausdorff finite-dimensional boundaryless smooth real
manifold `N` is a Lie groupoid. (The `T2Space N` hypothesis is sharp when `N` is nonempty by
`t2Space_sourceFiber_iff`.) -/
instance isLieGroupoid (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [IsManifold I ∞ N] [T2Space N] :
    IsLieGroupoid I (I.prod I) (Codiscrete N) := by
  have hs : Manifold.IsSubmersion (I.prod I) I ∞
      (Quiver.Total.left : Quiver.Total (Codiscrete N) → Codiscrete N) :=
    isSubmersion_source
  have hinv_eq : (fun a : Quiver.Total (Codiscrete N) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (Codiscrete N))) =
      ⇑(arrowDiffeomorph I ∞ N).symm ∘ Prod.swap ∘ ⇑(arrowDiffeomorph I ∞ N) := by
    funext a
    rcases a with ⟨⟨x⟩, ⟨y⟩, f⟩
    simp only [Function.comp_apply, arrowDiffeomorph_apply, Prod.swap_prod_mk,
      arrowDiffeomorph_symm_apply, Codiscrete.uniqueHom_default, Quiver.Total.mk.injEq,
      heq_eq_eq, true_and]
    exact Subsingleton.elim _ _
  have hinv : ContMDiff (I.prod I) (I.prod I) ∞ fun a : Quiver.Total (Codiscrete N) ↦
      (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total (Codiscrete N)) :=
    hinv_eq ▸ (arrowDiffeomorph I ∞ N).symm.contMDiff.comp
      ((contMDiff_snd.prodMk contMDiff_fst).comp (arrowDiffeomorph I ∞ N).contMDiff)
  refine IsLieGroupoid.of_source_inverse_mul I (I.prod I) (Codiscrete N) hs hinv ?_
    (fun x ↦ (t2Space_sourceFiber_iff x).mpr inferInstance)
  let := transverseFiberProductChartedSpace
    (f := (Quiver.Total.left : Quiver.Total (Codiscrete N) → Codiscrete N))
    (g := (Quiver.Total.right : Quiver.Total (Codiscrete N) → Codiscrete N))
    (n := (∞ : ℕ∞ω)) (by simp)
    hs.contMDiff (hs.contMDiff.comp hinv)
    (transverse_of_isSubmersion_left (by simp) hs)
  have hemb := isSmoothEmbedding_coe_transverseFiberProduct
    (f := (Quiver.Total.left : Quiver.Total (Codiscrete N) → Codiscrete N))
    (g := (Quiver.Total.right : Quiver.Total (Codiscrete N) → Codiscrete N))
    (n := (∞ : ℕ∞ω)) (by simp)
    hs.contMDiff (hs.contMDiff.comp hinv)
    (transverse_of_isSubmersion_left (by simp) hs)
  have heq : (fun p : {p : Quiver.Total (Codiscrete N) × Quiver.Total (Codiscrete N) //
      p.1.left = p.2.right} ↦ p.1.2.comp p.1.1 p.2.symm) =
      fun p ↦ (arrowDiffeomorph I ∞ N).symm
        ((arrowDiffeomorph I ∞ N p.1.1).1, (arrowDiffeomorph I ∞ N p.1.2).2) := by
    funext p
    rcases p with ⟨⟨⟨⟨y⟩, ⟨z⟩, f⟩, ⟨⟨x⟩, ⟨y'⟩, g⟩⟩, hp⟩
    dsimp only at hp
    cases hp
    simp only [Quiver.Total.mk_comp_mk, arrowDiffeomorph_apply, arrowDiffeomorph_symm_apply,
      Codiscrete.uniqueHom_default, Quiver.Total.mk.injEq, heq_eq_eq, true_and]
    exact Subsingleton.elim _ _
  exact heq ▸ (arrowDiffeomorph I ∞ N).symm.contMDiff.comp
    ((contMDiff_fst.comp ((arrowDiffeomorph I ∞ N).contMDiff.comp hemb.contMDiff.fst)).prodMk
      (contMDiff_snd.comp ((arrowDiffeomorph I ∞ N).contMDiff.comp hemb.contMDiff.snd)))

/-- Every source fibre `s⁻¹(x)` of `Codiscrete N` is diffeomorphic to `N`, via target projection. -/
noncomputable def sourceFiberDiffeomorph (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [IsManifold I ∞ N] [T2Space N] (x : Codiscrete N) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete N) x
    {a : Quiver.Total (Codiscrete N) // a.left = x} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ (E × E) - finrank ℝ E) → ℝ), I⟯ N := by
  letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete N) x
  have hemb := IsLieGroupoid.isSmoothEmbedding_coe_sourceFiber I (I.prod I) (Codiscrete N) x
  exact
    { toFun := fun a ↦ (arrowDiffeomorph I ∞ N a.1).1
      invFun := fun y ↦ ⟨(arrowDiffeomorph I ∞ N).symm (y, x.as), by simp⟩
      left_inv := fun a ↦ by
        rcases a with ⟨⟨x', ⟨y⟩, f⟩, h⟩
        dsimp only at h
        subst h
        apply Subtype.ext
        simp only [arrowDiffeomorph_apply, arrowDiffeomorph_symm_apply, Codiscrete.mk_as,
          Codiscrete.uniqueHom_default, Quiver.Total.mk.injEq, heq_eq_eq, true_and]
        exact Subsingleton.elim _ _
      right_inv := fun y ↦ by simp
      contMDiff_toFun := contMDiff_fst.comp ((arrowDiffeomorph I ∞ N).contMDiff.comp hemb.contMDiff)
      contMDiff_invFun := hemb.contMDiff_iff_comp.mpr
        ((arrowDiffeomorph I ∞ N).symm.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)) }

@[simp]
theorem sourceFiberDiffeomorph_apply (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [IsManifold I ∞ N] [T2Space N] (x : Codiscrete N)
    (a : {a : Quiver.Total (Codiscrete N) // a.left = x}) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete N) x
    sourceFiberDiffeomorph I x a = a.1.right.as := by
  let := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete N) x
  simp [sourceFiberDiffeomorph]
  rfl

@[simp]
theorem sourceFiberDiffeomorph_symm_apply (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [IsManifold I ∞ N] [T2Space N] (x : Codiscrete N) (y : N) :
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete N) x
    (sourceFiberDiffeomorph I x).symm y = ⟨⟨x, ⟨y⟩, default⟩, rfl⟩ := by
  let := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete N) x
  simp [sourceFiberDiffeomorph]
  rfl

/-- Every target fibre `t⁻¹(x)` of `Codiscrete N` is diffeomorphic to `N`, via source projection. -/
noncomputable def targetFiberDiffeomorph (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [IsManifold I ∞ N] [T2Space N] (x : Codiscrete N) :
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete N) x
    {a : Quiver.Total (Codiscrete N) // a.right = x} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ (E × E) - finrank ℝ E) → ℝ), I⟯ N := by
  letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete N) x
  have hemb := IsLieGroupoid.isSmoothEmbedding_coe_targetFiber I (I.prod I) (Codiscrete N) x
  exact
    { toFun := fun a ↦ (arrowDiffeomorph I ∞ N a.1).2
      invFun := fun w ↦ ⟨(arrowDiffeomorph I ∞ N).symm (x.as, w), by simp⟩
      left_inv := fun a ↦ by
        rcases a with ⟨⟨⟨w⟩, x', f⟩, h⟩
        dsimp only at h
        subst h
        apply Subtype.ext
        simp only [arrowDiffeomorph_apply, arrowDiffeomorph_symm_apply, Codiscrete.mk_as,
          Codiscrete.uniqueHom_default, Quiver.Total.mk.injEq, heq_eq_eq, true_and]
        exact Subsingleton.elim _ _
      right_inv := fun w ↦ by simp
      contMDiff_toFun := contMDiff_snd.comp ((arrowDiffeomorph I ∞ N).contMDiff.comp hemb.contMDiff)
      contMDiff_invFun := hemb.contMDiff_iff_comp.mpr
        ((arrowDiffeomorph I ∞ N).symm.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)) }

@[simp]
theorem targetFiberDiffeomorph_apply (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [IsManifold I ∞ N] [T2Space N] (x : Codiscrete N)
    (a : {a : Quiver.Total (Codiscrete N) // a.right = x}) :
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete N) x
    targetFiberDiffeomorph I x a = a.1.left.as := by
  let := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete N) x
  simp [targetFiberDiffeomorph]
  rfl

@[simp]
theorem targetFiberDiffeomorph_symm_apply (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [IsManifold I ∞ N] [T2Space N] (x : Codiscrete N) (w : N) :
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete N) x
    (targetFiberDiffeomorph I x).symm w = ⟨⟨⟨w⟩, x, default⟩, rfl⟩ := by
  let := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete N) x
  simp [targetFiberDiffeomorph]
  rfl

/-- Geometric composable pairs `((z, y), (y, x))` in `Codiscrete N` are diffeomorphic to
`N × N × N` via `(z, y, x)`. -/
noncomputable def composablePairsDiffeomorph (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (N : Type*) [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N] :
    letI := IsLieGroupoid.composablePairsChartedSpace I (I.prod I) (Codiscrete N)
    {p : Quiver.Total (Codiscrete N) × Quiver.Total (Codiscrete N) //
        p.1.left = p.2.right} ≃ₘ^∞⟮
      𝓘(ℝ, Fin (finrank ℝ (E × E) + finrank ℝ (E × E) - finrank ℝ E) → ℝ),
      I.prod (I.prod I)⟯ N × N × N := by
  letI := IsLieGroupoid.composablePairsChartedSpace I (I.prod I) (Codiscrete N)
  have hemb := IsLieGroupoid.isSmoothEmbedding_coe_composablePairs I (I.prod I) (Codiscrete N)
  exact
    { toFun := fun p ↦ ((arrowDiffeomorph I ∞ N p.1.1).1,
        (arrowDiffeomorph I ∞ N p.1.1).2, (arrowDiffeomorph I ∞ N p.1.2).2)
      invFun := fun q ↦ ⟨((arrowDiffeomorph I ∞ N).symm (q.1, q.2.1),
        (arrowDiffeomorph I ∞ N).symm (q.2.1, q.2.2)), by simp⟩
      left_inv := fun p ↦ by
        rcases p with ⟨⟨⟨⟨y⟩, ⟨z⟩, f⟩, ⟨⟨x⟩, ⟨y'⟩, g⟩⟩, hp⟩
        dsimp only at hp
        cases hp
        apply Subtype.ext
        simp only [arrowDiffeomorph_apply, arrowDiffeomorph_symm_apply,
          Codiscrete.uniqueHom_default, Prod.mk.injEq, Quiver.Total.mk.injEq, heq_eq_eq, true_and]
        exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
      right_inv := fun q ↦ by simp
      contMDiff_toFun :=
        (contMDiff_fst.comp ((arrowDiffeomorph I ∞ N).contMDiff.comp hemb.contMDiff.fst)).prodMk
          ((contMDiff_snd.comp
            ((arrowDiffeomorph I ∞ N).contMDiff.comp hemb.contMDiff.fst)).prodMk
            (contMDiff_snd.comp ((arrowDiffeomorph I ∞ N).contMDiff.comp hemb.contMDiff.snd)))
      contMDiff_invFun := hemb.contMDiff_iff_comp.mpr
        (((arrowDiffeomorph I ∞ N).symm.contMDiff.comp
          (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd))).prodMk
          ((arrowDiffeomorph I ∞ N).symm.contMDiff.comp
            ((contMDiff_fst.comp contMDiff_snd).prodMk (contMDiff_snd.comp contMDiff_snd)))) }

@[simp]
theorem composablePairsDiffeomorph_apply (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [IsManifold I ∞ N] [T2Space N]
    (p : {p : Quiver.Total (Codiscrete N) × Quiver.Total (Codiscrete N) // p.1.left = p.2.right}) :
    letI := IsLieGroupoid.composablePairsChartedSpace I (I.prod I) (Codiscrete N)
    composablePairsDiffeomorph I N p = (p.1.1.right.as, p.1.1.left.as, p.1.2.left.as) := by
  let := IsLieGroupoid.composablePairsChartedSpace I (I.prod I) (Codiscrete N)
  simp [composablePairsDiffeomorph]
  rfl

@[simp]
theorem composablePairsDiffeomorph_symm_apply (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [IsManifold I ∞ N] [T2Space N] (q : N × N × N) :
    letI := IsLieGroupoid.composablePairsChartedSpace I (I.prod I) (Codiscrete N)
    (composablePairsDiffeomorph I N).symm q =
      ⟨(⟨⟨q.2.1⟩, ⟨q.1⟩, default⟩, ⟨⟨q.2.2⟩, ⟨q.2.1⟩, default⟩), rfl⟩ := by
  let := IsLieGroupoid.composablePairsChartedSpace I (I.prod I) (Codiscrete N)
  simp [composablePairsDiffeomorph]
  rfl

/-- In `Codiscrete N`, left translation by `g = (y, x)` (`x → y`) sends `(x, w) ∈ t⁻¹(x)` to
`(y, w) ∈ t⁻¹(y)`. -/
theorem leftTranslationDiffeomorph_apply_mk (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [IsManifold I ∞ N] [T2Space N] (w x y : N) :
    let g : Quiver.Total (Codiscrete N) := ⟨⟨x⟩, ⟨y⟩, default⟩
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete N) g.left
    letI := IsLieGroupoid.targetFiberChartedSpace I (I.prod I) (Codiscrete N) g.right
    (IsLieGroupoid.leftTranslationDiffeomorph I (I.prod I) (Codiscrete N) g
      ⟨⟨⟨w⟩, ⟨x⟩, default⟩, rfl⟩).val = ⟨⟨w⟩, ⟨y⟩, default⟩ := by
  extract_lets
  rw [IsLieGroupoid.leftTranslationDiffeomorph_apply]
  exact comp_mk w x y

/-- In `Codiscrete N`, right translation by `g = (y, x)` (`x → y`) sends `(w, y) ∈ s⁻¹(y)` to
`(w, x) ∈ s⁻¹(x)`. -/
theorem rightTranslationDiffeomorph_apply_mk (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [IsManifold I ∞ N] [T2Space N] (w x y : N) :
    let g : Quiver.Total (Codiscrete N) := ⟨⟨x⟩, ⟨y⟩, default⟩
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete N) g.right
    letI := IsLieGroupoid.sourceFiberChartedSpace I (I.prod I) (Codiscrete N) g.left
    (IsLieGroupoid.rightTranslationDiffeomorph I (I.prod I) (Codiscrete N) g
      ⟨⟨⟨y⟩, ⟨w⟩, default⟩, rfl⟩).val = ⟨⟨x⟩, ⟨w⟩, default⟩ := by
  extract_lets
  rw [IsLieGroupoid.rightTranslationDiffeomorph_apply]
  exact comp_mk x y w

/-- The arrow manifold of `Codiscrete N` has dimension `2 * dim N`. -/
theorem finrank_arrows (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    finrank ℝ (E × E) = 2 * finrank ℝ E := by
  rw [Module.finrank_prod, two_mul]

/-- Each source and target fibre of `Codiscrete N` has dimension `dim N`. -/
theorem finrank_sourceFiber (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    finrank ℝ (E × E) - finrank ℝ E = finrank ℝ E := by
  rw [finrank_arrows]
  omega

/-- The composable-pairs manifold of `Codiscrete N` has dimension `3 * dim N`. -/
theorem finrank_composablePairs (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    finrank ℝ (E × E) + finrank ℝ (E × E) - finrank ℝ E = 3 * finrank ℝ E := by
  rw [finrank_arrows]
  omega

/-- Degree `k` of the smooth nerve of `Codiscrete N` has dimension `(k + 1) * dim N`. -/
theorem nerveModelDim_eq (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (k : ℕ) :
    IsLieGroupoid.nerveModelDim (finrank ℝ E) (finrank ℝ (E × E)) k =
      (k + 1) * finrank ℝ E := by
  have hle : finrank ℝ E ≤ finrank ℝ (E × E) := by
    rw [finrank_arrows]
    omega
  rw [IsLieGroupoid.nerveModelDim_eq_add_mul hle, finrank_sourceFiber]
  ring

end LieGroupoid

end TauCeti.PairGroupoid
