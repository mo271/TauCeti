/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Groupoid.Basic

import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse

/-!
# Tangent-space identities at units of a Lie groupoid

For a Lie groupoid `C` with object manifold modelled on `I` and arrow manifold modelled on `J`,
the unit section `u : C → Quiver.Total C`, `x ↦ ⟨x, x, 𝟙 x⟩`, satisfies `s ∘ u = id`, `t ∘ u = id`,
and `inv ∘ u = u`. Consequently:

* `u` is a smooth embedding (`TauCeti.IsLieGroupoid.isSmoothEmbedding_unit`);
* `du_x` is injective and provides a canonical right inverse to both `ds_{1_x}` and `dt_{1_x}`;
* `T_{1_x} Γ` splits as the direct sums `range(du_x) ⊕ ker(ds_{1_x})` and
  `range(du_x) ⊕ ker(dt_{1_x})`;
* the differential of geometric multiplication `m : Γ ×_{s,t} Γ → Γ` at `(1_x, 1_x)` satisfies
  `dm_{(1_x, 1_x)}(ξ) = v + w - du_x(ds_{1_x}(v))` where `v = d(pr₁) ξ` and `w = d(pr₂) ξ`
  (`TauCeti.IsLieGroupoid.mfderiv_mul_unit_apply`);
* the differential of arrow inversion at `1_x` satisfies
  `d(inv)_{1_x}(v) = du_x(ds_{1_x}(v) + dt_{1_x}(v)) - v`, after identifying
  `TangentSpace J ⟨x, x, inv (𝟙 x)⟩` with `TangentSpace J ⟨x, x, 𝟙 x⟩` via `tangentSpaceCast`
  (`TauCeti.IsLieGroupoid.mfderiv_inverse_unit_apply`).

## Main results

* `TauCeti.IsLieGroupoid.isSmoothEmbedding_unit`: the unit section is a smooth embedding.
* `TauCeti.IsLieGroupoid.mfderiv_source_comp_mfderiv_unit`,
  `TauCeti.IsLieGroupoid.mfderiv_target_comp_mfderiv_unit`: `ds_{1_x} ∘ du_x = id` and
  `dt_{1_x} ∘ du_x = id`.
* `TauCeti.IsLieGroupoid.isCompl_range_mfderiv_unit_ker_mfderiv_source`,
  `TauCeti.IsLieGroupoid.isCompl_range_mfderiv_unit_ker_mfderiv_target`: direct-sum splittings of
  the tangent space at a unit.
* `TauCeti.IsLieGroupoid.mfderiv_mul_unit_apply`: formula for `dm_{(1_x, 1_x)}`.
* `TauCeti.IsLieGroupoid.mfderiv_inverse_unit_apply`: formula for `d(inv)_{1_x}`.
* `TauCeti.IsLieGroupoid.mfderiv_inverse_unit_of_ker_source`: specialization to `ker(ds_{1_x})`.

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), Section 1.4.
* M. Crainic and R. L. Fernandes, *Lectures on integrability of Lie brackets*, Geom. Topol.
  Monogr. **17** (2011), Section 1.4.
-/

public section

open CategoryTheory Function Manifold Module Set Topology
open scoped ContDiff Manifold

namespace TauCeti.IsLieGroupoid

section Helpers

private theorem tangentSpaceCast_mfderiv_congr_fun
    {E₁ H₁ X₁ E₂ H₂ X₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace X₁] [ChartedSpace H₁ X₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace X₂] [ChartedSpace H₂ X₂]
    {f g : X₁ → X₂} (h : f = g) (x : X₁) (v : TangentSpace I₁ x) :
    tangentSpaceCast I₂ (f x) (g x) (mfderiv I₁ I₂ f x v) = mfderiv I₁ I₂ g x v := by
  subst h
  rfl

private theorem tangentSpaceCast_mfderiv_congr_pt
    {E₁ H₁ X₁ E₂ H₂ X₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace X₁] [ChartedSpace H₁ X₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace X₂] [ChartedSpace H₂ X₂]
    (f : X₁ → X₂) {a b : X₁} (hab : a = b) (v : TangentSpace I₁ a) :
    tangentSpaceCast I₂ (f a) (f b) (mfderiv I₁ I₂ f a v) =
      mfderiv I₁ I₂ f b (tangentSpaceCast I₁ a b v) := by
  subst hab
  rfl

private theorem tangentSpaceCast_trans_apply
    {E₁ H₁ X₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    (I₁ : ModelWithCorners ℝ E₁ H₁) [TopologicalSpace X₁] [ChartedSpace H₁ X₁]
    (a b c : X₁) (v : TangentSpace I₁ a) :
    tangentSpaceCast I₁ b c (tangentSpaceCast I₁ a b v) = tangentSpaceCast I₁ a c v :=
  rfl

end Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H']
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
  [I.Boundaryless] [J.Boundaryless]
  (C : Type*) [Category C] [IsGroupoid C]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)] [IsLieGroupoid I J C]

/-! ### Unit embedding and direct-sum splittings -/

/-- The unit section `x ↦ 1_x` is a smooth embedding of `C` into `Quiver.Total C`. -/
theorem isSmoothEmbedding_unit :
    Manifold.IsSmoothEmbedding I J ∞ fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C) :=
  (contMDiff_unit (I := I) (J := J) (C := C)).isSmoothEmbedding_of_leftInverse (by simp)
    ((contMDiff_source I J C).of_le (by simp)) fun _ ↦ rfl

/-- Differentiating `s ∘ u = id` at `x`: `ds_{1_x} ∘ du_x = id`. -/
theorem mfderiv_source_comp_mfderiv_unit (x : C) :
    (mfderiv J I (Quiver.Total.left : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩).comp
      (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x) =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  rw [← mfderiv_comp x
    ((contMDiff_source I J C _).mdifferentiableAt (by simp))
    ((contMDiff_unit (I := I) (J := J) (C := C) x).mdifferentiableAt (by simp))]
  exact mfderiv_id

@[simp]
theorem mfderiv_source_mfderiv_unit (x : C) (v : TangentSpace I x) :
    mfderiv J I (Quiver.Total.left : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩
      (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x v) = v :=
  congrArg (fun L ↦ L v) (mfderiv_source_comp_mfderiv_unit I J C x)

/-- Differentiating `t ∘ u = id` at `x`: `dt_{1_x} ∘ du_x = id`. -/
theorem mfderiv_target_comp_mfderiv_unit (x : C) :
    (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩).comp
      (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x) =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  rw [← mfderiv_comp x
    ((contMDiff_target I J C _).mdifferentiableAt (by simp))
    ((contMDiff_unit (I := I) (J := J) (C := C) x).mdifferentiableAt (by simp))]
  exact mfderiv_id

@[simp]
theorem mfderiv_target_mfderiv_unit (x : C) (v : TangentSpace I x) :
    mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩
      (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x v) = v :=
  congrArg (fun L ↦ L v) (mfderiv_target_comp_mfderiv_unit I J C x)

/-- The differential of the unit section is injective at every object. -/
theorem injective_mfderiv_unit (x : C) :
    Injective (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x) :=
  LeftInverse.injective (mfderiv_source_mfderiv_unit I J C x)

/-- At a unit arrow `1_x`, `ds_{1_x}` is split surjective with right inverse `du_x`. -/
theorem hasRightInverse_mfderiv_source_unit (x : C) :
    (mfderiv J I (Quiver.Total.left : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩).HasRightInverse :=
  ⟨mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x,
    mfderiv_source_mfderiv_unit I J C x⟩

/-- At a unit arrow `1_x`, `dt_{1_x}` is split surjective with right inverse `du_x`. -/
theorem hasRightInverse_mfderiv_target_unit (x : C) :
    (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩).HasRightInverse :=
  ⟨mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x,
    mfderiv_target_mfderiv_unit I J C x⟩

/-- Direct-sum splitting `T_{1_x} Γ = range(du_x) ⊕ ker(ds_{1_x})`. -/
theorem isCompl_range_mfderiv_unit_ker_mfderiv_source (x : C) :
    IsCompl
      (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x).range
      (mfderiv J I (Quiver.Total.left : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩).ker := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro v ⟨w, rfl⟩ hv
    have hw : w = 0 := by
      have h' : mfderiv J I (Quiver.Total.left : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩
          (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x w) = 0 := hv
      rwa [mfderiv_source_mfderiv_unit I J C x w] at h'
    simp [hw]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    let u := mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x
    let s := mfderiv J I (Quiver.Total.left : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩
    have hsplit : v = u (s v) + (v - u (s v)) := by abel
    rw [hsplit]
    refine Submodule.add_mem_sup ⟨s v, rfl⟩ ?_
    change s (v - u (s v)) = 0
    rw [map_sub, mfderiv_source_mfderiv_unit I J C x (s v), sub_self]

/-- Direct-sum splitting `T_{1_x} Γ = range(du_x) ⊕ ker(dt_{1_x})`. -/
theorem isCompl_range_mfderiv_unit_ker_mfderiv_target (x : C) :
    IsCompl
      (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x).range
      (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩).ker := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro v ⟨w, rfl⟩ hv
    have hw : w = 0 := by
      have h' : mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩
          (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x w) = 0 := hv
      rwa [mfderiv_target_mfderiv_unit I J C x w] at h'
    simp [hw]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    let u := mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x
    let t := mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩
    have hsplit : v = u (t v) + (v - u (t v)) := by abel
    rw [hsplit]
    refine Submodule.add_mem_sup ⟨t v, rfl⟩ ?_
    change t (v - u (t v)) = 0
    rw [map_sub, mfderiv_target_mfderiv_unit I J C x (t v), sub_self]

/-- Inversion fixes the unit section, so `d(inv)_{1_x}(du_x v) = du_x v` after casting along
`inv (𝟙 x) = 𝟙 x`. -/
@[simp]
theorem mfderiv_inverse_mfderiv_unit (x : C) (v : TangentSpace I x) :
    tangentSpaceCast J (⟨x, x, inv (𝟙 x)⟩ : Quiver.Total C) ⟨x, x, 𝟙 x⟩
      (mfderiv J J (fun a : Quiver.Total C ↦ (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total C))
        ⟨x, x, 𝟙 x⟩ (mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x v)) =
      mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x v := by
  let invMap : Quiver.Total C → Quiver.Total C := fun a ↦ ⟨a.right, a.left, inv a.hom⟩
  let u : C → Quiver.Total C := fun y ↦ ⟨y, y, 𝟙 y⟩
  have hcomp : invMap ∘ u = u := funext fun y ↦ by simp [invMap, u]
  have hdiff := mfderiv_comp x
    ((contMDiff_inverse (I := I) (J := J) (C := C) (u x)).mdifferentiableAt (by simp))
    ((contMDiff_unit (I := I) (J := J) (C := C) x).mdifferentiableAt (by simp))
  have hval : mfderiv J J invMap (u x) (mfderiv I J u x v) = mfderiv I J (invMap ∘ u) x v := by
    rw [hdiff]
    rfl
  rw [hval]
  exact tangentSpaceCast_mfderiv_congr_fun hcomp x v

/-! ### Differentials of multiplication and inversion at units -/

/-- **Differential of multiplication at a unit pair.** For a tangent vector `ξ` to `Γ ×_{s,t} Γ`
at `(1_x, 1_x)`, writing `v = d(pr₁) ξ` and `w = d(pr₂) ξ` (which satisfy `ds(v) = dt(w)`), the
differential of geometric multiplication is `dm_{(1_x, 1_x)}(ξ) = v + w - du_x(ds_{1_x}(v))`. -/
theorem mfderiv_mul_unit_apply (x : C) :
    letI := composablePairsChartedSpace I J C
    ∀ ξ : TangentSpace 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
        (⟨(⟨x, x, 𝟙 x⟩, ⟨x, x, 𝟙 x⟩), rfl⟩ :
          {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right}),
      tangentSpaceCast J
        ((⟨x, x, 𝟙 x⟩ : Quiver.Total C).comp ⟨x, x, 𝟙 x⟩ rfl) ⟨x, x, 𝟙 x⟩
        (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
          (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦
            p.1.2.comp p.1.1 p.2.symm) ⟨(⟨x, x, 𝟙 x⟩, ⟨x, x, 𝟙 x⟩), rfl⟩ ξ) =
        mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
          (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦ p.1.1)
          ⟨(⟨x, x, 𝟙 x⟩, ⟨x, x, 𝟙 x⟩), rfl⟩ ξ +
        mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
          (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦ p.1.2)
          ⟨(⟨x, x, 𝟙 x⟩, ⟨x, x, 𝟙 x⟩), rfl⟩ ξ -
        mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x
          (mfderiv J I (Quiver.Total.left : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩
            (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ) J
              (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right} ↦ p.1.1)
              ⟨(⟨x, x, 𝟙 x⟩, ⟨x, x, 𝟙 x⟩), rfl⟩ ξ)) := by
  let := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  let K := 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
  let P := {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right}
  let u : C → Quiver.Total C := fun y ↦ ⟨y, y, 𝟙 y⟩
  let m : P → Quiver.Total C := fun p ↦ p.1.2.comp p.1.1 p.2.symm
  let p₀ : P := ⟨(u x, u x), rfl⟩
  let pr₁ : P → Quiver.Total C := fun p ↦ p.1.1
  let pr₂ : P → Quiver.Total C := fun p ↦ p.1.2
  have hu : ContMDiff I J ∞ u := contMDiff_unit (I := I) (J := J) (C := C)
  have hs : ContMDiff J I ∞ (Quiver.Total.left : Quiver.Total C → C) := contMDiff_source I J C
  have ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C) := contMDiff_target I J C
  have hemb := isSmoothEmbedding_coe_composablePairs I J C
  have hm : ContMDiff K J ∞ m := contMDiff_mul_composablePairs I J C
  have hpr₁ : ContMDiff K J ∞ pr₁ := hemb.contMDiff.fst
  have hpr₂ : ContMDiff K J ∞ pr₂ := hemb.contMDiff.snd
  -- Left, right, and diagonal unit inclusions into `Γ ×_{s,t} Γ`.
  let ι₁ : Quiver.Total C → P := fun g ↦ ⟨(g, u g.left), rfl⟩
  let ι₂ : Quiver.Total C → P := fun h ↦ ⟨(u h.right, h), rfl⟩
  let δ : C → P := fun y ↦ ⟨(u y, u y), rfl⟩
  have hι₁ : ContMDiff J K ∞ ι₁ :=
    hemb.contMDiff_iff_comp.mpr (contMDiff_id.prodMk (hu.comp hs))
  have hι₂ : ContMDiff J K ∞ ι₂ :=
    hemb.contMDiff_iff_comp.mpr ((hu.comp ht).prodMk contMDiff_id)
  have hδ : ContMDiff I K ∞ δ :=
    hemb.contMDiff_iff_comp.mpr (hu.prodMk hu)
  have hval_diff : MDifferentiableAt K (J.prod J)
      (Subtype.val : P → Quiver.Total C × Quiver.Total C) p₀ :=
    (hemb.contMDiff p₀).mdifferentiableAt (by simp)
  intro ξ
  set v : TangentSpace J (u x) := mfderiv K J pr₁ p₀ ξ
  set w : TangentSpace J (u x) := mfderiv K J pr₂ p₀ ξ
  -- From the fibre-product tangent equation at `p₀`, `ds(v) = dt(w)`.
  have hcompat : mfderiv J I (Quiver.Total.left : Quiver.Total C → C) (u x) v =
      mfderiv J I (Quiver.Total.right : Quiver.Total C → C) (u x) w := by
    have hmem := (mem_range_mfderiv_coe_composablePairs_iff I J C p₀
      (mfderiv K (J.prod J) Subtype.val p₀ ξ)).1 ⟨ξ, rfl⟩
    rw [← hval_diff.mfderiv_fst_apply, ← hval_diff.mfderiv_snd_apply] at hmem
    exact hmem
  -- Compute projections of `dι₁ v`, `dι₂ w`, and `dδ (ds v)`.
  have hpr₁_ι₁ : mfderiv K J pr₁ p₀ (mfderiv J K ι₁ (u x) v) = v := by
    rw [← ContinuousLinearMap.comp_apply,
      ← mfderiv_comp (u x) ((hpr₁ p₀).mdifferentiableAt (by simp))
        ((hι₁ (u x)).mdifferentiableAt (by simp))]
    exact congrArg (fun L ↦ L v) (mfderiv_id : mfderiv J J (pr₁ ∘ ι₁) (u x) = _)
  have hpr₂_ι₁ : mfderiv K J pr₂ p₀ (mfderiv J K ι₁ (u x) v) =
      mfderiv I J u x (mfderiv J I Quiver.Total.left (u x) v) := by
    rw [← ContinuousLinearMap.comp_apply,
      ← mfderiv_comp (u x) ((hpr₂ p₀).mdifferentiableAt (by simp))
        ((hι₁ (u x)).mdifferentiableAt (by simp))]
    change mfderiv J J (u ∘ Quiver.Total.left) (u x) v = _
    rw [mfderiv_comp (u x) ((hu x).mdifferentiableAt (by simp))
      ((hs (u x)).mdifferentiableAt (by simp))]
    rfl
  have hpr₁_ι₂ : mfderiv K J pr₁ p₀ (mfderiv J K ι₂ (u x) w) =
      mfderiv I J u x (mfderiv J I Quiver.Total.right (u x) w) := by
    rw [← ContinuousLinearMap.comp_apply,
      ← mfderiv_comp (u x) ((hpr₁ p₀).mdifferentiableAt (by simp))
        ((hι₂ (u x)).mdifferentiableAt (by simp))]
    change mfderiv J J (u ∘ Quiver.Total.right) (u x) w = _
    rw [mfderiv_comp (u x) ((hu x).mdifferentiableAt (by simp))
      ((ht (u x)).mdifferentiableAt (by simp))]
    rfl
  have hpr₂_ι₂ : mfderiv K J pr₂ p₀ (mfderiv J K ι₂ (u x) w) = w := by
    rw [← ContinuousLinearMap.comp_apply,
      ← mfderiv_comp (u x) ((hpr₂ p₀).mdifferentiableAt (by simp))
        ((hι₂ (u x)).mdifferentiableAt (by simp))]
    exact congrArg (fun L ↦ L w) (mfderiv_id : mfderiv J J (pr₂ ∘ ι₂) (u x) = _)
  have hpr₁_δ (z : TangentSpace I x) :
      mfderiv K J pr₁ p₀ (mfderiv I K δ x z) = mfderiv I J u x z := by
    rw [← ContinuousLinearMap.comp_apply,
      ← mfderiv_comp x ((hpr₁ p₀).mdifferentiableAt (by simp))
        ((hδ x).mdifferentiableAt (by simp))]
    rfl
  have hpr₂_δ (z : TangentSpace I x) :
      mfderiv K J pr₂ p₀ (mfderiv I K δ x z) = mfderiv I J u x z := by
    rw [← ContinuousLinearMap.comp_apply,
      ← mfderiv_comp x ((hpr₂ p₀).mdifferentiableAt (by simp))
        ((hδ x).mdifferentiableAt (by simp))]
    rfl
  -- Hence `ξ = dι₁ v + dι₂ w - dδ (ds v)` since both sides have the same two projections.
  let sv := mfderiv J I (Quiver.Total.left : Quiver.Total C → C) (u x) v
  have hξ_eq : ξ = mfderiv J K ι₁ (u x) v + mfderiv J K ι₂ (u x) w - mfderiv I K δ x sv := by
    apply sub_eq_zero.mp
    apply eq_zero_of_mfderiv_composablePairs I J C p₀
    · have h1 : mfderiv K J pr₁ p₀ (ξ - (mfderiv J K ι₁ (u x) v +
          mfderiv J K ι₂ (u x) w - mfderiv I K δ x sv)) = 0 := by
        rw [map_sub, map_sub, map_add, hpr₁_ι₁, hpr₁_ι₂, hpr₁_δ, ← hcompat]
        change v - (v + mfderiv I J u x sv - mfderiv I J u x sv) = 0
        abel
      exact h1
    · have h2 : mfderiv K J pr₂ p₀ (ξ - (mfderiv J K ι₁ (u x) v +
          mfderiv J K ι₂ (u x) w - mfderiv I K δ x sv)) = 0 := by
        rw [map_sub, map_sub, map_add, hpr₂_ι₁, hpr₂_ι₂, hpr₂_δ]
        change w - (mfderiv I J u x sv + w - mfderiv I J u x sv) = 0
        abel
      exact h2
  -- Evaluate `dm` on each summand via `m ∘ ι₁ = id`, `m ∘ ι₂ = id`, and `m ∘ δ = u`.
  have hm_ι₁ : m ∘ ι₁ = id := funext fun g ↦ Quiver.Total.id_comp g
  have hm_ι₂ : m ∘ ι₂ = id := funext fun h ↦ Quiver.Total.comp_id h
  have hm_δ : m ∘ δ = u := funext fun y ↦ Quiver.Total.id_comp (u y)
  have hdm_ι₁ :
      tangentSpaceCast J (m p₀) (u x) (mfderiv K J m p₀ (mfderiv J K ι₁ (u x) v)) = v := by
    have hc : mfderiv K J m p₀ (mfderiv J K ι₁ (u x) v) = mfderiv J J (m ∘ ι₁) (u x) v := by
      rw [mfderiv_comp (u x) ((hm p₀).mdifferentiableAt (by simp))
        ((hι₁ (u x)).mdifferentiableAt (by simp))]
      rfl
    rw [hc]
    exact (tangentSpaceCast_mfderiv_congr_fun hm_ι₁ (u x) v).trans
      (congrArg (fun L ↦ L v) mfderiv_id)
  have hdm_ι₂ :
      tangentSpaceCast J (m p₀) (u x) (mfderiv K J m p₀ (mfderiv J K ι₂ (u x) w)) = w := by
    have hc : mfderiv K J m p₀ (mfderiv J K ι₂ (u x) w) = mfderiv J J (m ∘ ι₂) (u x) w := by
      rw [mfderiv_comp (u x) ((hm p₀).mdifferentiableAt (by simp))
        ((hι₂ (u x)).mdifferentiableAt (by simp))]
      rfl
    rw [hc]
    exact (tangentSpaceCast_mfderiv_congr_fun hm_ι₂ (u x) w).trans
      (congrArg (fun L ↦ L w) mfderiv_id)
  have hdm_δ :
      tangentSpaceCast J (m p₀) (u x) (mfderiv K J m p₀ (mfderiv I K δ x sv)) =
        mfderiv I J u x sv := by
    have hc : mfderiv K J m p₀ (mfderiv I K δ x sv) = mfderiv I J (m ∘ δ) x sv := by
      rw [mfderiv_comp x ((hm p₀).mdifferentiableAt (by simp))
        ((hδ x).mdifferentiableAt (by simp))]
      rfl
    rw [hc]
    exact tangentSpaceCast_mfderiv_congr_fun hm_δ x sv
  change tangentSpaceCast J (m p₀) (u x) (mfderiv K J m p₀ ξ) = v + w - mfderiv I J u x sv
  rw [hξ_eq, map_sub, map_add, map_sub, map_add, hdm_ι₁, hdm_ι₂, hdm_δ]

/-- **Differential of inversion at a unit.** Differentiating `m(g, g⁻¹) = u(t(g))` at `1_x` yields
`d(inv)_{1_x}(v) = du_x(ds_{1_x}(v) + dt_{1_x}(v)) - v` (after casting along `inv (𝟙 x) = 𝟙 x`). -/
theorem mfderiv_inverse_unit_apply (x : C) (v : TangentSpace J (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :
    tangentSpaceCast J (⟨x, x, inv (𝟙 x)⟩ : Quiver.Total C) ⟨x, x, 𝟙 x⟩
      (mfderiv J J (fun a : Quiver.Total C ↦ (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total C))
        ⟨x, x, 𝟙 x⟩ v) =
      mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x
        (mfderiv J I (Quiver.Total.left : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩ v +
          mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩ v) - v := by
  let := composablePairsChartedSpace I J C
  have := isManifold_composablePairs I J C
  let K := 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ E' - finrank ℝ E) → ℝ)
  let P := {p : Quiver.Total C × Quiver.Total C // p.1.left = p.2.right}
  let u : C → Quiver.Total C := fun y ↦ ⟨y, y, 𝟙 y⟩
  let invMap : Quiver.Total C → Quiver.Total C := fun a ↦ ⟨a.right, a.left, inv a.hom⟩
  let m : P → Quiver.Total C := fun p ↦ p.1.2.comp p.1.1 p.2.symm
  let p₀ : P := ⟨(u x, u x), rfl⟩
  let ψ : Quiver.Total C → P := fun g ↦ ⟨(g, invMap g), rfl⟩
  have hu : ContMDiff I J ∞ u := contMDiff_unit (I := I) (J := J) (C := C)
  have ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C) := contMDiff_target I J C
  have hinv : ContMDiff J J ∞ invMap := contMDiff_inverse (I := I) (J := J) (C := C)
  have hemb := isSmoothEmbedding_coe_composablePairs I J C
  have hm : ContMDiff K J ∞ m := contMDiff_mul_composablePairs I J C
  have hψ : ContMDiff J K ∞ ψ := hemb.contMDiff_iff_comp.mpr (contMDiff_id.prodMk hinv)
  have hinv_u : invMap (u x) = u x := by simp [invMap, u]
  have hψ_at : ψ (u x) = p₀ := Subtype.ext (Prod.ext rfl hinv_u)
  have hdiff_ψ : MDifferentiableAt J K ψ (u x) := (hψ (u x)).mdifferentiableAt (by simp)
  -- Cast `dψ_{1_x} v` along `ψ (u x) = p₀` to obtain a tangent vector at `p₀`.
  let ξ : TangentSpace K p₀ := tangentSpaceCast K (ψ (u x)) p₀ (mfderiv J K ψ (u x) v)
  -- Compute projections of `ξ`.
  have hpr₁_ψ : mfderiv K J (fun p : P ↦ p.1.1) p₀ ξ = v := by
    have h₁ : mfderiv K J (fun p : P ↦ p.1.1) (ψ (u x)) (mfderiv J K ψ (u x) v) = v := by
      rw [← ContinuousLinearMap.comp_apply,
        ← mfderiv_comp (u x) ((hemb.contMDiff.fst (ψ (u x))).mdifferentiableAt (by simp)) hdiff_ψ]
      exact congrArg (fun L ↦ L v) (mfderiv_id : mfderiv J J ((fun p : P ↦ p.1.1) ∘ ψ) (u x) = _)
    rw [← tangentSpaceCast_mfderiv_congr_pt (fun p : P ↦ p.1.1) hψ_at (mfderiv J K ψ (u x) v), h₁]
    rfl
  have hpr₂_ψ : mfderiv K J (fun p : P ↦ p.1.2) p₀ ξ =
      tangentSpaceCast J (invMap (u x)) (u x) (mfderiv J J invMap (u x) v) := by
    have h₂ : mfderiv K J (fun p : P ↦ p.1.2) (ψ (u x)) (mfderiv J K ψ (u x) v) =
        mfderiv J J invMap (u x) v := by
      rw [← ContinuousLinearMap.comp_apply,
        ← mfderiv_comp (u x) ((hemb.contMDiff.snd (ψ (u x))).mdifferentiableAt (by simp)) hdiff_ψ]
      rfl
    rw [← tangentSpaceCast_mfderiv_congr_pt (fun p : P ↦ p.1.2) hψ_at (mfderiv J K ψ (u x) v), h₂]
  -- Compare `dm_{p₀} ξ` with `d(m ∘ ψ)_{1_x} v = d(u ∘ t)_{1_x} v`.
  have hcomp_eq : m ∘ ψ = u ∘ Quiver.Total.right := funext fun g ↦ Quiver.Total.inv_comp g
  have hleft : tangentSpaceCast J (m (ψ (u x))) (u x) (mfderiv J J (m ∘ ψ) (u x) v) =
      mfderiv I J u x (mfderiv J I Quiver.Total.right (u x) v) := by
    calc tangentSpaceCast J (m (ψ (u x))) (u x) (mfderiv J J (m ∘ ψ) (u x) v)
      _ = mfderiv J J (u ∘ Quiver.Total.right) (u x) v :=
          tangentSpaceCast_mfderiv_congr_fun hcomp_eq (u x) v
      _ = mfderiv I J u x (mfderiv J I Quiver.Total.right (u x) v) := by
          rw [mfderiv_comp (u x) ((hu x).mdifferentiableAt (by simp))
            ((ht (u x)).mdifferentiableAt (by simp))]
          rfl
  have hm_cast : tangentSpaceCast J (m p₀) (u x) (mfderiv K J m p₀ ξ) =
      tangentSpaceCast J (m (ψ (u x))) (u x) (mfderiv J J (m ∘ ψ) (u x) v) := by
    rw [← tangentSpaceCast_mfderiv_congr_pt m hψ_at (mfderiv J K ψ (u x) v),
      tangentSpaceCast_trans_apply J (m (ψ (u x))) (m p₀) (u x),
      mfderiv_comp (u x) ((hm (ψ (u x))).mdifferentiableAt (by simp)) hdiff_ψ]
    rfl
  have hdm := mfderiv_mul_unit_apply I J C x ξ
  rw [hpr₁_ψ, hpr₂_ψ] at hdm
  have heq : mfderiv I J u x (mfderiv J I Quiver.Total.right (u x) v) =
      v + tangentSpaceCast J (invMap (u x)) (u x) (mfderiv J J invMap (u x) v) -
        mfderiv I J u x (mfderiv J I Quiver.Total.left (u x) v) := by
    calc mfderiv I J u x (mfderiv J I Quiver.Total.right (u x) v)
      _ = tangentSpaceCast J (m (ψ (u x))) (u x) (mfderiv J J (m ∘ ψ) (u x) v) := hleft.symm
      _ = tangentSpaceCast J (m p₀) (u x) (mfderiv K J m p₀ ξ) := hm_cast.symm
      _ = _ := hdm
  rw [map_add]
  calc tangentSpaceCast J (invMap (u x)) (u x) (mfderiv J J invMap (u x) v)
    _ = (v + tangentSpaceCast J (invMap (u x)) (u x) (mfderiv J J invMap (u x) v)) - v := by abel
    _ = (mfderiv I J u x (mfderiv J I Quiver.Total.right (u x) v) +
          mfderiv I J u x (mfderiv J I Quiver.Total.left (u x) v)) - v := by
        rw [eq_add_of_sub_eq heq.symm]
    _ = mfderiv I J u x (mfderiv J I Quiver.Total.left (u x) v) +
          mfderiv I J u x (mfderiv J I Quiver.Total.right (u x) v) - v := by abel

/-- On the source-vertical space `ker(ds_{1_x})`, the differential of inversion satisfies
`d(inv)_{1_x}(v) = du_x(dt_{1_x}(v)) - v` (after casting along `inv (𝟙 x) = 𝟙 x`). -/
theorem mfderiv_inverse_unit_of_ker_source (x : C)
    {v : TangentSpace J (⟨x, x, 𝟙 x⟩ : Quiver.Total C)}
    (hv : mfderiv J I (Quiver.Total.left : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩ v = 0) :
    tangentSpaceCast J (⟨x, x, inv (𝟙 x)⟩ : Quiver.Total C) ⟨x, x, 𝟙 x⟩
      (mfderiv J J (fun a : Quiver.Total C ↦ (⟨a.right, a.left, inv a.hom⟩ : Quiver.Total C))
        ⟨x, x, 𝟙 x⟩ v) =
      mfderiv I J (fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C)) x
        (mfderiv J I (Quiver.Total.right : Quiver.Total C → C) ⟨x, x, 𝟙 x⟩ v) - v := by
  rw [mfderiv_inverse_unit_apply I J C x v, hv, zero_add]

end TauCeti.IsLieGroupoid
